//! Turns `memcpy`, `memmove` and `memset` calls of a small constant size into loads and stores.
//!
//! Copies whose size is only known after inlining (`ptr::copy_nonoverlapping(x, y, 1)` inside an
//! `#[inline(always)]` `ptr::swap`, `size_of::<u32>()` bytes in `load_int_le!`) and the copies of
//! values larger than [`FunctionBuilder::emit_small_memory_copy`]'s 32 bytes reach Cranelift as
//! libcalls. LLVM's always-inliner propagates the constant into `llvm.memcpy`, which instruction
//! selection expands even without optimizations. This pass does the same once the CGU's
//! functions are inlined: a libcall whose size argument folds to a constant up to
//! [`MAX_INLINE_BYTES`] becomes 16-byte vector and scalar loads followed by the stores (all loads
//! first, so `memmove`'s overlapping copies stay correct).
//!
//! Only on x86_64 and AArch64, where unaligned scalar and 128-bit vector accesses are always
//! allowed: the libcall gives no alignment.
//!
//! [`FunctionBuilder::emit_small_memory_copy`]: cranelift_frontend::FunctionBuilder::emit_small_memory_copy

use cranelift_codegen::cursor::{Cursor, FuncCursor};
use cranelift_codegen::ir::{
    self, ConstantData, ExternalName, InstBuilder, InstructionData, LibCall, MemFlagsData, Opcode,
    Value, types,
};
use target_lexicon::Architecture;

/// The largest copy or fill written out inline, in bytes.
pub(crate) const MAX_INLINE_BYTES: u64 = 128;

/// Whether the pass runs for this target.
pub(crate) fn enabled(isa: &dyn cranelift_codegen::isa::TargetIsa) -> bool {
    matches!(isa.triple().architecture, Architecture::X86_64 | Architecture::Aarch64(_))
        && std::env::var_os("CG_CLIF_NO_INLINE_MEMCPY").is_none()
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Kind {
    Copy,
    Set,
}

/// Rewrites the function's small constant-size `memcpy`/`memmove`/`memset` calls in place.
pub(crate) fn inline_small_mem_libcalls(func: &mut ir::Function) {
    // Cheap check first: most functions call none of them.
    let has_libcall = func.dfg.ext_funcs.values().any(|ext| {
        matches!(
            ext.name,
            ExternalName::LibCall(LibCall::Memcpy | LibCall::Memmove | LibCall::Memset)
        )
    });
    if !has_libcall {
        return;
    }

    let mut todo = Vec::new();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            let InstructionData::Call { opcode: Opcode::Call, func_ref, .. } = func.dfg.insts[inst]
            else {
                continue;
            };
            let kind = match func.dfg.ext_funcs[func_ref].name {
                ExternalName::LibCall(LibCall::Memcpy | LibCall::Memmove) => Kind::Copy,
                ExternalName::LibCall(LibCall::Memset) => Kind::Set,
                _ => continue,
            };
            let args = func.dfg.inst_args(inst);
            if args.len() != 3 {
                continue;
            }
            let Some(size) = const_value(&func.dfg, args[2], 0) else { continue };
            if size > MAX_INLINE_BYTES {
                continue;
            }
            let fill = if kind == Kind::Set {
                match const_value(&func.dfg, args[1], 0) {
                    Some(v) => Some(v as u8),
                    None => continue,
                }
            } else {
                None
            };
            todo.push((inst, kind, size, fill));
        }
    }

    for (inst, kind, size, fill) in todo {
        let args = func.dfg.inst_args(inst).to_vec();
        let dest = args[0];
        let mut pos = FuncCursor::new(func).at_inst(inst);
        let flags = MemFlagsData::new().with_notrap();
        match kind {
            Kind::Copy => {
                let src = args[1];
                let mut loads = Vec::new();
                for (offset, ty) in chunks(size) {
                    loads.push((pos.ins().load(ty, flags, src, offset), offset));
                }
                for (val, offset) in loads {
                    pos.ins().store(flags, val, dest, offset);
                }
            }
            Kind::Set => {
                let byte = fill.unwrap();
                let mut vector = None;
                for (offset, ty) in chunks(size) {
                    let val = if ty == types::I8X16 {
                        *vector.get_or_insert_with(|| {
                            let c =
                                pos.func.dfg.constants.insert(ConstantData::from(vec![byte; 16]));
                            pos.ins().vconst(types::I8X16, c)
                        })
                    } else {
                        let bits = u64::from(byte) * 0x0101_0101_0101_0101;
                        let mask = if ty.bits() >= 64 { u64::MAX } else { (1 << ty.bits()) - 1 };
                        pos.ins().iconst(ty, (bits & mask) as i64)
                    };
                    pos.ins().store(flags, val, dest, offset);
                }
            }
        }
        // The libcalls return their first argument.
        let results = pos.func.dfg.inst_results(inst).to_vec();
        pos.remove_inst();
        func.dfg.detach_inst_results(inst);
        for result in results {
            func.dfg.change_to_alias(result, dest);
        }
    }
}

/// The accesses that cover `size` bytes: 16-byte vectors, then 8, 4, 2 and 1-byte integers.
fn chunks(size: u64) -> impl Iterator<Item = (i32, ir::Type)> {
    let mut offset = 0u64;
    std::iter::from_fn(move || {
        let left = size - offset;
        let (ty, len) = match left {
            0 => return None,
            16.. => (types::I8X16, 16),
            8.. => (types::I64, 8),
            4.. => (types::I32, 4),
            2.. => (types::I16, 2),
            _ => (types::I8, 1),
        };
        let at = offset as i32;
        offset += len;
        Some((at, ty))
    })
}

/// The value of `v` when it folds to a constant through a few integer operations.
fn const_value(dfg: &ir::DataFlowGraph, v: Value, depth: u32) -> Option<u64> {
    if depth > 6 {
        return None;
    }
    let v = dfg.resolve_aliases(v);
    let inst = dfg.value_def(v).inst()?;
    let mask = |x: u64| {
        let bits = dfg.value_type(v).bits();
        if bits >= 64 { x } else { x & ((1u64 << bits) - 1) }
    };
    match dfg.insts[inst] {
        InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => Some(mask(imm.bits() as u64)),
        InstructionData::Binary { opcode, args } => {
            let a = const_value(dfg, args[0], depth + 1)?;
            let b = const_value(dfg, args[1], depth + 1)?;
            match opcode {
                Opcode::Imul => Some(mask(a.checked_mul(b)?)),
                Opcode::Iadd => Some(mask(a.checked_add(b)?)),
                Opcode::Ishl if b < 64 => Some(mask(a.checked_shl(b as u32)?)),
                _ => None,
            }
        }
        InstructionData::Unary { opcode: Opcode::Uextend, arg } => const_value(dfg, arg, depth + 1),
        InstructionData::Unary { opcode: Opcode::Ireduce, arg } => {
            const_value(dfg, arg, depth + 1).map(mask)
        }
        _ => None,
    }
}
