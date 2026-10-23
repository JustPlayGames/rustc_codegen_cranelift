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
    self, BlockArg, ConstantData, ExternalName, InstBuilder, InstructionData, LibCall,
    MemFlagsData, Opcode, Value, ValueDef, types,
};
use rustc_data_structures::fx::FxHashMap;
use target_lexicon::Architecture;

/// The largest copy or fill written out inline, in bytes.
pub(crate) const MAX_INLINE_BYTES: u64 = 128;

/// Whether the pass runs for this target.
pub(crate) fn enabled(isa: &dyn cranelift_codegen::isa::TargetIsa) -> bool {
    matches!(isa.triple().architecture, Architecture::X86_64 | Architecture::Aarch64(_))
        && std::env::var_os("CG_CLIF_NO_INLINE_MEMCPY").is_none()
}

/// Copies a value of `size` bytes (16 up to [`MAX_INLINE_BYTES`]) with 16-byte vector loads and
/// stores (and scalar ones for the tail) where the pass is enabled, instead of
/// `emit_small_memory_copy`'s 8-byte ones or a `memcpy` call above 32 bytes. Returns whether it
/// did.
pub(crate) fn emit_vector_copy(
    fx: &mut crate::FunctionCx<'_, '_, '_>,
    dest: Value,
    src: Value,
    size: u64,
    flags: MemFlagsData,
) -> bool {
    if !(16..=MAX_INLINE_BYTES).contains(&size) || !enabled(fx.module.isa()) {
        return false;
    }
    debug_assert!(!flags.aligned(), "the alignment of 16-byte accesses is not known");
    let loads: Vec<_> = chunks(size)
        .map(|(offset, ty)| (fx.bcx.ins().load(ty, flags, src, offset), offset))
        .collect();
    for (value, offset) in loads {
        fx.bcx.ins().store(flags, value, dest, offset);
    }
    true
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

    // The values each block parameter receives: an inlined callee's parameters are block
    // parameters fed by the jump into its body.
    let mut incoming: FxHashMap<(ir::Block, usize), Vec<Option<Value>>> = FxHashMap::default();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            let dfg = &func.dfg;
            for dest in dfg.insts[inst].branch_destination(&dfg.jump_tables, &dfg.exception_tables)
            {
                let target = dest.block(&dfg.value_lists);
                for (i, arg) in dest.args(&dfg.value_lists).enumerate() {
                    let value = match arg {
                        BlockArg::Value(v) => Some(v),
                        _ => None,
                    };
                    incoming.entry((target, i)).or_default().push(value);
                }
            }
        }
    }
    let consts = Consts { dfg: &func.dfg, incoming: &incoming };

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
            let Some(size) = consts.value(args[2], 0) else { continue };
            if size > MAX_INLINE_BYTES {
                continue;
            }
            let fill = if kind == Kind::Set {
                match consts.value(args[1], 0) {
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

/// Folds values to constants.
struct Consts<'a> {
    dfg: &'a ir::DataFlowGraph,
    incoming: &'a FxHashMap<(ir::Block, usize), Vec<Option<Value>>>,
}

impl Consts<'_> {
    /// The value of `v` when it folds to a constant through a few integer operations and block
    /// parameters that receive the same constant from every branch.
    fn value(&self, v: Value, depth: u32) -> Option<u64> {
        if depth > 8 {
            return None;
        }
        let dfg = self.dfg;
        let v = dfg.resolve_aliases(v);
        let mask = |x: u64| {
            let bits = dfg.value_type(v).bits();
            if bits >= 64 { x } else { x & ((1u64 << bits) - 1) }
        };
        let inst = match dfg.value_def(v) {
            ValueDef::Result(inst, _) => inst,
            ValueDef::Param(block, i) => {
                let values = self.incoming.get(&(block, i))?;
                let mut folded = None;
                for &value in values {
                    let c = self.value(value?, depth + 1)?;
                    if folded.is_some_and(|f| f != c) {
                        return None;
                    }
                    folded = Some(c);
                }
                return folded;
            }
            _ => return None,
        };
        match dfg.insts[inst] {
            InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => {
                Some(mask(imm.bits() as u64))
            }
            InstructionData::Binary { opcode, args } => {
                let a = self.value(args[0], depth + 1)?;
                let b = self.value(args[1], depth + 1)?;
                match opcode {
                    Opcode::Imul => Some(mask(a.checked_mul(b)?)),
                    Opcode::Iadd => Some(mask(a.checked_add(b)?)),
                    Opcode::Ishl if b < 64 => Some(mask(a.checked_shl(b as u32)?)),
                    _ => None,
                }
            }
            InstructionData::Unary { opcode: Opcode::Uextend, arg } => self.value(arg, depth + 1),
            InstructionData::Unary { opcode: Opcode::Ireduce, arg } => {
                self.value(arg, depth + 1).map(mask)
            }
            _ => None,
        }
    }
}
