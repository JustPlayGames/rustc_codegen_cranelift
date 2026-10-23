//! Functions that only call another function with their own parameters and return its results,
//! with the same signature (`call f(params); return results`), are defined as a `jmp` to it on
//! x86_64, without compiling them. About one compiled function in seven of a debug build is such
//! a forwarder (trait methods forwarding to an inherent one, closures' `call_once` shims, generic
//! wrappers around an inner function), each costing Cranelift a full function's work for a call
//! and a return.
//!
//! The callee then runs with the forwarder's arguments, stack and return address, as LLVM's tail
//! call makes it when optimizing: with equal signatures every argument, stack argument and the
//! return area are where the callee expects them, and its return goes straight to the caller. The
//! forwarder has no frame and never shows in a backtrace once it has jumped; at the jump itself
//! (a profiler's sample) the return address is where it was at the entry: an FDE without
//! instructions says so on ELF, and on Windows a function without unwind info is such a leaf
//! already (`define_frameless_function`). Calls that must abort when they unwind
//! carry a tag that their function's unwind tables act on, so they keep their own frame. Not done
//! with debuginfo (each function has its own description), nor for a function calling itself.
//! Only on ELF and COFF, where `mark_colocated` makes every direct call a rel32 one.

use cranelift_codegen::binemit::Reloc;
use cranelift_codegen::ir::{ExternalName, InstructionData, Opcode};
use cranelift_codegen::isa::TargetIsa;
use cranelift_module::{ModuleReloc, ModuleRelocTarget};

use crate::prelude::*;

/// The bytes of `jmp rel32` and the relocation of its target, when `func` (of `func_id`) only
/// forwards its parameters to another function and returns its results.
pub(crate) fn jump_thunk(
    func: &Function,
    func_id: FuncId,
    isa: &dyn TargetIsa,
) -> Option<([u8; 5], ModuleReloc)> {
    if isa.triple().architecture != target_lexicon::Architecture::X86_64 {
        return None;
    }
    let entry = func.layout.entry_block()?;
    // The instructions run from the entry block, through plain jumps (blocks are merged only
    // when the function is compiled): the call, then the return.
    let mut path = [None; 2];
    let mut n = 0;
    let mut block = entry;
    'blocks: for _ in 0..16 {
        for inst in func.layout.block_insts(block) {
            match func.dfg.insts[inst] {
                InstructionData::Jump { opcode: Opcode::Jump, destination } => {
                    let target = destination.block(&func.dfg.value_lists);
                    if destination.args(&func.dfg.value_lists).next().is_some()
                        || !func.dfg.block_params(target).is_empty()
                    {
                        return None;
                    }
                    block = target;
                    continue 'blocks;
                }
                _ if n < 2 => {
                    path[n] = Some(inst);
                    n += 1;
                }
                _ => return None,
            }
        }
        break;
    }
    let (Some(call), Some(ret)) = (path[0], path[1]) else { return None };
    if func.dfg.insts[ret].opcode() != Opcode::Return {
        return None;
    }
    let InstructionData::Call { opcode: Opcode::Call, func_ref, .. } = func.dfg.insts[call] else {
        return None;
    };
    if func.dfg.inst_args(call) != func.dfg.block_params(entry)
        || func.dfg.inst_args(ret) != func.dfg.inst_results(call)
        || !func.debug_tags.get(call).is_empty()
    {
        return None;
    }
    let ext_func = &func.dfg.ext_funcs[func_ref];
    if func.dfg.signatures[ext_func.signature] != func.signature {
        return None;
    }
    let ExternalName::User(name) = ext_func.name else { return None };
    let name = &func.params.user_named_funcs()[name];
    if name.namespace == 0 && name.index == func_id.as_u32() {
        return None;
    }
    // The relocation Cranelift gives the call once `mark_colocated` has made it direct: on ELF a
    // PLT32 (the linker resolves it to the callee, or to a PLT entry for one in a shared
    // library), on COFF a rel32 (to the import library's thunk for a function in a DLL). Other
    // object formats keep the call.
    let format = isa.triple().binary_format;
    if format != target_lexicon::BinaryFormat::Elf && format != target_lexicon::BinaryFormat::Coff {
        return None;
    }
    let kind = Reloc::X86CallPCRel4;
    let target = ModuleRelocTarget::user(name.namespace, name.index);
    Some(([0xe9, 0, 0, 0, 0], ModuleReloc { offset: 1, kind, name: target, addend: -4 }))
}
