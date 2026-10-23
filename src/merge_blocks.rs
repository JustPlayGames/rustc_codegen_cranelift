//! Merges a block into its only predecessor when that predecessor ends in a plain `jump` to it.
//!
//! Lowering MIR leaves many such pairs: a call continues in the block of its return target, a
//! `try_call` the inliner turned back into a plain call jumps to the block it split off, and an
//! inlined body is entered and left with jumps. Without optimizations Cranelift keeps every CLIF
//! block as a block of its own up to register allocation, and each one costs there (liveness,
//! block parameters, critical edge splitting), although emission later drops the jump itself.

use cranelift_codegen::ir::{self, BlockArg, Function, InstructionData, Opcode};

pub(crate) fn merge_jump_chains(func: &mut Function) {
    let Some(entry) = func.layout.entry_block() else { return };

    // Incoming edges per block. A block that is an exception, `br_table` or `brif` target, or
    // the target of more than one jump, is left alone.
    let mut preds = vec![0u32; func.dfg.num_blocks()];
    let mut candidates = 0usize;
    for block in func.layout.blocks() {
        let Some(inst) = func.layout.last_inst(block) else { continue };
        let data = &func.dfg.insts[inst];
        if data.opcode() == Opcode::Jump {
            candidates += 1;
        }
        for dest in data.branch_destination(&func.dfg.jump_tables, &func.dfg.exception_tables) {
            let target = dest.block(&func.dfg.value_lists);
            preds[target.as_u32() as usize] += 1;
        }
    }
    if candidates == 0 {
        return;
    }

    let blocks: Vec<ir::Block> = func.layout.blocks().collect();
    let mut removed = vec![false; preds.len()];
    let mut args: Vec<ir::Value> = Vec::new();
    for block in blocks {
        if removed[block.as_u32() as usize] {
            continue;
        }
        // Follow the chain: once the next block is merged, its own jump ends this block.
        while let Some(jump) = func.layout.last_inst(block) {
            let InstructionData::Jump { opcode: Opcode::Jump, destination } = func.dfg.insts[jump]
            else {
                break;
            };
            let target = destination.block(&func.dfg.value_lists);
            if target == block || target == entry || preds[target.as_u32() as usize] != 1 {
                break;
            }

            args.clear();
            args.extend(destination.args(&func.dfg.value_lists).map(|arg| match arg {
                BlockArg::Value(value) => value,
                _ => unreachable!("jump with a try_call argument"),
            }));
            // In a cycle of unreachable blocks a jump can pass the target's own parameter
            // (`block2: jump block1(v2)` with `block1(v2): jump block2`): aliasing the parameter
            // to itself would be an alias loop, which resolving aliases later panics on.
            let target_params = func.dfg.block_params(target);
            if args.iter().any(|&arg| target_params.contains(&func.dfg.resolve_aliases(arg))) {
                break;
            }
            let params = func.dfg.detach_block_params(target);
            for (i, &arg) in args.iter().enumerate() {
                let param = params.get(i, &func.dfg.value_lists).unwrap();
                func.dfg.change_to_alias(param, arg);
            }

            func.layout.remove_inst(jump);
            while let Some(inst) = func.layout.first_inst(target) {
                func.layout.remove_inst(inst);
                func.layout.append_inst(inst, block);
            }
            func.layout.remove_block(target);
            removed[target.as_u32() as usize] = true;
        }
    }
}
