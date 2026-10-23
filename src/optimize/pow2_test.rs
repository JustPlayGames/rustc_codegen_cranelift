//! Turns `x.count_ones() == 1` (`is_power_of_two`) into a test without a population count.
//!
//! Every `ptr::copy_nonoverlapping`, `slice::from_raw_parts` and friends checks its alignment
//! with `is_aligned_to`, which asserts `align.is_power_of_two()`, i.e. `align.count_ones() == 1`.
//! Without the `popcnt` target feature (the x86_64 baseline) a population count is a chain of
//! about 20 shifts, masks and a multiply. The comparison only needs to know whether exactly one
//! bit is set: `x ^ (x - 1) > x - 1` (unsigned) holds exactly for powers of two, also for `x = 0`
//! (`MAX > MAX` is false). Runs after the CLIF inliner, which brings `count_ones` and the
//! comparison into one function (the count reaches the comparison through the block parameter
//! of the inlined call's return).

use cranelift_codegen::cursor::{Cursor, FuncCursor};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    self, BlockArg, InstBuilder, InstructionData, Opcode, Value, ValueDef, types,
};
use rustc_data_structures::fx::FxHashMap;

pub(crate) fn rewrite_popcount_tests(func: &mut ir::Function) {
    // Cheap check first: almost no function counts bits.
    if !func
        .layout
        .blocks()
        .flat_map(|block| func.layout.block_insts(block))
        .any(|inst| func.dfg.insts[inst].opcode() == Opcode::Popcnt)
    {
        return;
    }

    // The values each block parameter receives.
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

    // `v` through aliases and block parameters that receive the same value from every branch.
    let source = |dfg: &ir::DataFlowGraph, mut v: Value| -> Value {
        for _ in 0..8 {
            v = dfg.resolve_aliases(v);
            let ValueDef::Param(block, i) = dfg.value_def(v) else { break };
            let Some(values) = incoming.get(&(block, i)) else { break };
            let Some(Some(first)) = values.first().copied() else { break };
            if values.iter().any(|&x| x != Some(first)) || first == v {
                break;
            }
            v = first;
        }
        v
    };
    // The integer `x` when `v` is `popcnt(x)`, possibly widened or narrowed (a count fits in
    // any integer type).
    let popcount_of = |dfg: &ir::DataFlowGraph, v: Value| -> Option<Value> {
        let mut v = source(dfg, v);
        for _ in 0..4 {
            let ValueDef::Result(inst, _) = dfg.value_def(v) else { return None };
            match dfg.insts[inst] {
                InstructionData::Unary { opcode: Opcode::Popcnt, arg } => {
                    let ty = dfg.value_type(arg);
                    return (ty.is_int() && ty.bits() <= 64).then_some(arg);
                }
                InstructionData::Unary { opcode: Opcode::Uextend | Opcode::Ireduce, arg } => {
                    v = source(dfg, arg);
                }
                _ => return None,
            }
        }
        None
    };
    let is_one = |dfg: &ir::DataFlowGraph, v: Value| -> bool {
        let v = source(dfg, v);
        let ValueDef::Result(inst, _) = dfg.value_def(v) else { return false };
        matches!(dfg.insts[inst], InstructionData::UnaryImm { opcode: Opcode::Iconst, imm }
            if imm.bits() == 1)
    };

    let mut todo = Vec::new();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            let InstructionData::IntCompare { opcode: Opcode::Icmp, cond, args } =
                func.dfg.insts[inst]
            else {
                continue;
            };
            if !matches!(cond, IntCC::Equal | IntCC::NotEqual) {
                continue;
            }
            let x = if is_one(&func.dfg, args[1]) {
                popcount_of(&func.dfg, args[0])
            } else if is_one(&func.dfg, args[0]) {
                popcount_of(&func.dfg, args[1])
            } else {
                None
            };
            if let Some(x) = x {
                todo.push((inst, cond, x));
            }
        }
    }

    for (inst, cond, x) in todo {
        let mut pos = FuncCursor::new(func).at_inst(inst);
        let ty = pos.func.dfg.value_type(x);
        debug_assert!(ty.is_int() && ty != types::I128);
        let below = pos.ins().iadd_imm_s(x, -1);
        let flipped = pos.ins().bxor(x, below);
        let cond = if cond == IntCC::Equal {
            IntCC::UnsignedGreaterThan
        } else {
            IntCC::UnsignedLessThanOrEqual
        };
        pos.func.replace(inst).icmp(cond, flipped, below);
    }
}
