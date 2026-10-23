//! Peephole optimizations that can be performed while creating clif ir.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstructionData, Opcode, Value, ValueDef};
use cranelift_frontend::FunctionBuilder;

/// If the given value was produced by the lowering of `Rvalue::Not` return the input and true,
/// otherwise return the given value and false.
pub(crate) fn maybe_unwrap_bool_not(bcx: &mut FunctionBuilder<'_>, arg: Value) -> (Value, bool) {
    if let ValueDef::Result(arg_inst, 0) = bcx.func.dfg.value_def(arg)
        && let InstructionData::IntCompare {
            opcode: Opcode::Icmp,
            cond: IntCC::Equal,
            args: [icmp_arg, imm],
        } = bcx.func.dfg.insts[arg_inst]
        && let ValueDef::Result(imm_inst, 0) = bcx.func.dfg.value_def(imm)
        && let InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } =
            bcx.func.dfg.insts[imm_inst]
        && imm.bits() == 0
    {
        // This is the lowering of `Rvalue::Not`
        (icmp_arg, true)
    } else {
        (arg, false)
    }
}

/// Returns whether the branch is statically known to be taken or `None` if it isn't statically known.
pub(crate) fn maybe_known_branch_taken(
    bcx: &FunctionBuilder<'_>,
    arg: Value,
    test_zero: bool,
) -> Option<bool> {
    let ValueDef::Result(arg_inst, 0) = bcx.func.dfg.value_def(arg) else { return None };

    let nonzero = match bcx.func.dfg.insts[arg_inst] {
        InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => imm.bits() != 0,
        // A compare of two constants: monomorphization made both sides known (lane counts and
        // sizes of generic code, `cfg!`-like consts), so only one side of the branch is ever
        // taken. Folding it here lets Cranelift drop the other side as unreachable.
        InstructionData::IntCompare { opcode: Opcode::Icmp, cond, args: [a, b] } => {
            let ty = bcx.func.dfg.value_type(a);
            eval_icmp(cond, ty.bits(), known_iconst(bcx, a)?, known_iconst(bcx, b)?)
        }
        _ => return None,
    };
    Some(if test_zero { !nonzero } else { nonzero })
}

fn known_iconst(bcx: &FunctionBuilder<'_>, v: Value) -> Option<i64> {
    let ValueDef::Result(inst, 0) = bcx.func.dfg.value_def(v) else { return None };
    match bcx.func.dfg.insts[inst] {
        InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => Some(imm.bits()),
        _ => None,
    }
}

/// `a cond b` for `bits`-wide integers (at most 64 bits) given as raw immediates.
fn eval_icmp(cond: IntCC, bits: u32, a: i64, b: i64) -> bool {
    let (ua, ub) = if bits >= 64 {
        (a as u64, b as u64)
    } else {
        let mask = (1u64 << bits) - 1;
        (a as u64 & mask, b as u64 & mask)
    };
    let sext = |x: u64| if bits >= 64 { x as i64 } else { ((x << (64 - bits)) as i64) >> (64 - bits) };
    let (sa, sb) = (sext(ua), sext(ub));
    match cond {
        IntCC::Equal => ua == ub,
        IntCC::NotEqual => ua != ub,
        IntCC::UnsignedLessThan => ua < ub,
        IntCC::UnsignedLessThanOrEqual => ua <= ub,
        IntCC::UnsignedGreaterThan => ua > ub,
        IntCC::UnsignedGreaterThanOrEqual => ua >= ub,
        IntCC::SignedLessThan => sa < sb,
        IntCC::SignedLessThanOrEqual => sa <= sb,
        IntCC::SignedGreaterThan => sa > sb,
        IntCC::SignedGreaterThanOrEqual => sa >= sb,
    }
}

/// If `arg` is a `select` between two constants of which exactly one is `value` (a niche
/// discriminant: `select(tag == niche, a, b)`), return the select's condition and whether it is
/// true when `arg == value`. A branch on `arg == value` can then test the condition directly.
pub(crate) fn maybe_select_of_consts_eq(
    bcx: &FunctionBuilder<'_>,
    arg: Value,
    value: u128,
) -> Option<(Value, bool)> {
    let value = u64::try_from(value).ok()?;
    let ValueDef::Result(arg_inst, 0) = bcx.func.dfg.value_def(arg) else { return None };
    let InstructionData::Ternary { opcode: Opcode::Select, args: [cond, a, b] } =
        bcx.func.dfg.insts[arg_inst]
    else {
        return None;
    };
    let bits = bcx.func.dfg.value_type(arg).bits();
    if bits > 64 {
        return None;
    }
    let mask = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
    let value = value & mask;
    let iconst = |v: Value| {
        let ValueDef::Result(inst, 0) = bcx.func.dfg.value_def(v) else { return None };
        match bcx.func.dfg.insts[inst] {
            InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => {
                Some(imm.bits() as u64 & mask)
            }
            _ => None,
        }
    };
    match (iconst(a)? == value, iconst(b)? == value) {
        (true, false) => Some((cond, true)),
        (false, true) => Some((cond, false)),
        _ => None,
    }
}
