//! SSA analysis

use rustc_index::IndexVec;
use rustc_middle::mir::StatementKind::*;

use crate::prelude::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum SsaKind {
    NotSsa,
    MaybeSsa,
}

impl SsaKind {
    pub(crate) fn is_ssa<'tcx>(self, fx: &FunctionCx<'_, '_, 'tcx>, ty: Ty<'tcx>) -> bool {
        self == SsaKind::MaybeSsa && (fx.clif_type(ty).is_some() || fx.clif_pair_type(ty).is_some())
    }
}

pub(crate) fn analyze(fx: &FunctionCx<'_, '_, '_>) -> IndexVec<Local, SsaKind> {
    let mut flag_map =
        fx.mir.local_decls.iter().map(|_| SsaKind::MaybeSsa).collect::<IndexVec<Local, SsaKind>>();

    // Unoptimized builds with full debuginfo keep every user variable in memory, as LLVM does at
    // -O0, so that debuggers find it at one frame offset throughout the function.
    if let Some(vars) = debug_variable_locals(fx) {
        for local in vars.iter() {
            flag_map[local] = SsaKind::NotSsa;
        }
    }

    for bb in fx.mir.basic_blocks.iter() {
        for stmt in bb.statements.iter() {
            // Borrowing a place takes the address of its local's memory, unless the place goes
            // through a pointer (`&*x`, `&(*x).field`, `&raw const (*x.0)[i]`): then the local is
            // only read for the pointer value and can stay in registers.
            if let Assign(place_and_rval) = &stmt.kind
                && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = &place_and_rval.1
                && !place.projection.iter().any(|elem| matches!(elem, PlaceElem::Deref))
            {
                flag_map[place.local] = SsaKind::NotSsa;
            }
        }
    }

    flag_map
}

/// The locals that hold user variables, when they are to be kept in memory for the debugger
/// (unoptimized builds with full debuginfo).
pub(crate) fn debug_variable_locals(
    fx: &FunctionCx<'_, '_, '_>,
) -> Option<rustc_index::bit_set::DenseBitSet<Local>> {
    if fx.debug_context.is_none()
        || fx.tcx.sess.opts.debuginfo != rustc_session::config::DebugInfo::Full
        || fx.tcx.sess.opts.optimize != rustc_session::config::OptLevel::No
    {
        return None;
    }
    let mut set = rustc_index::bit_set::DenseBitSet::new_empty(fx.mir.local_decls.len());
    for var in &fx.mir.var_debug_info {
        if let VarDebugInfoContents::Place(place) = var.value {
            set.insert(place.local);
        }
    }
    Some(set)
}
