//! Move forwarding: pass a moved local to a call in place instead of copying it to a temporary.
//!
//! MIR often moves a value into a fresh temporary just to move that temporary into a call
//! (`_8 = move _3; _0 = <F as FnOnce>::call_once(move _8, ..)`, with `_3` a closure argument
//! that has a drop flag). For a value passed by reference this costs a copy into a stack slot of
//! its own in every frame that forwards it: deeply recursive code that hands closures down
//! (UI element trees) then needs far more stack than LLVM-built code, whose memcpy optimisation
//! removes such copies. When the temporary is used for nothing else and the source isn't touched
//! between the move and the call, the temporary becomes an alias of the source, the move isn't
//! emitted, and the call receives the source's memory, as an owned by-reference argument does.
//! Like stack slot sharing, this only runs when optimizing.

use rustc_index::IndexVec;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{Location, Operand, Rvalue, StatementKind, TerminatorKind};

use crate::analyze::SsaKind;
use crate::prelude::*;

pub(crate) struct MoveForwarding {
    /// The local each forwarded temporary aliases.
    pub(crate) alias_of: IndexVec<Local, Option<Local>>,
    /// The `temp = move source` statements not to emit, with their source.
    pub(crate) skipped: Vec<(Location, Local)>,
}

pub(crate) fn analyze<'tcx>(
    fx: &FunctionCx<'_, '_, 'tcx>,
    ssa: &IndexVec<Local, SsaKind>,
) -> MoveForwarding {
    let mir = fx.mir;
    let mut forwarding = MoveForwarding {
        alias_of: IndexVec::from_elem_n(None, mir.local_decls.len()),
        skipped: vec![],
    };
    if fx.tcx.sess.opts.optimize == rustc_session::config::OptLevel::No {
        return forwarding;
    }

    // Uses of each local anywhere in the body, storage markers and debuginfo aside.
    let mut uses = IndexVec::<Local, u32>::from_elem_n(0, mir.local_decls.len());
    struct CountUses<'a>(&'a mut IndexVec<Local, u32>);
    impl<'tcx> Visitor<'tcx> for CountUses<'_> {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
            if !matches!(context, PlaceContext::NonUse(_)) {
                self.0[local] += 1;
            }
        }
    }
    CountUses(&mut uses).visit_body(mir);

    let is_memory = |local: Local| {
        let ty = fx.monomorphize(mir.local_decls[local].ty);
        let layout = fx.layout_of(ty);
        !ssa[local].is_ssa(fx, ty) && layout.is_sized() && layout.size.bytes() > 0
    };

    for (bb, data) in mir.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        let terminator = data.terminator();
        let TerminatorKind::Call { args, destination, .. } = &terminator.kind else {
            continue;
        };
        for (i, stmt) in data.statements.iter().enumerate() {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (dest, Rvalue::Use(Operand::Move(src), _)) = &**assign else { continue };
            let (Some(temp), Some(src)) = (dest.as_local(), src.as_local()) else { continue };
            if temp == src
                || src == RETURN_PLACE
                || mir.local_kind(temp) != rustc_middle::mir::LocalKind::Temp
                || forwarding.alias_of[src].is_some()
                || forwarding.alias_of[temp].is_some()
            {
                continue;
            }
            // Only the move and one moved argument of this block's call use the temporary.
            if uses[temp] != 2
                || args.iter().filter(|arg| arg.node == Operand::Move(temp.into())).count() != 1
            {
                continue;
            }
            if destination.local == src || destination.local == temp {
                continue;
            }
            if !is_memory(temp) || !is_memory(src) {
                continue;
            }
            // Nothing between the move and the call touches the source, and the call mentions
            // it nowhere else.
            let mut touched = false;
            for later in &data.statements[i + 1..] {
                touched |= mentions(later, src);
            }
            if touched || terminator_mentions(terminator, src) {
                continue;
            }
            forwarding.alias_of[temp] = Some(src);
            forwarding.skipped.push((Location { block: bb, statement_index: i }, src));
        }
    }
    forwarding
}

struct Mentions {
    local: Local,
    found: bool,
}

impl<'tcx> Visitor<'tcx> for Mentions {
    fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Location) {
        self.found |= local == self.local;
    }
}

fn mentions(stmt: &rustc_middle::mir::Statement<'_>, local: Local) -> bool {
    let mut m = Mentions { local, found: false };
    m.visit_statement(stmt, Location::START);
    m.found
}

fn terminator_mentions(terminator: &rustc_middle::mir::Terminator<'_>, local: Local) -> bool {
    let mut m = Mentions { local, found: false };
    m.visit_terminator(terminator, Location::START);
    m.found
}
