//! Stack slot sharing: locals whose storage is never live at the same time share one stack slot.
//!
//! Without it every MIR local that needs memory gets a stack slot of its own, so a function that
//! builds many large temporaries one after the other (UI builder chains: dozens of `Div`s of
//! hundreds of bytes each) gets a frame several times larger than LLVM's at `-O1` and up, where
//! LLVM's stack colouring merges allocas with disjoint lifetimes. Deeply recursive code then
//! overflows stacks that LLVM-built code fits in.
//!
//! A local occupies its slot where its storage is maybe live (between `StorageLive` and
//! `StorageDead`, a forward dataflow) and, unless it is ever borrowed, only where its value is
//! maybe live as well (backward liveness: from a write to the last read): builder chains keep
//! all their temporaries' storage live to the end of the statement, but each value dies when it
//! is moved into the next call. A local also occupies its slot at every statement that mentions
//! it, so that a destination never shares memory with an operand of the same statement. Two
//! locals share a slot when they never occupy at the same program point. Locals without
//! `StorageLive` (always live), SSA locals, arguments and the return place are left alone. Like
//! LLVM, with full debuginfo this only runs when optimizing, so debug builds that describe
//! variables keep one slot per local for debuggers.

use rustc_index::IndexVec;
use rustc_middle::mir::visit::{MutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{BasicBlock, Location, Rvalue, StatementKind, TerminatorKind};

use crate::analyze::SsaKind;
use crate::move_forwarding::MoveForwarding;
use crate::prelude::*;

/// Above this many words of interference checks (candidates squared times program points over
/// 64), don't share: the analysis would cost more compile time than the frame size is worth.
const MAX_WORK: usize = 64 << 20;

pub(crate) struct SlotSharing {
    /// The shared slot of each local that got one.
    pub(crate) group_of: IndexVec<Local, Option<usize>>,
    /// Size and alignment of each shared slot.
    pub(crate) groups: Vec<(u64, u64)>,
}

struct BitSet(Vec<u64>);

impl BitSet {
    fn new(bits: usize) -> Self {
        BitSet(vec![0; bits.div_ceil(64)])
    }
    fn insert(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn remove(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }
    fn union(&mut self, other: &BitSet) -> bool {
        let mut changed = false;
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            let new = *a | *b;
            changed |= new != *a;
            *a = new;
        }
        changed
    }
    fn intersects(&self, other: &BitSet) -> bool {
        self.0.iter().zip(&other.0).any(|(a, b)| a & b != 0)
    }
}

/// The indices of the set bits of `word`, lowest first.
fn set_bits(mut word: u64) -> impl Iterator<Item = usize> {
    std::iter::from_fn(move || {
        if word == 0 {
            return None;
        }
        let b = word.trailing_zeros() as usize;
        word &= word - 1;
        Some(b)
    })
}

pub(crate) fn analyze<'tcx>(
    fx: &FunctionCx<'_, '_, 'tcx>,
    ssa: &IndexVec<Local, SsaKind>,
    forwarding: &MoveForwarding,
) -> SlotSharing {
    let mir = fx.mir;
    let mut sharing = SlotSharing {
        group_of: IndexVec::from_elem_n(None, mir.local_decls.len()),
        groups: vec![],
    };
    // Without optimizations a debugger may show a local whose memory another one reuses, so
    // locals keep slots of their own then, unless the debuginfo describes no variables (line
    // tables only, or none).
    if fx.tcx.sess.opts.optimize == rustc_session::config::OptLevel::No
        && fx.tcx.sess.opts.debuginfo == rustc_session::config::DebugInfo::Full
    {
        return sharing;
    }

    // Candidates: memory locals with storage markers.
    let mut has_storage_live = IndexVec::<Local, bool>::from_elem_n(false, mir.local_decls.len());
    for bb in mir.basic_blocks.iter() {
        for stmt in &bb.statements {
            if let StatementKind::StorageLive(local) = stmt.kind {
                has_storage_live[local] = true;
            }
        }
    }
    let mut index_of = IndexVec::<Local, Option<usize>>::from_elem_n(None, mir.local_decls.len());
    let mut candidates = vec![];
    for local in mir.vars_and_temps_iter() {
        // A forwarded temporary has no memory of its own.
        if !has_storage_live[local] || forwarding.alias_of[local].is_some() {
            continue;
        }
        let ty = fx.monomorphize(mir.local_decls[local].ty);
        if ssa[local].is_ssa(fx, ty) {
            continue;
        }
        let layout = fx.layout_of(ty);
        if layout.is_unsized() || layout.size.bytes() == 0 {
            continue;
        }
        index_of[local] = Some(candidates.len());
        candidates.push((local, layout.size.bytes(), layout.align.abi.bytes()));
    }
    if candidates.len() < 2 {
        return sharing;
    }

    // Program points: before each statement and before the terminator of each block.
    let mut block_start = IndexVec::<BasicBlock, usize>::with_capacity(mir.basic_blocks.len());
    let mut points = 0;
    for bb in mir.basic_blocks.iter() {
        block_start.push(points);
        points += bb.statements.len() + 1;
    }
    if candidates.len().saturating_mul(candidates.len()).saturating_mul(points.div_ceil(64))
        > MAX_WORK
    {
        return sharing;
    }

    // Maybe-live storage at each block entry: forward union dataflow.
    let n = candidates.len();
    let mut entry: IndexVec<BasicBlock, BitSet> =
        mir.basic_blocks.indices().map(|_| BitSet::new(n)).collect();
    let mut worklist: Vec<BasicBlock> = mir.basic_blocks.indices().collect();
    let mut queued = IndexVec::<BasicBlock, bool>::from_elem_n(true, mir.basic_blocks.len());
    while let Some(bb) = worklist.pop() {
        queued[bb] = false;
        let mut live = BitSet(entry[bb].0.clone());
        for stmt in &mir.basic_blocks[bb].statements {
            apply(&stmt.kind, &index_of, &mut live);
        }
        for succ in mir.basic_blocks[bb].terminator().successors() {
            if entry[succ].union(&live) && !queued[succ] {
                queued[succ] = true;
                worklist.push(succ);
            }
        }
    }

    // Which candidates are ever borrowed: a pointer to them may be used anywhere while their
    // storage is live, so their value liveness says nothing.
    let mut borrowed = BitSet::new(n);
    for bb in mir.basic_blocks.iter() {
        for stmt in &bb.statements {
            if let StatementKind::Assign(assign) = &stmt.kind
                && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = &assign.1
                && !place.is_indirect()
                && let Some(c) = index_of[place.local]
            {
                borrowed.insert(c);
            }
        }
    }

    // Value liveness (backward): live before a statement = (live after - whole writes) + reads.
    let mut live_in: IndexVec<BasicBlock, BitSet> =
        mir.basic_blocks.indices().map(|_| BitSet::new(n)).collect();
    let mut queued = IndexVec::<BasicBlock, bool>::from_elem_n(true, mir.basic_blocks.len());
    let mut worklist: Vec<BasicBlock> = mir.basic_blocks.indices().rev().collect();
    let predecessors = mir.basic_blocks.predecessors();
    while let Some(bb) = worklist.pop() {
        queued[bb] = false;
        let live = block_live_in(mir, bb, &index_of, n, &live_in, |_, _| {});
        if live.0 != live_in[bb].0 {
            live_in[bb] = live;
            for &pred in &predecessors[bb] {
                if !queued[pred] {
                    queued[pred] = true;
                    worklist.push(pred);
                }
            }
        }
    }

    // Where each candidate occupies its slot.
    let mut live_at: Vec<BitSet> = (0..n).map(|_| BitSet::new(points)).collect();
    let words = n.div_ceil(64);
    // Storage liveness before each statement of the current block (row i = before statement i,
    // the last row before the terminator), reused across blocks.
    let mut storage_at: Vec<u64> = vec![];
    let mut mentioned: Vec<Vec<usize>> = vec![];
    // Forwarded sources by block.
    let mut skipped_in: IndexVec<BasicBlock, Vec<(usize, usize)>> =
        IndexVec::from_elem_n(vec![], mir.basic_blocks.len());
    for &(loc, src) in &forwarding.skipped {
        if let Some(c) = index_of[src] {
            skipped_in[loc.block].push((loc.statement_index, c));
        }
    }
    for (bb, data) in mir.basic_blocks.iter_enumerated() {
        let rows = data.statements.len() + 1;
        storage_at.clear();
        let mut storage = BitSet(entry[bb].0.clone());
        for i in 0..rows {
            storage_at.extend_from_slice(&storage.0);
            if let Some(stmt) = data.statements.get(i) {
                apply(&stmt.kind, &index_of, &mut storage);
            }
        }
        mentioned.clear();
        mentioned.resize(rows, vec![]);
        collect_mentions(mir, bb, &index_of, &mut mentioned);
        // A forwarded source's memory is the call's argument: it is in use from its move to the
        // call, although its value is dead after the move.
        for &(statement_index, c) in &skipped_in[bb] {
            for m in &mut mentioned[statement_index..] {
                m.push(c);
            }
        }
        let start = block_start[bb];
        // Value liveness before each statement of the block, from the end: a candidate occupies
        // its slot where its storage is live and it is borrowed or its value is live.
        block_live_in(mir, bb, &index_of, n, &live_in, |i, value_live| {
            let point = start + i;
            let storage = &storage_at[i * words..(i + 1) * words];
            for (w, ((&s, &v), &b)) in storage.iter().zip(&value_live.0).zip(&borrowed.0).enumerate()
            {
                for bit in set_bits(s & (v | b)) {
                    live_at[w * 64 + bit].insert(point);
                }
            }
            for &c in &mentioned[i] {
                live_at[c].insert(point);
            }
        });
    }

    // Greedy: largest locals first, each into the first slot it doesn't interfere with.
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&c| std::cmp::Reverse(candidates[c].1));
    let mut group_live: Vec<BitSet> = vec![];
    for c in order {
        let (local, size, align) = candidates[c];
        let group = match group_live.iter().position(|g| !g.intersects(&live_at[c])) {
            Some(g) => {
                group_live[g].union(&live_at[c]);
                let (gsize, galign) = &mut sharing.groups[g];
                *gsize = (*gsize).max(size);
                *galign = (*galign).max(align);
                g
            }
            None => {
                group_live.push(BitSet(live_at[c].0.clone()));
                sharing.groups.push((size, align));
                sharing.groups.len() - 1
            }
        };
        sharing.group_of[local] = Some(group);
    }
    for (size, align) in &mut sharing.groups {
        *size = size.next_multiple_of(*align);
    }
    sharing
}

fn apply(kind: &StatementKind<'_>, index_of: &IndexVec<Local, Option<usize>>, live: &mut BitSet) {
    match *kind {
        StatementKind::StorageLive(local) => {
            if let Some(c) = index_of[local] {
                live.insert(c);
            }
        }
        StatementKind::StorageDead(local) => {
            if let Some(c) = index_of[local] {
                live.remove(c);
            }
        }
        _ => {}
    }
}

/// Value liveness at the entry of `bb` from its successors' entries. `each(i, live)` sees the liveness before the terminator (`i` = number of
/// statements) and then before each statement, from the last to the first.
fn block_live_in<'tcx>(
    mir: &rustc_middle::mir::Body<'tcx>,
    bb: BasicBlock,
    index_of: &IndexVec<Local, Option<usize>>,
    n: usize,
    live_in: &IndexVec<BasicBlock, BitSet>,
    mut each: impl FnMut(usize, &BitSet),
) -> BitSet {
    let data = &mir.basic_blocks[bb];
    let terminator = data.terminator();
    let mut live = BitSet::new(n);
    // A call's destination is written on the return edge only: it stays live if another
    // successor (the unwind edge) still needs its old value.
    let (return_target, destination) = match &terminator.kind {
        TerminatorKind::Call { target, destination, .. } => (*target, destination.as_local()),
        _ => (None, None),
    };
    for succ in terminator.successors() {
        if Some(succ) == return_target
            && let Some(dest) = destination
            && let Some(c) = index_of[dest]
        {
            let mut from_return = BitSet(live_in[succ].0.clone());
            from_return.remove(c);
            live.union(&from_return);
        } else {
            live.union(&live_in[succ]);
        }
    }
    let mut transfer = Transfer { index_of, live: &mut live };
    transfer.visit_terminator(
        terminator,
        Location { block: bb, statement_index: data.statements.len() },
    );
    each(data.statements.len(), &live);
    for (i, stmt) in data.statements.iter().enumerate().rev() {
        Transfer { index_of, live: &mut live }
            .visit_statement(stmt, Location { block: bb, statement_index: i });
        each(i, &live);
    }
    live
}

/// Backward liveness transfer of one statement or terminator, field-insensitively: a write of the
/// whole local kills it, any read, borrow or partial write keeps it alive.
struct Transfer<'a> {
    index_of: &'a IndexVec<Local, Option<usize>>,
    live: &'a mut BitSet,
}

impl<'tcx> Visitor<'tcx> for Transfer<'_> {
    // `super_place` hands a projected place's base local a `Projection` context, so only a write
    // of the whole local reaches here as a store.
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if let Some(c) = self.index_of[local] {
            match context {
                PlaceContext::NonUse(_) => {}
                // A call's destination is written on the return edge: see `block_live_in`.
                PlaceContext::MutatingUse(MutatingUseContext::Call) => {}
                PlaceContext::MutatingUse(
                    MutatingUseContext::Store
                    | MutatingUseContext::AsmOutput
                    | MutatingUseContext::Yield,
                ) => self.live.remove(c),
                _ => self.live.insert(c),
            }
        }
    }
}

/// The candidates each statement (and, last, the terminator) of `bb` mentions at all.
fn collect_mentions<'tcx>(
    mir: &rustc_middle::mir::Body<'tcx>,
    bb: BasicBlock,
    index_of: &IndexVec<Local, Option<usize>>,
    mentioned: &mut [Vec<usize>],
) {
    struct Mentions<'a> {
        index_of: &'a IndexVec<Local, Option<usize>>,
        out: Vec<usize>,
    }
    impl<'tcx> Visitor<'tcx> for Mentions<'_> {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
            if !matches!(context, PlaceContext::NonUse(_))
                && let Some(c) = self.index_of[local]
            {
                self.out.push(c);
            }
        }
    }
    let data = &mir.basic_blocks[bb];
    for (i, stmt) in data.statements.iter().enumerate() {
        let mut m = Mentions { index_of, out: vec![] };
        m.visit_statement(stmt, Location { block: bb, statement_index: i });
        mentioned[i] = m.out;
    }
    let mut m = Mentions { index_of, out: vec![] };
    m.visit_terminator(
        data.terminator(),
        Location { block: bb, statement_index: data.statements.len() },
    );
    mentioned[data.statements.len()] = m.out;
}
