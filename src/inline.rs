//! Post-monomorphization inlining of the functions of one codegen unit, on Cranelift IR.
//!
//! rustc's MIR inliner works on generic MIR, so a call through a generic parameter (an iterator
//! adapter calling its closure, `T: PartialOrd` calling `u32::lt`, `Deref` of a `Vec`) is still a
//! call after monomorphization. LLVM inlines those afterwards, at every opt level for
//! `#[inline(always)]` and by its own heuristics when optimizing; Cranelift does not inline on its
//! own. This pass uses Cranelift's inliner (`Context::inline`) over the functions of the codegen
//! unit, whose Cranelift IR is all there before any of it is compiled:
//!
//! - without optimizations, only `#[inline(always)]` callees (as LLVM's always-inliner does);
//! - when optimizing, also small callees (`Inliner::max_size` instructions, more with
//!   `#[inline]`), never `#[inline(never)]` or `#[cold]` ones.
//!
//! Callees are processed first (bottom-up over the codegen unit's call graph), so a callee is
//! inlined with its own inlined calls; recursive calls stay calls. A callee is never inlined
//! when it has inline assembly, reads the frame or stack pointer or the return address, has
//! dynamic stack slots, or tail calls; nor when its stack slots exceed a budget (so inlining
//! cannot grow a caller's frame much: `stack_slot_sharing` works per MIR body and does not see
//! inlined slots), and a caller stops taking callees once it has grown past a limit.
//!
//! Configuration: `-Cllvm-args=clif-inline=<off|always|small|N>` (N = the size limit for
//! callees without `#[inline]`; `small` = the default limit). Default: `always` without
//! optimizations, `small` with them.

use std::borrow::Cow;

use cranelift_codegen::inline::{Inline, InlineCommand};
use cranelift_codegen::ir::{self, InstructionData, Opcode};
use rustc_data_structures::fx::FxHashMap;

use crate::base::CodegenedFunction;
use crate::prelude::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum InlineMode {
    Off,
    /// Only `#[inline(always)]` callees.
    Always,
    /// `#[inline(always)]` callees and those up to this many instructions (twice that with
    /// `#[inline]`).
    Small(u32),
}

pub(crate) const DEFAULT_SMALL: u32 = 24;

/// The callee's own attributes, recorded when its Cranelift IR is built.
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct InlineHints {
    pub(crate) always: bool,
    pub(crate) hint: bool,
    pub(crate) never: bool,
    pub(crate) cold: bool,
    pub(crate) has_inline_asm: bool,
}

pub(crate) fn inline_mode(sess: &rustc_session::Session) -> InlineMode {
    for opt in &sess.opts.cg.llvm_args {
        if let Some(value) = opt.strip_prefix("clif-inline=") {
            return match value {
                "off" => InlineMode::Off,
                "always" => InlineMode::Always,
                "small" => InlineMode::Small(DEFAULT_SMALL),
                n => InlineMode::Small(n.parse().unwrap_or_else(|_| {
                    sess.dcx().fatal(format!(
                        "clif-inline: expected off, always, small or a number, got `{n}`"
                    ))
                })),
            };
        }
    }
    if sess.opts.optimize == rustc_session::config::OptLevel::No {
        InlineMode::Always
    } else {
        InlineMode::Small(DEFAULT_SMALL)
    }
}

/// Stack slot bytes a callee may bring into its caller.
const MAX_CALLEE_STACK: u32 = 512;
/// Stack slot bytes an `#[inline(always)]` callee may bring into its caller.
const MAX_ALWAYS_STACK: u32 = 4096;
/// A caller takes no more callees once it has this many instructions and has grown past
/// twice its own size (an `#[inline(always)]` callee is still taken).
const MAX_CALLER_INSTS: usize = 3000;

fn inst_count(func: &ir::Function) -> u32 {
    let mut n = 0;
    for block in func.layout.blocks() {
        n += func.layout.block_insts(block).count() as u32;
    }
    n
}

fn stack_bytes(func: &ir::Function) -> u32 {
    func.sized_stack_slots.values().map(|slot| slot.size).sum()
}

/// Whether anything in the body depends on it being a frame of its own.
fn has_frame_dependent_code(func: &ir::Function) -> bool {
    if !func.dynamic_stack_slots.is_empty() {
        return true;
    }
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            match func.dfg.insts[inst].opcode() {
                Opcode::GetFramePointer
                | Opcode::GetStackPointer
                | Opcode::GetReturnAddress
                | Opcode::ReturnCall
                | Opcode::ReturnCallIndirect
                | Opcode::StackSwitch => return true,
                _ => {}
            }
        }
    }
    false
}

struct Candidate {
    size: u32,
    stack: u32,
    hints: InlineHints,
    frame_dependent: bool,
    /// Has calls that must abort when they unwind (tagged plain calls, see
    /// `common::terminate_calls`).
    terminate_calls: bool,
}

fn callee_func_id(caller: &ir::Function, func_ref: ir::FuncRef) -> Option<FuncId> {
    match caller.dfg.ext_funcs[func_ref].name {
        ir::ExternalName::User(name) => {
            let name = &caller.params.user_named_funcs()[name];
            if name.namespace == 0 { Some(FuncId::from_u32(name.index)) } else { None }
        }
        _ => None,
    }
}

fn direct_callees(func: &ir::Function, out: &mut Vec<FuncId>) {
    out.clear();
    for block in func.layout.blocks() {
        for inst in func.layout.block_insts(block) {
            match func.dfg.insts[inst] {
                InstructionData::Call { func_ref, .. }
                | InstructionData::TryCall { func_ref, .. } => {
                    if let Some(id) = callee_func_id(func, func_ref) {
                        out.push(id);
                    }
                }
                _ => {}
            }
        }
    }
}

struct Inliner<'a> {
    mode: InlineMode,
    index: &'a FxHashMap<FuncId, usize>,
    funcs: &'a [CodegenedFunction],
    candidates: &'a [Candidate],
    /// Functions whose bodies are final (already processed): only those are inlined.
    done: &'a [bool],
    caller: usize,
    caller_start: u32,
    inlined: u32,
    /// The caller's stack slots each inlined call brought: (first slot index, count).
    groups: Vec<(u32, u32)>,
}

impl Inliner<'_> {
    fn wants(&self, caller: &ir::Function, callee: usize) -> bool {
        let c = &self.candidates[callee];
        if callee == self.caller
            || !self.done[callee]
            || c.frame_dependent
            || c.hints.has_inline_asm
        {
            return false;
        }
        if c.hints.always {
            return c.stack <= MAX_ALWAYS_STACK;
        }
        let InlineMode::Small(limit) = self.mode else { return false };
        if c.hints.never || c.hints.cold || c.stack > MAX_CALLEE_STACK {
            return false;
        }
        let limit = if c.hints.hint { limit * 2 } else { limit };
        if c.size > limit {
            return false;
        }
        let now = caller.dfg.num_insts();
        !(now > MAX_CALLER_INSTS && now as u32 > 2 * self.caller_start.max(1))
    }
}

impl Inline for Inliner<'_> {
    fn inline(
        &mut self,
        caller: &ir::Function,
        call_inst: ir::Inst,
        call_opcode: ir::Opcode,
        callee: ir::FuncRef,
        _call_args: &[ir::Value],
    ) -> InlineCommand<'_> {
        let Some(id) = callee_func_id(caller, callee) else { return InlineCommand::KeepCall };
        let Some(&idx) = self.index.get(&id) else { return InlineCommand::KeepCall };
        if !self.wants(caller, idx) {
            return InlineCommand::KeepCall;
        }
        // Calls that must abort when they unwind are plain calls with a tag, which inlining
        // would lose: at such a call site the callee's own calls would be listed as calls that
        // unwind, and at a `try_call` site the inliner turns the callee's tagged calls into
        // `try_call`s to the caller's landing pad.
        if caller.debug_tags.has(call_inst)
            || (call_opcode == Opcode::TryCall && self.candidates[idx].terminate_calls)
        {
            return InlineCommand::KeepCall;
        }
        let body = &self.funcs[idx].func;
        let sig = caller.dfg.ext_funcs[callee].signature;
        if caller.dfg.signatures[sig] != body.signature {
            return InlineCommand::KeepCall;
        }
        self.inlined += 1;
        if !body.sized_stack_slots.is_empty() {
            self.groups
                .push((caller.sized_stack_slots.len() as u32, body.sized_stack_slots.len() as u32));
        }
        // Bottom-up: the callee's own calls were already considered.
        InlineCommand::Inline { callee: Cow::Borrowed(body), visit_callee: false }
    }
}

/// Inlines calls between the functions of one codegen unit (see the module documentation).
pub(crate) fn inline_cgu(mode: InlineMode, funcs: &mut [CodegenedFunction]) {
    if mode == InlineMode::Off || funcs.len() < 2 {
        return;
    }
    // Nothing to do when no function could be inlined.
    if mode == InlineMode::Always && !funcs.iter().any(|f| f.inline_hints.always) {
        return;
    }
    let index: FxHashMap<FuncId, usize> =
        funcs.iter().enumerate().map(|(i, f)| (f.func_id, i)).collect();
    let mut candidates: Vec<Candidate> = funcs
        .iter()
        .map(|f| {
            if mode == InlineMode::Always && !f.inline_hints.always {
                // Never inlined in this mode: its size and body don't matter.
                return Candidate {
                    size: 0,
                    stack: 0,
                    hints: f.inline_hints,
                    frame_dependent: false,
                    terminate_calls: false,
                };
            }
            Candidate {
                size: inst_count(&f.func),
                stack: stack_bytes(&f.func),
                hints: f.inline_hints,
                frame_dependent: has_frame_dependent_code(&f.func),
                terminate_calls: !f.func.debug_tags.is_empty(),
            }
        })
        .collect();

    // Post-order over the call graph (iterative DFS), so callees come before their callers.
    let n = funcs.len();
    let mut callees: Vec<Vec<usize>> = Vec::with_capacity(n);
    let mut scratch = Vec::new();
    for f in funcs.iter() {
        direct_callees(&f.func, &mut scratch);
        let mut v: Vec<usize> = scratch.iter().filter_map(|id| index.get(id).copied()).collect();
        v.sort_unstable();
        v.dedup();
        callees.push(v);
    }
    let mut order = Vec::with_capacity(n);
    let mut state = vec![0u8; n]; // 0 new, 1 on stack, 2 finished
    for root in 0..n {
        if state[root] != 0 {
            continue;
        }
        let mut stack = vec![(root, 0usize)];
        state[root] = 1;
        while let Some(&mut (node, ref mut next)) = stack.last_mut() {
            if let Some(&child) = callees[node].get(*next) {
                *next += 1;
                if state[child] == 0 {
                    state[child] = 1;
                    stack.push((child, 0));
                }
            } else {
                state[node] = 2;
                order.push(node);
                stack.pop();
            }
        }
    }

    let mut done = vec![false; n];
    let mut ctx = cranelift_codegen::Context::new();
    for idx in order {
        // Without optimizations only `#[inline(always)]` callees are taken: a caller with none
        // has nothing to inline, so don't walk its body.
        let has_callee = if mode == InlineMode::Always {
            callees[idx].iter().any(|&c| c != idx && candidates[c].hints.always)
        } else {
            callees[idx].iter().any(|&c| c != idx)
        };
        if has_callee {
            ctx.clear();
            ctx.func = std::mem::replace(&mut funcs[idx].func, ir::Function::new());
            let caller_start = candidates[idx].size;
            let mut inliner = Inliner {
                mode,
                index: &index,
                funcs: &*funcs,
                candidates: &candidates,
                done: &done,
                caller: idx,
                caller_start,
                inlined: 0,
                groups: Vec::new(),
            };
            let res = ctx.inline(&mut inliner);
            let inlined = inliner.inlined;
            let groups = std::mem::take(&mut inliner.groups);
            if let Err(err) = res {
                panic!("inlining into {} failed: {err:?}", funcs[idx].symbol_name);
            }
            share_inlined_slots(&mut ctx.func, &groups);
            funcs[idx].func = std::mem::replace(&mut ctx.func, ir::Function::new());
            if inlined > 0 {
                candidates[idx].size = inst_count(&funcs[idx].func);
                candidates[idx].stack = stack_bytes(&funcs[idx].func);
                candidates[idx].frame_dependent = has_frame_dependent_code(&funcs[idx].func);
                candidates[idx].terminate_calls = !funcs[idx].func.debug_tags.is_empty();
            }
        }
        done[idx] = true;
    }
}

/// Lets the stack slots of different inlined calls share memory.
///
/// An inlined callee's slots hold its locals, which are dead once the call returns (nothing may
/// point into a returned-from frame), and the inlined bodies of two calls never run at the
/// same time: each call's slots are laid out in one area as the callee's own frame had them,
/// and all calls' areas start at the same address. Without this, every inlined call would add
/// its whole frame to the caller's, where LLVM-built code gets them coloured.
fn share_inlined_slots(func: &mut ir::Function, groups: &[(u32, u32)]) {
    if groups.len() < 2 {
        return;
    }
    // slot -> (offset in the shared area)
    let mut remap: FxHashMap<ir::StackSlot, u32> = FxHashMap::default();
    let mut area_size = 0u32;
    let mut area_align = 0u8;
    for &(first, count) in groups {
        let mut offset = 0u32;
        for i in first..first + count {
            let slot = ir::StackSlot::from_u32(i);
            let data = &func.sized_stack_slots[slot];
            if data.kind != ir::StackSlotKind::ExplicitSlot || data.key.is_some() {
                continue;
            }
            let align = 1u32 << data.align_shift;
            offset = (offset + align - 1) & !(align - 1);
            remap.insert(slot, offset);
            offset += data.size;
            area_align = area_align.max(data.align_shift);
        }
        area_size = area_size.max(offset);
    }
    if remap.is_empty() {
        return;
    }
    let area = func.create_sized_stack_slot(ir::StackSlotData::new(
        ir::StackSlotKind::ExplicitSlot,
        area_size,
        area_align,
    ));
    let insts: Vec<ir::Inst> =
        func.layout.blocks().flat_map(|block| func.layout.block_insts(block)).collect();
    for inst in insts {
        if let InstructionData::StackAddr { stack_slot, offset, .. } = &mut func.dfg.insts[inst] {
            if let Some(&base) = remap.get(stack_slot) {
                *stack_slot = area;
                *offset = ir::immediates::Offset32::new(i32::from(*offset) + base as i32);
            }
        }
    }
    for (&slot, _) in &remap {
        func.sized_stack_slots[slot].size = 0;
        func.sized_stack_slots[slot].align_shift = 0;
    }
}
