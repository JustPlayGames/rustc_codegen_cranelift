//! User variables and arguments (`DW_TAG_variable`/`DW_TAG_formal_parameter`, CodeView
//! `S_LOCAL`), for full debuginfo.
//!
//! Only variables whose value lives in a stack slot get a location: unoptimized builds with full
//! debuginfo keep every user variable in memory for this (`analyze::debug_variable_locals`), so
//! each one is at a fixed offset from the stack pointer once the prologue has run. Variables of
//! optimized code that live in registers are left out.

use cranelift_codegen::{MachBufferFrameLayout, MachSrcLoc};
use gimli::write::{Address, AttributeValue, Expression, FileId, Range, RangeList, UnitEntryId};
use rustc_session::config::DebugInfo;

use super::emit::address_for_func;
use super::{DebugContext, FunctionDebugContext, TypeDebugContext};
use crate::prelude::*;

pub(crate) struct DebugVariable {
    pub(super) name: String,
    /// 1-based argument index for function parameters.
    pub(super) arg_index: Option<u16>,
    pub(super) loc: (FileId, u64, u64),
    pub(super) slot: StackSlot,
    pub(super) offset: i32,
    pub(super) dw_type: Option<UnitEntryId>,
    pub(super) cv_type: u32,
    /// The MIR scope the variable is declared in (0: the function's outermost scope).
    pub(super) scope: u32,
}

impl DebugVariable {
    /// Offset from the stack pointer after the prologue.
    pub(super) fn sp_offset(&self, frame_layout: &MachBufferFrameLayout) -> Option<i64> {
        let slot = frame_layout.stackslots.get(self.slot)?;
        Some(i64::from(slot.offset) + i64::from(self.offset))
    }
}

/// Records the user variables of the function being compiled, once its locals have places.
pub(crate) fn define_variables<'tcx>(
    fx: &mut FunctionCx<'_, '_, 'tcx>,
    type_dbg: &mut TypeDebugContext<'tcx>,
) {
    let tcx = fx.tcx;
    if tcx.sess.opts.debuginfo != DebugInfo::Full {
        return;
    }
    let mut variables = Vec::new();
    let mut params_seen = Vec::new();
    for var in &fx.mir.var_debug_info {
        if var.composite.is_some() {
            continue;
        }
        let VarDebugInfoContents::Place(place) = var.value else { continue };
        // Variables of macro expansions (`format_args!`'s `args`) would fill every frame with
        // look-alike names: variables are described at function scope, without lexical blocks.
        if var.source_info.span.from_expansion() {
            continue;
        }
        // Bodies that are replaced by a trap have no locals.
        let Some(local_place) = fx.local_map.get(place.local) else { continue };
        let Some((slot, mut offset)) = local_place.debug_stack_location() else { continue };
        let mut layout = fx.layout_of(fx.monomorphize(fx.mir.local_decls[place.local].ty));
        let mut direct = true;
        for elem in place.projection {
            match elem {
                ProjectionElem::Field(field, _) => {
                    offset += i32::try_from(layout.fields.offset(field.index()).bytes()).unwrap();
                    layout = layout.field(&*fx, field.index());
                }
                _ => {
                    direct = false;
                    break;
                }
            }
        }
        if !direct || layout.is_unsized() || layout.size.bytes() == 0 {
            continue;
        }
        let arg_index = if place.projection.is_empty() { var.argument_index } else { None };
        if let Some(index) = arg_index {
            // MIR inlining can repeat an argument index: keep the first.
            if params_seen.contains(&index) {
                continue;
            }
            params_seen.push(index);
        }

        let debug_context = fx.debug_context.as_deref_mut().unwrap();
        let loc = debug_context.get_span_loc(tcx, fx.mir.span, var.source_info.span);
        let (dw_type, cv_type) = if debug_context.codeview.is_some() {
            (None, debug_context.codeview_type(tcx, type_dbg, layout.ty))
        } else {
            (Some(debug_context.debug_type(tcx, type_dbg, layout.ty)), 0)
        };
        variables.push(DebugVariable {
            name: var.name.to_string(),
            arg_index,
            loc,
            slot,
            offset,
            dw_type,
            cv_type,
            scope: if arg_index.is_some() { 0 } else { var.source_info.scope.as_u32() },
        });
    }
    let scope_parents =
        fx.mir.source_scopes.iter().map(|scope| scope.parent_scope.map(|p| p.as_u32())).collect();
    // Parameters first, in order, then the other variables in declaration order.
    variables.sort_by_key(|var| var.arg_index.map_or(u32::MAX, u32::from));
    let func_debug_cx = fx.func_debug_cx.as_mut().unwrap();
    func_debug_cx.variables = variables;
    func_debug_cx.scope_parents = scope_parents;
}

impl FunctionDebugContext {
    /// The code ranges of each MIR scope, its nested scopes included, sorted and merged.
    pub(super) fn scope_ranges(&self, context: &Context) -> Vec<Vec<(u32, u32)>> {
        let mut ranges = vec![Vec::new(); self.scope_parents.len()];
        if ranges.is_empty() {
            return ranges;
        }
        let mcr = context.compiled_code().unwrap();
        for &MachSrcLoc { start, end, loc } in mcr.buffer.get_srclocs_sorted() {
            let loc = loc.as_abs();
            if loc.is_default() || start == end {
                continue;
            }
            let mut scope = Some(self.source_loc_set[loc.bits() as usize].3);
            while let Some(s) = scope {
                let s = s as usize;
                if s >= ranges.len() {
                    break;
                }
                ranges[s].push((start, end));
                scope = self.scope_parents[s];
            }
        }
        for list in &mut ranges {
            list.sort_unstable();
            let mut merged: Vec<(u32, u32)> = Vec::with_capacity(list.len());
            for &(start, end) in list.iter() {
                match merged.last_mut() {
                    Some(last) if start <= last.1 => last.1 = last.1.max(end),
                    _ => merged.push((start, end)),
                }
            }
            *list = merged;
        }
        ranges
    }
}

impl DebugContext {
    /// Variables of nested MIR scopes go into `DW_TAG_lexical_block`s covering their scope's
    /// code, so that debuggers show them only there (and shadowed names resolve).
    pub(super) fn define_dwarf_variables(
        &mut self,
        entry_id: UnitEntryId,
        func_id: FuncId,
        func_debug_cx: &FunctionDebugContext,
        context: &Context,
    ) {
        let variables = &func_debug_cx.variables;
        let Some(frame_layout) = context.compiled_code().unwrap().buffer.frame_layout() else {
            return;
        };
        if variables.is_empty() {
            return;
        }
        let scope_ranges = func_debug_cx.scope_ranges(context);
        let mut blocks: FxHashMap<u32, UnitEntryId> = FxHashMap::default();
        for var in variables {
            let Some(sp_offset) = var.sp_offset(frame_layout) else { continue };
            let Some(parent) = self.lexical_block(
                entry_id,
                func_id,
                var.scope,
                &func_debug_cx.scope_parents,
                &scope_ranges,
                &mut blocks,
            ) else {
                continue;
            };
            let tag = if var.arg_index.is_some() {
                gimli::DW_TAG_formal_parameter
            } else {
                gimli::DW_TAG_variable
            };
            let var_id = self.dwarf.unit.add(parent, tag);
            let name = self.dwarf.strings.add(var.name.as_str());
            let entry = self.dwarf.unit.get_mut(var_id);
            let mut location = Expression::new();
            // DW_AT_frame_base is the stack pointer.
            location.op_fbreg(sp_offset);
            entry.set(gimli::DW_AT_location, AttributeValue::Exprloc(location));
            entry.set(gimli::DW_AT_name, AttributeValue::StringRef(name));
            entry.set(gimli::DW_AT_decl_file, AttributeValue::FileIndex(Some(var.loc.0)));
            entry.set(gimli::DW_AT_decl_line, AttributeValue::Udata(var.loc.1));
            if let Some(dw_type) = var.dw_type {
                entry.set(gimli::DW_AT_type, AttributeValue::UnitRef(dw_type));
            }
        }
    }
}

impl DebugContext {
    /// The DIE to put a variable of `scope` under: the subprogram for the outermost scope, else a
    /// lexical block nested like the scopes. `None` if the scope has no code.
    fn lexical_block(
        &mut self,
        entry_id: UnitEntryId,
        func_id: FuncId,
        scope: u32,
        scope_parents: &[Option<u32>],
        scope_ranges: &[Vec<(u32, u32)>],
        blocks: &mut FxHashMap<u32, UnitEntryId>,
    ) -> Option<UnitEntryId> {
        let index = scope as usize;
        let Some(&parent_scope) = scope_parents.get(index) else { return Some(entry_id) };
        let Some(parent_scope) = parent_scope else { return Some(entry_id) };
        if let Some(&block) = blocks.get(&scope) {
            return Some(block);
        }
        let ranges = &scope_ranges[index];
        if ranges.is_empty() {
            return None;
        }
        let parent = self.lexical_block(
            entry_id,
            func_id,
            parent_scope,
            scope_parents,
            scope_ranges,
            blocks,
        )?;
        let block = self.dwarf.unit.add(parent, gimli::DW_TAG_lexical_block);
        let Address::Symbol { symbol, .. } = address_for_func(func_id) else { unreachable!() };
        let list = RangeList(
            ranges
                .iter()
                .map(|&(start, end)| Range::StartEnd {
                    begin: Address::Symbol { symbol, addend: i64::from(start) },
                    end: Address::Symbol { symbol, addend: i64::from(end) },
                })
                .collect(),
        );
        let list = self.dwarf.unit.ranges.add(list);
        self.dwarf.unit.get_mut(block).set(gimli::DW_AT_ranges, AttributeValue::RangeListRef(list));
        blocks.insert(scope, block);
        Some(block)
    }
}
