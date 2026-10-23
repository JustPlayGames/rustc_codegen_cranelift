//! SSA analysis

use rustc_index::IndexVec;
use rustc_middle::mir::StatementKind::*;
use rustc_middle::mir::visit::{PlaceContext, Visitor};

use crate::prelude::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum SsaKind {
    NotSsa,
    MaybeSsa,
}

impl SsaKind {
    pub(crate) fn is_ssa<'tcx>(self, fx: &FunctionCx<'_, '_, 'tcx>, ty: Ty<'tcx>) -> bool {
        self == SsaKind::MaybeSsa && ssa_shape(fx, fx.layout_of(ty)).is_some()
    }

    /// `is_ssa` for a type whose layout is at hand.
    pub(crate) fn is_ssa_layout<'tcx>(
        self,
        fx: &FunctionCx<'_, '_, 'tcx>,
        layout: TyAndLayout<'tcx>,
    ) -> bool {
        self == SsaKind::MaybeSsa && ssa_shape(fx, layout).is_some()
    }
}

/// How the value of a local kept in Cranelift variables is split: any sized type whose layout is
/// one scalar or a pair of scalars, so besides integers, floats and pointers also newtypes
/// (`NonNull`, `Unique`), small structs and tuples, and enums whose tag or niche shares the
/// scalars with at most one field (`Option<&T>`, `Option<NonZero>`, `Result<u32, ()>`,
/// `Ordering`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum SsaShape {
    /// One variable, holding a scalar of this size.
    One(Size),
    /// Two variables: the scalar at offset 0 (`a` bytes) and the one at `b_offset` (`b` bytes).
    Pair { a: Size, b_offset: Size, b: Size },
}

/// Where a field of a value or place kept in variables lives.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum SsaField {
    /// A zero-sized field, which needs no variable.
    Zst,
    /// All of the variables (a newtype's field, the only field of an enum variant).
    Same,
    /// The first variable of a pair.
    First,
    /// The second variable of a pair.
    Second,
}

pub(crate) fn ssa_shape<'tcx>(
    fx: &FunctionCx<'_, '_, 'tcx>,
    layout: TyAndLayout<'tcx>,
) -> Option<SsaShape> {
    if layout.is_unsized() || layout.is_uninhabited() {
        return None;
    }
    // A coroutine is laid out around its saved locals; leave it in memory.
    if let ty::Coroutine(..) = layout.ty.kind() {
        return None;
    }
    match layout.backend_repr {
        BackendRepr::Scalar(scalar) if scalar.size(&fx.tcx) == layout.size => {
            Some(SsaShape::One(layout.size))
        }
        BackendRepr::ScalarPair { a, b, b_offset } => {
            Some(SsaShape::Pair { a: a.size(&fx.tcx), b_offset, b: b.size(&fx.tcx) })
        }
        _ => None,
    }
}

/// The variables that field `field` of a value or place of `layout`, kept in variables split as
/// `shape`, lives in, with the field's own shape and layout, or `None` when the field does not
/// line up with the variables. A place of shape `One` is one scalar and the offsets of its fields
/// are relative to it; a place of shape `Pair` always starts where its local starts, so the
/// fields of an enum variant (a downcast of the local) are at their offsets in the enum.
pub(crate) fn ssa_field<'tcx>(
    fx: &FunctionCx<'_, '_, 'tcx>,
    shape: SsaShape,
    layout: TyAndLayout<'tcx>,
    field: usize,
) -> Option<(SsaField, SsaShape, TyAndLayout<'tcx>)> {
    let field_layout = layout.field(fx, field);
    if field_layout.is_zst() {
        return Some((SsaField::Zst, shape, field_layout));
    }
    if field_layout.is_unsized() {
        return None;
    }
    let offset = layout.fields.offset(field);
    let is_scalar = |size: Size| {
        field_layout.size == size
            && match field_layout.backend_repr {
                BackendRepr::Scalar(scalar) => scalar.size(&fx.tcx) == size,
                _ => false,
            }
    };
    let (place, field_shape) = match shape {
        SsaShape::One(size) if offset == Size::ZERO && is_scalar(size) => (SsaField::Same, shape),
        SsaShape::Pair { a, b_offset, b } => {
            if offset == Size::ZERO && ssa_shape(fx, field_layout) == Some(shape) {
                (SsaField::Same, shape)
            } else if offset == Size::ZERO && is_scalar(a) {
                (SsaField::First, SsaShape::One(a))
            } else if offset == b_offset && is_scalar(b) {
                (SsaField::Second, SsaShape::One(b))
            } else {
                return None;
            }
        }
        SsaShape::One(_) => return None,
    };
    Some((place, field_shape, field_layout))
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

    keep_projected_locals_in_memory(fx, &mut flag_map);

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

/// Takes out of SSA the locals that some place projects in a way their variables can't follow:
/// an index or subslice, or a field that is not one of the scalars (see [`ssa_field`]).
fn keep_projected_locals_in_memory(
    fx: &FunctionCx<'_, '_, '_>,
    flag_map: &mut IndexVec<Local, SsaKind>,
) {
    struct Projections<'a, 'm, 'c, 'tcx> {
        fx: &'a FunctionCx<'m, 'c, 'tcx>,
        flag_map: &'a mut IndexVec<Local, SsaKind>,
    }
    impl<'tcx> Visitor<'tcx> for Projections<'_, '_, '_, 'tcx> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
            if place.projection.is_empty()
                || matches!(context, PlaceContext::NonUse(_))
                || self.flag_map[place.local] == SsaKind::NotSsa
            {
                return;
            }
            let fx = self.fx;
            let layout = fx.local_layouts[place.local];
            let Some(shape) = ssa_shape(fx, layout) else { return };
            if !projection_in_vars(fx, shape, layout, place.projection) {
                self.flag_map[place.local] = SsaKind::NotSsa;
            }
        }
    }

    Projections { fx, flag_map }.visit_body(fx.mir);
}

/// Whether the projections of a place based on a local in variables stay in its variables up to
/// the first deref (from there on the place is the memory the pointer points to).
fn projection_in_vars<'tcx>(
    fx: &FunctionCx<'_, '_, 'tcx>,
    mut shape: SsaShape,
    mut layout: TyAndLayout<'tcx>,
    projection: &[PlaceElem<'tcx>],
) -> bool {
    for elem in projection {
        match *elem {
            PlaceElem::Deref => return true,
            PlaceElem::Field(field, _) => match ssa_field(fx, shape, layout, field.index()) {
                // A zero-sized place needs no memory.
                Some((SsaField::Zst, _, _)) => return true,
                Some((_, field_shape, field_layout)) => {
                    shape = field_shape;
                    layout = field_layout;
                }
                None => return false,
            },
            PlaceElem::Downcast(_, variant) => layout = layout.for_variant(fx, variant),
            _ => return false,
        }
    }
    true
}
