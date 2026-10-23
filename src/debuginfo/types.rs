// Adapted from https://github.com/rust-lang/rust/blob/10a7aa14fed9b528b74b0f098c4899c37c09a9c7/compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs

use gimli::write::{AttributeValue, UnitEntryId};
use rustc_abi::{FieldsShape, TagEncoding, Variants};
use rustc_codegen_ssa::debuginfo::type_names;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::layout::LayoutOf;
use rustc_middle::ty::{self, Ty, TyCtxt};

use crate::prelude::{FIRST_VARIANT, FieldIdx, TyAndLayout};
use crate::{DebugContext, FullyMonomorphizedLayoutCx};

#[derive(Default)]
pub(crate) struct TypeDebugContext<'tcx> {
    type_map: FxHashMap<Ty<'tcx>, UnitEntryId>,
    /// CodeView type indices (MSVC targets).
    pub(super) cv_type_map: FxHashMap<Ty<'tcx>, u32>,
}

/// Returns from the enclosing function if the type debuginfo node with the given
/// unique ID can be found in the type map.
macro_rules! return_if_type_created_in_meantime {
    ($type_dbg:expr, $ty:expr) => {
        if let Some(&type_id) = $type_dbg.type_map.get(&$ty) {
            return type_id;
        }
    };
}

impl DebugContext {
    pub(crate) fn debug_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ty: Ty<'tcx>,
    ) -> UnitEntryId {
        if let Some(&type_id) = type_dbg.type_map.get(&ty) {
            return type_id;
        }

        let type_id = match ty.kind() {
            ty::Never | ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => {
                self.basic_type(tcx, ty)
            }
            ty::Tuple(elems) if elems.is_empty() => self.basic_type(tcx, ty),
            ty::Array(elem_ty, len) => self.array_type(
                tcx,
                type_dbg,
                ty,
                *elem_ty,
                len.try_to_target_usize(tcx).expect("expected monomorphic const in codegen"),
            ),
            // ty::Slice(_) | ty::Str
            // ty::Dynamic
            // ty::Foreign
            ty::RawPtr(pointee_type, _) | ty::Ref(_, pointee_type, _) => {
                self.pointer_type(tcx, type_dbg, ty, *pointee_type)
            }
            // `Box<T>` with a zero-sized allocator looks like a pointer, as LLVM describes it.
            ty::Adt(def, args)
                if def.is_box()
                    && args.get(1).is_none_or(|arg| {
                        FullyMonomorphizedLayoutCx(tcx).layout_of(arg.expect_ty()).is_1zst()
                    }) =>
            {
                self.pointer_type(tcx, type_dbg, ty, args.type_at(0))
            }
            ty::FnPtr(..) => self.opaque_pointer_type(tcx, ty),
            // Pattern types (`NonNull`'s `*const T is !null`) look like their base type.
            ty::Pat(base, _) => self.debug_type(tcx, type_dbg, *base),
            ty::Tuple(components) => self.tuple_type(tcx, type_dbg, ty, components),
            ty::Adt(..) | ty::Closure(..) | ty::CoroutineClosure(..) | ty::Coroutine(..) => {
                // Inserts itself into the type map before its fields, for recursive types.
                return self.adt_type(tcx, type_dbg, ty);
            }
            _ => self.placeholder_for_type(tcx, type_dbg, ty),
        };

        type_dbg.type_map.insert(ty, type_id);

        type_id
    }

    fn basic_type<'tcx>(&mut self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> UnitEntryId {
        let (name, encoding) = match ty.kind() {
            ty::Never => ("!", gimli::DW_ATE_unsigned),
            ty::Tuple(elems) if elems.is_empty() => ("()", gimli::DW_ATE_unsigned),
            ty::Bool => ("bool", gimli::DW_ATE_boolean),
            ty::Char => ("char", gimli::DW_ATE_UTF),
            ty::Int(int_ty) => (int_ty.name_str(), gimli::DW_ATE_signed),
            ty::Uint(uint_ty) => (uint_ty.name_str(), gimli::DW_ATE_unsigned),
            ty::Float(float_ty) => (float_ty.name_str(), gimli::DW_ATE_float),
            _ => unreachable!(),
        };

        let type_id = self.dwarf.unit.add(self.dwarf.unit.root(), gimli::DW_TAG_base_type);
        let type_entry = self.dwarf.unit.get_mut(type_id);
        type_entry.set(gimli::DW_AT_name, AttributeValue::StringRef(self.dwarf.strings.add(name)));
        type_entry.set(gimli::DW_AT_encoding, AttributeValue::Encoding(encoding));
        type_entry.set(
            gimli::DW_AT_byte_size,
            AttributeValue::Udata(FullyMonomorphizedLayoutCx(tcx).layout_of(ty).size.bytes()),
        );

        type_id
    }

    fn array_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        array_ty: Ty<'tcx>,
        elem_ty: Ty<'tcx>,
        len: u64,
    ) -> UnitEntryId {
        let elem_dw_ty = self.debug_type(tcx, type_dbg, elem_ty);

        return_if_type_created_in_meantime!(type_dbg, array_ty);

        let array_type_id = self.dwarf.unit.add(self.dwarf.unit.root(), gimli::DW_TAG_array_type);
        let array_type_entry = self.dwarf.unit.get_mut(array_type_id);
        array_type_entry.set(gimli::DW_AT_type, AttributeValue::UnitRef(elem_dw_ty));

        let subrange_id = self.dwarf.unit.add(array_type_id, gimli::DW_TAG_subrange_type);
        let subrange_entry = self.dwarf.unit.get_mut(subrange_id);
        subrange_entry
            .set(gimli::DW_AT_type, AttributeValue::UnitRef(self.array_size_type.unwrap()));
        subrange_entry.set(gimli::DW_AT_lower_bound, AttributeValue::Udata(0));
        subrange_entry.set(gimli::DW_AT_count, AttributeValue::Udata(len));

        array_type_id
    }

    fn pointer_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ptr_type: Ty<'tcx>,
        pointee_type: Ty<'tcx>,
    ) -> UnitEntryId {
        // `&[T]` points at `T`, `&str` at `u8`.
        let pointee_dw_ty = match pointee_type.kind() {
            ty::Slice(elem) => self.debug_type(tcx, type_dbg, *elem),
            ty::Str => self.debug_type(tcx, type_dbg, tcx.types.u8),
            _ => self.debug_type(tcx, type_dbg, pointee_type),
        };

        return_if_type_created_in_meantime!(type_dbg, ptr_type);

        let name = type_names::compute_debuginfo_type_name(tcx, ptr_type, true);

        if !tcx.type_has_metadata(pointee_type, ty::TypingEnv::fully_monomorphized()) {
            let pointer_type_id =
                self.dwarf.unit.add(self.dwarf.unit.root(), gimli::DW_TAG_pointer_type);
            let pointer_entry = self.dwarf.unit.get_mut(pointer_type_id);
            pointer_entry.set(gimli::DW_AT_type, AttributeValue::UnitRef(pointee_dw_ty));
            pointer_entry
                .set(gimli::DW_AT_name, AttributeValue::StringRef(self.dwarf.strings.add(name)));

            pointer_type_id
        } else {
            self.wide_pointer_type(tcx, type_dbg, pointee_type, pointee_dw_ty, name)
        }
    }

    fn tuple_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        tuple_type: Ty<'tcx>,
        components: &'tcx [Ty<'tcx>],
    ) -> UnitEntryId {
        let components = components
            .iter()
            .map(|&ty| (ty, self.debug_type(tcx, type_dbg, ty)))
            .collect::<Vec<_>>();

        return_if_type_created_in_meantime!(type_dbg, tuple_type);

        let name = type_names::compute_debuginfo_type_name(tcx, tuple_type, false);
        let layout = FullyMonomorphizedLayoutCx(tcx).layout_of(tuple_type);

        let tuple_type_id =
            self.dwarf.unit.add(self.dwarf.unit.root(), gimli::DW_TAG_structure_type);
        let tuple_entry = self.dwarf.unit.get_mut(tuple_type_id);
        tuple_entry.set(gimli::DW_AT_name, AttributeValue::StringRef(self.dwarf.strings.add(name)));
        tuple_entry.set(gimli::DW_AT_byte_size, AttributeValue::Udata(layout.size.bytes()));
        tuple_entry.set(gimli::DW_AT_alignment, AttributeValue::Udata(layout.align.bytes()));

        for (i, (ty, dw_ty)) in components.into_iter().enumerate() {
            let member_id = self.dwarf.unit.add(tuple_type_id, gimli::DW_TAG_member);
            let member_entry = self.dwarf.unit.get_mut(member_id);
            member_entry.set(
                gimli::DW_AT_name,
                AttributeValue::StringRef(self.dwarf.strings.add(format!("__{i}"))),
            );
            member_entry.set(gimli::DW_AT_type, AttributeValue::UnitRef(dw_ty));
            member_entry.set(
                gimli::DW_AT_alignment,
                AttributeValue::Udata(FullyMonomorphizedLayoutCx(tcx).layout_of(ty).align.bytes()),
            );
            member_entry.set(
                gimli::DW_AT_data_member_location,
                AttributeValue::Udata(layout.fields.offset(i).bytes()),
            );
        }

        tuple_type_id
    }

    /// `{ data_ptr, length }` for slices and `str`, `{ pointer, vtable }` for trait objects, as
    /// LLVM describes them (the debuggers' Rust support reads these names).
    fn wide_pointer_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        pointee_type: Ty<'tcx>,
        pointee_dw_ty: UnitEntryId,
        name: String,
    ) -> UnitEntryId {
        let cx = FullyMonomorphizedLayoutCx(tcx);
        // A `Box` with a zero-sized allocator has the layout of the raw pointer.
        let layout = cx.layout_of(Ty::new_mut_ptr(tcx, pointee_type));
        let extra = layout.field(&cx, 1);
        let extra_dw_ty = self.debug_type(tcx, type_dbg, extra.ty);
        let slice_like = matches!(
            tcx.struct_tail_for_codegen(pointee_type, ty::TypingEnv::fully_monomorphized()).kind(),
            ty::Slice(_) | ty::Str
        );
        let (addr_name, extra_name) =
            if slice_like { ("data_ptr", "length") } else { ("pointer", "vtable") };

        let root = self.dwarf.unit.root();
        let data_ptr_id = self.dwarf.unit.add(root, gimli::DW_TAG_pointer_type);
        self.dwarf
            .unit
            .get_mut(data_ptr_id)
            .set(gimli::DW_AT_type, AttributeValue::UnitRef(pointee_dw_ty));

        let struct_id = self.dwarf.unit.add(root, gimli::DW_TAG_structure_type);
        let name_id = self.dwarf.strings.add(name);
        let entry = self.dwarf.unit.get_mut(struct_id);
        entry.set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
        entry.set(gimli::DW_AT_byte_size, AttributeValue::Udata(layout.size.bytes()));
        entry.set(gimli::DW_AT_alignment, AttributeValue::Udata(layout.align.bytes()));
        self.add_member(
            struct_id,
            addr_name,
            data_ptr_id,
            layout.fields.offset(0).bytes(),
            layout.field(&cx, 0).align.bytes(),
        );
        self.add_member(
            struct_id,
            extra_name,
            extra_dw_ty,
            layout.fields.offset(1).bytes(),
            extra.align.bytes(),
        );
        struct_id
    }

    fn opaque_pointer_type<'tcx>(&mut self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> UnitEntryId {
        let name = type_names::compute_debuginfo_type_name(tcx, ty, true);
        let id = self.dwarf.unit.add(self.dwarf.unit.root(), gimli::DW_TAG_pointer_type);
        let name_id = self.dwarf.strings.add(name);
        self.dwarf.unit.get_mut(id).set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
        id
    }

    fn add_member(
        &mut self,
        parent: UnitEntryId,
        name: &str,
        ty: UnitEntryId,
        offset: u64,
        align: u64,
    ) -> UnitEntryId {
        let member_id = self.dwarf.unit.add(parent, gimli::DW_TAG_member);
        let name_id = self.dwarf.strings.add(name);
        let member = self.dwarf.unit.get_mut(member_id);
        member.set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
        member.set(gimli::DW_AT_type, AttributeValue::UnitRef(ty));
        member.set(gimli::DW_AT_alignment, AttributeValue::Udata(align));
        member.set(gimli::DW_AT_data_member_location, AttributeValue::Udata(offset));
        member_id
    }

    fn new_struct_entry(
        &mut self,
        parent: UnitEntryId,
        tag: gimli::DwTag,
        name: &str,
        size: u64,
        align: u64,
    ) -> UnitEntryId {
        let id = self.dwarf.unit.add(parent, tag);
        let name_id = self.dwarf.strings.add(name);
        let entry = self.dwarf.unit.get_mut(id);
        entry.set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
        entry.set(gimli::DW_AT_byte_size, AttributeValue::Udata(size));
        entry.set(gimli::DW_AT_alignment, AttributeValue::Udata(align));
        id
    }

    /// Structs, unions, closures and enums: their fields, and for enums with data the variants
    /// in a `DW_TAG_variant_part` as LLVM writes them.
    fn adt_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ty: Ty<'tcx>,
    ) -> UnitEntryId {
        let cx = FullyMonomorphizedLayoutCx(tcx);
        let layout = cx.layout_of(ty);
        // Nested in the namespaces of their path, with their unqualified name, as LLVM writes
        // them: debuggers show the qualified name, which the Rust pretty printers match.
        let name = type_names::compute_debuginfo_type_name(tcx, ty, false);
        let root = match ty.kind() {
            ty::Adt(adt, _) => match tcx.opt_parent(adt.did()) {
                Some(parent) => self.item_namespace(tcx, parent),
                None => self.dwarf.unit.root(),
            },
            ty::Closure(def_id, _) | ty::CoroutineClosure(def_id, _) | ty::Coroutine(def_id, _) => {
                self.item_namespace(tcx, *def_id)
            }
            _ => self.dwarf.unit.root(),
        };
        let size = layout.size.bytes();
        let align = layout.align.bytes();

        let adt = match ty.kind() {
            ty::Adt(adt, _) => Some(*adt),
            _ => None,
        };

        // Fieldless enums with a plain tag: an enumeration type.
        if let Some(adt) = adt
            && adt.is_enum()
            && adt.variants().iter().all(|v| v.fields.is_empty())
            && let Variants::Multiple { tag, tag_encoding: TagEncoding::Direct, .. } =
                &layout.variants
        {
            let base_ty = tag_int_type(tcx, tag.primitive());
            let base_dw_ty = self.debug_type(tcx, type_dbg, base_ty);
            if let Some(&id) = type_dbg.type_map.get(&ty) {
                return id;
            }
            let enum_id =
                self.new_struct_entry(root, gimli::DW_TAG_enumeration_type, &name, size, align);
            self.dwarf
                .unit
                .get_mut(enum_id)
                .set(gimli::DW_AT_type, AttributeValue::UnitRef(base_dw_ty));
            type_dbg.type_map.insert(ty, enum_id);
            let signed = matches!(tag.primitive(), rustc_abi::Primitive::Int(_, true));
            for (index, variant) in adt.variants().iter_enumerated() {
                let value = ty.discriminant_for_variant(tcx, index).unwrap().val;
                let value = tag.size(&tcx).truncate(value);
                let enumerator = self.dwarf.unit.add(enum_id, gimli::DW_TAG_enumerator);
                let name_id = self.dwarf.strings.add(variant.name.as_str());
                let entry = self.dwarf.unit.get_mut(enumerator);
                entry.set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
                let value = if signed {
                    AttributeValue::Sdata(tag.size(&tcx).sign_extend(value) as i64)
                } else {
                    AttributeValue::Udata(value as u64)
                };
                entry.set(gimli::DW_AT_const_value, value);
            }
            return enum_id;
        }

        let tag = if matches!(layout.variants, Variants::Multiple { .. }) && adt.is_some() {
            gimli::DW_TAG_structure_type
        } else if adt.is_some_and(|adt| adt.is_union()) {
            gimli::DW_TAG_union_type
        } else {
            gimli::DW_TAG_structure_type
        };
        let struct_id = self.new_struct_entry(root, tag, &name, size, align);
        type_dbg.type_map.insert(ty, struct_id);
        self.add_template_params(tcx, type_dbg, struct_id, ty);

        match &layout.variants {
            Variants::Multiple { tag, tag_encoding, tag_field, variants }
                if let Some(adt) = adt =>
            {
                // Variant structs, nested in the enum's type as LLVM nests them.
                let mut variant_structs = Vec::new();
                for (index, _) in variants.iter_enumerated() {
                    let variant_layout = layout.for_variant(&cx, index);
                    let variant = adt.variant(index);
                    let id = self.new_struct_entry(
                        struct_id,
                        gimli::DW_TAG_structure_type,
                        variant.name.as_str(),
                        size,
                        align,
                    );
                    self.add_fields(tcx, type_dbg, id, variant_layout, Some(variant), None);
                    variant_structs.push((index, variant.name, id));
                }

                let tag_ty = tag_int_type(tcx, tag.primitive());
                let tag_dw_ty = self.debug_type(tcx, type_dbg, tag_ty);
                let variant_part = self.dwarf.unit.add(struct_id, gimli::DW_TAG_variant_part);
                let discr = self.dwarf.unit.add(variant_part, gimli::DW_TAG_member);
                let discr_entry = self.dwarf.unit.get_mut(discr);
                discr_entry.set(gimli::DW_AT_type, AttributeValue::UnitRef(tag_dw_ty));
                discr_entry
                    .set(gimli::DW_AT_alignment, AttributeValue::Udata(tag.size(&tcx).bytes()));
                discr_entry.set(
                    gimli::DW_AT_data_member_location,
                    AttributeValue::Udata(layout.fields.offset(tag_field.as_usize()).bytes()),
                );
                discr_entry.set(gimli::DW_AT_artificial, AttributeValue::Flag(true));
                self.dwarf
                    .unit
                    .get_mut(variant_part)
                    .set(gimli::DW_AT_discr, AttributeValue::UnitRef(discr));

                for (index, variant_name, variant_struct) in variant_structs {
                    let discr_value = match tag_encoding {
                        TagEncoding::Direct => {
                            let value = ty.discriminant_for_variant(tcx, index).unwrap().val;
                            Some(tag.size(&tcx).truncate(value))
                        }
                        TagEncoding::Niche { untagged_variant, niche_variants, niche_start } => {
                            if index == *untagged_variant {
                                None
                            } else {
                                let value = (index.as_u32() as u128)
                                    .wrapping_sub(niche_variants.start.as_u32() as u128)
                                    .wrapping_add(*niche_start);
                                Some(tag.size(&tcx).truncate(value))
                            }
                        }
                    };
                    let variant_id = self.dwarf.unit.add(variant_part, gimli::DW_TAG_variant);
                    if let Some(value) = discr_value {
                        self.dwarf
                            .unit
                            .get_mut(variant_id)
                            .set(gimli::DW_AT_discr_value, AttributeValue::Udata(value as u64));
                    }
                    self.add_member(variant_id, variant_name.as_str(), variant_struct, 0, align);
                }
            }
            _ => {
                let variant = match adt {
                    Some(adt) if !adt.is_enum() => Some(adt.non_enum_variant()),
                    Some(adt) if adt.variants().len() == 1 => Some(adt.variant(FIRST_VARIANT)),
                    _ => None,
                };
                let upvar_names = match ty.kind() {
                    ty::Closure(def_id, _) | ty::CoroutineClosure(def_id, _) => {
                        Some(tcx.closure_saved_names_of_captured_variables(*def_id))
                    }
                    _ => None,
                };
                self.add_fields(tcx, type_dbg, struct_id, layout, variant, upvar_names);
            }
        }
        struct_id
    }

    /// `DW_TAG_template_type_parameter`s of a generic ADT: the Rust pretty printers read a
    /// `Vec`'s or a `HashMap`'s element types from them.
    fn add_template_params<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        parent: UnitEntryId,
        ty: Ty<'tcx>,
    ) {
        let ty::Adt(def, args) = *ty.kind() else { return };
        if args.types().next().is_none() {
            return;
        }
        fn parameter_names(tcx: TyCtxt<'_>, generics: &ty::Generics) -> Vec<rustc_span::Symbol> {
            let mut names = generics
                .parent
                .map_or_else(Vec::new, |def_id| parameter_names(tcx, tcx.generics_of(def_id)));
            names.extend(generics.own_params.iter().map(|param| param.name));
            names
        }
        let names = parameter_names(tcx, tcx.generics_of(def.did()));
        for (arg, name) in std::iter::zip(args.iter(), names) {
            let Some(arg_ty) = arg.as_type() else { continue };
            let arg_ty = tcx.normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                rustc_middle::ty::Unnormalized::new_wip(arg_ty),
            );
            let arg_dw_ty = self.debug_type(tcx, type_dbg, arg_ty);
            let param = self.dwarf.unit.add(parent, gimli::DW_TAG_template_type_parameter);
            let name_id = self.dwarf.strings.add(name.as_str());
            let entry = self.dwarf.unit.get_mut(param);
            entry.set(gimli::DW_AT_type, AttributeValue::UnitRef(arg_dw_ty));
            entry.set(gimli::DW_AT_name, AttributeValue::StringRef(name_id));
        }
    }

    fn add_fields<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        parent: UnitEntryId,
        layout: TyAndLayout<'tcx>,
        variant: Option<&ty::VariantDef>,
        upvar_names: Option<&rustc_index::IndexVec<FieldIdx, rustc_span::Symbol>>,
    ) {
        let cx = FullyMonomorphizedLayoutCx(tcx);
        let count = match layout.fields {
            FieldsShape::Arbitrary { .. } | FieldsShape::Union(_) => layout.fields.count(),
            FieldsShape::Array { .. } | FieldsShape::Primitive => 0,
        };
        for i in 0..count {
            let field = layout.field(&cx, i);
            let name =
                if let Some(def) = variant.and_then(|v| v.fields.get(FieldIdx::from_usize(i))) {
                    def.name.to_string()
                } else if let Some(name) =
                    upvar_names.and_then(|names| names.get(FieldIdx::from_usize(i)))
                {
                    name.to_string()
                } else {
                    format!("__{i}")
                };
            let field_dw_ty = self.debug_type(tcx, type_dbg, field.ty);
            self.add_member(
                parent,
                &name,
                field_dw_ty,
                layout.fields.offset(i).bytes(),
                field.align.bytes(),
            );
        }
    }

    fn placeholder_for_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ty: Ty<'tcx>,
    ) -> UnitEntryId {
        self.debug_type(
            tcx,
            type_dbg,
            Ty::new_array(
                tcx,
                tcx.types.u8,
                FullyMonomorphizedLayoutCx(tcx).layout_of(ty).size.bytes(),
            ),
        )
    }
}

/// The integer type a tag of this primitive reads as.
fn tag_int_type<'tcx>(tcx: TyCtxt<'tcx>, primitive: rustc_abi::Primitive) -> Ty<'tcx> {
    use rustc_abi::{Integer, Primitive};
    match primitive {
        Primitive::Int(int, signed) => match (int, signed) {
            (Integer::I8, false) => tcx.types.u8,
            (Integer::I16, false) => tcx.types.u16,
            (Integer::I32, false) => tcx.types.u32,
            (Integer::I64, false) => tcx.types.u64,
            (Integer::I128, false) => tcx.types.u128,
            (Integer::I8, true) => tcx.types.i8,
            (Integer::I16, true) => tcx.types.i16,
            (Integer::I32, true) => tcx.types.i32,
            (Integer::I64, true) => tcx.types.i64,
            (Integer::I128, true) => tcx.types.i128,
        },
        Primitive::Pointer(_) => tcx.types.usize,
        Primitive::Float(_) => tcx.types.u64,
    }
}
