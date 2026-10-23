//! CodeView type records (`.debug$T`) for the types of user variables.
//!
//! Primitive types map to CodeView's built-in type indices. Structs, tuples, closures and
//! fat pointers become `LF_STRUCTURE`s with their fields, named as LLVM names them for MSVC
//! targets (`compute_debuginfo_type_name`), so that the natvis visualizers rustc passes to the
//! linker (`String`, `Vec`, slices, ...) apply. Enums with data become an `LF_UNION` of their
//! variants plus the tag, under their Rust name (LLVM's `enum2$<..>` layout, which the natvis
//! files expect, is not reproduced). Every aggregate is first declared by a forward reference,
//! which is what other records refer to, so recursive types work; debuggers resolve it through
//! the unique name.

use rustc_abi::{FieldsShape, TagEncoding, Variants};
use rustc_codegen_ssa::debuginfo::type_names;
use rustc_middle::ty::layout::LayoutOf;

use super::{DebugContext, TypeDebugContext};
use crate::FullyMonomorphizedLayoutCx;
use crate::prelude::*;

const LF_POINTER: u16 = 0x1002;
const LF_FIELDLIST: u16 = 0x1203;
const LF_ARRAY: u16 = 0x1503;
const LF_STRUCTURE: u16 = 0x1505;
const LF_UNION: u16 = 0x1506;
const LF_MEMBER: u16 = 0x150d;
const LF_ENUM: u16 = 0x1507;
const LF_ENUMERATE: u16 = 0x1502;

const LF_LONG: u16 = 0x8003;
const LF_QUADWORD: u16 = 0x8009;

const LF_ULONG: u16 = 0x8004;
const LF_UQUADWORD: u16 = 0x800a;

const PROP_FWDREF: u16 = 0x0080;
const PROP_HAS_UNIQUE_NAME: u16 = 0x0200;

const T_VOID: u32 = 0x0003;
const T_BOOL08: u32 = 0x0030;
const T_REAL32: u32 = 0x0040;
const T_REAL64: u32 = 0x0041;
const T_REAL128: u32 = 0x0043;
const T_REAL16: u32 = 0x0046;
const T_INT1: u32 = 0x0068;
const T_UINT1: u32 = 0x0069;
const T_INT2: u32 = 0x0072;
const T_UINT2: u32 = 0x0073;
const T_INT4: u32 = 0x0074;
const T_UINT4: u32 = 0x0075;
const T_INT8: u32 = 0x0076;
const T_UINT8: u32 = 0x0077;
const T_INT16: u32 = 0x0078;
const T_UINT16: u32 = 0x0079;
const T_CHAR32: u32 = 0x007b;
/// Pointer mode of a built-in type index: 64-bit near pointer.
const T_64P: u32 = 0x0600;

/// `CV_PTR_64`, pointer mode `CV_PTR_MODE_PTR`, size 8.
const POINTER_ATTRS_64: u32 = 0x0c | (8 << 13);

/// Member access: public.
const MEMBER_ATTRS: u16 = 3;

/// The `.debug$T` records of one object, after the built-in `void ()` procedure type.
pub(crate) struct CvTypeTable {
    pub(super) data: Vec<u8>,
    next_index: u32,
}

impl CvTypeTable {
    pub(super) fn new(data: Vec<u8>, next_index: u32) -> Self {
        CvTypeTable { data, next_index }
    }

    fn add(&mut self, kind: u16, f: impl FnOnce(&mut Vec<u8>)) -> u32 {
        super::codeview::type_record(&mut self.data, kind, f);
        let index = self.next_index;
        self.next_index += 1;
        index
    }

    fn pointer(&mut self, referent: u32) -> u32 {
        if referent < 0x1000 && referent & 0xff00 == 0 {
            return T_64P | referent;
        }
        self.add(LF_POINTER, |r| {
            r.extend_from_slice(&referent.to_le_bytes());
            r.extend_from_slice(&POINTER_ATTRS_64.to_le_bytes());
        })
    }

    fn array(&mut self, element: u32, size: u64) -> u32 {
        self.add(LF_ARRAY, |r| {
            r.extend_from_slice(&element.to_le_bytes());
            r.extend_from_slice(&(T_UINT8).to_le_bytes()); // index type
            numeric(r, size);
            r.push(0); // name
        })
    }

    fn forward(&mut self, kind: u16, name: &str, unique: &str) -> u32 {
        self.add(kind, |r| {
            r.extend_from_slice(&0u16.to_le_bytes()); // member count
            r.extend_from_slice(&(PROP_FWDREF | PROP_HAS_UNIQUE_NAME).to_le_bytes());
            r.extend_from_slice(&0u32.to_le_bytes()); // field list
            if kind == LF_STRUCTURE {
                r.extend_from_slice(&0u32.to_le_bytes()); // derived from
                r.extend_from_slice(&0u32.to_le_bytes()); // vtable shape
            }
            numeric(r, 0);
            name_and_unique(r, name, unique);
        })
    }

    fn complete(
        &mut self,
        kind: u16,
        name: &str,
        unique: &str,
        size: u64,
        members: &[(String, u32, u64)],
    ) -> u32 {
        let field_list = self.add(LF_FIELDLIST, |r| {
            for (member_name, ty, offset) in members {
                r.extend_from_slice(&LF_MEMBER.to_le_bytes());
                r.extend_from_slice(&MEMBER_ATTRS.to_le_bytes());
                r.extend_from_slice(&ty.to_le_bytes());
                numeric(r, *offset);
                super::codeview::cstr(r, member_name.as_bytes());
                // Sub-records of a field list are aligned with LF_PAD bytes.
                while r.len() % 4 != 0 {
                    let left = 4 - r.len() % 4;
                    r.push(0xf0 | left as u8);
                }
            }
        });
        let count = u16::try_from(members.len()).unwrap_or(u16::MAX);
        self.add(kind, |r| {
            r.extend_from_slice(&count.to_le_bytes());
            r.extend_from_slice(&PROP_HAS_UNIQUE_NAME.to_le_bytes());
            r.extend_from_slice(&field_list.to_le_bytes());
            if kind == LF_STRUCTURE {
                r.extend_from_slice(&0u32.to_le_bytes());
                r.extend_from_slice(&0u32.to_le_bytes());
            }
            numeric(r, size);
            name_and_unique(r, name, unique);
        })
    }
}

impl CvTypeTable {
    fn enumeration(
        &mut self,
        name: &str,
        unique: &str,
        underlying: u32,
        enumerators: &[(String, i128)],
    ) -> u32 {
        let field_list = self.add(LF_FIELDLIST, |r| {
            for (enumerator, value) in enumerators {
                r.extend_from_slice(&LF_ENUMERATE.to_le_bytes());
                r.extend_from_slice(&MEMBER_ATTRS.to_le_bytes());
                signed_numeric(r, *value);
                super::codeview::cstr(r, enumerator.as_bytes());
                while r.len() % 4 != 0 {
                    let left = 4 - r.len() % 4;
                    r.push(0xf0 | left as u8);
                }
            }
        });
        let count = u16::try_from(enumerators.len()).unwrap_or(u16::MAX);
        self.add(LF_ENUM, |r| {
            r.extend_from_slice(&count.to_le_bytes());
            r.extend_from_slice(&PROP_HAS_UNIQUE_NAME.to_le_bytes());
            r.extend_from_slice(&underlying.to_le_bytes());
            r.extend_from_slice(&field_list.to_le_bytes());
            name_and_unique(r, name, unique);
        })
    }
}

/// A signed CodeView numeric leaf.
fn signed_numeric(r: &mut Vec<u8>, value: i128) {
    if (0..0x8000).contains(&value) {
        r.extend_from_slice(&(value as u16).to_le_bytes());
    } else if let Ok(value) = i32::try_from(value) {
        r.extend_from_slice(&LF_LONG.to_le_bytes());
        r.extend_from_slice(&value.to_le_bytes());
    } else if let Ok(value) = i64::try_from(value) {
        r.extend_from_slice(&LF_QUADWORD.to_le_bytes());
        r.extend_from_slice(&value.to_le_bytes());
    } else {
        r.extend_from_slice(&LF_UQUADWORD.to_le_bytes());
        r.extend_from_slice(&(value as u64).to_le_bytes());
    }
}

/// A CodeView numeric leaf: the value itself below 0x8000, else a tagged 32- or 64-bit value.
fn numeric(r: &mut Vec<u8>, value: u64) {
    if value < 0x8000 {
        r.extend_from_slice(&(value as u16).to_le_bytes());
    } else if let Ok(value) = u32::try_from(value) {
        r.extend_from_slice(&LF_ULONG.to_le_bytes());
        r.extend_from_slice(&value.to_le_bytes());
    } else {
        r.extend_from_slice(&LF_UQUADWORD.to_le_bytes());
        r.extend_from_slice(&value.to_le_bytes());
    }
}

fn name_and_unique(r: &mut Vec<u8>, name: &str, unique: &str) {
    // A record is at most 64 KiB: cut very long (generic) names.
    super::codeview::cstr(r, super::codeview::truncate(name, 4000).as_bytes());
    super::codeview::cstr(r, unique.as_bytes());
}

impl DebugContext {
    /// The CodeView type index of `ty`, adding its records to the object's `.debug$T`.
    pub(crate) fn codeview_type<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ty: Ty<'tcx>,
    ) -> u32 {
        if let Some(&index) = type_dbg.cv_type_map.get(&ty) {
            return index;
        }
        let index = self.codeview_type_uncached(tcx, type_dbg, ty);
        type_dbg.cv_type_map.insert(ty, index);
        index
    }

    fn cv_table(&mut self) -> &mut CvTypeTable {
        &mut self.codeview.as_mut().unwrap().types
    }

    fn codeview_type_uncached<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ty: Ty<'tcx>,
    ) -> u32 {
        let cx = FullyMonomorphizedLayoutCx(tcx);
        let layout = cx.layout_of(ty);
        match *ty.kind() {
            ty::Bool => return T_BOOL08,
            ty::Char => return T_CHAR32,
            ty::Int(int) => {
                return match int {
                    IntTy::I8 => T_INT1,
                    IntTy::I16 => T_INT2,
                    IntTy::I32 => T_INT4,
                    IntTy::I64 | IntTy::Isize => T_INT8,
                    IntTy::I128 => T_INT16,
                };
            }
            ty::Uint(uint) => {
                return match uint {
                    UintTy::U8 => T_UINT1,
                    UintTy::U16 => T_UINT2,
                    UintTy::U32 => T_UINT4,
                    UintTy::U64 | UintTy::Usize => T_UINT8,
                    UintTy::U128 => T_UINT16,
                };
            }
            ty::Float(float) => {
                return match float {
                    FloatTy::F16 => T_REAL16,
                    FloatTy::F32 => T_REAL32,
                    FloatTy::F64 => T_REAL64,
                    FloatTy::F128 => T_REAL128,
                };
            }
            ty::Never => return T_VOID,
            ty::Tuple(elems) if elems.is_empty() => return T_VOID,
            ty::FnPtr(..) => return self.cv_table().pointer(T_VOID),
            ty::Pat(base, _) => return self.codeview_type(tcx, type_dbg, base),
            ty::RawPtr(pointee, _) | ty::Ref(_, pointee, _) => {
                return self.codeview_pointer(tcx, type_dbg, ty, pointee);
            }
            // `Box<T>` with a zero-sized allocator looks like a pointer, as LLVM describes it.
            ty::Adt(def, args)
                if def.is_box()
                    && args.get(1).is_none_or(|arg| cx.layout_of(arg.expect_ty()).is_1zst()) =>
            {
                return self.codeview_pointer(tcx, type_dbg, ty, args.type_at(0));
            }
            ty::Array(elem, _) => {
                let elem = self.codeview_type(tcx, type_dbg, elem);
                return self.cv_table().array(elem, layout.size.bytes());
            }
            _ => {}
        }

        let name = type_names::compute_debuginfo_type_name(tcx, ty, true);
        let unique = format!("{:x}", tcx.type_id_hash(ty).as_u128());

        // Fieldless enums with a plain tag: a C-like enum.
        if let ty::Adt(adt, _) = ty.kind()
            && adt.is_enum()
            && adt.variants().iter().all(|v| v.fields.is_empty())
            && let Variants::Multiple { tag, tag_encoding: TagEncoding::Direct, .. } =
                &layout.variants
        {
            let signed = matches!(tag.primitive(), rustc_abi::Primitive::Int(_, true));
            let underlying = match (tag.size(&tcx).bytes(), signed) {
                (1, false) => T_UINT1,
                (2, false) => T_UINT2,
                (4, false) => T_UINT4,
                (8, false) => T_UINT8,
                (1, true) => T_INT1,
                (2, true) => T_INT2,
                (4, true) => T_INT4,
                (8, true) => T_INT8,
                (_, true) => T_INT16,
                (_, false) => T_UINT16,
            };
            let enumerators: Vec<(String, i128)> = adt
                .variants()
                .iter_enumerated()
                .map(|(index, variant)| {
                    let value = tag
                        .size(&tcx)
                        .truncate(ty.discriminant_for_variant(tcx, index).unwrap().val);
                    let value =
                        if signed { tag.size(&tcx).sign_extend(value) } else { value as i128 };
                    (variant.name.to_string(), value)
                })
                .collect();
            return self.cv_table().enumeration(&name, &unique, underlying, &enumerators);
        }

        let is_enum = matches!(layout.variants, Variants::Multiple { .. });
        let kind = if is_enum { LF_UNION } else { LF_STRUCTURE };
        // LLVM's names for enums on MSVC (`enum2$<..>`) select natvis visualizers that expect
        // LLVM's enum layout: give ours the plain Rust name instead.
        let name = if is_enum {
            rustc_middle::ty::print::with_no_trimmed_paths!(ty.to_string())
        } else {
            name
        };
        let forward = self.cv_table().forward(kind, &name, &unique);
        type_dbg.cv_type_map.insert(ty, forward);

        let mut members = Vec::new();
        match &layout.variants {
            Variants::Multiple { tag, tag_encoding, tag_field, variants } => {
                // The tag (or the niche holding it), then each variant's fields as a struct at
                // offset 0, like a union.
                let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
                let tag_ty = match tag.primitive().size(&tcx).bytes() {
                    1 => T_UINT1,
                    2 => T_UINT2,
                    4 => T_UINT4,
                    8 => T_UINT8,
                    _ => T_UINT16,
                };
                let tag_name = match tag_encoding {
                    TagEncoding::Direct => "tag",
                    TagEncoding::Niche { .. } => "niche",
                };
                members.push((tag_name.to_string(), tag_ty, tag_offset));
                if let ty::Adt(adt, _) = ty.kind() {
                    for (index, _) in variants.iter_enumerated() {
                        let variant_layout = layout.for_variant(&cx, index);
                        let variant_name = adt.variant(index).name.to_string();
                        let variant_ty = self.codeview_variant_struct(
                            tcx,
                            type_dbg,
                            variant_layout,
                            &format!("{name}::{variant_name}"),
                            &format!("{unique}-{}", index.as_u32()),
                            Some(adt.variant(index)),
                        );
                        members.push((variant_name, variant_ty, 0));
                    }
                }
            }
            Variants::Single { .. } | Variants::Empty => {
                let variant = match ty.kind() {
                    ty::Adt(adt, _) if !adt.is_enum() => Some(adt.non_enum_variant()),
                    ty::Adt(adt, _) if adt.variants().len() == 1 => {
                        Some(adt.variant(FIRST_VARIANT))
                    }
                    _ => None,
                };
                let upvar_names = match ty.kind() {
                    ty::Closure(def_id, _) | ty::CoroutineClosure(def_id, _) => {
                        Some(tcx.closure_saved_names_of_captured_variables(*def_id))
                    }
                    _ => None,
                };
                self.codeview_fields(tcx, type_dbg, layout, variant, upvar_names, &mut members);
            }
        }
        self.cv_table().complete(kind, &name, &unique, layout.size.bytes(), &members);
        forward
    }

    /// Thin pointers are `LF_POINTER`s; wide ones (slices, `str`, trait objects) are structs of
    /// two fields, named as LLVM names them, which the natvis visualizers read.
    fn codeview_pointer<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        ptr_ty: Ty<'tcx>,
        pointee: Ty<'tcx>,
    ) -> u32 {
        if !tcx.type_has_metadata(pointee, ty::TypingEnv::fully_monomorphized()) {
            let pointee = self.codeview_type(tcx, type_dbg, pointee);
            return self.cv_table().pointer(pointee);
        }
        let cx = FullyMonomorphizedLayoutCx(tcx);
        let name = type_names::compute_debuginfo_type_name(tcx, ptr_ty, true);
        let unique = format!("{:x}", tcx.type_id_hash(ptr_ty).as_u128());
        let forward = self.cv_table().forward(LF_STRUCTURE, &name, &unique);
        type_dbg.cv_type_map.insert(ptr_ty, forward);

        let layout = cx.layout_of(Ty::new_mut_ptr(tcx, pointee));
        let element = match pointee.kind() {
            ty::Slice(elem) => *elem,
            ty::Str => tcx.types.u8,
            _ => pointee,
        };
        let element = self.codeview_type(tcx, type_dbg, element);
        let data_ptr = self.cv_table().pointer(element);
        let extra = layout.field(&cx, 1);
        let extra_ty = self.codeview_type(tcx, type_dbg, extra.ty);
        let slice_like = matches!(
            tcx.struct_tail_for_codegen(pointee, ty::TypingEnv::fully_monomorphized()).kind(),
            ty::Slice(_) | ty::Str
        );
        let (addr_name, extra_name) =
            if slice_like { ("data_ptr", "length") } else { ("pointer", "vtable") };
        let members = [
            (addr_name.to_string(), data_ptr, layout.fields.offset(0).bytes()),
            (extra_name.to_string(), extra_ty, layout.fields.offset(1).bytes()),
        ];
        self.cv_table().complete(LF_STRUCTURE, &name, &unique, layout.size.bytes(), &members);
        forward
    }

    fn codeview_variant_struct<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        layout: TyAndLayout<'tcx>,
        name: &str,
        unique: &str,
        variant: Option<&ty::VariantDef>,
    ) -> u32 {
        let forward = self.cv_table().forward(LF_STRUCTURE, name, unique);
        let mut members = Vec::new();
        self.codeview_fields(tcx, type_dbg, layout, variant, None, &mut members);
        self.cv_table().complete(LF_STRUCTURE, name, unique, layout.size.bytes(), &members);
        forward
    }

    fn codeview_fields<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        type_dbg: &mut TypeDebugContext<'tcx>,
        layout: TyAndLayout<'tcx>,
        variant: Option<&ty::VariantDef>,
        upvar_names: Option<&rustc_index::IndexVec<FieldIdx, rustc_span::Symbol>>,
        members: &mut Vec<(String, u32, u64)>,
    ) {
        let cx = FullyMonomorphizedLayoutCx(tcx);
        let count = match layout.fields {
            FieldsShape::Arbitrary { .. } => layout.fields.count(),
            // Fat pointers, unions and SIMD vectors.
            FieldsShape::Union(_) | FieldsShape::Array { .. } | FieldsShape::Primitive => {
                if matches!(layout.fields, FieldsShape::Union(_)) {
                    layout.fields.count()
                } else {
                    0
                }
            }
        };
        for i in 0..count {
            let field = layout.field(&cx, i);
            let field_name = if let Some(variant) = variant
                && let Some(def) = variant.fields.get(FieldIdx::from_usize(i))
            {
                def.name.to_string()
            } else if let Some(name) =
                upvar_names.and_then(|names| names.get(FieldIdx::from_usize(i)))
            {
                name.to_string()
            } else {
                format!("__{i}")
            };
            let field_ty = if field.size.bytes() == 0 {
                continue;
            } else {
                self.codeview_type(tcx, type_dbg, field.ty)
            };
            members.push((field_name, field_ty, layout.fields.offset(i).bytes()));
        }
    }
}
