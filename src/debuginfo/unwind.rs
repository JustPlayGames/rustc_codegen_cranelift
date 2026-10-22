//! Unwind info generation (`.eh_frame`)

use cranelift_codegen::MachExceptionHandler;
use cranelift_codegen::ir::Endianness;
use cranelift_codegen::isa::unwind::UnwindInfo;
use cranelift_module::DataId;
use cranelift_object::ObjectProduct;
use gimli::write::{Address, CieId, EhFrame, FrameTable, Section};
use gimli::{Encoding, Format, RunTimeEndian};

use super::emit::{DebugRelocName, address_for_data, address_for_func};
use super::gcc_except_table::{
    Action, ActionKind, ActionTable, CallSite, CallSiteTable, GccExceptTable, TypeInfoTable,
};
use super::object::WriteDebugInfo;
use crate::prelude::*;

pub(crate) const EXCEPTION_HANDLER_CLEANUP: u32 = 0;
pub(crate) const EXCEPTION_HANDLER_CATCH: u32 = 1;
/// A landing pad that aborts (`UnwindAction::Terminate`). Treated as a cleanup in the
/// `.gcc_except_table`; on Windows it catches C++ exceptions only, like LLVM's `catch (...)`
/// terminate funclet, so that `longjmp` and SEH exceptions don't trigger it.
pub(crate) const EXCEPTION_HANDLER_TERMINATE: u32 = 2;

/// The language-specific handler of every function with landing pads on Windows x64, and the
/// helpers its landing pads call, defined by `seh_runtime.rs`.
pub(crate) const SEH_PERSONALITY: &str = "__cg_clif_seh_personality";
pub(crate) const SEH_RESUME: &str = "__cg_clif_seh_resume";
pub(crate) const SEH_FREE: &str = "__cg_clif_seh_free";

/// Whether landing pads use the SEH runtime functions above (x86_64-pc-windows-msvc) rather
/// than the Itanium ABI (`_Unwind_Resume`, `.gcc_except_table`).
pub(crate) fn uses_seh_runtime(triple: &target_lexicon::Triple) -> bool {
    cfg!(feature = "unwinding")
        && triple.operating_system == target_lexicon::OperatingSystem::Windows
        && triple.architecture == target_lexicon::Architecture::X86_64
        && triple.environment == target_lexicon::Environment::Msvc
}

/// `.pdata`/`.xdata` for one function (Windows x64).
struct WinFunction {
    func_id: FuncId,
    code_len: u32,
    /// `UNWIND_INFO`, followed by the handler's RVA (at `handler_reloc`) and its data.
    xdata: Vec<u8>,
    handler_reloc: Option<usize>,
}

pub(crate) struct UnwindContext {
    endian: RunTimeEndian,
    frame_table: FrameTable,
    cie_id: Option<CieId>,
    /// A CIE without personality and LSDA, for functions without landing pads: like LLVM, only
    /// functions that catch or clean up need the personality routine and a `.gcc_except_table`.
    plain_cie_id: Option<CieId>,
    win_functions: Vec<WinFunction>,
    uses_seh: bool,
    seh_personality: Option<FuncId>,
}

impl UnwindContext {
    pub(crate) fn new(module: &mut dyn Module, eh_personality: &str, pic_eh_frame: bool) -> Self {
        let endian = match module.isa().endianness() {
            Endianness::Little => RunTimeEndian::Little,
            Endianness::Big => RunTimeEndian::Big,
        };
        let mut frame_table = FrameTable::default();

        let mut plain_cie_id = None;
        let cie_id = if let Some(mut cie) = module.isa().create_systemv_cie() {
            let ptr_encoding = if pic_eh_frame {
                gimli::DwEhPe(gimli::DW_EH_PE_pcrel.0 | gimli::DW_EH_PE_sdata4.0)
            } else {
                gimli::DW_EH_PE_absptr
            };

            cie.fde_address_encoding = ptr_encoding;
            plain_cie_id = Some(frame_table.add_cie(cie.clone()));

            // FIXME only add personality function and lsda when necessary: https://github.com/rust-lang/rust/blob/1f76d219c906f0112bb1872f33aa977164c53fa6/compiler/rustc_codegen_ssa/src/mir/mod.rs#L200-L204
            if cfg!(feature = "unwinding") {
                let code_ptr_encoding = if pic_eh_frame {
                    if module.isa().triple().architecture == target_lexicon::Architecture::X86_64 {
                        gimli::DwEhPe(
                            gimli::DW_EH_PE_indirect.0
                                | gimli::DW_EH_PE_pcrel.0
                                | gimli::DW_EH_PE_sdata4.0,
                        )
                    } else if let target_lexicon::Architecture::Aarch64(_) =
                        module.isa().triple().architecture
                    {
                        gimli::DwEhPe(
                            gimli::DW_EH_PE_indirect.0
                                | gimli::DW_EH_PE_pcrel.0
                                | gimli::DW_EH_PE_sdata8.0,
                        )
                    } else {
                        todo!()
                    }
                } else {
                    gimli::DwEhPe(gimli::DW_EH_PE_indirect.0 | gimli::DW_EH_PE_absptr.0)
                };

                cie.lsda_encoding = Some(ptr_encoding);

                // FIXME use eh_personality lang item instead
                let personality = module
                    .declare_function(
                        eh_personality,
                        Linkage::Import,
                        &Signature {
                            params: vec![
                                AbiParam::new(types::I32),
                                AbiParam::new(types::I32),
                                AbiParam::new(types::I64),
                                AbiParam::new(module.target_config().pointer_type()),
                                AbiParam::new(module.target_config().pointer_type()),
                            ],
                            returns: vec![AbiParam::new(types::I32)],
                            call_conv: module.target_config().default_call_conv,
                        },
                    )
                    .unwrap();

                // Use indirection here to support PIC the case where rust_eh_personality is defined in
                // another DSO.
                let personality_ref = module
                    .declare_data(&format!("DW.ref.{eh_personality}"), Linkage::Local, false, false)
                    .unwrap();

                let mut personality_ref_data = DataDescription::new();
                // Note: Must not use define_zeroinit. The unwinder can't handle this being in the .bss
                // section.
                let pointer_bytes = usize::from(module.target_config().pointer_bytes());
                personality_ref_data.define(vec![0; pointer_bytes].into_boxed_slice());
                let personality_func_ref =
                    module.declare_func_in_data(personality, &mut personality_ref_data);
                personality_ref_data.write_function_addr(0, personality_func_ref);

                module.define_data(personality_ref, &personality_ref_data).unwrap();

                cie.personality = Some((code_ptr_encoding, address_for_data(personality_ref)));
            }

            Some(frame_table.add_cie(cie))
        } else {
            None
        };

        // Declared on first use: an unused import would still be an undefined symbol of the object.
        let uses_seh = uses_seh_runtime(module.isa().triple());
        let seh_personality = None;

        UnwindContext {
            endian,
            frame_table,
            cie_id,
            plain_cie_id,
            win_functions: vec![],
            uses_seh,
            seh_personality,
        }
    }

    /// Whether this object needs the SEH runtime functions (`seh_runtime.rs`): it has landing
    /// pads, or calls the resume or free helper.
    pub(crate) fn needs_seh_runtime(&self, module: &dyn Module) -> bool {
        self.uses_seh
            && (self.seh_personality.is_some()
                || module.get_name(SEH_RESUME).is_some()
                || module.get_name(SEH_FREE).is_some())
    }

    pub(crate) fn add_function(
        &mut self,
        module: &mut dyn Module,
        func_id: FuncId,
        context: &Context,
    ) {
        let triple = module.isa().triple();
        if matches!(triple.operating_system, target_lexicon::OperatingSystem::MacOSX { .. })
            && triple.architecture == target_lexicon::Architecture::X86_64
        {
            // The object crate doesn't currently support DW_GNU_EH_PE_absptr, which macOS
            // requires for unwinding tables. See gimli-rs/object#415.
            return;
        }

        let Some(unwind_info) =
            context.compiled_code().unwrap().create_unwind_info(module.isa()).unwrap()
        else {
            return;
        };

        match unwind_info {
            UnwindInfo::SystemV(unwind_info) => {
                let mut fde = unwind_info.to_fde(address_for_func(func_id));

                // Like LLVM, only functions with landing pads get the personality function and an
                // LSDA: an unwind through a function without any just continues to its caller, as
                // the personality would do for call sites without a landing pad. Every
                // `UnwindAction::Terminate` becomes a landing pad, so nounwind functions keep
                // their LSDA and abort.
                let has_landing_pads = context
                    .compiled_code()
                    .unwrap()
                    .buffer
                    .call_sites()
                    .any(|call_site| !call_site.exception_handlers.is_empty());
                if cfg!(feature = "unwinding") && has_landing_pads {
                    // FIXME use unique symbol name derived from function name
                    let lsda = module.declare_anonymous_data(false, false).unwrap();

                    let encoding = Encoding {
                        format: Format::Dwarf32,
                        version: 1,
                        address_size: module.isa().frontend_config().pointer_bytes(),
                    };

                    let mut gcc_except_table_data = GccExceptTable {
                        call_sites: CallSiteTable(vec![]),
                        actions: ActionTable::new(),
                        type_info: TypeInfoTable::new(gimli::DW_EH_PE_udata4),
                    };

                    let catch_type = gcc_except_table_data.type_info.add(Address::Constant(0));
                    let catch_action = gcc_except_table_data
                        .actions
                        .add(Action { kind: ActionKind::Catch(catch_type), next_action: None });

                    for call_site in context.compiled_code().unwrap().buffer.call_sites() {
                        if call_site.exception_handlers.is_empty() {
                            gcc_except_table_data.call_sites.0.push(CallSite {
                                start: u64::from(call_site.ret_addr - 1),
                                length: 1,
                                landing_pad: 0,
                                action_entry: None,
                            });
                        }
                        for &handler in call_site.exception_handlers {
                            match handler {
                                MachExceptionHandler::Tag(tag, landingpad) => {
                                    let landing_pad = u64::from(landingpad.as_offset());
                                    let action_entry = match tag.as_u32() {
                                        EXCEPTION_HANDLER_CLEANUP | EXCEPTION_HANDLER_TERMINATE => {
                                            None
                                        }
                                        EXCEPTION_HANDLER_CATCH => Some(catch_action),
                                        _ => unreachable!(),
                                    };
                                    gcc_except_table_data.call_sites.0.push(CallSite {
                                        start: u64::from(call_site.ret_addr - 1),
                                        length: 1,
                                        landing_pad,
                                        action_entry,
                                    });
                                }
                                _ => unreachable!(),
                            }
                        }
                    }

                    let mut gcc_except_table = super::emit::WriterRelocate::new(self.endian);

                    gcc_except_table_data.write(&mut gcc_except_table, encoding).unwrap();

                    let mut data = DataDescription::new();
                    data.define(gcc_except_table.writer.into_vec().into_boxed_slice());
                    data.set_custom_section(".gcc_except_table");

                    for reloc in &gcc_except_table.relocs {
                        match reloc.name {
                            DebugRelocName::Section(_id) => unreachable!(),
                            DebugRelocName::Symbol(id) => {
                                let id = id.try_into().unwrap();
                                if id & 1 << 31 == 0 {
                                    let func_ref = module
                                        .declare_func_in_data(FuncId::from_u32(id), &mut data);
                                    data.write_function_addr(reloc.offset, func_ref);
                                } else {
                                    let gv = module.declare_data_in_data(
                                        DataId::from_u32(id & !(1 << 31)),
                                        &mut data,
                                    );
                                    data.write_data_addr(reloc.offset, gv, 0);
                                }
                            }
                        };
                    }

                    module.define_data(lsda, &data).unwrap();
                    fde.lsda = Some(address_for_data(lsda));
                }

                let cie_id = if cfg!(feature = "unwinding") && !has_landing_pads {
                    self.plain_cie_id
                } else {
                    self.cie_id
                };
                self.frame_table.add_fde(cie_id.unwrap(), fde);
            }
            UnwindInfo::WindowsX64(unwind_info) => {
                let compiled_code = context.compiled_code().unwrap();
                let mut xdata = vec![0; unwind_info.emit_size()];
                unwind_info.emit(&mut xdata);

                // Landing pads: a language-specific handler finds them through a table of
                // (return offset, landing pad offset, kind), sorted by return offset.
                let mut table = vec![];
                for call_site in compiled_code.buffer.call_sites() {
                    for &handler in call_site.exception_handlers {
                        match handler {
                            MachExceptionHandler::Tag(tag, landingpad) => table.push([
                                call_site.ret_addr,
                                landingpad.as_offset(),
                                tag.as_u32(),
                            ]),
                            _ => unreachable!(),
                        }
                    }
                }

                let handler_reloc = if self.uses_seh && !table.is_empty() {
                    if self.seh_personality.is_none() {
                        let ptr = AbiParam::new(module.target_config().pointer_type());
                        self.seh_personality = Some(
                            module
                                .declare_function(
                                    SEH_PERSONALITY,
                                    Linkage::Import,
                                    &Signature {
                                        params: vec![ptr, ptr, ptr, ptr],
                                        returns: vec![AbiParam::new(types::I32)],
                                        call_conv: module.target_config().default_call_conv,
                                    },
                                )
                                .unwrap(),
                        );
                    }
                    table.sort();
                    // UNW_FLAG_EHANDLER | UNW_FLAG_UHANDLER
                    xdata[0] |= 0x3 << 3;
                    let handler_reloc = xdata.len();
                    xdata.extend(0u32.to_le_bytes());
                    xdata.extend(u32::try_from(table.len()).unwrap().to_le_bytes());
                    for entry in table {
                        for field in entry {
                            xdata.extend(field.to_le_bytes());
                        }
                    }
                    Some(handler_reloc)
                } else {
                    None
                };

                self.win_functions.push(WinFunction {
                    func_id,
                    code_len: compiled_code.code_info().total_size,
                    xdata,
                    handler_reloc,
                });
            }
            UnwindInfo::WindowsArm64(_) => {
                // FIXME emit .pdata/.xdata on Windows Arm64 too
            }
            unwind_info => unimplemented!("{:?}", unwind_info),
        }
    }

    pub(crate) fn emit(self, product: &mut ObjectProduct) {
        if !self.win_functions.is_empty() {
            emit_pdata_xdata(product, &self.win_functions, self.seh_personality);
        }

        let mut eh_frame = EhFrame::from(super::emit::WriterRelocate::new(self.endian));
        self.frame_table.write_eh_frame(&mut eh_frame).unwrap();

        if !eh_frame.0.writer.slice().is_empty() {
            let id = eh_frame.id();
            let section_id = product.add_debug_section(id, eh_frame.0.writer.into_vec());
            let mut section_map = FxHashMap::default();
            section_map.insert(id, section_id);

            let use_section_symbol = product.object.format() != object::BinaryFormat::MachO;
            for reloc in &eh_frame.0.relocs {
                product.add_debug_reloc(&section_map, &section_id, reloc, use_section_symbol);
            }
        }
    }

    #[cfg(all(feature = "jit", windows))]
    pub(crate) unsafe fn register_jit(self, _jit_module: &cranelift_jit::JITModule) {}

    #[cfg(all(feature = "jit", not(windows)))]
    pub(crate) unsafe fn register_jit(self, jit_module: &cranelift_jit::JITModule) {
        use std::mem::ManuallyDrop;

        let mut eh_frame = EhFrame::from(super::emit::WriterRelocate::new(self.endian));
        self.frame_table.write_eh_frame(&mut eh_frame).unwrap();

        if eh_frame.0.writer.slice().is_empty() {
            return;
        }

        let mut eh_frame = eh_frame.0.relocate_for_jit(jit_module);

        // GCC expects a terminating "empty" length, so write a 0 length at the end of the table.
        eh_frame.extend(&[0, 0, 0, 0]);

        // FIXME support unregistering unwind tables once cranelift-jit supports deallocating
        // individual functions
        let eh_frame = ManuallyDrop::new(eh_frame);

        // =======================================================================
        // Everything after this line up to the end of the file is loosely based on
        // https://github.com/bytecodealliance/wasmtime/blob/4471a82b0c540ff48960eca6757ccce5b1b5c3e4/crates/jit/src/unwind/systemv.rs
        #[cfg(target_os = "macos")]
        unsafe {
            // On macOS, `__register_frame` takes a pointer to a single FDE
            let start = eh_frame.as_ptr();
            let end = start.add(eh_frame.len());
            let mut current = start;

            // Walk all of the entries in the frame table and register them
            while current < end {
                let len = std::ptr::read::<u32>(current as *const u32) as usize;

                // Skip over the CIE
                if current != start {
                    __register_frame(current);
                }

                // Move to the next table entry (+4 because the length itself is not inclusive)
                current = current.add(len + 4);
            }
        }
        #[cfg(not(target_os = "macos"))]
        {
            // On other platforms, `__register_frame` will walk the FDEs until an entry of length 0
            unsafe { __register_frame(eh_frame.as_ptr()) };
        }
    }
}

/// Writes the `.xdata` (`UNWIND_INFO`) and `.pdata` (`RUNTIME_FUNCTION`) sections that let the
/// Windows unwinder walk and unwind through the functions of this object.
fn emit_pdata_xdata(
    product: &mut ObjectProduct,
    functions: &[WinFunction],
    seh_personality: Option<FuncId>,
) {
    use object::write::Relocation;
    use object::{RelocationEncoding, RelocationFlags, RelocationKind, SectionKind};

    let image_offset = RelocationFlags::Generic {
        kind: RelocationKind::ImageOffset,
        encoding: RelocationEncoding::Generic,
        size: 32,
    };

    let xdata_section =
        product.object.add_section(vec![], b".xdata".to_vec(), SectionKind::ReadOnlyData);
    let pdata_section =
        product.object.add_section(vec![], b".pdata".to_vec(), SectionKind::ReadOnlyData);
    let xdata_symbol = product.object.section_symbol(xdata_section);
    let personality_symbol = seh_personality.map(|id| product.function_symbol(id));

    // COFF relocations have implicit addends, which `add_relocation` writes into the section
    // data: set the data first.
    let mut xdata = Vec::new();
    let mut pdata = Vec::new();
    let mut xdata_relocs = Vec::new();
    let mut pdata_relocs = Vec::new();
    for function in functions {
        let xdata_offset = xdata.len();
        assert_eq!(xdata_offset % 4, 0);
        xdata.extend_from_slice(&function.xdata);
        if let Some(handler_reloc) = function.handler_reloc {
            xdata_relocs.push((xdata_offset + handler_reloc, personality_symbol.unwrap(), 0));
        }

        let func_symbol = product.function_symbol(function.func_id);
        let pdata_offset = pdata.len();
        pdata.extend([0; 12]);
        pdata_relocs.push((pdata_offset, func_symbol, 0));
        pdata_relocs.push((pdata_offset + 4, func_symbol, i64::from(function.code_len)));
        pdata_relocs.push((pdata_offset + 8, xdata_symbol, i64::try_from(xdata_offset).unwrap()));
    }

    product.object.section_mut(xdata_section).set_data(xdata, 4);
    product.object.section_mut(pdata_section).set_data(pdata, 4);
    for (section, relocs) in [(xdata_section, xdata_relocs), (pdata_section, pdata_relocs)] {
        for (offset, symbol, addend) in relocs {
            product
                .object
                .add_relocation(
                    section,
                    Relocation {
                        offset: u64::try_from(offset).unwrap(),
                        symbol,
                        flags: image_offset,
                        addend,
                    },
                )
                .unwrap();
        }
    }
}

unsafe extern "C" {
    // libunwind import
    fn __register_frame(fde: *const u8);
}
