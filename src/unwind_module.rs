use cranelift_codegen::Context;
use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::Signature;
use cranelift_codegen::isa::{TargetFrontendConfig, TargetIsa};
use cranelift_module::{
    DataDescription, DataId, FuncId, FuncOrDataId, Linkage, Module, ModuleDeclarations,
    ModuleReloc, ModuleResult,
};
use cranelift_object::{ObjectModule, ObjectProduct};

use crate::UnwindContext;

/// A wrapper around a [Module] which adds any defined function to the [UnwindContext].
pub(crate) struct UnwindModule<T> {
    pub(crate) module: T,
    unwind_context: UnwindContext,
}

impl<T: Module> UnwindModule<T> {
    pub(crate) fn new(
        mut module: T,
        eh_personality: &str,
        pic_eh_frame: bool,
        terminate_symbols: [Option<String>; 2],
    ) -> Self {
        let unwind_context =
            UnwindContext::new(&mut module, eh_personality, pic_eh_frame, terminate_symbols);
        UnwindModule { module, unwind_context }
    }
}

impl UnwindModule<ObjectModule> {
    pub(crate) fn finish(mut self) -> ObjectProduct {
        if self.unwind_context.needs_seh_runtime(&self.module) {
            let abort = self.unwind_context.seh_abort_symbols().cloned();
            crate::seh_runtime::define(&mut self, abort.as_ref());
        }
        let mut product = self.module.finish();
        self.unwind_context.emit(&mut product);
        product
    }
}

#[cfg(feature = "jit")]
impl UnwindModule<cranelift_jit::JITModule> {
    pub(crate) fn finalize_definitions(mut self) -> cranelift_jit::JITModule {
        self.module.finalize_definitions().unwrap();
        unsafe { self.unwind_context.register_jit(&self.module) };
        self.module
    }
}

impl<T: Module> Module for UnwindModule<T> {
    fn isa(&self) -> &dyn TargetIsa {
        self.module.isa()
    }

    fn declarations(&self) -> &ModuleDeclarations {
        self.module.declarations()
    }

    fn get_name(&self, name: &str) -> Option<FuncOrDataId> {
        self.module.get_name(name)
    }

    fn target_config(&self) -> TargetFrontendConfig {
        self.module.target_config()
    }

    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &Signature,
    ) -> ModuleResult<FuncId> {
        self.module.declare_function(name, linkage, signature)
    }

    fn declare_anonymous_function(&mut self, signature: &Signature) -> ModuleResult<FuncId> {
        self.module.declare_anonymous_function(signature)
    }

    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> ModuleResult<DataId> {
        self.module.declare_data(name, linkage, writable, tls)
    }

    fn declare_anonymous_data(&mut self, writable: bool, tls: bool) -> ModuleResult<DataId> {
        self.module.declare_anonymous_data(writable, tls)
    }

    fn define_function_with_control_plane(
        &mut self,
        func: FuncId,
        ctx: &mut Context,
        ctrl_plane: &mut ControlPlane,
    ) -> ModuleResult<()> {
        mark_colocated(self.module.isa(), &mut ctx.func);
        self.module.define_function_with_control_plane(func, ctx, ctrl_plane)?;
        self.unwind_context.add_function(&mut self.module, func, ctx);
        Ok(())
    }

    fn define_function_bytes(
        &mut self,
        func_id: FuncId,
        alignment: u64,
        bytes: &[u8],
        relocs: &[ModuleReloc],
    ) -> ModuleResult<()> {
        // Only for code that needs no unwind info: a jump to another function (see
        // `create_wrapper_function`), which never has a frame of its own.
        self.module.define_function_bytes(func_id, alignment, bytes, relocs)
    }

    fn define_data(&mut self, data_id: DataId, data: &DataDescription) -> ModuleResult<()> {
        self.module.define_data(data_id, data)
    }
}

/// Lets references to other functions and statics skip the GOT where the linker can resolve them
/// directly, as LLVM does for Rust code (x86_64 only).
///
/// `cranelift_module` only marks references to symbols defined in the same object as colocated,
/// so every call to another codegen unit or crate loads the callee's address from the GOT and
/// calls it indirectly. On ELF that is a GOT entry per callee in every executable (the
/// `R_X86_64_GOTPCREL` loads are not relaxable); on COFF, which has no GOT, every such reference
/// gets its own `.refptr` stub section in each object.
///
/// - ELF: calls become direct `call`s with `R_X86_64_PLT32`, which the linker resolves to the
///   callee, or to a PLT entry when the callee lives in a shared library. Taking a function's
///   address and statics keep the GOT, which is always valid in position-independent code.
/// - COFF: every non-TLS reference becomes a direct rel32 reference (`build_isa` turns `is_pic`
///   off for COFF, so colocated symbols get a RIP-relative `lea`): a PE image is at most 2 GiB and
///   functions imported from a DLL are called through their import library's thunk. Statics
///   imported from a DLL need `__imp_` references, which this backend never emitted (the
///   `.refptr` stub pointed at the static itself).
pub(crate) fn mark_colocated(isa: &dyn TargetIsa, func: &mut cranelift_codegen::ir::Function) {
    use cranelift_codegen::entity::EntityRef;
    use cranelift_codegen::ir::{ExternalName, GlobalValueData, InstructionData};

    let triple = isa.triple();
    if triple.architecture != target_lexicon::Architecture::X86_64 {
        return;
    }
    let coff = triple.binary_format == target_lexicon::BinaryFormat::Coff;
    if !coff && triple.binary_format != target_lexicon::BinaryFormat::Elf {
        return;
    }

    let mut address_taken = vec![false; func.dfg.ext_funcs.len()];
    if !coff {
        for block in func.layout.blocks() {
            for inst in func.layout.block_insts(block) {
                if let InstructionData::FuncAddr { func_ref, .. } = func.dfg.insts[inst] {
                    address_taken[func_ref.index()] = true;
                }
            }
        }
    }
    for (func_ref, ext_func) in func.dfg.ext_funcs.iter_mut() {
        if matches!(ext_func.name, ExternalName::User(_) | ExternalName::LibCall(_))
            && !address_taken[func_ref.index()]
        {
            ext_func.colocated = true;
        }
    }
    if coff {
        for global_value in func.global_values.values_mut() {
            if let GlobalValueData::Symbol { colocated, tls: false, .. } = global_value {
                *colocated = true;
            }
        }
    }
}
