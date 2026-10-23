use cranelift_codegen::isa::TargetFrontendConfig;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use rustc_abi::{Float, Integer, Primitive};
use rustc_index::IndexVec;
use rustc_middle::ty::TypeFoldable;
use rustc_middle::ty::layout::{
    self, FnAbiError, FnAbiOfHelpers, FnAbiRequest, HasTypingEnv as _, LayoutError,
    LayoutOfHelpers, codegen_handle_fn_abi_err,
};
use rustc_span::Symbol;
use rustc_target::callconv::FnAbi;
use rustc_target::spec::{Arch, HasTargetSpec, Target};

use crate::constant::ConstantCx;
use crate::debuginfo::FunctionDebugContext;
use crate::prelude::*;

pub(crate) fn pointer_ty(tcx: TyCtxt<'_>) -> types::Type {
    match tcx.data_layout.pointer_size().bits() {
        16 => types::I16,
        32 => types::I32,
        64 => types::I64,
        bits => bug!("ptr_sized_integer: unknown pointer bit size {}", bits),
    }
}

pub(crate) fn scalar_to_clif_type(tcx: TyCtxt<'_>, scalar: Scalar) -> Type {
    match scalar.primitive() {
        Primitive::Int(int, _sign) => match int {
            Integer::I8 => types::I8,
            Integer::I16 => types::I16,
            Integer::I32 => types::I32,
            Integer::I64 => types::I64,
            Integer::I128 => types::I128,
        },
        Primitive::Float(float) => match float {
            Float::F16 => types::F16,
            Float::F16B => bug!("f16b is not supported by the Cranelift codegen backend"),
            Float::F32 => types::F32,
            Float::F64 => types::F64,
            Float::F128 => types::F128,
            Float::PpcF128 => bug!("cranelift does not support powerpc"),
        },
        // FIXME(erikdesjardins): handle non-default addrspace ptr sizes
        Primitive::Pointer(_) => pointer_ty(tcx),
    }
}

fn clif_type_from_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<types::Type> {
    Some(match ty.kind() {
        ty::Bool => types::I8,
        ty::Uint(size) => match size {
            UintTy::U8 => types::I8,
            UintTy::U16 => types::I16,
            UintTy::U32 => types::I32,
            UintTy::U64 => types::I64,
            UintTy::U128 => types::I128,
            UintTy::Usize => pointer_ty(tcx),
        },
        ty::Int(size) => match size {
            IntTy::I8 => types::I8,
            IntTy::I16 => types::I16,
            IntTy::I32 => types::I32,
            IntTy::I64 => types::I64,
            IntTy::I128 => types::I128,
            IntTy::Isize => pointer_ty(tcx),
        },
        ty::Char => types::I32,
        ty::Float(size) => match size {
            FloatTy::F16 => types::F16,
            FloatTy::F32 => types::F32,
            FloatTy::F64 => types::F64,
            FloatTy::F128 => types::F128,
        },
        ty::FnPtr(..) => pointer_ty(tcx),
        ty::RawPtr(pointee_ty, _) | ty::Ref(_, pointee_ty, _) => {
            if tcx.type_has_metadata(*pointee_ty, ty::TypingEnv::fully_monomorphized()) {
                return None;
            } else {
                pointer_ty(tcx)
            }
        }
        ty::Param(_) => bug!("ty param {:?}", ty),
        _ => return None,
    })
}

pub(crate) fn codegen_icmp_imm(
    fx: &mut FunctionCx<'_, '_, '_>,
    intcc: IntCC,
    lhs: Value,
    rhs: i128,
) -> Value {
    let lhs_ty = fx.bcx.func.dfg.value_type(lhs);
    if lhs_ty == types::I128 {
        // FIXME legalize `icmp_imm.i128` in Cranelift

        let (lhs_lsb, lhs_msb) = fx.bcx.ins().isplit(lhs);
        let (rhs_lsb, rhs_msb) = (rhs as u128 as u64 as i64, (rhs as u128 >> 64) as u64 as i64);

        match intcc {
            IntCC::Equal => {
                let lsb_eq = fx.bcx.ins().icmp_imm_u(IntCC::Equal, lhs_lsb, rhs_lsb);
                let msb_eq = fx.bcx.ins().icmp_imm_u(IntCC::Equal, lhs_msb, rhs_msb);
                fx.bcx.ins().band(lsb_eq, msb_eq)
            }
            IntCC::NotEqual => {
                let lsb_ne = fx.bcx.ins().icmp_imm_u(IntCC::NotEqual, lhs_lsb, rhs_lsb);
                let msb_ne = fx.bcx.ins().icmp_imm_u(IntCC::NotEqual, lhs_msb, rhs_msb);
                fx.bcx.ins().bor(lsb_ne, msb_ne)
            }
            _ => {
                // if msb_eq {
                //     lsb_cc
                // } else {
                //     msb_cc
                // }

                let msb_eq = fx.bcx.ins().icmp_imm_u(IntCC::Equal, lhs_msb, rhs_msb);
                let lsb_cc = fx.bcx.ins().icmp_imm_u(intcc, lhs_lsb, rhs_lsb);
                let msb_cc = fx.bcx.ins().icmp_imm_u(intcc, lhs_msb, rhs_msb);

                fx.bcx.ins().select(msb_eq, lsb_cc, msb_cc)
            }
        }
    } else {
        let rhs = rhs as i64; // Truncates on purpose in case rhs is actually an unsigned value
        fx.bcx.ins().icmp_imm_u(intcc, lhs, rhs)
    }
}

pub(crate) fn codegen_bitcast(fx: &mut FunctionCx<'_, '_, '_>, dst_ty: Type, val: Value) -> Value {
    let mut flags = MemFlagsData::new();
    flags.set_endianness(match fx.tcx.data_layout.endian {
        rustc_abi::Endian::Big => cranelift_codegen::ir::Endianness::Big,
        rustc_abi::Endian::Little => cranelift_codegen::ir::Endianness::Little,
    });
    fx.bcx.ins().bitcast(dst_ty, flags, val)
}

pub(crate) fn type_zero_value(bcx: &mut FunctionBuilder<'_>, ty: Type) -> Value {
    if ty == types::I128 {
        let zero = bcx.ins().iconst(types::I64, 0);
        bcx.ins().iconcat(zero, zero)
    } else {
        bcx.ins().iconst(ty, 0)
    }
}

pub(crate) fn type_min_max_value(
    bcx: &mut FunctionBuilder<'_>,
    ty: Type,
    signed: bool,
) -> (Value, Value) {
    assert!(ty.is_int());

    if ty == types::I128 {
        if signed {
            let min = i128::MIN as u128;
            let min_lsb = bcx.ins().iconst(types::I64, min as u64 as i64);
            let min_msb = bcx.ins().iconst(types::I64, (min >> 64) as u64 as i64);
            let min = bcx.ins().iconcat(min_lsb, min_msb);

            let max = i128::MAX as u128;
            let max_lsb = bcx.ins().iconst(types::I64, max as u64 as i64);
            let max_msb = bcx.ins().iconst(types::I64, (max >> 64) as u64 as i64);
            let max = bcx.ins().iconcat(max_lsb, max_msb);

            return (min, max);
        } else {
            let min_half = bcx.ins().iconst(types::I64, 0);
            let min = bcx.ins().iconcat(min_half, min_half);

            let max_half = bcx.ins().iconst(types::I64, u64::MAX as i64);
            let max = bcx.ins().iconcat(max_half, max_half);

            return (min, max);
        }
    }

    let min = match (ty, signed) {
        (types::I8, false) | (types::I16, false) | (types::I32, false) | (types::I64, false) => {
            0i64
        }
        (types::I8, true) => i64::from(i8::MIN as u8),
        (types::I16, true) => i64::from(i16::MIN as u16),
        (types::I32, true) => i64::from(i32::MIN as u32),
        (types::I64, true) => i64::MIN,
        _ => unreachable!(),
    };

    let max = match (ty, signed) {
        (types::I8, false) => i64::from(u8::MAX),
        (types::I16, false) => i64::from(u16::MAX),
        (types::I32, false) => i64::from(u32::MAX),
        (types::I64, false) => u64::MAX as i64,
        (types::I8, true) => i64::from(i8::MAX as u8),
        (types::I16, true) => i64::from(i16::MAX as u16),
        (types::I32, true) => i64::from(i32::MAX as u32),
        (types::I64, true) => i64::MAX,
        _ => unreachable!(),
    };

    let (min, max) = (bcx.ins().iconst(ty, min), bcx.ins().iconst(ty, max));

    (min, max)
}

pub(crate) fn type_sign(ty: Ty<'_>) -> bool {
    match ty.kind() {
        ty::Ref(..) | ty::RawPtr(..) | ty::FnPtr(..) | ty::Char | ty::Uint(..) | ty::Bool => false,
        ty::Int(..) => true,
        ty::Float(..) => false, // `signed` is unused for floats
        _ => panic!("{}", ty),
    }
}

pub(crate) fn create_wrapper_function(
    module: &mut dyn Module,
    sig: Signature,
    wrapper_name: &str,
    callee_name: &str,
) {
    let wrapper_func_id = module.declare_function(wrapper_name, Linkage::Export, &sig).unwrap();
    let callee_func_id = module.declare_function(callee_name, Linkage::Import, &sig).unwrap();

    // On x86_64 the wrapper is a single `jmp` to the callee, as LLVM's tail call makes it: the
    // allocator shims (`__rust_alloc` and friends) run on every allocation, and a call + return
    // there costs a frame, a second return address and four instructions instead of one. The jump
    // leaves the caller's frame and return address as they are, so the wrapper needs no unwind
    // info (a leaf without stack, for SEH as for DWARF unwinders).
    if module.isa().triple().architecture == target_lexicon::Architecture::X86_64 {
        use cranelift_codegen::binemit::Reloc;
        use cranelift_module::ModuleReloc;
        let kind = if module.isa().triple().binary_format == target_lexicon::BinaryFormat::Elf {
            Reloc::X86CallPLTRel4
        } else {
            Reloc::X86CallPCRel4
        };
        let reloc = ModuleReloc { offset: 1, kind, name: callee_func_id.into(), addend: -4 };
        module.define_function_bytes(wrapper_func_id, 16, &[0xe9, 0, 0, 0, 0], &[reloc]).unwrap();
        return;
    }

    let mut ctx = Context::new();
    ctx.func.signature = sig;
    {
        let mut func_ctx = FunctionBuilderContext::new();
        let mut bcx = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);

        let block = bcx.create_block();
        bcx.switch_to_block(block);
        let func = &mut bcx.func.stencil;
        let args = func
            .signature
            .params
            .iter()
            .map(|param| func.dfg.append_block_param(block, param.value_type))
            .collect::<Vec<Value>>();

        let callee_func_ref = module.declare_func_in_func(callee_func_id, bcx.func);
        let call_inst = bcx.ins().call(callee_func_ref, &args);
        let results = bcx.inst_results(call_inst).to_vec(); // Clone to prevent borrow error

        bcx.ins().return_(&results);
        bcx.seal_all_blocks();
        bcx.finalize(module.target_config());
    }
    module.define_function(wrapper_func_id, &mut ctx).unwrap();
}

pub(crate) struct FunctionCx<'m, 'clif, 'tcx: 'm> {
    pub(crate) module: &'m mut dyn Module,
    pub(crate) debug_context: Option<&'clif mut DebugContext>,
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) target_config: TargetFrontendConfig, // Cached from module
    pub(crate) pointer_type: Type,                  // Cached from module
    pub(crate) constants_cx: ConstantCx<'tcx>,
    pub(crate) func_debug_cx: Option<FunctionDebugContext>,

    pub(crate) cgu_name: Symbol,
    pub(crate) instance: Instance<'tcx>,
    pub(crate) symbol_name: String,
    pub(crate) mir: &'tcx Body<'tcx>,
    pub(crate) fn_abi: &'tcx FnAbi<'tcx, Ty<'tcx>>,

    pub(crate) bcx: FunctionBuilder<'clif>,
    pub(crate) block_map: IndexVec<BasicBlock, Block>,
    pub(crate) local_map: IndexVec<Local, CPlace<'tcx>>,
    /// Statements not to emit: moves into temporaries that alias their source (`move_forwarding`).
    pub(crate) skipped_stmts: rustc_data_structures::fx::FxHashSet<rustc_middle::mir::Location>,

    /// When `#[track_caller]` is used, the implicit caller location is stored in this variable.
    pub(crate) caller_location: Option<CValue<'tcx>>,

    /// During cleanup the exception pointer is kept in this stack slot (see
    /// [`FunctionCx::exception_slot`]).
    pub(crate) exception_slot: Option<Pointer>,
    /// The blocks unwinding calls land in, one per cleanup block (storing the exception pointer
    /// and jumping to it) and one per reason to abort, shared by all calls that unwind there.
    pub(crate) landing_pads: rustc_data_structures::fx::FxHashMap<LandingPad, Block>,
    /// Whether calls that must abort when they unwind (`UnwindAction::Terminate`) are plain
    /// calls tagged with [`crate::debuginfo::terminate_tag`] rather than calls with a landing
    /// pad that aborts (see [`terminate_calls`]).
    pub(crate) terminate_calls: bool,
    /// Panic calls shared by all sites in this function that panic the same way (same panic
    /// function, same unwind action), see `codegen_panic_inner`. Without debuginfo only.
    pub(crate) shared_panics: rustc_data_structures::fx::FxHashMap<
        (rustc_attr_ir::lang_items::LangItem, SharedUnwind),
        Block,
    >,
    /// The functions this function calls directly, see [`FunctionCx::get_function_ref`].
    pub(crate) func_refs: rustc_data_structures::fx::FxHashMap<Instance<'tcx>, FuncRef>,

    pub(crate) clif_comments: crate::pretty_clif::CommentWriter,

    pub(crate) inline_asm: String,
    pub(crate) inline_asm_index: u32,
}

/// The unwind action of a shared panic call, see [`FunctionCx::shared_panics`].
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SharedUnwind {
    Continue,
    Unreachable,
    Cleanup(BasicBlock),
    // `UnwindTerminateReason` is a fieldless enum without `Hash`: its discriminant.
    Terminate(u8),
}

impl SharedUnwind {
    pub(crate) fn of(unwind: UnwindAction) -> Self {
        match unwind {
            UnwindAction::Continue => SharedUnwind::Continue,
            UnwindAction::Unreachable => SharedUnwind::Unreachable,
            UnwindAction::Cleanup(block) => SharedUnwind::Cleanup(block),
            UnwindAction::Terminate(reason) => SharedUnwind::Terminate(reason as u8),
        }
    }
}

/// Where an unwinding call lands, see [`FunctionCx::landing_pads`].
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum LandingPad {
    Cleanup(BasicBlock),
    Terminate(UnwindTerminateReason),
}

impl std::hash::Hash for LandingPad {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match *self {
            LandingPad::Cleanup(block) => block.hash(state),
            // `UnwindTerminateReason` is a fieldless enum without `Hash`.
            LandingPad::Terminate(reason) => std::mem::discriminant(&reason).hash(state),
        }
    }
}

impl<'tcx> LayoutOfHelpers<'tcx> for FunctionCx<'_, '_, 'tcx> {
    #[inline]
    fn handle_layout_err(&self, err: LayoutError<'tcx>, span: Span, ty: Ty<'tcx>) -> ! {
        FullyMonomorphizedLayoutCx(self.tcx).handle_layout_err(err, span, ty)
    }
}

impl<'tcx> FnAbiOfHelpers<'tcx> for FunctionCx<'_, '_, 'tcx> {
    #[inline]
    fn handle_fn_abi_err(
        &self,
        err: FnAbiError<'tcx>,
        span: Span,
        fn_abi_request: FnAbiRequest<'tcx>,
    ) -> ! {
        FullyMonomorphizedLayoutCx(self.tcx).handle_fn_abi_err(err, span, fn_abi_request)
    }
}

impl<'tcx> layout::HasTyCtxt<'tcx> for FunctionCx<'_, '_, 'tcx> {
    fn tcx<'b>(&'b self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> rustc_abi::HasDataLayout for FunctionCx<'_, '_, 'tcx> {
    fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
        &self.tcx.data_layout
    }
}

impl<'tcx> layout::HasTypingEnv<'tcx> for FunctionCx<'_, '_, 'tcx> {
    fn typing_env(&self) -> ty::TypingEnv<'tcx> {
        ty::TypingEnv::fully_monomorphized()
    }
}

impl<'tcx> HasTargetSpec for FunctionCx<'_, '_, 'tcx> {
    fn target_spec(&self) -> &Target {
        &self.tcx.sess.target
    }
}

impl<'tcx> FunctionCx<'_, '_, 'tcx> {
    pub(crate) fn monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<TyCtxt<'tcx>> + Copy,
    {
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            self.typing_env(),
            ty::EarlyBinder::bind(self.tcx, value),
        )
    }

    pub(crate) fn clif_type(&self, ty: Ty<'tcx>) -> Option<Type> {
        clif_type_from_ty(self.tcx, ty)
    }

    pub(crate) fn get_block(&self, bb: BasicBlock) -> Block {
        *self.block_map.get(bb).unwrap()
    }

    pub(crate) fn get_local_place(&mut self, local: Local) -> CPlace<'tcx> {
        *self.local_map.get(local).unwrap_or_else(|| {
            panic!("Local {:?} doesn't exist", local);
        })
    }

    /// The stack slot the landing pads store the exception pointer in, for the `UnwindResume`
    /// that ends their cleanup. Memory rather than an SSA variable: a variable became a block
    /// parameter of every cleanup block that more than one landing pad reaches and stayed live
    /// across the cleanup's drop calls, all register allocation work for a path that only runs
    /// while unwinding.
    pub(crate) fn exception_slot(&mut self) -> Pointer {
        if let Some(slot) = self.exception_slot {
            return slot;
        }
        let size = self.pointer_type.bytes();
        let slot = self.create_stack_slot(size, size);
        self.exception_slot = Some(slot);
        slot
    }

    pub(crate) fn create_stack_slot(&mut self, size: u32, align: u32) -> Pointer {
        assert!(
            size.is_multiple_of(align),
            "size must be a multiple of alignment (size={size}, align={align})"
        );
        debug_assert!(align.is_power_of_two(), "alignment must be a power of two (align={align})");

        let abi_align = if self.tcx.sess.target.arch == Arch::S390x { 8 } else { 16 };
        // Cranelift can only guarantee alignment up to the ABI alignment provided by the target.
        // If the requested alignment is less than the abi_align it can be used directly.
        if align <= abi_align {
            let stack_slot = self.bcx.create_sized_stack_slot(StackSlotData {
                kind: StackSlotKind::ExplicitSlot,
                size,
                // The maximum value of ilog2 is 31 which will always fit in a u8.
                align_shift: align.ilog2().try_into().unwrap(),
                key: None,
            });
            Pointer::stack_slot(stack_slot)
        } else {
            // Alignment is larger than the ABI alignment guaranteed. Dynamically realign a stack slot
            // instead. This wastes some space for the realignment.
            let stack_slot = self.bcx.create_sized_stack_slot(StackSlotData {
                kind: StackSlotKind::ExplicitSlot,
                size: size + align,
                align_shift: abi_align.ilog2().try_into().unwrap(),
                key: None,
            });
            let base_ptr = self.bcx.ins().stack_addr(self.pointer_type, stack_slot, 0);
            let misalign_offset = self.bcx.ins().band_imm_u(base_ptr, i64::from(align - 1));
            let align = self.bcx.ins().iconst(self.pointer_type, i64::from(align));
            let realign_offset = self.bcx.ins().isub(align, misalign_offset);
            Pointer::new(self.bcx.ins().iadd(base_ptr, realign_offset))
        }
    }

    pub(crate) fn set_debug_loc(&mut self, source_info: mir::SourceInfo) {
        if let Some(debug_context) = &mut self.debug_context {
            let (file_id, line, column) =
                debug_context.get_span_loc(self.tcx, self.mir.span, source_info.span);

            // Scopes only matter for the lexical blocks of variables (full debuginfo): leaving
            // them out otherwise keeps one source location per position.
            let scope = if self.tcx.sess.opts.debuginfo == rustc_session::config::DebugInfo::Full {
                source_info.scope.as_u32()
            } else {
                0
            };
            let source_loc =
                self.func_debug_cx.as_mut().unwrap().add_dbg_loc(file_id, line, column, scope);
            self.bcx.set_srcloc(source_loc);
        }
    }

    pub(crate) fn get_caller_location(&mut self, source_info: mir::SourceInfo) -> CValue<'tcx> {
        self.mir.caller_location_span(source_info, self.caller_location, self.tcx, |span| {
            let const_loc = self.tcx.span_as_caller_location(span);
            crate::constant::codegen_const_value(self, const_loc, self.tcx.caller_location_ty())
        })
    }
}

pub(crate) struct FullyMonomorphizedLayoutCx<'tcx>(pub(crate) TyCtxt<'tcx>);

impl<'tcx> LayoutOfHelpers<'tcx> for FullyMonomorphizedLayoutCx<'tcx> {
    #[inline]
    fn handle_layout_err(&self, err: LayoutError<'tcx>, span: Span, ty: Ty<'tcx>) -> ! {
        if let LayoutError::SizeOverflow(_)
        | LayoutError::InvalidSimd { .. }
        | LayoutError::ReferencesError(_) = err
        {
            self.0.sess.dcx().span_fatal(span, err.to_string())
        } else {
            self.0
                .sess
                .dcx()
                .span_fatal(span, format!("failed to get layout for `{}`: {}", ty, err))
        }
    }
}

impl<'tcx> FnAbiOfHelpers<'tcx> for FullyMonomorphizedLayoutCx<'tcx> {
    #[inline]
    fn handle_fn_abi_err(
        &self,
        err: FnAbiError<'tcx>,
        span: Span,
        fn_abi_request: FnAbiRequest<'tcx>,
    ) -> ! {
        codegen_handle_fn_abi_err(self.0, err, span, fn_abi_request).raise_fatal()
    }
}

impl<'tcx> layout::HasTyCtxt<'tcx> for FullyMonomorphizedLayoutCx<'tcx> {
    fn tcx<'b>(&'b self) -> TyCtxt<'tcx> {
        self.0
    }
}

impl<'tcx> rustc_abi::HasDataLayout for FullyMonomorphizedLayoutCx<'tcx> {
    fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
        &self.0.data_layout
    }
}

impl<'tcx> layout::HasTypingEnv<'tcx> for FullyMonomorphizedLayoutCx<'tcx> {
    fn typing_env(&self) -> ty::TypingEnv<'tcx> {
        ty::TypingEnv::fully_monomorphized()
    }
}

impl<'tcx> HasTargetSpec for FullyMonomorphizedLayoutCx<'tcx> {
    fn target_spec(&self) -> &Target {
        &self.0.sess.target
    }
}

/// Whether `UnwindAction::Terminate` calls are plain calls that the unwind tables mark to abort
/// (the default), or calls with a landing pad that aborts (`-Cllvm-args=clif-terminate=pads`,
/// as LLVM does). Plain calls cost no block, landing pad or block parameters; when one unwinds,
/// the panic aborts during the search for a handler, before any destructor runs: the panic's
/// message is printed as ever, then on Itanium-ABI targets "failed to initiate panic" instead
/// of "panic in a function that cannot unwind" (Rust's personality ends the search at a call
/// site its table leaves out); the SEH runtime calls the same panic function a landing pad
/// would. compiler_builtins keeps the pads: it may not call into core.
pub(crate) fn terminate_calls(tcx: TyCtxt<'_>) -> bool {
    if tcx.is_compiler_builtins(LOCAL_CRATE) {
        return false;
    }
    for opt in &tcx.sess.opts.cg.llvm_args {
        if let Some(value) = opt.strip_prefix("clif-terminate=") {
            return value != "pads";
        }
    }
    true
}

/// The symbols of the panic functions that `UnwindTerminateReason::{Abi, InCleanup}` call
/// (`None` where the lang item doesn't exist).
pub(crate) fn terminate_symbols(tcx: TyCtxt<'_>) -> [Option<String>; 2] {
    [UnwindTerminateReason::Abi, UnwindTerminateReason::InCleanup].map(|reason| {
        let def_id = tcx.lang_items().get(reason.lang_item())?;
        Some(tcx.symbol_name(Instance::mono(tcx, def_id)).name.to_owned())
    })
}

/// `v * k` for a multiplier known at compile time, such as a type's size: nothing for 1, a shift
/// for powers of two (which x86_64 folds into an address's scale), a multiply otherwise. Without
/// optimizations Cranelift lowers an `imul` by a constant as written: three cycles of latency on
/// every pointer offset and index.
pub(crate) fn mul_by_const(bcx: &mut FunctionBuilder<'_>, v: Value, k: i64) -> Value {
    let ty = bcx.func.dfg.value_type(v);
    let k = k as u64;
    if k == 0 {
        bcx.ins().iconst(ty, 0)
    } else if k == 1 {
        v
    } else if k.is_power_of_two() && k.trailing_zeros() < ty.bits() {
        bcx.ins().ishl_imm_u(v, i64::from(k.trailing_zeros()))
    } else {
        bcx.ins().imul_imm_u(v, k as i64)
    }
}
