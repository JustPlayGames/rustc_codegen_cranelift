//! The runtime side of panic unwinding on x86_64-pc-windows-msvc.
//!
//! Rust panics on MSVC targets are C++ exceptions (`_CxxThrowException` in `panic_unwind`), and
//! LLVM handles them with funclets and `__CxxFrameHandler3`. Cranelift has no funclets: its
//! `try_call` landing pads are blocks of the function itself, entered after the stack has been
//! unwound to the function's frame, like on Itanium-ABI targets. This module defines the three
//! functions that bridge the two, much as libgcc's `_GCC_specific_handler` does on windows-gnu:
//!
//! - [`SEH_PERSONALITY`], the language-specific handler in the `UNWIND_INFO` of every function
//!   with landing pads (`debuginfo/unwind.rs` writes it and its table of
//!   `(return offset, landing pad offset, kind)`). In the search phase, catch and terminate pads
//!   take C++ exceptions (like LLVM's `catch (...)`); in the unwind phase, cleanup pads run for
//!   Rust panics. It enters a pad with `RtlUnwindEx`, which restores the non-volatile registers
//!   and passes the pad a pointer to a heap copy of the exception object in `rax`: the original
//!   lives on the thrower's stack, which the unwind has released. All pads of one unwind share
//!   one copy, stashed in unused slots of the exception record. The search phase clears that
//!   stash in every frame it passes: a record can reuse the stack slot of an earlier exception's
//!   record and keep its stash (`RtlRaiseException` dispatches in user mode from a copy that
//!   writes only the record's parameters), and that stash names a copy its resume freed.
//! - [`SEH_RESUME`], called at the end of a cleanup pad: it moves the object onto its own stack,
//!   frees the copy and raises the C++ exception again from there, so the next handler, cranelift
//!   or C++ (`__CxxFrameHandler3` frames of the LLVM-built standard library), takes it from there.
//! - [`SEH_FREE`], called by catch pads after `catch_fn` took the payload out of the copy.
//!
//! Every object file that needs them gets its own local copy (about 1 KiB).

use cranelift_codegen::ir::{BlockArg, MemFlagsData, StackSlotData, StackSlotKind, UserFuncName};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

use crate::debuginfo::{SEH_FREE, SEH_PERSONALITY, SEH_RESUME};
use crate::prelude::*;

const CXX_EXCEPTION: i64 = 0xE06D7363;
const STATUS_UNWIND_CONSOLIDATE: i64 = 0x80000029;
const EXCEPTION_NONCONTINUABLE: i64 = 0x1;
const EXCEPTION_UNWINDING_OR_EXIT: i64 = 0x2 | 0x4;
const EXCEPTION_TARGET_UNWIND: i64 = 0x20;
const EXCEPTION_CONTINUE_SEARCH: i64 = 1;
const KIND_CLEANUP: i64 = 0;
const KIND_CATCH: i64 = 1;
const KIND_ABORT: i64 = crate::debuginfo::SEH_KIND_ABORT as i64;

/// Marks a heap copy (header word) and a stash in an exception record.
const COPY_MAGIC: i64 = 0x6367_636c_6966_6578;
const STASH_MAGIC: i64 = 0x5354_4153_4843_4c46;
/// Copy header: magic, the record's 4 parameters, object size; the object follows.
const COPY_HEADER: i64 = 48;
/// Largest exception object copied (Rust's is 24 bytes).
const MAX_OBJECT: i64 = 256;
/// `sizeof(CONTEXT)` on x86_64.
const CONTEXT_SIZE: u32 = 1232;

// EXCEPTION_RECORD
const REC_CODE: i32 = 0;
const REC_FLAGS: i32 = 4;
const REC_NPARAMS: i32 = 24;
const fn rec_info(i: i32) -> i32 {
    32 + 8 * i
}
// DISPATCHER_CONTEXT
const DC_CONTROL_PC: i32 = 0;
const DC_IMAGE_BASE: i32 = 8;
const DC_FUNCTION_ENTRY: i32 = 16;
const DC_HANDLER_DATA: i32 = 56;
const DC_HISTORY_TABLE: i32 = 64;

/// Defines the SEH runtime functions in `module`, local to it.
/// `abort`: the panic functions a call site of kind `SEH_KIND_ABORT + reason` calls, when this
/// object has such call sites (`None` inside: the lang item doesn't exist, the handler traps).
pub(crate) fn define(module: &mut dyn Module, abort: Option<&[Option<String>; 2]>) {
    let ptr = module.target_config().pointer_type();
    let call_conv = module.target_config().default_call_conv;
    let sig = |params: &[Type], returns: &[Type]| Signature {
        params: params.iter().map(|&t| AbiParam::new(t)).collect(),
        returns: returns.iter().map(|&t| AbiParam::new(t)).collect(),
        call_conv,
    };

    let personality = module
        .declare_function(SEH_PERSONALITY, Linkage::Local, &sig(&[ptr; 4], &[types::I32]))
        .unwrap();
    let resume = module.declare_function(SEH_RESUME, Linkage::Local, &sig(&[ptr], &[])).unwrap();
    let free = module.declare_function(SEH_FREE, Linkage::Local, &sig(&[ptr], &[])).unwrap();
    let copy = module
        .declare_function("__cg_clif_seh_copy", Linkage::Local, &sig(&[ptr], &[ptr]))
        .unwrap();

    let imports = Imports {
        rtl_unwind_ex: module
            .declare_function("RtlUnwindEx", Linkage::Import, &sig(&[ptr; 6], &[]))
            .unwrap(),
        raise_exception: module
            .declare_function(
                "RaiseException",
                Linkage::Import,
                &sig(&[types::I32, types::I32, types::I32, ptr], &[]),
            )
            .unwrap(),
        get_process_heap: module
            .declare_function("GetProcessHeap", Linkage::Import, &sig(&[], &[ptr]))
            .unwrap(),
        heap_alloc: module
            .declare_function("HeapAlloc", Linkage::Import, &sig(&[ptr, types::I32, ptr], &[ptr]))
            .unwrap(),
        heap_free: module
            .declare_function(
                "HeapFree",
                Linkage::Import,
                &sig(&[ptr, types::I32, ptr], &[types::I32]),
            )
            .unwrap(),
        copy,
        abort: abort.map(|symbols| {
            symbols.each_ref().map(|symbol| {
                symbol.as_ref().map(|symbol| {
                    module.declare_function(symbol, Linkage::Import, &sig(&[], &[])).unwrap()
                })
            })
        }),
    };

    for (func_id, body) in [
        (
            personality,
            define_personality as fn(&mut dyn Module, &mut FunctionBuilder<'_>, &Imports, Type),
        ),
        (resume, define_resume),
        (free, define_free),
        (copy, define_copy),
    ] {
        let decl = module.declarations().get_function_decl(func_id);
        let mut func = Function::with_name_signature(
            UserFuncName::user(0, func_id.as_u32()),
            decl.signature.clone(),
        );
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut bcx = FunctionBuilder::new(&mut func, &mut builder_ctx);
        body(module, &mut bcx, &imports, ptr);
        bcx.seal_all_blocks();
        bcx.finalize(module.target_config());

        if cfg!(debug_assertions) {
            cranelift_codegen::verify_function(&func, module.isa())
                .unwrap_or_else(|err| panic!("{}", err));
        }
        let mut ctx = Context::for_function(func);
        module.define_function(func_id, &mut ctx).unwrap();
    }
}

struct Imports {
    rtl_unwind_ex: FuncId,
    raise_exception: FuncId,
    get_process_heap: FuncId,
    heap_alloc: FuncId,
    heap_free: FuncId,
    copy: FuncId,
    /// See [`define`].
    abort: Option<[Option<FuncId>; 2]>,
}

fn call(
    module: &mut dyn Module,
    bcx: &mut FunctionBuilder<'_>,
    f: FuncId,
    args: &[Value],
) -> Option<Value> {
    let func_ref = module.declare_func_in_func(f, bcx.func);
    let inst = bcx.ins().call(func_ref, args);
    bcx.inst_results(inst).first().copied()
}

fn fail(bcx: &mut FunctionBuilder<'_>) {
    bcx.ins().trap(TrapCode::user(1 /* unreachable */).unwrap());
}

fn load(bcx: &mut FunctionBuilder<'_>, ty: Type, addr: Value, offset: i32) -> Value {
    bcx.ins().load(ty, MemFlagsData::trusted(), addr, offset)
}

fn uload32(bcx: &mut FunctionBuilder<'_>, addr: Value, offset: i32) -> Value {
    bcx.ins().uload32(MemFlagsData::trusted(), addr, offset)
}

fn store(bcx: &mut FunctionBuilder<'_>, value: Value, addr: Value, offset: i32) {
    bcx.ins().store(MemFlagsData::trusted(), value, addr, offset);
}

/// `personality(rec, frame, context, dispatcher_context) -> EXCEPTION_DISPOSITION`
fn define_personality(
    module: &mut dyn Module,
    bcx: &mut FunctionBuilder<'_>,
    imports: &Imports,
    ptr: Type,
) {
    let entry = bcx.create_block();
    let lookup = bcx.create_block();
    let lookup_body = bcx.create_block();
    let lookup_next = bcx.create_block();
    let found = bcx.create_block();
    let dispatch = bcx.create_block();
    let dispatch_cxx = bcx.create_block();
    let dispatch_catch = bcx.create_block();
    let unwinding = bcx.create_block();
    let unwinding_cleanup = bcx.create_block();
    let not_cxx = bcx.create_block();
    let consolidate = bcx.create_block();
    let consolidate_inner = bcx.create_block();
    let unwinding_copy = bcx.create_block();
    let unwinding_have_copy = bcx.create_block();
    let enter_pad = bcx.create_block();
    let continue_search = bcx.create_block();

    bcx.append_block_params_for_function_params(entry);
    bcx.switch_to_block(entry);
    let [rec, frame, _context, dc] = *bcx.block_params(entry) else { unreachable!() };
    let table = load(bcx, ptr, dc, DC_HANDLER_DATA);
    let function_entry = load(bcx, ptr, dc, DC_FUNCTION_ENTRY);
    let image_base = load(bcx, ptr, dc, DC_IMAGE_BASE);
    let begin = uload32(bcx, function_entry, 0);
    let fn_start = bcx.ins().iadd(image_base, begin);
    let control_pc = load(bcx, ptr, dc, DC_CONTROL_PC);
    let offset = bcx.ins().isub(control_pc, fn_start);
    let count = uload32(bcx, table, 0);
    let zero = bcx.ins().iconst(ptr, 0);
    bcx.ins().jump(lookup, &[BlockArg::Value(zero)]);

    // Linear search of the (return offset, landing pad offset, kind) entries.
    let i = bcx.append_block_param(lookup, ptr);
    bcx.switch_to_block(lookup);
    let done = bcx.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, i, count);
    bcx.ins().brif(done, continue_search, &[], lookup_body, &[]);

    bcx.switch_to_block(lookup_body);
    let entry_offset = bcx.ins().imul_imm_u(i, 12);
    let entry_addr = bcx.ins().iadd(table, entry_offset);
    let ret_offset = uload32(bcx, entry_addr, 4);
    let is_entry = bcx.ins().icmp(IntCC::Equal, ret_offset, offset);
    bcx.ins().brif(is_entry, found, &[], lookup_next, &[]);

    bcx.switch_to_block(lookup_next);
    let next = bcx.ins().iadd_imm_s(i, 1);
    bcx.ins().jump(lookup, &[BlockArg::Value(next)]);

    bcx.switch_to_block(found);
    let pad_offset = uload32(bcx, entry_addr, 8);
    let kind = uload32(bcx, entry_addr, 12);
    let pad = bcx.ins().iadd(fn_start, pad_offset);
    let flags = uload32(bcx, rec, REC_FLAGS);
    let code = uload32(bcx, rec, REC_CODE);
    let unwinding_flags = bcx.ins().band_imm_u(flags, EXCEPTION_UNWINDING_OR_EXIT);
    bcx.ins().brif(unwinding_flags, unwinding, &[], dispatch, &[]);

    // Search phase: catch and terminate pads take C++ exceptions only.
    bcx.switch_to_block(dispatch);
    let not_cxx_code = bcx.ins().icmp_imm_u(IntCC::NotEqual, code, CXX_EXCEPTION);
    let dispatch_clear = bcx.create_block();
    bcx.ins().brif(not_cxx_code, continue_search, &[], dispatch_clear, &[]);

    // A search phase starts a new dispatch of `rec`: drop a stash in it before any pad of this
    // frame or a frame above can read it. It can be an earlier exception's, whose record had the
    // same address and whose copy that exception's resume freed (two raises from one resume call
    // site, e.g. an inlined callee's cleanup and a cleanup of the same frame): `copy` would hand
    // the freed copy to the next pad, which frees it again (STATUS_HEAP_CORRUPTION). Every frame
    // whose pads the unwind phase can enter has this handler, so the search phase passes here
    // before; a catch pad's copy is then the only stash an unwind reads.
    bcx.switch_to_block(dispatch_clear);
    let no_stash = bcx.ins().iconst(ptr, 0);
    store(bcx, no_stash, rec, rec_info(12));
    let is_cleanup = bcx.ins().icmp_imm_u(IntCC::Equal, kind, KIND_CLEANUP);
    bcx.ins().brif(is_cleanup, continue_search, &[], dispatch_cxx, &[]);

    bcx.switch_to_block(dispatch_cxx);
    let is_catch = bcx.ins().icmp_imm_u(IntCC::Equal, kind, KIND_CATCH);
    if let Some(abort) = imports.abort {
        // A call that must abort without a landing pad: abort here, in the search phase, with
        // the panic function its terminate pad would call.
        let dispatch_pad = bcx.create_block();
        let abort_any = bcx.create_block();
        let abort_blocks = [bcx.create_block(), bcx.create_block()];
        bcx.ins().brif(is_catch, dispatch_catch, &[], dispatch_pad, &[]);

        bcx.switch_to_block(dispatch_pad);
        let is_abort =
            bcx.ins().icmp_imm_u(IntCC::UnsignedGreaterThanOrEqual, kind, KIND_ABORT);
        bcx.ins().brif(
            is_abort,
            abort_any,
            &[],
            enter_pad,
            &[BlockArg::Value(rec), BlockArg::Value(zero)],
        );

        bcx.switch_to_block(abort_any);
        let in_cleanup = bcx.ins().icmp_imm_u(IntCC::Equal, kind, KIND_ABORT + 1);
        bcx.ins().brif(in_cleanup, abort_blocks[1], &[], abort_blocks[0], &[]);
        for (block, func) in abort_blocks.into_iter().zip(abort) {
            bcx.switch_to_block(block);
            bcx.set_cold_block(block);
            if let Some(func) = func {
                call(module, bcx, func, &[]);
            }
            fail(bcx);
        }
    } else {
        bcx.ins().brif(
            is_catch,
            dispatch_catch,
            &[],
            enter_pad,
            &[BlockArg::Value(rec), BlockArg::Value(zero)],
        );
    }

    bcx.switch_to_block(dispatch_catch);
    // null for foreign exceptions: `catch_fn` aborts on them, like LLVM's catch (...) pad.
    let value = call(module, bcx, imports.copy, &[rec]).unwrap();
    bcx.ins().jump(enter_pad, &[BlockArg::Value(rec), BlockArg::Value(value)]);

    // Unwind phase: run cleanup pads for Rust panics (foreign unwinds skip them).
    bcx.switch_to_block(unwinding);
    let target = bcx.ins().band_imm_u(flags, EXCEPTION_TARGET_UNWIND);
    let target = bcx.ins().icmp_imm_u(IntCC::NotEqual, target, 0);
    let not_cleanup = bcx.ins().icmp_imm_u(IntCC::NotEqual, kind, KIND_CLEANUP);
    let skip = bcx.ins().bor(target, not_cleanup);
    bcx.ins().brif(skip, continue_search, &[], unwinding_cleanup, &[]);

    bcx.switch_to_block(unwinding_cleanup);
    let is_cxx = bcx.ins().icmp_imm_u(IntCC::Equal, code, CXX_EXCEPTION);
    bcx.ins().brif(is_cxx, unwinding_copy, &[BlockArg::Value(rec)], not_cxx, &[]);

    // The C++ runtime's unwinds to its catch blocks (vcruntime's `_UnwindNestedFrames`) are
    // STATUS_UNWIND_CONSOLIDATE with the thrown exception's record in ExceptionInformation[6].
    bcx.switch_to_block(not_cxx);
    let is_consolidate = bcx.ins().icmp_imm_u(IntCC::Equal, code, STATUS_UNWIND_CONSOLIDATE);
    bcx.ins().brif(is_consolidate, consolidate, &[], continue_search, &[]);

    bcx.switch_to_block(consolidate);
    let nparams = uload32(bcx, rec, REC_NPARAMS);
    let enough = bcx.ins().icmp_imm_u(IntCC::UnsignedGreaterThanOrEqual, nparams, 7);
    let inner = load(bcx, ptr, rec, rec_info(6));
    let inner_set = bcx.ins().icmp_imm_u(IntCC::NotEqual, inner, 0);
    let usable = bcx.ins().band(enough, inner_set);
    bcx.ins().brif(usable, consolidate_inner, &[], continue_search, &[]);

    bcx.switch_to_block(consolidate_inner);
    let inner_code = uload32(bcx, inner, REC_CODE);
    let inner_cxx = bcx.ins().icmp_imm_u(IntCC::Equal, inner_code, CXX_EXCEPTION);
    bcx.ins().brif(inner_cxx, unwinding_copy, &[BlockArg::Value(inner)], continue_search, &[]);

    let cxx = bcx.append_block_param(unwinding_copy, ptr);
    bcx.switch_to_block(unwinding_copy);
    let value = call(module, bcx, imports.copy, &[cxx]).unwrap();
    bcx.ins().brif(value, unwinding_have_copy, &[], continue_search, &[]);

    bcx.switch_to_block(unwinding_have_copy);
    bcx.ins().jump(enter_pad, &[BlockArg::Value(cxx), BlockArg::Value(value)]);

    // RtlUnwindEx(frame, pad, rec, value, scratch context, history table): never returns.
    // It captures the current context into its ContextRecord argument and works in it, so it
    // gets a buffer of its own, never a context an unwind in progress still uses.
    let unwind_rec = bcx.append_block_param(enter_pad, ptr);
    let value = bcx.append_block_param(enter_pad, ptr);
    bcx.switch_to_block(enter_pad);
    let scratch = bcx.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        CONTEXT_SIZE,
        4,
    ));
    let scratch = bcx.ins().stack_addr(ptr, scratch, 0);
    let history = load(bcx, ptr, dc, DC_HISTORY_TABLE);
    call(module, bcx, imports.rtl_unwind_ex, &[frame, pad, unwind_rec, value, scratch, history]);
    fail(bcx);

    bcx.switch_to_block(continue_search);
    let disposition = bcx.ins().iconst(types::I32, EXCEPTION_CONTINUE_SEARCH);
    bcx.ins().return_(&[disposition]);
}

/// `copy(rec) -> object copy or null`: the heap copy of the Rust panic object thrown by `rec`
/// (a C++ exception whose type is named "rust_panic"), shared by all pads of one unwind through
/// a stash in the record's unused ExceptionInformation[12..15]; null for other exceptions.
fn define_copy(
    module: &mut dyn Module,
    bcx: &mut FunctionBuilder<'_>,
    imports: &Imports,
    ptr: Type,
) {
    let entry = bcx.create_block();
    let null = bcx.create_block();
    bcx.append_block_params_for_function_params(entry);
    bcx.switch_to_block(entry);
    let rec = bcx.block_params(entry)[0];

    let check = |bcx: &mut FunctionBuilder<'_>, cond: Value| {
        let next = bcx.create_block();
        bcx.ins().brif(cond, next, &[], null, &[]);
        bcx.switch_to_block(next);
    };

    // A C++ exception with a ThrowInfo...
    let code = uload32(bcx, rec, REC_CODE);
    let c = bcx.ins().icmp_imm_u(IntCC::Equal, code, CXX_EXCEPTION);
    check(bcx, c);
    let nparams = uload32(bcx, rec, REC_NPARAMS);
    let c = bcx.ins().icmp_imm_u(IntCC::Equal, nparams, 4);
    check(bcx, c);
    let magic = load(bcx, ptr, rec, rec_info(0));
    let magic_low = bcx.ins().iadd_imm_s(magic, -0x1993_0520);
    let c = bcx.ins().icmp_imm_u(IntCC::UnsignedLessThanOrEqual, magic_low, 2);
    check(bcx, c);
    let object = load(bcx, ptr, rec, rec_info(1));
    let c = bcx.ins().icmp_imm_u(IntCC::NotEqual, object, 0);
    check(bcx, c);
    let throw_info = load(bcx, ptr, rec, rec_info(2));
    let c = bcx.ins().icmp_imm_u(IntCC::NotEqual, throw_info, 0);
    check(bcx, c);
    let base = load(bcx, ptr, rec, rec_info(3));

    // ...whose first catchable type is named "rust_panic" (types match by name across modules).
    let rva = uload32(bcx, throw_info, 12);
    let catchable_types = bcx.ins().iadd(base, rva);
    let n = bcx.ins().sload32(MemFlagsData::trusted(), catchable_types, 0);
    let c = bcx.ins().icmp_imm_s(IntCC::SignedGreaterThanOrEqual, n, 1);
    check(bcx, c);
    let rva = uload32(bcx, catchable_types, 4);
    let catchable_type = bcx.ins().iadd(base, rva);
    let rva = uload32(bcx, catchable_type, 4);
    let type_descriptor = bcx.ins().iadd(base, rva);
    for (i, &byte) in b"rust_panic\0".iter().enumerate() {
        let b =
            bcx.ins().uload8(types::I32, MemFlagsData::trusted(), type_descriptor, 16 + i as i32);
        let c = bcx.ins().icmp_imm_u(IntCC::Equal, b, i64::from(byte));
        check(bcx, c);
    }
    let size = uload32(bcx, catchable_type, 20);
    let c = bcx.ins().icmp_imm_u(IntCC::NotEqual, size, 0);
    check(bcx, c);
    let c = bcx.ins().icmp_imm_u(IntCC::UnsignedLessThanOrEqual, size, MAX_OBJECT);
    check(bcx, c);

    // Already copied for this unwind?
    let stashed = bcx.create_block();
    let fresh = bcx.create_block();
    let stash_magic = load(bcx, ptr, rec, rec_info(12));
    let stash_copy = load(bcx, ptr, rec, rec_info(13));
    let stash_check = load(bcx, ptr, rec, rec_info(14));
    let expected = bcx.ins().bxor(stash_copy, rec);
    let c1 = bcx.ins().icmp_imm_u(IntCC::Equal, stash_magic, STASH_MAGIC);
    let c2 = bcx.ins().icmp(IntCC::Equal, stash_check, expected);
    let c = bcx.ins().band(c1, c2);
    bcx.ins().brif(c, stashed, &[], fresh, &[]);

    bcx.switch_to_block(stashed);
    bcx.ins().return_(&[stash_copy]);

    bcx.switch_to_block(fresh);
    let heap = call(module, bcx, imports.get_process_heap, &[]).unwrap();
    let flags = bcx.ins().iconst(types::I32, 0);
    let alloc_size = bcx.ins().iadd_imm_s(size, COPY_HEADER);
    let mem = call(module, bcx, imports.heap_alloc, &[heap, flags, alloc_size]).unwrap();
    let allocated = bcx.create_block();
    let oom = bcx.create_block();
    bcx.ins().brif(mem, allocated, &[], oom, &[]);
    bcx.switch_to_block(oom);
    fail(bcx);

    bcx.switch_to_block(allocated);
    let v = bcx.ins().iconst(ptr, COPY_MAGIC);
    store(bcx, v, mem, 0);
    for i in 0..4 {
        let param = load(bcx, ptr, rec, rec_info(i));
        store(bcx, param, mem, 8 + 8 * i);
    }
    store(bcx, size, mem, 40);
    let copy = bcx.ins().iadd_imm_s(mem, COPY_HEADER);
    let target_config = module.target_config();
    bcx.call_memcpy(target_config, copy, object, size);
    let v = bcx.ins().iconst(ptr, STASH_MAGIC);
    store(bcx, v, rec, rec_info(12));
    store(bcx, copy, rec, rec_info(13));
    let check_value = bcx.ins().bxor(copy, rec);
    store(bcx, check_value, rec, rec_info(14));
    bcx.ins().return_(&[copy]);

    bcx.switch_to_block(null);
    let zero = bcx.ins().iconst(ptr, 0);
    bcx.ins().return_(&[zero]);
}

/// Returns the copy header of `obj`, checking its magic.
fn copy_header(bcx: &mut FunctionBuilder<'_>, obj: Value) -> Value {
    let header = bcx.ins().iadd_imm_s(obj, -COPY_HEADER);
    let magic = load(bcx, obj.type_of(bcx), header, 0);
    let ok = bcx.create_block();
    let bad = bcx.create_block();
    let c = bcx.ins().icmp_imm_u(IntCC::Equal, magic, COPY_MAGIC);
    bcx.ins().brif(c, ok, &[], bad, &[]);
    bcx.switch_to_block(bad);
    fail(bcx);
    bcx.switch_to_block(ok);
    header
}

trait TypeOf {
    fn type_of(self, bcx: &FunctionBuilder<'_>) -> Type;
}
impl TypeOf for Value {
    fn type_of(self, bcx: &FunctionBuilder<'_>) -> Type {
        bcx.func.dfg.value_type(self)
    }
}

/// `resume(obj) -> !`: raise the panic again, from this frame, with the object on its stack.
fn define_resume(
    module: &mut dyn Module,
    bcx: &mut FunctionBuilder<'_>,
    imports: &Imports,
    ptr: Type,
) {
    let entry = bcx.create_block();
    let non_null = bcx.create_block();
    let null = bcx.create_block();
    bcx.append_block_params_for_function_params(entry);
    bcx.switch_to_block(entry);
    let obj = bcx.block_params(entry)[0];
    bcx.ins().brif(obj, non_null, &[], null, &[]);
    bcx.switch_to_block(null);
    fail(bcx);

    bcx.switch_to_block(non_null);
    let header = copy_header(bcx, obj);
    let size = load(bcx, ptr, header, 40);
    let local = bcx.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        MAX_OBJECT as u32,
        4,
    ));
    let local = bcx.ins().stack_addr(ptr, local, 0);
    let target_config = module.target_config();
    bcx.call_memcpy(target_config, local, obj, size);

    let args = bcx.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 32, 3));
    let args = bcx.ins().stack_addr(ptr, args, 0);
    for i in 0..4 {
        let param = if i == 1 { local } else { load(bcx, ptr, header, 8 + 8 * i) };
        store(bcx, param, args, 8 * i);
    }

    let heap = call(module, bcx, imports.get_process_heap, &[]).unwrap();
    let flags = bcx.ins().iconst(types::I32, 0);
    call(module, bcx, imports.heap_free, &[heap, flags, header]);

    let code = bcx.ins().iconst(types::I32, CXX_EXCEPTION);
    let flags = bcx.ins().iconst(types::I32, EXCEPTION_NONCONTINUABLE);
    let nparams = bcx.ins().iconst(types::I32, 4);
    call(module, bcx, imports.raise_exception, &[code, flags, nparams, args]);
    fail(bcx);
}

/// `free(obj)`: release a copy after a catch pad (null for foreign exceptions).
fn define_free(
    module: &mut dyn Module,
    bcx: &mut FunctionBuilder<'_>,
    imports: &Imports,
    _ptr: Type,
) {
    let entry = bcx.create_block();
    let non_null = bcx.create_block();
    let done = bcx.create_block();
    bcx.append_block_params_for_function_params(entry);
    bcx.switch_to_block(entry);
    let obj = bcx.block_params(entry)[0];
    bcx.ins().brif(obj, non_null, &[], done, &[]);

    bcx.switch_to_block(non_null);
    let header = copy_header(bcx, obj);
    let heap = call(module, bcx, imports.get_process_heap, &[]).unwrap();
    let flags = bcx.ins().iconst(types::I32, 0);
    call(module, bcx, imports.heap_free, &[heap, flags, header]);
    bcx.ins().jump(done, &[]);

    bcx.switch_to_block(done);
    bcx.ins().return_(&[]);
}
