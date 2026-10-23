//! The AOT driver uses [`cranelift_object`] to write object files suitable for linking into a
//! standalone executable.

use std::convert::Infallible;
use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;
use std::sync::{Arc, Condvar, Mutex};
use std::time::Instant;

use cranelift_object::{ObjectBuilder, ObjectModule};
use rustc_ast::expand::allocator::AllocatorMethod;
use rustc_attr_ir::Linkage as RLinkage;
use rustc_codegen_ssa::back::lto::ThinModule;
use rustc_codegen_ssa::back::write::{
    CodegenContext, FatLtoInput, ModuleConfig, SharedEmitter, TargetMachineFactoryFn, ThinLtoInput,
};
use rustc_codegen_ssa::traits::{ExtraBackendMethods, WriteBackendMethods};
use rustc_codegen_ssa::{CompiledModule, ModuleCodegen, ModuleKind};
use rustc_data_structures::profiling::SelfProfilerRef;
use rustc_errors::{DiagCtxt, DiagCtxtHandle};
use rustc_middle::dep_graph::WorkProduct;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::mono::{MonoItem, MonoItemData, Visibility};
use rustc_session::{BorrowedIncrCompSession, Session};
use rustc_session::config::{OptLevel, OutputFilenames, OutputType};
use rustc_span::Symbol;

use crate::base::CodegenedFunction;
use crate::debuginfo::TypeDebugContext;
use crate::global_asm::{GlobalAsmConfig, GlobalAsmContext};
use crate::prelude::*;
use crate::unwind_module::UnwindModule;

pub(crate) struct AotModule {
    producer: String,
    global_asm_config: GlobalAsmConfig,
    module: UnwindModule<ObjectModule>,
    debug_context: Option<DebugContext>,
    codegened_functions: Vec<CodegenedFunction>,
    global_asm: String,
    inline_mode: crate::inline::InlineMode,
}

fn make_module(tcx: TyCtxt<'_>, cgu_name: &str) -> AotModule {
    let isa = crate::build_isa(tcx.sess, false);

    let mut builder = ObjectBuilder::new(
        isa,
        cgu_name.to_owned() + ".o",
        cranelift_module::default_libcall_names(),
    )
    .unwrap();

    // Disable function sections by default on MSVC as it causes significant slowdowns with link.exe.
    // Maybe link.exe has exponential behavior when there are many sections with the same name? Also
    // explicitly disable it on MinGW as rustc already disables it by default on MinGW and as such
    // isn't tested. If rustc enables it in the future on MinGW, we can re-enable it too once it has
    // been on MinGW.
    let default_function_sections =
        tcx.sess.target.function_sections && !tcx.sess.target.is_like_windows;
    let function_sections =
        tcx.sess.opts.unstable_opts.function_sections.unwrap_or(default_function_sections);
    builder.per_function_section(function_sections);
    // Data in sections of their own too, as LLVM's `-fdata-sections` that rustc asks for with
    // function sections: with one data section per codegen unit, a single reference keeps all
    // of its data alive and with it every function its vtables point to, so `--gc-sections`
    // could keep most of the program.
    builder.per_data_object_section(function_sections);

    let module = UnwindModule::new(
        ObjectModule::new(builder),
        &rustc_symbol_mangling::eh_personality_symbol(tcx),
        true,
    );

    let producer = crate::debuginfo::producer(tcx.sess);
    let global_asm_config = GlobalAsmConfig::new(tcx.sess);
    let debug_context = DebugContext::new(tcx, module.isa(), false, cgu_name);
    let codegened_functions = vec![];
    let global_asm = String::new();
    let inline_mode = crate::inline::inline_mode(tcx.sess);

    AotModule {
        producer,
        global_asm_config,
        module,
        debug_context,
        codegened_functions,
        global_asm,
        inline_mode,
    }
}

fn emit_module(
    output_filenames: &OutputFilenames,
    prof: &SelfProfilerRef,
    module: UnwindModule<ObjectModule>,
    debug: Option<DebugContext>,
    kind: ModuleKind,
    name: String,
    global_asm_object: Option<PathBuf>,
    producer_str: &str,
) -> Result<CompiledModule, String> {
    let mut product = module.finish();

    if let Some(mut debug) = debug {
        debug.emit(&mut product);
    }

    if product.object.format() == cranelift_object::object::BinaryFormat::Elf {
        let comment_section = product.object.add_section(
            Vec::new(),
            b".comment".to_vec(),
            cranelift_object::object::SectionKind::OtherString,
        );
        let mut producer = vec![0];
        producer.extend(producer_str.as_bytes());
        producer.push(0);
        product.object.set_section_data(comment_section, producer, 1);
    }

    let tmp_file = output_filenames.temp_path_for_cgu(OutputType::Object, &name);
    let file = match File::create(&tmp_file) {
        Ok(file) => file,
        Err(err) => return Err(format!("error creating object file: {}", err)),
    };

    let mut file = BufWriter::new(file);
    if let Err(err) = product.object.write_stream(&mut file) {
        return Err(format!("error writing object file: {}", err));
    }
    let file = match file.into_inner() {
        Ok(file) => file,
        Err(err) => return Err(format!("error writing object file: {}", err)),
    };

    if prof.enabled() {
        prof.artifact_size(
            "object_file",
            tmp_file.file_name().unwrap().to_string_lossy(),
            file.metadata().unwrap().len(),
        );
    }

    Ok(CompiledModule {
        name,
        kind,
        object: Some(tmp_file),
        global_asm_object,
        dwarf_object: None,
        bytecode: None,
        assembly: None,
        llvm_ir: None,
    })
}

fn codegen_cgu(tcx: TyCtxt<'_>, cgu_name: Symbol) -> AotModule {
    let _timer = tcx.prof.generic_activity_with_arg("codegen cgu", cgu_name.as_str());
    let _ip = crate::insn_prof::scope("cg: codegen cgu (rest)");

    let cgu = tcx.codegen_unit(cgu_name);
    let mono_items = cgu.items_in_deterministic_order(tcx);

    let mut module = make_module(tcx, cgu_name.as_str());
    let mut type_dbg = TypeDebugContext::default();
    let mut constants_cx = crate::constant::ConstantCx::new();
    super::predefine_mono_items(tcx, &mut module.module, &mono_items);
    for (mono_item, item_data) in mono_items {
        match mono_item {
            MonoItem::Fn(instance) => {
                let flags = tcx.codegen_instance_attrs(instance.def).flags;
                if flags.contains(CodegenFnAttrFlags::NAKED) {
                    rustc_codegen_ssa::mir::naked_asm::codegen_naked_asm(
                        &mut GlobalAsmContext { tcx, global_asm: &mut module.global_asm },
                        instance,
                        MonoItemData {
                            linkage: RLinkage::External,
                            visibility: if item_data.linkage == RLinkage::Internal {
                                Visibility::Hidden
                            } else {
                                item_data.visibility
                            },
                            ..item_data
                        },
                    );
                    continue;
                }
                let codegened_function = crate::base::codegen_fn(
                    tcx,
                    cgu.name(),
                    module.debug_context.as_mut(),
                    &mut type_dbg,
                    Function::new(),
                    &mut module.module,
                    &mut constants_cx,
                    instance,
                );
                module.codegened_functions.push(codegened_function);
            }
            MonoItem::Static(def_id) => {
                let data_id = crate::constant::codegen_static(
                    tcx,
                    &mut module.module,
                    &mut constants_cx,
                    def_id,
                );
                if let Some(debug_context) = module.debug_context.as_mut() {
                    debug_context.define_static(tcx, &mut type_dbg, def_id, data_id);
                }
            }
            MonoItem::GlobalAsm(item_id) => {
                rustc_codegen_ssa::base::codegen_global_asm(
                    &mut GlobalAsmContext { tcx, global_asm: &mut module.global_asm },
                    item_id,
                );
            }
        }
    }
    crate::main_shim::maybe_create_entry_wrapper(tcx, &mut module.module, false, cgu.is_primary());

    module
}

fn compile_cgu(
    prof: &SelfProfilerRef,
    dcx: DiagCtxtHandle<'_>,
    output_filenames: &OutputFilenames,
    should_write_ir: bool,
    mut aot_module: AotModule,
    cgu_name: String,
    kind: ModuleKind,
) -> Result<CompiledModule, String> {
    prof.generic_activity_with_arg("compile functions", &*cgu_name).run(|| {
        cranelift_codegen::timing::set_thread_profiler(Box::new(super::MeasuremeProfiler(
            prof.clone(),
        )));

        prof.generic_activity_with_arg("inline functions", &*cgu_name).run(|| {
            let _ip = crate::insn_prof::scope("be: CLIF inliner");
            crate::inline::inline_cgu(aot_module.inline_mode, &mut aot_module.codegened_functions)
        });

        if crate::mem_libcalls::enabled(aot_module.module.isa()) {
            prof.generic_activity_with_arg("inline small memcpys", &*cgu_name).run(|| {
                let _ip = crate::insn_prof::scope("be: small memcpys");
                for codegened_func in &mut aot_module.codegened_functions {
                    crate::mem_libcalls::inline_small_mem_libcalls(&mut codegened_func.func);
                }
            });
        }

        let mut cached_context = Context::new();
        for codegened_func in aot_module.codegened_functions {
            crate::base::compile_fn(
                &prof,
                dcx,
                &output_filenames,
                should_write_ir,
                &mut cached_context,
                &mut aot_module.module,
                aot_module.debug_context.as_mut(),
                &mut aot_module.global_asm,
                codegened_func,
            );
        }
    });

    let global_asm_object_file =
        prof.generic_activity_with_arg("compile assembly", &*cgu_name).run(|| {
            if aot_module.global_asm.is_empty() {
                return Ok::<_, String>(None);
            }

            let global_asm_object_file = output_filenames.temp_path_ext_for_cgu("asm.o", &cgu_name);
            crate::global_asm::compile_global_asm(
                &aot_module.global_asm_config,
                aot_module.global_asm,
                &global_asm_object_file,
            )?;

            Ok(Some(global_asm_object_file))
        })?;

    prof.generic_activity_with_arg("write object file", &*cgu_name).run(|| {
        let _ip = crate::insn_prof::scope("be: write object file");
        emit_module(
            output_filenames,
            prof,
            aot_module.module,
            aot_module.debug_context,
            kind,
            cgu_name.clone(),
            global_asm_object_file,
            &aot_module.producer,
        )
    })
}

#[derive(Clone, Default)]
pub(crate) struct AotDriver {
    /// Set with `-Zthreads` > 1: codegen units translated ahead of rustc_codegen_ssa's loop.
    pub(crate) prefetch: Option<Arc<Prefetch>>,
}

/// Translates codegen units (MIR to CLIF) on rustc's other threads while rustc_codegen_ssa's
/// loop asks for them one by one on the main thread: that loop translates only its first
/// `-Zthreads` units in parallel and the rest serially, while Cranelift compiles them on the
/// worker threads. The runner starts once rustc_codegen_ssa asked for its first unit (it has
/// then decided which units to reuse: the ones it marked green), queues one job per unit in the
/// order the loop asks for them, at most `threads` at a time, and keeps at most `ahead` units
/// translated that the loop hasn't taken yet.
///
/// Nothing here waits for a job that hasn't started: a unit asked for while its job is still
/// queued is taken back and translated by the caller, and a running job never waits for the
/// main thread. So a thread that runs a job while it waits for other work (rayon steals) can't
/// deadlock, whichever thread it is.
#[derive(Default)]
pub(crate) struct Prefetch {
    state: Mutex<PrefetchState>,
    changed: Condvar,
}

#[derive(Default)]
struct PrefetchState {
    /// rustc_codegen_ssa asked for its first codegen unit.
    started: bool,
    /// rustc_codegen_ssa is done asking (or gave up).
    finished: bool,
    units: FxHashMap<Symbol, Unit>,
    /// Units queued or translating.
    in_flight: usize,
    /// Units translated that nobody took yet.
    ready: usize,
}

enum Unit {
    Queued,
    Translating,
    Ready(rustc_data_structures::sync::IntoDynSyncSend<(ModuleCodegen<AotModule>, u64)>),
    Taken,
}

/// Marks the prefetch finished when rustc_codegen_ssa returns or unwinds, so the runner stops.
pub(crate) struct FinishPrefetch<'a>(pub(crate) &'a Prefetch);

impl Drop for FinishPrefetch<'_> {
    fn drop(&mut self) {
        let mut state = self.0.state.lock().unwrap_or_else(|err| err.into_inner());
        state.finished = true;
        self.0.changed.notify_all();
    }
}

impl Prefetch {
    /// Queues the units' jobs until every unit is queued or taken, or rustc_codegen_ssa is done.
    pub(crate) fn run(&self, tcx: TyCtxt<'_>, threads: usize) {
        {
            let mut state = self.state.lock().unwrap();
            while !state.started && !state.finished {
                state = self.changed.wait(state).unwrap();
            }
            if state.finished {
                return;
            }
        }

        // The order of rustc_codegen_ssa's loop: largest and smallest first, then the second
        // largest and smallest, ... Units it reuses are green.
        let mut units =
            tcx.collect_and_partition_mono_items(()).codegen_units.iter().collect::<Vec<_>>();
        units.sort_by_key(|cgu| std::cmp::Reverse(cgu.size_estimate()));
        let (first_half, second_half) = units.split_at(units.len() / 2);
        let mut ordered = Vec::with_capacity(units.len());
        let mut second = second_half.iter().rev();
        for cgu in first_half {
            ordered.push(*cgu);
            if let Some(cgu) = second.next() {
                ordered.push(*cgu);
            }
        }
        ordered.extend(second);
        let units = ordered
            .into_iter()
            .filter(|cgu| {
                !tcx.dep_graph.is_fully_enabled()
                    || !tcx.dep_graph.is_green(&cgu.codegen_dep_node(tcx))
            })
            .map(|cgu| cgu.name())
            .collect::<Vec<_>>();

        let ahead = threads * 2;
        // Only runs with `-Zthreads` > 1, when rustc's types may cross threads.
        let proof = rustc_data_structures::sync::check_dyn_thread_safe()
            .expect("prefetch without parallel rustc");
        let data = proof.derive((self, tcx, units));
        rustc_thread_pool::scope(move |scope| {
            let (this, tcx, units) = data.into_inner();
            this.queue(tcx, units, threads, ahead, scope, proof);
        });
    }

    fn queue<'scope, 'tcx: 'scope>(
        &'scope self,
        tcx: TyCtxt<'tcx>,
        units: Vec<Symbol>,
        threads: usize,
        ahead: usize,
        scope: &rustc_thread_pool::Scope<'scope>,
        proof: rustc_data_structures::sync::FromDyn<()>,
    ) {
        for cgu_name in units {
            {
                let mut state = self.state.lock().unwrap();
                while (state.in_flight >= threads || state.ready >= ahead) && !state.finished {
                    state = self.changed.wait(state).unwrap();
                }
                if state.finished {
                    return;
                }
                if state.units.contains_key(&cgu_name) {
                    continue;
                }
                state.units.insert(cgu_name, Unit::Queued);
                state.in_flight += 1;
            }
            let job = proof.derive((self, tcx));
            scope.spawn(move |_| {
                let (this, tcx) = job.into_inner();
                this.translate(tcx, cgu_name)
            });
        }
    }

    fn translate(&self, tcx: TyCtxt<'_>, cgu_name: Symbol) {
        {
            let mut state = self.state.lock().unwrap();
            match state.units.get(&cgu_name) {
                Some(Unit::Queued) if !state.finished => {
                    state.units.insert(cgu_name, Unit::Translating);
                }
                // Taken back by the loop, or nobody needs it any more.
                _ => return,
            }
        }
        let unit = compile_codegen_unit(tcx, cgu_name);
        let mut state = self.state.lock().unwrap();
        state
            .units
            .insert(cgu_name, Unit::Ready(rustc_data_structures::sync::IntoDynSyncSend(unit)));
        state.in_flight -= 1;
        state.ready += 1;
        self.changed.notify_all();
    }

    /// The unit if a job translated it or is translating it; `None` if the caller should.
    fn take(&self, cgu_name: Symbol) -> Option<(ModuleCodegen<AotModule>, u64)> {
        let mut state = self.state.lock().unwrap();
        if !state.started {
            state.started = true;
            self.changed.notify_all();
        }
        loop {
            match state.units.get(&cgu_name) {
                None => {
                    state.units.insert(cgu_name, Unit::Taken);
                    return None;
                }
                Some(Unit::Queued) => {
                    // Its job hasn't started: don't wait for a thread to pick it up.
                    state.units.insert(cgu_name, Unit::Taken);
                    state.in_flight -= 1;
                    self.changed.notify_all();
                    return None;
                }
                Some(Unit::Translating) => state = self.changed.wait(state).unwrap(),
                Some(Unit::Ready(_)) => {
                    let Some(Unit::Ready(unit)) = state.units.insert(cgu_name, Unit::Taken) else {
                        unreachable!()
                    };
                    state.ready -= 1;
                    self.changed.notify_all();
                    return Some(unit.0);
                }
                Some(Unit::Taken) => unreachable!("codegen unit {cgu_name} asked for twice"),
            }
        }
    }
}

fn compile_codegen_unit(tcx: TyCtxt<'_>, cgu_name: Symbol) -> (ModuleCodegen<AotModule>, u64) {
    let start_time = Instant::now();

    let dep_node = tcx.codegen_unit(cgu_name).codegen_dep_node(tcx);
    let (module, _) = tcx.dep_graph.with_task(
        dep_node,
        tcx,
        || {
            let aot_module = codegen_cgu(tcx, cgu_name);
            ModuleCodegen::new_regular(cgu_name.as_str().to_owned(), aot_module)
        },
        Some(rustc_middle::dep_graph::hash_result),
    );

    let time_to_codegen = start_time.elapsed();

    // We assume that the cost to run LLVM on a CGU is proportional to
    // the time we needed for codegenning it.
    let cost = time_to_codegen.as_nanos() as u64;

    (module, cost)
}

impl ExtraBackendMethods for AotDriver {
    type Module = AotModule;

    fn codegen_allocator<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        module_name: &str,
        methods: &[AllocatorMethod],
    ) -> Self::Module {
        let mut allocator_module = make_module(tcx, module_name);
        crate::allocator::codegen(tcx, &mut allocator_module.module, methods);
        allocator_module
    }

    fn compile_codegen_unit(
        &self,
        tcx: TyCtxt<'_>,
        cgu_name: Symbol,
        _bitcode_needed: bool,
    ) -> (ModuleCodegen<Self::Module>, u64) {
        if let Some(unit) = self.prefetch.as_ref().and_then(|prefetch| prefetch.take(cgu_name)) {
            return unit;
        }
        compile_codegen_unit(tcx, cgu_name)
    }
}

impl WriteBackendMethods for AotDriver {
    type Module = AotModule;
    type ModuleBuffer = Infallible;
    type TargetMachine = ();
    type ThinData = Infallible;

    fn target_machine_factory(
        &self,
        _sess: &Session,
        _opt_level: OptLevel,
    ) -> TargetMachineFactoryFn<Self> {
        Arc::new(|_, _| ())
    }

    fn optimize_and_codegen_fat_lto(
        _sess: &Session,
        _cgcx: &CodegenContext,
        _shared_emitter: &SharedEmitter,
        _tm_factory: TargetMachineFactoryFn<Self>,
        _exported_symbols_for_lto: &[String],
        _each_linked_rlib_for_lto: &[PathBuf],
        _modules: Vec<FatLtoInput<Self>>,
    ) -> CompiledModule {
        unreachable!()
    }

    fn run_thin_lto(
        _cgcx: &CodegenContext,
        _prof: &SelfProfilerRef,
        _incr_comp_session: Option<&BorrowedIncrCompSession>,
        _dcx: rustc_errors::DiagCtxtHandle<'_>,
        _exported_symbols_for_lto: &[String],
        _each_linked_rlib_for_lto: &[PathBuf],
        _modules: Vec<ThinLtoInput<Self>>,
    ) -> (Vec<ThinModule<Self>>, Vec<WorkProduct>) {
        unreachable!()
    }

    fn optimize(
        _cgcx: &CodegenContext,
        _prof: &SelfProfilerRef,
        _shared_emitter: &SharedEmitter,
        _module: &mut ModuleCodegen<Self::Module>,
        _config: &ModuleConfig,
    ) {
    }

    fn optimize_and_codegen_thin(
        _cgcx: &CodegenContext,
        _prof: &SelfProfilerRef,
        _shared_emitter: &SharedEmitter,
        _tm_factory: TargetMachineFactoryFn<Self>,
        _thin: ThinModule<Self>,
    ) -> CompiledModule {
        unreachable!()
    }

    fn codegen(
        cgcx: &CodegenContext,
        prof: &SelfProfilerRef,
        shared_emitter: &SharedEmitter,
        module: ModuleCodegen<Self::Module>,
        config: &ModuleConfig,
    ) -> CompiledModule {
        let dcx = DiagCtxt::new(Box::new(shared_emitter.clone()));
        compile_cgu(
            prof,
            dcx.handle(),
            &cgcx.output_filenames,
            config.emit_ir,
            module.module_llvm,
            module.name,
            module.kind,
        )
        .unwrap_or_else(|err| dcx.handle().fatal(err))
    }

    fn serialize_module(_module: Self::Module, _is_thin: bool) -> Self::ModuleBuffer {
        unreachable!()
    }
}
