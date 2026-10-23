//! Which register allocator compiles each function.
//!
//! Register allocation is the largest part of compiling a function at opt-level 0 (about a third
//! of the backend's work on large crates), and the backtracking allocator costs several times
//! the single-pass one. The single-pass allocator's code is slower, though: with it everywhere,
//! test suites ran 14-35% more instructions. Without optimizations (`regalloc=mixed`, the default
//! there), the single-pass allocator compiles the functions where it saves the most and costs
//! the least at run time:
//! - code that typically runs once: the entry point (a test harness's `main`), `#[cold]`
//!   functions and test code (functions in a `tests`, `test` or `*_tests` module, and their
//!   closures);
//! - very large functions, where the backtracking allocator's cost grows faster than their
//!   size (a deserializer's `visit_map` of 30,000 instructions took 6 G instructions to
//!   allocate), and large loop-free ones, whose code runs at most once per call.
//! Everything else keeps the backtracking allocator.

use cranelift_codegen::ir::Function;
use cranelift_codegen::settings::RegallocAlgorithm;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_session::config::OptLevel;
use rustc_span::def_id::DefId;

/// Functions of at least this many CLIF instructions get the single-pass allocator.
const LARGE: usize = 1024;
/// Functions without loops of at least this many CLIF instructions get it too.
const LARGE_WITHOUT_LOOPS: usize = 256;

/// What `choose` needs to know about a function besides its body.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Hint {
    /// The ISA's allocator for every function.
    Isa,
    /// One per function; `runs_rarely`: entry point, `#[cold]` or test code.
    Mixed { runs_rarely: bool },
}

fn mixed(tcx: TyCtxt<'_>) -> bool {
    match crate::BackendConfig::from_opts(&tcx.sess.opts.cg.llvm_args)
        .ok()
        .and_then(|config| config.regalloc_algorithm)
    {
        Some(algorithm) => algorithm == "mixed",
        None => tcx.sess.opts.optimize == OptLevel::No,
    }
}

pub(crate) fn hint<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>, cold: bool) -> Hint {
    // One session per process.
    static MIXED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*MIXED.get_or_init(|| mixed(tcx)) {
        return Hint::Isa;
    }
    let def_id = instance.def_id();
    let runs_rarely = cold
        || tcx.entry_fn(()).is_some_and(|(entry, _)| entry == def_id)
        || (def_id.is_local() && in_test_module(tcx, def_id));
    Hint::Mixed { runs_rarely }
}

pub(crate) fn choose(hint: Hint, func: &Function) -> Option<RegallocAlgorithm> {
    let Hint::Mixed { runs_rarely } = hint else { return None };
    let insts = func.dfg.num_insts();
    let single_pass =
        runs_rarely || insts >= LARGE || (insts >= LARGE_WITHOUT_LOOPS && !has_loop(func));
    Some(if single_pass { RegallocAlgorithm::SinglePass } else { RegallocAlgorithm::Backtracking })
}

/// Whether `def_id` lies in a test module: one named `tests`, `test` or `*_tests` (the usual
/// names of `#[cfg(test)]` modules), at any depth.
fn in_test_module(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let mut cur = def_id;
    loop {
        let key = tcx.def_key(cur);
        if let Some(name) = key.get_opt_name()
            && matches!(tcx.def_kind(cur), DefKind::Mod)
        {
            let name = name.as_str();
            if name == "tests" || name == "test" || name.ends_with("_tests") {
                return true;
            }
        }
        match key.parent {
            Some(index) => cur = DefId { krate: cur.krate, index },
            None => return false,
        }
    }
}

fn has_loop(func: &Function) -> bool {
    let cfg = cranelift_codegen::flowgraph::ControlFlowGraph::with_function(func);
    let domtree = cranelift_codegen::dominator_tree::DominatorTree::with_function(func, &cfg);
    func.layout
        .blocks()
        .any(|block| cfg.succ_iter(block).any(|succ| domtree.block_dominates(succ, block)))
}
