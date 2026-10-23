//! Opt-in instruction counts per compilation phase, for compile-speed work.
//!
//! Set `CG_CLIF_INSN_PROF=<file>` and every rustc run appends one line per phase to that file:
//! `crate<TAB>phase<TAB>self instructions<TAB>total instructions<TAB>count`. Counts are user-space
//! instructions retired by the thread running the phase (Linux perf counters), so phases on the
//! codegen worker threads are measured too, which `-Zself-profile-counter=instructions:u` can't do.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

static PATH: OnceLock<Option<String>> = OnceLock::new();

fn path() -> Option<&'static str> {
    PATH.get_or_init(|| std::env::var("CG_CLIF_INSN_PROF").ok()).as_deref()
}

#[derive(Default, Clone, Copy)]
struct Acc {
    self_: u64,
    total: u64,
    count: u64,
}

static TOTALS: Mutex<Option<HashMap<&'static str, Acc>>> = Mutex::new(None);

struct Frame {
    name: &'static str,
    start: u64,
    child: u64,
}

static FN_ROWS: Mutex<Vec<String>> = Mutex::new(Vec::new());

thread_local! {
    static FN_ACC: RefCell<Option<HashMap<&'static str, u64>>> = const { RefCell::new(None) };
    static FD: i64 = open_counter();
    static STACK: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
}

#[repr(C)]
struct PerfEventAttr {
    type_: u32,
    size: u32,
    config: u64,
    sample_period: u64,
    sample_type: u64,
    read_format: u64,
    flags: u64,
    rest: [u64; 10],
}

unsafe extern "C" {
    fn syscall(n: i64, ...) -> i64;
    fn read(fd: i32, buf: *mut u8, n: usize) -> isize;
}

fn open_counter() -> i64 {
    if !cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        return -1;
    }
    let mut attr = PerfEventAttr {
        type_: 0, // PERF_TYPE_HARDWARE
        size: std::mem::size_of::<PerfEventAttr>() as u32,
        config: 1, // PERF_COUNT_HW_INSTRUCTIONS
        sample_period: 0,
        sample_type: 0,
        read_format: 0,
        flags: (1 << 5) | (1 << 6), // exclude_kernel, exclude_hv
        rest: [0; 10],
    };
    // perf_event_open(attr, pid = this thread, cpu = any, group = none, flags = 0)
    unsafe { syscall(298, &mut attr as *mut PerfEventAttr, 0i64, -1i64, -1i64, 0i64) }
}

fn now() -> u64 {
    FD.with(|&fd| {
        if fd < 0 {
            return 0;
        }
        let mut v = 0u64;
        unsafe { read(fd as i32, &mut v as *mut u64 as *mut u8, 8) };
        v
    })
}

pub(crate) struct Scope(bool);

#[inline]
pub(crate) fn scope(name: &'static str) -> Scope {
    if path().is_none() {
        return Scope(false);
    }
    let start = now();
    STACK.with(|s| s.borrow_mut().push(Frame { name, start, child: 0 }));
    Scope(true)
}

impl Drop for Scope {
    fn drop(&mut self) {
        if !self.0 {
            return;
        }
        let t = now();
        STACK.with(|s| {
            let mut s = s.borrow_mut();
            let f = s.pop().unwrap();
            let total = t.saturating_sub(f.start);
            if let Some(p) = s.last_mut() {
                p.child += total;
            }
            let mut g = TOTALS.lock().unwrap();
            let a = g.get_or_insert_with(HashMap::new).entry(f.name).or_default();
            a.self_ += total.saturating_sub(f.child);
            FN_ACC.with(|acc| {
                if let Some(acc) = acc.borrow_mut().as_mut() {
                    *acc.entry(f.name).or_default() += total.saturating_sub(f.child);
                }
            });
            a.total += total;
            a.count += 1;
        });
    }
}

pub(crate) fn enabled() -> bool {
    path().is_some()
}

/// Starts collecting per-phase counts of one function (on this thread).
pub(crate) fn fn_begin() {
    if path().is_some() {
        FN_ACC.with(|acc| *acc.borrow_mut() = Some(HashMap::new()));
    }
}

/// Records one row for the function whose counts `fn_begin` started.
pub(crate) fn fn_end(symbol: &str, class: u8, insts: usize, blocks: usize, has_loop: bool) {
    if path().is_none() {
        return;
    }
    let Some(acc) = FN_ACC.with(|acc| acc.borrow_mut().take()) else { return };
    let get = |k: &str| acc.get(k).copied().unwrap_or(0);
    let total: u64 = acc.values().sum();
    FN_ROWS.lock().unwrap().push(format!(
        "{symbol}\t{class}\t{insts}\t{blocks}\t{}\t{}\t{}\t{}\t{total}\n",
        has_loop as u8,
        get("Register allocation"),
        get("VCode lowering"),
        get("VCode emission"),
    ));
}

/// Bits: 1 = test code (a `tests`/`test`/`*_tests` module in its path), 2 = closure, 4 = generic
/// instance, 8 = defined in another crate, 16 = shim, 32 = #[cold].
pub(crate) fn fn_class<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    instance: rustc_middle::ty::Instance<'tcx>,
    cold: bool,
) -> u8 {
    let def_id = instance.def_id();
    let mut class = 0;
    if def_id.is_local() && in_test_module(tcx, def_id) {
        class |= 1;
    }
    if tcx.is_closure_like(def_id) {
        class |= 2;
    }
    if !instance.args.is_empty() {
        class |= 4;
    }
    if !def_id.is_local() {
        class |= 8;
    }
    if !matches!(instance.def, rustc_middle::ty::InstanceKind::Item(_)) {
        class |= 16;
    }
    if cold {
        class |= 32;
    }
    class
}

pub(crate) fn dump(crate_name: &str) {
    let Some(p) = path() else { return };
    let rows = std::mem::take(&mut *FN_ROWS.lock().unwrap());
    if !rows.is_empty() {
        if let Ok(mut f) =
            std::fs::OpenOptions::new().create(true).append(true).open(format!("{p}.fn"))
        {
            for r in rows {
                let _ = f.write_all(format!("{crate_name}\t{r}").as_bytes());
            }
        }
    }
    let Some(map) = TOTALS.lock().unwrap().take() else { return };
    let mut rows: Vec<_> = map.into_iter().collect();
    rows.sort_by_key(|(_, a)| std::cmp::Reverse(a.self_));
    let mut out = String::new();
    for (name, a) in rows {
        out.push_str(&format!("{crate_name}\t{name}\t{}\t{}\t{}\n", a.self_, a.total, a.count));
    }
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(p) {
        let _ = f.write_all(out.as_bytes());
    }
}

/// Whether `def_id` lies in a test module: one named `tests`, `test` or `*_tests` (the
/// workspace's convention for `#[cfg(test)]` modules), at any depth.
fn in_test_module(tcx: rustc_middle::ty::TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    let mut cur = def_id;
    loop {
        let key = tcx.def_key(cur);
        if let Some(name) = key.get_opt_name() {
            let name = name.as_str();
            if matches!(tcx.def_kind(cur), rustc_hir::def::DefKind::Mod)
                && (name == "tests" || name == "test" || name.ends_with("_tests"))
            {
                return true;
            }
        }
        match key.parent {
            Some(index) => cur = rustc_span::def_id::DefId { krate: cur.krate, index },
            None => return false,
        }
    }
}
