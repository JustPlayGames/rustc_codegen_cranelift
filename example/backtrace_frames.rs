// Backtraces through every frame of a call chain: functions without a frame pointer (where the
// target lets it be omitted) must still unwind through their CFI, from a plain call chain with
// inlined calls in it and from a panic inside a closure, with each frame's name and, with
// debuginfo, its file and line.

use std::backtrace::Backtrace;
use std::hint::black_box;
use std::panic;
use std::sync::Mutex;

static PANIC_TRACE: Mutex<String> = Mutex::new(String::new());

#[inline(never)]
fn level_one(n: u64) -> String {
    // A frame with stack slots and callee-saved registers around the call.
    let local = [n; 7];
    let s = level_two(black_box(n + 1));
    assert_eq!(black_box(local)[6], n);
    s
}

#[inline(never)]
fn level_two(n: u64) -> String {
    level_three(n * 2)
}

#[inline(always)]
fn level_three(n: u64) -> String {
    level_four(n + 3)
}

#[inline(never)]
fn level_four(n: u64) -> String {
    // A leaf-like frame that only calls into the capture.
    black_box(n);
    Backtrace::force_capture().to_string()
}

#[inline(never)]
fn panics_in_closure(v: &[u32]) -> u32 {
    let f = |x: &u32| -> u32 {
        if *x == 3 {
            panic!("three");
        }
        x + 1
    };
    v.iter().map(f).sum()
}

#[inline(never)]
fn calls_closure() -> u32 {
    panics_in_closure(black_box(&[1, 2, 3, 4]))
}

fn assert_in_order(trace: &str, names: &[&str], what: &str) {
    let mut at = 0;
    for name in names {
        match trace[at..].find(name) {
            Some(i) => at += i + name.len(),
            None => panic!("{what}: `{name}` missing or out of order in:\n{trace}"),
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let lines = args.iter().any(|a| a == "lines");
    let unwind = args.iter().any(|a| a == "unwind");

    let trace = level_one(black_box(5));
    assert_in_order(
        &trace,
        &["level_four", "level_two", "level_one", "backtrace_frames", "main"],
        "call chain",
    );
    if lines {
        assert!(trace.contains("backtrace_frames.rs:"), "no file:line in:\n{trace}");
    }

    if !unwind {
        println!("backtrace_frames ok");
        return;
    }
    panic::set_hook(Box::new(|_| {
        *PANIC_TRACE.lock().unwrap() = Backtrace::force_capture().to_string();
    }));
    let r = panic::catch_unwind(|| calls_closure());
    let _ = panic::take_hook();
    assert!(r.is_err());
    let trace = PANIC_TRACE.lock().unwrap().clone();
    assert_in_order(
        &trace,
        &["panics_in_closure::{closure", "panics_in_closure", "calls_closure", "main"],
        "panic in a closure",
    );
    if lines {
        assert!(trace.contains("backtrace_frames.rs:"), "no file:line in:\n{trace}");
    }

    // The frames are left in a usable state after the unwind.
    assert_eq!(black_box(level_one(black_box(9))).is_empty(), false);
    println!("backtrace_frames ok");
}
