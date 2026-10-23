// Calls that must abort when they unwind (nounwind functions, drops during cleanup) abort with
// the panic's message, at every opt-level, also when inlined (`#[inline(always)]` callees at
// such call sites and callees with such calls at unwinding call sites), and calls that may
// unwind next to them still unwind. Each case runs in a child process (this program again).
use std::hint::black_box;
use std::panic::catch_unwind;
use std::process::Command;

struct Loud(&'static str);
impl Drop for Loud {
    fn drop(&mut self) {
        eprintln!("dropped {}", self.0);
    }
}
struct Bomb;
impl Drop for Bomb {
    fn drop(&mut self) {
        if black_box(true) {
            panic!("boom-drop");
        }
    }
}

#[inline(never)]
fn may_panic(yes: bool, msg: &'static str) {
    if black_box(yes) {
        panic!("{}", msg);
    }
}

// 1: panic directly in a nounwind function.
extern "C" fn abi_direct() {
    may_panic(true, "boom-abi");
}
// 2: a nounwind function whose only unwinding call is that one (no landing pads at all).
extern "C" fn abi_only_call() {
    may_panic(black_box(true), "boom-only");
}
// 3: a nounwind function with cleanup: the drop runs, then it aborts.
extern "C" fn abi_with_cleanup() {
    let _l = Loud("abi_with_cleanup");
    may_panic(true, "boom-cleanup");
}
// 4: a destructor panicking during cleanup.
#[inline(never)]
fn bomb_in_cleanup() {
    let _b = Bomb;
    may_panic(true, "first");
}
// 5: an #[inline(always)] function called at a call site that must abort.
#[inline(always)]
fn always_helper(msg: &'static str) {
    let _l = Loud("always_helper");
    may_panic(true, msg);
}
extern "C" fn abi_calls_always() {
    always_helper("boom-inlined-at-terminate");
}
// 6: an #[inline(always)] function with a call that must abort (its cleanup's drop), called
// where the caller unwinds to its own cleanup.
#[inline(always)]
fn always_with_bomb() {
    let _b = Bomb;
    may_panic(true, "first-inlined");
}
#[inline(never)]
fn calls_always_with_bomb() {
    let _l = Loud("calls_always_with_bomb");
    always_with_bomb();
}
// 7: an #[inline(always)] nounwind function inlined at a plain call site.
#[inline(always)]
extern "C" fn always_abi(yes: bool) {
    may_panic(yes, "boom-always-abi");
}
#[inline(never)]
fn calls_always_abi() {
    let _l = Loud("calls_always_abi");
    always_abi(black_box(true));
}
// 8: a thread's panic inside a nounwind function aborts the process.
extern "C" fn abi_on_thread() {
    may_panic(true, "boom-thread");
}

// Unwinding next to calls that must abort: these must be caught.
#[inline(never)]
fn unwinds_after_cleanup() {
    {
        let _l = Loud("scope");
        may_panic(false, "never");
    }
    may_panic(true, "caught-after-cleanup");
}
#[inline(never)]
fn unwinds_through_nounwind_neighbour() {
    always_abi(black_box(false));
    let _l = Loud("neighbour");
    may_panic(true, "caught-neighbour");
}
// A cleanup that only the unwind path runs (the value is built in the return place), so the
// call returns straight into the epilogue.
#[inline(never)]
fn returns_after_call() -> Loud {
    let l = Loud("returned");
    may_panic(true, "caught-returned");
    l
}
#[inline(always)]
fn always_unwinds() {
    let _b = Loud("always_unwinds");
    may_panic(true, "caught-inlined");
}
#[inline(never)]
fn calls_always_unwinds() {
    let _l = Loud("calls_always_unwinds");
    always_unwinds();
}

fn child(case: &str) {
    let r = catch_unwind(|| match case {
        "abi_direct" => abi_direct(),
        "abi_only_call" => abi_only_call(),
        "abi_with_cleanup" => abi_with_cleanup(),
        "bomb_in_cleanup" => bomb_in_cleanup(),
        "abi_calls_always" => abi_calls_always(),
        "calls_always_with_bomb" => calls_always_with_bomb(),
        "calls_always_abi" => calls_always_abi(),
        "abi_on_thread" => {
            let _ = std::thread::spawn(|| abi_on_thread()).join();
        }
        "unwinds" => {
            let r = catch_unwind(|| drop(returns_after_call()));
            eprintln!("caught={}", r.is_err());
            for f in [unwinds_after_cleanup as fn(), unwinds_through_nounwind_neighbour, calls_always_unwinds] {
                let r = catch_unwind(f);
                eprintln!("caught={}", r.is_err());
            }
            std::process::exit(0);
        }
        _ => unreachable!(),
    });
    eprintln!("CAUGHT {}", r.is_err());
    std::process::exit(7);
}

fn aborted(status: std::process::ExitStatus) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        status.signal() == Some(6)
    }
    #[cfg(windows)]
    {
        // __fastfail (STATUS_STACK_BUFFER_OVERRUN), what Rust's abort is on Windows.
        status.code() == Some(0xC0000409u32 as i32)
    }
}

fn main() {
    if let Some(case) = std::env::args().nth(1) {
        child(&case);
        return;
    }
    // (case, texts stderr must hold)
    let aborting: [(&str, &[&str]); 8] = [
        ("abi_direct", &["boom-abi"]),
        ("abi_only_call", &["boom-only"]),
        ("abi_with_cleanup", &["boom-cleanup"]),
        ("bomb_in_cleanup", &["first", "boom-drop"]),
        ("abi_calls_always", &["boom-inlined-at-terminate"]),
        ("calls_always_with_bomb", &["first-inlined", "boom-drop"]),
        ("calls_always_abi", &["boom-always-abi"]),
        ("abi_on_thread", &["boom-thread"]),
    ];
    let exe = std::env::current_exe().unwrap();
    let mut ok = 0;
    let total = aborting.len() + 4;
    for (case, texts) in aborting {
        let out = Command::new(&exe).arg(case).output().unwrap();
        let err = String::from_utf8_lossy(&out.stderr);
        let good = aborted(out.status) && !err.contains("CAUGHT") && texts.iter().all(|t| err.contains(t));
        if good {
            ok += 1;
        } else {
            println!("FAIL {case}: {:?}\n{err}", out.status);
        }
    }
    let out = Command::new(&exe).arg("unwinds").output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    let caught = err.matches("caught=true").count();
    for d in ["dropped returned", "dropped scope", "dropped neighbour", "dropped always_unwinds", "dropped calls_always_unwinds"] {
        if !err.contains(d) {
            println!("FAIL unwinds: no `{d}`\n{err}");
        }
    }
    if out.status.success() && caught == 4 && err.matches("dropped").count() == 5 {
        ok += 4;
    } else {
        println!("FAIL unwinds: {:?} caught={caught}\n{err}", out.status);
    }
    println!("terminate_calls {ok}/{total}");
    if ok != total {
        std::process::exit(1);
    }
}
