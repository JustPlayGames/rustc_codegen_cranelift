// Without debuginfo, sites in one function that panic alike (same panic function, same unwind
// action) share one panic call. Each site still reports its own message and location, the
// right cleanup runs for each, and sites with different cleanups or argument values stay apart.
use std::cell::Cell;
use std::hint::black_box;
use std::panic::{self, AssertUnwindSafe, catch_unwind};
use std::sync::Mutex;

static SEEN: Mutex<Option<(String, u32)>> = Mutex::new(None);

thread_local! {
    static DROPS: Cell<u32> = const { Cell::new(0) };
}

struct Counted(u32);
impl Drop for Counted {
    fn drop(&mut self) {
        DROPS.with(|d| d.set(d.get() * 10 + self.0));
    }
}

#[inline(never)]
fn checks(case: u32, a: u8, v: &[u32], i: usize) -> u32 {
    let _one = Counted(1);
    let mut acc = 0u32;
    if case == 0 { acc += u32::from(black_box(a) + 200); } let l0 = line!();
    if case == 1 { acc += u32::from(black_box(a) + 201); } let l1 = line!();
    if case == 2 { acc += v[black_box(i)]; } let l2 = line!();
    let _two = Counted(2);
    if case == 3 { acc += u32::from(black_box(a) + 202); } let l3 = line!();
    if case == 4 { acc += v[black_box(i) + 1]; } let l4 = line!();
    if case == 5 { acc += u32::from(black_box(a) * 3); } let l5 = line!();
    if case == 6 { acc += v[black_box(i) * 2]; } let l6 = line!();
    black_box((l0, l1, l2, l3, l4, l5, l6));
    acc
}

#[track_caller]
#[inline(never)]
fn tracked(a: u8, b: u8) -> u8 {
    black_box(a) + black_box(b)
}

#[inline(never)]
fn tracked_callers(case: u32) -> u8 {
    let mut r = 0;
    if case == 0 { r += tracked(200, 100); } let l0 = line!();
    if case == 1 { r += tracked(250, 10); } let l1 = line!();
    black_box((l0, l1));
    r
}

fn expect(what: &str, f: impl FnOnce(), msg: &str, line: u32, drops: u32) {
    DROPS.with(|d| d.set(0));
    *SEEN.lock().unwrap() = None;
    let r = catch_unwind(AssertUnwindSafe(f));
    assert!(r.is_err(), "{what}: no panic", what = what);
    let (m, l) = SEEN.lock().unwrap().take().expect("hook not called");
    assert!(m.contains(msg), "{what}: message {m:?}, expected {msg:?}", what = what, m = m, msg = msg);
    assert_eq!(l, line, "{what}: line");
    assert_eq!(DROPS.with(|d| d.get()), drops, "{what}: drops");
    println!("ok {what}: {m} at line {l}");
}

fn main() {
    panic::set_hook(Box::new(|info| {
        let msg = if let Some(s) = info.payload().downcast_ref::<String>() {
            s.clone()
        } else if let Some(s) = info.payload().downcast_ref::<&str>() {
            s.to_string()
        } else {
            String::new()
        };
        *SEEN.lock().unwrap() = Some((msg, info.location().unwrap().line()));
    }));
    let v = [1u32, 2, 3];
    let base = line!() - 51; // the line of `if case == 0` in `checks`
    expect("add 0", || { checks(0, 100, &v, 0); }, "overflow", base, 1);
    expect("add 1", || { checks(1, 100, &v, 0); }, "overflow", base + 1, 1);
    expect("index 2", || { checks(2, 0, &v, 7); }, "index out of bounds: the len is 3 but the index is 7", base + 2, 1);
    expect("add 3", || { checks(3, 100, &v, 0); }, "overflow", base + 4, 21);
    expect("index 4", || { checks(4, 0, &v, 2); }, "index out of bounds: the len is 3 but the index is 3", base + 5, 21);
    expect("mul 5", || { checks(5, 100, &v, 0); }, "multiply with overflow", base + 6, 21);
    expect("index 6", || { checks(6, 0, &v, 2); }, "index out of bounds: the len is 3 but the index is 4", base + 7, 21);
    assert_eq!(checks(9, 1, &v, 0), 0);
    let tbase = line!() - 39; // the line of `if case == 0` in `tracked_callers`
    expect("tracked 0", || { tracked_callers(0); }, "overflow", tbase, 0);
    expect("tracked 1", || { tracked_callers(1); }, "overflow", tbase + 1, 0);
    println!("all ok");
}
