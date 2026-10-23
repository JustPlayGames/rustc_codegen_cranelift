// Functions that only pass their parameters on to another function and return its results are a
// `jmp` to it without debuginfo (`jump_thunk`): arguments in registers and on the stack, a struct
// returned through a pointer (sret), a struct passed by pointer, calls through fn pointers and
// vtables, a panic unwinding through a forwarder, and a nounwind forwarder, which must keep its
// frame and abort. With the argument `thunks`, the forwarders must start with a `jmp` (x86_64)
// and have unwind info for a profiler's samples at it (Linux), as must the allocator shim, a
// `jmp` to the default allocator (`create_wrapper_function`).
// Each aborting case runs in a child process (this program again).
#![feature(rustc_attrs)]

use std::hint::black_box;
use std::panic::catch_unwind;
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

static DROPS: AtomicU32 = AtomicU32::new(0);
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

#[inline(never)]
fn add(a: u64, b: u64) -> u64 {
    a.wrapping_mul(3).wrapping_add(b)
}
#[inline(never)]
fn fwd_add(a: u64, b: u64) -> u64 {
    add(a, b)
}

// More arguments than registers (6 integer and 8 float registers on SysV, 4 in all on Win64).
#[inline(never)]
#[rustfmt::skip]
fn many(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64, a8: u64,
        a9: u64, f0: f64, f1: f64, f2: f64, f3: f64, f4: f64, f5: f64, f6: f64, f7: f64,
        f8: f64, f9: f64, a10: u8, a11: u16) -> f64 {
    let ints = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 as u64, a11 as u64];
    let floats = [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9];
    let i: u64 = ints.iter().enumerate().map(|(i, x)| (i as u64 + 1) * x).sum();
    let f: f64 = floats.iter().enumerate().map(|(i, x)| (i as f64 + 1.0) * x).sum();
    i as f64 + f
}
#[inline(never)]
#[rustfmt::skip]
fn fwd_many(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64, a8: u64,
            a9: u64, f0: f64, f1: f64, f2: f64, f3: f64, f4: f64, f5: f64, f6: f64, f7: f64,
            f8: f64, f9: f64, a10: u8, a11: u16) -> f64 {
    many(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, a10, a11)
}

// Returned through a pointer to the caller's place (sret), also with stack arguments.
#[derive(Clone, Copy, PartialEq, Debug)]
struct Big([u64; 8]);
#[inline(never)]
fn make_big(seed: u64, k: u64) -> Big {
    Big(std::array::from_fn(|i| seed.wrapping_mul(i as u64 + 1).wrapping_add(k)))
}
#[inline(never)]
fn fwd_big(seed: u64, k: u64) -> Big {
    make_big(seed, k)
}
#[inline(never)]
#[rustfmt::skip]
fn make_big_many(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64,
                 a8: u64) -> Big {
    let mut v = [a0, a1, a2, a3, a4, a5, a6, a7];
    v[7] ^= a8;
    Big(v.map(|x| x + 1))
}
#[inline(never)]
#[rustfmt::skip]
fn fwd_big_many(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64,
                a8: u64) -> Big {
    make_big_many(a0, a1, a2, a3, a4, a5, a6, a7, a8)
}

// Passed by pointer to a copy the callee may change.
#[inline(never)]
fn take_big(mut b: Big, k: u64) -> u64 {
    b.0[0] = k;
    b.0.iter().sum()
}
#[inline(never)]
fn fwd_take_big(b: Big, k: u64) -> u64 {
    take_big(b, k)
}

// A trait method forwarding to an inherent one, called through a vtable.
trait Shape {
    fn area(&self, scale: u64) -> u64;
}
struct Sq(u64);
impl Sq {
    #[inline(never)]
    fn area_inherent(&self, scale: u64) -> u64 {
        self.0 * self.0 * scale
    }
}
impl Shape for Sq {
    #[inline(never)]
    fn area(&self, scale: u64) -> u64 {
        self.area_inherent(scale)
    }
}

// Unwinding through forwarders, to a cleanup in their caller.
#[inline(never)]
fn panics_if(yes: u64) -> u64 {
    if black_box(yes) != 0 {
        panic!("boom-{yes}");
    }
    yes + 1
}
#[inline(never)]
fn fwd_panics(yes: u64) -> u64 {
    panics_if(yes)
}
extern "C-unwind" fn fwd_panics_c_unwind(yes: u64) -> u64 {
    panics_if(yes)
}
#[inline(never)]
fn guarded(f: fn(u64) -> u64, yes: u64) -> u64 {
    let _g = Guard;
    f(yes) + 1
}
#[inline(never)]
fn guarded_c_unwind(yes: u64) -> u64 {
    let _g = Guard;
    fwd_panics_c_unwind(yes) + 1
}

// A nounwind function: its call must abort when it unwinds, so it is no jump.
extern "C" fn fwd_nounwind(yes: u64) -> u64 {
    panics_if(yes)
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

unsafe extern "Rust" {
    #[rustc_std_internal_symbol]
    fn __rust_alloc(size: usize, align: usize) -> *mut u8;
}

fn starts_with_jmp(f: *const ()) -> bool {
    unsafe { *(f as *const u8) == 0xe9 }
}

// A profiler's sample at the jump unwinds through the forwarder's FDE.
#[cfg(target_os = "linux")]
fn has_fde(f: *const ()) -> bool {
    unsafe extern "C" {
        fn _Unwind_Find_FDE(pc: *const u8, bases: *mut [usize; 3]) -> *const u8;
    }
    let mut bases = [0; 3];
    unsafe { !_Unwind_Find_FDE((f as *const u8).add(1), &mut bases).is_null() }
}
#[cfg(not(target_os = "linux"))]
fn has_fde(_: *const ()) -> bool {
    true
}

fn main() {
    let mut args = std::env::args().skip(1);
    let arg = args.next();
    if arg.as_deref() == Some("nounwind") {
        let r = catch_unwind(|| fwd_nounwind(black_box(7)));
        eprintln!("CAUGHT {}", r.is_err());
        std::process::exit(7);
    }

    assert_eq!(fwd_add(black_box(5), 6), 21);
    let f: fn(u64, u64) -> u64 = black_box(fwd_add);
    assert_eq!(f(7, 1), 22);

    #[rustfmt::skip]
    let m = fwd_many(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5, 8.5,
                     9.5, 11, 12);
    #[rustfmt::skip]
    let want = many(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5, 8.5,
                    9.5, 11, 12);
    assert_eq!(m, want);
    assert_eq!(m, 650.0 + 357.5);

    assert_eq!(fwd_big(black_box(3), 4), make_big(3, 4));
    assert_eq!(fwd_big(3, 4).0[7], 28);
    let bm = fwd_big_many(1, 2, 3, 4, 5, 6, 7, 8, black_box(9));
    assert_eq!(bm, Big([2, 3, 4, 5, 6, 7, 8, 2]));

    let b = Big([1; 8]);
    assert_eq!(fwd_take_big(b, black_box(10)), 17);
    assert_eq!(b, Big([1; 8]));

    let shapes: Vec<Box<dyn Shape>> = vec![Box::new(Sq(3)), Box::new(Sq(4))];
    assert_eq!(shapes.iter().map(|s| s.area(black_box(2))).sum::<u64>(), 50);

    std::panic::set_hook(Box::new(|_| {}));
    assert!(catch_unwind(|| guarded(black_box(fwd_panics), 1)).is_err());
    assert!(catch_unwind(|| guarded_c_unwind(black_box(2))).is_err());
    assert_eq!(guarded(fwd_panics, 0) + guarded_c_unwind(0), 4);
    assert_eq!(DROPS.load(Ordering::Relaxed), 4);
    let _ = std::panic::take_hook();

    let exe = std::env::current_exe().unwrap();
    let out = Command::new(&exe).arg("nounwind").output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        aborted(out.status) && err.contains("boom-7") && !err.contains("CAUGHT"),
        "nounwind forwarder: {:?}\n{err}",
        out.status
    );

    if arg.as_deref() == Some("thunks") && cfg!(target_arch = "x86_64") {
        let forwarders: [(&str, *const (), bool); 9] = [
            ("__rust_alloc", __rust_alloc as *const (), true),
            ("fwd_add", fwd_add as *const (), true),
            ("fwd_many", fwd_many as *const (), true),
            ("fwd_big", fwd_big as *const (), true),
            ("fwd_big_many", fwd_big_many as *const (), true),
            ("area", <Sq as Shape>::area as *const (), true),
            ("fwd_panics", fwd_panics as *const (), true),
            ("fwd_panics_c_unwind", fwd_panics_c_unwind as *const (), true),
            ("fwd_nounwind", fwd_nounwind as *const (), false),
        ];
        let mut bad = 0;
        for (name, f, jmp) in forwarders {
            if starts_with_jmp(f) != jmp {
                println!("FAIL {name}: jmp expected {jmp}");
                bad += 1;
            }
            if !has_fde(f) {
                println!("FAIL {name}: no FDE");
                bad += 1;
            }
        }
        // Reported, not required: whether this one is a jump depends on how its argument is
        // copied.
        println!("fwd_take_big jmp={}", starts_with_jmp(fwd_take_big as *const ()));
        assert_eq!(bad, 0);
    }
    println!("ok");
}
