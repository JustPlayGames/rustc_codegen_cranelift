// expect: ok:volatile_mmio ok
// Volatile accesses happen exactly as written, at every opt-level: none is removed, merged with
// another, forwarded from a store or split into narrower ones. A page without access rights
// stands in for a device: each access faults, the handler lets that one instruction run and
// single-steps it (x86 trap flag), and logs it: a write with the bytes it changed (against a
// fill pattern), a read with the value the "device" handed it (byte N for the Nth read, so a read
// split into narrower ones shows mixed bytes). Linux on x86_64 only; elsewhere it only checks
// the values.

#![feature(core_intrinsics, portable_simd)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::{
    unaligned_volatile_load, unaligned_volatile_store, volatile_copy_memory,
    volatile_copy_nonoverlapping_memory, volatile_set_memory,
};
use std::ptr::{read_volatile, write_volatile};
use std::simd::u32x4;

#[inline(always)]
fn rd<T>(p: *const u8, off: usize) -> T {
    unsafe { read_volatile(p.add(off) as *const T) }
}

#[inline(always)]
fn wr<T>(p: *mut u8, off: usize, v: T) {
    unsafe { write_volatile(p.add(off) as *mut T, v) }
}

#[inline(never)]
fn store_twice(p: *mut u8) {
    wr(p, 0, 1u32);
    wr(p, 0, 2u32);
}

#[inline(never)]
fn same_value_twice(p: *mut u8) {
    wr(p, 0, 5u32);
    wr(p, 0, 5u32);
}

#[inline(never)]
fn load_twice(p: *mut u8) -> u32 {
    rd::<u32>(p, 0).wrapping_add(rd::<u32>(p, 0))
}

#[inline(never)]
fn store_then_load(p: *mut u8) -> u32 {
    wr(p, 0, 7u32);
    rd::<u32>(p, 0)
}

#[inline(never)]
fn load_then_store_back(p: *mut u8) {
    let v: u32 = rd(p, 0);
    wr(p, 0, v);
}

#[inline(never)]
fn load_unused(p: *mut u8) {
    let _: u64 = rd(p, 8);
}

#[inline(never)]
fn poll(p: *mut u8) -> u32 {
    let mut polls = 0;
    while rd::<u8>(p, 0) != 3 {
        polls += 1;
    }
    polls
}

#[inline(never)]
fn widths(p: *mut u8) -> (u8, u16, u64, u128) {
    wr(p, 0, 0x12u8);
    wr(p, 0, 0x3456u16);
    wr(p, 0, 0x0102_0304_0506_0708u64);
    wr(p, 0, 0x1111_2222_3333_4444_5555_6666_7777_8888u128);
    (rd(p, 0), rd(p, 0), rd(p, 0), rd(p, 0))
}

#[inline(never)]
fn pair_and_vector(p: *mut u8) -> ((u32, u16), u32x4) {
    wr(p, 0, (0x0a0b_0c0du32, 0x0102u16));
    wr(p, 16, u32x4::from_array([1, 2, 3, 4]));
    (rd(p, 0), rd(p, 16))
}

#[inline(never)]
fn array(p: *mut u8) -> [u16; 3] {
    wr(p, 0, [0x0101u16, 0x0202, 0x0303]);
    rd(p, 0)
}

#[inline(never)]
fn unaligned(p: *mut u8) -> u32 {
    unsafe {
        unaligned_volatile_store(p.add(1) as *mut u32, 0x0403_0201);
        unaligned_volatile_store(p.add(1) as *mut u32, 0x0807_0605);
        unaligned_volatile_load(p.add(1) as *const u32)
    }
}

#[inline(never)]
fn set_twice(p: *mut u8) {
    unsafe {
        volatile_set_memory(p.add(32), 0x11, 4);
        volatile_set_memory(p.add(32), 0x22, 4);
    }
}

#[inline(never)]
fn copy_twice(p: *mut u8, src: &[u8; 4]) {
    unsafe {
        volatile_copy_nonoverlapping_memory(p.add(40), src.as_ptr(), 4);
        volatile_copy_memory(p.add(40), src.as_ptr(), 4);
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod device {
    use std::ffi::c_void;
    use std::ptr::{addr_of, addr_of_mut};

    pub const PAGE: usize = 4096;
    const SPAN: usize = 64;
    const FILL: u8 = 0xee;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Access {
        /// A read at this offset, which the device answered with this byte.
        Read(usize, u8),
        /// A write of these bytes at this offset.
        Write(usize, [u8; 16], usize),
    }

    #[repr(C)]
    struct SigAction {
        sa_sigaction: usize,
        sa_mask: [u64; 16],
        sa_flags: i32,
        sa_restorer: usize,
    }

    unsafe extern "C" {
        fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64)
        -> *mut c_void;
        fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
        fn sigaction(sig: i32, act: *const SigAction, old: *mut SigAction) -> i32;
    }

    const PROT_NONE: i32 = 0;
    const PROT_RW: i32 = 3;
    const SIGSEGV: i32 = 11;
    const SIGTRAP: i32 = 5;
    const SA_SIGINFO: i32 = 4;
    // ucontext_t: uc_mcontext.gregs starts at byte 40; REG_EFL = 17, REG_ERR = 19.
    const EFL: usize = 40 + 17 * 8;
    const ERR: usize = 40 + 19 * 8;
    const TF: u64 = 0x100;

    static mut BASE: usize = 0;
    static mut LOG: [Option<Access>; 64] = [None; 64];
    static mut LEN: usize = 0;
    static mut NEXT_READ: u8 = 1;
    // The access being single-stepped: (offset, is a write).
    static mut PENDING: Option<(usize, bool)> = None;

    unsafe fn reg(ctx: *mut c_void, off: usize) -> *mut u64 {
        unsafe { (ctx as *mut u8).add(off) as *mut u64 }
    }

    unsafe fn give_up(sig: i32) {
        let dfl = SigAction { sa_sigaction: 0, sa_mask: [0; 16], sa_flags: 0, sa_restorer: 0 };
        unsafe { sigaction(sig, &dfl, std::ptr::null_mut()) };
    }

    extern "C" fn on_segv(_sig: i32, info: *mut c_void, ctx: *mut c_void) {
        unsafe {
            let addr = *((info as *const u8).add(16) as *const usize);
            let base = BASE;
            if addr < base || addr >= base + PAGE || (*addr_of!(PENDING)).is_some() {
                // Not the device: let it crash.
                return give_up(SIGSEGV);
            }
            mprotect(base as *mut c_void, PAGE, PROT_RW);
            let write = *reg(ctx, ERR) & 2 != 0;
            let fill = if write {
                FILL
            } else {
                let n = NEXT_READ;
                NEXT_READ += 1;
                n
            };
            std::ptr::write_bytes(base as *mut u8, fill, SPAN);
            PENDING = Some((addr - base, write));
            *reg(ctx, EFL) |= TF;
        }
    }

    extern "C" fn on_trap(_sig: i32, _info: *mut c_void, ctx: *mut c_void) {
        unsafe {
            let Some((off, write)) = (*addr_of_mut!(PENDING)).take() else {
                return give_up(SIGTRAP);
            };
            *reg(ctx, EFL) &= !TF;
            let base = BASE as *const u8;
            let access = if write {
                let changed: Vec<usize> = (0..SPAN).filter(|&i| *base.add(i) != FILL).collect();
                let (first, last) = match (changed.first(), changed.last()) {
                    (Some(&f), Some(&l)) => (f, l),
                    _ => (off, off),
                };
                let mut bytes = [0u8; 16];
                let len = (last + 1 - first).min(16);
                for i in 0..len {
                    bytes[i] = *base.add(first + i);
                }
                Access::Write(first, bytes, len)
            } else {
                Access::Read(off, NEXT_READ - 1)
            };
            if LEN < 64 {
                (*addr_of_mut!(LOG))[LEN] = Some(access);
                LEN += 1;
            }
            mprotect(BASE as *mut c_void, PAGE, PROT_NONE);
        }
    }

    pub fn map() -> *mut u8 {
        unsafe {
            // MAP_PRIVATE | MAP_ANONYMOUS
            let p = mmap(std::ptr::null_mut(), PAGE, PROT_NONE, 0x02 | 0x20, -1, 0);
            assert!(p as isize != -1, "mmap failed");
            BASE = p as usize;
            for (sig, f) in [
                (SIGSEGV, on_segv as extern "C" fn(i32, *mut c_void, *mut c_void)),
                (SIGTRAP, on_trap),
            ] {
                let act = SigAction {
                    sa_sigaction: f as usize,
                    sa_mask: [0; 16],
                    sa_flags: SA_SIGINFO,
                    sa_restorer: 0,
                };
                assert_eq!(sigaction(sig, &act, std::ptr::null_mut()), 0);
            }
            p as *mut u8
        }
    }

    /// Runs `f` against the device and returns its result and the accesses it made.
    pub fn run<R>(f: impl FnOnce() -> R) -> (R, Vec<Access>) {
        unsafe {
            LEN = 0;
            NEXT_READ = 1;
            let r = f();
            let log = (&*addr_of!(LOG))[..LEN].iter().map(|a| a.unwrap()).collect();
            (r, log)
        }
    }

    pub fn w(off: usize, bytes: &[u8]) -> Access {
        let mut b = [0u8; 16];
        b[..bytes.len()].copy_from_slice(bytes);
        Access::Write(off, b, bytes.len())
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn main() {
    use device::{Access::Read as R, run, w};

    let p = black_box(device::map());

    let ((), log) = run(|| store_twice(p));
    assert_eq!(log, [w(0, &1u32.to_le_bytes()), w(0, &2u32.to_le_bytes())], "store_twice");

    let ((), log) = run(|| same_value_twice(p));
    assert_eq!(log, [w(0, &5u32.to_le_bytes()), w(0, &5u32.to_le_bytes())], "same_value_twice");

    let (v, log) = run(|| load_twice(p));
    assert_eq!(log, [R(0, 1), R(0, 2)], "load_twice");
    assert_eq!(v, 0x0101_0101 + 0x0202_0202, "load_twice: a read was split or merged");

    let (v, log) = run(|| store_then_load(p));
    assert_eq!(log, [w(0, &7u32.to_le_bytes()), R(0, 1)], "store_then_load");
    assert_eq!(v, 0x0101_0101, "store_then_load: the store was forwarded to the load");

    let ((), log) = run(|| load_then_store_back(p));
    assert_eq!(log, [R(0, 1), w(0, &[1; 4])], "load_then_store_back");

    let ((), log) = run(|| load_unused(p));
    assert_eq!(log, [R(8, 1)], "load_unused");

    let (polls, log) = run(|| poll(p));
    assert_eq!((polls, log), (2, vec![R(0, 1), R(0, 2), R(0, 3)]), "poll");

    let (v, mut log) = run(|| widths(p));
    let wide = 0x1111_2222_3333_4444_5555_6666_7777_8888u128.to_le_bytes();
    // A u128 is two 8-byte accesses, in either order (LLVM stores the high half first).
    assert_eq!(log.len(), 10, "widths: {:?}", log);
    log[3..5].sort_by_key(|a| format!("{:?}", a));
    let (lo, hi) = match log[8..10] {
        [R(0, lo), R(8, hi)] | [R(8, hi), R(0, lo)] => (lo as u128, hi as u128),
        _ => panic!("widths: u128 read {:?}", &log[8..10]),
    };
    assert_eq!(
        log[..8],
        [
            w(0, &[0x12]),
            w(0, &0x3456u16.to_le_bytes()),
            w(0, &0x0102_0304_0506_0708u64.to_le_bytes()),
            w(0, &wide[..8]),
            w(8, &wide[8..]),
            R(0, 1),
            R(0, 2),
            R(0, 3),
        ],
        "widths"
    );
    let bytes = |n: u128| n * 0x0101_0101_0101_0101;
    assert_eq!(v, (1, 0x0202, 0x0303_0303_0303_0303, bytes(hi) << 64 | bytes(lo)));
    assert_eq!(lo + hi, 9, "widths: u128 read {:?}", &log[8..10]);

    // A pair is one access per field and a vector one access in all (LLVM reads this pair as one
    // 8-byte access and, without optimizations, the vector as two).
    let (v, log) = run(|| pair_and_vector(p));
    let mut vec_bytes = Vec::new();
    for x in [1u32, 2, 3, 4] {
        vec_bytes.extend_from_slice(&x.to_le_bytes());
    }
    assert_eq!(
        log,
        [
            w(0, &0x0a0b_0c0du32.to_le_bytes()),
            w(4, &0x0102u16.to_le_bytes()),
            w(16, &vec_bytes),
            R(0, 1),
            R(4, 2),
            R(16, 3),
        ],
        "pair_and_vector"
    );
    assert_eq!(v.0, (0x0101_0101, 0x0202));
    assert_eq!(v.1.to_array(), [0x0303_0303; 4]);

    let (v, log) = run(|| array(p));
    assert_eq!(
        log,
        [w(0, &[1, 1]), w(2, &[2, 2]), w(4, &[3, 3]), R(0, 1), R(2, 2), R(4, 3)],
        "array: one access per element"
    );
    assert_eq!(v, [0x0101, 0x0202, 0x0303]);

    let (v, log) = run(|| unaligned(p));
    assert_eq!(
        log,
        [w(1, &[1, 2, 3, 4]), w(1, &[5, 6, 7, 8]), R(1, 1)],
        "unaligned"
    );
    assert_eq!(v, 0x0101_0101);

    // memset and memcpy may use any access widths: only that both happen, in order.
    let ((), log) = run(|| set_twice(p));
    let writes: Vec<_> = log.iter().filter(|a| matches!(a, device::Access::Write(..))).collect();
    assert!(writes.len() >= 2, "set_twice: {:?}", log);
    assert_eq!(**writes.first().unwrap(), w(32, &[0x11; 4]), "set_twice: {:?}", log);
    assert_eq!(**writes.last().unwrap(), w(32, &[0x22; 4]), "set_twice: {:?}", log);

    let src = [9u8, 8, 7, 6];
    let ((), log) = run(|| copy_twice(p, black_box(&src)));
    let writes = log.iter().filter(|a| matches!(a, device::Access::Write(..))).count();
    assert!(writes >= 2, "copy_twice: {:?}", log);

    println!("volatile_mmio ok");
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
fn main() {
    // No fault-driven device here: check that the values still round-trip.
    let mut mem = [0u8; 64];
    let p = black_box(mem.as_mut_ptr());
    store_twice(p);
    assert_eq!(load_twice(p), 4);
    assert_eq!(store_then_load(p), 7);
    load_then_store_back(p);
    same_value_twice(p);
    load_unused(p);
    let w = widths(p);
    assert_eq!(w.3, 0x1111_2222_3333_4444_5555_6666_7777_8888);
    let (pair, v) = pair_and_vector(p);
    assert_eq!((pair, v.to_array()), ((0x0a0b_0c0d, 0x0102), [1, 2, 3, 4]));
    assert_eq!(array(p), [0x0101, 0x0202, 0x0303]);
    assert_eq!(unaligned(p), 0x0807_0605);
    set_twice(p);
    copy_twice(p, &[9, 8, 7, 6]);
    assert_eq!(mem[32..36], [0x22; 4]);
    assert_eq!(mem[40..44], [9, 8, 7, 6]);
    p.wrapping_add(0);
    mem[0] = 3;
    assert_eq!(poll(mem.as_mut_ptr()), 0);
    println!("volatile_mmio ok");
}
