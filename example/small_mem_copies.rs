// Copies and fills of a small constant size, which the backend writes out as loads and stores
// instead of `memcpy`/`memmove`/`memset` calls (the size is often only known once the
// `#[inline(always)]` `ptr::copy_nonoverlapping`/`ptr::copy`/`ptr::write_bytes` are inlined):
// every size around the vector and scalar chunk boundaries, unaligned and overlapping in both
// directions, against byte-by-byte results.

#![feature(cfg_overflow_checks)]

use std::hint::black_box;
use std::ptr;

fn pattern(buf: &mut [u8], seed: u8) {
    for (i, b) in buf.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(31).wrapping_add(seed);
    }
}

fn copy_bytes(dst: &mut [u8], at: usize, src: &[u8], from: usize, n: usize) {
    let tmp: Vec<u8> = src[from..from + n].to_vec();
    for i in 0..n {
        dst[at + i] = tmp[i];
    }
}

fn check<const N: usize>() {
    // Non-overlapping, at every misalignment of source and destination.
    for (from, at) in [(0, 0), (1, 0), (0, 3), (5, 7)] {
        let mut src = [0u8; 160];
        let mut dst = [0u8; 160];
        pattern(&mut src, 1);
        pattern(&mut dst, 99);
        let mut want = dst;
        copy_bytes(&mut want, at, &src, from, N);
        unsafe {
            ptr::copy_nonoverlapping(
                black_box(src.as_ptr().add(from)) as *const [u8; N],
                black_box(dst.as_mut_ptr().add(at)) as *mut [u8; N],
                1,
            );
        }
        assert_eq!(dst, want, "copy_nonoverlapping {N} bytes from {from} to {at}");
    }

    // Overlapping copies, forward and backward.
    for (from, at) in [(0, 1), (1, 0), (0, 9), (9, 0), (3, 4), (16, 0), (0, 16)] {
        let mut buf = [0u8; 160];
        pattern(&mut buf, 7);
        let mut want = buf;
        let snapshot = buf;
        copy_bytes(&mut want, at, &snapshot, from, N);
        unsafe {
            let base = black_box(buf.as_mut_ptr());
            ptr::copy(base.add(from) as *const [u8; N], base.add(at) as *mut [u8; N], 1);
        }
        assert_eq!(buf, want, "copy {N} bytes from {from} to {at}");
    }

    // Fills with zero and with another byte.
    for (at, byte) in [(0, 0u8), (3, 0xab), (1, 0xff), (8, 0x01)] {
        let mut buf = [0u8; 160];
        pattern(&mut buf, 3);
        let mut want = buf;
        for i in 0..N {
            want[at + i] = byte;
        }
        unsafe {
            ptr::write_bytes(black_box(buf.as_mut_ptr().add(at)) as *mut [u8; N], byte, 1);
        }
        assert_eq!(buf, want, "write_bytes {N} bytes of {byte:#x} at {at}");
    }

    // Swaps go through a temporary.
    let mut a = [0u8; N];
    let mut b = [0u8; N];
    pattern(&mut a, 11);
    pattern(&mut b, 200);
    let (wa, wb) = (b, a);
    unsafe { ptr::swap(black_box(&mut a as *mut [u8; N]), black_box(&mut b as *mut [u8; N])) };
    assert_eq!((a, b), (wa, wb), "swap {N} bytes");

    // Values of the size moved around by value.
    let mut v = [[0u8; N]; 3];
    pattern(&mut v[0], 5);
    v[2] = black_box(v[0]);
    v[1] = black_box(v[2]);
    assert_eq!(v[1], v[0], "move {N} bytes");
}

macro_rules! sizes {
    ($($n:literal)*) => { $(check::<$n>();)* };
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
struct Mixed {
    a: u64,
    b: [u32; 5],
    c: u16,
    d: [u8; 33],
    e: f64,
}

fn check_repeat<T: Copy + PartialEq + std::fmt::Debug, const N: usize>(x: T) {
    let a = [black_box(x); N];
    for (i, e) in black_box(&a).iter().enumerate() {
        assert_eq!(*e, x, "[{x:?}; {N}] at {i}");
    }
}

#[repr(C)]
struct Repeated {
    tag: u8,
    halves: [u16; 13],
    tail: [u8; 3],
}

fn repeats() {
    check_repeat::<u8, 16>(0xa5);
    check_repeat::<u8, 17>(0x5a);
    check_repeat::<u8, 100>(7);
    check_repeat::<u8, 256>(0xfe);
    check_repeat::<u16, 8>(0xbeef);
    check_repeat::<u16, 13>(0x1234);
    check_repeat::<u32, 5>(0xdead_beef);
    check_repeat::<u32, 33>(42);
    check_repeat::<u64, 3>(u64::MAX - 1);
    check_repeat::<u64, 31>(0x0102_0304_0506_0708);
    check_repeat::<i8, 20>(-3);
    check_repeat::<f32, 7>(1.5);
    check_repeat::<f64, 9>(-2.25);
    check_repeat::<bool, 24>(true);
    check_repeat::<char, 6>('\u{1f600}');
    check_repeat::<usize, 4>(usize::MAX / 3);
    let r = Repeated { tag: 9, halves: [black_box(0x7777); 13], tail: [black_box(1); 3] };
    let r = black_box(r);
    assert_eq!((r.tag, r.halves, r.tail), (9, [0x7777; 13], [1; 3]));
}

// Without overflow checks, `<<` takes the shift amount modulo the width, as Cranelift's `ishl`
// does: the size of this copy is `1u32 << (36 % 32)` = 16 bytes.
#[cfg(not(overflow_checks))]
#[inline(always)]
fn wide_shift(x: u32, s: u32) -> usize {
    (x << s) as usize
}

#[cfg(not(overflow_checks))]
fn copy_with_wide_shift() {
    let src = black_box([7u8; 32]);
    let mut dst = [0u8; 32];
    let n = wide_shift(1, 36);
    unsafe { ptr::copy_nonoverlapping(black_box(src.as_ptr()), black_box(dst.as_mut_ptr()), n) };
    assert_eq!(dst.iter().filter(|&&b| b == 7).count(), 16);
}

fn main() {
    repeats();
    #[cfg(not(overflow_checks))]
    copy_with_wide_shift();

    sizes!(1 2 3 4 5 6 7 8 9 12 15 16 17 23 24 31 32 33 40 47 48 63 64 65 72 96 100 112 120 127 128 129 130 144);

    // Element counts other than one: the size is a multiplication of constants.
    let mut words = [0u32; 40];
    let src: Vec<u32> = (0..40).map(|i| i * 0x0101_0101).collect();
    unsafe { ptr::copy_nonoverlapping(black_box(src.as_ptr()), black_box(words.as_mut_ptr()), 13) };
    assert_eq!(&words[..13], &src[..13]);
    assert!(words[13..].iter().all(|&w| w == 0));
    unsafe { ptr::copy(black_box(words.as_ptr()), black_box(words.as_mut_ptr().add(2)), 11) };
    assert_eq!(&words[2..13], &src[..11]);
    unsafe { ptr::write_bytes(black_box(words.as_mut_ptr().add(20)), 0x5a, 7) };
    assert!(words[20..27].iter().all(|&w| w == 0x5a5a_5a5a));
    assert_eq!(words[27], 0);

    // Slice swaps and reversals (`swap_unchecked` copies one element at a time).
    let mut bytes: Vec<u8> = (0..=255).collect();
    bytes.reverse();
    assert!(bytes.iter().enumerate().all(|(i, &b)| b as usize == 255 - i));
    bytes.swap(black_box(3), black_box(200));
    assert_eq!((bytes[3], bytes[200]), (55, 252));

    // A struct with padding and odd sizes, copied by value.
    let m = Mixed { a: 1, b: [2, 3, 4, 5, 6], c: 7, d: [8; 33], e: 9.5 };
    let mut ms = [m; 4];
    ms[3].d[32] = 42;
    ms[1] = black_box(ms[3]);
    assert_eq!(ms[1], ms[3]);
    assert_eq!(ms[1].d[32], 42);

    // SipHash reads the tail of a message with fixed-size copies (`load_int_le!`): the reference
    // vectors of SipHash-2-4 (key 00..0f, messages 00, 00 01, ...), folded together.
    #[allow(deprecated)]
    {
        use std::hash::{Hasher, SipHasher};
        let mut acc = 0u64;
        for len in 0..16u8 {
            let msg: Vec<u8> = (0..len).collect();
            let mut h = SipHasher::new_with_keys(0x0706_0504_0302_0100, 0x0f0e_0d0c_0b0a_0908);
            h.write(black_box(&msg));
            let v = h.finish();
            if len == 1 {
                assert_eq!(v, 0x74f8_39c5_93dc_67fd);
            }
            acc = acc.rotate_left(7) ^ v;
        }
        assert_eq!(acc, 0xb0c2_173f_301d_41eb);
    }

    println!("ok");
}
