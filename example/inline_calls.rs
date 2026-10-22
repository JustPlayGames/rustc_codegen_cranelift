// Calls between the functions of a codegen unit are inlined after monomorphization: always for
// #[inline(always)], and small callees when optimizing. This checks that inlined code computes
// the same values (generic closures, by-reference and by-value arguments, multiple returns,
// panics caught across an inlined frame, recursion, #[inline(never)] kept), and that the stack
// slots of different inlined calls share memory: a recursion whose every frame inlines 16 calls
// with a 3.5 KiB local each fits a stack it fits only when those slots are shared.

use std::hint::black_box;

#[inline(always)]
fn fill(seed: u64) -> u64 {
    let mut buf = [0u64; 448];
    for (i, b) in buf.iter_mut().enumerate() {
        *b = seed.wrapping_mul(i as u64 + 1);
    }
    black_box(&mut buf);
    buf.iter().fold(0u64, |a, &b| a.wrapping_add(b))
}

#[inline(never)]
fn recurse(depth: u32) -> u64 {
    if depth == 0 {
        return 0;
    }
    let mut s = 0u64;
    s = s.wrapping_add(fill(depth as u64));
    s = s.wrapping_add(fill(depth as u64 + 1));
    s = s.wrapping_add(fill(depth as u64 + 2));
    s = s.wrapping_add(fill(depth as u64 + 3));
    s = s.wrapping_add(fill(depth as u64 + 4));
    s = s.wrapping_add(fill(depth as u64 + 5));
    s = s.wrapping_add(fill(depth as u64 + 6));
    s = s.wrapping_add(fill(depth as u64 + 7));
    s = s.wrapping_add(fill(depth as u64 + 8));
    s = s.wrapping_add(fill(depth as u64 + 9));
    s = s.wrapping_add(fill(depth as u64 + 10));
    s = s.wrapping_add(fill(depth as u64 + 11));
    s = s.wrapping_add(fill(depth as u64 + 12));
    s = s.wrapping_add(fill(depth as u64 + 13));
    s = s.wrapping_add(fill(depth as u64 + 14));
    s = s.wrapping_add(fill(depth as u64 + 15));
    s.wrapping_add(recurse(black_box(depth - 1)))
}

fn expected_recurse(depth: u32) -> u64 {
    let mut s = 0u64;
    for d in 1..=depth {
        for k in 0..16u64 {
            let seed = d as u64 + k;
            for i in 0..448u64 {
                s = s.wrapping_add(seed.wrapping_mul(i + 1));
            }
        }
    }
    s
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Pair {
    a: u32,
    b: u64,
}

#[inline(always)]
fn swap_pair(p: Pair) -> (u64, u32) {
    (p.b, p.a)
}

#[inline]
fn add_ref(x: &mut u64, y: &u64) {
    *x += *y;
}

#[inline(always)]
fn checked(v: &[u8], i: usize) -> u8 {
    v[i]
}

#[inline(never)]
fn not_inlined(x: u32) -> u32 {
    x.rotate_left(3)
}

#[inline(always)]
fn fact(n: u64) -> u64 {
    if n <= 1 { 1 } else { n * fact(n - 1) }
}

fn sum_by<T: Copy, F: Fn(T) -> u64>(v: &[T], f: F) -> u64 {
    v.iter().map(|&x| f(x)).sum()
}

fn main() {
    let v: Vec<u32> = (0..100).collect();
    assert_eq!(sum_by(&v, |x| x as u64 * 2), 9900);
    assert_eq!(v.iter().filter(|&&x| x % 3 == 0).count(), 34);
    assert!(v.iter().any(|&x| x == 42));

    let (b, a) = swap_pair(black_box(Pair { a: 7, b: 1 << 40 }));
    assert_eq!((a, b), (7, 1 << 40));

    let mut x = 5u64;
    add_ref(&mut x, &black_box(6));
    assert_eq!(x, 11);

    let data = vec![1u8, 2, 3];
    assert_eq!(checked(&data, 2), 3);
    let r = std::panic::catch_unwind(|| checked(black_box(&data), black_box(9)));
    assert!(r.is_err());

    assert_eq!(not_inlined(1), 8);
    assert_eq!(fact(black_box(10)), 3628800);

    let depth = 100;
    let got = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || recurse(black_box(depth)))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(got, expected_recurse(depth));
    println!("ok");
}
