#![feature(pointer_is_aligned_to)]
// `count_ones() == 1` (`is_power_of_two`, the alignment checks of `ptr::copy_nonoverlapping` and
// `slice::from_raw_parts`) without a population count, pointer offsets and indices by a type's
// size as shifts, and the allocator shims as a jump: all values at the edges of their types.
use std::hint::black_box as bb;

static mut FAILS: u32 = 0;
fn check<T: PartialEq + std::fmt::Debug>(what: &str, got: T, want: T) {
    if got != want {
        unsafe { FAILS += 1 }
        println!("FAIL {what}: got {got:?}, want {want:?}");
    }
}

fn naive_pow2(x: u128) -> bool {
    let mut n = 0;
    for i in 0..128 {
        n += (x >> i) & 1;
    }
    n == 1
}

macro_rules! pow2_checks {
    ($($t:ty),*) => {$(
        let mut values: Vec<$t> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, <$t>::MAX, <$t>::MAX - 1, <$t>::MIN];
        for i in 0..<$t>::BITS {
            values.push((1 as $t) << i);
            values.push(((1 as $t) << i).wrapping_add(1));
            values.push(((1 as $t) << i).wrapping_sub(1));
        }
        for v in values {
            let x = bb(v);
            let want = naive_pow2(x as u128 & (u128::MAX >> (128 - <$t>::BITS)));
            check(concat!(stringify!($t), " count_ones == 1"), x.count_ones() == 1, want);
            check(concat!(stringify!($t), " 1 == count_ones"), 1 == x.count_ones(), want);
            check(concat!(stringify!($t), " count_ones != 1"), x.count_ones() != 1, !want);
            check(concat!(stringify!($t), " count_ones as u8 == 1"), x.count_ones() as u8 == 1, want);
            check(concat!(stringify!($t), " count_ones == 2"), x.count_ones() == 2, naive_count(x as u128 & (u128::MAX >> (128 - <$t>::BITS))) == 2);
            if x.count_ones() == 1 {
                check(concat!(stringify!($t), " branch"), want, true);
            } else {
                check(concat!(stringify!($t), " branch"), want, false);
            }
        }
    )*};
}

fn naive_count(x: u128) -> u32 {
    (0..128).map(|i| ((x >> i) & 1) as u32).sum()
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct Three([u8; 3]);
#[derive(Clone, Copy, PartialEq, Debug)]
struct Zst;

fn offsets() {
    let words: Vec<u64> = (0..64).map(|i| i * 3).collect();
    let halves: Vec<u16> = (0..64).map(|i| i * 5).collect();
    let threes: Vec<Three> = (0..64).map(|i| Three([i, i + 1, i + 2])).collect();
    let bigs: Vec<[u64; 5]> = (0..64).map(|i| [i; 5]).collect();
    let zsts = vec![Zst; 64];
    for i in [0usize, 1, 2, 7, 31, 63] {
        let i = bb(i);
        check("u64 index", words[i], i as u64 * 3);
        check("u16 index", halves[i], i as u16 * 5);
        check("[u8; 3] index", threes[i], Three([i as u8, i as u8 + 1, i as u8 + 2]));
        check("[u64; 5] index", bigs[i], [i as u64; 5]);
        check("zst index", zsts[i], Zst);
        unsafe {
            check("u64 add", *words.as_ptr().add(i), i as u64 * 3);
            check("u16 add", *halves.as_ptr().add(i), i as u16 * 5);
            check(
                "[u8; 3] add",
                *threes.as_ptr().add(i),
                Three([i as u8, i as u8 + 1, i as u8 + 2]),
            );
            check("[u64; 5] add", *bigs.as_ptr().add(i), [i as u64; 5]);
            let end = words.as_ptr().add(63);
            check("u64 sub", *end.sub(i), (63 - i) as u64 * 3);
            check("u64 offset -", *end.offset(-(i as isize)), (63 - i) as u64 * 3);
            check(
                "u16 wrapping_offset -",
                *halves.as_ptr().add(63).wrapping_offset(-(i as isize)),
                (63 - i) as u16 * 5,
            );
            check(
                "[u8; 3] offset -",
                *threes.as_ptr().add(63).offset(-(i as isize)),
                Three([(63 - i) as u8, (64 - i) as u8, (65 - i) as u8]),
            );
            check("zst add", zsts.as_ptr().add(i) as usize, zsts.as_ptr() as usize);
            check("u64 offset_from", words.as_ptr().add(i).offset_from(words.as_ptr()), i as isize);
            check(
                "[u8; 3] offset_from",
                threes.as_ptr().add(i).offset_from(threes.as_ptr()),
                i as isize,
            );
        }
        let mut copy = vec![0u64; 64];
        copy[..i].copy_from_slice(&words[..i]);
        check("copy_from_slice", &copy[..i], &words[..i]);
        let mut three_copy = vec![Three([0; 3]); 64];
        three_copy[..i].copy_from_slice(&threes[..i]);
        check("copy_from_slice [u8; 3]", &three_copy[..i], &threes[..i]);
        check("chunks", words.chunks(bb(3)).nth(i / 3).unwrap()[0], (i / 3 * 3) as u64 * 3);
    }
    // Alignment checks of every power of two and some that are not.
    let base = 0x1000usize;
    for shift in 0..12 {
        let align = 1usize << shift;
        let p = bb(base + align) as *const ();
        check("is_aligned_to own", p.is_aligned_to(align), true);
        check("is_aligned_to twice", p.is_aligned_to(align * 2), (base + align) % (align * 2) == 0);
    }
}

fn allocations() {
    // The allocator shims (`__rust_alloc` and friends) are one jump to the default allocator.
    let mut v: Vec<Box<[u64]>> = Vec::new();
    for i in 0..200usize {
        v.push(vec![i as u64; i % 17 + 1].into_boxed_slice());
        if i % 3 == 0 {
            v.swap_remove(i / 4);
        }
    }
    let mut s = String::new();
    for i in 0..1000 {
        s.push(char::from(b'a' + (i % 26) as u8));
        s.shrink_to_fit();
    }
    let z = vec![0u8; bb(4096)];
    check("alloc_zeroed", z.iter().all(|&b| b == 0), true);
    check("alloc sum", v.iter().map(|b| b.len()).sum::<usize>() > 0, true);
    check("realloc", s.len(), 1000);
    check("realloc content", s.as_bytes()[999], b'a' + (999 % 26) as u8);
}

fn main() {
    pow2_checks!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
    offsets();
    allocations();
    let fails = unsafe { FAILS };
    if fails != 0 {
        println!("{fails} checks failed");
        std::process::exit(1);
    }
    println!("ok");
}
