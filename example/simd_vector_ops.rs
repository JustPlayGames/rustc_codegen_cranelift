// Integer add/sub/and/or/xor, comparisons and to_bitmask on 128-bit vectors are single vector
// instructions; other widths go lane by lane. Both are checked against scalar results here.

#![feature(portable_simd)]
use std::hint::black_box;
use std::simd::prelude::*;
macro_rules! check {
    ($t:ty, $n:literal, $seed:expr) => {{
        let mut s: u64 = $seed;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        for _ in 0..2000 {
            let a: [$t; $n] = std::array::from_fn(|_| next() as $t);
            let b: [$t; $n] = std::array::from_fn(|i| if i % 3 == 0 { a[i] } else { next() as $t });
            let (x, y) = (
                black_box(Simd::<$t, $n>::from_array(a)),
                black_box(Simd::<$t, $n>::from_array(b)),
            );
            let add = (x + y).to_array();
            let sub = (x - y).to_array();
            let and = (x & y).to_array();
            let or = (x | y).to_array();
            let xor = (x ^ y).to_array();
            let eq = x.simd_eq(y);
            let ne = x.simd_ne(y);
            let lt = x.simd_lt(y);
            let le = x.simd_le(y);
            let gt = x.simd_gt(y);
            let ge = x.simd_ge(y);
            for i in 0..$n {
                assert_eq!(add[i], a[i].wrapping_add(b[i]));
                assert_eq!(sub[i], a[i].wrapping_sub(b[i]));
                assert_eq!(and[i], a[i] & b[i]);
                assert_eq!(or[i], a[i] | b[i]);
                assert_eq!(xor[i], a[i] ^ b[i]);
                assert_eq!(eq.test(i), a[i] == b[i]);
                assert_eq!(ne.test(i), a[i] != b[i]);
                assert_eq!(lt.test(i), a[i] < b[i]);
                assert_eq!(le.test(i), a[i] <= b[i]);
                assert_eq!(gt.test(i), a[i] > b[i]);
                assert_eq!(ge.test(i), a[i] >= b[i]);
            }
            let bm = lt.to_bitmask();
            let mut want = 0u64;
            for i in 0..$n {
                if a[i] < b[i] {
                    want |= 1 << i;
                }
            }
            assert_eq!(bm, want);
        }
    }};
}
fn main() {
    check!(u8, 16, 1);
    check!(i8, 16, 2);
    check!(u16, 8, 3);
    check!(i16, 8, 4);
    check!(u32, 4, 5);
    check!(i32, 4, 6);
    check!(u64, 2, 7);
    check!(i64, 2, 8);
    check!(u8, 8, 9);
    check!(i32, 8, 10);
    check!(u8, 32, 11);
    check!(i16, 4, 12);
    println!("simd ok");
}
