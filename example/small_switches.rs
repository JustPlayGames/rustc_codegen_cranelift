// Matches with one to three targets, which are lowered to compares and branches instead of a jump
// table: niche and tagged enums (the `otherwise` target is unreachable), integer matches with a
// wildcard, signed, 128-bit and narrow discriminants, values at the edges of their types.
use std::cmp::Ordering;
use std::hint::black_box as bb;
use std::num::NonZeroU64;
use std::ptr::NonNull;

static mut FAILS: u32 = 0;
fn check<T: PartialEq + std::fmt::Debug>(what: &str, got: T, want: T) {
    if got != want {
        unsafe { FAILS += 1 }
        println!("FAIL {what}: got {got:?}, want {want:?}");
    }
}

#[derive(Clone, Copy, Debug)]
enum Three {
    A,
    B(u32),
    C(u64),
}

#[derive(Clone, Copy, Debug)]
#[repr(i8)]
enum Signed {
    Minus = -128,
    Zero = 0,
    Plus = 127,
}

#[derive(Clone, Copy, Debug)]
#[repr(u64)]
enum Far {
    Low = 1,
    High = 0xffff_ffff_ffff_fff0,
}

#[derive(Clone, Copy, Debug)]
#[repr(i128)]
enum Wide {
    Neg = -5,
    Big = 0x1234_5678_9abc_def0_0fed_cba9_8765_4321,
    Max = i128::MAX,
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
enum Edge {
    Top = 255,
    Bottom = 0,
}

#[inline(never)]
fn opt_ptr(x: Option<NonNull<u8>>) -> u32 {
    match x {
        Some(_) => 1,
        None => 2,
    }
}
#[inline(never)]
fn opt_ref(x: Option<&u64>) -> u64 {
    match x {
        None => 7,
        Some(v) => *v,
    }
}
#[inline(never)]
fn opt_bool(x: Option<bool>) -> u32 {
    match x {
        Some(true) => 1,
        Some(false) => 2,
        None => 3,
    }
}
#[inline(never)]
fn opt_ord(x: Option<Ordering>) -> i32 {
    match x {
        Some(Ordering::Less) => -1,
        Some(Ordering::Equal) => 0,
        Some(Ordering::Greater) => 1,
        None => 9,
    }
}
#[inline(never)]
fn ord(x: Ordering) -> u32 {
    match x {
        Ordering::Less => 10,
        Ordering::Equal => 20,
        Ordering::Greater => 30,
    }
}
#[inline(never)]
fn res(x: Result<u32, ()>) -> u32 {
    match x {
        Ok(v) => v,
        Err(()) => 99,
    }
}
#[inline(never)]
fn nz(x: Option<NonZeroU64>) -> u64 {
    match x {
        Some(v) => v.get(),
        None => 0,
    }
}
#[inline(never)]
fn three(x: Three) -> u64 {
    match x {
        Three::A => 1,
        Three::B(v) => v as u64 + 100,
        Three::C(v) => v + 1000,
    }
}
#[inline(never)]
fn signed(x: Signed) -> i32 {
    match x {
        Signed::Minus => -1,
        Signed::Zero => 0,
        Signed::Plus => 1,
    }
}
#[inline(never)]
fn far(x: Far) -> u32 {
    match x {
        Far::Low => 1,
        Far::High => 2,
    }
}
#[inline(never)]
fn wide(x: Wide) -> u32 {
    match x {
        Wide::Neg => 1,
        Wide::Big => 2,
        Wide::Max => 3,
    }
}
#[inline(never)]
fn edge(x: Edge) -> u32 {
    match x {
        Edge::Top => 1,
        Edge::Bottom => 2,
    }
}
#[inline(never)]
fn int2(x: u32) -> u32 {
    match x {
        3 => 30,
        4 => 40,
        _ => 0,
    }
}
#[inline(never)]
fn int3(x: i64) -> u32 {
    match x {
        -1 => 1,
        0 => 2,
        i64::MAX => 3,
        _ => 4,
    }
}
#[inline(never)]
fn int3_zero_last(x: u8) -> u32 {
    match x {
        255 => 1,
        1 => 2,
        0 => 3,
        _ => 4,
    }
}
#[inline(never)]
fn u128_3(x: u128) -> u32 {
    match x {
        0 => 1,
        u128::MAX => 2,
        0x1_0000_0000_0000_0000 => 3,
        _ => 4,
    }
}
#[inline(never)]
fn i128_2(x: i128) -> u32 {
    match x {
        -1 => 1,
        i128::MIN => 2,
        _ => 3,
    }
}
#[inline(never)]
fn chars(x: char) -> u32 {
    match x {
        'a' => 1,
        '\u{10FFFF}' => 2,
        _ => 3,
    }
}
#[inline(never)]
fn four(x: u16) -> u32 {
    // Four consecutive values: still a jump table.
    match x {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 4,
        _ => 5,
    }
}

fn main() {
    let mut b = 5u8;
    check("opt_ptr some", opt_ptr(bb(NonNull::new(&mut b))), 1);
    check("opt_ptr none", opt_ptr(bb(None)), 2);
    check("opt_ref some", opt_ref(bb(Some(&42))), 42);
    check("opt_ref none", opt_ref(bb(None)), 7);
    check("opt_bool t", opt_bool(bb(Some(true))), 1);
    check("opt_bool f", opt_bool(bb(Some(false))), 2);
    check("opt_bool n", opt_bool(bb(None)), 3);
    for (x, w) in [
        (Some(Ordering::Less), -1),
        (Some(Ordering::Equal), 0),
        (Some(Ordering::Greater), 1),
        (None, 9),
    ] {
        check("opt_ord", opt_ord(bb(x)), w);
    }
    for (x, w) in [(Ordering::Less, 10), (Ordering::Equal, 20), (Ordering::Greater, 30)] {
        check("ord", ord(bb(x)), w);
    }
    check("res ok", res(bb(Ok(5))), 5);
    check("res err", res(bb(Err(()))), 99);
    check("nz some", nz(bb(NonZeroU64::new(u64::MAX))), u64::MAX);
    check("nz none", nz(bb(None)), 0);
    check("three a", three(bb(Three::A)), 1);
    check("three b", three(bb(Three::B(u32::MAX))), u32::MAX as u64 + 100);
    check("three c", three(bb(Three::C(5))), 1005);
    check("signed -", signed(bb(Signed::Minus)), -1);
    check("signed 0", signed(bb(Signed::Zero)), 0);
    check("signed +", signed(bb(Signed::Plus)), 1);
    check("far low", far(bb(Far::Low)), 1);
    check("far high", far(bb(Far::High)), 2);
    check("wide neg", wide(bb(Wide::Neg)), 1);
    check("wide big", wide(bb(Wide::Big)), 2);
    check("wide max", wide(bb(Wide::Max)), 3);
    check("edge top", edge(bb(Edge::Top)), 1);
    check("edge bottom", edge(bb(Edge::Bottom)), 2);
    for (x, w) in [(3, 30), (4, 40), (0, 0), (5, 0), (u32::MAX, 0), (3 + (1 << 31), 0)] {
        check("int2", int2(bb(x)), w);
    }
    for (x, w) in [(-1, 1), (0, 2), (i64::MAX, 3), (1, 4), (i64::MIN, 4), (u32::MAX as i64, 4)] {
        check("int3", int3(bb(x)), w);
    }
    for x in 0..=255u8 {
        let w = match x {
            255 => 1,
            1 => 2,
            0 => 3,
            _ => 4,
        };
        check("int3_zero_last", int3_zero_last(bb(x)), w);
    }
    for (x, w) in [
        (0, 1),
        (u128::MAX, 2),
        (1 << 64, 3),
        (1, 4),
        (u64::MAX as u128, 4),
        ((1 << 64) + 1, 4),
        (u128::MAX - 1, 4),
    ] {
        check("u128_3", u128_3(bb(x)), w);
    }
    for (x, w) in [(-1, 1), (i128::MIN, 2), (0, 3), (u64::MAX as i128, 3), (-1 << 64, 3)] {
        check("i128_2", i128_2(bb(x)), w);
    }
    for (x, w) in [('a', 1), ('\u{10FFFF}', 2), ('b', 3), ('\0', 3)] {
        check("chars", chars(bb(x)), w);
    }
    for x in 0..8u16 {
        check("four", four(bb(x)), if x < 4 { x as u32 + 1 } else { 5 });
    }
    check("four max", four(bb(u16::MAX)), 5);
    let fails = unsafe { FAILS };
    if fails != 0 {
        println!("{fails} failures");
        std::process::exit(1);
    }
    println!("small switches ok");
}
