// Locals of small structs, tuples and enums whose layout is one scalar or a pair of scalars are
// kept in Cranelift variables. This checks their fields, enum tags and niches, field writes,
// drops and coercions against the expected values, at every opt level the test is built with.

use std::cmp::Ordering;
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::num::{NonZeroU8, NonZeroU64, NonZeroU128};
use std::ptr::NonNull;
use std::rc::Rc;

#[derive(Copy, Clone, Debug, PartialEq)]
struct Meters(f32);

#[derive(Copy, Clone, Debug, PartialEq)]
struct Padded {
    small: u8,
    big: u64,
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct WithZst {
    _marker: std::marker::PhantomData<u32>,
    value: u32,
    _unit: (),
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Light {
    Red,
    Amber,
    Green,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Niched<'a> {
    Both(u64, &'a u32),
    Num(u64),
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Tagged {
    A(u64),
    B(u64),
    C,
}

#[inline(never)]
fn non_null(p: Option<NonNull<u32>>) -> u32 {
    match p {
        Some(p) => unsafe { *p.as_ptr() },
        None => 0,
    }
}

#[inline(never)]
fn opt_ref(r: Option<&u64>) -> u64 {
    let mut x = r;
    if black_box(false) {
        x = None;
    }
    x.copied().unwrap_or(7)
}

#[inline(never)]
fn result_unit(v: u32, ok: bool) -> Result<u32, ()> {
    let r = if ok { Ok(v) } else { Err(()) };
    black_box(r)
}

#[inline(never)]
fn nonzero(v: u64) -> Option<NonZeroU64> {
    let n = NonZeroU64::new(v);
    let m = n.map(|n| n.saturating_add(1));
    m
}

#[inline(never)]
fn nonzero128(v: u128) -> u128 {
    let n = NonZeroU128::new(v);
    match n {
        Some(n) => n.get() * 2,
        None => 3,
    }
}

#[inline(never)]
fn compare(a: i32, b: i32) -> Ordering {
    let o = a.cmp(&b);
    let r = o.reverse();
    r.reverse()
}

#[inline(never)]
fn next_light(l: Light) -> Light {
    let next = match l {
        Light::Red => Light::Green,
        Light::Green => Light::Amber,
        Light::Amber => Light::Red,
    };
    next
}

#[inline(never)]
fn padded(small: u8, big: u64) -> Padded {
    let mut p = Padded { small, big };
    p.small = p.small.wrapping_add(1);
    p.big += u64::from(p.small);
    black_box(p)
}

#[inline(never)]
fn tuples(a: u8, b: u32) -> (u32, u8) {
    let t = (a, b);
    let mut u = (t.1, t.0);
    u.0 += 1;
    u
}

#[inline(never)]
fn meters(m: Meters, x: f32) -> (Meters, u8) {
    let mut pair = (m, 1u8);
    pair.0.0 += x;
    pair.1 = (pair.0.0 > 10.0) as u8;
    pair
}

#[inline(never)]
fn with_zst(v: u32) -> u32 {
    let mut w = WithZst { _marker: std::marker::PhantomData, value: v, _unit: () };
    w.value *= 3;
    w.value
}

#[inline(never)]
fn niched<'a>(a: u64, r: &'a u32, both: bool) -> Niched<'a> {
    let n = if both { Niched::Both(a, r) } else { Niched::Num(a + 1) };
    black_box(n)
}

#[inline(never)]
fn read_niched(n: Niched<'_>) -> u64 {
    let m = n;
    match m {
        Niched::Both(a, r) => a + u64::from(*r),
        Niched::Num(a) => a * 10,
    }
}

#[inline(never)]
fn tagged(i: u64) -> Tagged {
    let t = match i % 3 {
        0 => Tagged::A(i),
        1 => Tagged::B(i * 2),
        _ => Tagged::C,
    };
    t
}

#[inline(never)]
fn read_tagged(t: Tagged) -> u64 {
    match t {
        Tagged::A(x) => x + 1,
        Tagged::B(x) => x + 2,
        Tagged::C => 99,
    }
}

#[inline(never)]
fn opt_pair<'a>(v: u32, r: &'a u8, some: bool) -> Option<(u32, &'a u8)> {
    let o = if some { Some((v, r)) } else { None };
    let mapped = o.map(|(v, r)| (v + u32::from(*r), r));
    mapped
}

#[inline(never)]
fn nested(v: u8) -> Option<Option<bool>> {
    let x = match v {
        0 => None,
        1 => Some(None),
        _ => Some(Some(v % 2 == 0)),
    };
    x
}

#[inline(never)]
fn chars(c: u32) -> Option<char> {
    let o = char::from_u32(c);
    o.map(|c| c.to_ascii_uppercase())
}

#[inline(never)]
fn results(a: u64, ok: bool) -> Result<u64, u64> {
    let r = if ok { Ok(a) } else { Err(a + 5) };
    let r2 = r.map(|x| x * 2).map_err(|e| e * 3);
    r2
}

#[inline(never)]
fn maybe_uninit(v: u64) -> u64 {
    let mut m = MaybeUninit::<u64>::uninit();
    m.write(v);
    let x = unsafe { m.assume_init() };
    x + 1
}

#[inline(never)]
fn boxes(v: u32) -> u32 {
    let b = Box::new(v);
    let o: Option<Box<u32>> = Some(b);
    let d: Box<dyn Fn() -> u32> = {
        let o = o;
        let x = *o.unwrap();
        Box::new(move || x + 1)
    };
    let s = std::mem::size_of_val(&*d) as u32;
    d() + s * 0
}

#[inline(never)]
fn rcs(v: u32) -> usize {
    let a = Rc::new(v);
    let b = a.clone();
    let c: Option<Rc<u32>> = Some(b);
    let n = Rc::strong_count(&a);
    drop(c);
    n + Rc::strong_count(&a)
}

#[inline(never)]
fn closure(v: &u32) -> u32 {
    let f = |x: u32| x + *v;
    let g = move |x: u32| f(x) * 2;
    g(3)
}

#[inline(never)]
fn nonzero_u8(v: u8) -> u8 {
    let n = NonZeroU8::new(v);
    let w = n.and_then(|n| n.checked_add(1));
    w.map_or(0, |n| n.get())
}

#[inline(never)]
fn slices(s: &[u16]) -> u16 {
    let mut it = s.iter();
    let mut sum = 0u16;
    while let Some(&x) = it.next() {
        sum = sum.wrapping_add(x);
    }
    let first = s.first();
    sum + first.copied().unwrap_or(0)
}

#[inline(never)]
fn wide(a: u128, b: u128) -> (u128, u128) {
    let mut p = (a, b);
    p.1 = p.0.wrapping_mul(3);
    p
}

#[inline(never)]
fn arrays(x: u16, s: &[u32]) -> (u32, u32) {
    let small = [x; 5];
    let big = [x; 40];
    let bytes = [x as u8; 16];
    let listed = [x, x + 1, x + 2];
    let [first, .., last] = listed;
    let ends = match s {
        [a, .., b] => a + b,
        _ => 0,
    };
    let sum = small.iter().map(|&v| u32::from(v)).sum::<u32>()
        + big.iter().map(|&v| u32::from(v)).sum::<u32>()
        + bytes.iter().map(|&v| u32::from(v)).sum::<u32>();
    (sum + u32::from(first) + u32::from(last), ends)
}

fn main() {
    let x = 42u32;
    assert_eq!(non_null(black_box(Some(NonNull::from(&x)))), 42);
    assert_eq!(non_null(black_box(None)), 0);
    assert_eq!(opt_ref(black_box(Some(&9))), 9);
    assert_eq!(opt_ref(black_box(None)), 7);
    assert_eq!(result_unit(black_box(5), black_box(true)), Ok(5));
    assert_eq!(result_unit(black_box(5), black_box(false)), Err(()));
    assert_eq!(nonzero(black_box(0)), None);
    assert_eq!(nonzero(black_box(4)), NonZeroU64::new(5));
    assert_eq!(nonzero(black_box(u64::MAX)), NonZeroU64::new(u64::MAX));
    assert_eq!(nonzero128(black_box(0)), 3);
    assert_eq!(nonzero128(black_box(1 << 100)), 1 << 101);
    assert_eq!(compare(black_box(1), black_box(2)), Ordering::Less);
    assert_eq!(compare(black_box(2), black_box(2)), Ordering::Equal);
    assert_eq!(compare(black_box(3), black_box(2)), Ordering::Greater);
    assert_eq!(next_light(black_box(Light::Red)), Light::Green);
    assert_eq!(next_light(black_box(Light::Green)), Light::Amber);
    assert_eq!(next_light(black_box(Light::Amber)), Light::Red);
    assert_eq!(padded(black_box(255), black_box(10)), Padded { small: 0, big: 10 });
    assert_eq!(padded(black_box(1), black_box(10)), Padded { small: 2, big: 12 });
    assert_eq!(tuples(black_box(3), black_box(70_000)), (70_001, 3));
    assert_eq!(meters(black_box(Meters(9.5)), black_box(1.0)), (Meters(10.5), 1));
    assert_eq!(meters(black_box(Meters(1.0)), black_box(1.0)), (Meters(2.0), 0));
    assert_eq!(with_zst(black_box(4)), 12);
    let r = 6u32;
    assert_eq!(read_niched(niched(black_box(4), &r, black_box(true))), 10);
    assert_eq!(read_niched(niched(black_box(4), &r, black_box(false))), 50);
    assert_eq!(niched(black_box(4), &r, black_box(false)), Niched::Num(5));
    for i in 0..9 {
        let expected = match i % 3 {
            0 => i + 1,
            1 => i * 2 + 2,
            _ => 99,
        };
        assert_eq!(read_tagged(tagged(black_box(i))), expected);
    }
    let byte = 4u8;
    assert_eq!(opt_pair(black_box(3), &byte, black_box(true)), Some((7, &4)));
    assert_eq!(opt_pair(black_box(3), &byte, black_box(false)), None);
    assert_eq!(nested(black_box(0)), None);
    assert_eq!(nested(black_box(1)), Some(None));
    assert_eq!(nested(black_box(2)), Some(Some(true)));
    assert_eq!(nested(black_box(3)), Some(Some(false)));
    assert_eq!(chars(black_box('q' as u32)), Some('Q'));
    assert_eq!(chars(black_box(0xD800)), None);
    assert_eq!(results(black_box(4), black_box(true)), Ok(8));
    assert_eq!(results(black_box(4), black_box(false)), Err(27));
    assert_eq!(maybe_uninit(black_box(41)), 42);
    assert_eq!(boxes(black_box(9)), 10);
    assert_eq!(rcs(black_box(1)), 3);
    assert_eq!(closure(black_box(&5)), 16);
    assert_eq!(nonzero_u8(black_box(0)), 0);
    assert_eq!(nonzero_u8(black_box(254)), 255);
    assert_eq!(nonzero_u8(black_box(255)), 0);
    assert_eq!(slices(black_box(&[1, 2, 3])), 7);
    assert_eq!(slices(black_box(&[])), 0);
    assert_eq!(wide(black_box(5), black_box(1)), (5, 15));
    assert_eq!(arrays(black_box(3), black_box(&[5, 6, 7])), (15 + 120 + 48 + 3 + 5, 12));
    assert_eq!(arrays(black_box(1), black_box(&[5])), (5 + 40 + 16 + 1 + 3, 0));
    println!("ssa_adts ok");
}
