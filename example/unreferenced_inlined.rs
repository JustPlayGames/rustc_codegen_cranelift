// `#[inline(always)]` functions that inlining leaves unreferenced get a trap instead of their
// body. Every other way of reaching such a function must still find its code: a function
// pointer taken in code, function pointers in statics and constants, vtables, recursion and
// chains of always-inline functions.
use std::hint::black_box;

#[inline(always)]
fn add_one(x: u32) -> u32 {
    x + 1
}

#[inline(always)]
fn add_two(x: u32) -> u32 {
    add_one(add_one(x))
}

#[inline(always)]
fn by_pointer(x: u32) -> u32 {
    x * 3
}

#[inline(always)]
fn in_static(x: u32) -> u32 {
    x * 5
}

#[inline(always)]
fn in_const(x: u32) -> u32 {
    x * 7
}

static TABLE: [fn(u32) -> u32; 1] = [in_static];
const FROM_CONST: fn(u32) -> u32 = in_const;

trait Shape {
    fn area(&self) -> u32;
}

struct Square(u32);

impl Shape for Square {
    #[inline(always)]
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

#[inline(always)]
fn countdown(n: u32) -> u32 {
    if n == 0 { 0 } else { countdown(n - 1) + 2 }
}

#[inline(always)]
fn generic_twice<T: Copy + std::ops::Add<Output = T>>(x: T) -> T {
    x + x
}

#[inline(never)]
fn call_dyn(s: &dyn Shape) -> u32 {
    s.area()
}

fn main() {
    assert_eq!(add_two(black_box(1)), 3);
    let f: fn(u32) -> u32 = by_pointer;
    assert_eq!(black_box(f)(black_box(2)), 6);
    assert_eq!(black_box(TABLE[0])(black_box(2)), 10);
    assert_eq!(black_box(FROM_CONST)(black_box(2)), 14);
    assert_eq!(call_dyn(black_box(&Square(4))), 16);
    assert_eq!(countdown(black_box(5)), 10);
    assert_eq!(generic_twice(black_box(21u64)), 42);
    assert_eq!(generic_twice(black_box(1.5f32)), 3.0);
    let g: fn(u8) -> u8 = generic_twice::<u8>;
    assert_eq!(black_box(g)(black_box(4)), 8);
    println!("ok");
}
