// CodeView debuginfo for MSVC targets: the `aot.codeview` test compiles this for
// x86_64-pc-windows-msvc and checks the objects as link.exe would (build_system/codeview_check.rs).

#![feature(no_core)]
#![no_core]
#![allow(dead_code)]

extern crate mini_core;

pub struct Point {
    pub x: i32,
    pub y: u64,
}

pub struct Pair<T> {
    pub first: T,
    pub second: T,
}

pub enum Shape {
    Circle(u32),
    Rect { w: u16, h: u16 },
    Empty,
}

pub enum Color {
    Red,
    Green,
    Blue,
}

pub struct Node {
    pub value: usize,
    pub next: *const Node,
}

#[inline(never)]
pub fn describe(p: Point, pair: &Pair<u8>, shape: &Shape, color: Color, node: &Node) -> usize {
    let local = Point { x: p.x, y: p.y };
    let copied = Pair { first: pair.first, second: pair.second };
    let size = match shape {
        Shape::Circle(_) => 1,
        Shape::Rect { .. } => 2,
        Shape::Empty => 3,
    };
    let c = match color {
        Color::Red => 1usize,
        _ => 2,
    };
    let mut add = |k: usize| k + size;
    add(c) + node.value + copied.first as usize + local.y as usize
}
