// A volatile read is never removed, not even when its value is unused (as after inlining
// `read_volatile` into a caller that drops the result): reading an unmapped address must still
// fault. Each case runs in a child process of this test.

#![feature(portable_simd)]

use std::hint::black_box;
use std::process::Command;
use std::ptr::{read_volatile, write_volatile};
use std::simd::u32x4;

const BAD: usize = 0x10;

fn fault(case: &str) {
    let addr = black_box(BAD);
    unsafe {
        match case {
            "u8" => {
                read_volatile(addr as *const u8);
            }
            "u128" => {
                read_volatile(addr as *const u128);
            }
            "pair" => {
                read_volatile(addr as *const (u32, u64));
            }
            "array" => {
                read_volatile(addr as *const [u8; 40]);
            }
            "simd" => {
                read_volatile(addr as *const u32x4);
            }
            "unit_then_u16" => {
                read_volatile(addr as *const ());
                read_volatile(addr as *const u16);
            }
            _ => unreachable!(),
        }
    }
}

fn main() {
    if let Some(case) = std::env::args().nth(1) {
        fault(&case);
        println!("{case}: no fault");
        std::process::exit(0);
    }

    // Values still round-trip.
    let mut a = 0u8;
    let mut b = 0u128;
    let mut c = (0u32, 0u64);
    let mut d = [0u8; 40];
    let mut e = u32x4::splat(0);
    unsafe {
        write_volatile(&mut a, black_box(7));
        write_volatile(&mut b, black_box(1 << 100));
        write_volatile(&mut c, black_box((3, 4)));
        write_volatile(&mut d, black_box([9; 40]));
        write_volatile(&mut e, black_box(u32x4::from_array([1, 2, 3, 4])));
        assert_eq!(read_volatile(&a), 7);
        assert_eq!(read_volatile(&b), 1 << 100);
        assert_eq!(read_volatile(&c), (3, 4));
        assert_eq!(read_volatile(&d), [9; 40]);
        assert_eq!(read_volatile(&e).to_array(), [1, 2, 3, 4]);
    }

    let exe = std::env::current_exe().unwrap();
    for case in ["u8", "u128", "pair", "array", "simd", "unit_then_u16"] {
        let out = Command::new(&exe).arg(case).output().unwrap();
        assert!(
            !out.status.success(),
            "an unused volatile read of {case} from {BAD:#x} did not fault: {}",
            String::from_utf8_lossy(&out.stdout)
        );
    }
    println!("volatile_unused ok");
}
