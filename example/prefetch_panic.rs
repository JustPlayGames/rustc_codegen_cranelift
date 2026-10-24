// With `-Zthreads` > 1 codegen units are translated ahead on rustc's other threads. A job that
// panics (an internal compiler error) must make rustc exit with that error, not leave the main
// thread waiting for the unit forever. The build system's test
// sets CG_CLIF_TEST_PANIC_IN_PREFETCH, which makes every prefetched unit panic.

macro_rules! modules {
    ($($name:ident),*) => {
        $(
            pub mod $name {
                #[inline(never)]
                pub fn work(n: u64) -> u64 {
                    let mut acc = n;
                    for i in 0..n {
                        acc = acc.wrapping_mul(31).wrapping_add(i ^ (acc >> 3));
                    }
                    acc
                }
            }
        )*
        fn main() {
            let mut total = 0u64;
            $( total = total.wrapping_add($name::work(std::hint::black_box(10))); )*
            println!("{total}");
        }
    };
}

modules!(m00, m01, m02, m03, m04, m05, m06, m07, m08, m09, m10, m11, m12, m13, m14, m15,
    m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31);
