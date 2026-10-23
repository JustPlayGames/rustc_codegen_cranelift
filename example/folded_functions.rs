// Functions whose Cranelift IR is the same are compiled once and the others become aliases of
// that code (`fold_identical`): calls, function pointers (also in statics and vtables), drop
// glue and unwinding through them must keep working.

use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};

thread_local! {
    static DROPS: Cell<u32> = const { Cell::new(0) };
}

#[derive(Default, Clone, Copy)]
struct A(u32);
#[derive(Default, Clone, Copy)]
struct B(u32);

trait Get {
    fn get(&self) -> u32;
}
impl Get for A {
    fn get(&self) -> u32 {
        self.0 + 1
    }
}
impl Get for B {
    fn get(&self) -> u32 {
        self.0 + 1
    }
}

#[inline(never)]
fn twice<T: Get>(x: &T) -> u32 {
    x.get() * 2
}

// The same code for A and B; each also calls its own (folded) `twice`.
#[inline(never)]
fn sum<T: Get + Default>(xs: &[T]) -> u32 {
    xs.iter().map(twice).sum::<u32>() + twice(&T::default())
}

struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        DROPS.with(|d| d.set(d.get() + 1));
    }
}

// A cleanup to run when `f` unwinds through it.
#[inline(never)]
fn guarded<T: Default>(f: fn() -> T) -> T {
    let _guard = Guard;
    f()
}

fn boom_a() -> A {
    panic!("boom a")
}
fn boom_b() -> B {
    panic!("boom b")
}

static TWICE_B: fn(&B) -> u32 = twice::<B>;

fn main() {
    let a = vec![A(1), A(2), A(3)];
    let b = vec![B(1), B(2), B(3)];
    assert_eq!(sum(&a), 20);
    assert_eq!(sum(&b), 20);

    let fa: fn(&A) -> u32 = twice::<A>;
    let fb: fn(&B) -> u32 = std::hint::black_box(twice::<B>);
    assert_eq!(fa(&A(4)), 10);
    assert_eq!(fb(&B(5)), 12);
    assert_eq!(TWICE_B(&B(6)), 14);

    let dyns: Vec<Box<dyn Get>> = vec![Box::new(A(7)), Box::new(B(8))];
    assert_eq!(dyns.iter().map(|x| x.get()).sum::<u32>(), 17);

    // Drop glue of two vectors with equally laid out elements.
    let va: Vec<Vec<A>> = vec![a.clone(), a];
    let vb: Vec<Vec<B>> = vec![b.clone(), b];
    drop(std::hint::black_box(va));
    drop(std::hint::black_box(vb));

    std::panic::set_hook(Box::new(|_| {}));
    assert!(catch_unwind(AssertUnwindSafe(|| guarded(boom_a))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| guarded(boom_b))).is_err());
    assert_eq!(guarded(A::default).0 + guarded(B::default).0, 0);
    assert_eq!(DROPS.with(|d| d.get()), 4);
    println!("ok");
}
