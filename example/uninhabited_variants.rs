// Enum locals kept in Cranelift variables whose variant is uninhabited but still laid out: an
// aggregate written into that variant (`Some((a, b))` in `Option::<(Never, _)>::zip`) has fields
// that don't line up with the variables, so such a local lives in memory. tower-http's
// `Option<NeverClassifyEos<_>>::zip::<DefaultOnFailure>` hit an internal error here
// (place_field, "is not in its variables").

use std::hint::black_box;

#[allow(dead_code)]
#[repr(usize)]
#[derive(Clone, Copy, Debug, PartialEq)]
enum Level {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq)]
enum Unit {
    Seconds,
    Millis,
    Micros,
    Nanos,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct OnFailure {
    level: Level,
    unit: Unit,
}

enum Never {}

// A zero-sized uninhabited type, as tower-http's `NeverClassifyEos<T>`.
struct NeverEos<T> {
    _output: std::marker::PhantomData<fn() -> T>,
    _never: Never,
}

#[inline(never)]
fn zip_none(other: Option<OnFailure>) -> bool {
    let none: Option<NeverEos<u32>> = black_box(None);
    none.zip(other).is_none()
}

// The same written by hand: the variant's fields set one by one from a match.
#[allow(dead_code)]
enum Classified<T> {
    Ready(T),
    RequiresEos(NeverEos<T>),
}

#[inline(never)]
fn pair(c: Classified<u8>, f: OnFailure) -> Option<(NeverEos<u8>, OnFailure)> {
    match c {
        Classified::Ready(_) => None,
        Classified::RequiresEos(e) => Some((e, f)),
    }
}

#[inline(never)]
fn some_failure(f: Option<OnFailure>) -> Option<(OnFailure, u8)> {
    f.zip(Some(7))
}

fn main() {
    let failure = OnFailure { level: Level::Warn, unit: Unit::Millis };
    assert!(zip_none(black_box(Some(failure))));
    assert!(zip_none(black_box(None)));
    assert!(pair(black_box(Classified::Ready(3)), failure).is_none());
    // An inhabited pair still lives in variables and keeps its values.
    assert_eq!(some_failure(black_box(Some(failure))), Some((failure, 7)));
    assert_eq!(some_failure(black_box(None)), None);
    println!("ok");
}
