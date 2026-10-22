// When optimizing, a local moved into a temporary only to be moved into a call is passed to the
// call in place, without a copy. This checks that values, drops and later writes of the source
// survive that, and that a deep recursion handing a large closure down each level fits a stack it
// only fits without the copies (built with -Copt-level=2).

use std::cell::Cell;

struct Counted<'a> {
    drops: &'a Cell<u32>,
    data: [u64; 32],
}

impl Drop for Counted<'_> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

// MIR moves `f` into a temporary in each arm (it has a drop flag), then into `call_once`.
#[inline(never)]
fn with_maybe<R>(push: Option<u64>, log: &mut Vec<u64>, f: impl FnOnce(&mut Vec<u64>) -> R) -> R {
    if let Some(x) = push {
        log.push(x);
        let r = f(log);
        log.push(x + 100);
        r
    } else {
        f(log)
    }
}

#[inline(never)]
fn twice<R>(log: &mut Vec<u64>, f: impl FnOnce(&mut Vec<u64>) -> R) -> R {
    with_maybe(Some(1), log, |log| with_maybe(None, log, f))
}

#[inline(never)]
fn consume(mut big: [u64; 64]) -> u64 {
    // The callee owns its by-reference argument and may write to it.
    big[0] += 1000;
    big.iter().sum()
}

#[inline(never)]
fn reuse_after_move() -> u64 {
    let mut src = [1u64; 64];
    let mut total = 0;
    for round in 0..3 {
        let tmp = src;
        total += consume(tmp);
        // The source is written again after its move into the call and read once more.
        src = [round + 2; 64];
        total += src[0];
    }
    total
}

static JOB_DROPS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

struct Job {
    pad: [u64; 512],
    sum: u64,
}

impl Drop for Job {
    fn drop(&mut self) {
        JOB_DROPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

// A 4 KiB value handed down every level through a moved temporary: copied into each frame
// unless forwarded. (LLVM keeps these copies too: its frames overflow this test's stack.)
#[inline(never)]
fn level(depth: u32, mut job: Job) -> u64 {
    if depth == 0 {
        return job.sum;
    }
    job.sum += job.pad[depth as usize % 512];
    if depth % 2 == 0 { level(depth - 1, job) } else { std::hint::black_box(level(depth - 1, job)) }
}

fn main() {
    let drops = Cell::new(0);
    let c = Counted { drops: &drops, data: [3; 32] };
    let mut log = vec![];
    let r = twice(&mut log, move |log| {
        log.push(7);
        let c = c; // the whole value, not just the `Copy` field (edition 2021 captures)
        c.data.iter().sum::<u64>()
    });
    assert_eq!(r, 96);
    assert_eq!(log, [1, 7, 101]);
    assert_eq!(drops.get(), 1);

    // Not called: dropped exactly once on the way.
    let c = Counted { drops: &drops, data: [0; 32] };
    let mut log = vec![];
    with_maybe(Some(5), &mut log, move |_| drop(c));
    assert_eq!(drops.get(), 2);

    // 64 + 1000 + 2, 64 + 1000 + 3 (src = [2; 64] -> 128 + 1000), ...
    assert_eq!(reuse_after_move(), (64 + 1000) + 2 + (128 + 1000) + 3 + (192 + 1000) + 4);

    // 400 levels of 4 KiB copies would need 1.6 MiB, more than this 1 MiB stack.
    let r = std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(|| level(400, Job { pad: [1; 512], sum: 0 }))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(r, 400);
    assert_eq!(JOB_DROPS.load(std::sync::atomic::Ordering::Relaxed), 1);
}
