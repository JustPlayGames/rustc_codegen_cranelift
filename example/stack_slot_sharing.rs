// When optimizing, locals whose storage is never live at the same time share stack slots.
// This checks that values survive that sharing, and that a deep recursion through a builder
// chain of large temporaries fits a stack it only fits with sharing (built with -Copt-level=2).

#[derive(Clone)]
struct Big {
    data: [u64; 128],
    n: u64,
}

impl Big {
    #[inline(never)]
    fn step(mut self, x: u64) -> Self {
        self.data[(x % 128) as usize] += x;
        self.n += x;
        self
    }
}

#[inline(never)]
fn new() -> Big {
    Big { data: [0; 128], n: 0 }
}

#[inline(never)]
fn recurse(depth: u32) -> u64 {
    if depth == 0 {
        return 0;
    }
    // 16 statements, each with 1 KiB temporaries that die at the end of the statement.
    let mut sum = 0;
    sum += new().step(1).n;
    sum += new().step(2).n;
    sum += new().step(3).data[3];
    sum += new().step(4).n;
    sum += new().step(5).n;
    sum += new().step(6).n;
    sum += new().step(7).n;
    sum += new().step(8).n;
    sum += new().step(9).n;
    sum += new().step(10).n;
    sum += new().step(11).n;
    sum += new().step(12).n;
    sum += new().step(13).n;
    sum += new().step(14).n;
    sum += new().step(15).n;
    sum += new().step(16).n;
    sum + std::hint::black_box(recurse(depth - 1))
}

#[inline(never)]
fn branches(k: u64) -> u64 {
    // Each arm's temporaries may share with the others', but `keep` lives across all of them.
    let keep = new().step(7);
    let r = match k % 3 {
        0 => new().step(1).step(2).n,
        1 => new().step(3).step(4).data[3],
        _ => {
            let mut acc = 0;
            for i in 0..4 {
                let t = new().step(i + 1);
                let u = t.clone().step(10);
                acc += t.n + u.n + keep.n;
            }
            acc
        }
    };
    r + keep.n + keep.data[7]
}

fn main() {
    assert_eq!(recurse(1), 136);
    assert_eq!(branches(0), 3 + 14);
    assert_eq!(branches(1), 3 + 14);
    // t.n = i+1, u.n = i+11, keep.n = 7 for i in 0..4: 10 + 50 + 28 = 88
    assert_eq!(branches(2), 88 + 14);

    // 300 levels: a few KiB each when the temporaries share slots, 32+ KiB each when they don't,
    // which would overflow this 2 MiB stack.
    let r = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| recurse(300))
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(r, 300 * 136);
}
