// Unwinding from inside stack probes on Linux x86-64: frames of a page or more are probed in the
// prologue, and those probes move RSP. An unwinder stopping there (a stack overflow faults in a
// probe; a sampling profiler's signal can land in one) must still find the callers, and Rust's
// own overflow handler must still report the overflow. Each case runs in a child process, so a
// crash in the unwinder fails the case instead of the whole test.

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod linux {
    use std::ffi::c_void;
    use std::hint::black_box;
    use std::mem::MaybeUninit;
    use std::os::unix::process::ExitStatusExt;
    use std::process::Command;

    #[repr(C)]
    struct SigAction {
        handler: usize,
        mask: [u64; 16],
        flags: i32,
        restorer: usize,
    }
    #[repr(C)]
    struct ITimerVal {
        interval_s: i64,
        interval_us: i64,
        value_s: i64,
        value_us: i64,
    }
    unsafe extern "C" {
        fn sigaction(sig: i32, act: *const SigAction, old: *mut SigAction) -> i32;
        fn setitimer(which: i32, new: *const ITimerVal, old: *mut ITimerVal) -> i32;
        fn _Unwind_Backtrace(
            cb: extern "C" fn(*mut c_void, *mut c_void) -> i32,
            arg: *mut c_void,
        ) -> i32;
        fn _Unwind_GetIP(ctx: *mut c_void) -> usize;
        fn write(fd: i32, buf: *const c_void, n: usize) -> isize;
        fn madvise(addr: *mut c_void, len: usize, advice: i32) -> i32;
        fn _exit(code: i32) -> !;
    }
    const SIGSEGV: i32 = 11;
    const SIGBUS: i32 = 7;
    const SIGPROF: i32 = 27;
    const SA_SIGINFO: i32 = 0x4;
    const SA_ONSTACK: i32 = 0x0800_0000;
    const SA_RESTART: i32 = 0x1000_0000;
    const ITIMER_PROF: i32 = 2;
    const URC_END_OF_STACK: i32 = 5;
    const MADV_DONTNEED: i32 = 4;
    // `ucontext_t`'s RIP (`uc_mcontext.gregs[REG_RIP]`).
    const UC_RIP: usize = 168;

    // Recursion whose every frame is probed (24 KiB: the probe loop), until the stack overflows.
    #[inline(never)]
    #[unsafe(no_mangle)]
    pub fn deep_sysv(d: u64) -> u64 {
        let mut a = [0u64; 3000];
        a[black_box(5)] = d;
        black_box(&mut a);
        if d == 0 { 0 } else { deep_sysv(d - 1) + a[5] }
    }

    // The same with the Windows x64 calling convention, whose probes move RSP outside Windows too.
    #[inline(never)]
    #[unsafe(no_mangle)]
    pub extern "win64" fn deep_win64(d: u64) -> u64 {
        let mut a = [0u64; 3000];
        a[black_box(5)] = d;
        black_box(&mut a);
        if d == 0 { 0 } else { deep_win64(d - 1) + a[5] }
    }

    fn in_fn(ip: usize, f: usize) -> bool {
        ip >= f && ip < f + 0x400
    }

    fn put(s: &[u8]) {
        unsafe { write(2, s.as_ptr().cast(), s.len()) };
    }

    fn put_num(mut v: usize) {
        let mut b = [0u8; 20];
        let mut i = 20;
        loop {
            i -= 1;
            b[i] = b'0' + (v % 10) as u8;
            v /= 10;
            if v == 0 {
                break;
            }
        }
        put(&b[i..]);
    }

    // The fault: unwind from the probe that hit the guard page and count the recursive frames
    // found (correct CFI: the walk goes through dozens of them).
    static mut DEEP: usize = 0;
    static mut FRAMES: usize = 0;
    static mut TARGET: usize = 0;

    extern "C" fn count_frame(ctx: *mut c_void, _: *mut c_void) -> i32 {
        unsafe {
            FRAMES += 1;
            if in_fn(_Unwind_GetIP(ctx), TARGET) {
                DEEP += 1;
            }
            if FRAMES >= 64 { URC_END_OF_STACK } else { 0 }
        }
    }

    extern "C" fn on_fault(_: i32, _: *mut c_void, _: *mut c_void) {
        unsafe {
            _Unwind_Backtrace(count_frame, std::ptr::null_mut());
            put(b"frames=");
            put_num(FRAMES);
            put(b" recursive=");
            put_num(DEEP);
            put(b"\n");
            _exit(if DEEP >= 8 { 0 } else { 1 });
        }
    }

    fn fault(win64: bool) {
        unsafe {
            TARGET = if win64 { deep_win64 as *const () as usize } else { deep_sysv as *const () as usize };
            let act = SigAction {
                handler: on_fault as *const () as usize,
                mask: [0; 16],
                flags: SA_SIGINFO | SA_ONSTACK,
                restorer: 0,
            };
            sigaction(SIGSEGV, &act, std::ptr::null_mut());
            sigaction(SIGBUS, &act, std::ptr::null_mut());
        }
        overflow(win64);
    }

    fn overflow(win64: bool) {
        let t = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(move || if win64 { deep_win64(1 << 40) } else { deep_sysv(1 << 40) })
            .unwrap();
        println!("{}", t.join().unwrap());
    }

    // The sampler: SIGPROF signals land while big frames are probed, and each walks the stack:
    // the frame after the interrupted one must be `driver`.
    static mut RIP: usize = 0;
    static mut AFTER_RIP: bool = false;
    static mut FOUND: bool = false;
    static mut SAMPLES: usize = 0;
    static mut IN_PROBES: usize = 0;
    static mut LOST: usize = 0;

    extern "C" fn find_driver(ctx: *mut c_void, _: *mut c_void) -> i32 {
        unsafe {
            let ip = _Unwind_GetIP(ctx);
            if AFTER_RIP {
                FOUND = in_fn(ip, driver as *const () as usize);
                return URC_END_OF_STACK;
            }
            AFTER_RIP = ip == RIP;
            0
        }
    }

    // The probes come first in the prologue.
    fn in_probes(ip: usize, f: usize) -> bool {
        ip >= f && ip < f + 0x30
    }

    extern "C" fn on_prof(_: i32, _: *mut c_void, uc: *mut c_void) {
        unsafe {
            SAMPLES += 1;
            RIP = *((uc as *const u8).add(UC_RIP) as *const usize);
            if !in_probes(RIP, probed_sysv as *const () as usize)
                && !in_probes(RIP, probed_win64 as *const () as usize)
            {
                return;
            }
            IN_PROBES += 1;
            AFTER_RIP = false;
            FOUND = false;
            _Unwind_Backtrace(find_driver, std::ptr::null_mut());
            if !FOUND {
                LOST += 1;
            }
        }
    }

    // A frame of 1 MiB that is barely used: its prologue's 256 probes are most of its work.
    #[inline(never)]
    #[unsafe(no_mangle)]
    pub fn probed_sysv(x: u64) -> u64 {
        let mut a = MaybeUninit::<[u64; 1 << 17]>::uninit();
        let p = a.as_mut_ptr() as *mut u64;
        unsafe {
            p.write(x);
            black_box(p).read()
        }
    }

    #[inline(never)]
    #[unsafe(no_mangle)]
    pub extern "win64" fn probed_win64(x: u64) -> u64 {
        let mut a = MaybeUninit::<[u64; 1 << 17]>::uninit();
        let p = a.as_mut_ptr() as *mut u64;
        unsafe {
            p.write(x);
            black_box(p).read()
        }
    }

    // Gives back the pages of the stack below the caller's frame (where the probed frames go),
    // so that every probe faults and the samples land on the probes, as a stack overflow does.
    #[inline(never)]
    fn drop_stack_below() {
        let here = black_box(0u8);
        let top = (&here as *const u8 as *const () as usize - (64 << 10)) & !4095;
        let bottom = top - (3 << 20);
        unsafe { madvise(bottom as *mut c_void, top - bottom, MADV_DONTNEED) };
    }

    #[inline(never)]
    #[unsafe(no_mangle)]
    pub fn driver(n: u64) -> u64 {
        let mut s = 0u64;
        for i in 0..n {
            drop_stack_below();
            s = s.wrapping_add(probed_sysv(i));
            drop_stack_below();
            s = s.wrapping_add(probed_win64(i));
        }
        s
    }

    fn sample() {
        unsafe {
            let act = SigAction {
                handler: on_prof as *const () as usize,
                mask: [0; 16],
                flags: SA_SIGINFO | SA_RESTART,
                restorer: 0,
            };
            sigaction(SIGPROF, &act, std::ptr::null_mut());
            let every = ITimerVal { interval_s: 0, interval_us: 200, value_s: 0, value_us: 200 };
            setitimer(ITIMER_PROF, &every, std::ptr::null_mut());
        }
        let start = std::time::Instant::now();
        let mut s = 0;
        // About half a second of CPU time.
        while start.elapsed().as_millis() < 500 {
            s ^= driver(black_box(100));
        }
        unsafe {
            let off = ITimerVal { interval_s: 0, interval_us: 0, value_s: 0, value_us: 0 };
            setitimer(ITIMER_PROF, &off, std::ptr::null_mut());
            let (samples, in_probes, lost) = (SAMPLES, IN_PROBES, LOST);
            println!("samples={samples} in_probes={in_probes} lost={lost} ({})", s & 1);
            std::process::exit(if lost == 0 && in_probes >= 10 { 0 } else { 1 });
        }
    }

    fn child(case: &str) -> (std::process::ExitStatus, String) {
        let out = Command::new(std::env::current_exe().unwrap()).arg(case).output().unwrap();
        let text = String::from_utf8_lossy(&out.stdout).into_owned()
            + &String::from_utf8_lossy(&out.stderr);
        (out.status, text)
    }

    pub fn main() {
        match std::env::args().nth(1).as_deref() {
            Some("overflow-sysv") => return overflow(false),
            Some("overflow-win64") => return overflow(true),
            Some("fault-sysv") => return fault(false),
            Some("fault-win64") => return fault(true),
            Some("sample") => return sample(),
            _ => {}
        }
        let mut failed = false;
        for case in ["overflow-sysv", "overflow-win64"] {
            // Rust's own handler reports the overflow and aborts.
            let (status, text) = child(case);
            let ok = status.signal() == Some(6) && text.contains("has overflowed its stack");
            println!("{case}: {} ({status})", if ok { "ok" } else { "FAIL" });
            failed |= !ok;
            if !ok {
                println!("{text}");
            }
        }
        for case in ["fault-sysv", "fault-win64", "sample"] {
            let (status, text) = child(case);
            let ok = status.success();
            println!("{case}: {} ({status}) {}", if ok { "ok" } else { "FAIL" }, text.trim());
            failed |= !ok;
        }
        assert!(!failed);
    }
}

fn main() {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    linux::main();
}
