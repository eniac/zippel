//! Comparison benchmarks: zippel-generated protocols vs. native Rust
//! implementations.
//!
//! Each protocol lives in its own submodule with two parallel halves
//! (`zippel_side` and `native_side`) plus a shared input-generation
//! helper that seeds both halves identically.

use std::time::Duration;

/// Per-sample prover and verifier wall-times and peak heaps for one
/// protocol measurement.
///
/// Produced by every `Setup::time_protocol` in this crate, for both the
/// `zippel_side` and `native_side` halves, so the two are directly
/// comparable. Every vector holds [`SAMPLES`] entries, one per run, in run
/// order (see [`sample_with`]). Nothing includes input generation, key/SRS
/// setup, or `.zippel` compilation — those happen in `Setup::new`.
#[derive(Debug, Clone)]
pub struct Timing {
    /// Wall-time of each prover run on identical inputs.
    pub prove: Vec<Duration>,
    /// Wall-time of each verifier run on one fixed proof.
    pub verify: Vec<Duration>,
    /// Peak heap of each prover run, in bytes above what was live when it
    /// started (see [`mem`]).
    pub prove_peak: Vec<usize>,
    /// Peak heap of each verifier run, measured the same way.
    pub verify_peak: Vec<usize>,
}

impl Timing {
    /// Mean prover wall-time.
    #[must_use]
    pub fn prove_mean(&self) -> Duration {
        mean(&self.prove)
    }

    /// Mean verifier wall-time.
    #[must_use]
    pub fn verify_mean(&self) -> Duration {
        mean(&self.verify)
    }
}

/// Mean of a non-empty slice of durations.
///
/// # Panics
/// Panics if `ds` is empty or longer than `u32::MAX`.
#[must_use]
pub fn mean(ds: &[Duration]) -> Duration {
    ds.iter().sum::<Duration>() / u32::try_from(ds.len()).expect("sample count fits u32")
}

/// Peak-heap measurement. The benchmark binaries install
/// [`mem::Counting`] as the global allocator; it counts nothing until
/// [`mem::peak_of`] switches it on, so timed runs pay one relaxed atomic
/// load per allocation.
pub mod mem {
    use std::alloc::{GlobalAlloc, Layout};
    use std::sync::atomic::{AtomicBool, AtomicIsize, Ordering::Relaxed};

    static ON: AtomicBool = AtomicBool::new(false);
    static LIVE: AtomicIsize = AtomicIsize::new(0);
    static PEAK: AtomicIsize = AtomicIsize::new(0);

    /// The allocator [`Counting`] forwards to: the system allocator, or
    /// dhat's under the `dhat` feature so [`crate::sample_with`] can
    /// heap-profile a run.
    #[cfg(not(feature = "dhat"))]
    static INNER: std::alloc::System = std::alloc::System;
    #[cfg(feature = "dhat")]
    static INNER: dhat::Alloc = dhat::Alloc;

    /// The inner allocator, counting live bytes while measurement is on.
    pub struct Counting;

    #[allow(clippy::cast_possible_wrap)]
    fn grow(bytes: usize) {
        let live = LIVE.fetch_add(bytes as isize, Relaxed) + bytes as isize;
        PEAK.fetch_max(live, Relaxed);
    }

    #[allow(clippy::cast_possible_wrap)]
    fn shrink(bytes: usize) {
        LIVE.fetch_sub(bytes as isize, Relaxed);
    }

    // SAFETY: every call forwards to `INNER` unchanged; the counters have
    // no effect on the returned memory.
    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let p = unsafe { INNER.alloc(layout) };
            if !p.is_null() && ON.load(Relaxed) {
                grow(layout.size());
            }
            p
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            let p = unsafe { INNER.alloc_zeroed(layout) };
            if !p.is_null() && ON.load(Relaxed) {
                grow(layout.size());
            }
            p
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { INNER.dealloc(ptr, layout) };
            if ON.load(Relaxed) {
                shrink(layout.size());
            }
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            let p = unsafe { INNER.realloc(ptr, layout, new_size) };
            if !p.is_null() && ON.load(Relaxed) {
                if new_size > layout.size() {
                    grow(new_size - layout.size());
                } else {
                    shrink(layout.size() - new_size);
                }
            }
            p
        }
    }

    /// Run `f` once and return its result with the peak number of heap
    /// bytes live at any moment during the call, counted from zero at the
    /// start: transient buffers count, memory that was already live does
    /// not. Only meaningful when [`Counting`] is the global allocator, and
    /// nothing else may allocate concurrently.
    #[allow(clippy::cast_sign_loss)]
    pub fn peak_of<T>(f: impl FnOnce() -> T) -> (T, usize) {
        LIVE.store(0, Relaxed);
        PEAK.store(0, Relaxed);
        ON.store(true, Relaxed);
        let out = f();
        ON.store(false, Relaxed);
        (out, PEAK.load(Relaxed).max(0) as usize)
    }
}

/// `SAMPLES` wall-times of `f`, then `SAMPLES` peak heaps from as many
/// further runs; see [`sample_with`].
#[track_caller]
pub fn sample<T>(f: impl FnMut() -> T) -> (Vec<Duration>, Vec<usize>, T) {
    let mut f = f;
    sample_with(|| (), |()| f())
}

/// Runs `f` [`SAMPLES`] times under a timer, then [`SAMPLES`] more times
/// with the heap counter on, so counting never touches a timed run.
/// Returns every run's wall-time and every counted run's peak heap, in run
/// order, and the last run's output. `setup` (e.g. a fresh transcript)
/// runs before each call, outside both the timer and the memory count;
/// each output is dropped outside them too.
#[track_caller]
pub fn sample_with<S, T>(
    mut setup: impl FnMut() -> S,
    mut f: impl FnMut(S) -> T,
) -> (Vec<Duration>, Vec<usize>, T) {
    let n = *SAMPLES;
    #[cfg(feature = "dhat")]
    let caller = std::panic::Location::caller();
    let mut times = Vec::with_capacity(n);
    for _ in 0..n {
        let state = setup();
        let t = std::time::Instant::now();
        let out = f(state);
        times.push(t.elapsed());
        drop(out);
    }
    let mut peaks = Vec::with_capacity(n);
    let mut last = None;
    for _ in 0..n {
        drop(last.take());
        let state = setup();
        #[cfg(feature = "dhat")]
        let profiler = peaks.is_empty().then(|| dhat_profiler(caller));
        let (out, peak) = mem::peak_of(|| f(state));
        #[cfg(feature = "dhat")]
        drop(profiler);
        peaks.push(peak);
        last = Some(out);
    }
    (times, peaks, last.expect("SAMPLES > 0"))
}

/// Starts dhat for the first counted run of a measurement. Each profile is
/// written to `$DHAT_DIR` (default `dhat/`) as `<n>-<file>_<line>.json`,
/// `<n>` counting measurements in run order and `<file>_<line>` the
/// `sample`/`sample_with` call site that took it. `$DHAT_FRAMES` (default
/// 32) caps the backtrace depth.
#[cfg(feature = "dhat")]
fn dhat_profiler(caller: &std::panic::Location<'_>) -> dhat::Profiler {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::var("DHAT_DIR").unwrap_or_else(|_| "dhat".into());
    std::fs::create_dir_all(&dir).expect("create DHAT_DIR");
    let file = std::path::Path::new(caller.file())
        .file_stem()
        .map_or_else(String::new, |s| s.to_string_lossy().into_owned());
    let frames = std::env::var("DHAT_FRAMES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(32);
    dhat::Profiler::builder()
        .file_name(format!("{dir}/{n:02}-{file}_{}.json", caller.line()))
        .trim_backtraces(Some(frames))
        .build()
}

/// Runs a `.zippel` compile [`SAMPLES`] times and returns the last
/// handler with every run's wall-time. The previous handler is dropped
/// before each run, outside the timer.
pub fn sample_compile<H>(mut compile: impl FnMut() -> H) -> (H, Vec<Duration>) {
    let n = *SAMPLES;
    let mut times = Vec::with_capacity(n);
    let mut last = None;
    for _ in 0..n {
        drop(last.take());
        let t = std::time::Instant::now();
        let h = compile();
        times.push(t.elapsed());
        last = Some(h);
    }
    (last.expect("SAMPLES > 0"), times)
}

/// Number of runs behind every measurement: each prover and verifier
/// wall-time, each peak heap, and each compile time is taken this many
/// times and every sample is kept, so the CSVs carry one row per sample.
///
/// Resolved once at process start from the `BENCH_SAMPLES` environment
/// variable (must be `> 0`); the default is 10.
///
/// ```sh
/// BENCH_SAMPLES=3 cargo run --release --bin bench_all
/// ```
///
/// Use as `*SAMPLES` (deref `LazyLock<usize>` → `usize`).
pub static SAMPLES: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
    std::env::var("BENCH_SAMPLES")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(10)
});

// The `*_upstream` modules below are vendored third-party code (see each
// module's doc comment for provenance) and are not to be edited to satisfy
// lints. `#[allow(warnings)]` here — in this non-vendored file, applying
// recursively to the vendored module tree it annotates — blanket-suppresses
// lints for them instead.
#[allow(warnings)]
pub mod ark_spartan_upstream;
pub mod cache;
pub mod dekart;
pub mod dekart_upstream;
pub mod dory;
pub mod dory_upstream;
pub mod groth16;
pub mod hyperplonk;
pub mod hyperplonk_upstream;
pub mod hyrax;
#[allow(warnings)]
pub mod hyrax_upstream;
pub mod ipa;
pub mod kzg;
pub mod kzh;
pub mod kzh_upstream;
pub mod pari;
#[allow(warnings)]
pub mod pari_upstream;
pub mod pst13;
#[allow(warnings)]
pub mod pst13_upstream;
pub mod schnorr;
pub mod spartan;
pub mod sumcheck;
#[allow(warnings)]
pub mod sumcheck_upstream;
