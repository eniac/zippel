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
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicBool, AtomicIsize, Ordering::Relaxed};

    static ON: AtomicBool = AtomicBool::new(false);
    static LIVE: AtomicIsize = AtomicIsize::new(0);
    static PEAK: AtomicIsize = AtomicIsize::new(0);

    /// The system allocator, counting live bytes while measurement is on.
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

    // SAFETY: every call forwards to `System` unchanged; the counters have
    // no effect on the returned memory.
    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let p = unsafe { System.alloc(layout) };
            if !p.is_null() && ON.load(Relaxed) {
                grow(layout.size());
            }
            p
        }

        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            let p = unsafe { System.alloc_zeroed(layout) };
            if !p.is_null() && ON.load(Relaxed) {
                grow(layout.size());
            }
            p
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { System.dealloc(ptr, layout) };
            if ON.load(Relaxed) {
                shrink(layout.size());
            }
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            let p = unsafe { System.realloc(ptr, layout, new_size) };
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
pub fn sample_with<S, T>(
    mut setup: impl FnMut() -> S,
    mut f: impl FnMut(S) -> T,
) -> (Vec<Duration>, Vec<usize>, T) {
    let n = *SAMPLES;
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
        let (out, peak) = mem::peak_of(|| f(state));
        peaks.push(peak);
        last = Some(out);
    }
    (times, peaks, last.expect("SAMPLES > 0"))
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
