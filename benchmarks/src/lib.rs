//! Comparison benchmarks: zippel-generated protocols vs. native Rust
//! implementations.
//!
//! Each protocol lives in its own submodule with two parallel halves
//! (`zippel_side` and `native_side`) plus a shared input-generation
//! helper that seeds both halves identically.

use std::time::Duration;

/// Mean prover and verifier wall-times for one protocol measurement.
///
/// Produced by every `Setup::time_protocol` in this crate, for both the
/// `zippel_side` and `native_side` halves, so the two are directly
/// comparable. Neither field includes input generation, key/SRS setup, or
/// `.zippel` compilation — those happen in `Setup::new`.
#[derive(Debug, Clone, Copy)]
pub struct Timing {
    /// Mean wall-time of a single prover run, averaged over
    /// `PROVER_SAMPLES` (or `VERIFY_SAMPLES`, for the jitter-dominated
    /// Schnorr prover) invocations on identical inputs.
    pub prove: Duration,
    /// Mean wall-time of a single verifier run on one fixed proof,
    /// averaged over `VERIFY_SAMPLES` invocations. IPA is single-sample
    /// because its verifier is an O(N) MSM.
    pub verify: Duration,
    /// Peak heap of one prover run, in bytes above what was live when it
    /// started (see [`mem`]).
    pub prove_peak: usize,
    /// Peak heap of one verifier run, measured the same way.
    pub verify_peak: usize,
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

/// Mean wall-time of `f` over `samples` runs, then its peak heap from one
/// more, untimed run (so counting never touches a timed run). Returns the
/// mean, the peak, and the last run's output.
///
/// # Panics
/// Panics if `samples` is zero.
pub fn sample<T>(samples: u32, mut f: impl FnMut() -> T) -> (Duration, usize, T) {
    sample_with(samples, || (), |()| f())
}

/// [`sample`] with a per-run `setup` (e.g. a fresh transcript) that runs
/// before each call, outside both the timer and the memory count.
///
/// # Panics
/// Panics if `samples` is zero.
pub fn sample_with<S, T>(
    samples: u32,
    mut setup: impl FnMut() -> S,
    mut f: impl FnMut(S) -> T,
) -> (Duration, usize, T) {
    assert!(samples > 0);
    let mut total = Duration::ZERO;
    for _ in 0..samples {
        let state = setup();
        let t = std::time::Instant::now();
        let out = f(state);
        total += t.elapsed();
        drop(out);
    }
    let state = setup();
    let (out, peak) = mem::peak_of(|| f(state));
    (total / samples, peak, out)
}

/// Number of verifier samples to take per `time_protocol` call. Each
/// `Timing { verify }` returned by a `*_side::Setup::time_protocol(...)`
/// is the MEAN of this many independent verifier invocations on the same
/// proof.
///
/// IPA is the exception — its verifier is O(N) MSM, ~tens of seconds per
/// call at S=20, so it stays single-sample. See `ipa::*::time_protocol`.
pub const VERIFY_SAMPLES: u32 = 100;

/// Number of prover samples to take per `time_protocol` call. Each
/// `Timing { prove }` is the MEAN of this many independent prover
/// invocations on the same inputs.
///
/// Resolved once at process start from the `PROVER_SAMPLES` environment
/// variable (must be `> 0`). Default is **1** — single-shot per call —
/// because each prover run is seconds-to-minutes at log_size=18-20 and
/// repeatedly sampling multiplies the sweep wall-clock linearly. Override
/// when running short sizes where jitter dominates:
///
/// ```sh
/// PROVER_SAMPLES=10 cargo run --release --bin bench_all
/// ```
///
/// Schnorr is the exception — its prover is ~0.1ms, dominated by jitter,
/// so it samples at `VERIFY_SAMPLES` rate (100). See `schnorr::*::time_protocol`.
///
/// Use as `*PROVER_SAMPLES` (deref `LazyLock<u32>` → `u32`).
pub static PROVER_SAMPLES: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| {
    std::env::var("PROVER_SAMPLES")
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(1)
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
