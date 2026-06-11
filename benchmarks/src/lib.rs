//! Comparison benchmarks: zippel-generated protocols vs. native Rust
//! implementations.
//!
//! Each protocol lives in its own submodule with two parallel halves
//! (`zippel_side` and `native_side`) plus a shared input-generation
//! helper that seeds both halves identically.

use std::time::Duration;

#[derive(Debug, Clone, Copy)]
pub struct Timing {
    pub prove: Duration,
    pub verify: Duration,
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

pub mod cache;
pub mod groth16;
pub mod hyrax;
pub mod ipa;
pub mod kzg;
pub mod pari;
pub mod pari_upstream;
pub mod pst13;
pub mod pst13_upstream;
pub mod schnorr;
pub mod spartan;
pub mod sumcheck;
pub mod sumcheck_upstream;
