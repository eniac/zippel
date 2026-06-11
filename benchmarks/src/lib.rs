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
/// proof; `prove` stays single-shot because provers are slow and one run
/// already takes seconds-to-minutes at log_size=20.
///
/// IPA is the exception — its verifier is O(N) MSM, ~tens of seconds per
/// call at S=20, so it stays single-sample. See `ipa::*::time_protocol`.
pub const VERIFY_SAMPLES: u32 = 100;

pub mod cache;
pub mod groth16;
pub mod hyrax;
pub mod ipa;
pub mod kzg;
pub mod pari;
pub mod pari_upstream;
pub mod pst13;
pub mod schnorr;
pub mod spartan;
pub mod sumcheck;
pub mod sumcheck_upstream;
