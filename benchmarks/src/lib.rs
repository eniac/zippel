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

pub mod sumcheck;
