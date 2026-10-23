//! Native baseline implementations vendored for protocol comparisons.
//!
//! Each tree retains its provenance and local changes. Keep benchmark setup and
//! cross-verification adapters in the corresponding protocol harness.

pub mod ark_spartan;
pub mod dekart;
pub mod dory;
pub mod hyperplonk;
pub mod hyrax;
pub mod kzh;
#[cfg(test)]
pub(crate) mod libspartan;
pub mod pari;
pub mod pst13;
pub mod sumcheck;
