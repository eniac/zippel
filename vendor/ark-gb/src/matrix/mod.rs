//! Sparse matrix support for ark-gb.
//!
//! The base data shape — `Matrix<F> = Vec<Vec<(F, usize)>>` — and its
//! [`transpose`] / [`mat_vec_mul`] helpers are copied verbatim from
//! [`arkworks-rs/snark`] (`relations/src/utils/matrix.rs`,
//! commit `6d5f7ae`, dual MIT/Apache-2.0). ark-gb is GPL-3.0-or-later;
//! the original licences are compatible with redistribution under
//! GPL-3 (one-way upgrade). See ADR-022 for the full attribution.
//!
//! Phase L extends this layout with the operations a future F4-style
//! reducer needs:
//!
//! * [`SparseRow`] — a strictly column-sorted sparse row with a
//!   no-zero-entries invariant.
//! * row arithmetic (scale, AXPY).
//! * Gaussian elimination ([`row_echelon`], [`rref`], [`rank`]).
//!
//! The Phase L surface is monomial-agnostic. F4 wiring (assembling
//! S-pair batches into a [`Matrix`], reading basis elements out of an
//! RREF) is **out of scope** for Phase L and lives in a successor phase.
//!
//! [`arkworks-rs/snark`]: https://github.com/arkworks-rs/snark

pub mod gauss;
pub mod sparse;

pub use gauss::{rank, row_echelon, rref};
pub use sparse::{Matrix, SparseRow, mat_vec_mul, transpose};
