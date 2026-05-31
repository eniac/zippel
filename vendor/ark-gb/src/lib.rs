//! # ark_gb
//!
//! Polynomial layer for the Singular Groebner-basis port.
//!
//! This crate is an early milestone of the port described in
//! `~/project/docs/rust-bba-port-plan.md`. It supplies the ring,
//! field, monomial, polynomial, and geobucket primitives that a
//! later `bba` driver will build on. There is deliberately **no**
//! S/T/L, **no** S-pair queue, **no** FFI, and **no** parallelism
//! in this crate yet.
//!
//! ## Current scope
//!
//! * **Field:** Z/p with `2 ≤ p < 2^31`, Barrett-reduced modular mul.
//! * **Ordering:** `DegRevLex` only.
//! * **Exponent width:** 8 bits per variable, up to
//!   [`MAX_VARS`](ring::MAX_VARS) variables. `MAX_VARS = 31` is the
//!   default-`W=4` alias for [`max_vars::<W>()`](ring::max_vars).
//!   Instantiate `Ring::<F, 8>` for up to 63 variables, or
//!   `Ring::<F, 16>` for up to 127, by threading the second const
//!   generic through `Poly`/`SBasis`/`compute_gb` etc.
//! * **Polynomial:** parallel `Vec<F>` / `Vec<MonoTerm>` with
//!   cached leading-term metadata.
//!
//! Public types are `Send + Sync` and intended to be shared through
//! `Arc<Ring>` once the driver lands.

#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs)]

pub mod bba;
pub mod bset;
pub mod computation;
pub mod f4;
pub mod field;
pub mod gm;
pub mod kbucket;
pub mod lobject;
pub mod lset;
pub mod matrix;
pub mod monomial;
pub mod ordering;
pub mod pair;
pub mod parallel;
pub mod poly;
pub mod reducer;
pub mod ring;
pub mod sbasis;
mod simd;
pub mod validate;

pub use bba::compute_gb;
pub use bset::BSet;
pub use computation::{Computation, SharedLSet, SharedSBasis};
pub use f4::compute_gb_f4;
pub use field::Field;
pub use kbucket::KBucket;
pub use lobject::LObject;
pub use lset::LSet;
pub use monomial::{GrevLexTerm, MonoTerm, Monomial, OddElimTerm};
pub use pair::{Pair, PairKey};
pub use parallel::{CancelHandle, Cancelled, compute_gb_parallel};
pub use poly::Poly;
pub use ring::Ring;
pub use sbasis::SBasis;

// Compile-time Send + Sync check on the key public types.
#[cfg(test)]
const _: fn() = || {
    use crate::monomial::GrevLexTerm;
    use ark_bls12_381::Fr;
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Ring<Fr>>();
    assert_send_sync::<MonoTerm>();
    assert_send_sync::<Poly<Fr, GrevLexTerm>>();
    assert_send_sync::<Pair>();
    assert_send_sync::<SBasis<Fr, GrevLexTerm>>();
    assert_send_sync::<LSet>();
    assert_send_sync::<BSet>();

    // Same checks at W=8 (cap = 63 vars). Catches any Send/Sync
    // bound that accidentally hard-codes W=4.
    assert_send_sync::<Ring<Fr, 8>>();
    assert_send_sync::<MonoTerm<8>>();
    assert_send_sync::<Poly<Fr, GrevLexTerm<8>, 8>>();
    assert_send_sync::<Pair<8>>();
    assert_send_sync::<SBasis<Fr, GrevLexTerm<8>, 8>>();
    assert_send_sync::<LSet<8>>();
    assert_send_sync::<BSet<8>>();
};

// KBucket and LObject are Send but deliberately not Sync
// (per-thread ownership).
#[cfg(test)]
const _: fn() = || {
    use crate::monomial::GrevLexTerm;
    use ark_bls12_381::Fr;
    fn assert_send<T: Send>() {}
    assert_send::<KBucket<Fr, GrevLexTerm>>();
    assert_send::<LObject<Fr, GrevLexTerm>>();
    assert_send::<KBucket<Fr, GrevLexTerm<8>, 8>>();
    assert_send::<LObject<Fr, GrevLexTerm<8>, 8>>();
};
