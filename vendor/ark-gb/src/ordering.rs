//! Monomial orderings.
//!
//! Following zippel's design, the monomial order is pinned by the
//! monomial type itself via its `Ord` impl (see
//! [`crate::monomial::GrevLexTerm`], [`crate::monomial::OddElimTerm`]).
//! The runtime `MonoOrder` enum and `MonoOrder` trait that previously
//! lived here have been removed; pipeline functions are generic in
//! `M: Monomial<F>` and dispatch via `M::cmp` statically.
