//! Gröbner-basis test suite.
//!
//! * [`buchberger`] — unit tests for the in-tree legacy Buchberger
//!   implementation (term ops, S-polynomial, monomial orderings, small
//!   end-to-end examples).
//! * [`regression`] — cross-backend regression suite asserting that the
//!   shipping ark-gb path agrees element-wise with the legacy
//!   implementation on canonical fixtures (Katsura, Cyclic, etc.).

pub mod buchberger;
pub mod regression;
