//! ark-gb backend: interprets [`MonoOrder`](crate::frontend::MonoOrder) and
//! routes through the external ark-gb crate.
//!
//! Internal types (`SparsePolynomial`, `GroebnerBasis`, `GrevLexTerm`, etc.)
//! live in submodules and are an implementation detail of this backend.

pub(crate) mod adapter;
pub(crate) mod buchberger;
mod engine;
pub(crate) mod monomial;
pub(crate) mod sparsepoly;
pub(crate) mod tiered;

pub use engine::ArkGb;

#[cfg(test)]
pub(crate) use buchberger::GroebnerBasis;
#[cfg(test)]
pub(crate) use monomial::GrevLexTerm;
pub(crate) use sparsepoly::SparsePolynomial;

#[cfg(test)]
mod tests;
