//! ark-gb backend: interprets [`MonoOrder`](crate::frontend::MonoOrder) and
//! routes through the external ark-gb crate.
//!
//! Internal types (`SparsePolynomial`, `GroebnerBasis`, `GrevLexTerm`, etc.)
//! live in submodules and are an implementation detail of this backend.

#![allow(dead_code)]

pub mod adapter;
pub(crate) mod buchberger;
mod engine;
pub(crate) mod monomial;
pub(crate) mod sparsepoly;
pub(crate) mod tiered;

#[allow(unused_imports)]
pub(crate) use adapter::{
    TierLayoutGuard, ZippelTieredElimMono, assert_fits_in_ark_gb, build_tier_layout,
    collect_and_validate, compute_gb_pipeline, compute_reduced_gb_grevlex,
    compute_reduced_gb_with_elim, constant_only_basis, get_local_rank, LocalRankGuard,
};
#[allow(unused_imports)]
pub(crate) use buchberger::GroebnerBasis;
#[allow(unused_imports)]
pub(crate) use monomial::{ElimMono, ElimStrategy, GrevLexTerm, Monomial};
#[allow(unused_imports)]
pub(crate) use sparsepoly::SparsePolynomial;
#[allow(unused_imports)]
pub(crate) use tiered::{TieredElimMono, TieredElimStrategy};

pub use engine::ArkGb;

#[cfg(test)]
mod tests;
