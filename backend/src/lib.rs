//! Cryptographic backend for Zippel: the layer that turns the language's
//! source-level types into concrete `arkworks` field, curve, and pairing
//! elements and defines the typed IR operation set executed by `runtime`.
//!
//! Three things live here:
//!
//! - [`ArkConfig`] and its instances ([`ArkBls12_381`], [`ArkBn254`], …), which
//!   bundle a scalar field, one or two curve groups, and an optional pairing
//!   into a single type parameter `C` threaded through the whole compiler.
//! - [`ATyp`]/[`ABase`], the IR type level. Unlike the source-level
//!   `lang::typ::Typ`, `ATyp` splits polynomials into their physical encodings
//!   (`Uni`, `Mle`, `VPoly`) so layout is unambiguous at runtime.
//! - [`Op`]/[`GOp`], the hash-consed typed operations that make up a `graph`
//!   DAG, together with [`Value`], the runtime inhabitants those operations
//!   consume and produce.

#![feature(deref_patterns)]
#![feature(associated_type_defaults)]
/// The `ArkConfig` trait and its concrete curve/field instantiations.
pub mod config;
/// Stub field, curve, and pairing types used to fill unused `ArkConfig`
/// associated types on field-only or pairing-free configurations.
pub mod nothing;
/// The typed IR operation enum `Op<C, R>` and its hash-consing factory.
pub mod op;
/// Process-global counters recording which sumcheck optimization paths ran.
pub mod optimization;
/// Concrete polynomial encodings (dense/sparse univariate, multilinear,
/// sparse multivariate) and the arithmetic defined over them.
pub mod poly_variant;
/// The IR type level: `ATyp`/`ABase` and conversion from source-level `CTyp`.
pub mod types;
/// Runtime values `Value<C>` and the evaluation of each `Op` over them.
pub mod values;
/// Sum-of-products polynomial representation used by sumcheck-style protocols.
pub mod virtual_polynomial;

pub use config::{
    ArkBls12_381, ArkBn254, ArkConfig, ArkCurve25519, ArkEd25519, ArkField17, ArkField65537,
    ArkFieldN, ArkGroupOps, ArkMNT4_298, ArkPairingOps, ArkPallas, ArkScalarOps, ArkSecp256k1,
    ArkVesta,
};
pub use nothing::{NoCurve, NoField, NoPairing};
pub use op::{GOp, HasOpFactory, Op, Ref};
pub use optimization::{OptimizationStats, optimization_stats_snapshot, reset_optimization_stats};
pub use poly_variant::{PolyError, PolyVariant};
pub use types::{ABase, ATyp, binomial};
pub use values::{Value, value_to_bytes};
pub use virtual_polynomial::{SelectedEvalShape, VirtualPolynomial};

#[cfg(test)]
mod tests;
