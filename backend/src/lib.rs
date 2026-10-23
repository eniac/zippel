//! Cryptographic backend for Zippel: the layer that turns the language's
//! source-level types into concrete field, group, and pairing elements and
//! defines the typed IR operation set executed by `runtime`.
//!
//! Three things live here:
//!
//! - [`Backend`] and its instances ([`ArkBls12_381`], [`ArkBn254`], …), which
//!   bundle a scalar [`Field`], one or two [`Group`]s, and an optional
//!   [`Pairing`] into a single type parameter `C` threaded through the whole
//!   compiler. The shipped backends are arkworks'; any library implementing
//!   the three traits can be one.
//! - [`ATyp`]/[`ABase`], the IR type level. Unlike the source-level
//!   `lang::typ::Typ`, `ATyp` splits polynomials into their physical encodings
//!   (`Uni`, `Mle`, `VPoly`) so layout is unambiguous at runtime.
//! - [`Op`]/[`GOp`], the hash-consed typed operations that make up a `graph`
//!   DAG, together with [`Value`], the runtime inhabitants those operations
//!   consume and produce.

#![feature(deref_patterns)]
/// The `Field`, `Group` and `Pairing` traits a backend implements.
pub mod algebra;
/// The arkworks implementation of the algebra traits.
pub mod ark;
/// The `Backend` trait and its concrete curve/field instantiations.
pub mod config;
/// A conformance check for a backend: the laws and contracts Zippel relies on.
pub mod conformance;
/// The zkcrypto `ff`/`group` implementation of the algebra traits, and the
/// Ristretto and Pallas backends built from it.
pub mod ff_group;
/// Placeholder group and pairing filling the slots of field-only or
/// pairing-free backends.
pub mod nothing;
/// The typed IR operation enum `Op<C, R>` and its hash-consing factory.
pub mod op;
/// Process-global counters recording which sumcheck optimization paths ran.
pub mod optimization;
/// Concrete polynomial encodings (dense/sparse univariate, multilinear,
/// sparse multivariate) and the arithmetic defined over them.
pub mod poly_variant;
/// Vectors that share their storage: O(1) clones and slices, copy-on-write.
pub mod shared;
/// The IR type level: `ATyp`/`ABase` and conversion from source-level `CTyp`.
pub mod types;
/// Runtime values `Value<C>` and the evaluation of each `Op` over them.
pub mod values;
/// Sum-of-products polynomial representation used by sumcheck-style protocols.
pub mod virtual_polynomial;

pub use algebra::{DivisionByZero, Field, Group, Pairing};
pub use config::{
    ArkBls12_381, ArkBn254, ArkCurve25519, ArkEd25519, ArkField17, ArkField65537, ArkFieldN,
    ArkMNT4_298, ArkPallas, ArkSecp256k1, ArkVesta, Backend, G1Affine, G2Affine, GT,
};
pub use ff_group::{DalekRistretto, PastaPallas};
pub use nothing::{NoGroup, NoPairing};
pub use op::{GOp, Op, OpExclusion, Ref};
pub use optimization::{OptimizationStats, optimization_stats_snapshot, reset_optimization_stats};
pub use poly_variant::{PolyError, PolyVariant};
pub use shared::Shared;
pub use types::{ABase, ATyp, binomial};
pub use values::{PreparedG2Vec, Value, value_to_bytes};
pub use virtual_polynomial::{SelectedEvalShape, VirtualPolynomial};

#[cfg(test)]
mod tests;
