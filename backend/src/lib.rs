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
/// The `Backend` trait, keys, and the backends Zippel ships.
pub mod backends;
/// The IR: typed operations and their types.
pub mod ir;
/// Polynomials: concrete encodings and virtual sums of products.
pub mod poly;
/// Runtime values `Value<C>` and the evaluation of each `Op` over them.
pub mod value;

pub use algebra::{DivisionByZero, Field, Group, Pairing};
pub use backends::nothing::{NoGroup, NoPairing};
pub use backends::{
    ArkBls12_381, ArkBn254, ArkCurve25519, ArkEd25519, ArkFrRistretto, ArkMNT4_298, ArkPallas,
    ArkSecp256k1, ArkVesta, Backend, DalekRistretto, G1Affine, G1Points, G2Affine, G2Points, GT,
    PastaPallas,
};
pub use ir::op::{GOp, Op, OpExclusion, Ref};
pub use ir::types::{ABase, ATyp, binomial};
pub use poly::variant::{PolyError, PolyVariant};
pub use poly::virtual_polynomial::{SelectedEvalShape, VirtualPolynomial};
pub use value::shared::Shared;
pub use value::{Value, value_to_bytes};

#[cfg(test)]
mod tests;
