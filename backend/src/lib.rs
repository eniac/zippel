#![feature(deref_patterns)]
#![feature(associated_type_defaults)]
pub mod config;
pub mod nothing;
pub mod op;
pub mod optimization;
pub mod poly_variant;
pub mod types;
pub mod values;
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
