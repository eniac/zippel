#![feature(box_patterns)]
#![feature(associated_type_defaults)]
pub mod config;
pub mod poly_variant;
pub mod values;
pub mod types;
pub mod nothing;

pub use nothing::{NoField, NoCurve, NoPairing};
pub use values::{Value, value_to_bytes};
pub use types::{ABase, ATyp};
pub use poly_variant::{PolyVariant, PolyError};
pub use config::{
    ArkScalarOps,
    ArkGroupOps,
    ArkPairingOps,
    ArkConfig,
    ArkBls12_381,
    ArkBn254,
    ArkMNT4_298,
    ArkCurve25519,
    ArkSecp256k1,
    ArkPallas,
    ArkVesta,
    ArkEd25519,
    ArkFieldN,
    ArkField17,
    ArkField65537
};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod poly_variant_tests;
