//! Coefficient layer: any arkworks field.
//!
//! The upstream `rustgb` had a `struct Field { p: u32, barrett_mu: u64 }`
//! that wrapped a Barrett-reducing Z/p. In `ark-gb` we generalize over
//! `F: ark_ff::Field` (or `ark_ff::PrimeField` only where required).

pub use ark_ff::Field;

/// Coefficient type alias. Kept around so the rest of the crate can refer
/// to `Coeff<F>` symmetrically with the upstream `Coeff` type alias.
pub type Coeff<F> = F;
