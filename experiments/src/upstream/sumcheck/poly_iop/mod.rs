//! Vendored from EspressoSystems/hyperplonk `subroutines::poly_iop`.
//! We keep only `PolyIOP`, `errors`, `structs`, and `sum_check` —
//! the perm_check, prod_check, zero_check, pcs, and utils paths aren't
//! reachable from the sum-check entry point and are dropped.

use ark_ff::PrimeField;
use std::marker::PhantomData;

pub mod errors;
pub mod structs;
pub mod sum_check;

/// Marker struct for the PolyIOP family of protocols. The `SumCheck<F>`
/// trait is impl'd on this struct (in `sum_check::mod`), so callers
/// invoke `<PolyIOP<F> as SumCheck<F>>::prove(...)`.
#[derive(Clone, Debug, Default, Copy, PartialEq, Eq)]
pub struct PolyIOP<F: PrimeField> {
    #[doc(hidden)]
    phantom: PhantomData<F>,
}

pub use sum_check::SumCheck;
