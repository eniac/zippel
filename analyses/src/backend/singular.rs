//! Singular backend stub — not yet implemented.
//!
//! When implemented, this will translate [`MonoOrder`](crate::frontend::MonoOrder)
//! into a Singular ring declaration and call libSingular for GB computation.
//! Singular supports the full `MonoOrder` surface (including `DegLex`, weighted
//! orderings, and arbitrary block combinations) that ark-gb does not.

use std::marker::PhantomData;

use ark_ff::Field;

use super::{GbBackend, GbBasis};
use crate::frontend::{MonoOrder, Polynomial, UnsupportedMonoOrder};

pub struct Singular<F: Field> {
    _phantom: PhantomData<F>,
}

impl<F: Field> GbBackend<F> for Singular<F> {
    fn compute_gb(
        &self,
        _ideal: Vec<Polynomial<F>>,
        _order: &MonoOrder,
    ) -> Result<GbBasis<F>, UnsupportedMonoOrder> {
        unimplemented!("Singular backend is not yet implemented");
    }

    fn reduce(&self, _p: Polynomial<F>, _basis: &GbBasis<F>) -> Polynomial<F> {
        unimplemented!("Singular backend is not yet implemented");
    }
}
