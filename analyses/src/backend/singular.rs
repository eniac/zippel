//! Singular backend stub — not yet implemented.
//!
//! When implemented, this will translate [`MonoOrder`](crate::frontend::MonoOrder)
//! into a Singular ring declaration and call libSingular for GB computation.
//! Singular supports the full `MonoOrder` surface (including `DegLex`, weighted
//! orderings, and arbitrary block combinations) that ark-gb does not.

use std::marker::PhantomData;

use backend::ArkConfig;

use crate::frontend::{MonoOrder, Polynomial, UnsupportedMonoOrder};
use super::{GbBasis, GbBackend};

pub struct Singular<C: ArkConfig> {
    _phantom: PhantomData<C>,
}

impl<C: ArkConfig + backend::op::HasOpFactory> GbBackend<C> for Singular<C> {
    fn compute_gb(
        &self,
        _ideal: Vec<Polynomial<C::F>>,
        _order: &MonoOrder,
        _w: usize,
    ) -> Result<GbBasis<C::F>, UnsupportedMonoOrder> {
        unimplemented!("Singular backend is not yet implemented");
    }

    fn reduce(&self, _p: Polynomial<C::F>, _basis: &GbBasis<C::F>) -> Polynomial<C::F> {
        unimplemented!("Singular backend is not yet implemented");
    }
}
