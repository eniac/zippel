//! Adapter Groebner basis: routes Buchberger to ark-gb's `compute_gb`.
//!
//! See [`super`] module docs for the design overview.

use ark_ff::Field;

use super::poly::AdapterPoly;
use super::ring::VarRing;

/// Groebner basis driver. Holds the input generators in lazy form until
/// [`Self::buchberger`] is called, at which point the polynomials are
/// materialised, fed to ark-gb's `compute_gb`, and the result is wrapped
/// back into [`AdapterPoly`]s.
#[derive(Clone, Debug)]
pub struct AdapterGroebnerBasis<F: Field + Copy + Send + Sync> {
    pub(crate) vr: VarRing<F>,
    pub(crate) generators: Vec<AdapterPoly<F>>,
}

impl<F: Field + Copy + Send + Sync> AdapterGroebnerBasis<F> {
    /// Create an empty basis with the given variable ring.
    pub fn empty(vr: VarRing<F>) -> Self {
        Self {
            vr,
            generators: Vec::new(),
        }
    }

    /// Add a generator (lazy form OK — materialisation happens in `buchberger`).
    pub fn push(&mut self, _p: AdapterPoly<F>) {
        unimplemented!("AdapterGroebnerBasis::push — implemented in P2")
    }

    /// Run Buchberger via `ark_gb::compute_gb`. Returns the reduced
    /// Groebner basis as fresh `AdapterPoly`s sharing this basis's `VarRing`.
    pub fn buchberger(&mut self) {
        unimplemented!("AdapterGroebnerBasis::buchberger — implemented in P2")
    }

    /// Buchberger followed by inter-reduction (idempotent on a reduced basis).
    pub fn buchberger_and_reduce(&mut self) {
        unimplemented!("AdapterGroebnerBasis::buchberger_and_reduce — implemented in P2")
    }

    /// Reduce a polynomial against the current basis. Materialises both
    /// sides of the operation.
    pub fn reduce(&self, _p: AdapterPoly<F>) -> AdapterPoly<F> {
        unimplemented!("AdapterGroebnerBasis::reduce — implemented in P2")
    }
}
