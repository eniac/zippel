//! Adapter monomial: zippel `Monomial` impl over ark-gb's `GrevLexTerm<W>`.
//!
//! See [`super`] module docs for the design overview.

use crate::analyses::groebner::Monomial as ZippelMonomial;
use crate::pref::PRef;
use ark_ff::Field;
use ark_gb::monomial::GrevLexTerm;
use core::cmp::Ordering;
use core::ops::{Div, Mul, MulAssign};
use share::Ctx;
use std::fmt;
use std::marker::PhantomData;

use super::W;
use super::ring::VarRing;

/// A monomial newtype that implements zippel's [`ZippelMonomial`] trait by
/// delegating to ark-gb's [`GrevLexTerm<W>`].
///
/// Carries a [`VarRing`] handle so that `vars()` / `powers()` can map the
/// dense u32 indices back to [`PRef`]s without touching ark-gb internals.
#[derive(Clone, Debug)]
pub struct AdapterMonomial<F: Field + Copy + Send + Sync> {
    pub(crate) vr: VarRing<F>,
    pub(crate) inner: GrevLexTerm<W>,
    _marker: PhantomData<F>,
}

impl<F: Field + Copy + Send + Sync> AdapterMonomial<F> {
    /// Wrap an ark-gb `GrevLexTerm<W>` together with the `VarRing` it was
    /// interned against.
    pub fn new(_vr: VarRing<F>, _inner: GrevLexTerm<W>) -> Self {
        unimplemented!("AdapterMonomial::new — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> Default for AdapterMonomial<F> {
    fn default() -> Self {
        unimplemented!("AdapterMonomial::default — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> PartialEq for AdapterMonomial<F> {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!("AdapterMonomial::eq — implemented in P2")
    }
}
impl<F: Field + Copy + Send + Sync> Eq for AdapterMonomial<F> {}

impl<F: Field + Copy + Send + Sync> PartialOrd for AdapterMonomial<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field + Copy + Send + Sync> Ord for AdapterMonomial<F> {
    fn cmp(&self, _other: &Self) -> Ordering {
        unimplemented!("AdapterMonomial::cmp — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> fmt::Display for AdapterMonomial<F> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!("AdapterMonomial::fmt — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> MulAssign for AdapterMonomial<F> {
    fn mul_assign(&mut self, _other: Self) {
        unimplemented!("AdapterMonomial::mul_assign — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> Mul for AdapterMonomial<F> {
    type Output = Self;
    fn mul(self, _other: Self) -> Self {
        unimplemented!("AdapterMonomial::mul — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> Div for AdapterMonomial<F> {
    type Output = Option<Self>;
    fn div(self, _other: Self) -> Option<Self> {
        unimplemented!("AdapterMonomial::div — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> From<Vec<(PRef, usize)>> for AdapterMonomial<F> {
    fn from(_vars: Vec<(PRef, usize)>) -> Self {
        unimplemented!("AdapterMonomial::from(Vec<(PRef, usize)>) — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> ZippelMonomial for AdapterMonomial<F> {
    fn vars(&self) -> Vec<PRef> {
        unimplemented!("AdapterMonomial::vars — implemented in P2")
    }

    fn powers(&self) -> Vec<usize> {
        unimplemented!("AdapterMonomial::powers — implemented in P2")
    }

    fn evaluate<G: ark_ff::Field>(&self, _p: &Ctx<PRef, G>) -> G {
        unimplemented!("AdapterMonomial::evaluate — implemented in P2")
    }

    fn is_divided(&self, _other: &Self) -> bool {
        unimplemented!("AdapterMonomial::is_divided — implemented in P2")
    }

    fn lcm(&self, _other: &Self) -> Self {
        unimplemented!("AdapterMonomial::lcm — implemented in P2")
    }

    fn gcd(&self, _other: &Self) -> Self {
        unimplemented!("AdapterMonomial::gcd — implemented in P2")
    }
}
