//! Adapter polynomial: dual-form bridge between zippel's `SparsePolynomial`
//! API and ark-gb's `Poly<F, GrevLexTerm<W>, W>`.
//!
//! See [`super`] module docs for the dual-form rationale.

use crate::pref::PRef;
use ark_ff::Field;
use ark_gb::monomial::GrevLexTerm;
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;
use std::sync::Arc;

use super::W;
use super::monomial::AdapterMonomial;
use super::ring::VarRing;

/// Polynomial in either lazy or materialised form.
///
/// ## Lazy form
///
/// Holds an exponent-list representation `Vec<(F, Vec<(u32, u32)>)>` keyed
/// against a [`VarRing`] that is **not** yet frozen. All construction-phase
/// arithmetic (Add/Sub/Mul/`flat_map_vars`/`pow`) operates here, so new
/// variables can still be introduced.
///
/// ## Materialised form
///
/// Holds an actual `ark_gb::Poly<F, GrevLexTerm<W>, W>` over a frozen
/// `Arc<Ring<F, W>>`. Required before calling `compute_gb` or any reducer
/// path. Once materialised, the underlying `VarRing`'s nvars is locked.
#[derive(Clone, Debug)]
pub enum AdapterPoly<F: Field + Copy + Send + Sync> {
    /// Construction-time form. Each term is `(coeff, [(var_idx, exp), ...])`.
    Lazy {
        vr: VarRing<F>,
        terms: Vec<(F, Vec<(u32, u32)>)>,
    },
    /// Frozen, ark-gb-native form.
    Materialised {
        vr: VarRing<F>,
        ring: Arc<Ring<F, W>>,
        poly: Poly<F, GrevLexTerm<W>, W>,
    },
}

impl<F: Field + Copy + Send + Sync> AdapterPoly<F> {
    /// Construct an empty (zero) polynomial in lazy form.
    pub fn zero(vr: VarRing<F>) -> Self {
        Self::Lazy {
            vr,
            terms: Vec::new(),
        }
    }

    /// Build a polynomial from `(F, AdapterMonomial)` pairs in lazy form.
    pub fn from_terms(_vr: VarRing<F>, _terms: Vec<(F, AdapterMonomial<F>)>) -> Self {
        unimplemented!("AdapterPoly::from_terms — implemented in P2")
    }

    /// Force the polynomial into materialised form. Idempotent.
    ///
    /// **Side effect**: freezes the underlying [`VarRing`]. Subsequent
    /// `vr.intern(new_pref)` calls will panic.
    pub fn materialise(self) -> Self {
        unimplemented!("AdapterPoly::materialise — implemented in P2")
    }

    /// `true` if the polynomial is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Lazy { terms, .. } => terms.is_empty(),
            Self::Materialised { poly, .. } => poly.is_zero(),
        }
    }

    /// Leading term under GrevLex. Cheap in both forms (lazy form sorts the
    /// exponent list by inline GrevLex compare, materialised form delegates
    /// to `Poly::leading`).
    pub fn leading_term(&self) -> Option<(F, AdapterMonomial<F>)> {
        unimplemented!("AdapterPoly::leading_term — implemented in P2")
    }

    /// Iterate over `(coeff, monomial)` pairs in leading-first order.
    pub fn iter_terms(&self) -> Vec<(F, AdapterMonomial<F>)> {
        unimplemented!("AdapterPoly::iter_terms — implemented in P2")
    }

    /// `flat_map_vars`: replace each variable with another polynomial.
    ///
    /// **Must be called before** any [`Self::materialise`] step, since the
    /// substitution may introduce previously-unseen `PRef`s.
    pub fn flat_map_vars<G>(self, _f: G) -> Self
    where
        G: Fn(&PRef) -> Self,
    {
        unimplemented!("AdapterPoly::flat_map_vars — implemented in P2")
    }
}

// Arithmetic stubs — the full set (Add/Sub/Mul/Neg over both owned and
// reference forms) lands in P2 alongside the parity tests. Putting them
// behind `unimplemented!()` keeps the feature-flag wiring honest while
// preventing accidental use before P2 lands.

impl<F: Field + Copy + Send + Sync> std::ops::Add for AdapterPoly<F> {
    type Output = Self;
    fn add(self, _other: Self) -> Self {
        unimplemented!("AdapterPoly::add — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> std::ops::Sub for AdapterPoly<F> {
    type Output = Self;
    fn sub(self, _other: Self) -> Self {
        unimplemented!("AdapterPoly::sub — implemented in P2")
    }
}

impl<F: Field + Copy + Send + Sync> std::ops::Mul for AdapterPoly<F> {
    type Output = Self;
    fn mul(self, _other: Self) -> Self {
        unimplemented!("AdapterPoly::mul — implemented in P2")
    }
}
