//! Compute engine: zippel `SparsePolynomial<F, T>` ↔ `ark_gb::Poly<F, M, W>`.
//!
//! Each `Monomial` impl picks one of the two flat, monomorphic engine
//! functions:
//!
//! - [`grevlex::compute_gb_grevlex`] for `SparsePolynomial<F, GrevLexTerm>`.
//!   PRefs are sorted ascending and assigned ark-gb indices `0..n-1`.
//! - [`elim::compute_gb_elim`] for `SparsePolynomial<F, ElimTerm>`. PRefs
//!   are partitioned by the *PRef-attribute* predicate
//!   `ElimTerm::eliminate_var` into elim/keep blocks; elim PRefs are placed
//!   at **odd** indices, keep PRefs at **even**, with ghost padding.
//!   This is the only viable translation from zippel's PRef-attribute elim
//!   ordering to ark-gb's positional `OddElimTerm<W>`.
//!
//! Both engines use [`RingSnapshot`] to carry the per-call PRef slot map.
//! Conversions are concrete per engine; this module hosts only the shared
//! state (snapshot, error type, caps, helpers).

use crate::PRef;
use crate::analyses::groebner::SparsePolynomial;
use crate::analyses::groebner::monomial::Monomial as ZippelMonomial;
use ark_ff::Field;
use ark_gb::Ring;
use std::collections::BTreeSet;
use std::sync::Arc;

pub mod elim;
pub mod grevlex;

/// Width parameter for ark-gb's packed monomial layout. `W = 8` caps
/// `nvars` at 63 and per-variable exponents at 127.
pub const W: usize = 8;

/// Errors surfaced from the conversion boundary. Always indicate a
/// workload incompatibility with the chosen `W`, not a runtime error.
#[derive(Debug)]
pub enum EngineError {
    /// `nvars` exceeds `ark_gb::ring::max_vars::<W>() = W*8 - 1`.
    TooManyVars { nvars: usize, max: u32 },
    /// A variable's exponent in some monomial exceeds `ark_gb::MAX_VAR_EXP`.
    ExponentOverflow {
        var: PRef,
        exponent: usize,
        max: u32,
    },
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineError::TooManyVars { nvars, max } => write!(
                f,
                "engine: nvars = {} exceeds max_vars::<W={}>() = {}; \
                 increase W or reduce variable count",
                nvars, W, max
            ),
            EngineError::ExponentOverflow { var, exponent, max } => write!(
                f,
                "engine: exponent {} on variable {:?} exceeds \
                 ark_gb::MAX_VAR_EXP = {}; cannot pack at W = {}",
                exponent, var, max, W
            ),
        }
    }
}

/// Stack-local mapping between zippel `PRef`s and ark-gb dense indices.
///
/// `slots[i] = Some(p)` means ark-gb index `i` is bound to PRef `p`.
/// `slots[i] = None` is a *ghost* slot — used by the elim snapshot to pad
/// an empty parity slot. Ghosts never appear in any input or output
/// exponent vector.
///
/// One canonical bijection. Forward lookups (PRef → idx) are derived
/// inside the conversion hot loop via the per-engine `pref_to_idx`
/// helper (built lazily once per call); reverse lookups read `slots`
/// directly.
#[derive(Debug)]
pub struct RingSnapshot<F: Field + Copy + Send + Sync> {
    pub ring: Arc<Ring<F, W>>,
    pub slots: Vec<Option<PRef>>,
}

impl<F: Field + Copy + Send + Sync> RingSnapshot<F> {
    pub fn nvars(&self) -> u32 {
        self.slots.len() as u32
    }
}

/// Collect the union of PRefs appearing in any term of any polynomial.
pub(super) fn collect_prefs<F, M>(polys: &[SparsePolynomial<F, M>]) -> BTreeSet<PRef>
where
    F: Field,
    M: ZippelMonomial,
{
    let mut all = BTreeSet::new();
    for p in polys {
        for (term, _coef) in p.terms.iter() {
            for v in term.vars() {
                all.insert(v);
            }
        }
    }
    all
}

/// Allocate an ark-gb `Ring` of `nvars` variables. Surfaces `TooManyVars`
/// for any `nvars` exceeding the W-derived cap.
pub(super) fn make_ring<F: Field + Copy + Send + Sync>(
    nvars: usize,
) -> Result<Arc<Ring<F, W>>, EngineError> {
    let max = ark_gb::ring::max_vars::<W>();
    if nvars as u32 > max {
        return Err(EngineError::TooManyVars { nvars, max });
    }
    // ark-gb's `Ring::new(0)` returns `None`; the constant-ideal case is
    // handled by `unit_basis_if_constant` *before* this is called, so any
    // failure here would be a programming error.
    let ring = Ring::<F, W>::new(nvars as u32).expect("ark-gb Ring::new failed for non-zero nvars");
    Ok(Arc::new(ring))
}

/// If `polys` contains any non-zero polynomial whose only term is a
/// constant, the ideal contains 1 — the canonical reduced GB is `[1]`.
/// Returns `None` when no such poly is present (caller proceeds with the
/// usual GB computation).
///
/// Used as a direct branch *before* snapshot construction whenever the
/// input has zero variables, replacing the previous control-flow-via-
/// `EngineError::RingConstruction { nvars: 0 }` sentinel.
pub(super) fn unit_basis_if_constant<F, M>(
    polys: &[&SparsePolynomial<F, M>],
) -> Option<Vec<SparsePolynomial<F, M>>>
where
    F: Field + Copy,
    M: ZippelMonomial,
{
    use share::Ctx;
    for p in polys {
        if p.terms.iter().next().is_some() {
            let mut terms: Ctx<M, F> = Ctx::default();
            let one_term = M::default(); // empty monomial == 1
            let one_coef = F::one();
            terms.insert(&one_term, &one_coef);
            return Some(vec![SparsePolynomial { terms }]);
        }
    }
    None
}
