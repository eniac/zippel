//! Pure-engine bridge from zippel's `SparsePolynomial<F, GrevLexTerm>` to
//! `ark_gb::compute_gb` and back.
//!
//! This module is a *compute engine*: it accepts zippel polynomials, runs
//! ark-gb's Buchberger, and returns zippel polynomials. There is no shared
//! state, no long-lived `Ring`, no parallel poly type. The
//! [`RingSnapshot`] built by [`compute_gb`] is stack-local to a single call
//! and dropped on return.
//!
//! # Order parity
//!
//! - Zippel `GrevLexTerm`'s `Ord` returns `Less` for the *leading* monomial
//!   (so `BTreeMap::first` yields it). PRef ordering: smallest PRef =
//!   textbook-leftmost variable; largest PRef = textbook-rightmost.
//! - ark-gb pins variables to dense indices `0..nvars-1`, with
//!   `byte_index_for_var(nvars, i) = i + (W*8 - 1) - nvars`. Index 0 is
//!   textbook-leftmost.
//! - [`build_snapshot`] sorts the union of PRefs ascending and assigns
//!   index 0 to the smallest PRef. This makes PRef-greater ⇔ ark-index-greater
//!   ⇔ textbook-rightmost in both conventions, preserving the GrevLex order
//!   on round-trip.
//!
//! # Caps
//!
//! At W=8: `nvars ≤ 63` and per-variable exponent ≤ 127. Both checks are
//! enforced inside [`sparsepoly_to_ark`] and surface as
//! [`EngineError`]; [`compute_gb`] panics on `Err` with PRef context, since
//! a cap violation indicates the workload is incompatible with the chosen
//! `W` — not a recoverable runtime condition.
//!
//! # Reduced output
//!
//! `ark_gb::compute_gb` always returns a *reduced* basis. Callers of
//! `GroebnerBasis::buchberger` that expected the unreduced output will
//! observe a behavioural change. The corresponding Zippel parity tests
//! check ideal equality / S-pair closure, both of which hold for reduced
//! bases.

use crate::PRef;
use crate::analyses::groebner::monomial::Monomial as ZippelMonomial;
use crate::analyses::groebner::{GrevLexTerm, SparsePolynomial};
use ark_ff::Field;
use ark_gb::{Poly, Ring, compute_gb};
use ark_gb::{GrevLexTerm as ArkGrevLexTerm, MonoTerm as ArkMonoTerm};
use ark_gb::Monomial as ArkMonomial;
use share::Ctx;
use std::collections::BTreeMap;
use std::sync::Arc;

/// Width parameter for ark-gb's packed monomial layout. W=8 caps nvars
/// at 63 and per-variable exponents at 127.
pub const W: usize = 8;

/// Errors surfaced from the conversion boundary. Always indicate a
/// workload incompatibility with the chosen `W`, not a runtime error.
#[derive(Debug)]
pub enum EngineError {
    /// `nvars` exceeds `ark_gb::ring::max_vars::<W>() = W*8 - 1`.
    TooManyVars { nvars: usize, max: u32 },
    /// A variable's exponent in some monomial exceeds `0x7F`.
    ExponentOverflow { var: PRef, exponent: usize, max: u32 },
    /// `ark_gb::Ring::new` rejected the construction for some other reason
    /// (currently only `nvars == 0`, which we filter elsewhere, but kept
    /// here for completeness).
    RingConstruction { nvars: usize },
}

impl std::fmt::Display for EngineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EngineError::TooManyVars { nvars, max } => write!(
                f,
                "arkgb_engine: nvars = {} exceeds max_vars::<W={}>() = {}; \
                 increase W or reduce variable count",
                nvars, W, max
            ),
            EngineError::ExponentOverflow { var, exponent, max } => write!(
                f,
                "arkgb_engine: exponent {} on variable {:?} exceeds \
                 ark_gb::MAX_VAR_EXP = {}; this monomial cannot be packed at W={}",
                exponent, var, max, W
            ),
            EngineError::RingConstruction { nvars } => write!(
                f,
                "arkgb_engine: ark_gb::Ring::new({}) failed",
                nvars
            ),
        }
    }
}

/// Stack-local mapping between zippel `PRef`s and ark-gb dense
/// `0..nvars-1` indices, plus the constructed `Ring`.
///
/// Built fresh per call to [`compute_gb`]; never cached or shared.
#[derive(Debug)]
pub struct RingSnapshot<F: Field + Copy + Send + Sync> {
    pub ring: Arc<Ring<F, W>>,
    /// `idx_to_pref[i]` is the PRef bound to ark-gb index `i`. Sorted
    /// ascending by `PRef` — this is what makes the GrevLex direction
    /// agree with zippel's convention (PRef-greater ⇔ ark-rightmost).
    pub idx_to_pref: Vec<PRef>,
    pub pref_to_idx: BTreeMap<PRef, u32>,
}

impl<F: Field + Copy + Send + Sync> RingSnapshot<F> {
    /// Number of variables this snapshot pins.
    pub fn nvars(&self) -> u32 {
        self.idx_to_pref.len() as u32
    }
}

/// Collect the union of PRefs across `polys`, sort ascending, and build
/// the ring + index tables.
pub fn build_snapshot<F: Field + Copy + Send + Sync>(
    polys: &[SparsePolynomial<F, GrevLexTerm>],
) -> Result<RingSnapshot<F>, EngineError> {
    let mut all_prefs: std::collections::BTreeSet<PRef> =
        std::collections::BTreeSet::new();
    for p in polys {
        for (term, _coef) in p.terms.iter() {
            for v in term.vars() {
                all_prefs.insert(v);
            }
        }
    }

    let nvars = all_prefs.len();
    let max = ark_gb::ring::max_vars::<W>();
    if nvars == 0 {
        return Err(EngineError::RingConstruction { nvars: 0 });
    }
    if nvars as u32 > max {
        return Err(EngineError::TooManyVars { nvars, max });
    }

    let idx_to_pref: Vec<PRef> = all_prefs.into_iter().collect();
    let mut pref_to_idx: BTreeMap<PRef, u32> = BTreeMap::new();
    for (i, p) in idx_to_pref.iter().enumerate() {
        pref_to_idx.insert(p.clone(), i as u32);
    }

    let ring = Ring::<F, W>::new(nvars as u32)
        .ok_or(EngineError::RingConstruction { nvars })?;

    Ok(RingSnapshot {
        ring: Arc::new(ring),
        idx_to_pref,
        pref_to_idx,
    })
}

/// Convert one zippel `SparsePolynomial<F, GrevLexTerm>` to an ark-gb
/// `Poly`, validating per-variable exponent caps. This is the **sole**
/// place where zippel-Ord (`Less = leading`) meets ark-gb-Ord
/// (`Greater = leading`); ark-gb's `from_terms` handles the sort.
pub fn sparsepoly_to_ark<F: Field + Copy + Send + Sync>(
    snap: &RingSnapshot<F>,
    p: &SparsePolynomial<F, GrevLexTerm>,
) -> Result<Poly<F, ArkGrevLexTerm<W>, W>, EngineError> {
    let nvars = snap.nvars() as usize;
    let mut terms: Vec<(F, ArkGrevLexTerm<W>)> = Vec::with_capacity(p.terms.len());
    let max_exp = ark_gb::ring::MAX_VAR_EXP;

    for (mono, coef) in p.terms.iter() {
        if coef.is_zero() {
            continue;
        }
        let mut exps = vec![0u32; nvars];
        for (var, power) in mono.vars().into_iter().zip(mono.powers().into_iter()) {
            if (power as u32) > max_exp {
                return Err(EngineError::ExponentOverflow {
                    var,
                    exponent: power,
                    max: max_exp,
                });
            }
            // Safe: build_snapshot interned every PRef in the input.
            let idx = snap.pref_to_idx[&var] as usize;
            exps[idx] = power as u32;
        }
        let mt: ArkMonoTerm<W> = ArkMonoTerm::from_exponents(&snap.ring, &exps).ok_or(
            // Reachable only if the cap loop above missed something
            // (e.g. total_deg overflow). Surface a generic message.
            EngineError::ExponentOverflow {
                var: snap.idx_to_pref[0].clone(),
                exponent: 0,
                max: max_exp,
            },
        )?;
        let am: ArkGrevLexTerm<W> = ArkGrevLexTerm::from(mt);
        terms.push((*coef, am));
    }

    Ok(Poly::from_terms(&snap.ring, terms))
}

/// Convert an ark-gb `Poly` back to zippel's `SparsePolynomial`. The
/// reverse direction does no validation — every ark-gb monomial maps
/// uniquely to a `Vec<(PRef, usize)>` via `idx_to_pref`.
pub fn ark_to_sparsepoly<F: Field + Copy + Send + Sync>(
    snap: &RingSnapshot<F>,
    p: &Poly<F, ArkGrevLexTerm<W>, W>,
) -> SparsePolynomial<F, GrevLexTerm> {
    let mut terms: Ctx<GrevLexTerm, F> = Ctx::default();
    let nvars = snap.nvars() as usize;

    for (coef, mono) in p.iter() {
        if coef.is_zero() {
            continue;
        }
        // `Monomial<F, W>::exponents` returns `Vec<u32>` of length nvars
        // for any ark-gb monomial type, including `GrevLexTerm`.
        let exps: Vec<u32> =
            <ArkGrevLexTerm<W> as ArkMonomial<F, W>>::exponents(mono, &snap.ring);
        let mut pairs: Vec<(PRef, usize)> = Vec::new();
        for (i, e) in exps.iter().enumerate().take(nvars) {
            if *e > 0 {
                pairs.push((snap.idx_to_pref[i].clone(), *e as usize));
            }
        }
        let term: GrevLexTerm = GrevLexTerm::from(pairs);
        terms.insert(&term, &coef);
    }

    SparsePolynomial { terms }
}

/// Run `ark_gb::compute_gb` on `polys` and return the (reduced) basis.
///
/// # Panics
///
/// Panics with a descriptive message via [`EngineError::Display`] if the
/// workload exceeds W=8 caps (nvars > 63 or any exponent > 127). These
/// are workload incompatibilities — caller must bump `W` or simplify the
/// problem.
///
/// Returns an empty `Vec` if `polys` is empty or contains only zero
/// polynomials (no variables to construct a `Ring` over).
pub fn compute_gb_polys<F: Field + Copy + Send + Sync + 'static>(
    polys: &[SparsePolynomial<F, GrevLexTerm>],
) -> Vec<SparsePolynomial<F, GrevLexTerm>> {
    let nonzero: Vec<&SparsePolynomial<F, GrevLexTerm>> =
        polys.iter().filter(|p| !p.is_zero()).collect();
    if nonzero.is_empty() {
        return Vec::new();
    }

    // build_snapshot rejects nvars=0; if it triggers (all polys are
    // pure constants), we degrade to "the basis is {1}" or "{}".
    let snap = match build_snapshot(polys) {
        Ok(s) => s,
        Err(EngineError::RingConstruction { nvars: 0 }) => {
            // Pure-constant ideal. Any non-zero constant generates the
            // unit ideal; the reduced GB is a single non-zero constant.
            // (Mirrors ark-gb's compute_gb behaviour after canonicalising.)
            for p in &nonzero {
                if p.terms.iter().next().is_some() {
                    let mut terms: Ctx<GrevLexTerm, F> = Ctx::default();
                    let one_term = GrevLexTerm::from(Vec::<(PRef, usize)>::new());
                    let one_coef = F::one();
                    terms.insert(&one_term, &one_coef);
                    return vec![SparsePolynomial { terms }];
                }
            }
            return Vec::new();
        }
        Err(e) => panic!("{}", e),
    };

    let ark_inputs: Vec<Poly<F, ArkGrevLexTerm<W>, W>> = nonzero
        .iter()
        .map(|p| {
            sparsepoly_to_ark(&snap, p).unwrap_or_else(|e| panic!("{}", e))
        })
        .collect();

    let ark_result = compute_gb(snap.ring.clone(), ark_inputs);

    ark_result
        .iter()
        .map(|p| ark_to_sparsepoly(&snap, p))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyses::groebner::monomial::GrevLexTerm;
    use crate::analyses::groebner::sparsepoly::SparsePolynomial;
    use ark_bls12_381::Fr;
    use ark_ff::One;
    use backend::ATyp;
    use lang::id::Vid;
    use lang::typ::{Distribution, Qualifier};
    use petgraph::graph::NodeIndex;

    fn pref_for(name: &str) -> PRef {
        PRef::from_var(
            Vid::new(name),
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        )
    }

    fn mono(parts: Vec<(&str, usize)>) -> GrevLexTerm {
        let pairs: Vec<(PRef, usize)> = parts
            .into_iter()
            .map(|(name, p)| (pref_for(name), p))
            .collect();
        GrevLexTerm::from(pairs)
    }

    fn term(c: i64, parts: Vec<(&str, usize)>) -> SparsePolynomial<Fr, GrevLexTerm> {
        let mut terms: Ctx<GrevLexTerm, Fr> = Ctx::default();
        let m = mono(parts);
        let coef = if c < 0 { -Fr::from((-c) as u64) } else { Fr::from(c as u64) };
        terms.insert(&m, &coef);
        SparsePolynomial { terms }
    }

    fn add(
        a: SparsePolynomial<Fr, GrevLexTerm>,
        b: SparsePolynomial<Fr, GrevLexTerm>,
    ) -> SparsePolynomial<Fr, GrevLexTerm> {
        a + b
    }

    #[test]
    fn round_trip_preserves_polynomial() {
        // p = 3*a^2 + 2*a*b + 7
        let p = add(
            add(term(3, vec![("a", 2)]), term(2, vec![("a", 1), ("b", 1)])),
            term(7, vec![]),
        );
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        let ark = sparsepoly_to_ark(&snap, &p).unwrap();
        let back = ark_to_sparsepoly(&snap, &ark);
        assert_eq!(p, back);
    }

    #[test]
    fn order_tie_break_a2_vs_bc() {
        // Same-degree GrevLex tie: a^2 vs b*c. Zippel says a^2 leads.
        // ark-gb must agree after round-trip.
        let p = add(
            term(1, vec![("a", 2)]),
            term(1, vec![("b", 1), ("c", 1)]),
        );
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        let leading_zippel = p.terms.iter().next().map(|(t, _)| t.clone()).unwrap();
        assert_eq!(leading_zippel, mono(vec![("a", 2)]));

        let ark = sparsepoly_to_ark(&snap, &p).unwrap();
        let back = ark_to_sparsepoly(&snap, &ark);
        let leading_back = back.terms.iter().next().map(|(t, _)| t.clone()).unwrap();
        assert_eq!(leading_back, mono(vec![("a", 2)]));
        assert_eq!(p, back);
    }

    #[test]
    fn exponent_127_ok() {
        let p = term(1, vec![("a", 127)]);
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        let _ark = sparsepoly_to_ark(&snap, &p).unwrap();
    }

    #[test]
    fn exponent_128_panics_via_engine_error() {
        let p = term(1, vec![("a", 128)]);
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        let res = sparsepoly_to_ark(&snap, &p);
        match res {
            Err(EngineError::ExponentOverflow { exponent, max, .. }) => {
                assert_eq!(exponent, 128);
                assert_eq!(max, 0x7F);
            }
            other => panic!("expected ExponentOverflow, got {:?}", other),
        }
    }

    #[test]
    fn nvars_64_panics() {
        // 64 distinct variables, all degree-1: nvars > max_vars::<8>() = 63.
        let mut p = term(0, vec![]); // start with zero
        for i in 0..64 {
            let name = format!("v{}", i);
            // Need static lifetime for our test helper — leak the strings.
            let leaked: &'static str = Box::leak(name.into_boxed_str());
            p = p + term(1, vec![(leaked, 1)]);
        }
        let res = build_snapshot(std::slice::from_ref(&p));
        match res {
            Err(EngineError::TooManyVars { nvars, max }) => {
                assert_eq!(nvars, 64);
                assert_eq!(max, 63);
            }
            other => panic!("expected TooManyVars, got {:?}", other),
        }
    }

    #[test]
    fn compute_gb_simple_linear() {
        // Two linear polys in {a, b}: a + b, a - b. GB should be {a, b}
        // (up to scalar), or equivalently the ideal contains both
        // generators of the variable ring.
        let p1 = add(term(1, vec![("a", 1)]), term(1, vec![("b", 1)]));
        let p2 = add(term(1, vec![("a", 1)]), term(-1, vec![("b", 1)]));
        let gb = compute_gb_polys(&[p1, p2]);
        // Reduced GB is monic, so we should see exactly {a, b} (modulo
        // scalar). Each generator is a single linear term.
        assert_eq!(gb.len(), 2);
        for p in &gb {
            assert_eq!(p.terms.len(), 1);
            let (_, c) = p.terms.iter().next().unwrap();
            assert!(c.is_one());
        }
    }
}
