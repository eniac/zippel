//! Pure-engine bridge from zippel's `SparsePolynomial<F, M>` to
//! `ark_gb::compute_gb` and back.
//!
//! This module is a *compute engine*: it accepts zippel polynomials, runs
//! ark-gb's Buchberger, and returns zippel polynomials. There is no shared
//! state, no long-lived `Ring`, no parallel poly type. The
//! [`RingSnapshot`] built per call is stack-local and dropped on return.
//!
//! Two snapshot strategies are provided, one per supported zippel monomial
//! type:
//!
//! - [`compute_gb_grevlex`] for `SparsePolynomial<F, GrevLexTerm>`.
//!   PRefs are sorted ascending and assigned to ark-gb indices `0..nvars-1`,
//!   making PRef-greater ⇔ ark-rightmost ⇔ textbook-rightmost. This
//!   preserves GrevLex on round-trip.
//! - [`compute_gb_elim`] for `SparsePolynomial<F, ElimTerm>`. PRefs are
//!   partitioned into the *elim block* (those satisfying
//!   `ElimTerm::eliminate_var`) and the *keep block*, then interleaved:
//!   elim PRefs are assigned to **odd** indices, keep PRefs to **even**
//!   indices. This lines up with ark-gb's `OddElimTerm<W>` (whose elim
//!   predicate is `i % 2 == 1`), reproducing zippel's elim-block-then-grevlex
//!   ordering. Padding ghost variables are inserted when the two block
//!   sizes are unequal.
//!
//! # Caps (W = 8)
//!
//! - `nvars ≤ 63` (`max_vars::<W>() = W*8 - 1`).
//! - per-variable exponent ≤ 127 (`MAX_VAR_EXP = 0x7F`).
//!
//! Cap violations surface as [`EngineError`] inside [`build_snapshot_*`] /
//! [`sparsepoly_to_ark`] and panic at the engine entry point with PRef
//! context.
//!
//! # Reduced output
//!
//! `ark_gb::compute_gb` always returns a *reduced* basis, so
//! `GroebnerBasis::buchberger` now returns reduced bases unconditionally.
//! Existing zippel tests check ideal containment / S-pair closure, both of
//! which hold for reduced bases.

use crate::PRef;
use crate::analyses::groebner::monomial::Monomial as ZippelMonomial;
use crate::analyses::groebner::{ElimTerm, GrevLexTerm, SparsePolynomial};
use ark_ff::Field;
use ark_gb::Monomial as ArkMonomial;
use ark_gb::{
    GrevLexTerm as ArkGrevLexTerm, MonoTerm as ArkMonoTerm, OddElimTerm as ArkOddElimTerm,
};
use ark_gb::{Poly, Ring, compute_gb};
use share::Ctx;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// Width parameter for ark-gb's packed monomial layout. W=8 caps nvars at
/// 63 and per-variable exponents at 127.
pub const W: usize = 8;

/// Errors surfaced from the conversion boundary. Always indicate a workload
/// incompatibility with the chosen `W`, not a runtime error.
#[derive(Debug)]
pub enum EngineError {
    /// `nvars` exceeds `ark_gb::ring::max_vars::<W>() = W*8 - 1`.
    TooManyVars { nvars: usize, max: u32 },
    /// A variable's exponent in some monomial exceeds `0x7F`.
    ExponentOverflow {
        var: PRef,
        exponent: usize,
        max: u32,
    },
    /// `ark_gb::Ring::new` rejected the construction.
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
            EngineError::RingConstruction { nvars } => {
                write!(f, "arkgb_engine: ark_gb::Ring::new({}) failed", nvars)
            }
        }
    }
}

/// Stack-local mapping between zippel `PRef`s and ark-gb dense indices.
///
/// `idx_to_pref[i] = Some(p)` means ark-gb index `i` is bound to PRef `p`.
/// `idx_to_pref[i] = None` means index `i` is a *ghost* variable (used only
/// by the elim snapshot to pad an otherwise-empty parity slot, never appears
/// in any input or output exponent vector).
#[derive(Debug)]
pub struct RingSnapshot<F: Field + Copy + Send + Sync> {
    pub ring: Arc<Ring<F, W>>,
    pub idx_to_pref: Vec<Option<PRef>>,
    pub pref_to_idx: BTreeMap<PRef, u32>,
}

impl<F: Field + Copy + Send + Sync> RingSnapshot<F> {
    pub fn nvars(&self) -> u32 {
        self.idx_to_pref.len() as u32
    }
}

fn collect_prefs<F, M>(polys: &[SparsePolynomial<F, M>]) -> BTreeSet<PRef>
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

fn make_ring<F: Field + Copy + Send + Sync>(nvars: usize) -> Result<Arc<Ring<F, W>>, EngineError> {
    let max = ark_gb::ring::max_vars::<W>();
    if nvars as u32 > max {
        return Err(EngineError::TooManyVars { nvars, max });
    }
    let ring = Ring::<F, W>::new(nvars as u32).ok_or(EngineError::RingConstruction { nvars })?;
    Ok(Arc::new(ring))
}

/// Snapshot strategy for `GrevLexTerm`: union of PRefs sorted ascending,
/// assigned dense indices `0..nvars-1`. PRef-greater ⇔ ark-rightmost.
pub fn build_snapshot_grevlex<F: Field + Copy + Send + Sync>(
    polys: &[SparsePolynomial<F, GrevLexTerm>],
) -> Result<RingSnapshot<F>, EngineError> {
    let prefs = collect_prefs(polys);
    if prefs.is_empty() {
        return Err(EngineError::RingConstruction { nvars: 0 });
    }
    let idx_to_pref: Vec<Option<PRef>> = prefs.iter().cloned().map(Some).collect();
    let mut pref_to_idx = BTreeMap::new();
    for (i, p) in prefs.iter().enumerate() {
        pref_to_idx.insert(p.clone(), i as u32);
    }
    let ring = make_ring(idx_to_pref.len())?;
    Ok(RingSnapshot {
        ring,
        idx_to_pref,
        pref_to_idx,
    })
}

/// Snapshot strategy for `ElimTerm`: partition PRefs into *elim* (those
/// satisfying `ElimTerm::eliminate_var`) and *keep*; assign elim PRefs to
/// odd ark indices and keep PRefs to even ark indices, padding the
/// shorter block with ghost variables.
///
/// Within each block PRefs are sorted ascending so that PRef-greater ⇔
/// ark-rightmost-within-block, preserving the grevlex tiebreak after the
/// elim-block-sum prefix.
pub fn build_snapshot_elim<F: Field + Copy + Send + Sync>(
    polys: &[SparsePolynomial<F, ElimTerm>],
) -> Result<RingSnapshot<F>, EngineError> {
    let prefs = collect_prefs(polys);
    if prefs.is_empty() {
        return Err(EngineError::RingConstruction { nvars: 0 });
    }

    let mut elim: Vec<PRef> = Vec::new();
    let mut keep: Vec<PRef> = Vec::new();
    for p in prefs.into_iter() {
        if ElimTerm::eliminate_var(&p) {
            elim.push(p);
        } else {
            keep.push(p);
        }
    }

    // Interleave: even -> keep, odd -> elim. Total slots = 2 * max(|keep|, |elim|).
    let pairs = std::cmp::max(elim.len(), keep.len());
    let nvars = pairs * 2;
    let mut idx_to_pref: Vec<Option<PRef>> = vec![None; nvars];
    let mut pref_to_idx: BTreeMap<PRef, u32> = BTreeMap::new();
    for (i, p) in keep.into_iter().enumerate() {
        let idx = i * 2;
        pref_to_idx.insert(p.clone(), idx as u32);
        idx_to_pref[idx] = Some(p);
    }
    for (i, p) in elim.into_iter().enumerate() {
        let idx = i * 2 + 1;
        pref_to_idx.insert(p.clone(), idx as u32);
        idx_to_pref[idx] = Some(p);
    }
    let ring = make_ring(nvars)?;
    Ok(RingSnapshot {
        ring,
        idx_to_pref,
        pref_to_idx,
    })
}

/// Convert one zippel `SparsePolynomial<F, ZM>` to an ark-gb `Poly`.
/// Generic over the zippel/ark monomial pair; `ZM` and `AM` must agree on
/// the snapshot's variable indexing (see `build_snapshot_*`).
pub fn sparsepoly_to_ark<F, ZM, AM>(
    snap: &RingSnapshot<F>,
    p: &SparsePolynomial<F, ZM>,
) -> Result<Poly<F, AM, W>, EngineError>
where
    F: Field + Copy + Send + Sync,
    ZM: ZippelMonomial,
    AM: ArkMonomial<F, W> + From<ArkMonoTerm<W>>,
{
    let nvars = snap.nvars() as usize;
    let max_exp = ark_gb::ring::MAX_VAR_EXP;
    let mut terms: Vec<(F, AM)> = Vec::with_capacity(p.terms.len());

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
            // build_snapshot_* must have interned every PRef appearing in
            // the input. Missing => caller used a PRef not present in
            // any input poly, which is a bug.
            let idx = *snap.pref_to_idx.get(&var).expect(
                "arkgb_engine: PRef in poly term not present in snapshot \
                 (build_snapshot must be called on the same polys)",
            ) as usize;
            exps[idx] = power as u32;
        }
        let mt: ArkMonoTerm<W> = ArkMonoTerm::from_exponents(&snap.ring, &exps).ok_or(
            EngineError::ExponentOverflow {
                var: snap
                    .idx_to_pref
                    .iter()
                    .find_map(|p| p.clone())
                    .expect("snapshot must have at least one real PRef"),
                exponent: 0,
                max: max_exp,
            },
        )?;
        let am = AM::from(mt);
        terms.push((*coef, am));
    }
    Ok(Poly::from_terms(&snap.ring, terms))
}

/// Convert an ark-gb `Poly` back to zippel's `SparsePolynomial<F, ZM>`.
pub fn ark_to_sparsepoly<F, ZM, AM>(
    snap: &RingSnapshot<F>,
    p: &Poly<F, AM, W>,
) -> SparsePolynomial<F, ZM>
where
    F: Field + Copy + Send + Sync,
    ZM: ZippelMonomial + From<Vec<(PRef, usize)>>,
    AM: ArkMonomial<F, W>,
{
    let mut terms: Ctx<ZM, F> = Ctx::default();
    let nvars = snap.nvars() as usize;

    for (coef, mono) in p.iter() {
        if coef.is_zero() {
            continue;
        }
        let exps: Vec<u32> = AM::exponents(mono, &snap.ring);
        let mut pairs: Vec<(PRef, usize)> = Vec::new();
        for (i, e) in exps.iter().enumerate().take(nvars) {
            if *e == 0 {
                continue;
            }
            // A non-zero exponent on a ghost slot would mean ark-gb
            // produced a term over a phantom variable, which the elim
            // snapshot construction guarantees never happens (ghosts only
            // exist to pad even/odd parity, no input term references them,
            // so the ideal they generate has no ghost-bearing terms).
            let pref = snap.idx_to_pref[i]
                .clone()
                .expect("arkgb_engine: ark-gb produced exponent on ghost variable");
            pairs.push((pref, *e as usize));
        }
        let term: ZM = ZM::from(pairs);
        terms.insert(&term, &coef);
    }
    SparsePolynomial { terms }
}

/// Pure-constant ideal handler shared by the two `compute_gb_*` entry
/// points: `Some(unit)` if any input is a non-zero constant, else `None`.
fn unit_basis_if_constant<F, M>(
    polys: &[&SparsePolynomial<F, M>],
) -> Option<Vec<SparsePolynomial<F, M>>>
where
    F: Field + Copy,
    M: ZippelMonomial + From<Vec<(PRef, usize)>>,
{
    for p in polys {
        if p.terms.iter().next().is_some() {
            let mut terms: Ctx<M, F> = Ctx::default();
            let one_term = M::from(Vec::<(PRef, usize)>::new());
            let one_coef = F::one();
            terms.insert(&one_term, &one_coef);
            return Some(vec![SparsePolynomial { terms }]);
        }
    }
    None
}

/// Run `ark_gb::compute_gb` on a zippel polynomial slice and return the
/// (reduced) basis in zippel form. Generic over snapshot strategy and
/// monomial pair.
fn compute_gb_with<F, ZM, AM>(
    polys: &[SparsePolynomial<F, ZM>],
    build_snap: impl FnOnce(&[SparsePolynomial<F, ZM>]) -> Result<RingSnapshot<F>, EngineError>,
) -> Vec<SparsePolynomial<F, ZM>>
where
    F: Field + Copy + Send + Sync + 'static,
    ZM: ZippelMonomial + From<Vec<(PRef, usize)>>,
    AM: ArkMonomial<F, W> + From<ArkMonoTerm<W>> + 'static,
{
    let nonzero: Vec<&SparsePolynomial<F, ZM>> = polys.iter().filter(|p| !p.is_zero()).collect();
    if nonzero.is_empty() {
        return Vec::new();
    }

    let snap = match build_snap(polys) {
        Ok(s) => s,
        Err(EngineError::RingConstruction { nvars: 0 }) => {
            // Pure-constant ideal: ark-gb refuses nvars=0; caller wants
            // {1} (the unit ideal generator).
            return unit_basis_if_constant(&nonzero).unwrap_or_default();
        }
        Err(e) => panic!("{}", e),
    };

    let ark_inputs: Vec<Poly<F, AM, W>> = nonzero
        .iter()
        .map(|p| sparsepoly_to_ark(&snap, p).unwrap_or_else(|e| panic!("{}", e)))
        .collect();

    compute_gb(snap.ring.clone(), ark_inputs)
        .iter()
        .map(|p| ark_to_sparsepoly(&snap, p))
        .collect()
}

/// GB computation for `SparsePolynomial<F, GrevLexTerm>` via ark-gb's
/// `GrevLexTerm<W>`.
pub fn compute_gb_grevlex<F: Field + Copy + Send + Sync + 'static>(
    polys: &[SparsePolynomial<F, GrevLexTerm>],
) -> Vec<SparsePolynomial<F, GrevLexTerm>> {
    compute_gb_with::<F, GrevLexTerm, ArkGrevLexTerm<W>>(polys, build_snapshot_grevlex)
}

/// GB computation for `SparsePolynomial<F, ElimTerm>` via ark-gb's
/// `OddElimTerm<W>`. The snapshot lays out elim PRefs at odd indices and
/// keep PRefs at even indices so that ark-gb's `i % 2 == 1` elim predicate
/// matches `ElimTerm::eliminate_var`.
pub fn compute_gb_elim<F: Field + Copy + Send + Sync + 'static>(
    polys: &[SparsePolynomial<F, ElimTerm>],
) -> Vec<SparsePolynomial<F, ElimTerm>> {
    compute_gb_with::<F, ElimTerm, ArkOddElimTerm<W>>(polys, build_snapshot_elim)
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let coef = if c < 0 {
            -Fr::from((-c) as u64)
        } else {
            Fr::from(c as u64)
        };
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
        let p = add(
            add(term(3, vec![("a", 2)]), term(2, vec![("a", 1), ("b", 1)])),
            term(7, vec![]),
        );
        let snap = build_snapshot_grevlex(std::slice::from_ref(&p)).unwrap();
        let ark: Poly<Fr, ArkGrevLexTerm<W>, W> = sparsepoly_to_ark(&snap, &p).unwrap();
        let back: SparsePolynomial<Fr, GrevLexTerm> = ark_to_sparsepoly(&snap, &ark);
        assert_eq!(p, back);
    }

    #[test]
    fn order_tie_break_a2_vs_bc() {
        let p = add(term(1, vec![("a", 2)]), term(1, vec![("b", 1), ("c", 1)]));
        let snap = build_snapshot_grevlex(std::slice::from_ref(&p)).unwrap();
        let leading_zippel = p.terms.iter().next().map(|(t, _)| t.clone()).unwrap();
        assert_eq!(leading_zippel, mono(vec![("a", 2)]));

        let ark: Poly<Fr, ArkGrevLexTerm<W>, W> = sparsepoly_to_ark(&snap, &p).unwrap();
        let back: SparsePolynomial<Fr, GrevLexTerm> = ark_to_sparsepoly(&snap, &ark);
        let leading_back = back.terms.iter().next().map(|(t, _)| t.clone()).unwrap();
        assert_eq!(leading_back, mono(vec![("a", 2)]));
        assert_eq!(p, back);
    }

    #[test]
    fn exponent_127_ok() {
        let p = term(1, vec![("a", 127)]);
        let snap = build_snapshot_grevlex(std::slice::from_ref(&p)).unwrap();
        let _ark: Poly<Fr, ArkGrevLexTerm<W>, W> = sparsepoly_to_ark(&snap, &p).unwrap();
    }

    #[test]
    fn exponent_128_panics_via_engine_error() {
        let p = term(1, vec![("a", 128)]);
        let snap = build_snapshot_grevlex(std::slice::from_ref(&p)).unwrap();
        let res: Result<Poly<Fr, ArkGrevLexTerm<W>, W>, _> = sparsepoly_to_ark(&snap, &p);
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
        let mut p = term(0, vec![]);
        for i in 0..64 {
            let name = format!("v{}", i);
            let leaked: &'static str = Box::leak(name.into_boxed_str());
            p = p + term(1, vec![(leaked, 1)]);
        }
        let res = build_snapshot_grevlex(std::slice::from_ref(&p));
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
        let p1 = add(term(1, vec![("a", 1)]), term(1, vec![("b", 1)]));
        let p2 = add(term(1, vec![("a", 1)]), term(-1, vec![("b", 1)]));
        let gb = compute_gb_grevlex(&[p1, p2]);
        assert_eq!(gb.len(), 2);
        for p in &gb {
            assert_eq!(p.terms.len(), 1);
            let (_, c) = p.terms.iter().next().unwrap();
            assert!(c.is_one());
        }
    }
}
