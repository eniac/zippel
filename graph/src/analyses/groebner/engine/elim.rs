//! Monomorphic elim engine: zippel `ElimTerm` ↔ ark-gb `OddElimTerm<W>`.
//!
//! Zippel's `ElimTerm::eliminate_var` is a *PRef-attribute* predicate
//! (`Qualifier::Local`, or `Private + Uniform`). ark-gb's `OddElimTerm` is
//! *positional* (`i % 2 == 1`). The only viable translation places
//! attribute-elim PRefs at odd ark indices and keep PRefs at even, with
//! ghost padding when the two block sizes are unequal. Within each block,
//! PRefs are sorted ascending so PRef-greater ⇔ ark-rightmost-within-block,
//! preserving the grevlex tiebreak after the elim-block-sum prefix.

use super::{EngineError, RingSnapshot, W, collect_prefs, make_ring, unit_basis_if_constant};
use crate::PRef;
use crate::analyses::groebner::{ElimTerm, SparsePolynomial};
use ark_ff::Field;
use ark_gb::{MonoTerm as ArkMonoTerm, OddElimTerm as ArkOddElimTerm, Poly, compute_gb};
use share::Ctx;
use std::collections::BTreeMap;

/// Build the partitioned snapshot: PRef-attribute-elim PRefs at odd ark
/// indices, keep PRefs at even. Ghost-pad the shorter block.
fn build_snapshot<F: Field + Copy + Send + Sync>(
    polys: &[SparsePolynomial<F, ElimTerm>],
) -> Result<RingSnapshot<F>, EngineError> {
    let prefs = collect_prefs(polys);

    let mut elim: Vec<PRef> = Vec::new();
    let mut keep: Vec<PRef> = Vec::new();
    for p in prefs.into_iter() {
        if ElimTerm::eliminate_var(&p) {
            elim.push(p);
        } else {
            keep.push(p);
        }
    }

    // Total slots = 2 * max(|elim|, |keep|): each block fills its own
    // parity, the shorter one gets `None` ghost padding.
    let pairs = std::cmp::max(elim.len(), keep.len());
    let nvars = pairs * 2;
    let mut slots: Vec<Option<PRef>> = vec![None; nvars];
    for (i, p) in keep.into_iter().enumerate() {
        slots[i * 2] = Some(p);
    }
    for (i, p) in elim.into_iter().enumerate() {
        slots[i * 2 + 1] = Some(p);
    }
    let ring = make_ring(nvars)?;
    Ok(RingSnapshot { ring, slots })
}

/// Build the forward (PRef → ark-index) lookup once per call.
fn pref_to_idx<F: Field + Copy + Send + Sync>(snap: &RingSnapshot<F>) -> BTreeMap<PRef, u32> {
    let mut map = BTreeMap::new();
    for (i, slot) in snap.slots.iter().enumerate() {
        if let Some(p) = slot {
            map.insert(p.clone(), i as u32);
        }
    }
    map
}

/// Direct zippel `ElimTerm` → ark `OddElimTerm<W>` packing in a single
/// pass over `mono.iter()` (no `Vec<(PRef, usize)>` intermediate).
fn poly_to_ark<F: Field + Copy + Send + Sync>(
    snap: &RingSnapshot<F>,
    fwd: &BTreeMap<PRef, u32>,
    p: &SparsePolynomial<F, ElimTerm>,
) -> Result<Poly<F, ArkOddElimTerm<W>, W>, EngineError> {
    let nvars = snap.nvars() as usize;
    let max_exp = ark_gb::ring::MAX_VAR_EXP;
    let mut terms: Vec<(F, ArkOddElimTerm<W>)> = Vec::with_capacity(p.terms.len());
    let mut exps = vec![0u32; nvars];

    for (mono, coef) in p.terms.iter() {
        if coef.is_zero() {
            continue;
        }
        for slot in exps.iter_mut() {
            *slot = 0;
        }
        for (var, power) in mono.iter() {
            if (*power as u32) > max_exp {
                return Err(EngineError::ExponentOverflow {
                    var: var.clone(),
                    exponent: *power,
                    max: max_exp,
                });
            }
            let idx = *fwd
                .get(var)
                .expect("engine: PRef in poly term not present in snapshot")
                as usize;
            exps[idx] = *power as u32;
        }
        let mt = ArkMonoTerm::<W>::from_exponents(&snap.ring, &exps).expect(
            "engine: ark MonoTerm packing failed after caps verified \
             (this is a bug in the engine, not in the workload)",
        );
        terms.push((*coef, ArkOddElimTerm::<W>::from(mt)));
    }
    Ok(Poly::from_terms(&snap.ring, terms))
}

/// Direct ark `OddElimTerm<W>` → zippel `ElimTerm` unpack: write each
/// non-zero exponent straight into a fresh `Ctx<PRef, usize>` (no
/// `Vec<(PRef, usize)>` intermediate). Asserts ark-gb never produces a
/// term over a ghost slot — the snapshot construction guarantees this.
fn ark_to_poly<F: Field + Copy + Send + Sync>(
    snap: &RingSnapshot<F>,
    p: &Poly<F, ArkOddElimTerm<W>, W>,
) -> SparsePolynomial<F, ElimTerm> {
    use ark_gb::Monomial as ArkMonomial;
    let mut out: Ctx<ElimTerm, F> = Ctx::default();
    let nvars = snap.nvars() as usize;

    for (coef, mono) in p.iter() {
        if coef.is_zero() {
            continue;
        }
        let exps: Vec<u32> = ArkOddElimTerm::<W>::exponents(mono, &snap.ring);
        let mut ctx: Ctx<PRef, usize> = Ctx::default();
        for (i, e) in exps.iter().enumerate().take(nvars) {
            if *e == 0 {
                continue;
            }
            let pref = snap.slots[i]
                .clone()
                .expect("engine: ark-gb produced exponent on ghost slot");
            let exp = *e as usize;
            ctx.insert(&pref, &exp);
        }
        let term = ElimTerm::new(ctx);
        out.insert(&term, &coef);
    }
    SparsePolynomial { terms: out }
}

/// Compute a *reduced* Gröbner basis of the ideal generated by `polys`
/// under the elim-then-grevlex order. Routes through ark-gb's
/// `compute_gb` over `OddElimTerm<W>` with the partitioned snapshot.
pub fn compute_gb_elim<F: Field + Copy + Send + Sync + 'static>(
    polys: &[SparsePolynomial<F, ElimTerm>],
) -> Vec<SparsePolynomial<F, ElimTerm>> {
    let nonzero: Vec<&SparsePolynomial<F, ElimTerm>> =
        polys.iter().filter(|p| !p.is_zero()).collect();
    if nonzero.is_empty() {
        return Vec::new();
    }

    // Constant-ideal short-circuit: ark-gb refuses `nvars = 0`.
    if super::collect_prefs(polys).is_empty() {
        return unit_basis_if_constant(&nonzero).unwrap_or_default();
    }

    let snap = build_snapshot(polys).unwrap_or_else(|e| panic!("{}", e));
    let fwd = pref_to_idx(&snap);
    let ark_inputs: Vec<Poly<F, ArkOddElimTerm<W>, W>> = nonzero
        .iter()
        .map(|p| poly_to_ark(&snap, &fwd, p).unwrap_or_else(|e| panic!("{}", e)))
        .collect();

    compute_gb(snap.ring.clone(), ark_inputs)
        .iter()
        .map(|p| ark_to_poly(&snap, p))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyses::groebner::Monomial;
    use ark_bls12_381::Fr;
    use ark_ff::One;
    use backend::ATyp;
    use lang::id::Vid;
    use lang::typ::{Distribution, Qualifier};
    use petgraph::graph::NodeIndex;

    fn pref_keep(name: &str) -> PRef {
        // Public/Nonuniform => keep (eliminate_var = false)
        PRef::from_var(
            Vid::new(name),
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Public,
            Distribution::Nonuniform,
        )
    }

    fn pref_elim(name: &str) -> PRef {
        // Local => eliminate_var = true
        PRef::from_var(
            Vid::new(name),
            NodeIndex::new(0),
            ATyp::scalar(),
            0,
            Qualifier::Local,
            Distribution::Nonuniform,
        )
    }

    fn mono(parts: Vec<(PRef, usize)>) -> ElimTerm {
        let mut ctx: Ctx<PRef, usize> = Ctx::default();
        for (p, e) in parts {
            ctx.insert(&p, &e);
        }
        ElimTerm::new(ctx)
    }

    fn term(c: i64, parts: Vec<(PRef, usize)>) -> SparsePolynomial<Fr, ElimTerm> {
        let mut terms: Ctx<ElimTerm, Fr> = Ctx::default();
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
        a: SparsePolynomial<Fr, ElimTerm>,
        b: SparsePolynomial<Fr, ElimTerm>,
    ) -> SparsePolynomial<Fr, ElimTerm> {
        a + b
    }

    #[test]
    fn round_trip_preserves_polynomial() {
        let t = pref_elim("t");
        let x = pref_keep("x");
        let y = pref_keep("y");
        let p = add(
            add(
                term(3, vec![(t.clone(), 2), (y.clone(), 1)]),
                term(2, vec![(t.clone(), 1), (x.clone(), 1)]),
            ),
            term(7, vec![]),
        );
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        let fwd = pref_to_idx(&snap);
        let ark = poly_to_ark(&snap, &fwd, &p).unwrap();
        let back = ark_to_poly(&snap, &ark);
        assert_eq!(p, back);
    }

    #[test]
    fn partition_places_elim_at_odd_indices() {
        let t = pref_elim("t");
        let u = pref_elim("u");
        let x = pref_keep("x");
        let y = pref_keep("y");
        let p = add(
            term(1, vec![(t.clone(), 1), (x.clone(), 1)]),
            term(1, vec![(u.clone(), 1), (y.clone(), 1)]),
        );
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        // 2 elim + 2 keep => 4 slots, no ghost.
        assert_eq!(snap.slots.len(), 4);
        // Even indices are keep, odd indices are elim.
        for (i, slot) in snap.slots.iter().enumerate() {
            let pref = slot.as_ref().expect("no ghost expected with 2+2");
            if i % 2 == 0 {
                assert!(
                    !ElimTerm::eliminate_var(pref),
                    "even idx {} must be keep",
                    i
                );
            } else {
                assert!(ElimTerm::eliminate_var(pref), "odd idx {} must be elim", i);
            }
        }
    }

    #[test]
    fn unequal_blocks_use_ghost_padding() {
        let t = pref_elim("t");
        let x = pref_keep("x");
        let y = pref_keep("y");
        let z = pref_keep("z");
        // 1 elim + 3 keep => max=3 => 6 slots; 2 ghost slots at odd parity.
        let p = add(
            add(
                term(1, vec![(t.clone(), 1), (x.clone(), 1)]),
                term(1, vec![(y.clone(), 1)]),
            ),
            term(1, vec![(z.clone(), 1)]),
        );
        let snap = build_snapshot(std::slice::from_ref(&p)).unwrap();
        assert_eq!(snap.slots.len(), 6);

        let mut ghosts = 0usize;
        for (i, slot) in snap.slots.iter().enumerate() {
            match slot {
                Some(pref) if i % 2 == 0 => assert!(!ElimTerm::eliminate_var(pref)),
                Some(pref) => assert!(ElimTerm::eliminate_var(pref)),
                None => ghosts += 1,
            }
        }
        assert_eq!(ghosts, 2);

        // Round-trip succeeds despite ghost slots.
        let fwd = pref_to_idx(&snap);
        let ark = poly_to_ark(&snap, &fwd, &p).unwrap();
        let back = ark_to_poly(&snap, &ark);
        assert_eq!(p, back);
    }

    #[test]
    fn compute_gb_pure_constant_ideal_returns_one() {
        // [3] is a non-zero constant, so the ideal contains 1.
        let p = term(3, vec![]);
        let gb = compute_gb_elim(&[p]);
        assert_eq!(gb.len(), 1);
        assert_eq!(gb[0].terms.len(), 1);
        let (m, c) = gb[0].terms.iter().next().unwrap();
        assert!(m.is_constant());
        assert!(c.is_one());
    }
}
