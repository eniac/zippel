//! Property tests for the Gebauer–Möller pipeline.
//!
//! The headline check: for a random `SBasis` and a new `h`, the set
//! of pairs `enterpairs` produces must equal the set produced by a
//! slow O(n²) reference that
//!
//! * generates every candidate (s_idx, h_idx) pair;
//! * applies the product criterion directly on exponent vectors
//!   (no sev pre-filter);
//! * runs the chain criterion by straight divisibility on monomials
//!   (no sev pre-filter);
//! * does not touch the LSet side (we only check B survivors).
//!
//! If the sev-based path disagrees with the slow reference, the sev
//! pre-filter has a bug. Since MAX_VARS = 31 in the ark_gb bootstrap
//! (sev has 64 bits) the sev bloom filter is exact, so the two must
//! agree term-for-term.

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::gm;
use ark_gb::monomial::{GrevLexTerm, MonoTerm, Monomial};
use ark_gb::{LSet, Poly, Ring, SBasis};
use proptest::prelude::*;

const MAX_VARS: u32 = 4;
const MAX_EXP: u32 = 3;
const MAX_BASIS: usize = 8;

fn ring_strategy() -> impl Strategy<Value = Ring<Fr>> {
    (2u32..=MAX_VARS).prop_map(|n| Ring::<Fr>::new(n).unwrap())
}

fn lm_strategy(ring: Ring<Fr>) -> impl Strategy<Value = MonoTerm> {
    let n = ring.nvars() as usize;
    prop::collection::vec(0u32..=MAX_EXP, n).prop_filter_map("need nonzero", move |e| {
        if e.iter().all(|&x| x == 0) {
            return None;
        }
        Some(MonoTerm::from_exponents(&ring, &e).unwrap())
    })
}

fn scenario_strategy() -> impl Strategy<Value = (Ring<Fr>, Vec<MonoTerm>, MonoTerm)> {
    ring_strategy().prop_flat_map(|r| {
        let r1 = r.clone();
        let r2 = r.clone();
        let lms = prop::collection::vec(lm_strategy(r1.clone()), 1..=MAX_BASIS);
        (lms, lm_strategy(r2)).prop_map(move |(basis, h)| (r.clone(), basis, h))
    })
}

/// Slow reference: compute the surviving B after enterpairs.
///
/// Returns `(i, j)` index pairs only; the LCMs are deterministic
/// from the inputs so we don't need to check them separately.
fn slow_enterpairs(
    ring: &Ring<Fr>,
    lms: &[MonoTerm],
    redundant: &[bool],
    h_lm: &MonoTerm,
    h_idx: u32,
) -> Vec<(u32, u32)> {
    // Product criterion: coprime LMs are pruned.
    let mut pairs: Vec<(u32, u32, MonoTerm)> = Vec::new();
    for (i, lm_i) in lms.iter().enumerate() {
        if redundant[i] {
            continue;
        }
        if exp_coprime(ring, lm_i, h_lm) {
            continue;
        }
        let lcm = lm_i.lcm(h_lm, ring);
        pairs.push((i as u32, h_idx, lcm));
    }
    // Chain criterion inside B: drop pair[j] if some pair[i] with
    // i != j has lcm(i) | lcm(j) (strict or equal with i < j).
    let n = pairs.len();
    let mut kill = vec![false; n];
    for i in 0..n {
        if kill[i] {
            continue;
        }
        for j in 0..n {
            if i == j || kill[j] {
                continue;
            }
            let eq = pairs[i].2 == pairs[j].2;
            if eq {
                if j > i {
                    kill[j] = true;
                }
                continue;
            }
            if pairs[i].2.divides(&pairs[j].2, ring) {
                kill[j] = true;
            }
        }
    }
    pairs
        .into_iter()
        .enumerate()
        .filter(|(k, _)| !kill[*k])
        .map(|(_, (a, b, _))| (a, b))
        .collect()
}

fn exp_coprime(ring: &Ring<Fr>, a: &MonoTerm, b: &MonoTerm) -> bool {
    for i in 0..ring.nvars() {
        let ea = a.exponent(ring, i).unwrap();
        let eb = b.exponent(ring, i).unwrap();
        if ea > 0 && eb > 0 {
            return false;
        }
    }
    true
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(150))]

    #[test]
    fn enterpairs_agrees_with_slow_reference(
        (r, basis_lms, h_lm) in scenario_strategy(),
    ) {
        // Build the SBasis with single-term polys.
        let mut s = SBasis::<Fr, GrevLexTerm>::new();
        for m in &basis_lms {
            s.insert(&r, Poly::monomial(&r, Fr::one(), GrevLexTerm::from(*m)));
        }
        let h = Poly::monomial(&r, Fr::one(), GrevLexTerm::from(h_lm));
        let h_idx = s.insert(&r, h.clone()) as u32;

        // Snapshot post-redundancy state of the pre-h basis. The
        // inserted h lives at index h_idx; the redundancy flags we
        // want are for indices 0..h_idx.
        let lms_pre: Vec<MonoTerm> = (0..h_idx as usize)
            .map(|i| {
                *<GrevLexTerm as Monomial<Fr>>::as_mono_term(s.poly(i).leading().unwrap().1)
            })
            .collect();
        let red: Vec<bool> = (0..h_idx as usize).map(|i| s.is_redundant(i)).collect();

        // Fast path (L-side empty, so B-side is the whole story).
        let mut l = LSet::new();
        let inserted = gm::enterpairs(&r, &s, h_idx, &h, h.lm_deg(), &mut l, 0);
        let mut got: Vec<(u32, u32)> = (0..inserted)
            .map(|_| {
                let p = l.pop().unwrap();
                (p.i, p.j)
            })
            .collect();
        got.sort();

        let mut want = slow_enterpairs(&r, &lms_pre, &red, &h_lm, h_idx);
        want.sort();

        prop_assert_eq!(got, want);
    }
}
