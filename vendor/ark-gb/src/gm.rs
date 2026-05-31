//! Gebauer–Möller pair criteria and pair pipeline.
//!
//! Three user-visible entry points:
//!
//! * [`enter_one_pair_normal`] — build one candidate pair for
//!   `(s_idx, h_idx)`. Applies the product criterion (coprime
//!   leading monomials ⇒ pair eliminated). Returns `None` when the
//!   pair is pruned.
//! * [`chain_crit_normal`] — run the chain criterion on a candidate
//!   `BSet<W>` against existing [`SBasis`] and [`LSet<W>`] state. Prunes
//!   pairs in B whose LCM is covered by another pair's LCM; marks
//!   pairs in L that `lm(h)` covers.
//! * [`enterpairs`] — the whole pipeline: enumerate candidate
//!   pairs, apply product + chain criteria, merge survivors into L.
//! * [`enter_s`] — insert a survivor into the basis with redundancy
//!   marking (this is just `SBasis::insert`; re-exported here for
//!   API symmetry with Singular's `enterS`).
//!
//! Reference: `~/Singular/kernel/GBEngine/kutil.cc`
//! `enterOnePairNormal` (line 1939), `chainCritNormal` (line 3204).
//! Algorithms re-derived; no code copied. Our only concession to the
//! bootstrap is skipping signature / ecart-specific branches — we
//! always use the straight "global ordering, no Mora ecart" path.

use crate::bset::BSet;
use crate::field::Field;
use crate::lset::LSet;
use crate::monomial::{MonoTerm, Monomial};
use crate::pair::Pair;
use crate::poly::Poly;
use crate::ring::Ring;
use crate::sbasis::SBasis;

/// Generate one candidate pair for `(s_idx, h_idx)`.
///
/// Preconditions: `s_idx < h_idx`; `s_basis.poly(s_idx)` is
/// non-redundant and non-zero; `h` is nonzero. The caller provides
/// `h_lm_sev`, `h_lm` (these live in the driver's LObject cache
/// already and we don't want to re-read them through a `Poly`).
///
/// Returns `None` when the pair is pruned by the **product
/// criterion**: `lm(h)` and `lm(S[s_idx])` are coprime — the
/// S-polynomial reduces to zero before it can contribute anything
/// new to the basis.
#[allow(clippy::too_many_arguments)]
pub fn enter_one_pair_normal<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    s_basis: &SBasis<F, M, W>,
    s_idx: u32,
    h_idx: u32,
    h_lm: &MonoTerm<W>,
    h_lm_sev: u64,
    h_sugar: u32,
    arrival: u64,
) -> Option<Pair<W>> {
    debug_assert!(s_idx < h_idx);
    debug_assert!(!s_basis.is_redundant(s_idx as usize));

    let s_sevs = s_basis.sevs();
    let s_lm_sev = s_sevs[s_idx as usize];

    // Product criterion: coprime LMs ⇒ S-polynomial reduces to zero.
    //
    // sev is a bloom filter of nonzero exponents: `a_sev & b_sev ==
    // 0` implies no variable is shared, so coprime. The converse
    // (sev collision but actually coprime) is possible once variable
    // count exceeds 64 (sev wraps modulo 64). At default W=4 the
    // cap is `max_vars::<W>() = 31` so the sev check alone is exact;
    // for W >= 9 (`max_vars::<W>() = W*8 - 1 >= 71`) the wrap is
    // reachable, so the explicit coprime check after this fast path
    // is load-bearing — keep it.
    if (h_lm_sev & s_lm_sev) == 0 {
        return None;
    }
    let s_lm = s_basis
        .poly(s_idx as usize)
        .leading()
        .expect("non-redundant basis element is nonzero")
        .1
        .as_mono_term();
    if monomials_are_coprime(h_lm, s_lm, ring) {
        return None;
    }

    // LCM of the two leading monomials.
    let lcm = h_lm.lcm(s_lm, ring);
    // Sugar, following Giovini–Mora 1991 "One sugar cube, please":
    //   sugar(pair) = max(sugar(h) + deg(m_h), sugar(s) + deg(m_s))
    // where m_h = lcm / lm(h), m_s = lcm / lm(s). Equivalently,
    // deg(m_h) = deg(lcm) - deg(lm(h)), same for m_s. Every existing
    // basis element's sugar is treated as its leading total degree
    // in this bootstrap; the future bba driver may thread a richer
    // sugar through the Pair<W> via `h_sugar`.
    let deg_lcm = lcm.total_deg();
    let deg_h = h_lm.total_deg();
    let s_deg = s_basis.lm_degs()[s_idx as usize];
    let sugar_h_side = h_sugar + (deg_lcm - deg_h);
    let sugar_s_side = s_deg + (deg_lcm - s_deg);
    let sugar = sugar_h_side.max(sugar_s_side);

    Some(Pair::new(s_idx, h_idx, lcm, sugar, arrival))
}

/// Coprime check on monomials: no variable has nonzero exponent in
/// both. Called *after* the sev pre-filter rejects obvious shares.
fn monomials_are_coprime<F: Field + Copy + Send + Sync, const W: usize>(
    a: &MonoTerm<W>,
    b: &MonoTerm<W>,
    ring: &Ring<F, W>,
) -> bool {
    let n = ring.nvars();
    for i in 0..n {
        let ea = a.exponent(ring, i).expect("i < nvars");
        let eb = b.exponent(ring, i).expect("i < nvars");
        if ea > 0 && eb > 0 {
            return false;
        }
    }
    true
}

/// Chain criterion on a candidate B set and the existing basis +
/// LSet<W>.
///
/// Two phases:
///
/// 1. **B-internal**: for any two pairs `p = (i, h)` and `q = (j, h)`
///    in B with `lcm(p) | lcm(q)`, drop `q`. On equal LCMs, drop the
///    later one (higher index in `b.pairs()`); this is the same
///    "keep one representative per LCM equivalence class" rule
///    Singular uses in `chainCritNormal`. O(|B|²), with a sev
///    pre-filter on every inner-loop iteration.
/// 2. **L-side**: for every pair `(i, j)` currently live in L (with
///    `i, j != h`), if `lm(h) | lcm(i, j)` and `lcm(i, j)` differs
///    from both `lcm(lm(S[i]), lm(h))` and `lcm(lm(S[j]), lm(h))`,
///    the pair is covered by the chain `(i, h), (j, h)` and gets
///    tombstoned. The equality guards preserve the pair whose LCM
///    would collapse onto an S–h pair.
pub fn chain_crit_normal<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    s_basis: &SBasis<F, M, W>,
    h_lm: &MonoTerm<W>,
    h_lm_sev: u64,
    h_idx: u32,
    b: &mut BSet<W>,
    l: &mut LSet<W>,
) {
    // Phase 1: B-internal dedup.
    //
    // For each i, find every j whose lcm is divisible by pairs[i]'s
    // lcm and kill it. The naive O(n^2) scalar inner loop tests
    // `divides_with_sev(a.lcm_sev, c.lcm_sev, ...)` for every j.
    // ADR-009 replaces the scalar sev pre-filter with a SIMD-batched
    // scan over the BSet<W>'s flat `lcm_sevs` array.
    //
    // Sev pre-filter for "a divides c": every set bit of a.lcm_sev
    // must also be set in c.lcm_sev. That's the "subset_mask ⊆
    // sevs[idx]" predicate, which `find_sev_superset_match` returns
    // the next matching index for. (Note: this is the dual of
    // ADR-007's `find_sev_match`, which checks the opposite
    // direction — ADR-007 wanted "candidate divides leader" with
    // candidate iterating, here we want "outer-pair divides
    // inner-pair" with inner-pair iterating.)
    let n = b.len();
    let mut kill: Vec<bool> = vec![false; n];
    {
        let pairs = b.pairs();
        let lcm_sevs = b.lcm_sevs();
        for i in 0..n {
            if kill[i] {
                continue;
            }
            let a = &pairs[i];
            let a_sev = a.lcm_sev;
            let mut j = 0;
            loop {
                j = crate::simd::find_sev_superset_match(lcm_sevs, a_sev, j);
                if j >= n {
                    break;
                }
                if i == j || kill[j] {
                    j += 1;
                    continue;
                }
                let c = &pairs[j];
                let equal = a.lcm == c.lcm;
                if equal {
                    if j > i {
                        kill[j] = true;
                    }
                } else if a.lcm.divides(&c.lcm, ring) {
                    kill[j] = true;
                }
                j += 1;
            }
        }
    }
    for idx in (0..n).rev() {
        if kill[idx] {
            b.swap_remove(idx);
        }
    }

    // Phase 2: L-side G-M elimination.
    let mut to_drop: Vec<(u32, u32)> = Vec::new();
    for pair in l.iter_live() {
        if pair.i == h_idx || pair.j == h_idx {
            continue;
        }
        // Sev pre-filter: h_lm | pair.lcm requires every bit set in
        // h_lm_sev to also be set in pair.lcm_sev.
        if (h_lm_sev & !pair.lcm_sev) != 0 {
            continue;
        }
        if !h_lm.divides(&pair.lcm, ring) {
            continue;
        }
        // lcm(i, h) and lcm(j, h) — look up S[i], S[j] LMs.
        let lm_i = s_basis
            .poly(pair.i as usize)
            .leading()
            .expect("basis element in a live pair is nonzero")
            .1
            .as_mono_term();
        let lm_j = s_basis
            .poly(pair.j as usize)
            .leading()
            .expect("basis element in a live pair is nonzero")
            .1
            .as_mono_term();
        let lcm_ih = lm_i.lcm(h_lm, ring);
        if lcm_ih == pair.lcm {
            continue;
        }
        let lcm_jh = lm_j.lcm(h_lm, ring);
        if lcm_jh == pair.lcm {
            continue;
        }
        to_drop.push((pair.i, pair.j));
    }
    for (i, j) in to_drop {
        l.delete(i, j);
    }
}

/// Full `enterpairs` pipeline.
///
/// 1. Enumerate candidate pairs `(s_idx, h_idx)` for every
///    non-redundant `s_idx < h_idx`. Apply the product criterion
///    (via [`enter_one_pair_normal`]).
/// 2. Run [`chain_crit_normal`] on B and L.
/// 3. Merge surviving B pairs into L.
///
/// `arrival_start` is the first arrival counter to hand out; every
/// pair pushed into B (surviving the product criterion) gets the
/// next arrival. The bba driver advances `arrival_start` by the
/// returned count. The returned value is the number of pairs that
/// actually made it into L (after both phases of the chain crit).
#[allow(clippy::too_many_arguments)]
pub fn enterpairs<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    s_basis: &SBasis<F, M, W>,
    h_idx: u32,
    h_poly: &Poly<F, M, W>,
    h_sugar: u32,
    l_set: &mut LSet<W>,
    arrival_start: u64,
) -> usize {
    let h_lm = *h_poly.leading().expect("h is nonzero").1.as_mono_term();
    let h_lm_sev = h_poly.lm_sev();

    let mut b = BSet::new();
    let mut arrival = arrival_start;

    for s_idx in 0..h_idx {
        if s_basis.is_redundant(s_idx as usize) {
            continue;
        }
        if let Some(pair) = enter_one_pair_normal(
            ring, s_basis, s_idx, h_idx, &h_lm, h_lm_sev, h_sugar, arrival,
        ) {
            arrival += 1;
            b.push(pair);
        }
    }

    chain_crit_normal(ring, s_basis, &h_lm, h_lm_sev, h_idx, &mut b, l_set);

    let merged = b.len();
    for pair in b.into_pairs() {
        l_set.insert(pair);
    }
    merged
}

/// `enterS`: append `h` to the basis with redundancy marking. This
/// is just `SBasis::insert`; re-exported here so the bba driver's
/// call site reads `enter_s(h)` symmetric with `enterpairs(h)`.
pub fn enter_s<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    s_basis: &mut SBasis<F, M, W>,
    h: Poly<F, M, W>,
) -> usize {
    s_basis.insert(ring, h)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::GrevLexTerm;
    use ark_bls12_381::Fr;
    use ark_ff::One;

    fn mk_ring(nvars: u32) -> Ring<Fr> {
        Ring::<Fr>::new(nvars).unwrap()
    }

    fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
        GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
    }

    #[test]
    fn product_criterion_prunes_coprime_lms() {
        // x, y: coprime leading monomials.
        let r = mk_ring(3);
        let mut s = SBasis::new();
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 0, 0])),
        );
        let h = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[0, 1, 0]));
        let h_lm = h.leading().unwrap().1.0;
        let got = enter_one_pair_normal(&r, &s, 0, 1, &h_lm, h.lm_sev(), 1, 0);
        assert!(got.is_none(), "coprime LMs must be pruned by product crit");
    }

    #[test]
    fn share_variable_keeps_pair() {
        let r = mk_ring(3);
        let mut s = SBasis::new();
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 1, 0])),
        );
        let h = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[0, 1, 1]));
        let h_lm = h.leading().unwrap().1.0;
        let got = enter_one_pair_normal(&r, &s, 0, 1, &h_lm, h.lm_sev(), 2, 0).unwrap();
        assert_eq!(got.i, 0);
        assert_eq!(got.j, 1);
        // LCM = xyz (exp [1,1,1]).
        assert_eq!(got.lcm, mono(&r, &[1, 1, 1]).0);
    }

    #[test]
    fn enterpairs_ideal_xx_yy_empty_after_prodcrit() {
        // S = {x^2}, add y^2. Single pair (0, 1) with coprime LMs:
        // pruned by product crit. L is empty after enterpairs.
        let r = mk_ring(2);
        let mut s = SBasis::new();
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[2, 0])),
        );
        let h = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[0, 2]));
        let h_idx = s.insert(&r, h.clone());
        let mut l = LSet::new();
        let inserted = enterpairs(&r, &s, h_idx as u32, &h, h.lm_deg(), &mut l, 0);
        assert_eq!(inserted, 0);
        assert_eq!(l.len(), 0);
    }

    #[test]
    fn enterpairs_shares_variable_inserts_pair() {
        // S = {xy}, add yz. LMs share y; product crit does NOT prune.
        let r = mk_ring(3);
        let mut s = SBasis::new();
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 1, 0])),
        );
        let h = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[0, 1, 1]));
        let h_idx = s.insert(&r, h.clone());
        let mut l = LSet::new();
        let inserted = enterpairs(&r, &s, h_idx as u32, &h, h.lm_deg(), &mut l, 0);
        assert_eq!(inserted, 1);
        let pair = l.pop().unwrap();
        assert_eq!((pair.i, pair.j), (0, 1));
        assert_eq!(pair.lcm, mono(&r, &[1, 1, 1]).0);
    }

    #[test]
    fn chain_crit_b_internal_drops_subsumed() {
        // S = { x^2, y^3, x^2*y^2 }; add h = y*z.
        //   Pair (0, 3) LCM = lcm(x^2, yz)     = x^2 y z
        //   Pair (1, 3) LCM = lcm(y^3, yz)     = y^3 z
        //   Pair (2, 3) LCM = lcm(x^2 y^2, yz) = x^2 y^2 z
        // x^2 y z divides x^2 y^2 z → (2, 3) pruned.
        // y^3 z is not divisible by x^2 y z and does not divide
        //   x^2 y z → (1, 3) stays.
        //
        // We pick x^2 instead of x so that x^2 does NOT divide the
        // later x^2 y^2 (still not: it does divide — x^2 | x^2 y^2).
        // Instead let's use LMs that don't trigger redundancy:
        //   S[0] = x^2 (LM x^2);  x^2 | x^2 y^2 → S[0] becomes
        //     redundant when S[2] arrives, which would skip (0, h)
        //     entirely in enterpairs. We need the earlier elements'
        //     LMs NOT to divide the later ones.
        //
        // Use S[0] = x^2 z^2, S[1] = y^3, S[2] = x^2 y^2 (z-free).
        //   x^2 z^2 does not divide x^2 y^2 (z^2 missing).
        //   y^3 does not divide x^2 y^2 (y^3 > y^2).
        //   Add h = y*z (LM yz).
        //     (0, 3) LCM = lcm(x^2 z^2, yz)     = x^2 y z^2
        //     (1, 3) LCM = lcm(y^3, yz)         = y^3 z
        //     (2, 3) LCM = lcm(x^2 y^2, yz)     = x^2 y^2 z
        //   Does (0, 3) divide (2, 3)?  x^2 y z^2 | x^2 y^2 z?  No
        //     (z^2 does not divide z).  So (0, 3) does NOT prune
        //     (2, 3).  Different example needed.
        //
        // Simpler: construct B manually via a direct call to
        // chain_crit_normal rather than wrestling with SBasis
        // redundancy marking. That lets us test the B-internal
        // chain criterion in isolation.
        let r = mk_ring(3);
        let mut s = SBasis::new();
        // Three unrelated LMs (no redundancy triggered): z, y, x.
        // Their divisibility is irrelevant; we'll install crafted
        // pairs directly into B below.
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[0, 0, 1])),
        );
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[0, 1, 0])),
        );
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 0, 0])),
        );
        let h_lm = mono(&r, &[0, 1, 1]).0; // y z
        let h_lm_sev = h_lm.sev();

        // Build B by hand:
        //   (0, 3) LCM = xyz       (smallest, will survive)
        //   (1, 3) LCM = y^3 z     (incomparable with xyz, survives)
        //   (2, 3) LCM = x^2 y^2 z (xyz divides it — dies)
        let mut b = BSet::new();
        b.push(Pair::new(0, 3, mono(&r, &[1, 1, 1]).0, 3, 0));
        b.push(Pair::new(1, 3, mono(&r, &[0, 3, 1]).0, 4, 1));
        b.push(Pair::new(2, 3, mono(&r, &[2, 2, 1]).0, 5, 2));
        let mut l = LSet::new();

        chain_crit_normal(&r, &s, &h_lm, h_lm_sev, 3, &mut b, &mut l);

        // After the criterion, B has two survivors and (2, 3) is
        // gone.
        let surviving: Vec<(u32, u32)> = b.pairs().iter().map(|p| (p.i, p.j)).collect();
        assert!(surviving.contains(&(0, 3)), "(0, 3) must survive");
        assert!(surviving.contains(&(1, 3)), "(1, 3) must survive");
        assert!(!surviving.contains(&(2, 3)), "(2, 3) must be pruned");
        assert_eq!(b.len(), 2);
    }

    #[test]
    fn cyclic3_fixture_pair_count() {
        // Ideal (x + y + z, xy + yz + zx, xyz - 1) in F_32003[x,y,z]
        // degrevlex.  Leading monomials (degrevlex):
        //   f_0 = x + y + z    → LM = x
        //   f_1 = xy + yz + zx → LM = xy
        //   f_2 = xyz - 1      → LM = xyz
        //
        // SBasis::insert marks *older* elements redundant when `lm(h)`
        // divides `lm(S[i])`.  Here the LMs are nested the "wrong
        // way" for that (older LMs divide newer): x | xy | xyz, but
        // the insert rule needs lm(new) | lm(old), which fails for
        // every pair here.  So no redundancy is triggered during
        // input insertion.
        //
        // enter_s / enterpairs pipeline, tracking the LSet:
        //   insert f_0: no pairs yet (first element). L empty.
        //   insert f_1 (h_idx = 1):
        //     Pair (0, 1): LM(f_0) = x, LM(h) = xy.
        //     sev(x) = 1, sev(xy) = 3 → sev share, not coprime.
        //     coprime check: x and xy both nonzero in x → not coprime.
        //     → 1 pair survives product crit.
        //     LCM = xy, sugar = ... (will check).
        //     chain crit: only one candidate, no pruning.
        //     L has 1 pair (0, 1).
        //   insert f_2 (h_idx = 2):
        //     Pair (0, 2): LM(f_0) = x, LM(f_2) = xyz.
        //       Not coprime (share x). LCM = xyz.
        //     Pair (1, 2): LM(f_1) = xy, LM(f_2) = xyz.
        //       Not coprime (share x, y). LCM = xyz.
        //     chain crit (B-internal): both have LCM xyz (equal).
        //       Keep the first-inserted, drop the later. One of them
        //       (by our stable rule: keep lower index in B, drop
        //       higher) survives. B has 1 pair.
        //     chain crit (L-side): existing pair (0, 1) has LCM xy.
        //       xyz does not divide xy → (0, 1) stays.
        //     L now has 2 pairs.
        //   Final: SBasis.len == 3, no redundancy, LSet.len == 2.
        let r = mk_ring(3);
        let mut s = SBasis::new();
        let mut l = LSet::new();

        let f_0 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 0, 0])),
                (Fr::one(), mono(&r, &[0, 1, 0])),
                (Fr::one(), mono(&r, &[0, 0, 1])),
            ],
        );
        let f_1 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 0])),
                (Fr::one(), mono(&r, &[0, 1, 1])),
                (Fr::one(), mono(&r, &[1, 0, 1])),
            ],
        );
        let f_2 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 1])),
                (-Fr::one(), mono(&r, &[0, 0, 0])),
            ],
        );

        let h0_idx = enter_s(&r, &mut s, f_0.clone()) as u32;
        let _ = enterpairs(&r, &s, h0_idx, &f_0, f_0.lm_deg(), &mut l, 0);
        let h1_idx = enter_s(&r, &mut s, f_1.clone()) as u32;
        let _ = enterpairs(&r, &s, h1_idx, &f_1, f_1.lm_deg(), &mut l, 100);
        let h2_idx = enter_s(&r, &mut s, f_2.clone()) as u32;
        let _ = enterpairs(&r, &s, h2_idx, &f_2, f_2.lm_deg(), &mut l, 200);

        assert_eq!(s.len(), 3);
        for i in 0..3 {
            assert!(!s.is_redundant(i), "no redundancy expected at index {i}");
        }
        // After all three inputs the L set contains two surviving
        // pairs: (0, 1) with LCM xy and one of {(0, 2), (1, 2)}
        // with LCM xyz (the other was pruned by the B-internal
        // chain crit's equal-LCM rule).
        assert_eq!(l.len(), 2, "cyclic-3 expected pair count");
        assert!(l.contains(0, 1));
        // Exactly one of (0, 2) and (1, 2) survives.
        let both_survive = l.contains(0, 2) && l.contains(1, 2);
        let one_survives = l.contains(0, 2) ^ l.contains(1, 2);
        assert!(
            !both_survive && one_survives,
            "expected exactly one of (0,2), (1,2) to survive"
        );
    }

    #[test]
    fn chain_crit_l_side_drops_pair_covered_by_new_h() {
        // Build:
        //   S[0] = x^2 y   (LM x^2 y)
        //   S[1] = x y^2   (LM x y^2)
        // Seed L with pair (0, 1), LCM = x^2 y^2.
        // Insert h = xy (LM xy). xy | x^2 y^2.
        //   lcm(0, h) = x^2 y  ≠ x^2 y^2
        //   lcm(1, h) = x y^2  ≠ x^2 y^2
        // → (0, 1) dies by the L-side chain criterion.
        let r = mk_ring(2);
        let mut s = SBasis::new();
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[2, 1])),
        );
        s.insert(
            &r,
            Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 2])),
        );

        let mut l = LSet::new();
        let lcm_01 = mono(&r, &[2, 2]).0;
        l.insert(Pair::new(0, 1, lcm_01, 4, 0));
        assert!(l.contains(0, 1));

        let h = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 1]));
        let h_idx = s.insert(&r, h.clone());
        let _ = enterpairs(&r, &s, h_idx as u32, &h, h.lm_deg(), &mut l, 10);

        assert!(!l.contains(0, 1), "(0,1) must be L-side G-M-eliminated");
    }
}
