//! Property-based tests for [`KBucket`].
//!
//! The killer property: repeated `minus_m_mult_p` followed by
//! `into_poly` must match the slow-path `Poly::sub_mul_term` fold.
//! Everything else in this file is either a direct corollary of that
//! or a slot-bookkeeping invariant that isn't observable through
//! `into_poly` alone.
//!
//! Uses small strategies (1..=20 reductions, 1..=10-term polys, 5
//! variables, exponents ≤ 6) so the slow-path fold runs in a
//! reasonable time under `proptest`'s default case count.

use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_ff::{One, PrimeField, Zero};
use ark_gb::{GrevLexTerm, KBucket, MonoTerm, Poly, Ring};
use proptest::prelude::*;

const MAX_VARS: u32 = 5;
const MAX_EXP: u32 = 6;

fn arb_fr() -> impl Strategy<Value = Fr> {
    any::<[u8; 32]>().prop_map(|bytes| Fr::from_le_bytes_mod_order(&bytes))
}

fn arb_nonzero_fr() -> impl Strategy<Value = Fr> {
    arb_fr().prop_map(|f| if f.is_zero() { Fr::one() } else { f })
}

fn ring_strategy() -> impl Strategy<Value = Arc<Ring<Fr>>> {
    (1u32..=MAX_VARS).prop_map(|n| Arc::new(Ring::<Fr>::new(n).unwrap()))
}

fn poly_strategy(
    ring: Arc<Ring<Fr>>,
    max_terms: usize,
) -> impl Strategy<Value = Poly<Fr, GrevLexTerm>> {
    let n = ring.nvars() as usize;
    prop::collection::vec(
        (arb_nonzero_fr(), prop::collection::vec(0u32..=MAX_EXP, n)),
        0..=max_terms,
    )
    .prop_map(move |terms| {
        let converted: Vec<(Fr, GrevLexTerm)> = terms
            .into_iter()
            .map(|(c, e)| {
                (
                    c,
                    GrevLexTerm::from(MonoTerm::from_exponents(&ring, &e).unwrap()),
                )
            })
            .collect();
        Poly::from_terms(&ring, converted)
    })
}

fn mono_strategy(ring: Arc<Ring<Fr>>, max_exp: u32) -> impl Strategy<Value = GrevLexTerm> {
    let n = ring.nvars() as usize;
    prop::collection::vec(0u32..=max_exp, n)
        .prop_map(move |e| GrevLexTerm::from(MonoTerm::from_exponents(&ring, &e).unwrap()))
}

/// A seed polynomial plus a list of reducers `(m_i, c_i, q_i)`.
#[allow(clippy::type_complexity)]
fn bucket_workload_strategy() -> impl Strategy<
    Value = (
        Arc<Ring<Fr>>,
        Poly<Fr, GrevLexTerm>,
        Vec<(GrevLexTerm, Fr, Poly<Fr, GrevLexTerm>)>,
    ),
> {
    ring_strategy().prop_flat_map(|r| {
        // Cap monomial exponents at 3 and poly-term exponents at 3 so
        // their products (≤ 6) fit the 8-bit budget comfortably.
        let seed = poly_strategy(r.clone(), 10);
        let reducers = prop::collection::vec(
            (
                mono_strategy(r.clone(), 3),
                arb_nonzero_fr(),
                poly_strategy(r.clone(), 6),
            ),
            0..=15,
        );
        (Just(r), seed, reducers)
    })
}

/// Slow-path fold: start with `p`, then for each `(m, c, q)` set
/// `p ← p - c*m*q` via `Poly::sub_mul_term`. Per ADR-018,
/// `sub_mul_term` is infallible in release; the workload strategies
/// keep exponents well within the 7-bit budget.
fn slow_fold(
    ring: &Ring<Fr>,
    seed: Poly<Fr, GrevLexTerm>,
    ops: &[(GrevLexTerm, Fr, Poly<Fr, GrevLexTerm>)],
) -> Poly<Fr, GrevLexTerm> {
    let mut acc = seed;
    for (m, c, q) in ops {
        acc = acc.sub_mul_term(*c, m, q, ring);
    }
    acc
}

/// Bucket-path fold.
fn bucket_fold(
    ring: Arc<Ring<Fr>>,
    seed: Poly<Fr, GrevLexTerm>,
    ops: &[(GrevLexTerm, Fr, Poly<Fr, GrevLexTerm>)],
) -> Poly<Fr, GrevLexTerm> {
    let mut b = KBucket::from_poly(Arc::clone(&ring), seed);
    for (m, c, q) in ops {
        b.minus_m_mult_p(m, *c, q);
    }
    b.into_poly()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// The central property: bucket fold = slow-path fold.
    #[test]
    fn bucket_fold_matches_slow_path(
        (r, seed, ops) in bucket_workload_strategy()
    ) {
        let slow = slow_fold(&r, seed.clone(), &ops);
        let fast = bucket_fold(Arc::clone(&r), seed, &ops);
        slow.assert_canonical(&r);
        fast.assert_canonical(&r);
        prop_assert_eq!(fast, slow);
    }

    /// `into_poly` after seeding should round-trip a polynomial.
    #[test]
    fn seed_into_poly_round_trip((r, seed, _ops) in bucket_workload_strategy()) {
        let b = KBucket::from_poly(Arc::clone(&r), seed.clone());
        prop_assert_eq!(b.into_poly(), seed);
    }

    /// `leading()` must agree with `Poly::leading()` after any
    /// sequence of operations.
    #[test]
    fn leading_matches_poly_leading(
        (r, seed, ops) in bucket_workload_strategy()
    ) {
        let slow = slow_fold(&r, seed.clone(), &ops);

        let mut b = KBucket::from_poly(Arc::clone(&r), seed);
        for (m, c, q) in &ops {
            b.minus_m_mult_p(m, *c, q);
        }

        match (slow.leading(), b.leading()) {
            (None, None) => {},
            (Some((sc, sm)), Some((bc, bm))) => {
                prop_assert_eq!(sc, bc);
                prop_assert_eq!(*sm, *bm);
            },
            (a, b) => prop_assert!(false, "leading disagrees: slow = {:?}, bucket = {:?}",
                a.is_some(), b.is_some()),
        }
    }

    /// `is_zero` must agree with `into_poly().is_zero()`.
    #[test]
    fn is_zero_matches_poly_is_zero(
        (r, seed, ops) in bucket_workload_strategy()
    ) {
        let slow = slow_fold(&r, seed.clone(), &ops);
        let mut b = KBucket::from_poly(Arc::clone(&r), seed);
        for (m, c, q) in &ops {
            b.minus_m_mult_p(m, *c, q);
        }
        prop_assert_eq!(b.is_zero(), slow.is_zero());
    }

    /// `extract_leading` then `into_poly` must equal `Poly::extract_leading`:
    /// i.e. the tail of the polynomial.
    #[test]
    fn extract_leading_then_into_poly_matches_tail(
        (r, seed, ops) in bucket_workload_strategy()
    ) {
        let slow = slow_fold(&r, seed.clone(), &ops);

        let mut b = KBucket::from_poly(Arc::clone(&r), seed);
        for (m, c, q) in &ops {
            b.minus_m_mult_p(m, *c, q);
        }

        let bucket_lead = b.extract_leading();
        let after = b.into_poly();

        match slow.leading() {
            None => {
                prop_assert!(bucket_lead.is_none());
                prop_assert!(after.is_zero());
            }
            Some((sc, sm)) => {
                let (bc, bm) = bucket_lead.expect("bucket lead present when slow has lead");
                prop_assert_eq!(bc, sc);
                prop_assert_eq!(bm, *sm);

                // The remainder should be slow minus its leading term,
                // which equals reconstructing from slow's non-leading
                // terms. Reconstruct via scale/sub:
                let lead_poly = Poly::monomial(&r, bc, bm);
                let expected_tail = slow.sub(&lead_poly, &r);
                expected_tail.assert_canonical(&r);
                after.assert_canonical(&r);
                prop_assert_eq!(after, expected_tail);
            }
        }
    }

    /// Canonical invariants survive every operation.
    #[test]
    fn assert_canonical_through_sequence(
        (r, seed, ops) in bucket_workload_strategy()
    ) {
        let mut b = KBucket::from_poly(Arc::clone(&r), seed);
        b.assert_canonical();
        for (m, c, q) in &ops {
            b.minus_m_mult_p(m, *c, q);
            b.assert_canonical();
        }
        // Probing the leader must also preserve canonicality.
        let _ = b.leading();
        b.assert_canonical();
    }
}

// --- Fixed-input fixtures ---

fn mk_ring(nvars: u32) -> Arc<Ring<Fr>> {
    Arc::new(Ring::<Fr>::new(nvars).unwrap())
}

fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
    GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
}

/// Reduce a 10-term poly against a handful of 3-term reducers; bucket
/// and slow path must agree.
#[test]
fn small_bba_like_workload_matches() {
    let r = mk_ring(4);
    let seed = Poly::from_terms(
        &r,
        vec![
            (Fr::from(5u64), mono(&r, &[3, 1, 0, 0])),
            (Fr::from(7u64), mono(&r, &[2, 1, 1, 0])),
            (Fr::from(11u64), mono(&r, &[1, 2, 0, 1])),
            (Fr::from(13u64), mono(&r, &[0, 3, 1, 0])),
            (Fr::from(17u64), mono(&r, &[2, 0, 2, 0])),
            (Fr::from(19u64), mono(&r, &[1, 1, 1, 1])),
            (Fr::from(23u64), mono(&r, &[0, 2, 0, 2])),
            (Fr::from(29u64), mono(&r, &[0, 0, 3, 1])),
            (Fr::from(31u64), mono(&r, &[1, 0, 1, 2])),
            (Fr::from(37u64), mono(&r, &[0, 1, 0, 3])),
        ],
    );
    let ops: Vec<(GrevLexTerm, Fr, Poly<Fr, GrevLexTerm>)> = vec![
        (
            mono(&r, &[1, 0, 0, 0]),
            Fr::from(3u64),
            Poly::from_terms(
                &r,
                vec![
                    (Fr::from(1u64), mono(&r, &[1, 0, 0, 0])),
                    (Fr::from(2u64), mono(&r, &[0, 1, 0, 0])),
                    (Fr::from(4u64), mono(&r, &[0, 0, 1, 0])),
                ],
            ),
        ),
        (
            mono(&r, &[0, 1, 0, 0]),
            Fr::from(5u64),
            Poly::from_terms(
                &r,
                vec![
                    (Fr::from(1u64), mono(&r, &[0, 0, 1, 0])),
                    (Fr::from(6u64), mono(&r, &[0, 0, 0, 1])),
                ],
            ),
        ),
        (
            mono(&r, &[0, 0, 1, 0]),
            Fr::from(7u64),
            Poly::from_terms(&r, vec![(Fr::from(1u64), mono(&r, &[0, 1, 0, 0]))]),
        ),
    ];

    let slow = slow_fold(&r, seed.clone(), &ops);
    let fast = bucket_fold(r.clone(), seed, &ops);
    slow.assert_canonical(&r);
    fast.assert_canonical(&r);
    assert_eq!(fast, slow);
}
