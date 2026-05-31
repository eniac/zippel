//! Regression-detection suite for `compute_gb`.

use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_ff::Field as ArkField;
use ark_gb::bba::compute_gb_serial;
use ark_gb::compute_gb;
use ark_gb::monomial::{GrevLexTerm, MonoTerm, Monomial, OddElimTerm};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;
use ark_gb::validate::is_groebner_basis;

#[path = "../benches/groebner_shared.rs"]
mod shared;
use shared::{cyclic_polys, elim_ring, grevlex_ring, katsura_polys, one_poly, var_poly};

// ---------------------------------------------------------------------------
// Helpers.
// ---------------------------------------------------------------------------

fn deterministic_shuffle<X: Clone>(xs: &[X], seed: u64) -> Vec<X> {
    let mut out: Vec<X> = xs.to_vec();
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xDEAD_BEEF_DEAD_BEEF;
    let mut next = || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    for i in (1..out.len()).rev() {
        let j = (next() as usize) % (i + 1);
        out.swap(i, j);
    }
    out
}

fn assert_proper<M: Monomial<Fr>>(label: &str, gb: &[Poly<Fr, M>], ring: &Ring<Fr>) {
    assert!(!gb.is_empty(), "[{label}] empty reduced GB");
    let unit = M::one(ring);
    let unit_seen = gb.iter().any(|p| {
        let terms: Vec<_> = p.iter().collect();
        terms.len() == 1 && *terms[0].1 == unit
    });
    assert!(
        !unit_seen,
        "[{label}] reduced GB contains a constant — ideal is the whole ring"
    );
}

fn standard_monomial_count<M: Monomial<Fr>>(ring: &Ring<Fr>, gb: &[Poly<Fr, M>]) -> Option<usize> {
    let nvars = ring.nvars() as usize;
    let lm_exps: Vec<Vec<u32>> = gb
        .iter()
        .filter_map(|p| p.leading().map(|(_, m)| m.exponents(ring)))
        .collect();

    let bounds: Vec<u32> = (0..nvars)
        .map(|i| {
            lm_exps
                .iter()
                .filter_map(|e| {
                    let nonzero: Vec<usize> = (0..nvars).filter(|k| e[*k] > 0).collect();
                    if nonzero.len() == 1 && nonzero[0] == i {
                        Some(e[i])
                    } else {
                        None
                    }
                })
                .min()
        })
        .collect::<Option<Vec<_>>>()?;

    fn divides(a: &[u32], b: &[u32]) -> bool {
        a.iter().zip(b).all(|(x, y)| x <= y)
    }

    let mut idx = vec![0u32; nvars];
    let mut count = 0usize;
    loop {
        let candidate: Vec<u32> = idx.clone();
        if !lm_exps.iter().any(|lm| divides(lm, &candidate)) {
            count += 1;
        }
        let mut i = 0;
        loop {
            if i == nvars {
                return Some(count);
            }
            idx[i] += 1;
            if idx[i] < bounds[i] {
                break;
            }
            idx[i] = 0;
            i += 1;
        }
    }
}

fn assert_is_gb<M: Monomial<Fr> + From<MonoTerm>>(
    label: &str,
    ring: &Arc<Ring<Fr>>,
    input: &[Poly<Fr, M>],
    gb: &[Poly<Fr, M>],
) {
    if let Err(err) = is_groebner_basis(ring, input, gb) {
        panic!("[{label}] compute_gb output failed Buchberger's criterion: {err:?}");
    }
}

fn run_self_checks<M: Monomial<Fr> + From<MonoTerm> + 'static>(
    label: &str,
    ring: &Arc<Ring<Fr>>,
    input: &[Poly<Fr, M>],
    expected_dim: Option<usize>,
) -> Vec<Poly<Fr, M>> {
    let gb = compute_gb_serial(Arc::clone(ring), input.to_vec());
    assert_proper(label, &gb, ring);
    assert_is_gb(label, ring, input, &gb);

    let shuffled = deterministic_shuffle(input, 0x00C0_FFEE_u64);
    let gb_shuf = compute_gb_serial(Arc::clone(ring), shuffled);
    assert_eq!(gb, gb_shuf, "[{label}] reduced GB depends on input order");

    let dim = standard_monomial_count(ring, &gb);
    if let Some(exp) = expected_dim {
        assert_eq!(
            dim,
            Some(exp),
            "[{label}] standard-monomial count mismatch (got {dim:?}, expected Some({exp}))"
        );
    }
    gb
}

// ---------------------------------------------------------------------------
// GrevLexTerm cases.
// ---------------------------------------------------------------------------

#[test]
fn katsura_3_grevlex_self_checks() {
    let ring = grevlex_ring(3);
    let inputs = katsura_polys::<GrevLexTerm>(&ring);
    run_self_checks("katsura/3/grevlex", &ring, &inputs, Some(1 << 2));
}

#[test]
fn cyclic_3_grevlex_self_checks() {
    let ring = grevlex_ring(3);
    let inputs = cyclic_polys::<GrevLexTerm>(&ring);
    run_self_checks("cyclic/3/grevlex", &ring, &inputs, None);
}

// ---------------------------------------------------------------------------
// OddElimTerm cases.
// ---------------------------------------------------------------------------

#[test]
fn katsura_3_elim_self_checks() {
    let ring = elim_ring(3);
    let inputs = katsura_polys::<OddElimTerm>(&ring);
    run_self_checks("katsura/3/elim", &ring, &inputs, Some(1 << 2));
}

#[test]
fn cyclic_3_elim_self_checks() {
    let ring = elim_ring(3);
    let inputs = cyclic_polys::<OddElimTerm>(&ring);
    run_self_checks("cyclic/3/elim", &ring, &inputs, None);
}

// ---------------------------------------------------------------------------
// Cross-order dimension invariance.
// ---------------------------------------------------------------------------

#[test]
fn katsura_3_dim_order_invariant() {
    let ring = grevlex_ring(3);
    let gb_g = compute_gb(Arc::clone(&ring), katsura_polys::<GrevLexTerm>(&ring));
    let gb_e = compute_gb(Arc::clone(&ring), katsura_polys::<OddElimTerm>(&ring));
    let d_g = standard_monomial_count(&ring, &gb_g);
    let d_e = standard_monomial_count(&ring, &gb_e);
    assert_eq!(d_g, d_e, "katsura/3 std-mono count differs between orders");
    assert_eq!(d_g, Some(1 << 2));
}

#[test]
fn cyclic_3_dim_order_invariant() {
    let ring = grevlex_ring(3);
    let gb_g = compute_gb(Arc::clone(&ring), cyclic_polys::<GrevLexTerm>(&ring));
    let gb_e = compute_gb(Arc::clone(&ring), cyclic_polys::<OddElimTerm>(&ring));
    let d_g = standard_monomial_count(&ring, &gb_g);
    let d_e = standard_monomial_count(&ring, &gb_e);
    assert_eq!(d_g, d_e, "cyclic/3 std-mono count differs between orders");
    assert_eq!(d_g, Some(6));
}

// ---------------------------------------------------------------------------
// Pinned reduced GBs (sympy reference).
// ---------------------------------------------------------------------------

type PolyLit<'a> = &'a [(i64, u64, &'a [(usize, usize)])];
type BasisLit<'a> = &'a [PolyLit<'a>];

fn fr_from_rational(num: i64, den: u64) -> Fr {
    let mag = Fr::from(num.unsigned_abs());
    let n = if num < 0 { -mag } else { mag };
    let d = Fr::from(den);
    n * d.inverse().expect("denominator must be non-zero")
}

fn poly_from_lit(ring: &Ring<Fr>, lit: PolyLit<'_>) -> Poly<Fr, GrevLexTerm> {
    let mut out = Poly::<Fr, GrevLexTerm>::zero();
    for &(num, den, mono) in lit {
        let c = fr_from_rational(num, den);
        let mut term = Poly::<Fr, GrevLexTerm>::from_terms(ring, vec![(c, GrevLexTerm::one(ring))]);
        for &(vi, pow) in mono {
            for _ in 0..pow {
                let v = var_poly::<GrevLexTerm>(ring, vi);
                term = term.mul(&v, ring);
            }
        }
        out = out.add(&term, ring);
    }
    out
}

fn pinned_basis(ring: &Ring<Fr>, lits: BasisLit<'_>) -> Vec<Poly<Fr, GrevLexTerm>> {
    lits.iter().map(|p| poly_from_lit(ring, p)).collect()
}

fn assert_matches_pin(
    label: &str,
    ring: &Arc<Ring<Fr>>,
    our_gb: &[Poly<Fr, GrevLexTerm>],
    pinned: Vec<Poly<Fr, GrevLexTerm>>,
) {
    let pinned_canon = compute_gb_serial(Arc::clone(ring), pinned);
    assert_eq!(
        our_gb.len(),
        pinned_canon.len(),
        "[{label}] GB length differs from sympy reference"
    );
    assert_eq!(
        our_gb,
        &pinned_canon[..],
        "[{label}] reduced GB doesn't match sympy reference"
    );
}

const KATSURA_3_GB: BasisLit<'static> = &[
    &[
        (7, 1, &[(1, 1)]),
        (210, 1, &[(2, 3)]),
        (-79, 1, &[(2, 2)]),
        (3, 1, &[(2, 1)]),
    ],
    &[
        (5, 1, &[(1, 2)]),
        (-1, 1, &[(1, 1)]),
        (-3, 1, &[(2, 2)]),
        (1, 1, &[(2, 1)]),
    ],
    &[
        (10, 1, &[(1, 1), (2, 1)]),
        (-1, 1, &[(1, 1)]),
        (12, 1, &[(2, 2)]),
        (-4, 1, &[(2, 1)]),
    ],
    &[
        (1, 1, &[(0, 1)]),
        (2, 1, &[(1, 1)]),
        (2, 1, &[(2, 1)]),
        (-1, 1, &[]),
    ],
];

const CYCLIC_3_GB: BasisLit<'static> = &[
    &[(1, 1, &[(2, 3)]), (-1, 1, &[])],
    &[
        (1, 1, &[(1, 2)]),
        (1, 1, &[(1, 1), (2, 1)]),
        (1, 1, &[(2, 2)]),
    ],
    &[(1, 1, &[(0, 1)]), (1, 1, &[(1, 1)]), (1, 1, &[(2, 1)])],
];

#[test]
fn katsura_3_grevlex_pinned() {
    let ring = grevlex_ring(3);
    let our_gb = compute_gb_serial(Arc::clone(&ring), katsura_polys::<GrevLexTerm>(&ring));
    let pinned = pinned_basis(&ring, KATSURA_3_GB);
    assert_matches_pin("katsura/3/grevlex/pinned", &ring, &our_gb, pinned);
}

#[test]
fn cyclic_3_grevlex_pinned() {
    let ring = grevlex_ring(3);
    let our_gb = compute_gb_serial(Arc::clone(&ring), cyclic_polys::<GrevLexTerm>(&ring));
    let pinned = pinned_basis(&ring, CYCLIC_3_GB);
    assert_matches_pin("cyclic/3/grevlex/pinned", &ring, &our_gb, pinned);
}

#[test]
fn helpers_one_poly_is_unit() {
    let ring = grevlex_ring(3);
    let one = one_poly::<GrevLexTerm>(&ring);
    let v0 = var_poly::<GrevLexTerm>(&ring, 0);
    let prod = v0.mul(&one, &ring);
    assert_eq!(prod, v0, "1 * x_0 must equal x_0");
}
