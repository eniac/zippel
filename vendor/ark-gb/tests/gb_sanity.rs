//! Hand-checkable closed-form Gröbner basis sanity tests.
//!
//! These cases have GBs with known closed forms that we can write
//! out as literal `Poly<Fr, GrevLexTerm>` values; the test asserts the structure
//! of `compute_gb`'s output directly without going through
//! [`ark_gb::validate::is_groebner_basis`]. This breaks the cycle
//! "buggy reducer in `compute_gb` would also let a buggy GB
//! validate as correct via the same reducer in
//! `is_groebner_basis`".

use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::compute_gb;
use ark_gb::monomial::{GrevLexTerm, MonoTerm, Monomial};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

fn mono(ring: &Ring<Fr>, exps: &[u32]) -> GrevLexTerm {
    GrevLexTerm::from(MonoTerm::from_exponents(ring, exps).unwrap())
}

/// `compute_gb` of `[x - 1, x - 2]` over `Fr[x]` must reduce to
/// `[1]` (the unit ideal): subtracting the two generators yields
/// the constant `1`, after which everything reduces to zero.
#[test]
fn coprime_linears_collapse_to_unit_ideal() {
    let ring = Arc::new(Ring::<Fr>::new(1).unwrap());
    let f1 = Poly::<Fr, GrevLexTerm>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1])),
            (-Fr::one(), mono(&ring, &[0])),
        ],
    );
    let f2 = Poly::<Fr, GrevLexTerm>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1])),
            (-Fr::from(2u64), mono(&ring, &[0])),
        ],
    );
    let gb = compute_gb(ring.clone(), vec![f1, f2]);
    assert_eq!(gb.len(), 1, "GB([x-1, x-2]) must collapse to a constant");
    let g = &gb[0];
    // The single generator must be a non-zero constant — i.e. one
    // term, monomial all-zero exponents. After the auto-monic step
    // it must equal `1`.
    let terms: Vec<_> = g.iter().collect();
    assert_eq!(
        terms.len(),
        1,
        "constant ideal generator must be a single term"
    );
    let (c, m) = terms[0];
    assert_eq!(m.exponents(&ring), vec![0]);
    assert_eq!(c, Fr::one());
}

/// `compute_gb` of `[x + y, x - y]` over `Fr[x, y]` must yield a
/// 2-element GB whose leading-monomial set is `{x, y}`. The exact
/// generators (after auto-reduction + monic) are `x` and `y`.
#[test]
fn linear_two_var_gb_is_x_y() {
    let ring = Arc::new(Ring::<Fr>::new(2).unwrap());
    let f1 = Poly::<Fr, GrevLexTerm>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 0])),
            (Fr::one(), mono(&ring, &[0, 1])),
        ],
    );
    let f2 = Poly::<Fr, GrevLexTerm>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 0])),
            (-Fr::one(), mono(&ring, &[0, 1])),
        ],
    );
    let gb = compute_gb(ring.clone(), vec![f1, f2]);
    assert_eq!(gb.len(), 2, "GB([x+y, x-y]) must have exactly 2 generators");

    let mut lm_exps: Vec<Vec<u32>> = gb
        .iter()
        .map(|g| g.leading().unwrap().1.exponents(&ring))
        .collect();
    lm_exps.sort();
    assert_eq!(
        lm_exps,
        vec![vec![0, 1], vec![1, 0]],
        "leading monomials must be {{y, x}}"
    );

    // Each generator is a single monic term (linear, no constant).
    for g in &gb {
        let terms: Vec<_> = g.iter().collect();
        assert_eq!(terms.len(), 1, "{g:?} should be a single monic monomial");
        assert_eq!(terms[0].0, Fr::one(), "leading coeff must be 1");
    }
}

/// `compute_gb` of the singleton input `[xy - 1]` is `[xy - 1]`
/// itself: a single generator forms its own (already reduced) GB.
#[test]
fn singleton_xy_minus_1_is_self_gb() {
    let ring = Arc::new(Ring::<Fr>::new(2).unwrap());
    let f = Poly::<Fr, GrevLexTerm>::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 1])),
            (-Fr::one(), mono(&ring, &[0, 0])),
        ],
    );
    let gb = compute_gb(ring.clone(), vec![f]);
    assert_eq!(gb.len(), 1);
    let terms: Vec<_> = gb[0].iter().collect();
    assert_eq!(terms.len(), 2);
    // Leading term: xy with coeff 1.
    let (c0, m0) = terms[0];
    assert_eq!(m0.exponents(&ring), vec![1, 1]);
    assert_eq!(c0, Fr::one());
    // Trailing term: constant -1.
    let (c1, m1) = terms[1];
    assert_eq!(m1.exponents(&ring), vec![0, 0]);
    assert_eq!(c1, -Fr::one());
}

// (Fr already provides Neg via ark_ff.)
