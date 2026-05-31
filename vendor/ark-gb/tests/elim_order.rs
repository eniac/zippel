//! Tests for `OddElimTerm` (block elimination order).
//!
//! `OddElimTerm` eliminates odd-indexed variables: its `Ord` impl
//! first compares by total degree of the odd-indexed exponents, then
//! breaks ties with degrevlex on the full monomial.
//!
//! We exercise the smallest non-trivial case with `Fr[x, y]`
//! (var 0 = x, var 1 = y). Under `OddElimTerm`, var 1 (y) is
//! eliminated, so computing a GB should produce a polynomial
//! living entirely in `x` that generates the elimination ideal
//! `I ∩ Fr[x]`.

use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::compute_gb;
use ark_gb::monomial::{MonoTerm, Monomial, OddElimTerm};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

fn mono(ring: &Ring<Fr>, exps: &[u32]) -> OddElimTerm {
    OddElimTerm::from(MonoTerm::from_exponents(ring, exps).unwrap())
}

#[test]
fn elim_xy_minus_1_x_plus_y() {
    // Ring: Fr[x, y] with x = var 0, y = var 1.
    // OddElimTerm eliminates y (var 1).
    let ring = Arc::new(Ring::<Fr>::new(2).unwrap());

    // f1 = x*y - 1
    let f1 = Poly::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 1])),
            (-Fr::one(), mono(&ring, &[0, 0])),
        ],
    );
    // f2 = x + y
    let f2 = Poly::from_terms(
        &ring,
        vec![
            (Fr::one(), mono(&ring, &[1, 0])),
            (Fr::one(), mono(&ring, &[0, 1])),
        ],
    );

    let gb = compute_gb(ring.clone(), vec![f1, f2]);

    // The elimination ideal of (xy - 1, x + y) eliminating y is
    // (x² + 1). So we must find a generator whose every term has
    // y-exponent 0.
    let mut found_pure_x = false;
    for (i, p) in gb.iter().enumerate() {
        let exps = p
            .iter()
            .map(|(_, m)| m.exponents(&ring))
            .collect::<Vec<_>>();
        let pure_x = !exps.is_empty() && exps.iter().all(|e| e[1] == 0);
        if pure_x {
            found_pure_x = true;
            // The support should contain x^2 and a constant.
            assert!(
                exps.iter().any(|e| e[0] == 2 && e[1] == 0),
                "GB[{i}] is y-free but missing x^2 term: {exps:?}"
            );
            assert!(
                exps.iter().any(|e| e[0] == 0 && e[1] == 0),
                "GB[{i}] is y-free but missing constant term: {exps:?}"
            );
        }
    }
    assert!(
        found_pure_x,
        "OddElimTerm failed to produce a y-free generator; GB had {} polys",
        gb.len()
    );
}

#[test]
fn odd_elim_ordering_basic() {
    // With 3 vars [x0, x1, x2], OddElimTerm eliminates x1.
    // A monomial with higher x1-degree should sort higher.
    let ring = Ring::<Fr>::new(3).unwrap();
    let a = mono(&ring, &[0, 2, 0]); // x1^2: elim weight = 2
    let b = mono(&ring, &[3, 0, 0]); // x0^3: elim weight = 0
    assert!(a > b, "higher odd-var degree should sort greater");

    // Equal elim weight → falls back to degrevlex.
    let c = mono(&ring, &[2, 0, 0]); // elim weight = 0, deg = 2
    let d = mono(&ring, &[0, 0, 2]); // elim weight = 0, deg = 2
    // In degrevlex: x0^2 > x2^2 (lower last-var wins).
    assert!(c > d, "equal elim weight should fall back to degrevlex");
}
