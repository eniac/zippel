use crate::algebra::{radix2, vec_div, vec_mul};
use crate::config::ArkBls12_381;
use crate::{Backend, Field, Group, Pairing};
use ark_bls12_381::{Bls12_381, Fr, G1Projective, G2Projective};
use ark_ec::pairing::Pairing as ArkPairingEngine;
use ark_std::test_rng;
use std::panic::catch_unwind;

type C = ArkBls12_381;
type P = <C as Backend>::P;

/// `vec_div(f1, f2)` must leave `f2 = f1 / f2`, i.e. agree elementwise with
/// scalar division. Regression test: the implementation used to batch-invert
/// twice, which is the identity, so it silently computed `f1 * f2` instead.
#[test]
fn vec_div_agrees_with_scalar_div() {
    let mut rng = test_rng();
    let f1: Vec<Fr> = (0..2500).map(|_| Fr::rand(&mut rng)).collect();
    let f2: Vec<Fr> = (0..2500)
        .map(|_| {
            loop {
                let x = Fr::rand(&mut rng);
                if !x.is_zero() {
                    break x;
                }
            }
        })
        .collect();

    let mut quotient = f2.clone();
    vec_div(&f1, &mut quotient).unwrap();
    let expected: Vec<Fr> = f1
        .iter()
        .zip(&f2)
        .map(|(a, b)| *a * b.inverse().unwrap())
        .collect();
    assert_eq!(quotient, expected);

    // The defining property: multiplying the quotient back by the divisor
    // recovers the dividend. The double-inversion bug fails this.
    let mut roundtrip = quotient;
    vec_mul(&f2, &mut roundtrip);
    assert_eq!(roundtrip, f1);

    let mut with_zero = f2.clone();
    with_zero[1234] = Fr::zero();
    let before = with_zero.clone();
    assert!(vec_div(&f1, &mut with_zero).is_err());
    assert_eq!(with_zero, before, "a failed division leaves the divisor");
}

/// The generic radix-2 FFT (the default `Field::fft`, used by backends with no
/// FFT of their own) agrees with arkworks' and inverts.
#[test]
fn radix2_fft_matches_arkworks() {
    let mut rng = test_rng();
    for log_n in 0..=10 {
        let a: Vec<Fr> = (0..1 << log_n).map(|_| Fr::rand(&mut rng)).collect();
        let mut ours = a.clone();
        radix2(&mut ours, false);
        let mut theirs = a.clone();
        Fr::fft(&mut theirs);
        assert_eq!(ours, theirs, "n = 2^{log_n}");
        radix2(&mut ours, true);
        assert_eq!(ours, a, "n = 2^{log_n}");
    }
}

/// `multi_pairing` is the sum of the pairings, with one final exponentiation.
#[test]
fn multi_pairing_matches_pairing_fold() {
    let mut rng = test_rng();
    for n in [0, 1, 2, 4] {
        let g1: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let g2: Vec<G2Projective> = (0..n).map(|_| G2Projective::rand(&mut rng)).collect();
        let reference = g1
            .iter()
            .zip(&g2)
            .fold(<P as Pairing>::GT::zero(), |acc, (a, b)| {
                acc + P::pairing(a, b)
            });
        assert_eq!(P::multi_pairing(&g1, &g2), reference, "{n} pairs");
    }
}

// Chunked pairing must equal one `multi_pairing` over all pairs, including at
// and around the chunk boundary and for no pairs at all.
#[test]
fn prepared_vec_dot_equals_multi_pairing() {
    let mut rng = test_rng();
    for n in [0, 1, 31, 32, 33, 70] {
        let g1: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let g2: Vec<G2Projective> = (0..n).map(|_| G2Projective::rand(&mut rng)).collect();
        let prepared: Vec<<Bls12_381 as ArkPairingEngine>::G2Prepared> =
            g2.iter().map(|g| g.into()).collect();
        let chunked = P::multi_pairing_prepared(&g1, &prepared);
        let whole = Bls12_381::multi_pairing(g1.clone(), g2.clone());
        assert_eq!(chunked, whole, "{n} pairs");
    }
}

// A length mismatch must panic, as `multi_pairing` does, whether or not the
// two sides fall into the same number of chunks: a zip of the chunks alone
// would drop the unmatched tail of (32, 33) or (32, 64), and return the
// identity for (0, n).
#[test]
fn prepared_vec_dot_rejects_unequal_lengths() {
    let mut rng = test_rng();
    for (n1, n2) in [
        (0, 1),
        (1, 0),
        (0, 40),
        (10, 20),
        (32, 33),
        (33, 32),
        (32, 64),
        (64, 32),
        (33, 64),
    ] {
        let g1: Vec<G1Projective> = (0..n1).map(|_| G1Projective::rand(&mut rng)).collect();
        let prepared: Vec<<Bls12_381 as ArkPairingEngine>::G2Prepared> = (0..n2)
            .map(|_| G2Projective::rand(&mut rng).into())
            .collect();
        let result = catch_unwind(|| P::multi_pairing_prepared(&g1, &prepared));
        assert!(result.is_err(), "({n1}, {n2}) pairs were accepted");
    }
}
