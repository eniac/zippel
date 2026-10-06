use crate::config::ArkBls12_381;
use crate::{ArkConfig, ArkScalarOps};
use ark_bls12_381::Fr;
use ark_ff::Zero;
use ark_std::{UniformRand, test_rng};

type TestConfig = ArkBls12_381;
type FOps = <TestConfig as ArkConfig>::FOps;

/// `vec_div(f1, f2)` must leave `f2 = f1 / f2`, i.e. agree elementwise with the
/// scalar `div`. Regression test: the implementation used to batch-invert twice,
/// which is the identity, so it silently computed `f1 * f2` instead.
#[test]
fn vec_div_agrees_with_scalar_div() {
    let mut rng = test_rng();

    let f1: Vec<Fr> = (0..16).map(|_| Fr::rand(&mut rng)).collect();
    let f2: Vec<Fr> = (0..16)
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
    <FOps as ArkScalarOps<Fr>>::vec_div(&f1, &mut quotient);

    let mut expected = f2.clone();
    for (a, b) in f1.iter().zip(expected.iter_mut()) {
        <FOps as ArkScalarOps<Fr>>::div(a, b);
    }
    assert_eq!(quotient, expected);

    // The defining property: multiplying the quotient back by the divisor
    // recovers the dividend. The double-inversion bug fails this.
    let mut roundtrip = quotient;
    <FOps as ArkScalarOps<Fr>>::vec_mul(&f2, &mut roundtrip);
    assert_eq!(roundtrip, f1);
}

// Chunked pairing must equal one `multi_pairing` over all pairs, including at
// and around the chunk boundary and for no pairs at all.
#[test]
fn prepared_vec_dot_equals_multi_pairing() {
    use crate::config::{ArkBls12_381, ArkPairingOps};
    use ark_bls12_381::{Bls12_381, G1Projective, G2Projective};
    use ark_ec::pairing::Pairing;
    use ark_std::{UniformRand, test_rng};
    type C = ArkBls12_381;
    let mut rng = test_rng();
    for n in [0, 1, 31, 32, 33, 70] {
        let g1: Vec<G1Projective> = (0..n).map(|_| G1Projective::rand(&mut rng)).collect();
        let g2: Vec<G2Projective> = (0..n).map(|_| G2Projective::rand(&mut rng)).collect();
        let prepared: Vec<<Bls12_381 as Pairing>::G2Prepared> =
            g2.iter().map(|g| g.into()).collect();
        let chunked = <C as ArkConfig>::POps::billinear_vec_dot_prepared(&g1, &prepared);
        let whole = Bls12_381::multi_pairing(g1.clone(), g2.clone());
        assert_eq!(chunked, whole, "{n} pairs");
    }
}
