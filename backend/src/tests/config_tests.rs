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
