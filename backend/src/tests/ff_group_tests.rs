//! The `ff`/`group` adapter against arkworks: Ristretto's scalar field is
//! `ark_curve25519::Fr` and Pallas's is `ark_pallas::Fr`, so every field operation and
//! encoding must agree with arkworks' on the same integers.

use crate::algebra::radix2;
use crate::ff_group::{DalekMsm, FfPoint, FfScalar, Msm, Pippenger};
use crate::{Backend, DalekRistretto, Field, Group, PastaPallas};
use ark_std::test_rng;

/// `x` (any field) as the arkworks field `A` of the same modulus, by canonical bytes.
fn to_ark<F: Field, A: ark_ff::PrimeField>(x: &F) -> A {
    let mut bytes = Vec::new();
    x.write_bytes(&mut bytes);
    A::from_le_bytes_mod_order(&bytes)
}

fn agrees_with_arkworks<C: Backend, A: ark_ff::PrimeField>() {
    let mut rng = test_rng();
    let ark = |x: &C::F| to_ark::<C::F, A>(x);
    for _ in 0..50 {
        let (x, y) = (C::F::rand(&mut rng), C::F::rand(&mut rng));
        assert_eq!(ark(&(x + y)), ark(&x) + ark(&y));
        assert_eq!(ark(&(x - y)), ark(&x) - ark(&y));
        assert_eq!(ark(&(x * y)), ark(&x) * ark(&y));
        assert_eq!(ark(&-x), -ark(&x));
        assert_eq!(
            ark(&x.inverse().unwrap()),
            ark_ff::Field::inverse(&ark(&x)).unwrap()
        );
        assert_eq!(ark(&x.pow(12345)), ark_ff::Field::pow(&ark(&x), [12345]));
        // Canonical bytes round-trip through arkworks unchanged.
        let mut ours = Vec::new();
        x.write_bytes(&mut ours);
        let mut theirs = Vec::new();
        ark_serialize::CanonicalSerialize::serialize_compressed(&ark(&x), &mut theirs).unwrap();
        assert_eq!(ours, theirs);
    }
    assert!(C::F::zero().inverse().is_none());
    // The challenge and literal reduction: 32 bytes and 33 bytes (above the modulus).
    for len in [1, 8, 31, 32, 33, 64] {
        let bytes: Vec<u8> = (0..len).map(|i| (i * 37 + 11) as u8).collect();
        assert_eq!(
            ark(&C::F::from_le_bytes_mod_order(&bytes)),
            A::from_le_bytes_mod_order(&bytes),
            "{len} bytes"
        );
    }
    assert_eq!(C::F::TWO_ADICITY, <A as ark_ff::FftField>::TWO_ADICITY);
    for log_n in 0..=C::F::TWO_ADICITY {
        let root = C::F::two_adic_root(log_n).unwrap();
        assert!(root.pow(1 << log_n).is_one(), "2^{log_n}-th root");
        if log_n > 0 {
            assert!(
                !root.pow(1 << (log_n - 1)).is_one(),
                "primitive 2^{log_n}-th root"
            );
        }
    }
    assert!(C::F::two_adic_root(C::F::TWO_ADICITY + 1).is_none());
}

#[test]
fn ristretto_scalars_agree_with_arkworks() {
    agrees_with_arkworks::<DalekRistretto, ark_curve25519::Fr>();
}

#[test]
fn pallas_scalars_agree_with_arkworks() {
    agrees_with_arkworks::<PastaPallas, ark_pallas::Fr>();
}

/// Each MSM (dalek's and the generic Pippenger, on Ristretto; Pippenger on Pallas) is
/// the sum of the products, for sizes across Pippenger's window choices.
#[test]
fn msm_is_the_sum_of_products() {
    fn check<G: group::Group + group::GroupEncoding, M: Msm<G>>() {
        let mut rng = test_rng();
        for n in [0, 1, 2, 31, 32, 100, 600] {
            let bases: Vec<FfPoint<G, M>> = (0..n).map(|_| Group::rand(&mut rng)).collect();
            let scalars: Vec<FfScalar<G::Scalar>> = (0..n).map(|_| Field::rand(&mut rng)).collect();
            let naive = bases
                .iter()
                .zip(&scalars)
                .fold(FfPoint::zero(), |acc, (b, s)| acc + *b * *s);
            assert_eq!(FfPoint::msm(&bases, &scalars), naive, "n = {n}");
        }
    }
    check::<curve25519_dalek::RistrettoPoint, DalekMsm>();
    check::<curve25519_dalek::RistrettoPoint, Pippenger>();
    check::<pasta_curves::pallas::Point, Pippenger>();
}

/// Pallas's scalar field has 2-adicity 32, so the generic radix-2 FFT runs on it and
/// inverts.
#[test]
fn radix2_fft_inverts_on_pallas() {
    type F = <PastaPallas as Backend>::F;
    let mut rng = test_rng();
    for log_n in 0..=8 {
        let a: Vec<F> = (0..1 << log_n).map(|_| F::rand(&mut rng)).collect();
        let mut v = a.clone();
        radix2(&mut v, false);
        // The first evaluation is the sum of the coefficients (at x = 1).
        assert_eq!(v[0], a.iter().copied().sum::<F>());
        radix2(&mut v, true);
        assert_eq!(v, a, "n = 2^{log_n}");
    }
}

/// Every shipped backend passes the conformance check a new backend is held to.
#[test]
fn every_backend_conforms() {
    use crate::conformance::check_backend;
    use crate::*;
    let mut rng = test_rng();
    check_backend::<ArkBls12_381, _>(&mut rng);
    check_backend::<ArkBn254, _>(&mut rng);
    check_backend::<ArkMNT4_298, _>(&mut rng);
    check_backend::<ArkCurve25519, _>(&mut rng);
    check_backend::<ArkEd25519, _>(&mut rng);
    check_backend::<ArkSecp256k1, _>(&mut rng);
    check_backend::<ArkPallas, _>(&mut rng);
    check_backend::<ArkVesta, _>(&mut rng);
    check_backend::<ArkField65537, _>(&mut rng);
    check_backend::<DalekRistretto, _>(&mut rng);
    check_backend::<PastaPallas, _>(&mut rng);
}
