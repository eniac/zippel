//! The `ff`/`group` adapter against arkworks: Ristretto's scalar field is
//! `ark_curve25519::Fr` and Pallas's is `ark_pallas::Fr`, so every field operation and
//! encoding must agree with arkworks' on the same integers.

use crate::algebra::radix2;
use crate::backends::ff_group::{DalekMsm, FfPoint, FfScalar, Msm, Pippenger};
use crate::backends::hybrid::ArkFrRistrettoPoint;
use crate::{ArkFrRistretto, Backend, DalekRistretto, Field, Group, PastaPallas};
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

/// `ArkFrRistretto` hands dalek its arkworks scalars at each group operation: every
/// result must equal `DalekRistretto`'s for the same points and integers, byte for byte.
/// The group laws alone would not catch a bridge that maps scalars consistently wrong.
#[test]
fn ark_fr_ristretto_agrees_with_dalek() {
    type S = <ArkFrRistretto as Backend>::F;
    type D = <DalekRistretto as Backend>::G1;
    fn encoding<G: Group>(g: &G) -> Vec<u8> {
        let mut out = Vec::new();
        g.write_bytes(&mut out);
        out
    }
    let dalek = |s: &S| {
        let mut bytes = Vec::new();
        s.write_bytes(&mut bytes);
        <DalekRistretto as Backend>::F::from_le_bytes_mod_order(&bytes)
    };
    let mut rng = test_rng();
    let scalars: Vec<S> = [S::zero(), S::one(), -S::one()]
        .into_iter()
        .chain((0..20).map(|_| S::rand(&mut rng)))
        .collect();
    let bases = [D::generator(), D::rand(&mut rng)];
    for d in bases {
        let a = ArkFrRistrettoPoint::new(d.0);
        assert_eq!(encoding(&a), encoding(&d));
        for s in &scalars {
            assert_eq!(encoding(&(a * *s)), encoding(&(d * dalek(s))), "{s}");
            let mut assigned = a;
            assigned *= *s;
            assert_eq!(assigned, a * *s, "{s}");
        }
        let ours = a.batch_mul(&scalars);
        let theirs = d.batch_mul(&scalars.iter().map(dalek).collect::<Vec<_>>());
        assert_eq!(
            ours.iter().map(encoding).collect::<Vec<_>>(),
            theirs.iter().map(encoding).collect::<Vec<_>>()
        );
    }
    assert_eq!(
        ArkFrRistrettoPoint::generator(),
        ArkFrRistrettoPoint::new(D::generator().0)
    );
    for n in [0, 1, 2, 31, 100] {
        let bases: Vec<D> = (0..n).map(|_| D::rand(&mut rng)).collect();
        let scalars: Vec<S> = (0..n).map(|_| S::rand(&mut rng)).collect();
        let ours = ArkFrRistrettoPoint::msm(
            &bases
                .iter()
                .map(|d| ArkFrRistrettoPoint::new(d.0))
                .collect::<Vec<_>>(),
            &scalars,
        );
        let theirs = D::msm(&bases, &scalars.iter().map(dalek).collect::<Vec<_>>());
        assert_eq!(encoding(&ours), encoding(&theirs), "n = {n}");
    }
    assert!(ArkFrRistrettoPoint::msm(&[], &[]).is_zero());
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
