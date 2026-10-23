//! The laws and encoding contracts Zippel relies on, checked on random elements for every
//! shipped backend; each check panics, naming the property, at the first one that fails.

use crate::algebra::{Field, Group, Pairing};
use crate::backends::Backend;
use rand::Rng;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Random elements each property is checked on.
const SAMPLES: usize = 16;

fn hash_of<T: Hash>(x: &T) -> u64 {
    let mut h = DefaultHasher::new();
    x.hash(&mut h);
    h.finish()
}

fn bytes<T>(x: &T, write: impl Fn(&T, &mut Vec<u8>)) -> Vec<u8> {
    let mut out = Vec::new();
    write(x, &mut out);
    out
}

/// Checks every property of `C`'s field, of its groups when it has them, and of its
/// pairing when it has one.
///
/// # Panics
/// At the first property that fails.
fn check_backend<C: Backend, R: Rng + ?Sized>(rng: &mut R) {
    check_field::<C::F, R>(rng);
    if C::HAS_GROUP {
        check_group::<C::G1, R>(rng);
        check_group::<C::G2, R>(rng);
    }
    if C::HAS_PAIRING {
        check_pairing::<C::P, R>(rng);
    }
    if C::HAS_GROUP {
        check_keys::<C, R>(rng);
    }
    check_analysis_twin::<C>();
}

/// The backend's analysis twin has its scalar field and its capabilities: the two
/// fields' canonical encodings of `-1` (that is, of `p - 1`) agree.
fn check_analysis_twin<C: Backend>() {
    type A<C> = <C as Backend>::Analysis;
    assert_eq!(
        bytes(&-C::F::one(), C::F::write_bytes),
        bytes(
            &-<A<C> as Backend>::F::one(),
            <A<C> as Backend>::F::write_bytes
        ),
        "the analysis twin has the same modulus"
    );
    assert_eq!(
        (C::HAS_GROUP, C::HAS_PAIRING),
        (A::<C>::HAS_GROUP, A::<C>::HAS_PAIRING),
        "the analysis twin has the same capabilities"
    );
}

/// Every bulk operation equals the plain one when given the key the backend prepares:
/// for the whole vector, for a view of part of it, and for a key concatenated from two
/// views.
///
/// # Panics
/// At the first property that fails.
fn check_keys<C: Backend, R: Rng + ?Sized>(rng: &mut R) {
    use crate::backends::{G1Points, G2Points, Key};
    for n in [1, 5, 40] {
        let g1: Vec<C::G1> = (0..n).map(|_| C::G1::rand(rng)).collect();
        let g2: Vec<C::G2> = (0..n).map(|_| C::G2::rand(rng)).collect();
        let (a1, a2) = (C::G1::normalize_batch(&g1), C::G2::normalize_batch(&g2));
        let scalars: Vec<C::F> = (0..n).map(|_| C::F::rand(rng)).collect();
        let p1 = G1Points::<C>::keyed(a1.clone(), Key::prepare);
        let p2 = G2Points::<C>::keyed(a2.clone(), Key::prepare);
        for r in [0..n, n / 2..n] {
            let (v1, v2) = (p1.slice(r.clone()), p2.slice(r.clone()));
            assert_eq!(
                C::msm_g1(&v1, &scalars[r.clone()]),
                C::G1::msm(&a1[r.clone()], &scalars[r.clone()]),
                "G1 msm of a key"
            );
            assert_eq!(
                C::msm_g2(&v2, &scalars[r.clone()]),
                C::G2::msm(&a2[r.clone()], &scalars[r.clone()]),
                "G2 msm of a key"
            );
            if C::HAS_PAIRING {
                assert_eq!(
                    C::multi_pairing(&g1[r.clone()], &v2),
                    C::P::multi_pairing(&g1[r.clone()], &g2[r]),
                    "multi-pairing with a key"
                );
            }
        }
        let (front, back) = (p2.slice(n / 2..n), p2.slice(0..n / 2));
        if C::HAS_PAIRING
            && let (Some(f), Some(b)) = (front.key(), back.key())
            && let Some(joined) = f.key.concat(f.view, b.key, b.view)
        {
            let order: Vec<usize> = (n / 2..n).chain(0..n / 2).collect();
            let (o1, o2): (Vec<_>, Vec<_>) = order.iter().map(|&i| (g1[i], g2[i])).unzip();
            let affine: Vec<_> = order.iter().map(|&i| a2[i]).collect();
            let concatenated = G2Points::<C>::keyed(affine, |_| Some(joined));
            assert_eq!(
                C::multi_pairing(&o1, &concatenated),
                C::P::multi_pairing(&o1, &o2),
                "multi-pairing with a concatenated key"
            );
        }
    }
}

/// The field laws, and the contracts of [`Field`]'s methods.
///
/// # Panics
/// At the first property that fails.
fn check_field<F: Field, R: Rng + ?Sized>(rng: &mut R) {
    let (zero, one) = (F::zero(), F::one());
    assert!(
        zero.is_zero() && !one.is_zero() && one.is_one(),
        "zero and one"
    );
    assert!(zero.inverse().is_none(), "zero has no inverse");
    let width = bytes(&zero, F::write_bytes).len();
    for _ in 0..SAMPLES {
        let (a, b, c) = (F::rand(rng), F::rand(rng), F::rand(rng));
        assert_eq!(a + b, b + a, "addition commutes");
        assert_eq!((a + b) + c, a + (b + c), "addition associates");
        assert_eq!(a * (b + c), a * b + a * c, "multiplication distributes");
        assert_eq!((a + b) - b, a, "subtraction");
        assert_eq!(a + -a, zero, "negation");
        assert_eq!(a * one, a, "one is the identity");
        if let Some(inv) = a.inverse() {
            assert_eq!(a * inv, one, "inverse");
        }
        assert_eq!(a.pow(5), a * a * a * a * a, "pow");
        assert_eq!(a.pow(0), one, "pow 0");
        let (ab, ba) = (bytes(&a, F::write_bytes), bytes(&b, F::write_bytes));
        assert_eq!(ab.len(), width, "encodings have one width");
        assert_eq!(ab == ba, a == b, "the encoding is canonical");
        assert_eq!(
            a.cmp_canonical(&b) == Ordering::Equal,
            a == b,
            "the order is consistent with equality"
        );
        assert_eq!(
            a.cmp_canonical(&b),
            b.cmp_canonical(&a).reverse(),
            "the order is antisymmetric"
        );
        assert_eq!(a == b, hash_of(&a) == hash_of(&b), "hash follows equality");
    }
    for x in [0u64, 1, 2, 255, 256, 65537, u64::MAX] {
        assert_eq!(
            F::from_le_bytes_mod_order(&x.to_le_bytes()),
            F::from(x),
            "bytes {x} as a field element"
        );
    }
    // 2^256, reduced: (2^128)^2.
    let mut big = vec![0u8; 33];
    big[32] = 1;
    let two_128 = F::from(1u64 << 63) * F::from(1u64 << 63) * F::from(4);
    assert_eq!(
        F::from_le_bytes_mod_order(&big),
        two_128 * two_128,
        "bytes above the modulus are reduced"
    );
    for log_n in 0..=F::TWO_ADICITY.min(12) {
        let root = F::two_adic_root(log_n)
            .unwrap_or_else(|| panic!("a 2^{log_n}-th root, within TWO_ADICITY"));
        assert!(root.pow(1 << log_n).is_one(), "a 2^{log_n}-th root");
        if log_n > 0 {
            assert!(
                !root.pow(1 << (log_n - 1)).is_one(),
                "a primitive 2^{log_n}-th root"
            );
        }
    }
    assert!(
        F::two_adic_root(F::TWO_ADICITY + 1).is_none(),
        "no root above TWO_ADICITY"
    );
    for log_n in 0..=F::TWO_ADICITY.min(6) {
        let a: Vec<F> = (0..1 << log_n).map(|_| F::rand(rng)).collect();
        let mut v = a.clone();
        F::fft(&mut v);
        assert_eq!(v[0], a.iter().copied().sum::<F>(), "fft at 1 is the sum");
        F::ifft(&mut v);
        assert_eq!(v, a, "ifft inverts fft, n = 2^{log_n}");
    }
}

/// The group laws, and the contracts of [`Group`]'s methods.
///
/// # Panics
/// At the first property that fails.
fn check_group<G: Group, R: Rng + ?Sized>(rng: &mut R) {
    let zero = G::zero();
    assert!(
        zero.is_zero() && !G::generator().is_zero(),
        "zero and generator"
    );
    for _ in 0..SAMPLES {
        let (p, q) = (G::rand(rng), G::rand(rng));
        let (a, b) = (G::Scalar::rand(rng), G::Scalar::rand(rng));
        assert_eq!(p + q, q + p, "addition commutes");
        assert_eq!(p + zero, p, "zero is the identity");
        assert_eq!((p + q) - q, p, "subtraction");
        assert_eq!(p + -p, zero, "negation");
        assert_eq!(
            p * (a + b),
            p * a + p * b,
            "scalar multiplication distributes"
        );
        assert_eq!((p * a) * b, p * (a * b), "scalar multiplication associates");
        assert_eq!(
            Into::<G>::into(p.normalize()),
            p,
            "normalizing keeps the element"
        );
        let mut r = p;
        r.add_affine(&q.normalize());
        assert_eq!(r, p + q, "add_affine");
        assert_eq!(
            bytes(&p, G::write_bytes),
            bytes(&p.normalize(), G::write_affine_bytes),
            "both forms encode alike"
        );
        assert_eq!(
            bytes(&p, G::write_bytes) == bytes(&q, G::write_bytes),
            p == q,
            "the encoding is canonical"
        );
    }
    for n in [0, 1, 2, 33, 300] {
        let bases: Vec<G> = (0..n).map(|_| G::rand(rng)).collect();
        let scalars: Vec<G::Scalar> = (0..n).map(|_| G::Scalar::rand(rng)).collect();
        let affine = G::normalize_batch(&bases);
        assert_eq!(
            affine,
            bases.iter().map(G::normalize).collect::<Vec<_>>(),
            "normalize_batch"
        );
        let naive = bases
            .iter()
            .zip(&scalars)
            .fold(zero, |acc, (p, s)| acc + *p * *s);
        assert_eq!(G::msm(&affine, &scalars), naive, "msm of {n}");
        if let Some(p) = bases.first() {
            let products: Vec<G> = scalars.iter().map(|s| *p * *s).collect();
            assert_eq!(
                p.batch_mul(&scalars),
                G::normalize_batch(&products),
                "batch_mul"
            );
        }
    }
}

/// Bilinearity, and that the batched pairings agree with single ones.
///
/// # Panics
/// At the first property that fails.
fn check_pairing<P: Pairing, R: Rng + ?Sized>(rng: &mut R) {
    type S<P> = <<P as Pairing>::G1 as Group>::Scalar;
    let (p, q) = (P::G1::rand(rng), P::G2::rand(rng));
    let (a, b) = (S::<P>::rand(rng), S::<P>::rand(rng));
    let e = P::pairing(&p, &q);
    assert!(!e.is_zero(), "non-degenerate");
    assert_eq!(P::pairing(&(p * a), &(q * b)), e * (a * b), "bilinear");
    let a1: Vec<P::G1> = (0..3).map(|_| P::G1::rand(rng)).collect();
    let b2: Vec<P::G2> = (0..3).map(|_| P::G2::rand(rng)).collect();
    let sum = a1
        .iter()
        .zip(&b2)
        .fold(P::GT::zero(), |acc, (x, y)| acc + P::pairing(x, y));
    assert_eq!(P::multi_pairing(&a1, &b2), sum, "multi_pairing is the sum");
    assert_eq!(
        P::pairings(&a1, &b2)
            .into_iter()
            .fold(P::GT::zero(), |x, y| x + y),
        sum,
        "pairings"
    );
}

#[test]
fn every_backend_satisfies_the_laws() {
    use crate::*;
    let mut rng = ark_std::test_rng();
    check_backend::<ArkBls12_381, _>(&mut rng);
    check_backend::<ArkBn254, _>(&mut rng);
    check_backend::<ArkMNT4_298, _>(&mut rng);
    check_backend::<ArkCurve25519, _>(&mut rng);
    check_backend::<ArkEd25519, _>(&mut rng);
    check_backend::<ArkSecp256k1, _>(&mut rng);
    check_backend::<ArkPallas, _>(&mut rng);
    check_backend::<ArkVesta, _>(&mut rng);
    check_backend::<DalekRistretto, _>(&mut rng);
    check_backend::<ArkFrRistretto, _>(&mut rng);
    check_backend::<PastaPallas, _>(&mut rng);
}
