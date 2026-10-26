//! The transcript encoding of every `Value` variant, pinned: prover and
//! verifier absorb these bytes, so a change to them changes every challenge.

use crate::backends::{ArkBls12_381, ArkSecp256k1, Backend};
use crate::poly::variant::{DenseMle, DenseUni, Multivariate, SparseUni, Term};
use crate::{Group, Pairing, PolyVariant, Value, VirtualPolynomial, value_to_bytes};
use share::Ctx;
use std::fmt::Write;

fn f<C: Backend>(i: u64) -> C::F {
    C::F::from(i)
}

/// One polynomial of each encoding, plus a product that does not normalize
/// (the explicit sum-of-products encoding).
fn polys<C: Backend>() -> Vec<(&'static str, VirtualPolynomial<C::F>)> {
    let dense_uni = PolyVariant::DenseUni(DenseUni::new(vec![f::<C>(1), f::<C>(2), f::<C>(3)]));
    let sparse_uni = PolyVariant::SparseUni(SparseUni::new(vec![(0, f::<C>(1)), (5, f::<C>(2))]));
    let dense_mle = PolyVariant::DenseMle(DenseMle::new(2, (1..=4).map(f::<C>).collect()));
    let sparse_mle = PolyVariant::SparseMle {
        num_vars: 3,
        evals: vec![(1, f::<C>(7)), (6, f::<C>(9))],
    };
    let multivariate = PolyVariant::SparseMultivariate(Multivariate::new(
        2,
        vec![
            (f::<C>(3), Term::new(vec![(0, 2), (1, 1)])),
            (f::<C>(4), Term::new(vec![])),
        ],
    ));
    let mle = VirtualPolynomial::from_poly(dense_mle.clone());
    let product = mle.poly_mul(&mle);
    vec![
        ("poly_dense_uni", VirtualPolynomial::from_poly(dense_uni)),
        ("poly_sparse_uni", VirtualPolynomial::from_poly(sparse_uni)),
        ("poly_dense_mle", mle),
        ("poly_sparse_mle", VirtualPolynomial::from_poly(sparse_mle)),
        (
            "poly_multivariate",
            VirtualPolynomial::from_poly(multivariate),
        ),
        ("poly_product", product),
    ]
}

/// Every variant a pairing-free backend can hold.
fn group_values<C: Backend>() -> Vec<(&'static str, Value<C>)> {
    let g1 = C::G1::generator() * f::<C>(3);
    let g2 = C::G2::generator() * f::<C>(4);
    let mut record = Ctx::new();
    record.insert(&"a".to_string(), &Value::Scalar(f::<C>(5)));
    record.insert(&"b".to_string(), &Value::Bool(true));
    let mut values = vec![
        ("index", Value::Index(7)),
        ("scalar", Value::Scalar(f::<C>(5))),
        ("vec_index", Value::VecIndex(vec![1, 2, 3].into())),
        (
            "vec_scalar",
            Value::VecScalar((1..=3).map(f::<C>).collect::<Vec<_>>().into()),
        ),
        ("g1", Value::g1(g1)),
        ("g2", Value::g2(g2)),
        ("vec_g1", Value::vec_g1(vec![g1, g1 + g1])),
        ("vec_g2", Value::vec_g2(vec![g2, g2 + g2])),
        ("g1_affine", Value::g1_affine(g1.normalize())),
        ("g2_affine", Value::g2_affine(g2.normalize())),
        (
            "vec_g1_affine",
            Value::vec_g1_affine(vec![g1.normalize(), (g1 + g1).normalize()]),
        ),
        (
            "vec_g2_affine",
            Value::vec_g2_affine(vec![g2.normalize(), (g2 + g2).normalize()]),
        ),
        (
            "vec",
            Value::Vec(vec![Value::Scalar(f::<C>(2)), Value::Index(3)].into()),
        ),
        ("record", Value::Record(record)),
        ("unit", Value::Unit),
        ("bool", Value::Bool(true)),
    ];
    values.extend(polys::<C>().into_iter().map(|(n, p)| (n, Value::poly(p))));
    values
}

/// The pairing variants.
fn pairing_values<C: Backend>() -> Vec<(&'static str, Value<C>)> {
    let g1 = C::G1::generator() * f::<C>(3);
    let g2 = C::G2::generator() * f::<C>(4);
    let gt = C::P::pairing(&g1, &g2);
    vec![
        ("gt", Value::gt(gt)),
        ("vec_gt", Value::vec_gt(vec![gt, gt + gt])),
        (
            "vec_g2_prepared",
            Value::vec_g2_key(vec![g2.normalize(), (g2 + g2).normalize()]),
        ),
    ]
}

fn render<C: Backend>(values: Vec<(&'static str, Value<C>)>) -> String {
    let mut out = String::new();
    for (name, value) in values {
        let bytes = value_to_bytes(&value);
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        writeln!(out, "{name}: {hex}").unwrap();
    }
    out
}

#[test]
fn transcript_bytes_bls12_381() {
    let mut values = group_values::<ArkBls12_381>();
    values.extend(pairing_values::<ArkBls12_381>());
    insta::assert_snapshot!(render(values));
}

#[test]
fn transcript_bytes_secp256k1() {
    insta::assert_snapshot!(render(group_values::<ArkSecp256k1>()));
}

/// Sparse multivariate polynomials with the same terms over different
/// variable counts are different polynomials: equality must agree with the
/// hash and the order, which both read the variable count.
#[test]
fn multivariates_over_different_variable_counts_differ() {
    type F = <ArkBls12_381 as Backend>::F;
    let terms = vec![(F::from(3u64), Term::new(vec![(0, 1)]))];
    let two = PolyVariant::SparseMultivariate(Multivariate::new(2, terms.clone()));
    let three = PolyVariant::SparseMultivariate(Multivariate::new(3, terms));
    assert_ne!(two, three);
    assert_ne!(two.cmp(&three), std::cmp::Ordering::Equal);
}
