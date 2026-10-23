use crate::poly::variant::{DenseMle, DenseUni, Multivariate, SparseUni, Term};
use crate::{PolyVariant, VirtualPolynomial};
use ark_bls12_381::Fr;
use ark_ff::{One, Zero};
use ark_poly::{
    DenseMultilinearExtension, DenseUVPolynomial, MultilinearExtension, Polynomial,
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
};
use ark_std::{UniformRand, test_rng};
use std::cmp::Ordering;

fn rand_vec(n: usize) -> Vec<Fr> {
    let mut rng = test_rng();
    (0..n).map(|_| Fr::rand(&mut rng)).collect()
}

fn dense_mle(nv: usize) -> DenseMle<Fr> {
    DenseMle::new(nv, rand_vec(1 << nv))
}

/// Fixing and evaluating agree with arkworks on both sides of the parallel
/// threshold (2^10), for every number of fixed variables.
#[test]
fn fixing_a_dense_mle_matches_arkworks() {
    for nv in [0, 1, 2, 5, 11, 12] {
        let evals = rand_vec(1 << nv);
        let mle = DenseMultilinearExtension::from_evaluations_vec(nv, evals.clone());
        let point = rand_vec(nv);
        let poly = PolyVariant::DenseMle(DenseMle::new(nv, evals));
        assert_eq!(
            poly.evaluate_mv(&point).unwrap(),
            mle.evaluate(&point),
            "nv = {nv}"
        );
        for k in 0..nv {
            assert_eq!(
                poly.evaluate_or_fix(&point[..k]).unwrap(),
                PolyVariant::DenseMle(DenseMle::new(
                    nv - k,
                    mle.fix_variables(&point[..k]).evaluations
                )),
                "nv = {nv}, k = {k}"
            );
        }
        assert_eq!(
            poly.evaluate_or_fix(&point).unwrap(),
            PolyVariant::from_scalar(mle.evaluate(&point))
        );
    }
}

/// A sparse multivariate polynomial fixes its leading variables: evaluating the rest at the
/// remaining coordinates gives the full evaluation, for every number of fixed variables.
#[test]
fn fixing_a_sparse_multivariate_polynomial_matches_full_evaluation() {
    let nv = 3;
    let c = rand_vec(5);
    let term = Term::new;
    let p = Multivariate::new(
        nv,
        vec![
            (c[0], term(vec![])),
            (c[1], term(vec![(0, 2)])),
            (c[2], term(vec![(0, 1), (2, 1)])),
            (c[3], term(vec![(1, 3), (2, 1)])),
            (c[4], term(vec![(0, 1), (1, 1), (2, 2)])),
        ],
    );
    let point = rand_vec(nv);
    let full = p.evaluate(&point);
    let poly = PolyVariant::SparseMultivariate(p);
    for k in 0..=nv {
        let fixed = poly.evaluate_or_fix(&point[..k]).unwrap();
        let value = if k == nv {
            fixed.to_scalar().expect("every variable fixed")
        } else {
            fixed.evaluate_mv(&point[k..]).unwrap()
        };
        assert_eq!(value, full, "k = {k}");
    }
}

/// A sparse MLE fixes and evaluates like its dense table, and a partial evaluation is encoded
/// by its density (`17` is listed twice).
#[test]
fn fixing_a_sparse_mle_matches_its_dense_table() {
    let nv = 6;
    let evals: Vec<(usize, Fr)> = [3usize, 17, 17, 40, 63]
        .iter()
        .zip(rand_vec(5))
        .map(|(&i, v)| (i, v))
        .collect();
    let sparse = PolyVariant::SparseMle {
        num_vars: nv,
        evals,
    };
    let dense = sparse.to_dense();
    let point = rand_vec(nv);
    assert_eq!(
        sparse.evaluate_mv(&point).unwrap(),
        dense.evaluate_mv(&point).unwrap()
    );
    for k in 0..=nv {
        let fixed = sparse.evaluate_or_fix(&point[..k]).unwrap();
        assert_eq!(
            fixed.to_dense(),
            dense.evaluate_or_fix(&point[..k]).unwrap(),
            "k = {k}"
        );
        if k < nv {
            assert_encoded_by_density(&fixed, nv - k);
        }
    }
}

/// `poly` is an MLE over `num_vars` variables encoded by density: a `SparseMle` (one entry
/// per index, in order, no zeros) filling at most a quarter of its indices, else a `DenseMle`.
fn assert_encoded_by_density(poly: &PolyVariant<Fr>, num_vars: usize) {
    match poly {
        PolyVariant::SparseMle { num_vars: n, evals } => {
            assert_eq!(*n, num_vars);
            assert!(
                evals.len() * 4 <= 1 << num_vars,
                "too full for sparse: {poly}"
            );
            assert!(
                evals.windows(2).all(|w| w[0].0 < w[1].0)
                    && evals.iter().all(|(_, v)| !v.is_zero()),
                "not canonical: {evals:?}"
            );
        }
        PolyVariant::DenseMle(mle) => {
            assert_eq!(mle.num_vars(), num_vars);
            let nonzero = mle.evals().iter().filter(|v| !v.is_zero()).count();
            assert!(
                nonzero * 4 > 1 << num_vars,
                "sparse enough to stay sparse: {poly}"
            );
        }
        other => panic!("not an MLE: {other}"),
    }
}

fn sparse(num_vars: usize, indices: &[usize]) -> PolyVariant<Fr> {
    PolyVariant::SparseMle {
        num_vars,
        evals: indices
            .iter()
            .copied()
            .zip(rand_vec(indices.len()))
            .collect(),
    }
}

/// Fixing one variable of a 40-variable MLE with three entries stays sparse: a dense result
/// would have 2^39 entries.
#[test]
fn fixing_a_large_sparse_mle_stays_sparse() {
    let poly = sparse(40, &[0, 5, 1 << 39]);
    let point = rand_vec(40);
    let fixed = poly.evaluate_or_fix(&point[..1]).unwrap();
    assert_encoded_by_density(&fixed, 39);
    assert_eq!(
        fixed.evaluate_mv(&point[1..]).unwrap(),
        poly.evaluate_mv(&point).unwrap()
    );
}

/// Direct accumulation still selects the output encoding after collisions, cancellation
/// and zero weights, including the quarter-full boundary.
#[test]
fn fixing_sparse_mles_preserves_sparsity_after_accumulation() {
    let one = Fr::one();
    let cases = [
        (
            vec![
                (0, one),
                (0, -one),
                (2, Fr::from(3)),
                (3, Fr::from(6)),
                (8, one),
                (8, -one),
                (24, one),
                (24, -one),
            ],
            Fr::from(2),
        ),
        ((0..8).map(|i| (2 * i + 1, one)).collect(), Fr::zero()),
        ((0..8).map(|i| (2 * i + 1, one)).collect(), Fr::from(2)),
        ((0..9).map(|i| (2 * i + 1, one)).collect(), Fr::from(2)),
    ];
    for (evals, point) in cases {
        let poly = PolyVariant::SparseMle { num_vars: 6, evals };
        let fixed = poly.evaluate_or_fix(&[point]).unwrap();
        assert_encoded_by_density(&fixed, 5);
        assert_eq!(
            fixed.to_dense(),
            poly.to_dense().evaluate_or_fix(&[point]).unwrap()
        );
    }
}

#[test]
fn sparse_result_encoding_depends_on_values_after_cancellation() {
    for nonzero in [0, 7, 64, 65] {
        let entries: Vec<_> = (0..nonzero)
            .map(|i| (i << 2, Fr::from((i + 1) as u64)))
            .collect();
        let mut padded = entries.clone();
        for i in 0..100 {
            let index = ((i * 17) % 256) << 2;
            padded.extend([(index, Fr::one()), (index, -Fr::one())]);
        }
        let restrict = |evals| {
            PolyVariant::SparseMle {
                num_vars: 10,
                evals,
            }
            .evaluate_or_fix(&[Fr::from(2), Fr::from(3)])
            .unwrap()
        };
        let result = restrict(entries);
        assert_eq!(result, restrict(padded));
        assert_encoded_by_density(&result, 8);
    }
}

#[test]
fn sparse_mle_weights_match_dense_restrictions() {
    for entries in [16, 300] {
        let poly = PolyVariant::SparseMle {
            num_vars: 12,
            evals: (0..entries)
                .flat_map(|i| {
                    let index = (i * 113) % (1 << 12);
                    let value = Fr::from((i + 1) as u64);
                    [(index, value), (index, -value), (index, value)]
                })
                .collect(),
        };
        let dense = poly.to_dense();
        let mut point = rand_vec(12);
        point[0] = Fr::zero();
        point[2] = Fr::one();
        for k in [2, 4, 6, 8, 10] {
            let fixed = poly.evaluate_or_fix(&point[..k]).unwrap();
            assert_encoded_by_density(&fixed, 12 - k);
            assert_eq!(
                fixed.to_dense(),
                dense.evaluate_or_fix(&point[..k]).unwrap()
            );
        }
        assert_eq!(
            poly.evaluate_mv(&point).unwrap(),
            dense.evaluate_mv(&point).unwrap()
        );
    }
}

#[test]
fn sparse_mle_restriction_keeps_large_domains_sparse() {
    let poly = sparse(60, &[0, 17, 1 << 59]);
    let point = rand_vec(60);
    for k in [4, 40] {
        let fixed = poly.evaluate_or_fix(&point[..k]).unwrap();
        let PolyVariant::SparseMle { evals, .. } = &fixed else {
            panic!("large sparse restriction allocated its domain");
        };
        assert!(evals.len() <= 3);
        assert_eq!(
            fixed.evaluate_mv(&point[k..]).unwrap(),
            poly.evaluate_mv(&point).unwrap()
        );
    }
}

/// A selected evaluation (`eval<range>`) of a sparse MLE matches its dense table's and is
/// encoded by density: few fixed variables leave a sparse result, many a dense one.
#[test]
fn restricting_a_sparse_mle_matches_its_dense_table() {
    use lang::typ::CRange;
    let nv = 8;
    let poly = sparse(nv, &[1, 2, 3, 40, 41, 200, 255]);
    let dense = poly.to_dense();
    for (free, fixed) in [
        (CRange::from_raw(0, 1, 7), 1),
        (CRange::from_raw(2, 1, 4), 6),
    ] {
        let point = rand_vec(fixed);
        let restricted = poly
            .fix_variables_except_range(nv, free.clone(), &point)
            .unwrap();
        assert_encoded_by_density(&restricted, free.len());
        assert_eq!(
            restricted.to_dense(),
            dense.fix_variables_except_range(nv, free, &point).unwrap()
        );
    }
}

/// A dense MLE whose free variables are the low ones, with its high variables fixed, agrees
/// with arkworks' full evaluation and with the general path of its sparse encoding, on both
/// sides of the parallel threshold (2^10), for every number of free variables.
#[test]
fn restricting_a_dense_mle_to_its_low_variables_matches_full_evaluation() {
    use lang::typ::CRange;
    for nv in [2, 5, 11, 12] {
        let evals = rand_vec(1 << nv);
        let mle = DenseMultilinearExtension::from_evaluations_vec(nv, evals.clone());
        let poly = PolyVariant::DenseMle(DenseMle::new(nv, evals.clone()));
        let entries: Vec<(usize, Fr)> = evals.into_iter().enumerate().collect();
        let sparse = PolyVariant::SparseMle {
            num_vars: nv,
            evals: entries,
        };
        let point = rand_vec(nv);
        for free in 1..nv {
            let range = CRange::from_raw(0, 1, free);
            let (low, high) = point.split_at(free);
            let restricted = poly
                .fix_variables_except_range(nv, range.clone(), high)
                .unwrap();
            assert_eq!(restricted.num_vars(), free, "nv = {nv}, free = {free}");
            assert_eq!(
                restricted.evaluate_mv(low).unwrap(),
                mle.evaluate(&point),
                "nv = {nv}, free = {free}"
            );
            assert_eq!(
                restricted.to_dense(),
                sparse
                    .fix_variables_except_range(nv, range, high)
                    .unwrap()
                    .to_dense(),
                "nv = {nv}, free = {free}"
            );
        }
    }
}

/// Adding a sparse MLE: to a sparse one stays sparse while it is, to a dense one is dense;
/// each matches the dense sum.
#[test]
fn adding_sparse_mles_matches_the_dense_sum() {
    let a = sparse(6, &[1, 9, 9, 33]);
    let b = sparse(6, &[9, 40]);
    let sum = a.poly_add(&b).unwrap();
    assert_encoded_by_density(&sum, 6);
    assert_eq!(
        sum.to_dense(),
        a.to_dense().poly_add(&b.to_dense()).unwrap()
    );
    let full = PolyVariant::DenseMle(dense_mle(6));
    for (x, y) in [(&a, &full), (&full, &a)] {
        assert_eq!(
            x.poly_add(y).unwrap(),
            x.to_dense().poly_add(&y.to_dense()).unwrap()
        );
    }
    assert_eq!(a.poly_add_scalar(Fr::zero()), a);
}

/// A product of a dense and a sparse MLE fixes its leading variables factor by factor: the
/// sparse factor stays sparse, and the product is never multiplied out (which fails for MLEs,
/// as Spartan's prover did). Evaluating the rest gives the product at the whole point.
#[test]
fn fixing_a_product_of_dense_and_sparse_mles_keeps_the_factors() {
    let nv = 4;
    let dense = PolyVariant::DenseMle(dense_mle(nv));
    let sparse = PolyVariant::SparseMle {
        num_vars: nv,
        evals: [1usize, 6, 6, 11, 15]
            .iter()
            .zip(rand_vec(5))
            .map(|(&i, v)| (i, v))
            .collect(),
    };
    let point = rand_vec(nv);
    let expected = dense.evaluate_mv(&point).unwrap() * sparse.evaluate_mv(&point).unwrap();
    let product =
        VirtualPolynomial::from_poly(dense).poly_mul(&VirtualPolynomial::from_poly(sparse));
    for k in 1..nv {
        let fixed = product.evaluate_or_fix(&point[..k]).unwrap();
        assert_eq!(fixed.evaluate_mv(&point[k..]).unwrap(), expected, "k = {k}");
    }
}

fn samples() -> Vec<PolyVariant<Fr>> {
    let coeffs = rand_vec(3);
    vec![
        PolyVariant::DenseUni(DenseUni::new(coeffs.clone())),
        PolyVariant::SparseUni(SparseUni::new(coeffs.iter().copied().enumerate().collect())),
        PolyVariant::DenseMle(dense_mle(2)),
        PolyVariant::DenseMle(dense_mle(3)),
        PolyVariant::SparseMle {
            num_vars: 3,
            evals: vec![(1, Fr::one()), (5, Fr::from(7u64))],
        },
        PolyVariant::SparseMle {
            num_vars: 3,
            evals: vec![(1, Fr::one()), (6, Fr::from(7u64))],
        },
    ]
}

/// Every encoding equals itself, and `cmp` is `Equal` exactly when `eq`
/// holds: `SparseMle` used to be unequal to itself, and sparse encodings
/// compared `Greater` than themselves.
#[test]
fn ordering_is_consistent_with_equality() {
    let polys = samples();
    for a in &polys {
        assert_eq!(a, &a.clone(), "{a}");
        for b in &polys {
            assert_eq!(a.cmp(b) == Ordering::Equal, a == b, "{a} vs {b}");
            assert_eq!(a.cmp(b), b.cmp(a).reverse(), "{a} vs {b}");
        }
    }
}

/// Owned `*` used to return the left operand unchanged.
#[test]
fn owned_multiplication_multiplies() {
    let x = VirtualPolynomial::from_poly(PolyVariant::from_coeffs(vec![Fr::from(1u64), Fr::one()]));
    let y = VirtualPolynomial::from_poly(PolyVariant::from_coeffs(vec![Fr::from(2u64), Fr::one()]));
    let product = x.clone() * y.clone();
    assert_eq!(product, &x * &y);
    let t = Fr::from(5u64);
    assert_eq!(product.evaluate_uv(&t), Fr::from(42u64));
}

fn ark_uni(p: &DenseUni<Fr>) -> DensePolynomial<Fr> {
    DensePolynomial::from_coefficients_slice(p.coeffs())
}

/// Products match arkworks on both sides of the schoolbook threshold, and with zero
/// factors; quotient and remainder match arkworks' division, also for a sparse divisor
/// (`x^n - 1`) and dense divisors with enough non-zero coefficients for Newton division.
#[test]
fn univariate_arithmetic_matches_arkworks() {
    let uni = |len: usize| DenseUni::new(rand_vec(len));
    for (a, b) in [(0, 5), (3, 4), (32, 40), (33, 33), (100, 300)] {
        let (a, b) = (uni(a), uni(b));
        assert_eq!(
            a.mul(&b).coeffs(),
            (&ark_uni(&a) * &ark_uni(&b)).coeffs.as_slice(),
            "{} x {}",
            a.coeffs().len(),
            b.coeffs().len()
        );
    }
    let mut vanishing = vec![Fr::zero(); 65];
    vanishing[0] = -Fr::one();
    vanishing[64] = Fr::one();
    // dekart's `V*(x) = 1 + x + ... + x^n`: dense, so long division would be quadratic.
    let v_star = DenseUni::new(vec![Fr::one(); 513]);
    for (a, b) in [
        (uni(10), uni(3)),
        (uni(3), uni(10)),
        (uni(700), uni(300)),
        (uni(200), DenseUni::new(vanishing)),
        (uni(1500), v_star),
    ] {
        let (q, r) = a.div_rem(&b).unwrap();
        let (aq, ar) = DenseOrSparsePolynomial::from(ark_uni(&a))
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(ark_uni(&b)))
            .unwrap();
        assert_eq!(q.coeffs(), aq.coeffs.as_slice());
        assert_eq!(r.coeffs(), ar.coeffs.as_slice());
    }
    assert!(uni(4).div_rem(&DenseUni::default()).is_none());
}

/// Each encoding has one representation per polynomial: trailing zeros dropped, sparse terms
/// sorted with like terms merged and zeros removed.
#[test]
fn constructors_canonicalize() {
    let [a, b] = [Fr::from(2u64), Fr::from(3u64)];
    assert_eq!(
        DenseUni::new(vec![a, b, Fr::zero()]),
        DenseUni::new(vec![a, b])
    );
    assert!(DenseUni::new(vec![Fr::zero()]).is_zero());
    assert_eq!(
        SparseUni::new(vec![(4, a), (1, b), (4, -a), (1, a)]).terms(),
        &[(1, a + b)]
    );
    assert_eq!(Term::new(vec![(2, 1), (0, 0), (2, 3)]).powers(), &[(2, 4)]);
    let p = Multivariate::new(
        3,
        vec![
            (a, Term::new(vec![(1, 1)])),
            (b, Term::new(vec![])),
            (-a, Term::new(vec![(1, 1)])),
        ],
    );
    assert_eq!(p.terms(), &[(b, Term::default())]);
    assert!(PolyVariant::DenseMle(DenseMle::new(2, vec![Fr::zero(); 4])).is_zero());
}
