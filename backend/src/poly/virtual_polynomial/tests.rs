use super::rounds::trim_trailing_zero_coeffs;
use super::*;
use crate::poly::variant::DenseMle;
use crate::poly::variant::DenseUni;
use crate::{ArkBls12_381, Backend, Value};
use ark_bls12_381::Fr;
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use ark_std::test_rng;
use lang::typ::CRange;

/// A random dense univariate polynomial of degree `d`.
fn rand_uni(d: usize, rng: &mut impl ark_std::rand::Rng) -> DenseUni<Fr> {
    DenseUni::new((0..=d).map(|_| Fr::rand(rng)).collect())
}
use lang::ast::BinOp;

/// The multilinear round sum (evaluation form, one pass over the tails) equals the
/// interpolation oracle for every free variable: shared, sparse (duplicate index) and
/// constant factors, non-unit coefficients, below and above the parallel threshold.
#[test]
fn mle_round_sum_matches_interpolation() {
    let mut rng = test_rng();
    for nv in [3, 11] {
        let mut dense = || {
            VirtualPolynomial::from_poly(PolyVariant::DenseMle(DenseMle::new(
                nv,
                (0..1 << nv).map(|_| Fr::rand(&mut rng)).collect(),
            )))
        };
        let (f, g, h, k) = (dense(), dense(), dense(), dense());
        let mut rng = test_rng();
        let s = VirtualPolynomial::from_poly(PolyVariant::SparseMle {
            num_vars: nv,
            evals: vec![
                (0, Fr::from(3u64)),
                (5, Fr::rand(&mut rng)),
                (5, Fr::rand(&mut rng)),
                ((1 << nv) - 1, Fr::rand(&mut rng)),
            ],
        });
        let vp = f
            .poly_mul(&g)
            .poly_mul(&h)
            .poly_add(&f.poly_mul(&k).poly_mul_scalar(Fr::rand(&mut rng)))
            .poly_add(&s.poly_mul(&g).poly_mul_scalar(-Fr::one()))
            .poly_add_scalar(Fr::from(5u64));
        let tail = nv - 1;
        for free in 0..nv {
            let fast = vp
                .tail_sum_of_mle_products(free, tail, 1 << tail, 3)
                .unwrap();
            let mut oracle = vp.tail_sum_by_interpolation(free, tail, 1 << tail, 3);
            trim_trailing_zero_coeffs(&mut oracle);
            assert_eq!(fast, oracle, "nv = {nv}, free = {free}");
        }
    }
}

/// Normalizing a sum of multilinear terms and a constant sums them into one table,
/// encoded by the sum's density: `c1·f + c2·g + c3·s + 7` (sparse `s`) is one dense table
/// agreeing with the sum, and a sum of sparse tables stays sparse. Multiplying keeps the
/// terms: one product each.
#[test]
fn normalizing_sums_multilinear_terms_into_one_table() {
    let mut rng = test_rng();
    let nv = 4;
    let mut dense = || {
        PolyVariant::DenseMle(DenseMle::new(
            nv,
            (0..1 << nv).map(|_| Fr::rand(&mut rng)).collect(),
        ))
    };
    let (f, g, h) = (dense(), dense(), dense());
    let sparse = |i: usize, v: u64| PolyVariant::SparseMle {
        num_vars: nv,
        evals: vec![(i, Fr::from(v)), (i, Fr::from(v)), (15, Fr::from(1u64))],
    };
    let mut rng = test_rng();
    let (c1, c2, c3) = (Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng));
    let vp = |p: &PolyVariant<Fr>| VirtualPolynomial::from_poly(p.clone());
    let sum = vp(&f)
        .poly_mul_scalar(c1)
        .poly_add(&vp(&g).poly_mul_scalar(c2))
        .poly_add(&vp(&sparse(3, 2)).poly_mul_scalar(c3))
        .poly_add_scalar(Fr::from(7u64));
    assert_eq!(sum.poly_mul(&vp(&h)).products.len(), 4);
    let point: Vec<Fr> = (0..nv).map(|_| Fr::rand(&mut rng)).collect();
    let table = sum.normalize().unwrap();
    assert!(table.is_multilinear() && table.num_vars() == nv);
    assert_eq!(
        table.evaluate_mv(&point).unwrap(),
        sum.evaluate_mv(&point).unwrap()
    );
    let sparse_sum = vp(&sparse(3, 2)).poly_add(&vp(&sparse(5, 4)));
    let table = sparse_sum.normalize().unwrap();
    assert!(matches!(table, PolyVariant::SparseMle { .. }));
    assert_eq!(
        table.evaluate_mv(&point).unwrap(),
        sparse_sum.evaluate_mv(&point).unwrap()
    );
}

/// Reference oracle for the round/marginalize semantics, after HyperPlonk's
/// sumcheck prover: the explicit-round tests below check the production
/// paths against it. Not reachable from any language op.
fn marginalize<C: Backend>(
    poly: &VirtualPolynomial<C::F>,
    num_variables: usize,
    max_degree: usize,
    round: usize,
    challenge: Option<C::F>,
) -> (Vec<C::F>, VirtualPolynomial<C::F>) {
    #![allow(clippy::needless_range_loop)]
    // if self.round >= self.poly.aux_info.num_variables
    if num_variables == 0 {
        panic!("marginalize: num_variables must be > 0");
    }

    if let Some(n) = poly.num_vars() {
        let expected_current_vars = if round == 0 {
            num_variables
        } else {
            num_variables.saturating_sub(round - 1)
        };
        if n != expected_current_vars {
            panic!(
                "marginalize: num_variables mismatch: polynomial has {}, expected {} (num_variables={}, round={})",
                n, expected_current_vars, num_variables, round
            );
        }
    }

    // Step 1:
    // fix argument and evaluate f(x) over x_m = r; where r is the challenge
    // for the current round, and m is the round number, indexed from 1
    //
    // i.e.:
    // at round m <= n, for each mle g(x_1, ... x_n) within the flattened_mle
    // which has already been evaluated to g(r_1, ..., r_{m-1}, x_m ... x_n)
    //
    //    g(r_1, ..., r_{m-1}, x_m ... x_n)
    //
    // eval g over r_m, and mutate g to g(r_1, ... r_m, x_{m+1}... x_n)
    let next_poly = if round == 0 {
        poly.clone()
    } else if let Some(r) = challenge {
        poly.fix_first_mle_variables_factorwise(&[r])
            .unwrap_or_else(|e| {
                panic!(
                    "marginalize: failed to fix polynomial for round {} with challenge {:?} \
                     (num_variables={}, max_degree={}): {:?}",
                    round, r, num_variables, max_degree, e
                )
            })
    } else {
        poly.clone()
    };

    // Step 2: generate sum for the partial evaluated polynomial:
    // f(r_1, ... r_m, x_{m+1}... x_n); we sum over the hypercube for the remaining
    let num_remaining_vars = num_variables.saturating_sub(round + 1);
    let total: usize = 1usize << num_remaining_vars;
    let expected_mle_vars = num_variables.saturating_sub(round);

    let all_mle = next_poly
        .flattened_polys
        .iter()
        .all(|p| p.as_mle_evaluations().is_some());
    let mle_tables: Option<Vec<&[C::F]>> = if all_mle && !next_poly.flattened_polys.is_empty() {
        let tables: Vec<&[C::F]> = next_poly
            .flattened_polys
            .iter()
            .filter_map(|p| p.as_mle_evaluations())
            .collect();
        if tables.len() == next_poly.flattened_polys.len()
            && tables
                .iter()
                .all(|t| t.len() == (1usize << expected_mle_vars))
        {
            Some(tables)
        } else {
            None
        }
    } else {
        None
    };

    let mut evaluations = vec![C::F::zero(); max_degree + 1];

    if let Some(tables) = mle_tables {
        let mut products_sum = vec![C::F::zero(); max_degree + 1];

        for (coefficient, products) in &next_poly.products {
            let product_tables: Vec<&[C::F]> = products.iter().map(|&idx| tables[idx]).collect();
            let k = product_tables.len();

            let coeff_acc: Vec<C::F> = (0..total)
                .into_par_iter()
                .fold(
                    || (vec![C::F::zero(); k + 1], vec![C::F::zero(); k + 1]),
                    |(mut acc, mut coeffs), b| {
                        // P(t) = prod_i ((1-t)*v0_i + t*v1_i); coeffs of P (degree k).
                        coeffs[0] = C::F::one();
                        for c in &mut coeffs[1..] {
                            *c = C::F::zero();
                        }
                        for i in 0..k {
                            let v0_i = product_tables[i][2 * b];
                            let v1_i = product_tables[i][2 * b + 1];
                            let step = v1_i - v0_i;
                            for d in (1..=i + 1).rev() {
                                coeffs[d] = coeffs[d] * v0_i + coeffs[d - 1] * step;
                            }
                            coeffs[0] *= v0_i;
                        }
                        for (a, &c) in acc.iter_mut().zip(coeffs.iter()) {
                            *a += c;
                        }
                        (acc, coeffs)
                    },
                )
                .map(|(acc, _)| acc)
                .reduce(
                    || vec![C::F::zero(); k + 1],
                    |mut left, right| {
                        for (l, &r) in left.iter_mut().zip(right.iter()) {
                            *l += r;
                        }
                        left
                    },
                );

            for (ps, &acc) in products_sum.iter_mut().zip(coeff_acc.iter()) {
                *ps += *coefficient * acc;
            }
        }

        for t_idx in 0..=max_degree {
            let t = C::F::from_usize(t_idx);
            let mut val = C::F::zero();
            let mut t_pow = C::F::one();
            for d in 0..=max_degree {
                val += products_sum[d] * t_pow;
                t_pow *= t;
            }
            evaluations[t_idx] = val;
        }
    } else {
        let point_len = num_variables - round;
        for t_idx in 0..=max_degree {
            let t = C::F::from_usize(t_idx);
            let sum: C::F = (0..total)
                .into_par_iter()
                .map(|b| {
                    let mut point: Vec<C::F> = Vec::with_capacity(point_len);
                    point.push(t);
                    for j in 0..num_remaining_vars {
                        let bit = (b >> j) & 1;
                        point.push(if bit == 0 { C::F::zero() } else { C::F::one() });
                    }
                    next_poly
                        .evaluate_mv(&point)
                        .expect("marginalize: polynomial evaluation failed")
                })
                .sum();
            evaluations[t_idx] = sum;
        }
    }

    (evaluations, next_poly)
}

/// The polynomial of degree below `evals.len()` taking `evals[i]` at `i`.
fn round_from_evals(evals: &[Fr]) -> VirtualPolynomial<Fr> {
    let points: Vec<Fr> = (0..evals.len()).map(|i| Fr::from(i as u64)).collect();
    VirtualPolynomial::univariate(interpolate_univariate_from_points(&points, evals).unwrap())
}

/// `Value::eval` picks full evaluation over fixing variables by
/// `is_full_point`, so it must hold exactly when `evaluate_mv` succeeds.
#[test]
fn is_full_point_agrees_with_evaluate_mv() {
    let mut rng = test_rng();
    let mle = |nv: usize, rng: &mut _| {
        VirtualPolynomial::from_poly(PolyVariant::DenseMle(DenseMle::new(
            nv,
            (0..1 << nv).map(|_| Fr::rand(rng)).collect(),
        )))
    };
    let uni = VirtualPolynomial::from_poly(PolyVariant::DenseUni(rand_uni(3, &mut rng)));
    for poly in [mle(3, &mut rng), mle(1, &mut rng), mle(0, &mut rng), uni] {
        for len in 0..=4 {
            let point: Vec<Fr> = (0..len).map(|_| Fr::rand(&mut rng)).collect();
            assert_eq!(
                poly.is_full_point(len),
                poly.evaluate_mv(&point).is_ok(),
                "len = {len}"
            );
        }
    }
}

/// `sum_univariate_products_dense` sums large products in evaluation
/// form and small ones schoolbook; check both against a direct
/// Σ c·Π P expansion with ark-poly's own mul/add.
#[test]
fn sum_univariate_products_dense_matches_direct_expansion() {
    let mut rng = test_rng();
    for trial in 0..10 {
        let deg = |k: usize| 20 + (trial * 7 + k * 13) % 90;
        let polys: Vec<Arc<PolyVariant<Fr>>> = (0..5)
            .map(|k| Arc::new(PolyVariant::DenseUni(rand_uni(deg(k), &mut rng))))
            .collect();
        let small = Arc::new(PolyVariant::DenseUni(rand_uni(3, &mut rng)));
        // Two virtual polynomials sharing factor 0, as a reduce(+) sees them.
        let terms: Vec<Vec<_>> = vec![
            vec![
                (Fr::rand(&mut rng), vec![polys[0].clone(), polys[0].clone()]), // large square
                (Fr::rand(&mut rng), vec![polys[1].clone()]),                   // linear
                (Fr::rand(&mut rng), vec![]),                                   // scalar
            ],
            vec![
                (
                    Fr::rand(&mut rng),
                    vec![polys[0].clone(), polys[2].clone(), polys[3].clone()],
                ),
                (Fr::rand(&mut rng), vec![small.clone(), small.clone()]), // schoolbook path
                (Fr::rand(&mut rng), vec![polys[4].clone(), small.clone()]),
            ],
        ];
        let mut vps = Vec::new();
        let mut expected = DensePolynomial::<Fr>::from_coefficients_vec(vec![]);
        for vp_terms in &terms {
            let mut vp = VirtualPolynomial::new();
            for (c, factors) in vp_terms {
                vp.add_poly_list(factors.iter().cloned(), *c);
                let mut t = DensePolynomial::from_coefficients_vec(vec![*c]);
                for f in factors {
                    let PolyVariant::DenseUni(d) = &**f else {
                        unreachable!()
                    };
                    t = t.naive_mul(&DensePolynomial::from_coefficients_slice(d.coeffs()));
                }
                expected = &expected + &t;
            }
            vps.push(vp);
        }
        let got = VirtualPolynomial::sum_univariate_products_dense(&vps.iter().collect::<Vec<_>>())
            .unwrap();
        match got.normalize().unwrap() {
            PolyVariant::DenseUni(p) => {
                assert_eq!(p.coeffs(), expected.coeffs.as_slice(), "trial {trial}");
            }
            other => panic!("expected DenseUni, got {other:?}"),
        }
    }
}

#[test]
fn sum_univariate_products_dense_accepts_zero_factor() {
    let mut product = VirtualPolynomial::<Fr>::new();
    product.add_poly_list(
        [
            Arc::new(PolyVariant::DenseUni(DenseUni::new(vec![]))),
            Arc::new(PolyVariant::DenseUni(DenseUni::new(vec![
                Fr::one(),
                Fr::one(),
            ]))),
        ],
        Fr::one(),
    );
    let one = VirtualPolynomial::from_scalar(Fr::one());
    let sum = VirtualPolynomial::sum_univariate_products_dense(&[&product, &one]).unwrap();
    for x in [Fr::zero(), Fr::one(), Fr::from(7u64)] {
        assert_eq!(sum.evaluate_uv(&x), Fr::one());
    }
}

// ========== Test Helpers ==========
fn create_vp_from_scalar(val: u64) -> VirtualPolynomial<Fr> {
    VirtualPolynomial::from_scalar(Fr::from(val))
}

fn create_vp_from_poly_univariate(coeffs: Vec<u64>) -> VirtualPolynomial<Fr> {
    let coeffs_fr: Vec<Fr> = coeffs.iter().map(|&c| Fr::from(c)).collect();
    let poly = PolyVariant::DenseUni(DenseUni::new(coeffs_fr));
    VirtualPolynomial::from_poly(poly)
}

fn create_vp_from_mle(evals: Vec<u64>, num_vars: usize) -> VirtualPolynomial<Fr> {
    let evals_fr: Vec<Fr> = evals.iter().map(|&e| Fr::from(e)).collect();
    let mle = PolyVariant::DenseMle(DenseMle::new(num_vars, evals_fr));
    VirtualPolynomial::from_poly(mle)
}

fn assert_vp_eq(a: &VirtualPolynomial<Fr>, b: &VirtualPolynomial<Fr>, msg: &str) {
    // Evaluate at several random points to verify equality
    let mut rng = test_rng();
    for _ in 0..10 {
        let point = Fr::rand(&mut rng);
        let eval_a = a.evaluate_uv(&point);
        let eval_b = b.evaluate_uv(&point);
        assert_eq!(
            eval_a, eval_b,
            "{}: evaluation mismatch at point {:?}",
            msg, point
        );
    }
}

fn explicit_round_poly(poly: &VirtualPolynomial<Fr>, num_vars: usize) -> VirtualPolynomial<Fr> {
    let mut round_poly = VirtualPolynomial::new();
    for tail_index in 0..(1usize << (num_vars - 1)) {
        let tail: Vec<Fr> = (0..(num_vars - 1))
            .map(|j| Fr::from(((tail_index >> j) & 1) as u64))
            .collect();
        let selected = poly
            .fix_variables_except_range(CRange::singleton(0), &tail)
            .unwrap();
        round_poly = round_poly.poly_add(&selected);
    }
    round_poly
}

fn explicit_round_evals(
    poly: &VirtualPolynomial<Fr>,
    num_vars: usize,
    max_degree: usize,
) -> Vec<Fr> {
    let round_poly = explicit_round_poly(poly, num_vars);
    (0..=max_degree)
        .map(|t| round_poly.evaluate_uv(&Fr::from(t as u64)))
        .collect()
}

fn eval_coeffs(coeffs: &[Fr], point: Fr) -> Fr {
    coeffs
        .iter()
        .rev()
        .fold(Fr::zero(), |acc, coeff| acc * point + *coeff)
}

fn direct_unit_selected_coeffs(
    product: &VirtualPolynomial<Fr>,
    fixed_tail: &[Fr],
    degree: usize,
) -> Vec<Fr> {
    let points: Vec<Fr> = (0..=degree).map(|i| Fr::from(i as u64)).collect();
    let evals: Vec<Fr> = points
        .iter()
        .map(|t| {
            let mut point = Vec::with_capacity(1 + fixed_tail.len());
            point.push(*t);
            point.extend_from_slice(fixed_tail);
            product.evaluate_mv(&point).unwrap()
        })
        .collect();
    let mut coeffs = interpolate_univariate_from_points(&points, &evals).unwrap();
    trim_trailing_zero_coeffs(&mut coeffs);
    coeffs
}

#[test]
fn test_selected_unit_eval_matches_direct_evaluation_for_mle_product() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4], 2);
    let b = create_vp_from_mle(vec![5, 7, 11, 13], 2);
    let product = a.poly_mul(&b);
    let fixed_tail = vec![Fr::from(3u64)];

    let selected = product
        .fix_variables_except_range(CRange::singleton(0), &fixed_tail)
        .unwrap();

    for t in [0u64, 1, 2, 5] {
        let point = vec![Fr::from(t), fixed_tail[0]];
        let direct = product.evaluate_mv(&point).unwrap();
        let selected_eval = selected.evaluate_uv(&Fr::from(t));
        assert_eq!(selected_eval, direct, "selected eval mismatch at t={t}");
    }
}

#[test]
fn test_selected_unit_eval_of_mle_product_materializes_coefficient_univariate() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);
    let fixed_tail = vec![Fr::from(3u64), Fr::from(5u64)];

    let selected = product
        .fix_variables_except_range_with_shape(
            SelectedEvalShape::new(3, 1, 2),
            CRange::singleton(0),
            &fixed_tail,
        )
        .unwrap();

    assert_eq!(selected.num_vars(), Some(1));
    assert!(
        selected.flattened_polys.len() == 1
            && matches!(
                selected.flattened_polys[0].as_ref(),
                PolyVariant::DenseUni(_)
            ),
        "unit selected eval over MLE products must materialize a coefficient-compatible DenseUni"
    );
    let coeffs = selected
        .to_coeffs()
        .expect("unit selected eval must expose univariate coefficients");
    assert_eq!(
        coeffs,
        direct_unit_selected_coeffs(&product, &fixed_tail, 2)
    );

    for t in [0u64, 1, 2, 7] {
        let point = vec![Fr::from(t), fixed_tail[0], fixed_tail[1]];
        let direct = product.evaluate_mv(&point).unwrap();
        let selected_eval = selected.evaluate_uv(&Fr::from(t));
        assert_eq!(selected_eval, direct, "selected eval mismatch at t={t}");
        assert_eq!(
            eval_coeffs(&coeffs, Fr::from(t)),
            direct,
            "selected coefficients mismatch at t={t}"
        );
    }
}

#[test]
fn test_coef_after_unit_selected_eval_of_mle_product_returns_coefficients() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);
    let fixed_tail = vec![Fr::from(3u64), Fr::from(5u64)];

    let coeff_value = Value::<ArkBls12_381>::Poly(Arc::new(product.clone()))
        .value_eval_selected(
            CRange::singleton(0),
            Value::vec_scalar(fixed_tail.clone()),
            SelectedEvalShape::new(3, 1, 2),
        )
        .value_coef();

    let Value::VecScalar(coeffs) = coeff_value else {
        panic!("coef after unit selected eval should return VecScalar coefficients");
    };
    assert_eq!(
        coeffs,
        direct_unit_selected_coeffs(&product, &fixed_tail, 2)
    );

    for t in [0u64, 1, 2, 7] {
        let point = vec![Fr::from(t), fixed_tail[0], fixed_tail[1]];
        let direct = product.evaluate_mv(&point).unwrap();
        assert_eq!(
            eval_coeffs(&coeffs, Fr::from(t)),
            direct,
            "coef-selected polynomial mismatch at t={t}"
        );
    }
}

#[test]
fn test_fft_after_unit_selected_eval_of_mle_product_returns_evaluations() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);
    let fixed_tail = vec![Fr::from(3u64), Fr::from(5u64)];

    let selected_value = Value::<ArkBls12_381>::Poly(Arc::new(product.clone()))
        .value_eval_selected(
            CRange::singleton(0),
            Value::vec_scalar(fixed_tail.clone()),
            SelectedEvalShape::new(3, 1, 2),
        );

    let mut expected_fft = direct_unit_selected_coeffs(&product, &fixed_tail, 2);
    Fr::fft(&mut expected_fft);

    let fft_value = selected_value.value_fft(&crate::ATyp::uni(2));
    let Value::VecScalar(actual_fft) = fft_value else {
        panic!("fft after unit selected eval should return VecScalar evaluations");
    };
    assert_eq!(actual_fft.len(), expected_fft.len());
    assert_eq!(actual_fft, expected_fft);
}

#[test]
fn test_reduce_of_boolean_selected_mle_products_collapses_to_dense_univariate() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);

    let selected_terms = (0..4usize)
        .map(|tail_index| {
            let tail: Vec<Fr> = (0..2)
                .map(|j| Fr::from(((tail_index >> j) & 1) as u64))
                .collect();
            Value::<ArkBls12_381>::Poly(Arc::new(
                product
                    .fix_variables_except_range(CRange::singleton(0), &tail)
                    .unwrap(),
            ))
        })
        .collect::<Vec<_>>();

    let reduced = Value::<ArkBls12_381>::Vec(selected_terms.into())
        .value_reduce(BinOp::Add)
        .unwrap();
    let Value::Poly(round_poly) = reduced else {
        panic!("expected reduced polynomial");
    };

    assert_eq!(round_poly.num_vars(), Some(1));
    assert!(
        round_poly.flattened_polys.len() == 1
            && matches!(
                round_poly.flattened_polys[0].as_ref(),
                PolyVariant::DenseUni(_)
            ),
        "sum of selected MLE-product tails should materialize a compact DenseUni round polynomial"
    );

    let expected = explicit_round_evals(&product, 3, 2);
    let actual = (0..=2)
        .map(|t| round_poly.evaluate_uv(&Fr::from(t as u64)))
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

#[test]
fn test_prefix_eval_fixes_mle_product_factorwise() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);
    let r0 = Fr::from(5u64);
    let residual = product.evaluate_or_fix(&[r0]).unwrap();

    for (x1, x2) in [(0u64, 0u64), (1, 0), (0, 1), (3, 4)] {
        let direct = product
            .evaluate_mv(&[r0, Fr::from(x1), Fr::from(x2)])
            .unwrap();
        let residual_eval = residual.evaluate_mv(&[Fr::from(x1), Fr::from(x2)]).unwrap();
        assert_eq!(
            residual_eval, direct,
            "prefix residual mismatch at ({x1}, {x2})"
        );
    }
}

#[test]
fn test_prefix_eval_leaves_product_univariate_when_one_variable_remains() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);
    let r0 = Fr::from(5u64);
    let r1 = Fr::from(7u64);
    let residual = product.evaluate_or_fix(&[r0, r1]).unwrap();
    assert!(residual.is_univariate());

    for t in [0u64, 1, 6] {
        let direct = product.evaluate_mv(&[r0, r1, Fr::from(t)]).unwrap();
        let residual_eval = residual.evaluate_uv(&Fr::from(t));
        assert_eq!(residual_eval, direct, "univariate residual mismatch at {t}");
    }
}

#[test]
fn test_repeated_prefix_eval_matches_direct_for_deep_mle_product() {
    let base = create_vp_from_mle((1..=256).collect(), 8);
    let mut product = base.clone();
    for _ in 1..6 {
        product = product.poly_mul(&base);
    }

    let prefix: Vec<Fr> = (2u64..=7).map(Fr::from).collect();
    let mut residual = product.clone();
    for r in &prefix {
        residual = residual.evaluate_or_fix(&[*r]).unwrap();
    }

    for (x6, x7) in [(0u64, 0u64), (1, 0), (0, 1), (3, 5)] {
        let mut full_point = prefix.clone();
        full_point.push(Fr::from(x6));
        full_point.push(Fr::from(x7));
        let direct = product.evaluate_mv(&full_point).unwrap();
        let residual_eval = residual.evaluate_mv(&[Fr::from(x6), Fr::from(x7)]).unwrap();
        assert_eq!(
            residual_eval, direct,
            "deep repeated prefix residual mismatch at ({x6}, {x7})"
        );
    }
}

#[test]
fn test_deep_explicit_final_round_consistency() {
    let base = create_vp_from_mle((1..=256).collect(), 8);
    let mut product = base.clone();
    for _ in 1..6 {
        product = product.poly_mul(&base);
    }

    let mut rng = test_rng();
    let prefix: Vec<Fr> = (0..6).map(|_| Fr::rand(&mut rng)).collect();
    let mut curr_poly = product.clone();
    for r in &prefix {
        curr_poly = curr_poly.evaluate_or_fix(&[*r]).unwrap();
    }

    let round_poly = explicit_round_poly(&curr_poly, 2);
    let final_challenge = Fr::rand(&mut rng);
    let prev_eval = round_poly.evaluate_uv(&final_challenge);
    let final_poly = curr_poly.evaluate_or_fix(&[final_challenge]).unwrap();
    let ev0 = final_poly.evaluate_uv(&Fr::from(0u64));
    let ev1 = final_poly.evaluate_uv(&Fr::from(1u64));
    assert_eq!(prev_eval, ev0 + ev1);
}

#[test]
fn test_explicit_round_eval_matches_marginalize_reference_for_small_product() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4, 5, 6, 7, 8], 3);
    let b = create_vp_from_mle(vec![2, 3, 5, 7, 11, 13, 17, 19], 3);
    let product = a.poly_mul(&b);
    let max_degree = 2;

    let explicit_round0 = explicit_round_evals(&product, 3, max_degree);
    let (legacy_round0, _) = marginalize::<ArkBls12_381>(&product, 3, max_degree, 0, None);
    assert_eq!(explicit_round0, legacy_round0);

    let r1 = Fr::from(5u64);
    let residual = product.evaluate_or_fix(&[r1]).unwrap();
    let explicit_round1 = explicit_round_evals(&residual, 2, max_degree);
    let (legacy_round1, legacy_residual) =
        marginalize::<ArkBls12_381>(&product, 3, max_degree, 1, Some(r1));
    assert_eq!(explicit_round1, legacy_round1);

    for (x1, x2) in [(0u64, 0u64), (1, 0), (0, 1), (3, 4)] {
        assert_eq!(
            residual.evaluate_mv(&[Fr::from(x1), Fr::from(x2)]).unwrap(),
            legacy_residual
                .evaluate_mv(&[Fr::from(x1), Fr::from(x2)])
                .unwrap()
        );
    }
}

#[test]
fn test_explicit_round_eval_matches_marginalize_reference_for_degree10_product() {
    let num_vars = 8;
    let max_degree = 10;
    let mut rng = test_rng();
    let evals: Vec<Fr> = (0..(1usize << num_vars))
        .map(|_| Fr::rand(&mut rng))
        .collect();
    let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(DenseMle::new(num_vars, evals)));
    let mut product = base.clone();
    for _ in 1..max_degree {
        product = product.poly_mul(&base);
    }

    let explicit_round0 = explicit_round_evals(&product, num_vars, max_degree);
    let reduced_terms = (0..(1usize << (num_vars - 1)))
        .map(|tail_index| {
            let tail: Vec<Fr> = (0..(num_vars - 1))
                .map(|j| Fr::from(((tail_index >> j) & 1) as u64))
                .collect();
            Value::<ArkBls12_381>::Poly(Arc::new(
                product
                    .fix_variables_except_range(CRange::singleton(0), &tail)
                    .unwrap(),
            ))
        })
        .collect::<Vec<_>>();
    let reduced_round0 = match Value::<ArkBls12_381>::Vec(reduced_terms.into())
        .value_reduce(BinOp::Add)
        .unwrap()
    {
        Value::Poly(poly) => (0..=max_degree)
            .map(|t| poly.evaluate_uv(&Fr::from(t as u64)))
            .collect::<Vec<_>>(),
        other => panic!("expected reduced polynomial, got {other}"),
    };
    assert_eq!(explicit_round0, reduced_round0);
    let (legacy_round0, _) = marginalize::<ArkBls12_381>(&product, num_vars, max_degree, 0, None);
    assert_eq!(explicit_round0, legacy_round0);

    let r1 = Fr::from(5u64);
    let residual = product.evaluate_or_fix(&[r1]).unwrap();
    let explicit_round1 = explicit_round_evals(&residual, num_vars - 1, max_degree);
    let (legacy_round1, _) =
        marginalize::<ArkBls12_381>(&product, num_vars, max_degree, 1, Some(r1));
    assert_eq!(explicit_round1, legacy_round1);
}

#[test]
fn test_explicit_sumcheck_round_chain_consistency_degree6_num_vars8() {
    let num_vars = 8;
    let max_degree = 6;
    let mut rng = test_rng();
    let evals: Vec<Fr> = (0..(1usize << num_vars))
        .map(|_| Fr::rand(&mut rng))
        .collect();
    let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(DenseMle::new(num_vars, evals)));
    let mut curr_poly = base.clone();
    for _ in 1..max_degree {
        curr_poly = curr_poly.poly_mul(&base);
    }

    let mut prev_eval: Option<Fr> = None;
    let mut current_vars = num_vars;
    for round in 0..num_vars {
        let evs = if current_vars == 1 {
            (0..=max_degree)
                .map(|t| curr_poly.evaluate_uv(&Fr::from(t as u64)))
                .collect::<Vec<_>>()
        } else {
            explicit_round_evals(&curr_poly, current_vars, max_degree)
        };
        if let Some(prev) = prev_eval {
            assert_eq!(
                prev,
                evs[0] + evs[1],
                "sumcheck consistency failed at round {round}"
            );
        }
        let g = round_from_evals(&evs);
        let challenge = Fr::from((round + 5) as u64);
        prev_eval = Some(g.evaluate_uv(&challenge));
        if current_vars > 1 {
            curr_poly = curr_poly.evaluate_or_fix(&[challenge]).unwrap();
            current_vars -= 1;
        }
    }
}

#[test]
fn test_selected_wide_eval_matches_direct_evaluation_for_dense_mle() {
    let p = create_vp_from_mle((1u64..=16).collect(), 4);
    let fixed = vec![Fr::from(5u64), Fr::from(7u64)]; // variables 0 and 3
    let selected = p
        .fix_variables_except_range_with_shape(
            SelectedEvalShape::new(4, 2, 1),
            CRange::from_raw(1, 1, 3),
            &fixed,
        )
        .unwrap();

    assert_eq!(selected.num_vars(), Some(2));
    for (x1, x2) in [(0u64, 0u64), (1, 0), (0, 1), (2, 3)] {
        let direct = p
            .evaluate_mv(&[fixed[0], Fr::from(x1), Fr::from(x2), fixed[1]])
            .unwrap();
        let selected_eval = selected.evaluate_mv(&[Fr::from(x1), Fr::from(x2)]).unwrap();
        assert_eq!(
            selected_eval, direct,
            "wide selected eval mismatch at ({x1}, {x2})"
        );
    }
}

#[test]
fn test_selected_eval_typed_zero_preserves_output_arity() {
    let zero = VirtualPolynomial::<Fr>::zero_with_num_vars(3);
    let selected = zero
        .fix_variables_except_range_with_shape(
            SelectedEvalShape::new(3, 1, 5),
            CRange::singleton(0),
            &[Fr::from(2u64), Fr::from(3u64)],
        )
        .unwrap();

    assert_eq!(selected.num_vars(), Some(1));
    assert_eq!(selected.evaluate_uv(&Fr::from(11u64)), Fr::from(0u64));
}

#[test]
fn selected_eval_unit_zero_preserves_declared_degree_slots() {
    let degree = 7usize;
    let zero = VirtualPolynomial::<Fr>::zero_with_num_vars(3);
    let selected_value = Value::<ArkBls12_381>::Poly(Arc::new(zero)).value_eval_selected(
        CRange::singleton(0),
        Value::vec_scalar(vec![Fr::from(2u64), Fr::from(3u64)]),
        SelectedEvalShape::new(3, 1, degree),
    );

    let typ = crate::ATyp::uni(degree);
    let Value::VecScalar(coeffs) = selected_value.value_coef_typed(&typ) else {
        panic!("coef after unit selected zero should return VecScalar");
    };
    assert_eq!(coeffs.len(), degree + 1);
    assert!(coeffs.iter().all(|c| c.is_zero()));

    let Value::VecScalar(evals) = selected_value.value_fft(&typ) else {
        panic!("fft after unit selected zero should return VecScalar");
    };
    assert_eq!(evals.len(), degree + 1);
    assert!(evals.iter().all(|v| v.is_zero()));
}

#[test]
fn selected_eval_unit_constant_preserves_declared_degree_slots() {
    let degree = 7usize;
    let scalar = Fr::from(9u64);
    let constant = VirtualPolynomial::<Fr>::constant_with_num_vars(scalar, 3);
    let selected_value = Value::<ArkBls12_381>::Poly(Arc::new(constant)).value_eval_selected(
        CRange::singleton(0),
        Value::vec_scalar(vec![Fr::from(2u64), Fr::from(3u64)]),
        SelectedEvalShape::new(3, 1, degree),
    );

    let typ = crate::ATyp::uni(degree);
    let Value::VecScalar(coeffs) = selected_value.value_coef_typed(&typ) else {
        panic!("coef after unit selected constant should return VecScalar");
    };
    assert_eq!(coeffs.len(), degree + 1);
    assert_eq!(coeffs[0], scalar);
    assert!(coeffs[1..].iter().all(|c| c.is_zero()));

    let Value::VecScalar(evals) = selected_value.value_fft(&typ) else {
        panic!("fft after unit selected constant should return VecScalar");
    };
    assert_eq!(evals.len(), degree + 1);
    assert!(evals.iter().all(|v| *v == scalar));
}

#[test]
fn test_selected_eval_typed_constant_wide_range_preserves_output_arity() {
    let constant = VirtualPolynomial::<Fr>::constant_with_num_vars(Fr::from(9u64), 4);
    let selected = constant
        .fix_variables_except_range_with_shape(
            SelectedEvalShape::new(4, 2, 7),
            CRange::from_raw(1, 1, 3),
            &[Fr::from(2u64), Fr::from(5u64)],
        )
        .unwrap();

    assert_eq!(selected.num_vars(), Some(2));
    assert_eq!(
        selected
            .evaluate_mv(&[Fr::from(7u64), Fr::from(11u64)])
            .unwrap(),
        Fr::from(9u64)
    );
}

// ========== Ring Axiom Tests: Addition ==========

#[test]
fn test_addition_associativity() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]); // 1 + 2x + 3x^2
    let b = create_vp_from_poly_univariate(vec![4, 5]); // 4 + 5x
    let c = create_vp_from_scalar(7);

    let left = a.poly_add(&b.poly_add(&c));
    let right = a.poly_add(&b).poly_add(&c);

    assert_vp_eq(&left, &right, "Addition associativity: (a+b)+c = a+(b+c)");
}

#[test]
fn test_addition_commutativity() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let b = create_vp_from_poly_univariate(vec![4, 5]);

    let left = a.poly_add(&b);
    let right = b.poly_add(&a);

    assert_vp_eq(&left, &right, "Addition commutativity: a+b = b+a");
}

#[test]
fn test_addition_identity() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let zero = VirtualPolynomial::new(); // Zero polynomial

    let result = a.poly_add(&zero);

    assert_vp_eq(&result, &a, "Addition identity: a+0 = a");
}

#[test]
fn test_addition_inverse() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let zero = VirtualPolynomial::new();

    let neg_a = a.poly_mul_scalar(-Fr::one());
    let result = a.poly_add(&neg_a);

    assert_vp_eq(&result, &zero, "Addition inverse: a+(-a) = 0");
}

#[test]
fn test_scalar_addition() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let scalar = Fr::from(5u64);

    let result = a.poly_add_scalar(scalar);
    let expected = create_vp_from_poly_univariate(vec![6, 2, 3]); // (1+5) + 2x + 3x^2

    assert_vp_eq(&result, &expected, "Scalar addition");
}

// ========== Ring Axiom Tests: Multiplication ==========

#[test]
fn test_multiplication_associativity() {
    let a = create_vp_from_poly_univariate(vec![1, 2]); // 1 + 2x
    let b = create_vp_from_poly_univariate(vec![3, 4]); // 3 + 4x
    let c = create_vp_from_scalar(5);

    let left = a.poly_mul(&b.poly_mul(&c));
    let right = a.poly_mul(&b).poly_mul(&c);

    assert_vp_eq(
        &left,
        &right,
        "Multiplication associativity: (a*b)*c = a*(b*c)",
    );
}

#[test]
fn test_multiplication_identity() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let one = create_vp_from_scalar(1);

    let result = a.poly_mul(&one);

    assert_vp_eq(&result, &a, "Multiplication identity: a*1 = a");
}

#[test]
fn test_multiplication_zero() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let zero = VirtualPolynomial::new();

    let result = a.poly_mul(&zero);

    assert_vp_eq(&result, &zero, "Multiplication by zero: a*0 = 0");
}

#[test]
fn test_scalar_multiplication() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let scalar = Fr::from(5u64);

    let result = a.poly_mul_scalar(scalar);
    let expected = create_vp_from_poly_univariate(vec![5, 10, 15]);

    assert_vp_eq(&result, &expected, "Scalar multiplication");
}

// ========== Ring Axiom Tests: Distributivity ==========

#[test]
fn test_left_distributivity() {
    let a = create_vp_from_poly_univariate(vec![1, 2]);
    let b = create_vp_from_poly_univariate(vec![3, 4]);
    let c = create_vp_from_scalar(5);

    // a * (b + c)
    let left = a.poly_mul(&b.poly_add(&c));

    // a*b + a*c
    let right = a.poly_mul(&b).poly_add(&a.poly_mul(&c));

    assert_vp_eq(&left, &right, "Left distributivity: a*(b+c) = a*b + a*c");
}

#[test]
fn test_right_distributivity() {
    let a = create_vp_from_poly_univariate(vec![1, 2]);
    let b = create_vp_from_poly_univariate(vec![3, 4]);
    let c = create_vp_from_scalar(5);

    // (a + b) * c
    let left = a.poly_add(&b).poly_mul(&c);

    // a*c + b*c
    let right = a.poly_mul(&c).poly_add(&b.poly_mul(&c));

    assert_vp_eq(&left, &right, "Right distributivity: (a+b)*c = a*c + b*c");
}

// ========== Subtraction Tests ==========

#[test]
fn test_subtraction_as_inverse() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);
    let b = create_vp_from_poly_univariate(vec![4, 5]);

    let sub_result = a.poly_sub(&b);

    let neg_b = b.poly_mul_scalar(-Fr::one());
    let add_neg_result = a.poly_add(&neg_b);

    assert_vp_eq(
        &sub_result,
        &add_neg_result,
        "Subtraction as inverse: a-b = a+(-b)",
    );
}

#[test]
fn test_scalar_subtraction() {
    let a = create_vp_from_poly_univariate(vec![10, 2, 3]);
    let scalar = Fr::from(5u64);

    let result = a.poly_sub_scalar(scalar);
    let expected = create_vp_from_poly_univariate(vec![5, 2, 3]); // (10-5) + 2x + 3x^2

    assert_vp_eq(&result, &expected, "Scalar subtraction");
}

// ========== Division Refusal Tests ==========

// ========== Checked Vector Evaluation Tests ==========

// ========== Virtual Polynomial Specific Tests ==========

#[test]
fn test_product_representation() {
    // Create a virtual polynomial as a product: (1 + 2x) * (3 + 4x)
    let poly1 = PolyVariant::DenseUni(DenseUni::new(vec![Fr::from(1u64), Fr::from(2u64)]));
    let poly2 = PolyVariant::DenseUni(DenseUni::new(vec![Fr::from(3u64), Fr::from(4u64)]));

    let mut vp = VirtualPolynomial::new();
    vp.add_poly_list(vec![Arc::new(poly1), Arc::new(poly2)], Fr::one());

    // Expected: 3 + 10x + 8x^2
    let expected = create_vp_from_poly_univariate(vec![3, 10, 8]);

    assert_vp_eq(&vp, &expected, "Product representation");
}

#[test]
fn test_normalize_simple() {
    let a = create_vp_from_poly_univariate(vec![1, 2, 3]);

    // Normalize should give back the same polynomial
    let normalized = a.normalize().unwrap();
    let expected = PolyVariant::DenseUni(DenseUni::new(vec![
        Fr::from(1u64),
        Fr::from(2u64),
        Fr::from(3u64),
    ]));

    assert_eq!(normalized, expected, "Normalize simple polynomial");
}

#[test]
fn test_normalize_product() {
    // (1 + 2x) * (3 + 4x) = 3 + 10x + 8x^2
    let poly1 = PolyVariant::DenseUni(DenseUni::new(vec![Fr::from(1u64), Fr::from(2u64)]));
    let poly2 = PolyVariant::DenseUni(DenseUni::new(vec![Fr::from(3u64), Fr::from(4u64)]));

    let mut vp = VirtualPolynomial::new();
    vp.add_poly_list(vec![Arc::new(poly1), Arc::new(poly2)], Fr::one());

    let normalized = vp.normalize().unwrap();

    // Check the result evaluates correctly
    let point = Fr::from(5u64);
    let eval = normalized.evaluate(&[point]);

    // (1 + 2*5) * (3 + 4*5) = 11 * 23 = 253
    assert_eq!(eval, Fr::from(253u64), "Normalize product evaluation");
}

#[test]
fn test_mul_by_poly_and_scalar() {
    let poly1 = PolyVariant::DenseUni(DenseUni::new(vec![Fr::from(1u64), Fr::from(2u64)]));
    let poly2 = PolyVariant::DenseUni(DenseUni::new(vec![Fr::from(3u64), Fr::from(4u64)]));

    let vp = VirtualPolynomial::from_poly(poly1)
        .poly_mul(&VirtualPolynomial::from_poly(poly2))
        .poly_mul_scalar(Fr::from(2u64));

    // Should be 2 * (1 + 2x) * (3 + 4x) = 2 * (3 + 10x + 8x^2) = 6 + 20x + 16x^2
    let expected = create_vp_from_poly_univariate(vec![6, 20, 16]);

    assert_vp_eq(&vp, &expected, "mul_by_poly");
}

// ========== MLE Tests ==========

#[test]
fn test_mle_addition() {
    let a = create_vp_from_mle(vec![1, 2, 3, 4], 2); // 2-var MLE
    let b = create_vp_from_mle(vec![5, 6, 7, 8], 2);

    let result = a.poly_add(&b);
    let expected = create_vp_from_mle(vec![6, 8, 10, 12], 2);

    // Compare by evaluating at random points
    let mut rng = test_rng();
    for _ in 0..10 {
        let point = vec![Fr::rand(&mut rng), Fr::rand(&mut rng)];
        let eval_result = result.evaluate_mv(&point).unwrap();
        let eval_expected = expected.evaluate_mv(&point).unwrap();
        assert_eq!(eval_result, eval_expected, "MLE addition mismatch");
    }
}

#[test]
fn test_zero_polynomial() {
    let zero = VirtualPolynomial::<Fr>::new();

    assert!(zero.is_zero(), "Zero polynomial should report is_zero");

    let point = Fr::from(42u64);
    assert_eq!(
        zero.evaluate_uv(&point),
        Fr::zero(),
        "Zero polynomial evaluates to zero"
    );
}

#[test]
fn test_simplify() {
    let mut vp = VirtualPolynomial::new();

    // Add terms with zero coefficients
    vp.products.push((Fr::zero(), vec![]));
    vp.products.push((Fr::from(5u64), vec![]));
    vp.products.push((Fr::zero(), vec![]));

    vp.simplify();

    assert_eq!(
        vp.products.len(),
        1,
        "Simplify should remove zero coefficients"
    );
    assert_eq!(
        vp.products[0].0,
        Fr::from(5u64),
        "Simplify should keep non-zero coefficients"
    );
}
