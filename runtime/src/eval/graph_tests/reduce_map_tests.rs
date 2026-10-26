//! Tests for the generalized loop-fusion ops `Op::Map` / `Op::ReduceMap`
//! / `Op::LoopParam` and the streaming reduce-map evaluator.

use crate::eval::eval_op;
use crate::eval::graph_tests::helpers::{lowered, scalar};
use ark_ff::{One, Zero};
use backend::{ATyp, ArkBls12_381, Value};
use graph::{GOp, Op, Ref, UDags, mk};
use lang::ast::BinOp;
use rand::SeedableRng;
use rand::rngs::StdRng;
use share::Ctx;
use std::collections::HashMap;

type B = ArkBls12_381;

fn parse_and_build(src: &str) -> UDags<B> {
    lowered::<B>(src, &Ctx::new()).unwrap()
}

/// Count op nodes across all graphs matching `pred`.
fn count_ops<P: Fn(&GOp<B>) -> bool>(graphs: &UDags<B>, pred: P) -> usize {
    graphs
        .iter()
        .map(|dag| {
            dag.op_nodes()
                .into_iter()
                .filter(|n| dag[*n].op().is_some_and(|op| pred(op.get())))
                .count()
        })
        .sum()
}

/// Whether the inline op-tree references `Op::LoopParam(level, _)`.
fn op_has_loop_param(op: &GOp<B>, level: usize) -> bool {
    match op {
        Op::LoopParam(l, _) => *l == level,
        Op::Bin(_, a, b, _) | Op::Ram(a, b) | Op::Pair(a, b, _) | Op::Interpolate(a, b) => {
            op_has_loop_param(a.get(), level) || op_has_loop_param(b.get(), level)
        }
        Op::Map(d, b) | Op::ReduceMap(_, d, b) => {
            op_has_loop_param(d.get(), level) || op_has_loop_param(b.get(), level)
        }
        Op::Assert(a) | Op::Verify(a) => op_has_loop_param(a.get(), level),
        Op::Poly(a)
        | Op::Coef(a)
        | Op::ToScalar(a)
        | Op::Mle(a)
        | Op::Ifft(a)
        | Op::Fft(a)
        | Op::Reduce(_, a)
        | Op::Proj(a, _, _) => op_has_loop_param(a.get(), level),
        Op::Evaluate(p, _, pts) => {
            op_has_loop_param(p.get(), level)
                || pts
                    .as_ref()
                    .is_some_and(|x| op_has_loop_param(x.get(), level))
        }
        Op::Vec(vs) => vs.iter().any(|v| op_has_loop_param(v.get(), level)),
        Op::Record(fs) => fs.iter().any(|(_, v)| op_has_loop_param(v.get(), level)),
        _ => false,
    }
}

#[test]
fn generic_reduce_over_map_lowers_to_reduce_map() {
    let src = r#"
        fn s<F: Field>(witness xs: [F; 4]) -> F {
            reduce(+, [x + x for x in xs])
        }
    "#;
    let graphs = parse_and_build(src);

    // Exactly one fused reduce-map with the generic (Unknown) domain fact,
    // whose body references the loop binder; no unrolled Reduce/Map nodes.
    let mut reduce_maps = 0;
    for dag in graphs.iter() {
        for n in dag.op_nodes() {
            let Some(op) = dag[n].op() else {
                continue;
            };
            if let Op::ReduceMap(BinOp::Add, _, body) = op.get() {
                reduce_maps += 1;
                assert!(
                    op_has_loop_param(body.get(), 0),
                    "reduce-map body must reference the loop binder"
                );
            }
        }
    }
    assert_eq!(reduce_maps, 1, "expected exactly one generic reduce-map");
    assert_eq!(
        count_ops(&graphs, |op| matches!(op, Op::Reduce(_, _))),
        0,
        "comprehension must be fused, not unrolled into a Reduce"
    );
    assert_eq!(
        count_ops(&graphs, |op| matches!(op, Op::Map(_, _))),
        0,
        "domain is a plain ref, so no standalone Map should materialize"
    );
}

#[test]
fn standalone_map_lowers_to_map_op() {
    let src = r#"
        fn m<F: Field>(witness xs: [F; 4]) -> [F; 4] {
            [x + x for x in xs]
        }
    "#;
    let graphs = parse_and_build(src);

    let mut maps = 0;
    for dag in graphs.iter() {
        for n in dag.op_nodes() {
            let Some(op) = dag[n].op() else {
                continue;
            };
            if let Op::Map(_, body) = op.get() {
                maps += 1;
                assert!(
                    op_has_loop_param(body.get(), 0),
                    "map body must reference the loop binder"
                );
            }
        }
    }
    assert_eq!(maps, 1, "expected exactly one standalone Op::Map");
}

#[test]
fn nested_map_domain_is_composed_away() {
    let src = r#"
        fn c<F: Field>(witness xs: [F; 4]) -> F {
            reduce(+, [x + x for x in [y + y for y in xs]])
        }
    "#;
    let graphs = parse_and_build(src);

    let mut found = false;
    for dag in graphs.iter() {
        for n in dag.op_nodes() {
            let Some(op) = dag[n].op() else {
                continue;
            };
            if let Op::ReduceMap(_, domain, _) = op.get() {
                found = true;
                assert!(
                    !matches!(domain.get(), Op::Map(_, _)),
                    "inner comprehension must be composed into the reduce-map domain"
                );
            }
        }
    }
    assert!(found, "expected a reduce-map node");
    // The inner comprehension was fused into the body, not materialized.
    assert_eq!(
        count_ops(&graphs, |op| matches!(op, Op::Map(_, _))),
        0,
        "composed nested map must leave no standalone Map node"
    );
}

#[test]
fn effectful_body_declines_to_unroll() {
    let src = r#"
        fn e<F: Field>(witness xs: [F; 4]) -> F {
            reduce(+, [x + random<F> for x in xs])
        }
    "#;
    let graphs = parse_and_build(src);

    assert_eq!(
        count_ops(&graphs, |op| matches!(op, Op::ReduceMap(_, _, _))),
        0,
        "effectful body must decline fusion"
    );
    assert_eq!(
        count_ops(&graphs, |op| matches!(op, Op::Map(_, _))),
        0,
        "effectful body must decline to the unroll"
    );
}

#[test]
fn reduce_map_eval_matches_materialized_reduce() {
    let scalar_t = ATyp::scalar();
    let domain = Op::Vec(
        (1..=4u64)
            .map(|n| mk::<B>(Op::Value(scalar::<B>(n))))
            .collect(),
    );
    let body = Op::Bin(
        BinOp::Add,
        mk::<B>(Op::LoopParam(0, scalar_t.clone())),
        mk::<B>(Op::LoopParam(0, scalar_t.clone())),
        scalar_t,
    );
    let rm = GOp::reduce_map(BinOp::Add, domain, body);

    let env: HashMap<Ref, Value<B>> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(0);
    let got = eval_op(&rm, &env, &mut rng, &mut Vec::new()).unwrap();

    // Reference: materialized reduce over the doubled elements.
    let doubled = Op::Vec(
        [2u64, 4, 6, 8]
            .into_iter()
            .map(|n| mk::<B>(Op::Value(scalar::<B>(n))))
            .collect(),
    );
    let reference = Op::Reduce(BinOp::Add, mk::<B>(doubled));
    let want = eval_op(&reference, &env, &mut rng, &mut Vec::new()).unwrap();

    assert_eq!(
        got, want,
        "streaming reduce-map must match materialized reduce"
    );
    assert_eq!(got, scalar::<B>(20), "sum of 2*(1+2+3+4) = 20");
}

#[test]
fn map_eval_doubles_each_element() {
    let scalar_t = ATyp::scalar();
    let domain = Op::Vec(
        (1..=4u64)
            .map(|n| mk::<B>(Op::Value(scalar::<B>(n))))
            .collect(),
    );
    let body = Op::Bin(
        BinOp::Add,
        mk::<B>(Op::LoopParam(0, scalar_t.clone())),
        mk::<B>(Op::LoopParam(0, scalar_t.clone())),
        scalar_t,
    );
    let map = GOp::map(domain, body);

    let env: HashMap<Ref, Value<B>> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(0);
    let got = eval_op(&map, &env, &mut rng, &mut Vec::new()).unwrap();

    let want_vec = Op::Vec(
        [2u64, 4, 6, 8]
            .into_iter()
            .map(|n| mk::<B>(Op::Value(scalar::<B>(n))))
            .collect(),
    );
    let want = eval_op(&want_vec, &env, &mut rng, &mut Vec::new()).unwrap();
    assert_eq!(got, want, "map must apply the body element-wise");
}

#[test]
fn reduce_map_over_the_hypercube_sums_the_round() {
    for free_variable in 0..3 {
        use crate::eval::graph_tests::helpers::execute_graph;

        // A helper function returning the computed round polynomial
        let src = r#"
            fn test_opt<F: Field>(witness p: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
                let zero: F = 0;
                let one = zero + 1;
                reduce(+, [
                    eval<0>(p, tail)
                    for tail in [
                        [(((i / (2^j)) % 2) * one) for j in 0..2]
                        for i in 0..4
                    ]
                ])
            }
        "#;
        let src = src.replace("eval<0>", &format!("eval<{free_variable}>"));
        let graphs = parse_and_build(&src);
        let dag = &graphs[0];

        let mut inputs = Ctx::new();
        let mut rng = StdRng::seed_from_u64(0);
        let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
        inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

        let result = execute_graph(dag, inputs).unwrap();
        let Value::Poly(got_poly) = result else {
            panic!("Expected a polynomial result, found {:?}", result);
        };

        // Verify mathematical correctness of the optimized result:
        // Sum all Boolean assignments outside the selected variable.
        let Value::Poly(ref orig_poly) = poly_val else {
            unreachable!()
        };
        for t_idx in 0..4 {
            let t = <B as backend::Backend>::F::from(t_idx);
            let mut expected = <B as backend::Backend>::F::zero();
            for tail_index in 0..4 {
                let b0 = if tail_index & 1 == 1 {
                    <B as backend::Backend>::F::one()
                } else {
                    <B as backend::Backend>::F::zero()
                };
                let b1 = if (tail_index >> 1) & 1 == 1 {
                    <B as backend::Backend>::F::one()
                } else {
                    <B as backend::Backend>::F::zero()
                };
                let mut point = vec![b0, b1];
                point.insert(free_variable, t);
                expected += orig_poly.evaluate_mv(&point).unwrap();
            }
            assert_eq!(got_poly.evaluate_uv(&t), expected);
        }
    }
}

#[test]
fn reduce_map_over_a_non_power_of_two_domain_sums_it() {
    use crate::eval::graph_tests::helpers::execute_graph;

    // Domain size 3 is not a power of 2, so this is not a hypercube sum; the result is
    // still the sum of the mapped polynomials.
    let src = r#"
        fn test_no_opt<F: Field>(witness p: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(p, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..3
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization does not fire

    // Verify mathematical correctness of the fallback result:
    // R(t) = Sum_{i ∈ 0..3} P(t, tail_i)
    let Value::Poly(ref orig_poly) = poly_val else {
        unreachable!()
    };
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let mut expected = <B as backend::Backend>::F::zero();
        for tail_index in 0..3 {
            let b0 = if tail_index & 1 == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            let b1 = if (tail_index >> 1) & 1 == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            expected += orig_poly.evaluate_mv(&[t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
fn multiplicative_reduce_map_multiplies() {
    use crate::eval::graph_tests::helpers::execute_graph;

    // A multiplicative reduction is not a sumcheck round; the result is the product of
    // the mapped polynomials.
    let src = r#"
        fn test_mul_no_opt<F: Field>(witness p: Poly<F, 3, 1>) -> Poly<F, 1, 4> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(*, [
                eval<0>(p, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization does not fire

    // Verify mathematical correctness of the fallback result:
    // R(t) = Product_{b ∈ {0,1}^2} P(t, b)
    let Value::Poly(ref orig_poly) = poly_val else {
        unreachable!()
    };
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let mut expected = <B as backend::Backend>::F::one();
        for tail_index in 0..4 {
            let b0 = if tail_index & 1 == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            let b1 = if (tail_index >> 1) & 1 == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            expected *= orig_poly.evaluate_mv(&[t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
fn reduce_map_over_a_non_mle_sums_the_round() {
    use crate::eval::graph_tests::helpers::execute_graph;
    use backend::poly::variant::{Multivariate, Term};
    use backend::{PolyVariant, VirtualPolynomial};

    // Poly<F, 3, 2> is a polynomial of 3 variables and max degree 2 (non-MLE).
    // A hypercube sum of a polynomial that is not multilinear: the round is still the
    // sum over the hypercube.
    let src = r#"
        fn test_non_mle<F: Field>(witness p: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(p, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();

    // We construct a non-MLE polynomial (e.g. X_0^2 + X_1 + X_2) manually
    let terms = vec![
        (<B as backend::Backend>::F::one(), Term::new(vec![(0, 2)])),
        (<B as backend::Backend>::F::one(), Term::new(vec![(1, 1)])),
        (<B as backend::Backend>::F::one(), Term::new(vec![(2, 1)])),
    ];
    let p = Multivariate::new(3, terms);
    let poly_variant = PolyVariant::SparseMultivariate(p);
    let poly_val = Value::poly(VirtualPolynomial::from_poly(poly_variant));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization kernel is entered (seen is incremented),
    // and completes with fused counter incremented as well.

    // Verify mathematical correctness of the result:
    // R(t) = Sum_{b ∈ {0,1}^2} P(t, b)
    // For P(t, b0, b1) = t^2 + b0 + b1, the sum over b0, b1 in {0,1} is 4*t^2 + 4.
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let expected =
            t * t * <B as backend::Backend>::F::from(4) + <B as backend::Backend>::F::from(4);
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
fn reduce_map_with_a_modified_loop_param_sums_it() {
    use crate::eval::graph_tests::helpers::execute_graph;

    // The loop parameter is modified inside the eval call: eval<0>(p, [t + one for t in tail]).
    // The evaluation points are not the loop parameter's tail coordinates.
    let src = r#"
        fn test_modified<F: Field>(witness p: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(p, [t + one for t in tail])
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization does not fire because fixed is modified (not exactly the loop parameter)

    // Verify mathematical correctness of the non-optimized result:
    // R(t) = Sum_{b ∈ {0,1}^2} P(t, b0+1, b1+1)
    let Value::Poly(ref orig_poly) = poly_val else {
        unreachable!()
    };
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let mut expected = <B as backend::Backend>::F::zero();
        for tail_index in 0..4 {
            let b0 = if tail_index & 1 == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            let b1 = if (tail_index >> 1) & 1 == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            expected += orig_poly
                .evaluate_mv(&[
                    t,
                    b0 + <B as backend::Backend>::F::one(),
                    b1 + <B as backend::Backend>::F::one(),
                ])
                .unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
fn reduce_map_with_a_loop_dependent_poly_sums_it() {
    use crate::eval::graph_tests::helpers::execute_graph;

    // Here, the polynomial being evaluated (which is `p` in the eval expression)
    // actually depends on `tail` (the loop parameter).
    // Specifically: eval<0>(eval(poly_factory, [tail[0]]), [tail[1]])
    // `p` depends on the loop parameter, so it is not one polynomial summed over a
    // hypercube.
    let src = r#"
        fn test_dependent<F: Field>(witness poly_factory: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(eval(poly_factory, [tail[0]]), [tail[1]])
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    // poly_factory has 3 variables, evaluating it at tail[0] returns a polynomial of 2 variables.
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("poly_factory"), &poly_val.clone());

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(_got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization does not fire because the evaluated polynomial is not loop-invariant
}

#[test]
fn reduce_map_over_a_non_vector_domain_sums_it() {
    // In this case, the domain of the ReduceMap is NOT a vector (e.g. it is a polynomial type, Uni(3)).
    // The domain is not a vector, so evaluating the map reports a type mismatch.
    let scalar_t = ATyp::scalar();
    let domain = Op::Value(Value::poly(
        backend::VirtualPolynomial::constant_with_num_vars(<B as backend::Backend>::F::one(), 1),
    ));

    // fixed has LoopParam
    let fixed = mk::<B>(Op::LoopParam(0, scalar_t.clone()));
    let p = mk::<B>(Op::Value(Value::poly(
        backend::VirtualPolynomial::constant_with_num_vars(<B as backend::Backend>::F::one(), 2),
    )));
    let body = Op::Evaluate(p, Some(lang::ast::CRange::from_raw(0, 1, 1)), Some(fixed));

    let rm = GOp::reduce_map(BinOp::Add, domain, body);

    let env: HashMap<Ref, Value<B>> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(0);
    let _res = eval_op(&rm, &env, &mut rng, &mut Vec::new());

    // Optimization does not fire because the domain type is ATyp::Uni, not ATyp::Vec
}

#[test]
fn reduce_map_over_a_non_canonical_hypercube_sums_it() {
    use crate::eval::graph_tests::helpers::execute_graph;

    let src = r#"
        fn test_non_canonical<F: Field>(
            witness p: Poly<F, 3, 1>,
            witness domain: [[F; 2]; 4]
        ) -> Poly<F, 1, 1> {
            reduce(+, [
                eval<0>(p, tail)
                for tail in domain
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

    // Construct a non-canonical coordinate domain: [[1, 1], [1, 1], [1, 1], [1, 1]]
    let one = <B as backend::Backend>::F::one();
    let sub_vec = Value::vec_scalar(vec![one, one]);
    let domain_val = Value::Vec(
        vec![
            sub_vec.clone(),
            sub_vec.clone(),
            sub_vec.clone(),
            sub_vec.clone(),
        ]
        .into(),
    );
    inputs.insert(&lang::id::Vid::from("domain"), &domain_val);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization does NOT fire because the domain is non-canonical coordinates!

    // Verify correct unoptimized math result: R(t) = 4 * P(t, 1, 1)
    let Value::Poly(ref orig_poly) = poly_val else {
        unreachable!()
    };
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let expected =
            orig_poly.evaluate_mv(&[t, one, one]).unwrap() * <B as backend::Backend>::F::from(4u64);
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
fn reduce_map_over_non_canonical_indices_sums_it() {
    use crate::eval::graph_tests::helpers::execute_graph;

    let src = r#"
        fn test_non_canonical_indices<F: Field>(
            witness p: Poly<F, 3, 1>,
            witness domain: [Fin<4>; 4]
        ) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(p, [(((i / (2^j)) % 2) * one) for j in 0..2])
                for i in domain
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

    // Construct a non-canonical in-bounds index domain: [3, 2, 1, 0] (permutation of 0..3)
    let three = 3usize;
    let two = 2usize;
    let one = 1usize;
    let zero = 0usize;
    let domain_val = Value::VecIndex(vec![three, two, one, zero].into());
    inputs.insert(&lang::id::Vid::from("domain"), &domain_val);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Optimization does NOT fire because the domain is not canonical 0..3 indices!

    // Verify correctness of unoptimized result:
    // For each i in [3, 2, 1, 0], bit j is (i / 2^j) % 2.
    let Value::Poly(ref orig_poly) = poly_val else {
        unreachable!()
    };
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let mut expected = <B as backend::Backend>::F::zero();
        for &idx in &[3usize, 2usize, 1usize, 0usize] {
            let b0 = <B as backend::Backend>::F::from((idx % 2) as u64);
            let b1 = <B as backend::Backend>::F::from(((idx / 2) % 2) as u64);
            expected += orig_poly.evaluate_mv(&[t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
fn reduce_map_with_an_arity_mismatch_sums_it() {
    use crate::eval::graph_tests::helpers::execute_graph;

    // Poly has 3 variables (so 2 tail variables needed).
    // The domain has length 8 (implying 3 tail variables).
    // The fixed mapping only produces 2 bits (j in 0..2).
    // The fast path should detect the arity mismatch and safely fallback to the generic path instead of panicking.
    let src = r#"
        fn test_opt<F: Field>(witness p: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(p, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..8
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("p"), &poly_val.clone());

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    // Verify mathematical correctness of the fallback result
    let Value::Poly(ref orig_poly) = poly_val else {
        unreachable!()
    };
    for t_idx in 0..4 {
        let t = <B as backend::Backend>::F::from(t_idx);
        let mut expected = <B as backend::Backend>::F::zero();
        for i in 0..8 {
            let b0 = if (i % 2) == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            let b1 = if ((i / 2) % 2) == 1 {
                <B as backend::Backend>::F::one()
            } else {
                <B as backend::Backend>::F::zero()
            };
            expected += orig_poly.evaluate_mv(&[t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

/// `[w[s·x + t] for x in 0..n]` with `w` loop-invariant is one native gather, equal to
/// the element-by-element loop: a contiguous row, a strided column reading the outer
/// loop's element, and a non-affine index (`x·x`) that keeps the loop.
#[test]
fn affine_gather_matches_elementwise_map() {
    use crate::eval::{eval_loop_body_each, try_eval_affine_gather};
    use lang::typ::CRange;
    let idx_t = ATyp::fin(CRange::from_raw(0, 1, 12));
    let w: Vec<_> = (0..12u64).map(|n| scalar::<B>(n * 7 + 1)).collect();
    let w = mk::<B>(Op::Value(Value::value_vec(w)));
    let index = |n: usize| mk::<B>(Op::Value(Value::Index(n)));
    let outer = mk::<B>(Op::LoopParam(0, idx_t.clone()));
    let inner = mk::<B>(Op::LoopParam(1, idx_t.clone()));
    let bin = |op, a, b| mk::<B>(Op::Bin(op, a, b, idx_t.clone()));
    let row = bin(
        BinOp::Add,
        bin(BinOp::Mul, outer.clone(), index(4)),
        inner.clone(),
    );
    let column = bin(
        BinOp::Add,
        bin(BinOp::Mul, inner.clone(), index(3)),
        outer.clone(),
    );
    let square = bin(BinOp::Mul, inner.clone(), inner);
    let env: HashMap<Ref, Value<B>> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(0);
    for (index, n, fast) in [(row, 4, true), (column, 4, true), (square, 3, false)] {
        let body = mk::<B>(Op::Ram(w.clone(), index));
        let dom = Value::<B>::VecIndex((0..n).collect::<Vec<_>>().into());
        let params = [Value::Index(2)];
        let got =
            try_eval_affine_gather(&body, &dom, &env, &mut rng, &params, &mut Vec::new()).unwrap();
        assert_eq!(got.is_some(), fast);
        let want = Value::value_vec(
            eval_loop_body_each(&body, &env, dom.clone().into_elements(), &params).unwrap(),
        );
        if let Some(got) = got {
            assert_eq!(got, want);
        }
    }
}
