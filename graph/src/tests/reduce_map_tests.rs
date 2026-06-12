//! Tests for the generalized loop-fusion ops `Op::Map` / `Op::ReduceMap`
//! / `Op::LoopParam` and the streaming reduce-map evaluator.

use crate::eval::eval_op;
use crate::tests::test_helpers::scalar;
use crate::{GOp, Op, Ref, UDags, mk};
use ark_ff::{One, Zero};
use backend::{ATyp, ArkBls12_381, Value};
use lang::ast::{BinOp, UModule};
use rand::SeedableRng;
use rand::rngs::StdRng;
use share::Ctx;
use std::collections::HashMap;
use std::sync::Arc;
use serial_test::serial;

type B = ArkBls12_381;

fn parse_and_build(src: &str) -> UDags<B> {
    let module = UModule::from_str(src)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    UDags::<B>::from_module(module).unwrap()
}

/// Count op nodes across all graphs matching `pred`.
fn count_ops<P: Fn(&GOp<B>) -> bool>(graphs: &UDags<B>, pred: P) -> usize {
    graphs
        .0
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
        Op::Poly(a)
        | Op::Coef(a)
        | Op::Mle(a)
        | Op::Ifft(a)
        | Op::Fft(a)
        | Op::Check(a)
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
        fn s<F: Field>(private xs: [F; 4]) -> F {
            reduce(+, [x + x for x in xs])
        }
    "#;
    let graphs = parse_and_build(src);

    // Exactly one fused reduce-map with the generic (Unknown) domain fact,
    // whose body references the loop binder; no unrolled Reduce/Map nodes.
    let mut reduce_maps = 0;
    for dag in graphs.0.iter() {
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
        fn m<F: Field>(private xs: [F; 4]) -> [F; 4] {
            [x + x for x in xs]
        }
    "#;
    let graphs = parse_and_build(src);

    let mut maps = 0;
    for dag in graphs.0.iter() {
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
        fn c<F: Field>(private xs: [F; 4]) -> F {
            reduce(+, [x + x for x in [y + y for y in xs]])
        }
    "#;
    let graphs = parse_and_build(src);

    let mut found = false;
    for dag in graphs.0.iter() {
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
        fn e<F: Field>(private xs: [F; 4]) -> F {
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

    let env: HashMap<Ref, Arc<Value<B>>> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(0);
    let got = eval_op(&rm, &env, &mut rng).unwrap();

    // Reference: materialized reduce over the doubled elements.
    let doubled = Op::Vec(
        [2u64, 4, 6, 8]
            .into_iter()
            .map(|n| mk::<B>(Op::Value(scalar::<B>(n))))
            .collect(),
    );
    let reference = Op::Reduce(BinOp::Add, mk::<B>(doubled));
    let want = eval_op(&reference, &env, &mut rng).unwrap();

    assert_eq!(
        *got, *want,
        "streaming reduce-map must match materialized reduce"
    );
    assert_eq!(*got, scalar::<B>(20), "sum of 2*(1+2+3+4) = 20");
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

    let env: HashMap<Ref, Arc<Value<B>>> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(0);
    let got = eval_op(&map, &env, &mut rng).unwrap();

    let want_vec = Op::Vec(
        [2u64, 4, 6, 8]
            .into_iter()
            .map(|n| mk::<B>(Op::Value(scalar::<B>(n))))
            .collect(),
    );
    let want = eval_op(&want_vec, &env, &mut rng).unwrap();
    assert_eq!(*got, *want, "map must apply the body element-wise");
}

#[test]
#[serial]
fn test_reduce_map_fused_optimization_fires() {
    use backend::optimization::{optimization_stats_snapshot, reset_optimization_stats};
    use crate::tests::test_helpers::execute_graph;

    // A helper function returning the computed round polynomial
    let src = r#"
        fn test_opt<F: Field>(private poly: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(poly, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs.0[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("poly"), &poly_val.clone());

    reset_optimization_stats();
    let before = optimization_stats_snapshot();
    assert_eq!(before.canonical_sumcheck_rows_seen, 0);
    assert_eq!(before.canonical_sumcheck_rows_fused, 0);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    let after = optimization_stats_snapshot();
    // Optimization must fire
    assert_eq!(after.canonical_sumcheck_rows_seen, 1);
    assert_eq!(after.canonical_sumcheck_rows_fused, 1);

    // Verify mathematical correctness of the optimized result:
    // R(t) = Sum_{b ∈ {0,1}^2} P(t, b)
    let Value::Poly(ref orig_poly) = poly_val else { unreachable!() };
    for t_idx in 0..4 {
        let t = <B as backend::ArkConfig>::F::from(t_idx);
        let mut expected = <B as backend::ArkConfig>::F::zero();
        for tail_index in 0..4 {
            let b0 = if tail_index & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            let b1 = if (tail_index >> 1) & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            expected += orig_poly.evaluate_mv(&vec![t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
#[serial]
fn test_reduce_map_fused_optimization_skips_non_pow_two() {
    use backend::optimization::{optimization_stats_snapshot, reset_optimization_stats};
    use crate::tests::test_helpers::execute_graph;

    // Domain size 3 is not a power of 2, so the optimization must be skipped,
    // but the fallback path should execute correctly and return the correct polynomial.
    let src = r#"
        fn test_no_opt<F: Field>(private poly: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(poly, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..3
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs.0[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("poly"), &poly_val.clone());

    reset_optimization_stats();
    let before = optimization_stats_snapshot();
    assert_eq!(before.canonical_sumcheck_rows_seen, 0);
    assert_eq!(before.canonical_sumcheck_rows_fused, 0);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    let after = optimization_stats_snapshot();
    // Optimization does not fire
    assert_eq!(after.canonical_sumcheck_rows_seen, 0);
    assert_eq!(after.canonical_sumcheck_rows_fused, 0);

    // Verify mathematical correctness of the fallback result:
    // R(t) = Sum_{i ∈ 0..3} P(t, tail_i)
    let Value::Poly(ref orig_poly) = poly_val else { unreachable!() };
    for t_idx in 0..4 {
        let t = <B as backend::ArkConfig>::F::from(t_idx);
        let mut expected = <B as backend::ArkConfig>::F::zero();
        for tail_index in 0..3 {
            let b0 = if tail_index & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            let b1 = if (tail_index >> 1) & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            expected += orig_poly.evaluate_mv(&vec![t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
#[serial]
fn test_reduce_map_fused_optimization_skips_multiplicative() {
    use backend::optimization::{optimization_stats_snapshot, reset_optimization_stats};
    use crate::tests::test_helpers::execute_graph;

    // Multiplicative reduction should not match, so optimization must be skipped,
    // but the fallback path should execute correctly and return the correct polynomial.
    let src = r#"
        fn test_mul_no_opt<F: Field>(private poly: Poly<F, 3, 1>) -> Poly<F, 1, 4> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(*, [
                eval<0>(poly, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs.0[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("poly"), &poly_val.clone());

    reset_optimization_stats();
    let before = optimization_stats_snapshot();
    assert_eq!(before.canonical_sumcheck_rows_seen, 0);
    assert_eq!(before.canonical_sumcheck_rows_fused, 0);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    let after = optimization_stats_snapshot();
    // Optimization does not fire
    assert_eq!(after.canonical_sumcheck_rows_seen, 0);
    assert_eq!(after.canonical_sumcheck_rows_fused, 0);

    // Verify mathematical correctness of the fallback result:
    // R(t) = Product_{b ∈ {0,1}^2} P(t, b)
    let Value::Poly(ref orig_poly) = poly_val else { unreachable!() };
    for t_idx in 0..4 {
        let t = <B as backend::ArkConfig>::F::from(t_idx);
        let mut expected = <B as backend::ArkConfig>::F::one();
        for tail_index in 0..4 {
            let b0 = if tail_index & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            let b1 = if (tail_index >> 1) & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            expected *= orig_poly.evaluate_mv(&vec![t, b0, b1]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
#[serial]
fn test_reduce_map_fused_optimization_fallback_on_non_mle() {
    use backend::optimization::{optimization_stats_snapshot, reset_optimization_stats};
    use crate::tests::test_helpers::execute_graph;
    use backend::{PolyVariant, VirtualPolynomial};
    use ark_poly::multivariate::{SparsePolynomial as SparseMultivariatePolynomial, SparseTerm as MultiSparseTerm, Term};

    // Poly<F, 3, 2> is a polynomial of 3 variables and max degree 2 (non-MLE).
    // The optimization should still match at graph level (additive, canonical range, domain size 4),
    // and route to value_hypercube_reduce_selected, which should detect it's not MLE and
    // fallback to generic evaluation, computing the correct polynomial and not triggering errors.
    let src = r#"
        fn test_non_mle<F: Field>(private poly: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(poly, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs.0[0];

    let mut inputs = Ctx::new();
    
    // We construct a non-MLE polynomial (e.g. X_0^2 + X_1 + X_2) manually
    let terms = vec![
        (<B as backend::ArkConfig>::F::one(), MultiSparseTerm::new(vec![(0, 2)])),
        (<B as backend::ArkConfig>::F::one(), MultiSparseTerm::new(vec![(1, 1)])),
        (<B as backend::ArkConfig>::F::one(), MultiSparseTerm::new(vec![(2, 1)])),
    ];
    let p = SparseMultivariatePolynomial {
        num_vars: 3,
        terms,
    };
    let poly_variant = PolyVariant::SparseMultivariate(p);
    let poly_val = Value::Poly(VirtualPolynomial::from_poly(poly_variant));
    inputs.insert(&lang::id::Vid::from("poly"), &poly_val);

    reset_optimization_stats();
    let before = optimization_stats_snapshot();
    assert_eq!(before.canonical_sumcheck_rows_seen, 0);
    assert_eq!(before.canonical_sumcheck_rows_fused, 0);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    let after = optimization_stats_snapshot();
    // Optimization kernel is entered (seen is incremented),
    // and completes with fused counter incremented as well.
    assert_eq!(after.canonical_sumcheck_rows_seen, 1);
    assert_eq!(after.canonical_sumcheck_rows_fused, 1);

    // Verify mathematical correctness of the result:
    // R(t) = Sum_{b ∈ {0,1}^2} P(t, b)
    // For P(t, b0, b1) = t^2 + b0 + b1, the sum over b0, b1 in {0,1} is 4*t^2 + 4.
    for t_idx in 0..4 {
        let t = <B as backend::ArkConfig>::F::from(t_idx);
        let expected = t * t * <B as backend::ArkConfig>::F::from(4) + <B as backend::ArkConfig>::F::from(4);
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}

#[test]
#[serial]
fn test_reduce_map_fused_optimization_skips_modified_loop_param() {
    use backend::optimization::{optimization_stats_snapshot, reset_optimization_stats};
    use crate::tests::test_helpers::execute_graph;

    // The loop parameter is modified inside the eval call: eval<0>(poly, [t + one for t in tail]).
    // The optimization must skip because the evaluation points are not the exact loop parameter tail coordinates.
    let src = r#"
        fn test_modified<F: Field>(private poly: Poly<F, 3, 1>) -> Poly<F, 1, 1> {
            let zero: F = 0;
            let one = zero + 1;
            reduce(+, [
                eval<0>(poly, [t + one for t in tail])
                for tail in [
                    [(((i / (2^j)) % 2) * one) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;
    let graphs = parse_and_build(src);
    let dag = &graphs.0[0];

    let mut inputs = Ctx::new();
    let mut rng = StdRng::seed_from_u64(0);
    let poly_val = Value::<B>::random(&mut rng, &ATyp::Mle(3));
    inputs.insert(&lang::id::Vid::from("poly"), &poly_val.clone());

    reset_optimization_stats();
    let before = optimization_stats_snapshot();
    assert_eq!(before.canonical_sumcheck_rows_seen, 0);
    assert_eq!(before.canonical_sumcheck_rows_fused, 0);

    let result = execute_graph(dag, inputs).unwrap();
    let Value::Poly(got_poly) = result else {
        panic!("Expected a polynomial result, found {:?}", result);
    };

    let after = optimization_stats_snapshot();
    // Optimization does not fire because fixed is modified (not exactly the loop parameter)
    assert_eq!(after.canonical_sumcheck_rows_seen, 0);
    assert_eq!(after.canonical_sumcheck_rows_fused, 0);

    // Verify mathematical correctness of the non-optimized result:
    // R(t) = Sum_{b ∈ {0,1}^2} P(t, b0+1, b1+1)
    let Value::Poly(ref orig_poly) = poly_val else { unreachable!() };
    for t_idx in 0..4 {
        let t = <B as backend::ArkConfig>::F::from(t_idx);
        let mut expected = <B as backend::ArkConfig>::F::zero();
        for tail_index in 0..4 {
            let b0 = if tail_index & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            let b1 = if (tail_index >> 1) & 1 == 1 { <B as backend::ArkConfig>::F::one() } else { <B as backend::ArkConfig>::F::zero() };
            expected += orig_poly.evaluate_mv(&vec![
                t,
                b0 + <B as backend::ArkConfig>::F::one(),
                b1 + <B as backend::ArkConfig>::F::one(),
            ]).unwrap();
        }
        assert_eq!(got_poly.evaluate_uv(&t), expected);
    }
}



