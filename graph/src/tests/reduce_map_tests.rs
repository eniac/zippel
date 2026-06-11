//! Tests for the generalized loop-fusion ops `Op::Map` / `Op::ReduceMap`
//! / `Op::LoopParam` and the streaming reduce-map evaluator.

use crate::eval::eval_op;
use crate::tests::test_helpers::scalar;
use crate::{GOp, Op, Ref, UDags, mk};
use backend::{ATyp, ArkBls12_381, Value};
use lang::ast::{BinOp, UModule};
use rand::SeedableRng;
use rand::rngs::StdRng;
use share::Ctx;
use std::collections::HashMap;
use std::sync::Arc;

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
