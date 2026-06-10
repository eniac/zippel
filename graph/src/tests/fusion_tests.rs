use crate::{Op, UDags};
use backend::ArkBls12_381;
use lang::ast::UModule;
use share::Ctx;

type B = ArkBls12_381;

fn parse_and_build(src: &str) -> UDags<B> {
    let module = UModule::from_str(src)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    UDags::<B>::from_module(module).unwrap()
}

fn count_fused_hypercube_reduce(graphs: &UDags<B>) -> usize {
    graphs
        .0
        .iter()
        .map(|dag| {
            dag.op_nodes()
                .into_iter()
                .filter(|node| {
                    dag[*node]
                        .op()
                        .is_some_and(|op| matches!(op.get(), Op::HypercubeReduceSelected(_, _, _)))
                })
                .count()
        })
        .sum()
}

#[test]
fn inline_canonical_sumcheck_reduce_lowers_to_private_hypercube_reduce() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
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
    let dag = &graphs[0];
    let mut fused = 0usize;
    let mut selected_eval = 0usize;
    let mut materialized_selected_vec = 0usize;

    for node_index in dag.op_nodes() {
        if let Some(op) = dag[node_index].op() {
            match op.get() {
                Op::HypercubeReduceSelected(_, range, tail_num_vars) => {
                    fused += 1;
                    assert_eq!(range.start, 0);
                    assert_eq!(range.end, 1);
                    assert_eq!(*tail_num_vars, 2);
                }
                Op::Evaluate(_, Some(_), Some(_)) => selected_eval += 1,
                Op::Vec(children) => {
                    if children
                        .iter()
                        .any(|child| matches!(child.get(), Op::Evaluate(_, Some(_), Some(_))))
                    {
                        materialized_selected_vec += 1;
                    }
                }
                _ => {}
            }
        }
    }

    assert_eq!(fused, 1, "expected exactly one fused hypercube reduce op");
    assert_eq!(
        selected_eval, 0,
        "canonical fused lowering must not leave selected-eval op nodes"
    );
    assert_eq!(
        materialized_selected_vec, 0,
        "canonical fused lowering must not build a Vec of selected-eval terms"
    );
}

#[test]
fn let_bound_canonical_tail_domain_lowers_to_private_hypercube_reduce() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
            let zero: F = 0;
            let one = zero + 1;
            let tails = [
                [(((i / (2^j)) % 2) * one) for j in 0..2]
                for i in 0..4
            ];
            reduce(+, [eval<0>(poly, tail) for tail in tails])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        1,
        "let-bound canonical tail provenance should preserve the fused fast path"
    );
}

#[test]
fn binder_dependent_polynomial_operand_declines_fusion_but_graph_builds() {
    let src = r#"
        fn round<F: Field>(private polys: [Poly<F, 3, 2>; 2]) -> Poly<F, 1, 2> {
            reduce(+, [
                eval<0>(polys[tail[0]], tail)
                for tail in [
                    [((i / (2^j)) % 2) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "binder-dependent polynomial operands must fall back to ordinary map/reduce lowering"
    );
}

#[test]
fn public_argument_named_one_does_not_prove_tail_scale_one() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>, public one: F) -> Poly<F, 1, 2> {
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

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "spelling an input argument `one` is not constant provenance"
    );
}

#[test]
fn inner_tail_binder_named_one_shadows_outer_constant_one_for_inline_domain() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
            let one: F = 1;
            reduce(+, [
                eval<0>(poly, tail)
                for tail in [
                    [(((i / (2^one)) % 2) * one) for one in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "inner map binder `one` must shadow outer constant-one provenance during fusion classification"
    );
}

#[test]
fn inner_tail_binder_named_one_shadows_outer_constant_one_for_let_bound_domain() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
            let one: F = 1;
            let tails = [
                [(((i / (2^one)) % 2) * one) for one in 0..2]
                for i in 0..4
            ];
            reduce(+, [eval<0>(poly, tail) for tail in tails])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "let-bound tail provenance must not retain outer constant-one proof across an inner `one` binder"
    );
}

#[test]
fn pure_self_difference_zero_plus_one_tail_scale_lowers_to_private_hypercube_reduce() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>, public points: [F; 2]) -> Poly<F, 1, 2> {
            let zero = points[0] - points[0];
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

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        1,
        "pure `x - x` zero plus one should prove canonical Boolean tail scaling"
    );
}

#[test]
fn literal_one_tail_scale_lowers_to_private_hypercube_reduce() {
    let src = r#"
        fn round<F: Field>(private poly: Poly<F, 3, 2>) -> Poly<F, 1, 2> {
            reduce(+, [
                eval<0>(poly, tail)
                for tail in [
                    [(((i / (2^j)) % 2) * 1) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        1,
        "literal `* 1` should prove canonical Boolean tail scaling"
    );
}

#[test]
fn inline_random_polynomial_operand_declines_fusion_but_graph_builds() {
    let src = r#"
        fn round<F: Field>() -> Poly<F, 1, 1> {
            reduce(+, [
                eval<0>(mle([random<F> for k in 0..8]), tail)
                for tail in [
                    [((i / (2^j)) % 2) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "inline random polynomial operands must not be hoisted into the fused fast path"
    );
}

#[test]
fn inline_challenge_polynomial_operand_declines_fusion_but_graph_builds() {
    let src = r#"
        fn round<F: Field>() -> Poly<F, 1, 1> {
            reduce(+, [
                eval<0>(mle([challenge<F> for k in 0..8]), tail)
                for tail in [
                    [((i / (2^j)) % 2) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "inline challenge polynomial operands must not be hoisted into the fused fast path"
    );
}

#[test]
fn inline_let_random_polynomial_operand_declines_fusion_but_graph_builds() {
    let src = r#"
        fn round<F: Field>() -> Poly<F, 1, 1> {
            reduce(+, [
                eval<0>((let evs = [random<F> for k in 0..8]; mle(evs)), tail)
                for tail in [
                    [((i / (2^j)) % 2) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "inline let/random polynomial operands must not be hoisted into the fused fast path"
    );
}

#[test]
fn function_app_polynomial_operand_declines_fusion_but_graph_builds() {
    let src = r#"
        fn make_poly<F: Field>(private evs: [F; 8]) -> Poly<F, 3, 1> {
            mle(evs)
        }

        fn round<F: Field>(private evs: [F; 8]) -> Poly<F, 1, 1> {
            reduce(+, [
                eval<0>(make_poly(evs), tail)
                for tail in [
                    [((i / (2^j)) % 2) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        0,
        "function-call polynomial operands without a local hoist proof must not fuse"
    );
}

#[test]
fn let_bound_random_polynomial_variable_preserves_fusion() {
    let src = r#"
        fn round<F: Field>() -> Poly<F, 1, 1> {
            let poly = mle([random<F> for k in 0..8]);
            reduce(+, [
                eval<0>(poly, tail)
                for tail in [
                    [((i / (2^j)) % 2) for j in 0..2]
                    for i in 0..4
                ]
            ])
        }
    "#;

    let graphs = parse_and_build(src);

    assert_eq!(
        count_fused_hypercube_reduce(&graphs),
        1,
        "an already-bound polynomial variable should remain hoist-safe for fusion"
    );
}
