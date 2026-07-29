//! Tests for Phase 2 rewrites.
//!
//! Each test constructs an e-graph manually, runs the rewrites via
//! `egg::Runner`, and inspects the resulting e-classes.

use ark_ff::{One, Zero};
use backend::{ArkBls12_381, Value};
use egg::{EGraph, Id, Runner, Symbol};

use crate::lang::{ZAnalysis, ZIR};
use crate::rewrites::all_zir_rewrites;

type ZEgraph = EGraph<ZIR<ArkBls12_381>, ZAnalysis<ArkBls12_381>>;

/// Helper: run all rewrites to saturation on an e-graph.
fn saturate(egraph: &mut ZEgraph) {
    let rules = all_zir_rewrites::<ArkBls12_381>();
    let runner = Runner::default()
        .with_egraph(std::mem::take(egraph))
        .run(&rules);
    *egraph = runner.egraph;
}

// =====================================================================
// Syntactic rewrites (ii): poly shape peepholes
// =====================================================================

#[test]
fn test_ifft_fft_cancellation() {
    let mut eg: ZEgraph = EGraph::default();
    let p = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    let fft = eg.add(ZIR::Fft([p]));
    let ifft = eg.add(ZIR::Ifft([fft]));

    saturate(&mut eg);

    // ifft(fft(p)) should be unified with p
    assert!(
        eg.find(ifft) == eg.find(p),
        "ifft(fft(p)) should be unified with p"
    );
}

#[test]
fn test_fft_ifft_cancellation() {
    let mut eg: ZEgraph = EGraph::default();
    let v = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    ])));
    let ifft = eg.add(ZIR::Ifft([v]));
    let fft = eg.add(ZIR::Fft([ifft]));

    saturate(&mut eg);

    assert!(
        eg.find(fft) == eg.find(v),
        "fft(ifft(v)) should be unified with v"
    );
}

#[test]
fn test_coef_poly_cancellation() {
    let mut eg: ZEgraph = EGraph::default();
    let v = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    ])));
    let poly = eg.add(ZIR::Poly([v]));
    let coef = eg.add(ZIR::Coef([poly]));

    saturate(&mut eg);

    assert!(
        eg.find(coef) == eg.find(v),
        "coef(poly(v)) should be unified with v"
    );
}

#[test]
fn test_poly_coef_cancellation() {
    let mut eg: ZEgraph = EGraph::default();
    let p = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(7),
    )));
    let coef = eg.add(ZIR::Coef([p]));
    let poly = eg.add(ZIR::Poly([coef]));

    saturate(&mut eg);

    assert!(
        eg.find(poly) == eg.find(p),
        "poly(coef(p)) should be unified with p"
    );
}

// =====================================================================
// Commute rewrites
// =====================================================================

#[test]
fn test_commute_add() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    )));
    let b = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let add_ab = eg.add(ZIR::Add([a, b]));
    let add_ba = eg.add(ZIR::Add([b, a]));

    saturate(&mut eg);

    // After commute, Add(a,b) and Add(b,a) should be in the same e-class
    assert_eq!(
        eg.find(add_ab),
        eg.find(add_ba),
        "commute-add should unify Add(a,b) with Add(b,a)"
    );
}

#[test]
fn test_commute_mul() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(3),
    )));
    let b = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(5),
    )));
    let mul_ab = eg.add(ZIR::Mul([a, b]));
    let mul_ba = eg.add(ZIR::Mul([b, a]));

    saturate(&mut eg);

    assert_eq!(
        eg.find(mul_ab),
        eg.find(mul_ba),
        "commute-mul should unify Mul(a,b) with Mul(b,a)"
    );
}

// =====================================================================
// Identity rewrites
// =====================================================================

#[test]
fn test_add_zero() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    let zero = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::zero(),
    )));
    let add_zero = eg.add(ZIR::Add([a, zero]));

    saturate(&mut eg);

    // (+ a 0) should be unified with a
    assert_eq!(
        eg.find(add_zero),
        eg.find(a),
        "add-zero should unify Add(a, 0) with a"
    );
}

#[test]
fn test_mul_one() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    let one = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::one(),
    )));
    let mul_one = eg.add(ZIR::Mul([a, one]));

    saturate(&mut eg);

    assert_eq!(
        eg.find(mul_one),
        eg.find(a),
        "mul-one should unify Mul(a, 1) with a"
    );
}

#[test]
fn test_mul_zero() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    let zero = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::zero(),
    )));
    let mul_zero = eg.add(ZIR::Mul([a, zero]));

    saturate(&mut eg);

    // (* a 0) should be unified with 0
    assert_eq!(
        eg.find(mul_zero),
        eg.find(zero),
        "mul-zero should unify Mul(a, 0) with 0"
    );
}

// =====================================================================
// mul-div-cancel (viii): (* (/ ?a ?b) ?b) → ?a [field-typed]
// =====================================================================

#[test]
fn test_mul_div_cancel() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(6),
    )));
    let b = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let div = eg.add(ZIR::Div([a, b]));
    let mul = eg.add(ZIR::Mul([div, b]));

    saturate(&mut eg);

    // (* (/ a b) b) should be unified with a (both are scalar-typed)
    assert_eq!(
        eg.find(mul),
        eg.find(a),
        "mul-div-cancel should unify Mul(Div(a,b), b) with a"
    );
}

// =====================================================================
// Seq-elimination (ix)
// =====================================================================

#[test]
fn test_seq_eliminate_no_side_effect() {
    let mut eg: ZEgraph = EGraph::default();
    let first = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    )));
    let second = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let seq = eg.add(ZIR::Seq([first, second]));

    saturate(&mut eg);

    // Seq([constant, constant]) should be eliminated → unified with second
    assert_eq!(
        eg.find(seq),
        eg.find(second),
        "seq-eliminate should unify Seq(no-side-effect, second) with second"
    );
}

#[test]
fn test_seq_eliminate_with_random() {
    let mut eg: ZEgraph = EGraph::default();
    // Random is NOT a visible side effect — Seq with Random first should be eliminated
    let random = eg.add(ZIR::Random(Symbol::from("r1"), false));
    let second = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let seq = eg.add(ZIR::Seq([random, second]));

    saturate(&mut eg);

    // Random is not a visible side effect, so Seq should be eliminated
    assert_eq!(
        eg.find(seq),
        eg.find(second),
        "seq-eliminate should eliminate Seq with Random first (not visible side effect)"
    );
}

#[test]
fn test_seq_not_eliminated_with_challenge() {
    let mut eg: ZEgraph = EGraph::default();
    // Challenge IS a visible side effect — Seq should NOT be eliminated
    let challenge = eg.add(ZIR::Challenge(Symbol::from("c1"), false));
    let second = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let seq = eg.add(ZIR::Seq([challenge, second]));

    saturate(&mut eg);

    // Challenge is a visible side effect, so Seq should NOT be eliminated
    assert_ne!(
        eg.find(seq),
        eg.find(second),
        "seq-eliminate should NOT eliminate Seq with Challenge first (visible side effect)"
    );
}

// =====================================================================
// Record projection resolution (x)
// =====================================================================

#[test]
fn test_proj_record_resolution() {
    let mut eg: ZEgraph = EGraph::default();
    let x = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    )));
    let y = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let names: Box<[Symbol]> = vec![Symbol::from("a"), Symbol::from("b")].into_boxed_slice();
    let values: Box<[Id]> = vec![x, y].into_boxed_slice();
    let record = eg.add(ZIR::Record(names, values));
    let proj_a = eg.add(ZIR::Proj(Symbol::from("a"), [record]));

    saturate(&mut eg);

    // Proj("a", Record(["a","b"], [x,y])) should be unified with x
    assert_eq!(
        eg.find(proj_a),
        eg.find(x),
        "proj-record should unify Proj(\"a\", record) with x"
    );
}

#[test]
fn test_proj_record_resolution_second_field() {
    let mut eg: ZEgraph = EGraph::default();
    let x = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    )));
    let y = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let names: Box<[Symbol]> = vec![Symbol::from("a"), Symbol::from("b")].into_boxed_slice();
    let values: Box<[Id]> = vec![x, y].into_boxed_slice();
    let record = eg.add(ZIR::Record(names, values));
    let proj_b = eg.add(ZIR::Proj(Symbol::from("b"), [record]));

    saturate(&mut eg);

    // Proj("b", Record(["a","b"], [x,y])) should be unified with y
    assert_eq!(
        eg.find(proj_b),
        eg.find(y),
        "proj-record should unify Proj(\"b\", record) with y"
    );
}

#[test]
fn test_proj_record_blocked_by_side_effect() {
    let mut eg: ZEgraph = EGraph::default();
    // If the record contains a Challenge (visible side effect),
    // the projection should NOT be resolved.
    let challenge = eg.add(ZIR::Challenge(Symbol::from("c1"), false));
    let y = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let names: Box<[Symbol]> = vec![Symbol::from("a"), Symbol::from("b")].into_boxed_slice();
    let values: Box<[Id]> = vec![challenge, y].into_boxed_slice();
    let record = eg.add(ZIR::Record(names, values));
    let proj_a = eg.add(ZIR::Proj(Symbol::from("a"), [record]));

    saturate(&mut eg);

    // Record has a visible side effect (Challenge), so Proj should NOT be resolved
    assert_ne!(
        eg.find(proj_a),
        eg.find(challenge),
        "proj-record should NOT resolve when record has visible side effect"
    );
}

// =====================================================================
// Pairing rewrite (i)
// =====================================================================

#[test]
fn test_pairing_rewrite() {
    let mut eg: ZEgraph = EGraph::default();

    // Create G1 and G2 zero elements for the test
    let g1_a = eg.add(ZIR::Constant(Value::G1(
        <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
    )));
    let g2_b = eg.add(ZIR::Constant(Value::G2(
        <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
    )));
    let g1_c = eg.add(ZIR::Constant(Value::G1(
        <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
    )));
    let g2_d = eg.add(ZIR::Constant(Value::G2(
        <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
    )));

    // Build Pair(a, b) and Pair(c, d)
    let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
    let pair2 = eg.add(ZIR::Pair([g1_c, g2_d]));

    // Build Assert(pair1, pair2)
    let assert = eg.add(ZIR::Assert([pair1, pair2]));

    saturate(&mut eg);

    // After the pairing rewrite, the Assert e-class should contain
    // an Assert(Dot(Vec(...), Vec(...)), Constant(GT_zero)) node.
    let assert_class = &eg[eg.find(assert)];
    let has_dot_assert = assert_class.nodes.iter().any(|n| {
        if let ZIR::Assert([dot, _gt_zero]) = n {
            // Check that the first child is a Dot
            let dot_class = &eg[eg.find(*dot)];
            dot_class.nodes.iter().any(|dn| matches!(dn, ZIR::Dot(_)))
        } else {
            false
        }
    });
    assert!(
        has_dot_assert,
        "pairing rewrite should produce Assert(Dot(...), Constant(GT_zero))"
    );

    // Also verify the Dot has Vec children
    let has_dot_with_vecs = assert_class.nodes.iter().any(|n| {
        if let ZIR::Assert([dot, _]) = n {
            let dot_class = &eg[eg.find(*dot)];
            dot_class.nodes.iter().any(|dn| {
                if let ZIR::Dot([a, b]) = dn {
                    let a_class = &eg[eg.find(*a)];
                    let b_class = &eg[eg.find(*b)];
                    a_class.nodes.iter().any(|vn| matches!(vn, ZIR::Vec(_)))
                        && b_class.nodes.iter().any(|vn| matches!(vn, ZIR::Vec(_)))
                } else {
                    false
                }
            })
        } else {
            false
        }
    });
    assert!(
        has_dot_with_vecs,
        "pairing rewrite Dot should have Vec children"
    );
}

// =====================================================================
// sub-self identity rewrite
// =====================================================================

#[test]
fn test_sub_self() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    let sub = eg.add(ZIR::Sub([a, a]));

    saturate(&mut eg);

    // (- a a) should be unified with a zero constant
    let zero_class = &eg[eg.find(sub)];
    let has_zero = zero_class.nodes.iter().any(|n| {
        matches!(n, ZIR::Constant(Value::Scalar(v)) if v == &<ArkBls12_381 as backend::ArkConfig>::F::zero())
    });
    assert!(has_zero, "sub-self should produce a zero constant");
}

// =====================================================================
// reduce→dot rewrite (v)
// =====================================================================

#[test]
fn test_reduce_dot() {
    let mut eg: ZEgraph = EGraph::default();

    // Create two vector-typed constants
    let vec_a = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        <ArkBls12_381 as backend::ArkConfig>::F::from(3),
    ])));
    let vec_b = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(4),
        <ArkBls12_381 as backend::ArkConfig>::F::from(5),
        <ArkBls12_381 as backend::ArkConfig>::F::from(6),
    ])));

    // Build Mul(vec_a, vec_b)
    let mul = eg.add(ZIR::Mul([vec_a, vec_b]));

    // Build Map(tag, [dom, mul]) — dom is a dummy domain (vec_a)
    let tag = Symbol::from("i");
    let map = eg.add(ZIR::Map(tag, [vec_a, mul]));

    // Build Reduce(Add, [map])
    let reduce = eg.add(ZIR::Reduce(lang::ast::BinOp::Add, [map]));

    saturate(&mut eg);

    // The reduce e-class should now contain a Dot(vec_a, vec_b) node
    let reduce_class = &eg[eg.find(reduce)];
    let has_dot = reduce_class.nodes.iter().any(|n| matches!(n, ZIR::Dot(_)));
    assert!(
        has_dot,
        "reduce-dot should produce Dot(vec_a, vec_b) in the reduce e-class"
    );
}
