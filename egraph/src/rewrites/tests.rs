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

#[test]
fn test_pairing_rewrite_verify() {
    let mut eg: ZEgraph = EGraph::default();

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

    let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
    let pair2 = eg.add(ZIR::Pair([g1_c, g2_d]));

    // Bug 1: use Verify instead of Assert
    let verify = eg.add(ZIR::Verify([pair1, pair2]));

    saturate(&mut eg);

    let verify_class = &eg[eg.find(verify)];
    let has_dot_verify = verify_class.nodes.iter().any(|n| {
        if let ZIR::Verify([dot, _gt_zero]) = n {
            let dot_class = &eg[eg.find(*dot)];
            dot_class.nodes.iter().any(|dn| matches!(dn, ZIR::Dot(_)))
        } else {
            false
        }
    });
    assert!(
        has_dot_verify,
        "pairing rewrite should work for Verify: Verify(Dot(...), Constant(GT_zero))"
    );
}

#[test]
fn test_pairing_rewrite_n_pairs() {
    let mut eg: ZEgraph = EGraph::default();

    // Test Add-chained pairs on both sides:
    // lhs = Add(Pair(a,b), Pair(e,f))
    // rhs = Add(Pair(c,d), Pair(g,h))
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
    let g1_e = eg.add(ZIR::Neg([g1_a]));
    let g2_f = eg.add(ZIR::Constant(Value::G2(
        <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
    )));
    let g1_g = eg.add(ZIR::Neg([g1_c]));
    let g2_h = eg.add(ZIR::Constant(Value::G2(
        <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
    )));

    // lhs: Add(Pair(a,b), Pair(e,f))
    let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
    let pair2 = eg.add(ZIR::Pair([g1_e, g2_f]));
    let lhs = eg.add(ZIR::Add([pair1, pair2]));

    // rhs: Add(Pair(c,d), Pair(g,h))
    let pair3 = eg.add(ZIR::Pair([g1_c, g2_d]));
    let pair4 = eg.add(ZIR::Pair([g1_g, g2_h]));
    let rhs = eg.add(ZIR::Add([pair3, pair4]));

    let assert = eg.add(ZIR::Assert([lhs, rhs]));

    saturate(&mut eg);

    // The rewrite should fire and produce a Dot with Vec children.
    let assert_class = &eg[eg.find(assert)];
    let has_dot = assert_class.nodes.iter().any(|n| {
        if let ZIR::Assert([dot, _]) = n {
            let dot_class = &eg[eg.find(*dot)];
            dot_class.nodes.iter().any(|dn| {
                if let ZIR::Dot([a, b]) = dn {
                    let a_class = &eg[eg.find(*a)];
                    let b_class = &eg[eg.find(*b)];
                    a_class.nodes.iter().any(|vn| {
                        if let ZIR::Vec(ids) = vn {
                            // Should have 4 G1 elements (2 from each side)
                            ids.len() == 4
                        } else {
                            false
                        }
                    }) && b_class.nodes.iter().any(|vn| {
                        if let ZIR::Vec(ids) = vn {
                            // Should have 4 G2 elements
                            ids.len() == 4
                        } else {
                            false
                        }
                    })
                } else {
                    false
                }
            })
        } else {
            false
        }
    });
    assert!(has_dot, "pairing rewrite should fire for Add-chained pairs");
}

#[test]
fn test_pairing_rewrite_negates_g1s_both_forms() {
    let mut eg: ZEgraph = EGraph::default();

    // Verify the two Dot forms are produced (negating G1s, which is cheaper):
    // Form 1: dot([g1_a, neg(g1_c)], [g2_b, g2_d])  — negate RHS G1s
    // Form 2: dot([neg(g1_a), g1_c], [g2_b, g2_d])  — negate LHS G1s
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

    let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
    let pair2 = eg.add(ZIR::Pair([g1_c, g2_d]));
    let assert = eg.add(ZIR::Assert([pair1, pair2]));

    saturate(&mut eg);

    let assert_class = &eg[eg.find(assert)];

    // Check that G1 Vec has Neg nodes (G1s are negated)
    let g1_has_neg = assert_class.nodes.iter().any(|n| {
        if let ZIR::Assert([dot, _]) = n {
            let dot_class = &eg[eg.find(*dot)];
            dot_class.nodes.iter().any(|dn| {
                if let ZIR::Dot([g1_vec, _]) = dn {
                    let g1_class = &eg[eg.find(*g1_vec)];
                    g1_class.nodes.iter().any(|vn| {
                        if let ZIR::Vec(ids) = vn {
                            ids.iter().any(|id| {
                                eg[eg.find(*id)]
                                    .nodes
                                    .iter()
                                    .any(|n| matches!(n, ZIR::Neg(_)))
                            })
                        } else {
                            false
                        }
                    })
                } else {
                    false
                }
            })
        } else {
            false
        }
    });
    assert!(
        g1_has_neg,
        "pairing rewrite should negate G1s (cheaper than G2s)"
    );

    // Check that G2 Vec has NO Neg nodes (G2s are never negated)
    let g2_has_no_neg = assert_class.nodes.iter().any(|n| {
        if let ZIR::Assert([dot, _]) = n {
            let dot_class = &eg[eg.find(*dot)];
            dot_class.nodes.iter().any(|dn| {
                if let ZIR::Dot([_, g2_vec]) = dn {
                    let g2_class = &eg[eg.find(*g2_vec)];
                    g2_class.nodes.iter().any(|vn| {
                        if let ZIR::Vec(ids) = vn {
                            !ids.iter().any(|id| {
                                eg[eg.find(*id)]
                                    .nodes
                                    .iter()
                                    .any(|n| matches!(n, ZIR::Neg(_)))
                            })
                        } else {
                            false
                        }
                    })
                } else {
                    false
                }
            })
        } else {
            false
        }
    });
    assert!(g2_has_no_neg, "pairing rewrite should NOT negate any G2s");
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

#[test]
fn test_neg_neg() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    let neg1 = eg.add(ZIR::Neg([a]));
    let neg2 = eg.add(ZIR::Neg([neg1]));

    saturate(&mut eg);

    // (neg (neg a)) should be unified with a
    assert_eq!(
        eg.find(neg2),
        eg.find(a),
        "neg-neg should unify (neg (neg a)) with a"
    );
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

// =====================================================================
// LICM (xi): Map(tag, [dom, op(e, rest)]) → op(e, Map(tag, [dom, rest]))
// =====================================================================

#[test]
fn test_licm_lifts_scalar_from_map() {
    let mut eg: ZEgraph = EGraph::default();

    // scalar m (loop-invariant, no side effect)
    let m = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    // domain vector
    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    ])));
    // loop variable Var(tag)
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Add(m, Var(tag))
    let body = eg.add(ZIR::Add([m, var_i]));
    // Map(tag, [dom, body])
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    // The Map e-class should now contain Add(m, Map(tag, [dom, Var(tag)]))
    let map_class = &eg[eg.find(map)];
    let has_lifted_add = map_class.nodes.iter().any(|n| {
        if let ZIR::Add([a, b]) = n {
            // a should be the scalar m
            let a_class = &eg[eg.find(*a)];
            let a_is_scalar = a_class.nodes.iter().any(|an| {
                matches!(an, ZIR::Constant(Value::Scalar(v))
                    if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(42))
            });
            // b should be a Map
            let b_class = &eg[eg.find(*b)];
            let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            a_is_scalar && b_is_map
        } else {
            false
        }
    });
    assert!(
        has_lifted_add,
        "LICM should produce Add(m, Map(tag, [dom, Var(tag)])) in the map e-class"
    );
}

#[test]
fn test_licm_blocked_by_random() {
    let mut eg: ZEgraph = EGraph::default();

    // Random node — has_side_effect = true
    let r = eg.add(ZIR::Random(Symbol::from("r1"), false));
    // domain vector
    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    ])));
    // loop variable Var(tag)
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Add(r, Var(tag)) — r is loop-invariant but has side effect
    let body = eg.add(ZIR::Add([r, var_i]));
    // Map(tag, [dom, body])
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    // LICM should NOT fire: the Map e-class should NOT contain
    // Add(r, Map(tag, [dom, Var(tag)]))
    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Add([a, b]) = n {
            // a should be the Random node
            let a_class = &eg[eg.find(*a)];
            let a_is_random = a_class
                .nodes
                .iter()
                .any(|an| matches!(an, ZIR::Random(_, _)));
            // b should be a Map
            let b_class = &eg[eg.find(*b)];
            let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            a_is_random && b_is_map
        } else {
            false
        }
    });
    assert!(
        !has_lifted,
        "LICM should NOT lift Random out of Map (has_side_effect blocks it)"
    );
}

#[test]
fn test_licm_blocked_by_loop_variant() {
    let mut eg: ZEgraph = EGraph::default();

    // Two loop variables with different tags
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // domain vector
    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    ])));
    // body = Add(Var(tag), Var(tag)) — Var(tag) depends on tag (not loop-invariant)
    let body = eg.add(ZIR::Add([var_i, var_i]));
    // Map(tag, [dom, body])
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    // LICM should NOT fire: Var(tag) is not loop-invariant
    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Add([a, b]) = n {
            let b_class = &eg[eg.find(*b)];
            let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            // a should NOT be Var(tag) lifted out — check if a is Var
            let a_class = &eg[eg.find(*a)];
            let a_is_var = a_class.nodes.iter().any(|an| matches!(an, ZIR::Var(_)));
            a_is_var && b_is_map
        } else {
            false
        }
    });
    assert!(
        !has_lifted,
        "LICM should NOT lift Var(tag) out of Map (not loop-invariant)"
    );
}

// =====================================================================
// LICM: extended ops (Rem, Pow, Pair) + second-operand lifting
// =====================================================================

#[test]
fn test_licm_lifts_second_operand() {
    let mut eg: ZEgraph = EGraph::default();

    // scalar m (loop-invariant)
    let m = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(42),
    )));
    // domain vector
    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    ])));
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Sub(Var(tag), m) — m is the second operand, loop-invariant
    let body = eg.add(ZIR::Sub([var_i, m]));
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    // Should produce Sub(Map(tag, [dom, Var(tag)]), m)
    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Sub([a, b]) = n {
            // a should be a Map
            let a_class = &eg[eg.find(*a)];
            let a_is_map = a_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            // b should be the scalar m
            let b_class = &eg[eg.find(*b)];
            let b_is_scalar = b_class.nodes.iter().any(|bn| {
                matches!(bn, ZIR::Constant(Value::Scalar(v))
                    if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(42))
            });
            a_is_map && b_is_scalar
        } else {
            false
        }
    });
    assert!(
        has_lifted,
        "LICM should lift second operand: Sub(Map(tag, [dom, Var(tag)]), m)"
    );
}

#[test]
fn test_licm_rem() {
    let mut eg: ZEgraph = EGraph::default();

    let m = eg.add(ZIR::Constant(Value::Index(7)));
    let dom = eg.add(ZIR::Constant(Value::VecIndex(vec![0, 1, 2, 3])));
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Rem(Var(tag), m) — m is loop-invariant
    let body = eg.add(ZIR::Rem([var_i, m]));
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Rem([a, b]) = n {
            // a should be a Map, b should be the constant 7
            let a_class = &eg[eg.find(*a)];
            let a_is_map = a_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            let b_class = &eg[eg.find(*b)];
            let b_is_const = b_class
                .nodes
                .iter()
                .any(|bn| matches!(bn, ZIR::Constant(Value::Index(7))));
            a_is_map && b_is_const
        } else {
            false
        }
    });
    assert!(has_lifted, "LICM should lift Rem's invariant operand");
}

#[test]
fn test_licm_pow() {
    let mut eg: ZEgraph = EGraph::default();

    // exponent is loop-invariant scalar
    let exp = eg.add(ZIR::Constant(Value::Index(3)));
    let dom = eg.add(ZIR::Constant(Value::VecIndex(vec![0, 1, 2])));
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Pow(Var(tag), exp) — exp is second operand, loop-invariant
    let body = eg.add(ZIR::Pow([var_i, exp]));
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Pow([a, b]) = n {
            // a should be a Map, b should be the constant 3
            let a_class = &eg[eg.find(*a)];
            let a_is_map = a_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            let b_class = &eg[eg.find(*b)];
            let b_is_const = b_class
                .nodes
                .iter()
                .any(|bn| matches!(bn, ZIR::Constant(Value::Index(3))));
            a_is_map && b_is_const
        } else {
            false
        }
    });
    assert!(has_lifted, "LICM should lift Pow's invariant operand");
}

#[test]
fn test_licm_pow_lifts_base() {
    let mut eg: ZEgraph = EGraph::default();

    // base is loop-invariant scalar, exponent is Var(tag) (loop-variant)
    // LICM should lift the base: Pow(base, Map(tag, [dom, Var(tag)]))
    // This is now valid because lub_pow supports scalar ^ Vec (broadcast base).
    let base = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let dom = eg.add(ZIR::Constant(Value::VecIndex(vec![0, 1, 2])));
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Pow(base, Var(tag)) — base is first operand, loop-invariant
    let body = eg.add(ZIR::Pow([base, var_i]));
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    // LICM should lift the base: Pow(base, Map(tag, [dom, Var(tag)]))
    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Pow([a, b]) = n {
            // a should be the scalar base, b should be a Map
            let a_class = &eg[eg.find(*a)];
            let a_is_scalar = a_class.nodes.iter().any(|an| {
                matches!(an, ZIR::Constant(Value::Scalar(v))
                    if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(2))
            });
            let b_class = &eg[eg.find(*b)];
            let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            a_is_scalar && b_is_map
        } else {
            false
        }
    });
    assert!(
        has_lifted,
        "LICM should lift Pow's base: Pow(scalar, Map(...)) is now valid"
    );
}

#[test]
fn test_licm_pair() {
    let mut eg: ZEgraph = EGraph::default();

    // G1 scalar (loop-invariant)
    let g1 = eg.add(ZIR::Constant(Value::G1(
        <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
    )));
    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    ])));
    let tag = Symbol::from("i");
    let var_i = eg.add(ZIR::Var(tag));
    // body = Pair(g1, Var(tag)) — g1 is loop-invariant
    let body = eg.add(ZIR::Pair([g1, var_i]));
    let map = eg.add(ZIR::Map(tag, [dom, body]));

    saturate(&mut eg);

    let map_class = &eg[eg.find(map)];
    let has_lifted = map_class.nodes.iter().any(|n| {
        if let ZIR::Pair([a, b]) = n {
            // a should be the G1 constant, b should be a Map
            let a_class = &eg[eg.find(*a)];
            let a_is_g1 = a_class
                .nodes
                .iter()
                .any(|an| matches!(an, ZIR::Constant(Value::G1(_))));
            let b_class = &eg[eg.find(*b)];
            let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
            a_is_g1 && b_is_map
        } else {
            false
        }
    });
    assert!(has_lifted, "LICM should lift Pair's invariant G1 operand");
}

// =====================================================================
// Constant propagation (vii)
// =====================================================================

#[test]
fn test_const_prop_add() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(3),
    )));
    let b = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(4),
    )));
    let add = eg.add(ZIR::Add([a, b]));

    saturate(&mut eg);

    // Add(3, 4) should be unified with Constant(7)
    let add_class = &eg[eg.find(add)];
    let has_seven = add_class.nodes.iter().any(|n| {
        matches!(n, ZIR::Constant(Value::Scalar(v))
            if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(7))
    });
    assert!(has_seven, "const-prop should fold Add(3, 4) to Constant(7)");
}

#[test]
fn test_const_prop_mul() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(5),
    )));
    let b = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(6),
    )));
    let mul = eg.add(ZIR::Mul([a, b]));

    saturate(&mut eg);

    // Mul(5, 6) should be unified with Constant(30)
    let mul_class = &eg[eg.find(mul)];
    let has_thirty = mul_class.nodes.iter().any(|n| {
        matches!(n, ZIR::Constant(Value::Scalar(v))
            if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(30))
    });
    assert!(
        has_thirty,
        "const-prop should fold Mul(5, 6) to Constant(30)"
    );
}

#[test]
fn test_const_prop_sub() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(10),
    )));
    let b = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(3),
    )));
    let sub = eg.add(ZIR::Sub([a, b]));

    saturate(&mut eg);

    let sub_class = &eg[eg.find(sub)];
    let has_seven = sub_class.nodes.iter().any(|n| {
        matches!(n, ZIR::Constant(Value::Scalar(v))
            if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(7))
    });
    assert!(
        has_seven,
        "const-prop should fold Sub(10, 3) to Constant(7)"
    );
}

#[test]
fn test_const_prop_does_not_fire_on_non_constant() {
    let mut eg: ZEgraph = EGraph::default();
    let a = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(3),
    )));
    // Var is not a Constant
    let var = eg.add(ZIR::Var(Symbol::from("x")));
    let add = eg.add(ZIR::Add([a, var]));

    saturate(&mut eg);

    // Add(3, Var(x)) should NOT be folded to a Constant
    let add_class = &eg[eg.find(add)];
    let has_constant = add_class
        .nodes
        .iter()
        .any(|n| matches!(n, ZIR::Constant(_)));
    assert!(
        !has_constant,
        "const-prop should NOT fire when one operand is not Constant"
    );
}

// =====================================================================
// Loop fusion
// =====================================================================

#[test]
fn test_map_fusion_basic() {
    let mut eg: ZEgraph = EGraph::default();

    // domain vector [0, 1, 2]
    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    ])));

    // Inner map: Map(tag1, [dom, Add(Var(tag1), 1)])
    let tag1 = Symbol::from("x");
    let var_x = eg.add(ZIR::Var(tag1));
    let one = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    )));
    let body1 = eg.add(ZIR::Add([var_x, one]));
    let inner_map = eg.add(ZIR::Map(tag1, [dom, body1]));

    // Outer map: Map(tag2, [inner_map, Mul(Var(tag2), 2)])
    let tag2 = Symbol::from("y");
    let var_y = eg.add(ZIR::Var(tag2));
    let two = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let body2 = eg.add(ZIR::Mul([var_y, two]));
    let outer_map = eg.add(ZIR::Map(tag2, [inner_map, body2]));

    saturate(&mut eg);

    // After fusion, the outer_map e-class should contain a Map with
    // tag1 as the binder (the inner map's tag) and dom as the domain.
    // Substitution of Var(tag2) → body1 is done by rebuilding body2,
    // so the fused body should NOT contain tag2 in its free_vars.
    let outer_class = &eg[eg.find(outer_map)];
    let has_fused = outer_class.nodes.iter().any(|n| {
        if let ZIR::Map(t, [d, b]) = n {
            // The binder should be tag1 (the inner map's tag)
            // The body should NOT reference tag2 (the outer tag)
            *t == tag1
                && eg.find(*d) == eg.find(dom)
                && !eg[eg.find(*b)].data.free_vars.contains(&tag2)
        } else {
            false
        }
    });
    assert!(
        has_fused,
        "loop fusion should produce Map(tag1, [dom, fused_body]) without tag2"
    );
}

#[test]
fn test_map_fusion_blocked_by_side_effect() {
    let mut eg: ZEgraph = EGraph::default();

    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    ])));

    // Inner map body has a side effect (Random)
    let tag1 = Symbol::from("x");
    let var_x = eg.add(ZIR::Var(tag1));
    let rand = eg.add(ZIR::Random(Symbol::from("r1"), false));
    let body1 = eg.add(ZIR::Add([var_x, rand]));
    let inner_map = eg.add(ZIR::Map(tag1, [dom, body1]));

    // Outer map
    let tag2 = Symbol::from("y");
    let var_y = eg.add(ZIR::Var(tag2));
    let two = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let body2 = eg.add(ZIR::Mul([var_y, two]));
    let outer_map = eg.add(ZIR::Map(tag2, [inner_map, body2]));

    saturate(&mut eg);

    // Fusion should NOT fire because body1 has a side effect (Random)
    let outer_class = &eg[eg.find(outer_map)];
    let has_fused = outer_class.nodes.iter().any(|n| {
        if let ZIR::Map(t, [_, b]) = n {
            *t == tag1 && !eg[eg.find(*b)].data.free_vars.contains(&tag2)
        } else {
            false
        }
    });
    assert!(
        !has_fused,
        "loop fusion should NOT fire when inner body has side effect"
    );
}

#[test]
fn test_map_fusion_blocked_when_body2_no_tag2() {
    let mut eg: ZEgraph = EGraph::default();

    let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
        <ArkBls12_381 as backend::ArkConfig>::F::from(0),
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    ])));

    // Inner map: Map(tag1, [dom, Add(Var(tag1), 1)])
    let tag1 = Symbol::from("x");
    let var_x = eg.add(ZIR::Var(tag1));
    let one = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(1),
    )));
    let body1 = eg.add(ZIR::Add([var_x, one]));
    let inner_map = eg.add(ZIR::Map(tag1, [dom, body1]));

    // Outer map: body2 does NOT reference tag2 (uses a constant instead)
    let tag2 = Symbol::from("y");
    let two = eg.add(ZIR::Constant(Value::Scalar(
        <ArkBls12_381 as backend::ArkConfig>::F::from(2),
    )));
    let body2 = eg.add(ZIR::Mul([two, two])); // no Var(tag2)
    let outer_map = eg.add(ZIR::Map(tag2, [inner_map, body2]));

    saturate(&mut eg);

    // Fusion should NOT fire because body2 doesn't reference tag2
    let outer_class = &eg[eg.find(outer_map)];
    let has_fused = outer_class.nodes.iter().any(|n| {
        if let ZIR::Map(t, [_, b]) = n {
            *t == tag1 && !eg[eg.find(*b)].data.free_vars.contains(&tag2)
        } else {
            false
        }
    });
    assert!(
        !has_fused,
        "loop fusion should NOT fire when body2 doesn't reference tag2"
    );
}
