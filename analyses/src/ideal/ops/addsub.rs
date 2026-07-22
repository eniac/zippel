//! Add/subtract op encoders: `add_op`, `sub_op`, and shared helpers
//! `apply_binop`, `emit_slotwise_binop`, `add_sub_op`,
//! `add_sub_op_inner`, `add_sub_leaf`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;
use lang::ast::BinOp;

use crate::Var;
use crate::frontend::Polynomial;

use super::PolySource;
use super::{EncodeCtx, link_to_polys};

pub fn apply_binop<C: ArkConfig>(
    op: BinOp,
    a: &Polynomial<C::F>,
    b: &Polynomial<C::F>,
) -> Polynomial<C::F> {
    match op {
        BinOp::Add => a + b,
        BinOp::Sub => a - b,
        other => panic!("apply_binop called with {:?}", other),
    }
}

pub fn emit_slotwise_binop<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    left: &[Polynomial<C::F>],
    right: &[Polynomial<C::F>],
    op: BinOp,
    context: &str,
) {
    let pr_slots = var.slots();
    assert_eq!(
        pr_slots.len(),
        left.len(),
        "add_sub_op {context}: ideal slot count must match left operand"
    );
    assert_eq!(
        pr_slots.len(),
        right.len(),
        "add_sub_op {context}: ideal slot count must match right operand"
    );

    let combined: Vec<Polynomial<C::F>> = left
        .iter()
        .zip(right)
        .map(|(l, r)| apply_binop::<C>(op, l, r))
        .collect();
    link_to_polys(ctx.ideal, var, combined);
}

fn add_sub_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
    op: BinOp,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    add_sub_op_inner(ctx, var, &a_src, &b_src, r_typ, op);
}

/// Slot-wise addition with type-aware broadcasting.
pub fn add_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
) {
    add_sub_op(ctx, var, a, b, r_typ, BinOp::Add);
}

/// Slot-wise subtraction with type-aware broadcasting.
pub fn sub_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
) {
    add_sub_op(ctx, var, a, b, r_typ, BinOp::Sub);
}

fn add_sub_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
    op: BinOp,
) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            let r_inner = match r_typ {
                ATyp::Vec(inner, _) => inner,
                _ => panic!("add_sub_op_inner Vec×Vec ideal must be Vec"),
            };
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                add_sub_op_inner(
                    &mut *ctx,
                    &var.with_index(i).unwrap(),
                    &a_elem,
                    &b_elem,
                    r_inner,
                    op,
                );
            }
        }
        (ATyp::Vec(_, na), _) => {
            let r_inner = match r_typ {
                ATyp::Vec(inner, _) => inner,
                _ => panic!("add_sub_op_inner Vec×_ ideal must be Vec"),
            };
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                add_sub_op_inner(
                    &mut *ctx,
                    &var.with_index(i).unwrap(),
                    &a_elem,
                    b,
                    r_inner,
                    op,
                );
            }
        }
        (_, ATyp::Vec(_, nb)) => {
            let r_inner = match r_typ {
                ATyp::Vec(inner, _) => inner,
                _ => panic!("add_sub_op_inner _×Vec ideal must be Vec"),
            };
            for i in 0..*nb {
                let b_elem = b.at_index(i).unwrap();
                add_sub_op_inner(
                    &mut *ctx,
                    &var.with_index(i).unwrap(),
                    a,
                    &b_elem,
                    r_inner,
                    op,
                );
            }
        }
        _ => {
            add_sub_leaf(ctx, var, a, b, r_typ, op);
        }
    }
}

/// Leaf-level add/sub for non-Vec operands. Dispatches based on whether
/// the operands are polynomial-like (`Uni`/`VPoly`/`Mle`) or scalar-like:
///
/// - `poly ± scalar` → lift poly, inject scalar as constant, slot-wise
/// - `scalar ± poly` → inject scalar as constant, lift poly, slot-wise
/// - `poly ± poly` → lift both to result type, slot-wise
/// - `non-poly ± non-poly` (e.g. `Base×Base`) → raw slot-wise
/// - otherwise → `uncovered_op` (mixed poly/non-poly without scalar)
fn add_sub_leaf<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
    op: BinOp,
) {
    if PolySource::<C>::is_scalar_like(b.typ()) && a.is_poly() {
        let a_lifted = a.lift_to(r_typ);
        let b_lifted = b.inject_constant_to(r_typ);
        emit_slotwise_binop(
            ctx,
            var,
            a_lifted.polys(),
            b_lifted.polys(),
            op,
            "Poly×Scalar",
        );
    } else if PolySource::<C>::is_scalar_like(a.typ()) && b.is_poly() {
        let a_lifted = a.inject_constant_to(r_typ);
        let b_lifted = b.lift_to(r_typ);
        emit_slotwise_binop(
            ctx,
            var,
            a_lifted.polys(),
            b_lifted.polys(),
            op,
            "Scalar×Poly",
        );
    } else if a.is_poly() && b.is_poly() {
        let a_lifted = a.lift_to(r_typ);
        let b_lifted = b.lift_to(r_typ);
        emit_slotwise_binop(
            ctx,
            var,
            a_lifted.polys(),
            b_lifted.polys(),
            op,
            "poly/lifted",
        );
    } else if !a.is_poly() && !b.is_poly() {
        emit_slotwise_binop(ctx, var, a.polys(), b.polys(), op, "slotwise");
    } else {
        super::uncovered_op("add-sub-mixed-poly-nonpoly", var);
    }
}

#[cfg(test)]
mod tests {
    use super::super::multi_indices;
    use super::super::test_helpers::{
        assert_ideal_slot, scalar_poly_binop_ideal, trans_clos_from_src,
    };
    use super::super::{Ideal, IdealBuilder};

    use crate::frontend::Polynomial;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::Value;
    use graph::{GOp, Op};
    use lang::ast::BinOp;

    #[test]
    fn test_add_op_vpoly_add_coefficient_wise() {
        // VPoly(2,1) has 3 coefficient slots.  a + b should bind ideal.slot(i)
        // to a.slot(i) + b.slot(i) for each of the 3 slots.
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = {
            let p = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 1), Qualifier::Witness);
            ideal.register(&p);
            p
        };
        let var_b = {
            let p = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 1), Qualifier::Witness);
            ideal.register(&p);
            p
        };

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 1), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 1),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // 3 ideal slots bound.
        for i in 0..3 {
            assert!(
                ideal.pl.contains(&var.clone().with_index(i).unwrap()),
                "add ideal slot {} missing",
                i
            );
        }
        // Each ideal slot contains exactly a.slot(i) + b.slot(i).
        for i in 0..3 {
            let a_slot = var_a.clone().with_index(i).unwrap();
            let b_slot = var_b.clone().with_index(i).unwrap();
            let stored = ideal.pl.get(&var.clone().with_index(i).unwrap()).unwrap();
            let expected =
                &Polynomial::<ark_bls12_381::Fr>::var(&a_slot) + &Polynomial::var(&b_slot);
            assert_eq!(*stored, expected, "vpoly add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_mle_add_pointwise() {
        // Mle(2) has 4 evaluation slots. add is pointwise over hypercube.
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = {
            let p = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Witness);
            ideal.register(&p);
            p
        };
        let var_b = {
            let p = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Witness);
            ideal.register(&p);
            p
        };

        let var = Var::from_node(NodeIndex::new(2), ATyp::Mle(2), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Mle(2))),
            ATyp::Mle(2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        for i in 0..4 {
            let a_slot = var_a.clone().with_index(i).unwrap();
            let b_slot = var_b.clone().with_index(i).unwrap();
            let stored = ideal.pl.get(&var.clone().with_index(i).unwrap()).unwrap();
            let expected =
                &Polynomial::<ark_bls12_381::Fr>::var(&a_slot) + &Polynomial::var(&b_slot);
            assert_eq!(*stored, expected, "mle add slot {} mismatch", i);
        }
    }

    #[test]
    fn test_add_op_vpoly_sub_coefficient_wise() {
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 2), Qualifier::Witness);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 2), Qualifier::Witness);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 2), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Sub,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 2))),
            ATyp::VPoly(2, 2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // VPoly(2,2) has 6 slots.
        assert_eq!(ATyp::VPoly(2, 2).physical_len(), 6);
        for i in 0..6 {
            let a_slot = var_a.clone().with_index(i).unwrap();
            let b_slot = var_b.clone().with_index(i).unwrap();
            let stored = ideal.pl.get(&var.clone().with_index(i).unwrap()).unwrap();
            let expected =
                &Polynomial::<ark_bls12_381::Fr>::var(&a_slot) - &Polynomial::var(&b_slot);
            assert_eq!(*stored, expected, "vpoly sub slot {} mismatch", i);
        }
    }

    #[test]
    fn ideal_vec_add_1d() {
        let src = r#"
            proto va1d<F: Field>(instance a: F, instance b: F, instance c: F, instance d: F) where a == a {
                let v = [a, b] + [c, d];
                verify(v[0] == a + c)
            }"#;
        let tc = trans_clos_from_src(src);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Vec add verify: v[0] == a + c
        // The verify expression generates an equality constraint
        assert!(
            !gr.pl.is_empty(),
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        assert!(
            gr.generating_set.len() >= 2,
            "basis should have at least 2 rows (add constraint + verify eq), got {}",
            gr.generating_set.len()
        );
    }

    #[test]
    fn ideal_vec_add_2d() {
        let src = r#"
            proto va2d<F: Field>(
                instance a: F, instance b: F, instance c: F, instance d: F,
                instance e: F, instance f: F, instance g: F, instance h: F
            ) where a == a {
                let m1 = [[a, b], [c, d]];
                let m2 = [[e, f], [g, h]];
                let m3 = m1 + m2;
                let m3r0 = m3[0];
                verify(m3r0[0] == a + e)
            }"#;
        let tc = trans_clos_from_src(src);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // 2d Vec add: the verify expression is m3r0[0] == a+e
        // pl should contain the verify LHS mapped to a+e
        assert!(
            !gr.pl.is_empty(),
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        // Basis should contain the add constraint + verify eq
        assert!(
            gr.generating_set.len() >= 2,
            "basis should have at least 2 rows, got {}",
            gr.generating_set.len()
        );

        // Namespace should register all 8 instance inputs
        let ns_named_count = gr.vars.values().filter(|p| !p.name.is_empty()).count();
        assert!(
            ns_named_count >= 8,
            "namespace should register >= 8 named instance vars, got {}",
            ns_named_count
        );
    }

    #[test]
    fn ideal_vec_add_3d() {
        let src = r#"
            proto va3d<F: Field>(
                instance a: F, instance b: F, instance c: F, instance d: F,
                instance e: F, instance f: F, instance g: F, instance h: F
            ) where a == a {
                let t1 = [[[a, b], [c, d]], [[e, f], [g, h]]];
                let t2 = [[[a, b], [c, d]], [[e, f], [g, h]]];
                let t3 = t1 + t2;
                let t3d0 = t3[0];
                let t3d0r0 = t3d0[0];
                verify(t3d0r0[0] == a + a)
            }"#;
        let tc = trans_clos_from_src(src);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // 3d Vec add: same structure, verify(t3d0r0[0] == a + a)
        assert!(
            !gr.pl.is_empty(),
            "pl should have at least 1 entry for the verify expression, got {}",
            gr.pl.len()
        );

        assert!(
            gr.generating_set.len() >= 2,
            "basis should have at least 2 rows, got {}",
            gr.generating_set.len()
        );

        let ns_named_count = gr.vars.values().filter(|p| !p.name.is_empty()).count();
        assert!(
            ns_named_count >= 8,
            "namespace should register >= 8 named instance vars, got {}",
            ns_named_count
        );
    }

    #[test]
    fn test_add_uni_different_degrees() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let uni4_ideal = ATyp::Uni(4);

        let var_a = Var::from_node(NodeIndex::new(0), uni2.clone(), Qualifier::Witness);
        ideal.register(&var_a);
        let coefs_a: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_a.clone(), Op::Vec(coefs_a), &mut ideal);

        let var_b = Var::from_node(NodeIndex::new(1), uni4.clone(), Qualifier::Witness);
        ideal.register(&var_b);
        let coefs_b: Vec<_> = (1..=5u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_b.clone(), Op::Vec(coefs_b), &mut ideal);

        let var_r = Var::from_node(NodeIndex::new(2), uni4_ideal.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), uni2)),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), uni4)),
                uni4_ideal,
            ),
            &mut ideal,
        );

        assert_eq!(var_r.typ.physical_len(), 5, "Uni(4) has 5 coefficients");
        for i in 0..5 {
            let slot = var_r.clone().with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Uni(2)+Uni(4) ideal slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_add_scalar_poly_broadcast() {
        let (var_s, var_p, var_r, ideal) = scalar_poly_binop_ideal(BinOp::Add, true, ATyp::Uni(2));
        assert_eq!(
            ideal.generating_set.len(),
            3,
            "Scalar + Uni(2) should produce one row per coefficient slot"
        );

        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        for i in 0..3 {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            let expected = if i == 0 { &s + &p } else { p };
            assert_ideal_slot(&ideal, &var_r, i, expected);
        }
    }

    #[test]
    fn test_uni_add_scalar_lifts_to_constant_slot_only() {
        let (var_s, var_p, var_r, ideal) = scalar_poly_binop_ideal(BinOp::Add, false, ATyp::Uni(2));
        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        for i in 0..3 {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            let expected = if i == 0 { &p + &s } else { p };
            assert_ideal_slot(&ideal, &var_r, i, expected);
        }
    }

    #[test]
    fn test_uni_sub_scalar_lifts_to_constant_slot_only() {
        let (var_s, var_p, var_r, ideal) = scalar_poly_binop_ideal(BinOp::Sub, false, ATyp::Uni(2));
        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        for i in 0..3 {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            let expected = if i == 0 { &p - &s } else { p };
            assert_ideal_slot(&ideal, &var_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_sub_uni_negates_nonconstant_slots() {
        let (var_s, var_p, var_r, ideal) = scalar_poly_binop_ideal(BinOp::Sub, true, ATyp::Uni(2));
        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        for i in 0..3 {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            let expected = if i == 0 { &s - &p } else { -p };
            assert_ideal_slot(&ideal, &var_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_add_vpoly_lifts_to_constant_slot_only() {
        let poly_typ = ATyp::VPoly(2, 2);
        let (var_s, var_p, var_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Add, true, poly_typ.clone());
        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        let zero_slot = multi_indices(2, 2)
            .iter()
            .position(|idx| idx.iter().all(|degree| *degree == 0))
            .unwrap();
        for i in 0..poly_typ.physical_len() {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            let expected = if i == zero_slot { &s + &p } else { p };
            assert_ideal_slot(&ideal, &var_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_sub_vpoly_negates_nonconstant_slots() {
        let poly_typ = ATyp::VPoly(2, 2);
        let (var_s, var_p, var_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Sub, true, poly_typ.clone());
        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        let zero_slot = multi_indices(2, 2)
            .iter()
            .position(|idx| idx.iter().all(|degree| *degree == 0))
            .unwrap();
        for i in 0..poly_typ.physical_len() {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            let expected = if i == zero_slot { &s - &p } else { -p };
            assert_ideal_slot(&ideal, &var_r, i, expected);
        }
    }

    #[test]
    fn test_scalar_add_mle_broadcasts_to_all_evaluation_slots() {
        let poly_typ = ATyp::Mle(2);
        let (var_s, var_p, var_r, ideal) =
            scalar_poly_binop_ideal(BinOp::Add, true, poly_typ.clone());
        let s = Polynomial::<ark_bls12_381::Fr>::var(&var_s);
        for i in 0..poly_typ.physical_len() {
            let p_slot_var = var_p.with_index(i).unwrap();
            let p = Polynomial::var(&p_slot_var);
            assert_ideal_slot(&ideal, &var_r, i, &s + &p);
        }
    }

    /// `Vec(VPoly(1,2),2) + VPoly(1,1)` — Vec<Poly> plus a bare Poly.
    /// Each element recurses into the leaf poly/poly addition arm.
    #[test]
    fn test_add_vec_vpoly_by_vpoly() {
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_a = ATyp::VPoly(1, 2);
        let vec_a = ATyp::Vec(Box::new(elem_a.clone()), 2);
        let b_t = ATyp::VPoly(1, 1);

        let var_a = Var::from_node(NodeIndex::new(0), vec_a.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), b_t.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        // lub_add(Vec(VPoly(1,2),2), VPoly(1,1)) = Vec(lub_add(VPoly(1,2), VPoly(1,1)), 2)
        //                                        = Vec(VPoly(1,2), 2)
        let result_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_a.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), b_t.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        // All result slots populated (2 elements × 3 slots per VPoly(1,2) = 6).
        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Vec(VPoly)+VPoly element {i} slot {j} missing from pl"
                );
            }
        }
    }

    /// `Vec(VPoly(1,2),2) - VPoly(1,1)` — Vec<Poly> minus a bare Poly.
    /// Each element recurses into the leaf poly/poly subtraction arm.
    #[test]
    fn test_sub_vec_vpoly_by_vpoly() {
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_a = ATyp::VPoly(1, 2);
        let vec_a = ATyp::Vec(Box::new(elem_a.clone()), 2);
        let b_t = ATyp::VPoly(1, 1);

        let var_a = Var::from_node(NodeIndex::new(0), vec_a.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), b_t.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        let result_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Sub,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_a.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), b_t.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Vec(VPoly)-VPoly element {i} slot {j} missing from pl"
                );
            }
        }
    }

    /// `VPoly(1,2) + Vec(VPoly(1,1),2)` — bare Poly plus Vec<Poly>.
    /// The scalar-left vector addition broadcasts the poly across elements.
    #[test]
    fn test_add_vpoly_by_vec_vpoly() {
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let a_t = ATyp::VPoly(1, 2);
        let elem_b = ATyp::VPoly(1, 1);
        let vec_b = ATyp::Vec(Box::new(elem_b.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), a_t.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_b.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        // lub_add(VPoly(1,2), Vec(VPoly(1,1),2)) = Vec(lub_add(VPoly(1,2), VPoly(1,1)), 2)
        //                                        = Vec(VPoly(1,2), 2)
        let result_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), a_t.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_b.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "VPoly+Vec(VPoly) element {i} slot {j} missing from pl"
                );
            }
        }
    }
}
