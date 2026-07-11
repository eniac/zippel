//! Reduce op encoders: `reduce_op`, `reduce_polysource`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::{HOp, Op};
use lang::ast::BinOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::PolySource;
use super::div;
use super::mul::mul_op_inner;
use super::{EncodeCtx, link_to_polys, link_to_witness};

/// Left-fold of vector elements:
///   acc₀ = v[0],  acc_i = rop(acc_{i-1}, v[i]),  ideal = acc_{n-1}
///
/// Extracts the element type and length from `v`, fast-paths the
/// single-element case, then delegates to `reduce_polysource` for the
/// actual fold.
pub fn reduce_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: Var,
    rop: BinOp,
    v: &HOp<C>,
) {
    let v_typ = v.typ();
    let (elem_t, n) = match &v_typ {
        ATyp::Vec(box e, n) => (e.clone(), *n),
        _ => panic!("Reduce operand must be Vec; type checker guarantees this"),
    };

    if n == 1 {
        let Op::Ref(r, _) = v.get() else {
            panic!(
                "Reduce operand must be Ref; got {:?}",
                std::mem::discriminant(v.get())
            )
        };
        let v_var = ctx.ideal.find_ref(r);
        let elem_var = v_var.with_index(0).unwrap();
        link_to_witness(ctx.ideal, &var, &elem_var);
        return;
    }

    let v_src = PolySource::from_ref_vars(&ctx.ideal.vars, v);
    reduce_polysource(ctx, var, rop, v_src, elem_t, n);
}

/// Fold the `n` elements of `v_src` (each of type `elem_t`) under `rop`,
/// binding `var`. Shared by `Op::Reduce` (via `reduce_op`) and
/// `Op::ReduceMap` (via `map::reduce_map_op`).
///
/// Operator handling:
///
/// - **Add/And/Sub/Mul**: pure polynomial fold — Add/Sub start from the
///   first element, And/Mul chain via `mul_op_inner` with the last step
///   targeting `var` directly.
///
/// - **Concat**: passes through all physical slots.
///
/// - **Div/Rem**: lower as true left folds. Polynomial folds use
///   division/remainder witness identities for each step, while scalar
///   division uses per-slot constraints `acc - elem * var(target) = 0`.
///
/// - **Equ/Pow**: opaque. Chained equality can't be cleanly encoded in
///   the polynomial basis; Pow's left-fold `(a^b)^c` requires `a^(b*c)`
///   which is only valid for constant b, c and produces potentially
///   very-high-degree terms — better handled by the `BinOp::Pow` handler
///   in `add_op` which sees a single exponent directly.
///
/// - **Dot**: not supported (type checker rejects `reduce(dot, _)`).
pub fn reduce_polysource<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: Var,
    rop: BinOp,
    v_src: PolySource<C>,
    elem_t: ATyp,
    n: usize,
) {
    match rop {
        BinOp::Add => {
            let mut acc = v_src.at_index(0).unwrap();
            for i in 1..n {
                let elem = v_src.at_index(i).unwrap();
                let lifted = elem.lift_to(&elem_t);
                for (j, p) in acc.polys.iter_mut().enumerate() {
                    *p = &*p + &lifted.polys[j];
                }
            }
            link_to_polys(ctx.ideal, &var, acc.polys);
        }
        BinOp::And => {
            let mut acc = v_src.at_index(0).unwrap();
            for i in 1..n {
                let elem = v_src.at_index(i).unwrap();
                let is_last = i == n - 1;
                let acc_var = if is_last {
                    var.clone()
                } else {
                    let acc_name = ctx.builder.ns.next_name("reduce_and_acc");
                    ctx.sentinel_var(&acc_name, elem_t.clone())
                };
                mul_op_inner(ctx, &acc_var, &acc, &elem, &elem_t);
                acc = PolySource::new(
                    acc_var
                        .slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
                        .collect(),
                    elem_t.clone(),
                );
            }
        }
        BinOp::Sub => {
            let mut acc = v_src.at_index(0).unwrap();
            for i in 1..n {
                let elem = v_src.at_index(i).unwrap();
                let lifted = elem.lift_to(&elem_t);
                for (j, p) in acc.polys.iter_mut().enumerate() {
                    *p = &*p - &lifted.polys[j];
                }
            }
            link_to_polys(ctx.ideal, &var, acc.polys);
        }
        BinOp::Mul => {
            let mut acc = v_src.at_index(0).unwrap();
            let mut acc_typ = elem_t.clone();
            for i in 1..n {
                let elem = v_src.at_index(i).unwrap();
                let step_typ = ATyp::lub_mul(&acc_typ, elem.typ(), &Nothing)
                    .expect("reduce(*): type checker guarantees lub_mul");
                let is_last = i == n - 1;
                let acc_var = if is_last {
                    var.clone()
                } else {
                    let acc_name = ctx.builder.ns.next_name("reduce_mul_acc");
                    ctx.sentinel_var(&acc_name, step_typ.clone())
                };
                mul_op_inner(ctx, &acc_var, &acc, &elem, &step_typ);
                acc = PolySource::from_vars(&acc_var, step_typ.clone());
                acc_typ = step_typ;
            }
        }
        BinOp::Concat => {
            link_to_polys(ctx.ideal, &var, v_src.polys);
        }
        BinOp::Div | BinOp::Rem => {
            let is_rem = rop == BinOp::Rem;
            let mut acc_src = v_src.at_index(0).unwrap();
            let mut acc_typ = elem_t.clone();
            for step in 0..n - 1 {
                let is_last = step == n - 2;
                let elem_src = v_src.at_index(step + 1).unwrap();
                let step_typ = ATyp::lub_op(rop, &acc_typ, elem_src.typ(), &Nothing)
                    .expect("reduce(/,%): type checker guarantees lub");
                let target = if is_last {
                    var.clone()
                } else {
                    let acc_name = ctx.builder.ns.next_name(if is_rem {
                        "reduce_rem_acc"
                    } else {
                        "reduce_div_acc"
                    });
                    ctx.sentinel_var(&acc_name, step_typ.clone())
                };
                div::div_rem_op_inner(ctx, &target, &acc_src, &elem_src, is_rem, false);
                acc_src = PolySource::from_vars(&target, step_typ.clone());
                acc_typ = step_typ;
            }
        }
        BinOp::Equ | BinOp::Pow => {
            super::uncovered_op("reduce-equ-or-pow", &var);
        }
        BinOp::Dot => {
            panic!("reduce(dot, _) is rejected by the type checker");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Ideal, IdealBuilder};

    use crate::frontend::Polynomial;
    use backend::ArkBls12_381;

    use backend::ATyp;
    use backend::op::mk;
    use graph::{GOp, Op, Ref};

    #[test]
    fn test_reduce_add_over_scalar_vec() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        // v : Vec(F, 3)  →  reduce(+, v) : F
        let var_v = Var::from_node(
            NodeIndex::new(0),
            ATyp::Vec(Box::new(ATyp::scalar()), 3),
            Qualifier::Private,
        );
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(
                Ref::new(NodeIndex::new(0)),
                ATyp::Vec(Box::new(ATyp::scalar()), 3),
            )),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let v0 = var_v.clone().with_index(0).unwrap();
        let v1 = var_v.clone().with_index(1).unwrap();
        let v2 = var_v.clone().with_index(2).unwrap();

        let expected = &var_poly(&v0) + &(&var_poly(&v1) + &var_poly(&v2));
        let row = &expected - &var_poly(&var);
        assert!(
            ideal.generating_set.iter().any(|r| r == &row),
            "basis should contain v0+v1+v2 - ideal, got {:?}",
            ideal.generating_set
        );
        assert_eq!(
            ideal.pl.get(&var).cloned(),
            Some(expected),
            "pl[ideal] should map to v0+v1+v2"
        );
    }

    #[test]
    fn test_reduce_add_over_poly_vec() {
        // reduce(+, [Poly(1,2); 3]) : Poly(1,2)
        // Vec(Poly(1,2), 3) has 3 elements × 3 coefficients = 9 physical slots.
        // reduce should produce 3 polynomials (one per coefficient position),
        // where ideal[j] = v0[j] + v1[j] + v2[j].
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let poly_t = ATyp::Uni(2);
        let vec_t = ATyp::Vec(Box::new(poly_t.clone()), 3);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), poly_t.clone(), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        // Vec(Poly(1,2), 3): element 0 is slots 0,1,2; element 1 is slots 3,4,5; element 2 is slots 6,7,8.
        let v0_c0 = var_v.clone().with_index(0).unwrap().with_index(0).unwrap();
        let v0_c1 = var_v.clone().with_index(0).unwrap().with_index(1).unwrap();
        let v0_c2 = var_v.clone().with_index(0).unwrap().with_index(2).unwrap();
        let v1_c0 = var_v.clone().with_index(1).unwrap().with_index(0).unwrap();
        let v1_c1 = var_v.clone().with_index(1).unwrap().with_index(1).unwrap();
        let v1_c2 = var_v.clone().with_index(1).unwrap().with_index(2).unwrap();
        let v2_c0 = var_v.clone().with_index(2).unwrap().with_index(0).unwrap();
        let v2_c1 = var_v.clone().with_index(2).unwrap().with_index(1).unwrap();
        let v2_c2 = var_v.clone().with_index(2).unwrap().with_index(2).unwrap();

        let r_c0 = var.clone().with_index(0).unwrap();
        let r_c1 = var.clone().with_index(1).unwrap();
        let r_c2 = var.clone().with_index(2).unwrap();

        // ideal[0] = v0[0] + v1[0] + v2[0]
        let expected_c0 = &var_poly(&v0_c0) + &(&var_poly(&v1_c0) + &var_poly(&v2_c0));
        let expected_c1 = &var_poly(&v0_c1) + &(&var_poly(&v1_c1) + &var_poly(&v2_c1));
        let expected_c2 = &var_poly(&v0_c2) + &(&var_poly(&v1_c2) + &var_poly(&v2_c2));

        assert_eq!(
            ideal.pl.get(&r_c0).cloned(),
            Some(expected_c0.clone()),
            "pl[ideal[0]] = v0[0]+v1[0]+v2[0]"
        );
        assert_eq!(
            ideal.pl.get(&r_c1).cloned(),
            Some(expected_c1.clone()),
            "pl[ideal[1]] = v0[1]+v1[1]+v2[1]"
        );
        assert_eq!(
            ideal.pl.get(&r_c2).cloned(),
            Some(expected_c2.clone()),
            "pl[ideal[2]] = v0[2]+v1[2]+v2[2]"
        );

        let row0 = &expected_c0 - &var_poly(&r_c0);
        let row1 = &expected_c1 - &var_poly(&r_c1);
        let row2 = &expected_c2 - &var_poly(&r_c2);
        assert!(
            ideal.generating_set.iter().any(|r| r == &row0),
            "basis should contain row for coefficient 0"
        );
        assert!(
            ideal.generating_set.iter().any(|r| r == &row1),
            "basis should contain row for coefficient 1"
        );
        assert!(
            ideal.generating_set.iter().any(|r| r == &row2),
            "basis should contain row for coefficient 2"
        );
    }

    #[test]
    fn test_reduce_div_scalar_uses_slot_wise_div() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let v0 = var_v.clone().with_index(0).unwrap().with_index(0).unwrap();
        let v1 = var_v.clone().with_index(1).unwrap().with_index(0).unwrap();
        let v2 = var_v.clone().with_index(2).unwrap().with_index(0).unwrap();
        let r_slot = var.with_index(0).unwrap();

        let step1_vars: Vec<_> = ideal
            .generating_set
            .iter()
            .filter(|row| row.contains(&r_slot) && row.contains(&v2))
            .collect();
        assert!(
            !step1_vars.is_empty(),
            "basis should contain final div constraint involving v[2] and ideal"
        );

        let step0_vars: Vec<_> = ideal
            .generating_set
            .iter()
            .filter(|row| row.contains(&v0) && row.contains(&v1))
            .collect();
        assert!(
            !step0_vars.is_empty(),
            "basis should contain first div constraint involving v[0] and v[1]"
        );
    }

    #[test]
    fn reduce_mul_poly_accumulator_widens() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_t = ATyp::Uni(1);
        let vec_t = ATyp::Vec(Box::new(elem_t.clone()), 3);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(3), Qualifier::Private);
        ideal.register(&var);

        builder.add_op(
            var.clone(),
            Op::Reduce(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let high_slot = var.with_index(3).unwrap();
        assert!(
            ideal
                .generating_set
                .iter()
                .any(|row| row.contains(&high_slot)),
            "reduce(*) should lower the widened Uni(3) accumulator all the way to the final high-degree slot"
        );
    }

    /// Regression: `reduce(*, [..])` lowered to `Op::ReduceMap` must widen the
    /// accumulator type as the product degree grows, exactly like `Op::Reduce`.
    /// Pre-fix, `reduce_polysource`'s Mul arm typed every accumulator at the
    /// element type `Uni(1)`, so the first product (degree 2) overflowed the
    /// `r_idx` table in `mul_op` and panicked with "multi-index missing in
    /// ideal". This is the `Op::ReduceMap` twin of
    /// `reduce_mul_poly_accumulator_widens`.

    #[test]
    fn reduce_map_mul_poly_accumulator_widens() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_t = ATyp::Uni(1);
        let vec_t = ATyp::Vec(Box::new(elem_t.clone()), 3);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(3), Qualifier::Private);
        ideal.register(&var);

        // reduce(*, [x for x in polys]) — ReduceMap(Mul) with identity body over a
        // length-3 vector of degree-1 univariates → degree-3 product (Uni(3)).
        let domain = mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t));
        let body = mk::<ArkBls12_381>(Op::LoopParam(0, elem_t.clone()));
        builder.add_op(
            var.clone(),
            Op::ReduceMap(BinOp::Mul, domain, body),
            &mut ideal,
        );

        let high_slot = var.with_index(3).unwrap();
        assert!(
            ideal
                .generating_set
                .iter()
                .any(|row| row.contains(&high_slot)),
            "reduce(*) via ReduceMap must widen the Uni(1) accumulator to the Uni(3) product"
        );
    }

    #[test]
    fn reduce_rem_poly_left_fold_semantics() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_t = ATyp::Uni(3);
        let vec_t = ATyp::Vec(Box::new(elem_t.clone()), 3);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var);

        builder.add_op(
            var.clone(),
            Op::Reduce(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        assert_eq!(
            var.typ.physical_len(),
            3,
            "Uni(3) % Uni(3) % Uni(3) is lowered as the left-fold remainder type Uni(2)"
        );
        assert!(
            !ideal.generating_set.is_empty(),
            "reduce(%) should emit constraints for every polynomial fold step"
        );
    }

    // -----------------------------------------------------------------
    // reduce_op with PolySource: direct fold for Add/Sub
    // -----------------------------------------------------------------

    #[test]
    fn test_reduce_add_poly_vec_direct_fold() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let poly_t = ATyp::Uni(2);
        let vec_t = ATyp::Vec(Box::new(poly_t.clone()), 2);

        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), poly_t.clone(), Qualifier::Private);

        builder.add_op(
            var.clone(),
            Op::Reduce(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        for j in 0..3 {
            let v0_j = var_v.clone().with_index(0).unwrap().with_index(j).unwrap();
            let v1_j = var_v.clone().with_index(1).unwrap().with_index(j).unwrap();
            let r_j = var.clone().with_index(j).unwrap();
            let expected = &var_poly(&v0_j) + &var_poly(&v1_j);
            let stored = ideal.pl.get(&r_j).unwrap();
            assert_eq!(*stored, expected, "reduce add poly slot {} mismatch", j);
        }
    }
}
