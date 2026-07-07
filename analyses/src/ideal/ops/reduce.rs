//! Reduce op encoders: `reduce_op`, `reduce_polysource`, `selected_eval_to_poly`.

use std::collections::HashMap;

use ark_ff::One;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::{GOp, HOp, Op, Ref};
use lang::ast::BinOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::super::PolySource;
use super::super::combinatorics::{hypercube, multi_indices};
use super::binop::mul_op;
use super::div;
use super::{EncodeCtx, constrain_to_polys, link_to_polys, link_to_witness};

/// Left-fold of vector elements:
///   acc₀ = v[0],  acc_i = rop(acc_{i-1}, v[i]),  ideal = acc_{n-1}
///
/// Physical slots from `ref_vars(v)` are chunked by `elem_len`
/// (the element type's `physical_len`) into logical elements.
/// The fold is performed per-slot-position across elements.
///
/// Operator handling:
///
/// - **Add/And/Sub/Mul**: pure polynomial fold — Add/And start from
///   zero, Mul from one, Sub starts from the first element.
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

    match rop {
        BinOp::Add => {
            let mut acc: PolySource<C> = PolySource::new(
                (0..elem_t.physical_len())
                    .map(|_| Polynomial::zero())
                    .collect(),
                elem_t.clone(),
            );
            for i in 0..n {
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
                let acc_name = ctx.ns.next_name("reduce_and_acc");
                let acc_var = ctx.sentinel_var(&acc_name, elem_t.clone());
                mul_op(&acc_var, &acc, &elem, &elem_t, ctx.ideal);
                acc = PolySource::new(
                    acc_var
                        .slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
                        .collect(),
                    elem_t.clone(),
                );
            }
            constrain_to_polys(ctx.ideal, &var, acc.polys);
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
                    let acc_name = ctx.ns.next_name("reduce_mul_acc");
                    ctx.sentinel_var(&acc_name, step_typ.clone())
                };
                mul_op(&acc_var, &acc, &elem, &step_typ, ctx.ideal);
                acc = PolySource::from_vars(&acc_var, step_typ.clone());
                acc_typ = step_typ;
            }
        }
        BinOp::Concat => {
            link_to_polys(ctx.ideal, &var, v_src.polys);
        }
        BinOp::Div | BinOp::Rem => {
            let is_rem = rop == BinOp::Rem;
            let is_poly = PolySource::<C>::poly_shape_static(&elem_t).is_some();
            let mut acc_src = v_src.at_index(0).unwrap();
            let mut acc_typ = elem_t.clone();
            for step in 0..n - 1 {
                let is_last = step == n - 2;
                let elem_src = v_src.at_index(step + 1).unwrap();
                if !is_poly && is_rem {
                    panic!(
                        "Rem: non-polynomial remainder is undefined for Vec<{}>",
                        elem_t,
                    );
                }
                let step_typ = ATyp::lub_op(rop, &acc_typ, elem_src.typ(), &Nothing)
                    .expect("reduce(/,%): type checker guarantees lub");
                let target = if is_last {
                    var.clone()
                } else {
                    let acc_name = ctx.ns.next_name(if is_rem {
                        "reduce_rem_acc"
                    } else {
                        "reduce_div_acc"
                    });
                    ctx.sentinel_var(&acc_name, step_typ.clone())
                };
                if is_poly {
                    div::div_rem_op(ctx, &target, &acc_src, &elem_src, is_rem, false);
                } else {
                    div::slot_wise_div(ctx.ideal, &target, acc_src.polys(), elem_src.polys());
                }
                acc_src = PolySource::from_vars(&target, step_typ.clone());
                acc_typ = step_typ;
            }
        }
        BinOp::Equ | BinOp::Pow => {
            uncovered_op("reduce-equ-or-pow", &var);
        }
        BinOp::Dot => {
            panic!("reduce(dot, _) is rejected by the type checker");
        }
    }
}

/// Shared fold for `Op::Reduce` and `Op::ReduceMap`: combine the `n`
/// elements of `v_src` (each of type `elem_t`) under `rop`, binding `var`.
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
            let mut acc: PolySource<C> = PolySource::new(
                (0..elem_t.physical_len())
                    .map(|_| Polynomial::zero())
                    .collect(),
                elem_t.clone(),
            );
            for i in 0..n {
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
                let acc_name = ctx.ns.next_name("reduce_and_acc");
                let acc_var = ctx.sentinel_var(&acc_name, elem_t.clone());
                mul_op(&acc_var, &acc, &elem, &elem_t, ctx.ideal);
                acc = PolySource::new(
                    acc_var
                        .slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
                        .collect(),
                    elem_t.clone(),
                );
            }
            constrain_to_polys(ctx.ideal, &var, acc.polys);
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
                    let acc_name = ctx.ns.next_name("reduce_mul_acc");
                    ctx.sentinel_var(&acc_name, step_typ.clone())
                };
                mul_op(&acc_var, &acc, &elem, &step_typ, ctx.ideal);
                acc = PolySource::from_vars(&acc_var, step_typ.clone());
                acc_typ = step_typ;
            }
        }
        BinOp::Concat => {
            link_to_polys(ctx.ideal, &var, v_src.polys);
        }
        BinOp::Div | BinOp::Rem => {
            let is_rem = rop == BinOp::Rem;
            let is_poly = PolySource::<C>::poly_shape_static(&elem_t).is_some();
            let mut acc_src = v_src.at_index(0).unwrap();
            for step in 0..n - 1 {
                let is_last = step == n - 2;
                let target = if is_last {
                    var.clone()
                } else {
                    let acc_name = ctx.ns.next_name(if is_rem {
                        "reduce_rem_acc"
                    } else {
                        "reduce_div_acc"
                    });
                    ctx.sentinel_var(&acc_name, elem_t.clone())
                };
                let elem_src = v_src.at_index(step + 1).unwrap();
                if is_poly {
                    div::div_rem_op(ctx, &target, &acc_src, &elem_src, is_rem && is_last, false);
                } else {
                    if is_rem {
                        panic!(
                            "Rem: non-polynomial remainder is undefined for Vec<{}>",
                            elem_t,
                        );
                    }
                    div::slot_wise_div(ctx.ideal, &target, acc_src.polys(), elem_src.polys());
                }
                acc_src = PolySource::new(
                    target
                        .slots()
                        .into_iter()
                        .map(|s| Polynomial::var(&s))
                        .collect(),
                    elem_t.clone(),
                );
            }
        }
        BinOp::Equ | BinOp::Pow => {
            uncovered_op("reduce-equ-or-pow", &var);
        }
        BinOp::Dot => {
            panic!("reduce(dot, _) is rejected by the type checker");
        }
    }
}

/// Selected evaluation: keep variable `range.start` free and substitute
/// `fixed` for the remaining variables. Returns the residual univariate
/// coefficient polys, or `None` for unsupported shapes.
pub fn selected_eval_to_poly<C: ArkConfig>(
    p: &GOp<C>,
    range: &lang::typ::CRange,
    fixed: &GOp<C>,
    vars: &HashMap<Ref, Var>,
) -> Option<Vec<Polynomial<C::F>>> {
    if range.step != 1 || range.len() != 1 {
        return None;
    }

    let fixed_polys = PolySource::ref_vars(fixed, vars);
    match p.typ() {
        ATyp::VPoly(n, d) if range.end <= n && fixed_polys.len() == n.saturating_sub(1) => {
            let p_polys = PolySource::ref_vars(p, vars);
            let all_indices = multi_indices(n, d);
            let mut out = vec![Polynomial::<C::F>::zero(); d + 1];

            for (idx, ki) in all_indices.iter().enumerate() {
                let free_exp = ki[range.start];
                let mut term = p_polys[idx].clone();
                let mut fixed_idx = 0usize;
                for (var_idx, &var_exp) in ki.iter().enumerate().take(n) {
                    if var_idx == range.start {
                        continue;
                    }
                    if var_exp > 0 {
                        let mut fixed_pow = fixed_polys[fixed_idx].clone();
                        fixed_pow.pow(var_exp);
                        term = &term * &fixed_pow;
                    }
                    fixed_idx += 1;
                }
                out[free_exp] = &out[free_exp] + &term;
            }
            Some(out)
        }
        ATyp::Mle(n) if range.end <= n && fixed_polys.len() == n.saturating_sub(1) => {
            let p_polys = PolySource::ref_vars(p, vars);
            let all_b = hypercube(n);
            let one = Polynomial::<C::F>::lit(&C::F::one());
            let eq = |bi: usize, x: &Polynomial<C::F>| -> Polynomial<C::F> {
                if bi == 1 { x.clone() } else { &one - x }
            };
            let free = range.start;
            let mut out = vec![Polynomial::<C::F>::zero(); 2];
            for (idx, b) in all_b.iter().enumerate() {
                let mut w = one.clone();
                let mut fixed_idx = 0usize;
                for (var_idx, &bv) in b.iter().enumerate().take(n) {
                    if var_idx == free {
                        continue;
                    }
                    w = &w * &eq(bv, &fixed_polys[fixed_idx]);
                    fixed_idx += 1;
                }
                let term = &p_polys[idx] * &w;
                if b[free] == 0 {
                    out[0] = &out[0] + &term;
                    out[1] = &out[1] - &term;
                } else {
                    out[1] = &out[1] + &term;
                }
            }
            Some(out)
        }
        _ => None,
    }
}

fn uncovered_op(context: &str, target: &Var) -> ! {
    panic!(
        "ideal: operation has no polynomial-ideal treatment at {} for {}",
        context,
        target.verbose()
    );
}

#[cfg(test)]
mod tests {

    use crate::{Ideal, IdealBuilder};

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
    #[should_panic(expected = "Rem: non-polynomial remainder")]
    fn test_reduce_rem_scalar_panics() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Rem,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var, op, &mut ideal);
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
