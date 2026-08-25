//! Reduce op encoders: `reduce_op`, `reduce_op_inner`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::{HOp, Op};
use lang::ast::BinOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::super::poly_source::has_poly_type;
use super::PolySource;
use super::addsub::add_sub_op_inner;
use super::div;
use super::mul::mul_op_inner;
use super::{EncodeCtx, link_to_polys, link_to_witness};

/// Left-fold of vector elements:
///   acc₀ = v[0],  acc_i = rop(acc_{i-1}, v[i]),  ideal = acc_{n-1}
///
/// Extracts the element type and length from `v`, fast-paths the
/// single-element case, then delegates to `reduce_op_inner` for the
/// actual fold.
pub fn reduce_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
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
        link_to_witness(ctx.ideal, var, &elem_var);
        return;
    }

    let v_src = PolySource::from_ref_vars(&ctx.ideal.vars, v);
    reduce_op_inner(ctx, var.clone(), rop, v_src, elem_t, n);
}

/// Fold the `n` elements of `v_src` (each of type `elem_t`) under `rop`,
/// binding `var`. Shared by `Op::Reduce` (via `reduce_op`) and
/// `Op::ReduceMap` (via `map::reduce_map_op`).
///
/// All arithmetic ops (Add/Sub/Mul/And/Div/Rem) use the same left-fold
/// pattern via [`fold_with_handler`]: start from `v[0]`, then for each
/// subsequent element call the corresponding binary op handler
/// (`add_sub_op_inner`, `mul_op_inner`, `div::div_rem_op_inner`) with
/// intermediate sentinel accumulators. This delegates nesting/convolution/
/// lifting to the existing handlers, which already handle `Vec<T>`
/// (including nested `Vec<Vec<…>>`), `VPoly`, `Uni`, `Mle`, and base
/// types correctly.
///
/// - **Concat**: passes through all physical slots.
/// - **Pow**: opaque (see below).
/// - **Dot/Equ**: rejected by the type checker.
pub fn reduce_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: Var,
    rop: BinOp,
    v_src: PolySource<C>,
    elem_t: ATyp,
    n: usize,
) {
    match rop {
        BinOp::Add | BinOp::Sub => {
            fold_with_handler(
                ctx,
                &var,
                v_src,
                elem_t,
                n,
                "reduce_addsub_acc",
                |ctx, target, acc, elem, step_typ| {
                    add_sub_op_inner(ctx, target, acc, elem, step_typ, rop);
                },
                |acc_typ, elem_typ| {
                    ATyp::lub_op(rop, acc_typ, elem_typ, &Nothing)
                        .expect("reduce(+,-): type checker guarantees lub")
                },
                Some(|a: &Polynomial<C::F>, b: &Polynomial<C::F>| match rop {
                    BinOp::Add => a + b,
                    BinOp::Sub => a - b,
                    _ => unreachable!(),
                }),
            );
        }
        BinOp::Mul | BinOp::And => {
            let lub_fn = |a: &ATyp, b: &ATyp| -> ATyp {
                match rop {
                    BinOp::Mul => ATyp::lub_mul(a, b, &Nothing).expect("reduce(*): lub_mul"),
                    BinOp::And => ATyp::lub_and(a, b, &Nothing).expect("reduce(&&): lub_and"),
                    _ => unreachable!(),
                }
            };
            fold_with_handler(
                ctx,
                &var,
                v_src,
                elem_t,
                n,
                "reduce_mul_acc",
                |ctx, target, acc, elem, step_typ| {
                    mul_op_inner(ctx, target, acc, elem, step_typ);
                },
                lub_fn,
                Some(|a: &Polynomial<C::F>, b: &Polynomial<C::F>| a * b),
            );
        }
        BinOp::Concat => {
            link_to_polys(ctx.ideal, &var, v_src.polys);
        }
        BinOp::Div | BinOp::Rem => {
            let is_rem = rop == BinOp::Rem;
            fold_with_handler(
                ctx,
                &var,
                v_src,
                elem_t,
                n,
                if is_rem {
                    "reduce_rem_acc"
                } else {
                    "reduce_div_acc"
                },
                |ctx, target, acc, elem, _step_typ| {
                    div::div_rem_op_inner(ctx, target, acc, elem, is_rem);
                },
                |acc_typ, elem_typ| {
                    ATyp::lub_op(rop, acc_typ, elem_typ, &Nothing)
                        .expect("reduce(/,%): type checker guarantees lub")
                },
                None::<fn(&Polynomial<C::F>, &Polynomial<C::F>) -> Polynomial<C::F>>,
            );
        }
        BinOp::Pow => {
            super::uncovered_op("reduce-pow", &var);
        }
        BinOp::Dot => {
            panic!("reduce(dot, _) is rejected by the type checker");
        }
        BinOp::Equ => {
            panic!("reduce(==, _) is rejected by the type checker");
        }
    }
}

/// Generic left-fold: `acc₀ = v[0]`, `acc_i = handler(acc_{i-1}, v[i])`,
/// `var = acc_{n-1}`. Intermediate accumulators use sentinel vars.
/// `lub_fn` computes the result type of each fold step.
///
/// When `slotwise` is `Some` and `elem_t` contains no polynomial types
/// (scalar / vec-of-scalar / …), the fold accumulates directly in
/// polynomial space — each slot is combined with the slotwise closure —
/// avoiding sentinel vars entirely. This mirrors the fast path in
/// `pow_const`.
#[allow(clippy::too_many_arguments)]
fn fold_with_handler<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    v_src: PolySource<C>,
    elem_t: ATyp,
    n: usize,
    acc_name_prefix: &str,
    handler: impl Fn(&mut EncodeCtx<'_, C>, &Var, &PolySource<C>, &PolySource<C>, &ATyp),
    lub_fn: impl Fn(&ATyp, &ATyp) -> ATyp,
    slotwise: Option<impl Fn(&Polynomial<C::F>, &Polynomial<C::F>) -> Polynomial<C::F>>,
) {
    // Fast path: no polynomial types at any nesting level, so the binary
    // op is purely slot-wise with no cross-terms. Accumulate directly.
    if let Some(slotwise) = &slotwise
        && !has_poly_type(&elem_t)
    {
        let mut acc = v_src.at_index(0).unwrap();
        for i in 1..n {
            let elem = v_src.at_index(i).unwrap();
            for (j, p) in acc.polys.iter_mut().enumerate() {
                *p = slotwise(p, &elem.polys[j]);
            }
        }
        link_to_polys(ctx.ideal, var, acc.polys);
        return;
    }

    // Sentinel-var path: each step may change degree/shape, so go through
    // the handler with intermediate sentinel accumulators.
    let mut acc_src = v_src.at_index(0).unwrap();
    let mut acc_typ = elem_t.clone();
    for i in 1..n {
        let elem_src = v_src.at_index(i).unwrap();
        let step_typ = lub_fn(&acc_typ, elem_src.typ());
        let is_last = i == n - 1;
        let target = if is_last {
            var.clone()
        } else {
            let acc_name = ctx.builder.ns.next_name(acc_name_prefix);
            ctx.sentinel_var(&acc_name, step_typ.clone())
        };
        handler(ctx, &target, &acc_src, &elem_src, &step_typ);
        acc_src = PolySource::from_vars(&target, step_typ.clone());
        acc_typ = step_typ;
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
            Qualifier::Witness,
        );
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(
                Ref::new(NodeIndex::new(0)),
                ATyp::Vec(Box::new(ATyp::scalar()), 3),
            )),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let v0 = var_v.clone().with_index(0).unwrap();
        let v1 = var_v.clone().with_index(1).unwrap();
        let v2 = var_v.clone().with_index(2).unwrap();

        // Fast path: scalar types have no polynomial types, so the fold
        // accumulates directly in polynomial space. pl[var] = v0+v1+v2.
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let expected = &var_poly(&v0) + &(&var_poly(&v1) + &var_poly(&v2));
        assert_eq!(
            ideal.pl.get(&var).cloned(),
            Some(expected),
            "pl[ideal] should map to v0+v1+v2 (fast path)"
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
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), poly_t.clone(), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Add,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // With sentinel-var fold: step 1 binds sentinel[j] = v0[j]+v1[j],
        // step 2 binds var[j] = sentinel[j]+v2[j]. Check the generating set
        // contains constraints linking each coefficient slot.
        for j in 0..3 {
            let v0j = var_v.clone().with_index(0).unwrap().with_index(j).unwrap();
            let v1j = var_v.clone().with_index(1).unwrap().with_index(j).unwrap();
            let v2j = var_v.clone().with_index(2).unwrap().with_index(j).unwrap();
            let rj = var.clone().with_index(j).unwrap();

            let final_row: Vec<_> = ideal
                .generating_set
                .iter()
                .filter(|row| row.contains(&rj) && row.contains(&v2j))
                .collect();
            assert!(
                !final_row.is_empty(),
                "basis should contain final fold step for coefficient {j} (involves v[2][{j}] and ideal[{j}])"
            );

            let first_row: Vec<_> = ideal
                .generating_set
                .iter()
                .filter(|row| row.contains(&v0j) && row.contains(&v1j))
                .collect();
            assert!(
                !first_row.is_empty(),
                "basis should contain first fold step for coefficient {j} (involves v[0][{j}] and v[1][{j}])"
            );
        }
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
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let v0 = var_v.clone().with_index(0).unwrap();
        let v1 = var_v.clone().with_index(1).unwrap();
        let v2 = var_v.clone().with_index(2).unwrap();
        let r_slot = var.clone();

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
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(3), Qualifier::Witness);
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
    /// Pre-fix, `reduce_op_inner`'s Mul arm typed every accumulator at the
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
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(3), Qualifier::Witness);
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
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(2), Qualifier::Witness);
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

        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), poly_t.clone(), Qualifier::Witness);

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

    // -----------------------------------------------------------------
    // Nested Vec: reduce(+, Vec<Vec<F, M>, N>) — uses add_sub_op_inner
    // -----------------------------------------------------------------

    #[test]
    fn test_reduce_add_nested_scalar_vec() {
        // reduce(+, Vec<Vec<F, 2>, 3>) : Vec<F, 2>
        // Fast path: no poly types, so slot-wise accumulation directly.
        // pl[var[j]] = v[0][j] + v[1][j] + v[2][j].
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let inner_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let vec_t = ATyp::Vec(Box::new(inner_t.clone()), 3);

        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), inner_t.clone(), Qualifier::Witness);

        builder.add_op(
            var.clone(),
            Op::Reduce(
                BinOp::Add,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        for j in 0..2 {
            let v0_j = var_v.clone().with_index(0).unwrap().with_index(j).unwrap();
            let v1_j = var_v.clone().with_index(1).unwrap().with_index(j).unwrap();
            let v2_j = var_v.clone().with_index(2).unwrap().with_index(j).unwrap();
            let r_j = var.clone().with_index(j).unwrap();
            let expected = &var_poly(&v0_j) + &(&var_poly(&v1_j) + &var_poly(&v2_j));
            assert_eq!(
                ideal.pl.get(&r_j).cloned(),
                Some(expected),
                "pl[ideal[{j}]] = v0[{j}]+v1[{j}]+v2[{j}] (fast path)"
            );
        }
    }

    // -----------------------------------------------------------------
    // Nested Vec: reduce(*, Vec<Vec<F, M>, N>) — fast path (slot-wise)
    // -----------------------------------------------------------------

    #[test]
    fn test_reduce_mul_nested_scalar_vec() {
        // reduce(*, Vec<Vec<F, 2>, 3>) : Vec<F, 2>
        // Fast path: no poly types, so slot-wise accumulation directly.
        // pl[var[j]] = v[0][j] * v[1][j] * v[2][j].
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let inner_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let vec_t = ATyp::Vec(Box::new(inner_t.clone()), 3);

        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), inner_t.clone(), Qualifier::Witness);

        builder.add_op(
            var.clone(),
            Op::Reduce(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        for j in 0..2 {
            let v0_j = var_v.clone().with_index(0).unwrap().with_index(j).unwrap();
            let v1_j = var_v.clone().with_index(1).unwrap().with_index(j).unwrap();
            let v2_j = var_v.clone().with_index(2).unwrap().with_index(j).unwrap();
            let r_j = var.clone().with_index(j).unwrap();
            let expected = &(&var_poly(&v0_j) * &var_poly(&v1_j)) * &var_poly(&v2_j);
            assert_eq!(
                ideal.pl.get(&r_j).cloned(),
                Some(expected),
                "pl[ideal[{j}]] = v0[{j}]*v1[{j}]*v2[{j}] (fast path)"
            );
        }
    }

    // -----------------------------------------------------------------
    // Nested Vec with Poly: reduce(*, Vec<Vec<Poly(1,1), K>, N>)
    // — must use mul_op_inner (convolution), not slot-wise fast path
    // -----------------------------------------------------------------

    #[test]
    fn test_reduce_mul_nested_poly_vec() {
        // reduce(*, Vec<Vec<Poly(1,1), 2>, 2>) : Vec<Poly(1,2), 2>
        // Each element is a Poly(1,1) = [c0, c1].
        // Poly(1,1) × Poly(1,1) = Poly(1,2): [a0*b0, a0*b1+a1*b0, a1*b1].
        // Result should have 2 elements, each a Poly(1,2) with 3 coefficients.
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let poly1_t = ATyp::Uni(1); // Poly(1,1): 2 coefficients
        let inner_t = ATyp::Vec(Box::new(poly1_t.clone()), 2);
        let vec_t = ATyp::Vec(Box::new(inner_t.clone()), 2);
        let result_poly_t = ATyp::Uni(2); // Poly(1,2): 3 coefficients
        let result_t = ATyp::Vec(Box::new(result_poly_t.clone()), 2);

        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(1), result_t.clone(), Qualifier::Witness);

        builder.add_op(
            var.clone(),
            Op::Reduce(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_t)),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);

        // For each of the 2 elements (k=0,1):
        //   result[k] = v[0][k] * v[1][k]  (polynomial convolution)
        //   result[k][0] = v0[k][0] * v1[k][0]
        //   result[k][1] = v0[k][0] * v1[k][1] + v0[k][1] * v1[k][0]
        //   result[k][2] = v0[k][1] * v1[k][1]
        for k in 0..2 {
            let v0_k0 = var_v
                .clone()
                .with_index(0)
                .unwrap()
                .with_index(k)
                .unwrap()
                .with_index(0)
                .unwrap();
            let v0_k1 = var_v
                .clone()
                .with_index(0)
                .unwrap()
                .with_index(k)
                .unwrap()
                .with_index(1)
                .unwrap();
            let v1_k0 = var_v
                .clone()
                .with_index(1)
                .unwrap()
                .with_index(k)
                .unwrap()
                .with_index(0)
                .unwrap();
            let v1_k1 = var_v
                .clone()
                .with_index(1)
                .unwrap()
                .with_index(k)
                .unwrap()
                .with_index(1)
                .unwrap();

            let r_k0 = var.clone().with_index(k).unwrap().with_index(0).unwrap();
            let r_k1 = var.clone().with_index(k).unwrap().with_index(1).unwrap();
            let r_k2 = var.clone().with_index(k).unwrap().with_index(2).unwrap();

            let expected_0 = &var_poly(&v0_k0) * &var_poly(&v1_k0);
            let expected_1 =
                &(&var_poly(&v0_k0) * &var_poly(&v1_k1)) + &(&var_poly(&v0_k1) * &var_poly(&v1_k0));
            let expected_2 = &var_poly(&v0_k1) * &var_poly(&v1_k1);

            let stored_0 = ideal.pl.get(&r_k0).cloned();
            let stored_1 = ideal.pl.get(&r_k1).cloned();
            let stored_2 = ideal.pl.get(&r_k2).cloned();

            assert_eq!(
                stored_0,
                Some(expected_0),
                "reduce mul nested poly elem {} coeff 0",
                k
            );
            assert_eq!(
                stored_1,
                Some(expected_1),
                "reduce mul nested poly elem {} coeff 1",
                k
            );
            assert_eq!(
                stored_2,
                Some(expected_2),
                "reduce mul nested poly elem {} coeff 2",
                k
            );
        }
    }
}
