//! Binary op encoders: `add_op`, `sub_op`, `broadcast_binop`, `mul_op`,
//! `dot_op`, `pair_op`, and helpers `emit_slotwise_binop`, `apply_binop`.

use std::collections::HashMap;

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::HOp;
use lang::ast::BinOp;

use crate::Var;
use crate::frontend::Polynomial;

use super::PolySource;
use super::{EncodeCtx, link_to_polys};
use super::{hypercube, multi_indices};

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
        "broadcast_binop {context}: ideal slot count must match left operand"
    );
    assert_eq!(
        pr_slots.len(),
        right.len(),
        "broadcast_binop {context}: ideal slot count must match right operand"
    );

    let combined: Vec<Polynomial<C::F>> = left
        .iter()
        .zip(right)
        .map(|(l, r)| apply_binop::<C>(op, l, r))
        .collect();
    link_to_polys(ctx.ideal, var, combined);
}

fn broadcast_binop<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
    op: BinOp,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    broadcast_binop_inner(ctx, var, &a_src, &b_src, r_typ, op);
}

/// Slot-wise addition with type-aware broadcasting.
pub fn add_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
) {
    broadcast_binop(ctx, var, a, b, r_typ, BinOp::Add);
}

/// Slot-wise subtraction with type-aware broadcasting.
pub fn sub_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
) {
    broadcast_binop(ctx, var, a, b, r_typ, BinOp::Sub);
}

fn broadcast_binop_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
    op: BinOp,
) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                let r_inner = match r_typ {
                    ATyp::Vec(inner, _) => inner,
                    _ => panic!("broadcast_binop Vec×Vec ideal must be Vec"),
                };
                broadcast_binop_inner(
                    &mut *ctx,
                    &var.with_index(i).unwrap(),
                    &a_elem,
                    &b_elem,
                    r_inner,
                    op,
                );
            }
        }
        (_, _)
            if matches!(op, BinOp::Add | BinOp::Sub)
                && PolySource::<C>::is_scalar_like(b.typ())
                && a.is_poly() =>
        {
            let a_lifted = a.lift_to(r_typ);
            let b_lifted = b.inject_constant_to(r_typ);
            emit_slotwise_binop(
                &mut *ctx,
                var,
                a_lifted.polys(),
                b_lifted.polys(),
                op,
                "Poly×Scalar",
            );
        }
        (_, _)
            if matches!(op, BinOp::Add | BinOp::Sub)
                && PolySource::<C>::is_scalar_like(a.typ())
                && b.is_poly() =>
        {
            let a_lifted = a.inject_constant_to(r_typ);
            let b_lifted = b.lift_to(r_typ);
            emit_slotwise_binop(
                &mut *ctx,
                var,
                a_lifted.polys(),
                b_lifted.polys(),
                op,
                "Scalar×Poly",
            );
        }
        (_, _) if PolySource::<C>::is_scalar_like(b.typ()) && a.physical_len() > 1 => {
            let b_broadcast = b.broadcast_scalar_to(a.typ());
            emit_slotwise_binop(
                &mut *ctx,
                var,
                a.polys(),
                b_broadcast.polys(),
                op,
                "value×scalar",
            );
        }
        (_, _) if PolySource::<C>::is_scalar_like(a.typ()) && b.physical_len() > 1 => {
            let a_broadcast = a.broadcast_scalar_to(b.typ());
            emit_slotwise_binop(
                &mut *ctx,
                var,
                a_broadcast.polys(),
                b.polys(),
                op,
                "scalar×value",
            );
        }
        _ if a.is_poly() || b.is_poly() || matches!(r_typ, ATyp::Mle(_)) => {
            let a_lifted = a.lift_to(r_typ);
            let b_lifted = b.lift_to(r_typ);
            emit_slotwise_binop(
                &mut *ctx,
                var,
                a_lifted.polys(),
                b_lifted.polys(),
                op,
                "poly/lifted",
            );
        }
        _ => {
            emit_slotwise_binop(&mut *ctx, var, a.polys(), b.polys(), op, "slotwise");
        }
    }
}

/// For `Vec<T>` × `Vec<T>`, iterates over logical indices and recurses
/// per element. At the leaf level (non-Vec), dispatches to polynomial
/// convolution (VPoly/Uni/Mle) or slot-wise multiplication (base types).
pub fn mul_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    r_typ: &ATyp,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    mul_op_inner(ctx, target, &a_src, &b_src, r_typ);
}

pub fn mul_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            let r_inner = match r_typ {
                ATyp::Vec(inner, _) => inner,
                _ => panic!("mul_op Vec×Vec ideal must be Vec"),
            };
            for i in 0..*na {
                let t_i = target.with_index(i).unwrap();
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                mul_op_inner(&mut *ctx, &t_i, &a_elem, &b_elem, r_inner);
            }
        }
        (ATyp::Vec(_, na), _) => {
            let r_inner = match r_typ {
                ATyp::Vec(inner, _) => inner,
                _ => panic!("mul_op Vec×scalar ideal must be Vec"),
            };
            for i in 0..*na {
                let t_i = target.with_index(i).unwrap();
                let a_elem = a.at_index(i).unwrap();
                mul_op_inner(&mut *ctx, &t_i, &a_elem, b, r_inner);
            }
        }
        (_, ATyp::Vec(_, nb)) => {
            let r_inner = match r_typ {
                ATyp::Vec(inner, _) => inner,
                _ => panic!("mul_op scalar×Vec ideal must be Vec"),
            };
            for i in 0..*nb {
                let t_i = target.with_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                mul_op_inner(&mut *ctx, &t_i, a, &b_elem, r_inner);
            }
        }
        (_, ATyp::Base(ABase::Scalar)) if a.is_poly() => {
            let _target_slots = target.slots();
            let prods: Vec<Polynomial<C::F>> =
                a.polys().iter().map(|ap| ap * &b.polys()[0]).collect();
            link_to_polys(ctx.ideal, target, prods);
        }
        (ATyp::Base(ABase::Scalar), _) if b.is_poly() => {
            let prods: Vec<Polynomial<C::F>> =
                b.polys().iter().map(|bp| &a.polys()[0] * bp).collect();
            link_to_polys(ctx.ideal, target, prods);
        }
        (ATyp::Mle(na), ATyp::Mle(nb)) if na == nb => {
            let ATyp::VPoly(_nr, mr) = r_typ else {
                panic!("Mul Mle×Mle ideal must be VPoly");
            };
            let n = *na;
            let all_b = hypercube(n);
            let r_idx = multi_indices(n, *mr);
            let single_var_coeff = |ba: usize, bb: usize, k: usize| -> i64 {
                if k >= 3 {
                    return 0;
                }
                const C: [[[i64; 3]; 2]; 2] = [[[1, -2, 1], [0, 1, -1]], [[0, 1, -1], [0, 0, 1]]];
                C[ba][bb][k]
            };
            let lit_of = |v: i64| -> Polynomial<C::F> {
                if v >= 0 {
                    Polynomial::lit(&C::FOps::from_usize(v as usize))
                } else {
                    -Polynomial::lit(&C::FOps::from_usize((-v) as usize))
                }
            };
            let mut out: Vec<Polynomial<C::F>> = vec![Polynomial::<C::F>::zero(); r_idx.len()];
            for (ia, ba) in all_b.iter().enumerate() {
                for (ib, bb) in all_b.iter().enumerate() {
                    let uv = &a.polys()[ia] * &b.polys()[ib];
                    for (ir, k) in r_idx.iter().enumerate() {
                        let mut scalar: i64 = 1;
                        for i in 0..n {
                            let c = single_var_coeff(ba[i], bb[i], k[i]);
                            if c == 0 {
                                scalar = 0;
                                break;
                            }
                            scalar *= c;
                        }
                        if scalar == 0 {
                            continue;
                        }
                        out[ir] = &out[ir] + &(&lit_of(scalar) * &uv);
                    }
                }
            }
            link_to_polys(ctx.ideal, target, out);
        }
        (ATyp::Mle(na), ATyp::VPoly(nb, mb)) | (ATyp::VPoly(nb, mb), ATyp::Mle(na))
            if *na == *nb =>
        {
            let ATyp::VPoly(nr, mr) = r_typ else {
                panic!("Mul Mle×VPoly ideal must be VPoly");
            };
            assert!(
                *nr == *na && *mr == *mb + *na,
                "Mul Mle({})×VPoly({}, {}) ideal must be VPoly({}, {}), got VPoly({}, {})",
                na,
                nb,
                mb,
                na,
                *mb + *na,
                nr,
                mr
            );
            let n = *na;
            let (mle_src, vpoly_src) = if matches!(a.typ(), ATyp::Mle(_)) {
                (a, b)
            } else {
                (b, a)
            };
            let all_b = hypercube(n);
            let b_idx = multi_indices(n, *mb);
            let r_idx = multi_indices(n, *mr);
            let lit_of = |v: i64| -> Polynomial<C::F> {
                if v >= 0 {
                    Polynomial::lit(&C::FOps::from_usize(v as usize))
                } else {
                    -Polynomial::lit(&C::FOps::from_usize((-v) as usize))
                }
            };
            let mut out: Vec<Polynomial<C::F>> = vec![Polynomial::<C::F>::zero(); r_idx.len()];
            // Coefficient of x^k in L_{ba}(x) · x^{kb}, indexed by
            // [ba][k - kb] (only when k >= kb).  L_0(x)=1-x → x^kb - x^{kb+1};
            // L_1(x)=x → x^{kb+1}.
            const C: [[i64; 2]; 2] = [[1, -1], [0, 1]];
            for (ia, ba) in all_b.iter().enumerate() {
                for (ib, kb) in b_idx.iter().enumerate() {
                    let uv = &mle_src.polys()[ia] * &vpoly_src.polys()[ib];
                    for (ir, k) in r_idx.iter().enumerate() {
                        let mut scalar: i64 = 1;
                        for i in 0..n {
                            if k[i] < kb[i] {
                                scalar = 0;
                                break;
                            }
                            let delta = k[i] - kb[i];
                            if delta >= 2 {
                                scalar = 0;
                                break;
                            }
                            let c = C[ba[i]][delta];
                            if c == 0 {
                                scalar = 0;
                                break;
                            }
                            scalar *= c;
                        }
                        if scalar == 0 {
                            continue;
                        }
                        out[ir] = &out[ir] + &(&lit_of(scalar) * &uv);
                    }
                }
            }
            link_to_polys(ctx.ideal, target, out);
        }
        _ if a.is_poly() && b.is_poly() => {
            let a_norm = match a.typ() {
                ATyp::Uni(m) => ATyp::VPoly(1, *m),
                other => other.clone(),
            };
            let b_norm = match b.typ() {
                ATyp::Uni(m) => ATyp::VPoly(1, *m),
                other => other.clone(),
            };
            let r_norm = match r_typ {
                ATyp::Uni(m) => ATyp::VPoly(1, *m),
                other => other.clone(),
            };
            match (&a_norm, &b_norm, &r_norm) {
                (ATyp::VPoly(na, ma), ATyp::VPoly(nb, mb), ATyp::VPoly(nr, mr))
                    if na == nb && na == nr =>
                {
                    let a_idx = multi_indices(*na, *ma);
                    let b_idx = multi_indices(*nb, *mb);
                    let r_idx = multi_indices(*nr, *mr);
                    let r_pos: HashMap<&Vec<usize>, usize> =
                        r_idx.iter().enumerate().map(|(i, k)| (k, i)).collect();
                    let mut out: Vec<Polynomial<C::F>> =
                        vec![Polynomial::<C::F>::zero(); r_idx.len()];
                    for (ia, ka) in a_idx.iter().enumerate() {
                        for (ib, kb) in b_idx.iter().enumerate() {
                            let k: Vec<usize> =
                                ka.iter().zip(kb.iter()).map(|(x, y)| x + y).collect();
                            let ir = *r_pos.get(&k).expect("multi-index missing in ideal");
                            out[ir] = &out[ir] + &(&a.polys()[ia] * &b.polys()[ib]);
                        }
                    }
                    link_to_polys(ctx.ideal, target, out);
                }
                _ => {
                    super::uncovered_op("mul-unsupported-poly-combo", target);
                }
            }
        }
        (ATyp::Base(_), ATyp::Base(_)) => {
            let prods: Vec<Polynomial<C::F>> = a
                .polys()
                .iter()
                .zip(b.polys())
                .map(|(ap, bp)| ap * bp)
                .collect();
            link_to_polys(ctx.ideal, target, prods);
        }
        _ => {
            super::uncovered_op("mul-unsupported-type-combo", target);
        }
    }
}

pub fn dot_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    dot_op_inner(ctx, var, &a_src, &b_src);
}

fn dot_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            let r_elem_len = var.typ.physical_len();
            let mut acc: Vec<Polynomial<C::F>> = vec![Polynomial::zero(); r_elem_len];
            for i in 0..*na {
                let acc_name = ctx.builder.ns.next_name("dot_acc");
                let acc_var = ctx.sentinel_var(&acc_name, var.typ.clone());
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                mul_op_inner(&mut *ctx, &acc_var, &a_elem, &b_elem, &var.typ);
                let acc_vars: Vec<Polynomial<C::F>> = acc_var
                    .slots()
                    .into_iter()
                    .map(|s| Polynomial::var(&s))
                    .collect();
                assert_eq!(
                    acc_vars.len(),
                    acc.len(),
                    "dot_op: acc_var slot count must match accumulator"
                );
                for (j, a) in acc.iter_mut().enumerate() {
                    *a = &*a + &acc_vars[j];
                }
            }
            link_to_polys(ctx.ideal, var, acc);
        }
        (ATyp::Base(_), ATyp::Base(_)) => {
            assert_eq!(
                var.slots().len(),
                1,
                "Dot: Base·Base ideal must be single slot"
            );
            let sum: Polynomial<C::F> = a.polys().iter().zip(b.polys()).map(|(a, b)| a * b).sum();
            link_to_polys(ctx.ideal, var, vec![sum]);
        }
        _ => {
            super::uncovered_op("dot-unsupported-type-combo", var);
        }
    }
}

pub fn pair_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    pair_op_inner(ctx, var, &a_src, &b_src);
}

fn pair_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
) {
    match (a.typ(), b.typ(), &var.typ) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb), ATyp::Vec(r_inner, _)) if na == nb => {
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                let t_i = var.with_index(i).unwrap();
                let a_lifted = a_elem.lift_to(r_inner);
                let b_lifted = b_elem.lift_to(r_inner);
                let es: Vec<Polynomial<C::F>> = a_lifted
                    .polys()
                    .iter()
                    .zip(b_lifted.polys())
                    .map(|(a, b)| a * b)
                    .collect();
                link_to_polys(ctx.ideal, &t_i, es);
            }
        }
        (ATyp::Base(_), ATyp::Base(_), ATyp::Base(_)) => {
            let es: Vec<Polynomial<C::F>> = a
                .polys()
                .iter()
                .zip(b.polys())
                .map(|(a, b)| a * b)
                .collect();
            link_to_polys(ctx.ideal, var, es);
        }
        _ => {
            super::uncovered_op("pair-unsupported-type-combo", var);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::{
        assert_ideal_slot, scalar_poly_binop_ideal, trans_clos_from_src,
    };
    use super::super::{Ideal, IdealBuilder};
    use super::multi_indices;

    use crate::frontend::Polynomial;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::Value;
    use backend::op::mk;
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
            let p = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 1), Qualifier::Private);
            ideal.register(&p);
            p
        };
        let var_b = {
            let p = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 1), Qualifier::Private);
            ideal.register(&p);
            p
        };

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 1), Qualifier::Private);
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
            let p = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Private);
            ideal.register(&p);
            p
        };
        let var_b = {
            let p = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Private);
            ideal.register(&p);
            p
        };

        let var = Var::from_node(NodeIndex::new(2), ATyp::Mle(2), Qualifier::Private);
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
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 2), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 2), Qualifier::Private);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 2), Qualifier::Private);
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
    fn test_add_op_vpoly_mul_univariate_convolution() {
        // VPoly(1,1) × VPoly(1,1) → VPoly(1,2), a_0 b_0, a_0 b_1 + a_1 b_0, a_1 b_1.
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 1), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Private);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 2), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // VPoly(1,2) has physical_len = 3 slots (degrees 0, 1, 2 in graded-lex order).
        assert_eq!(ATyp::VPoly(1, 2).physical_len(), 3);
        let a0 = var_a.clone().with_index(0).unwrap();
        let a1 = var_a.clone().with_index(1).unwrap();
        let b0 = var_b.clone().with_index(0).unwrap();
        let b1 = var_b.clone().with_index(1).unwrap();

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let deg0 = ideal
            .pl
            .get(&var.clone().with_index(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = ideal
            .pl
            .get(&var.clone().with_index(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = ideal
            .pl
            .get(&var.clone().with_index(2).unwrap())
            .unwrap()
            .clone();
        assert_eq!(deg0, &var_poly(&a0) * &var_poly(&b0), "(*.x^0)");
        assert_eq!(
            deg1,
            &(&var_poly(&a0) * &var_poly(&b1)) + &(&var_poly(&a1) * &var_poly(&b0)),
            "(*.x^1)"
        );
        assert_eq!(deg2, &var_poly(&a1) * &var_poly(&b1), "(*.x^2)");
    }

    #[test]
    fn test_add_op_vpoly_mul_multivariate_spotcheck() {
        // VPoly(2,1) × VPoly(2,1) → VPoly(2,2). We spot-check one slot.
        // VPoly(2,1) multi-indices (graded-lex by total deg then lex):
        //   [0,0], [0,1], [1,0]   (sizes 3)
        // VPoly(2,2) multi-indices:
        //   [0,0], [0,1], [1,0], [0,2], [1,1], [2,0]   (size 6)
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 1), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 1), Qualifier::Private);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 2), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // Check the constant-term slot (multi-index [0,0]): should be a_[0,0] * b_[0,0].
        let r_idx = multi_indices(2, 2);
        let a_idx = multi_indices(2, 1);
        let pos_00 = r_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let a_pos_00 = a_idx.iter().position(|k| k == &vec![0, 0]).unwrap();

        let a00 = var_a.clone().with_index(a_pos_00).unwrap();
        let b00 = var_b.clone().with_index(a_pos_00).unwrap();
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let got = ideal
            .pl
            .get(&var.clone().with_index(pos_00).unwrap())
            .unwrap()
            .clone();
        assert_eq!(
            got,
            &var_poly(&a00) * &var_poly(&b00),
            "VPoly(2,2) constant term mismatch"
        );

        // Ensure all 6 slots were populated.
        for i in 0..6 {
            assert!(
                ideal.pl.contains(&var.clone().with_index(i).unwrap()),
                "VPoly(2,2) slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_mle_mul_basis_change() {
        // Mle(1) × Mle(1) → VPoly(1, 2). Verify by evaluating the idealing poly at
        // a concrete point x: for p(x) = u_0 · (1-x) + u_1 · x and
        // q(x) = v_0 · (1-x) + v_1 · x, the product p·q has coefficients
        //   x^0 :  u_0 v_0
        //   x^1 :  -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        //   x^2 :  u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_u = Var::from_node(NodeIndex::new(0), ATyp::Mle(1), Qualifier::Private);
        ideal.register(&var_u);
        let var_v = Var::from_node(NodeIndex::new(1), ATyp::Mle(1), Qualifier::Private);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 2), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Mle(1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // 3 slots populated.
        for i in 0..3 {
            assert!(
                ideal.pl.contains(&var.clone().with_index(i).unwrap()),
                "Mle×Mle slot {} missing",
                i
            );
        }

        let u0 = var_u.clone().with_index(0).unwrap();
        let u1 = var_u.clone().with_index(1).unwrap();
        let v0 = var_v.clone().with_index(0).unwrap();
        let v1 = var_v.clone().with_index(1).unwrap();
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);

        let deg0 = ideal
            .pl
            .get(&var.clone().with_index(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = ideal
            .pl
            .get(&var.clone().with_index(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = ideal
            .pl
            .get(&var.clone().with_index(2).unwrap())
            .unwrap()
            .clone();

        // deg0 = u_0 * v_0
        assert_eq!(deg0, &var_poly(&u0) * &var_poly(&v0), "mle mul deg0");

        // deg1 = -2 u_0 v_0 + u_0 v_1 + u_1 v_0
        let two =
            Polynomial::<ark_bls12_381::Fr>::lit(&<ark_bls12_381::Fr as From<u64>>::from(2u64));
        let expected_deg1 = &(&(&var_poly(&u0) * &var_poly(&v1))
            + &(&var_poly(&u1) * &var_poly(&v0)))
            - &(&two * &(&var_poly(&u0) * &var_poly(&v0)));
        assert_eq!(deg1, expected_deg1, "mle mul deg1");

        // deg2 = u_0 v_0 - u_0 v_1 - u_1 v_0 + u_1 v_1
        let expected_deg2 = &(&(&var_poly(&u0) * &var_poly(&v0))
            - &(&var_poly(&u0) * &var_poly(&v1)))
            + &(&(&var_poly(&u1) * &var_poly(&v1)) - &(&var_poly(&u1) * &var_poly(&v0)));
        assert_eq!(deg2, expected_deg2, "mle mul deg2");
    }

    #[test]
    fn test_add_op_mle_vpoly_mul_univariate() {
        // Mle(1) × VPoly(1, 1) → VPoly(1, 2).
        //   MLE: u_0 (eval at 0), u_1 (eval at 1), so p(x) = u_0·(1-x) + u_1·x
        //   VPoly: b_0 + b_1·x
        //   Product: p(x)·q(x) = (u_0·b_0) + (u_1·b_0 - u_0·b_0 + u_0·b_1)·x
        //                      + (u_1·b_1 - u_0·b_1)·x²
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_u = Var::from_node(NodeIndex::new(0), ATyp::Mle(1), Qualifier::Private);
        ideal.register(&var_u);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Private);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 2), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let u0 = var_u.clone().with_index(0).unwrap();
        let u1 = var_u.clone().with_index(1).unwrap();
        let b0 = var_b.clone().with_index(0).unwrap();
        let b1 = var_b.clone().with_index(1).unwrap();
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);

        let deg0 = ideal
            .pl
            .get(&var.clone().with_index(0).unwrap())
            .unwrap()
            .clone();
        let deg1 = ideal
            .pl
            .get(&var.clone().with_index(1).unwrap())
            .unwrap()
            .clone();
        let deg2 = ideal
            .pl
            .get(&var.clone().with_index(2).unwrap())
            .unwrap()
            .clone();

        assert_eq!(deg0, &var_poly(&u0) * &var_poly(&b0), "mle×vpoly deg0");

        let expected_deg1 = &(&var_poly(&u1) * &var_poly(&b0)) - &(&var_poly(&u0) * &var_poly(&b0))
            + &var_poly(&u0) * &var_poly(&b1);
        assert_eq!(deg1, expected_deg1, "mle×vpoly deg1");

        let expected_deg2 = &(&var_poly(&u1) * &var_poly(&b1)) - &(&var_poly(&u0) * &var_poly(&b1));
        assert_eq!(deg2, expected_deg2, "mle×vpoly deg2");
    }

    #[test]
    fn test_add_op_vpoly_mle_mul_bivariate() {
        // VPoly(2, 1) × Mle(2) → VPoly(2, 3). Commutative variant.
        // VPoly(2,1) has 3 slots: [0,0], [1,0], [0,1] (graded-lex).
        // Mle(2) has 4 slots: evals at (0,0), (1,0), (0,1), (1,1).
        // Result VPoly(2,3) has 10 slots.
        // Just verify all 10 ideal slots are populated.
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_b = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 1), Qualifier::Private);
        ideal.register(&var_b);
        let var_u = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Private);
        ideal.register(&var_u);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 3), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(2, 1))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Mle(2))),
            ATyp::VPoly(2, 3),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let r_idx = multi_indices(2, 3);
        assert_eq!(r_idx.len(), 10, "VPoly(2,3) should have 10 multi-indices");
        for i in 0..10 {
            assert!(
                ideal.pl.contains(&var.clone().with_index(i).unwrap()),
                "VPoly×Mle slot {} missing",
                i
            );
        }
    }

    #[test]
    fn test_add_op_mle_vpoly_mul_bivariate_coefficients() {
        // Mle(2) × VPoly(2, 1) → VPoly(2, 3).
        // Verify the constant-term slot (multi-index [0,0]) and a cross-term.
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_u = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Private);
        ideal.register(&var_u);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 1), Qualifier::Private);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 3), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Mul,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(2, 1))),
            ATyp::VPoly(2, 3),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        let r_idx = multi_indices(2, 3);
        let v_idx = multi_indices(2, 1);
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);

        // Constant term [0,0]: u_00 * b_00
        let pos_00 = r_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let v_pos_00 = v_idx.iter().position(|k| k == &vec![0, 0]).unwrap();
        let u00 = var_u.clone().with_index(0).unwrap();
        let b00 = var_b.clone().with_index(v_pos_00).unwrap();
        let got_00 = ideal
            .pl
            .get(&var.clone().with_index(pos_00).unwrap())
            .unwrap()
            .clone();
        assert_eq!(
            got_00,
            &var_poly(&u00) * &var_poly(&b00),
            "bivariate constant term"
        );

        // [1,0] slot: -u_00·b_10 + u_10·b_00 + u_00·b_10... check it's populated
        let pos_10 = r_idx.iter().position(|k| k == &vec![1, 0]).unwrap();
        assert!(
            ideal.pl.contains(&var.clone().with_index(pos_10).unwrap()),
            "bivariate [1,0] slot missing"
        );

        // All 10 slots populated
        assert_eq!(r_idx.len(), 10);
        for i in 0..10 {
            assert!(
                ideal.pl.contains(&var.clone().with_index(i).unwrap()),
                "Mle×VPoly bivariate slot {} missing",
                i
            );
        }
    }

    #[test]
    fn ideal_vec_add_1d() {
        let src = r#"
            proto va1d<F: Field>(public a: F, public b: F, public c: F, public d: F) where a == a {
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
                public a: F, public b: F, public c: F, public d: F,
                public e: F, public f: F, public g: F, public h: F
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

        // Namespace should register all 8 public inputs
        let ns_named_count = gr.vars.values().filter(|p| !p.name.is_empty()).count();
        assert!(
            ns_named_count >= 8,
            "namespace should register >= 8 named public vars, got {}",
            ns_named_count
        );
    }

    #[test]
    fn ideal_vec_add_3d() {
        let src = r#"
            proto va3d<F: Field>(
                public a: F, public b: F, public c: F, public d: F,
                public e: F, public f: F, public g: F, public h: F
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
            "namespace should register >= 8 named public vars, got {}",
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

        let var_a = Var::from_node(NodeIndex::new(0), uni2.clone(), Qualifier::Private);
        ideal.register(&var_a);
        let coefs_a: Vec<_> = (1..=3u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_a.clone(), Op::Vec(coefs_a), &mut ideal);

        let var_b = Var::from_node(NodeIndex::new(1), uni4.clone(), Qualifier::Private);
        ideal.register(&var_b);
        let coefs_b: Vec<_> = (1..=5u64)
            .map(|n| mk::<ArkBls12_381>(Op::Value(Value::Scalar(Fr::from(n)))))
            .collect();
        builder.add_op(var_b.clone(), Op::Vec(coefs_b), &mut ideal);

        let var_r = Var::from_node(NodeIndex::new(2), uni4_ideal.clone(), Qualifier::Private);
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
    fn test_mul_scalar_poly_broadcast() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);

        let var_s = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Public);
        ideal.register(&var_s);

        let var_p = Var::from_node(NodeIndex::new(1), uni2.clone(), Qualifier::Public);
        ideal.register(&var_p);

        let var_r = Var::from_node(NodeIndex::new(2), uni2.clone(), Qualifier::Public);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), uni2.clone())),
                uni2.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(
            ideal.generating_set.len(),
            3,
            "Scalar * Uni(2) should produce 3 basis rows (one per coefficient)"
        );
        for i in 0..3 {
            let slot = var_r.clone().with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Scalar*Uni(2) ideal slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_mul_vec_scalar_broadcast() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let v3 = ATyp::Vec(Box::new(s.clone()), 3);

        let var_v = Var::from_node(NodeIndex::new(0), v3.clone(), Qualifier::Public);
        ideal.register(&var_v);

        let var_s = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Public);
        ideal.register(&var_s);

        let var_r = Var::from_node(NodeIndex::new(2), v3.clone(), Qualifier::Public);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), v3.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
                v3.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(
            ideal.generating_set.len(),
            3,
            "Vec<Scalar,3> * Scalar should produce 3 basis rows"
        );
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

    #[test]
    fn test_dot_vec_scalar() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 3);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), s.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_s.clone())),
                s.clone(),
            ),
            &mut ideal,
        );

        assert!(
            ideal.pl.contains(&var_r),
            "Dot Vec(Scalar,3)·Vec(Scalar,3) ideal should be in pl"
        );
        assert!(
            !ideal.generating_set.is_empty(),
            "Dot Vec(Scalar,3)·Vec(Scalar,3) should produce basis rows"
        );
    }

    #[test]
    fn test_dot_vec_uni() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let dot_ideal = ATyp::Uni(6);

        let var_a = Var::from_node(NodeIndex::new(0), vec_uni2.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_uni4.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), dot_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                dot_ideal.clone(),
            ),
            &mut ideal,
        );

        for i in 0..7 {
            let slot = var_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Dot Vec(Uni(2),2)·Vec(Uni(4),2) ideal slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_pair_vec() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let g1 = ATyp::g1();
        let g2 = ATyp::g2();
        let gt = ATyp::gt();
        let vec_g1 = ATyp::Vec(Box::new(g1.clone()), 2);
        let vec_g2 = ATyp::Vec(Box::new(g2.clone()), 2);
        let vec_gt = ATyp::Vec(Box::new(gt.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_g1.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_g2.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_gt.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_g1.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_g2.clone())),
                vec_gt.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = var_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&elem),
                "Pair Vec(G1,2)×Vec(G2,2) ideal element {} missing from pl",
                i
            );
        }
    }
}
