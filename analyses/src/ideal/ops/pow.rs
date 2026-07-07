//! Power op encoders: `pow_op`, `pow_const`, and constant-exponent
//! resolvers `resolve_const_exp_scalar`, `resolve_const_exps_vec`.

use ark_ff::One;

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, Value};
use graph::{HOp, Op};
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::super::PolySource;
use super::binop::mul_op;
use super::{EncodeCtx, link_to_polys};

/// Try to resolve a scalar operand to a compile-time constant index.
pub fn resolve_const_exp_scalar<C: ArkConfig>(b: &HOp<C>) -> Option<usize> {
    match b.get() {
        Op::Value(Value::Index(i)) => Some(*i),
        _ => None,
    }
}

/// Try to resolve each element of a Vec operand to a compile-time constant index.
pub fn resolve_const_exps_vec<C: ArkConfig>(b: &HOp<C>, n: usize) -> Vec<Option<usize>> {
    match b.get() {
        Op::Value(Value::VecIndex(vs)) => vs.iter().map(|i| Some(*i)).collect(),
        Op::Vec(vs) => vs
            .iter()
            .map(|v| match v.get() {
                Op::Value(Value::Index(i)) => Some(*i),
                _ => None,
            })
            .collect(),
        Op::Value(Value::Index(i)) => {
            vec![Some(*i); n]
        }
        _ => vec![None; n],
    }
}

pub fn pow_const<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    base: &PolySource<C>,
    _ideal_typ: &ATyp,
    k: usize,
) {
    if k == 0 {
        let one = Polynomial::<C::F>::lit(&C::F::one());
        for pf in target.slots() {
            ctx.ideal.pl.insert(&pf, &one);
            ctx.ideal
                .generating_set
                .push(one.clone() - Polynomial::var(&pf));
        }
        return;
    }
    if k == 1 {
        link_to_polys(ctx.ideal, target, base.polys().to_vec());
        return;
    }
    let mut acc = PolySource::new(base.polys().to_vec(), base.typ().clone());
    for _step in 1..k {
        let next_name = ctx.ns.next_name("pow_acc");
        let next_typ = ATyp::lub_mul(acc.typ(), base.typ(), &Nothing).expect("pow_const: lub_mul");
        let next_var = ctx.sentinel_var(&next_name, next_typ.clone());
        mul_op(&next_var, &acc, base, &next_typ, ctx.ideal);
        acc = PolySource::new(
            next_var
                .slots()
                .into_iter()
                .map(|s| Polynomial::var(&s))
                .collect(),
            next_typ,
        );
    }
    link_to_polys(ctx.ideal, target, acc.polys);
}

pub fn pow_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    match (a_src.typ(), &b.typ(), &var.typ) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb), ATyp::Vec(r_inner, _)) if na == nb => {
            let elem_exps = resolve_const_exps_vec(b, *na);
            for (i, exp) in elem_exps.iter().enumerate().take(*na) {
                let t_i = var.with_index(i).unwrap();
                let elem_a = a_src.at_index(i).unwrap();
                if let Some(k) = exp {
                    pow_const(ctx, &t_i, &elem_a, r_inner, *k);
                } else {
                    uncovered_op("dynamic-pow", &t_i);
                }
            }
        }
        (ATyp::Vec(_, na), _, ATyp::Vec(r_inner, _)) => {
            let k = resolve_const_exp_scalar(b);
            for i in 0..*na {
                let t_i = var.with_index(i).unwrap();
                let elem_a = a_src.at_index(i).unwrap();
                if let Some(k) = k {
                    pow_const(ctx, &t_i, &elem_a, r_inner, k);
                } else {
                    uncovered_op("dynamic-pow", &t_i);
                }
            }
        }
        (_, ATyp::Vec(_, nb), ATyp::Vec(_, _)) => {
            let elem_exps = resolve_const_exps_vec(b, *nb);
            for (i, exp) in elem_exps.iter().enumerate().take(*nb) {
                let t_i = var.with_index(i).unwrap();
                if let Some(k) = exp {
                    pow_const(ctx, &t_i, &a_src, &t_i.typ, *k);
                } else {
                    uncovered_op("dynamic-pow", &t_i);
                }
            }
        }
        _ => {
            if let Some(k) = resolve_const_exp_scalar(b) {
                pow_const(ctx, var, &a_src, &var.typ, k);
            } else {
                uncovered_op("dynamic-pow", var);
            }
        }
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

    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::Value;
    use backend::op::mk;
    use graph::Op;

    #[test]
    #[should_panic(expected = "ideal: operation has no polynomial-ideal treatment at dynamic-pow")]
    fn test_pow_vec_element_wise() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );
        // The above panics with "dynamic-pow"; assertions below are not expected.
    }

    #[test]
    fn test_pow_uni_const_exp() {
        use crate::Var;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let ideal_uni4 = ATyp::Uni(4);

        let var_a = Var::from_node(NodeIndex::new(0), uni2.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), ideal_uni4.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), uni2.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                ideal_uni4.clone(),
            ),
            &mut ideal,
        );

        for i in 0..5 {
            let slot = var_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "Pow Uni(2)^2 ideal slot {} missing from pl",
                i
            );
        }
        // Constant-exponent pow uses explicit ideal treatment; ideal is in pl.
    }

    #[test]
    fn test_pow_vec_uni_const_exp() {
        use crate::Var;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let ideal_uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(ideal_uni4.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_uni2.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), vec_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = var_r.with_index(i).unwrap();
            for j in 0..5 {
                let slot = elem.with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Pow Vec(Uni(2),2)^2 element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
        // Constant-exponent pow uses explicit ideal treatment; ideal is in pl.
    }

    #[test]
    fn test_pow_vec_vecindex_per_element() {
        use crate::Var;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), vec_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::VecIndex(vec![2, 3]))),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = var_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&elem),
                "Pow Vec(Scalar,2)^VecIndex([2,3]) ideal element {} missing from pl",
                i
            );
        }
        // VecIndex-exponent pow uses explicit ideal treatment (per-element const exponents).
    }

    #[test]
    #[should_panic(expected = "ideal: operation has no polynomial-ideal treatment at dynamic-pow")]
    fn test_pow_vec_mixed_const_and_opaque() {
        use crate::Var;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );
        // The above panics with "dynamic-pow"; assertions below are not expected.
    }

    /// dynamic-pow: Vec^Vec with non-const exponent must panic rather
    /// than silently weakening the ideal.
    #[test]
    #[should_panic(expected = "ideal: operation has no polynomial-ideal treatment at dynamic-pow")]
    fn uncovered_op_dynamic_pow_vec_vec_panics() {
        use crate::Var;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(
            NodeIndex::new(2),
            ATyp::Vec(Box::new(s.clone()), 2),
            Qualifier::Private,
        );
        ideal.register(&var_r);

        // Non-const exponent (a runtime Ref, not a Value::Index) must panic.
        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                ATyp::Vec(Box::new(s.clone()), 2),
            ),
            &mut ideal,
        );
    }

    /// dynamic-pow: scalar^scalar with non-const exponent must panic.

    #[test]
    #[should_panic(expected = "ideal: operation has no polynomial-ideal treatment at dynamic-pow")]
    fn uncovered_op_dynamic_pow_scalar_panics() {
        use crate::Var;
        use backend::op::mk;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::typ::range::CRange::default());

        let var_a = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        // var_b is a Ref, not a Value::Index → non-const exponent.
        let var_b = Var::from_node(NodeIndex::new(1), fin.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), s.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), fin.clone())),
                s.clone(),
            ),
            &mut ideal,
        );
    }
}
