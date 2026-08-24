//! Power op encoders: `pow_op`, `pow_const`, `resolve_const_exp`.

use ark_ff::{BigInteger, One, PrimeField};

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::super::poly_source::has_poly_type;
use super::PolySource;
use super::mul::mul_op_inner;
use super::{EncodeCtx, link_to_polys};

/// Try to resolve a `PolySource` to a compile-time constant exponent.
/// Returns `Some(k)` if the source is a single constant polynomial whose
/// value fits in a `usize`; otherwise `None` (dynamic exponent).
fn resolve_const_exp<C: ArkConfig>(src: &PolySource<C>) -> Option<usize> {
    if src.polys().len() != 1 {
        return None;
    }
    let p = &src.polys()[0];
    if !p.is_constant() {
        return None;
    }
    let val = p.constant_coeff();
    let big = val.into_bigint();
    let bytes = big.to_bytes_le();
    let mut result: usize = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        if i >= std::mem::size_of::<usize>() {
            if byte != 0 {
                return None;
            }
            continue;
        }
        result |= (byte as usize) << (8 * i);
    }
    Some(result)
}

pub fn pow_const<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    base: &PolySource<C>,
    k: usize,
) {
    if k == 0 {
        // p^0 = 1 (constant polynomial). Type inference handles degree reduction:
        // Uni(n) ^ 0 has type Uni(0), Scalar ^ 0 has type Scalar.
        let one = Polynomial::<C::F>::lit(&C::F::one());
        link_to_polys(ctx.ideal, target, vec![one]);
        return;
    }

    if k == 1 {
        link_to_polys(ctx.ideal, target, base.polys().to_vec());
        return;
    }

    // Short-circuit: when the base type contains no polynomial type
    // (scalar / vec-of-scalar / vec-of-vec-of-scalar …), multiplication
    // is purely slot-wise with no cross-terms. Raise each slot polynomial
    // to the k-th power directly instead of allocating k-1 sentinel
    // `pow_acc` vars.
    if !has_poly_type(base.typ()) {
        let powered: Vec<Polynomial<C::F>> = base
            .polys()
            .iter()
            .map(|p| {
                let mut q = p.clone();
                q.pow(k);
                q
            })
            .collect();
        link_to_polys(ctx.ideal, target, powered);
        return;
    }

    let mut acc = PolySource::new(base.polys().to_vec(), base.typ().clone());
    for _step in 1..k {
        let next_name = ctx.builder.ns.next_name("pow_acc");
        let next_typ = ATyp::lub_mul(acc.typ(), base.typ(), &Nothing).expect("pow_const: lub_mul");
        let next_var = ctx
            .builder
            .sentinel_var(&next_name, next_typ.clone(), ctx.ideal);
        mul_op_inner(&mut *ctx, &next_var, &acc, base, &next_typ);
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
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    pow_op_inner(ctx, var, &a_src, &b_src);
}

fn pow_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a_src: &PolySource<C>,
    b_src: &PolySource<C>,
) {
    match (a_src.typ(), b_src.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            for i in 0..*na {
                let t_i = var.with_index(i).unwrap();
                let a_elem = a_src.at_index(i).unwrap();
                let b_elem = b_src.at_index(i).unwrap();
                pow_op_inner(ctx, &t_i, &a_elem, &b_elem);
            }
        }
        (ATyp::Vec(_, na), _) => {
            for i in 0..*na {
                let t_i = var.with_index(i).unwrap();
                let a_elem = a_src.at_index(i).unwrap();
                if let Some(k) = resolve_const_exp(b_src) {
                    pow_const(ctx, &t_i, &a_elem, k);
                } else {
                    super::uncovered_op("dynamic-pow", &t_i);
                }
            }
        }
        (_, ATyp::Vec(_, nb)) => {
            for i in 0..*nb {
                let t_i = var.with_index(i).unwrap();
                let b_elem = b_src.at_index(i).unwrap();
                if let Some(k) = resolve_const_exp(&b_elem) {
                    pow_const(ctx, &t_i, a_src, k);
                } else {
                    super::uncovered_op("dynamic-pow", &t_i);
                }
            }
        }
        _ => {
            if let Some(k) = resolve_const_exp(b_src) {
                pow_const(ctx, var, a_src, k);
            } else {
                super::uncovered_op("dynamic-pow", var);
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::super::{Ideal, IdealBuilder};

    use ark_ff::One;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::ArkConfig;
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
        let fin = ATyp::fin(lang::ast::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_ideal.clone(), Qualifier::Witness);
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

        let var_a = Var::from_node(NodeIndex::new(0), uni2.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), ideal_uni4.clone(), Qualifier::Witness);
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

        let var_a = Var::from_node(NodeIndex::new(0), vec_uni2.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), vec_ideal.clone(), Qualifier::Witness);
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

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), vec_ideal.clone(), Qualifier::Witness);
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
        let fin = ATyp::fin(lang::ast::range::CRange::default());
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_ideal.clone(), Qualifier::Witness);
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
        let fin = ATyp::fin(lang::ast::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        let var_r = Var::from_node(
            NodeIndex::new(2),
            ATyp::Vec(Box::new(s.clone()), 2),
            Qualifier::Witness,
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
        let fin = ATyp::fin(lang::ast::range::CRange::default());

        let var_a = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        // var_b is a Ref, not a Value::Index → non-const exponent.
        let var_b = Var::from_node(NodeIndex::new(1), fin.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), s.clone(), Qualifier::Witness);
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

    // === Regression tests for pow_op recursion fix ===

    /// pow_const with k=0 on Scalar: every slot of `target` must be bound to
    /// the constant polynomial 1 in `pl`.
    #[test]
    fn test_pow_scalar_exp_zero() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();

        let var_a = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::Index(0))),
                s.clone(),
            ),
            &mut ideal,
        );

        let slot = var_r.clone();
        let poly = ideal.pl.get(&slot).expect("pow k=0: slot must be in pl");
        assert!(
            poly.is_constant(),
            "pow k=0 on Scalar: ideal polynomial must be constant 1"
        );
        assert_eq!(
            poly.constant_coeff(),
            <ArkBls12_381 as ArkConfig>::F::one(),
            "pow k=0 on Scalar: constant coefficient must be 1"
        );
    }

    /// pow_const with k=1: `target` must be linked to `base` (identity).
    #[test]
    fn test_pow_scalar_exp_one() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();

        let var_a = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::Index(1))),
                s.clone(),
            ),
            &mut ideal,
        );

        let slot = var_r.clone();
        let poly = ideal.pl.get(&slot).expect("pow k=1: slot must be in pl");
        // k=1 links target to base — the polynomial should be the base's
        // variable polynomial (var(a_slot)), not a constant.
        assert!(
            !poly.is_constant(),
            "pow k=1: ideal polynomial must be the base variable, not a constant"
        );
    }

    /// Vec(Uni(2), 2) ^ VecIndex([2, 3]): per-element constant exponents
    /// on polynomial elements via VecIndex. Both elements get Uni(2)^2 and
    /// Uni(2)^3 respectively. The result type is Uni(6) (max degree), but
    /// element 0 (Uni(2)^2=Uni(4)) must be lifted to Uni(6) by the type
    /// checker. Here we test with VecIndex([2, 2]) so both produce Uni(4),
    /// matching the result type Vec(Uni(4), 2).
    #[test]
    fn test_pow_vec_uni_per_element_exps() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(uni4.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_uni2.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), vec_ideal.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Value(Value::VecIndex(vec![2, 2]))),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        // Both elements: Uni(2)^2 = Uni(4) → 5 slots each
        for i in 0..2 {
            let elem = var_r.with_index(i).unwrap();
            for j in 0..5 {
                let slot = elem.with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Pow Vec(Uni(2),2)^VecIndex([2,2]) element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
    }

    /// Vec(Vec(Scalar, 2), 2) ^ Index(2): nested Vec base with scalar const
    /// exponent. The exponent broadcasts to all elements, recursing through
    /// the nested Vec structure. All 4 scalar slots must be in pl.
    #[test]
    fn test_pow_nested_vec_scalar_exp() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s2 = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_vec_s2 = ATyp::Vec(Box::new(vec_s2.clone()), 2);
        let vec_vec_ideal = ATyp::Vec(Box::new(vec_s2.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_vec_s2.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), vec_vec_ideal.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_vec_s2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Value(Value::Index(2))),
                vec_vec_ideal.clone(),
            ),
            &mut ideal,
        );

        // 2×2 = 4 scalar slots, all must be in pl
        for i in 0..2 {
            let elem_i = var_r.with_index(i).unwrap();
            for j in 0..2 {
                let slot = elem_i.with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Pow Vec(Vec(Scalar,2),2)^2 element [{}][{}] missing from pl",
                    i,
                    j
                );
            }
        }
    }

    /// Vec(Scalar, 2) ^ Vec(Fin, 2) where the exponent is a Ref to a
    /// registered Var (symbolic, not constant). Must panic with dynamic-pow
    /// because the exponent values are symbolic polynomials, not constants.
    #[test]
    #[should_panic(expected = "ideal: operation has no polynomial-ideal treatment at dynamic-pow")]
    fn test_pow_vec_vec_ref_exponent_panics() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let fin = ATyp::fin(lang::ast::range::CRange::default());
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_fin = ATyp::Vec(Box::new(fin.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_fin.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_s.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        // Exponent is a Ref to a symbolic Var — not a constant.
        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_fin.clone())),
                vec_s.clone(),
            ),
            &mut ideal,
        );
    }

    /// Scalar ^ Index(3): basic scalar^3 with const exponent. The result
    /// should be in pl and not constant (depends on the base variable).
    #[test]
    fn test_pow_scalar_const_exp() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();

        let var_a = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_r = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Pow,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
                mk::<ArkBls12_381>(Op::Value(Value::Index(3))),
                s.clone(),
            ),
            &mut ideal,
        );

        let slot = var_r.clone();
        let poly = ideal.pl.get(&slot).expect("pow k=3: slot must be in pl");
        assert!(
            !poly.is_constant(),
            "pow k=3: ideal polynomial must depend on the base variable"
        );
        // k=3 introduces intermediate sentinel vars via mul_op, so the
        // polynomial in pl[target] is a product of sentinel vars, not
        // base^3 directly. Just check it's non-constant and in pl.
    }
}
