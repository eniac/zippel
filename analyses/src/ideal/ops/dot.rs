//! Dot-product op encoder: `dot_op`, `dot_op_inner`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::PolySource;
use super::mul::mul_op_inner;
use super::{EncodeCtx, link_to_polys};

/// Recursively check whether `typ` contains any polynomial type
/// (`Uni`/`Mle`/`VPoly`) at any nesting depth.
fn has_poly_type(typ: &ATyp) -> bool {
    match typ {
        ATyp::Uni(_) | ATyp::Mle(_) | ATyp::VPoly(_, _) => true,
        ATyp::Vec(inner, _) => has_poly_type(inner),
        _ => false,
    }
}

/// Element-wise slot-wise mul for non-polynomial types. Returns one
/// polynomial per physical slot of the result. Handles broadcasting
/// when one side is a single-slot scalar.
fn mul_slotwise<C: ArkConfig>(a: &PolySource<C>, b: &PolySource<C>) -> Vec<Polynomial<C::F>> {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            let mut out = Vec::new();
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                out.extend(mul_slotwise(&a_elem, &b_elem));
            }
            out
        }
        (ATyp::Vec(_, na), _) => {
            let mut out = Vec::new();
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                out.extend(mul_slotwise(&a_elem, b));
            }
            out
        }
        (_, ATyp::Vec(_, nb)) => {
            let mut out = Vec::new();
            for i in 0..*nb {
                let b_elem = b.at_index(i).unwrap();
                out.extend(mul_slotwise(a, &b_elem));
            }
            out
        }
        _ => a
            .polys()
            .iter()
            .zip(b.polys())
            .map(|(a, b)| a * b)
            .collect(),
    }
}

/// Fast path for dot products over non-polynomial types (scalar / group /
/// bool at any nesting depth). Computes `Σ_i a[i]·b[i]` per slot directly
/// as polynomial arithmetic, without allocating sentinel accumulator vars.
///
/// The element operation is always `mul` (element-wise with broadcasting),
/// not `dot`. Only the outer Vec dimension is summed.
fn dot_slotwise<C: ArkConfig>(
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
) -> Vec<Polynomial<C::F>> {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(inner_a, na), ATyp::Vec(inner_b, nb)) if na == nb => {
            let elem_typ = ATyp::lub_mul(&**inner_a, &**inner_b, &Nothing)
                .expect("dot_slotwise: lub_mul on element types");
            let mut acc = vec![Polynomial::<C::F>::zero(); elem_typ.physical_len()];
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                let products = mul_slotwise(&a_elem, &b_elem);
                for (j, slot) in acc.iter_mut().enumerate() {
                    *slot = &*slot + &products[j];
                }
            }
            acc
        }
        _ => {
            // Unreachable: CTyp::lub_dot only allows Vec×Vec, so the type
            // checker never produces a Dot op with non-Vec operands.
            super::uncovered_op("dot-non-vec", var);
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
        (ATyp::Vec(inner_a, na), ATyp::Vec(inner_b, nb)) if na == nb => {
            let mul_typ = ATyp::lub_mul(&**inner_a, &**inner_b, &Nothing)
                .expect("dot_op: lub_mul on element types");
            let add_typ =
                ATyp::lub_add(&mul_typ, &mul_typ, &Nothing).expect("dot_op: lub_add on mul type");
            assert_eq!(
                mul_typ, add_typ,
                "dot_op: lub_add must not change mul type — got mul={:?}, add={:?}",
                mul_typ, add_typ,
            );
            assert_eq!(
                add_typ, var.typ,
                "dot_op: type mismatch — lub_add(lub_mul({:?}, {:?})) = {:?}, but result type is {:?}",
                **inner_a, **inner_b, add_typ, var.typ,
            );

            let acc = if !has_poly_type(&var.typ) {
                dot_slotwise(var, a, b)
            } else {
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
                acc
            };

            link_to_polys(ctx.ideal, var, acc);
        }
        _ => {
            // Unreachable: CTyp::lub_dot only allows Vec×Vec, so the type
            // checker never produces a Dot op with non-Vec operands.
            super::uncovered_op("dot-non-vec", var);
        }
    }
}
#[cfg(test)]
mod tests {
    use super::super::{Ideal, IdealBuilder};

    use crate::frontend::Polynomial;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::op::mk;
    use graph::Op;

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

    /// Fast path: Vec(Scalar,3)·Vec(Scalar,3) → Scalar should produce the
    /// exact polynomial `a[0]*b[0] + a[1]*b[1] + a[2]*b[2]` and emit only
    /// 1 linking row (no `dot_acc` sentinel vars).
    #[test]
    fn test_dot_vec_scalar_fast_path_no_sentinels() {
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

        let before = ideal.generating_set.len();
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

        // Fast path: only 1 linking row (link_to_polys for the result).
        // Slow path would emit 3 sentinel linking rows + 1 final = 4.
        assert_eq!(
            ideal.generating_set.len() - before,
            1,
            "scalar dot fast path should emit exactly 1 linking row (no sentinels)"
        );

        // Verify the actual polynomial value.
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let a0 = var_a.clone().with_index(0).unwrap();
        let a1 = var_a.clone().with_index(1).unwrap();
        let a2 = var_a.clone().with_index(2).unwrap();
        let b0 = var_b.clone().with_index(0).unwrap();
        let b1 = var_b.clone().with_index(1).unwrap();
        let b2 = var_b.clone().with_index(2).unwrap();
        let expected = &(&var_poly(&a0) * &var_poly(&b0))
            + &(&var_poly(&a1) * &var_poly(&b1))
            + (&var_poly(&a2) * &var_poly(&b2));
        assert_eq!(
            ideal.pl.get(&var_r).unwrap(),
            &expected,
            "dot product polynomial mismatch"
        );
    }

    /// Fast path with nested vectors: Vec(Vec(Scalar,2),2)·Vec(Vec(Scalar,2),2)
    /// → Vec(Scalar,2). All slots populated, no sentinels.
    #[test]
    fn test_dot_nested_vec_scalar_fast_path() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s2 = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_vec_s2 = ATyp::Vec(Box::new(vec_s2.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_vec_s2.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_vec_s2.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_s2.clone(), Qualifier::Private);
        ideal.register(&var_r);

        let before = ideal.generating_set.len();
        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_vec_s2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_vec_s2.clone(),
                )),
                vec_s2.clone(),
            ),
            &mut ideal,
        );

        // 2 slots in result → 2 linking rows, no sentinels.
        assert_eq!(
            ideal.generating_set.len() - before,
            2,
            "nested vec-of-scalar dot fast path should emit 2 linking rows (no sentinels)"
        );

        for j in 0..2 {
            let slot = var_r.clone().with_index(j).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "nested vec dot result slot {j} missing from pl"
            );
        }
    }

    /// Type-mismatch: Vec(Scalar,2)·Vec(Scalar,2) with result type Bool
    /// should panic because lub_add(lub_mul(Scalar, Scalar)) = Scalar ≠ Bool.
    #[test]
    #[should_panic(expected = "dot_op: type mismatch")]
    fn test_dot_type_mismatch_panics() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let unit_typ = ATyp::unit();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), unit_typ.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_s.clone())),
                unit_typ.clone(),
            ),
            &mut ideal,
        );
    }

    /// dot(Vec(Vec(Scalar,2),1), Vec(Scalar,1)) — mismatched element types
    /// (Vec(Scalar,2) vs Scalar) where lub_dot allows the combination via
    /// lub_mul broadcasting. The Vec×Vec arm recurses into dot_op_inner,
    /// which falls through to the leaf arm (mul_op_inner) for the
    /// broadcast multiply. All 2 result slots must be populated.
    #[test]
    fn test_dot_mismatched_elem_types_broadcasts_via_leaf() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s2 = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_vec_s2_1 = ATyp::Vec(Box::new(vec_s2.clone()), 1);
        let vec_s1 = ATyp::Vec(Box::new(s.clone()), 1);
        // lub_dot(Vec(Vec(Scalar,2),1), Vec(Scalar,1))
        //   = lub_mul(Vec(Scalar,2), Scalar) = Vec(Scalar,2)
        let result_typ = ATyp::Vec(Box::new(s.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_vec_s2_1.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_s1.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), result_typ.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Dot,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_vec_s2_1.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_s1.clone())),
                result_typ.clone(),
            ),
            &mut ideal,
        );

        // Result type Vec(Scalar,2) has 2 physical slots.
        for j in 0..2 {
            let slot = var_r.clone().with_index(j).unwrap();
            assert!(
                ideal.pl.contains(&slot),
                "dot mismatched-elem slot {j} missing from pl"
            );
        }
    }
}
