//! Bilinear-pairing op encoder: `pair_op`, `pair_op_inner`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;

use crate::Var;
use crate::frontend::Polynomial;

use super::PolySource;
use super::{EncodeCtx, link_to_polys};

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
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                let t_i = var.with_index(i).unwrap();
                pair_op_inner(ctx, &t_i, &a_elem, &b_elem);
            }
        }
        (ATyp::Vec(_, na), _) => {
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let t_i = var.with_index(i).unwrap();
                pair_op_inner(ctx, &t_i, &a_elem, b);
            }
        }
        (_, ATyp::Vec(_, nb)) => {
            for i in 0..*nb {
                let b_elem = b.at_index(i).unwrap();
                let t_i = var.with_index(i).unwrap();
                pair_op_inner(ctx, &t_i, a, &b_elem);
            }
        }
        _ => {
            let a_lifted = a.lift_to(&var.typ);
            let b_lifted = b.lift_to(&var.typ);
            let es: Vec<Polynomial<C::F>> = a_lifted
                .polys()
                .iter()
                .zip(b_lifted.polys())
                .map(|(a, b)| a * b)
                .collect();
            link_to_polys(ctx.ideal, var, es);
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

    /// Pair with exact polynomial verification: `pair(G1, G2) → GT` should
    /// bind `pl[r] = var(a) * var(b)`.
    #[test]
    fn test_pair_scalar_exact_poly() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let g1 = ATyp::g1();
        let g2 = ATyp::g2();
        let gt = ATyp::gt();

        let var_a = Var::from_node(NodeIndex::new(0), g1.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), g2.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), gt.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), g1.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), g2.clone())),
                gt.clone(),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let a_slot = var_a.clone();
        let b_slot = var_b.clone();
        let expected = &var_poly(&a_slot) * &var_poly(&b_slot);
        assert_eq!(
            ideal.pl.get(&var_r).unwrap(),
            &expected,
            "pair(G1, G2) should bind pl[r] = var(a) * var(b)"
        );
    }

    /// Nested Vec pair: `pair(Vec(Vec(G1,2),2), Vec(Vec(G2,2),2)) → Vec(Vec(GT,2),2)`.
    /// All 4 leaf GT slots must be populated with the correct `var(a[i][j]) * var(b[i][j])`.
    #[test]
    fn test_pair_nested_vec_exact_poly() {
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
        let vec_vec_g1 = ATyp::Vec(Box::new(vec_g1.clone()), 2);
        let vec_vec_g2 = ATyp::Vec(Box::new(vec_g2.clone()), 2);
        let vec_vec_gt = ATyp::Vec(Box::new(vec_gt.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_vec_g1.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_vec_g2.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_vec_gt.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_vec_g1.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_vec_g2.clone(),
                )),
                vec_vec_gt.clone(),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);

        for i in 0..2 {
            for j in 0..2 {
                let a_slot = var_a.clone().with_index(i).unwrap().with_index(j).unwrap();
                let b_slot = var_b.clone().with_index(i).unwrap().with_index(j).unwrap();
                let r_slot = var_r.clone().with_index(i).unwrap().with_index(j).unwrap();
                let expected = &var_poly(&a_slot) * &var_poly(&b_slot);
                assert_eq!(
                    ideal.pl.get(&r_slot).unwrap(),
                    &expected,
                    "nested pair slot [{i}][{j}] mismatch"
                );
            }
        }
    }

    /// `pair(Vec(G1,2), Vec(G2,2))` with exact polynomial verification:
    /// each `pl[r[i]] = var(a[i]) * var(b[i])`.
    #[test]
    fn test_pair_vec_exact_poly() {
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

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        for i in 0..2 {
            let a_slot = var_a.clone().with_index(i).unwrap();
            let b_slot = var_b.clone().with_index(i).unwrap();
            let r_slot = var_r.clone().with_index(i).unwrap();
            let expected = &var_poly(&a_slot) * &var_poly(&b_slot);
            assert_eq!(
                ideal.pl.get(&r_slot).unwrap(),
                &expected,
                "pair vec slot {i} mismatch"
            );
        }
    }

    /// `pair(Vec(G1,2), G2)` — scalar broadcast permitted by `CTyp::lub_pair`.
    /// Each `pl[r[i]] = var(a[i]) * var(b)`.
    #[test]
    fn test_pair_vec_scalar_broadcast_exact_poly() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let g1 = ATyp::g1();
        let g2 = ATyp::g2();
        let gt = ATyp::gt();
        let vec_g1 = ATyp::Vec(Box::new(g1.clone()), 2);
        let vec_gt = ATyp::Vec(Box::new(gt.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), vec_g1.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), g2.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_gt.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_g1.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), g2.clone())),
                vec_gt.clone(),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let b_slot = var_b.clone();
        for i in 0..2 {
            let a_slot = var_a.clone().with_index(i).unwrap();
            let r_slot = var_r.clone().with_index(i).unwrap();
            let expected = &var_poly(&a_slot) * &var_poly(&b_slot);
            assert_eq!(
                ideal.pl.get(&r_slot).unwrap(),
                &expected,
                "pair vec×scalar slot {i} mismatch"
            );
        }
    }

    /// `pair(G1, Vec(G2,2))` — scalar broadcast on the left side.
    /// Each `pl[r[i]] = var(a) * var(b[i])`.
    #[test]
    fn test_pair_scalar_vec_broadcast_exact_poly() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let g1 = ATyp::g1();
        let g2 = ATyp::g2();
        let gt = ATyp::gt();
        let vec_g2 = ATyp::Vec(Box::new(g2.clone()), 2);
        let vec_gt = ATyp::Vec(Box::new(gt.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), g1.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_g2.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_gt.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Pair(
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), g1.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_g2.clone())),
                vec_gt.clone(),
            ),
            &mut ideal,
        );

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let a_slot = var_a.clone();
        for i in 0..2 {
            let b_slot = var_b.clone().with_index(i).unwrap();
            let r_slot = var_r.clone().with_index(i).unwrap();
            let expected = &var_poly(&a_slot) * &var_poly(&b_slot);
            assert_eq!(
                ideal.pl.get(&r_slot).unwrap(),
                &expected,
                "pair scalar×vec slot {i} mismatch"
            );
        }
    }
}
