//! Concatenation op encoder: `concat_op`, `bind_lifted_alias`, `bind_vec_aliases`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;

use crate::Var;

use super::EncodeCtx;
use super::Ideal;
use super::PolySource;
use super::link_to_polys;

/// Bind `target`'s slots to `source`'s polys lifted to `target_typ`.
pub fn bind_lifted_alias<C: ArkConfig>(
    target: &Var,
    source: &PolySource<C>,
    target_typ: &ATyp,
    ideal: &mut Ideal<C>,
) {
    let lifted = source.lift_to(target_typ);
    link_to_polys(ideal, target, lifted.polys);
}

/// Bind a range of `target`'s element slots to `source`'s elements.
pub fn bind_vec_aliases<C: ArkConfig>(
    target: &Var,
    target_offset: usize,
    source: &PolySource<C>,
    source_len: usize,
    elem_typ: &ATyp,
    ideal: &mut Ideal<C>,
) {
    for source_index in 0..source_len {
        let target_elem = target.with_index(target_offset + source_index).unwrap();
        let source_elem = source.at_index(source_index).unwrap();
        bind_lifted_alias(&target_elem, &source_elem, elem_typ, ideal);
    }
}

pub fn concat_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    _a_op: &HOp<C>,
    _b_op: &HOp<C>,
) {
    match (&var.typ, a.typ(), b.typ()) {
        (ATyp::Vec(r_elem, _), ATyp::Vec(_, na), ATyp::Vec(_, nb)) => {
            bind_vec_aliases(var, 0, a, *na, r_elem, ctx.ideal);
            bind_vec_aliases(var, *na, b, *nb, r_elem, ctx.ideal);
        }
        (ATyp::Vec(r_elem, _), ATyp::Vec(_, na), _) => {
            bind_vec_aliases(var, 0, a, *na, r_elem, ctx.ideal);
            let target_elem = var.with_index(*na).unwrap();
            bind_lifted_alias(&target_elem, b, r_elem, ctx.ideal);
        }
        (ATyp::Vec(r_elem, _), _, ATyp::Vec(_, nb)) => {
            let target_elem = var.with_index(0).unwrap();
            bind_lifted_alias(&target_elem, a, r_elem, ctx.ideal);
            bind_vec_aliases(var, 1, b, *nb, r_elem, ctx.ideal);
        }
        _ => {
            panic!(
                "ideal: operation has no polynomial-ideal treatment at concat-non-vector for {}",
                var.verbose()
            );
        }
    }
}

#[cfg(test)]
mod tests {

    use super::super::{Ideal, IdealBuilder};

    use backend::ArkBls12_381;

    use backend::ATyp;
    use backend::op::mk;
    use graph::{Op, Ref};

    #[test]
    fn test_concat_vec_uni_different_degrees() {
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
        let vec_ideal = ATyp::Vec(Box::new(uni4.clone()), 4);

        let var_a = Var::from_node(NodeIndex::new(0), vec_uni2.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_uni4.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(
            var_r.typ.physical_len(),
            20,
            "Vec(Uni(4), 4) has 4*5=20 slots"
        );
        for i in 0..4 {
            let elem = var_r.with_index(i).unwrap();
            for j in 0..5 {
                let slot = elem.with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Concat ideal element {} slot {} missing from pl",
                    i,
                    j
                );
            }
        }
    }

    #[test]
    fn test_concat_vec_scalar_element() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec_s = ATyp::Vec(Box::new(s.clone()), 2);
        let vec_ideal = ATyp::Vec(Box::new(s.clone()), 3);

        let var_a = Var::from_node(NodeIndex::new(0), vec_s.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), vec_ideal.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_s.clone())),
                mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
                vec_ideal.clone(),
            ),
            &mut ideal,
        );

        assert_eq!(var_r.typ.physical_len(), 3, "Vec(Scalar, 3) has 3 slots");
        for i in 0..3 {
            let elem = var_r.with_index(i).unwrap();
            assert!(
                ideal.pl.contains(&elem),
                "Concat Vec++Scalar ideal element {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_concat_vec_vec_elements() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let vec2 = ATyp::Vec(Box::new(s.clone()), 2);
        let vec3 = ATyp::Vec(Box::new(s.clone()), 3);
        let vec5 = ATyp::Vec(Box::new(s.clone()), 5);

        let var_a = Var::from_node(NodeIndex::new(0), vec2.clone(), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), vec3.clone(), Qualifier::Private);
        ideal.register(&var_b);
        let var_r = Var::from_node(NodeIndex::new(2), vec5.clone(), Qualifier::Private);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Concat,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec2)),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec3)),
                vec5,
            ),
            &mut ideal,
        );

        for i in 0..5 {
            let pr_i = var_r.with_index(i).unwrap();
            let pr_slot = pr_i.with_index(0).unwrap();
            assert!(
                ideal.pl.contains(&pr_slot),
                "concat ideal element {} slot 0 should be in pl",
                i
            );
        }
    }
}
