//! Check op encoder: `check_op` and `check_op_inner`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;

use super::EncodeCtx;
use super::Ideal;
use super::PolySource;

/// Slot-wise binary operation with type-aware broadcasting.
///
/// Handles all type combinations that the lub functions permit:
/// - `Scalar op Scalar` → single slot
/// - `Vec(T,n) op Vec(T,n)` → element-wise recursion
/// - `Vec(T,n) op Scalar` / `Scalar op Vec(T,n)` → broadcast scalar to each element
/// - `Poly op Scalar` / `Scalar op Poly` → broadcast scalar to each coefficient
/// - `Uni(n1) op Uni(n2)` → zero-pad shorter operand to match ideal degree
/// - Same-type poly op → straightforward slot-wise
pub fn check_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    _pr: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    check_op_inner(&a_src, &b_src, ctx.ideal);
    // NOTE: We do NOT emit `var.slots()` as basis polynomials here.
    // `==` is used as an assertion, not to compute the boolean
    // ideal of equality checking.
}

fn check_op_inner<C: ArkConfig>(a: &PolySource<C>, b: &PolySource<C>, ideal: &mut Ideal<C>) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            for i in 0..*na {
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                check_op_inner(&a_elem, &b_elem, ideal);
            }
        }
        _ => {
            let lub = ATyp::lub_equ(a.typ(), b.typ(), &Nothing).expect("check_op: lub_equ failed");
            let a_lifted = a.lift_to(&lub);
            let b_lifted = b.lift_to(&lub);
            for j in 0..lub.physical_len() {
                let diff = &a_lifted.polys[j] - &b_lifted.polys[j];
                ideal.generating_set.push(diff);
            }
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
    use graph::{Op, Ref};

    #[test]
    fn test_equ_vec_uni_different_degrees() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let uni2 = ATyp::Uni(2);
        let uni4 = ATyp::Uni(4);
        let vec_uni2 = ATyp::Vec(Box::new(uni2.clone()), 2);
        let vec_uni4 = ATyp::Vec(Box::new(uni4.clone()), 2);
        let unit_typ = ATyp::unit();

        let var_a = Var::from_node(NodeIndex::new(0), vec_uni2.clone(), Qualifier::Private);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_uni4.clone(), Qualifier::Private);
        ideal.register(&var_b);

        let var_r = Var::from_node(NodeIndex::new(2), unit_typ.clone(), Qualifier::Private);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Check(
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(0)),
                    vec_uni2.clone(),
                )),
                mk::<ArkBls12_381>(Op::Ref(
                    graph::Ref::new(NodeIndex::new(1)),
                    vec_uni4.clone(),
                )),
            ),
            &mut ideal,
        );

        assert!(
            !ideal.generating_set.is_empty(),
            "Vec(Uni(2),2) == Vec(Uni(4),2) should produce basis constraints (zero-padded per element)"
        );
    }

    #[test]
    fn test_equ_scalar_has_var_constraint_and_diff() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_b);
        let var_r = Var::from_node(NodeIndex::new(2), ATyp::unit(), Qualifier::Private);

        builder.add_op(
            var_r.clone(),
            Op::Check(
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
            ),
            &mut ideal,
        );

        let a_slot = var_a.with_index(0).unwrap();
        let b_slot = var_b.with_index(0).unwrap();
        let r_slot = var_r.with_index(0).unwrap();
        let diff = &Polynomial::var(&a_slot) - &Polynomial::var(&b_slot);
        assert!(
            ideal.generating_set.contains(&diff),
            "basis should contain a-b diff"
        );
        assert!(
            !ideal
                .generating_set
                .iter()
                .any(|p| *p == Polynomial::var(&r_slot)),
            "basis should NOT contain var_poly(r) for Unit ideal (== is an assertion, not a computation)"
        );
    }

    #[test]
    fn test_equ_uni_unit_ideal_bare_diffs() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var_b);
        let var_r = Var::from_node(NodeIndex::new(2), ATyp::unit(), Qualifier::Private);

        builder.add_op(
            var_r.clone(),
            Op::Check(
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(2))),
            ),
            &mut ideal,
        );

        let r_slot = var_r.with_index(0).unwrap();

        assert!(
            !ideal
                .generating_set
                .iter()
                .any(|p| *p == Polynomial::var(&r_slot)),
            "basis should NOT contain var_poly(r) for Unit ideal"
        );

        for j in 0..3 {
            let a_j = var_a.clone().with_index(j).unwrap();
            let b_j = var_b.clone().with_index(j).unwrap();
            let diff = &Polynomial::var(&a_j) - &Polynomial::var(&b_j);
            assert!(
                ideal.generating_set.contains(&diff),
                "basis should contain a[{}]-b[{}] diff",
                j,
                j
            );
        }

        assert!(
            !ideal.pl.contains(&r_slot),
            "Unit ideal slot should NOT be defined via pl"
        );
    }

    #[test]
    fn test_equ_uni_different_degrees_lifts_both() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(4), Qualifier::Private);
        ideal.register(&var_b);
        let var_r = Var::from_node(NodeIndex::new(2), ATyp::unit(), Qualifier::Private);

        builder.add_op(
            var_r.clone(),
            Op::Check(
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(4))),
            ),
            &mut ideal,
        );

        let r_slot = var_r.with_index(0).unwrap();
        assert!(
            !ideal
                .generating_set
                .iter()
                .any(|p| *p == Polynomial::var(&r_slot)),
            "basis should NOT contain var_poly(r) for Unit ideal"
        );

        let lub_len = ATyp::Uni(4).physical_len();
        assert_eq!(lub_len, 5);
        for j in 0..lub_len {
            let a_j = if j < 3 {
                Polynomial::var(&var_a.clone().with_index(j).unwrap())
            } else {
                Polynomial::zero()
            };
            let b_j = Polynomial::var(&var_b.clone().with_index(j).unwrap());
            let diff = a_j - b_j;
            assert!(
                ideal.generating_set.contains(&diff),
                "basis should contain lifted diff at slot {}",
                j
            );
        }
    }
}
