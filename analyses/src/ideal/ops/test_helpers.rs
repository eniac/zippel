//! Shared test helpers for ops module tests.

#![cfg(test)]

use crate::QualifierPropagation;
use crate::TransClos;
use crate::Var;
use crate::frontend::Polynomial;

use backend::ATyp;
use backend::ArkBls12_381;
use backend::op::mk;

use graph::{Op, Ref, UDags};

use lang::ast::BinOp;

use share::Ctx;
use share::unwrap;

use super::{Ideal, IdealBuilder};

use crate::tests::parse_and_concretize;

#[track_caller]
pub fn trans_clos_from_src(src: &str) -> TransClos<ArkBls12_381> {
    let m = parse_and_concretize(src, &Ctx::new());
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);

    TransClos::verifier(&g)
}

#[track_caller]
pub fn trans_clos_from_src_sized(
    src: &str,
    sizes: &share::Ctx<lang::id::Tid, usize>,
) -> TransClos<ArkBls12_381> {
    let m = parse_and_concretize(src, sizes);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let g = QualifierPropagation::from_dag(&gs[0]);

    TransClos::verifier(&g)
}

pub fn scalar_poly_binop_ideal(
    op: BinOp,
    scalar_left: bool,
    poly_typ: ATyp,
) -> (Var, Var, Var, Ideal<ArkBls12_381>) {
    use lang::typ::Qualifier;
    use petgraph::graph::NodeIndex;

    let mut builder = IdealBuilder::<ArkBls12_381>::new();
    let mut ideal = Ideal::<ArkBls12_381>::new();

    let scalar_typ = ATyp::scalar();
    let var_s = Var::from_node(NodeIndex::new(0), scalar_typ.clone(), Qualifier::Instance);
    ideal.register(&var_s);

    let var_p = Var::from_node(NodeIndex::new(1), poly_typ.clone(), Qualifier::Instance);
    ideal.register(&var_p);

    let var_r = Var::from_node(NodeIndex::new(2), poly_typ.clone(), Qualifier::Instance);
    ideal.register(&var_r);

    let scalar_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), scalar_typ));
    let poly_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), poly_typ.clone()));
    let (left, right) = if scalar_left {
        (scalar_op, poly_op)
    } else {
        (poly_op, scalar_op)
    };

    builder.add_op(
        var_r.clone(),
        Op::Bin(op, left, right, poly_typ),
        &mut ideal,
    );

    (var_s, var_p, var_r, ideal)
}

#[track_caller]
pub fn assert_ideal_slot(
    ideal: &Ideal<ArkBls12_381>,
    var_r: &Var,
    slot: usize,
    expected: Polynomial<ark_bls12_381::Fr>,
) {
    let r_slot = var_r.with_index(slot).unwrap();
    let stored = ideal.pl.get(&r_slot).unwrap();
    assert_eq!(*stored, expected, "ideal slot {slot} mismatch");
}
