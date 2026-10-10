//! Bool op encoder: `BinOp::Equ` in computation context (`let b = x == y`).

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::HOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;
use crate::ideal::Check;

use super::EncodeCtx;
use super::PolySource;

/// Encode `let b = x == y` as polynomial constraints using the standard
/// bool encoding.
///
/// `b` is a single `Bool` for every operand shape, vectors included, and
/// each scalar slot `j` of the LUB type of `x` and `y` contributes
/// `d_j = x_j - y_j` (inlined) and:
///   d_j * b = 0              (b=1 → d_j=0)
///
/// Plus a single aggregate constraint with one fresh sentinel `inv_j` per
/// slot:
///   Σ_j d_j * inv_j + b - 1 = 0
///
/// This gives: b=1 iff all d_j=0 (i.e. x == y). When all d_j=0, the
/// aggregate forces b=1. When some d_k≠0, set inv_k=1/d_k (others 0)
/// to satisfy the aggregate with b=0.
///
/// This connects `b` to `x` and `y` in the ideal, so that asserting `b`
/// (the `where` clause or a `verify`, which adds `b - 1 = 0`) lets the GB
/// solver reduce back to `x_j - y_j = 0` via:
///   b = 1  (asserted)
///   d_j * b = 0  →  d_j = 0  →  x_j - y_j = 0
pub fn equ_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    x: &HOp<C>,
    y: &HOp<C>,
) {
    assert!(
        matches!(var.typ, ATyp::Base(ABase::Bool)),
        "equ_op: unexpected result type {} (expected Bool)",
        var.typ
    );
    let x_src = PolySource::from_ref_vars(&ctx.ideal.vars, x);
    let y_src = PolySource::from_ref_vars(&ctx.ideal.vars, y);
    let b_poly = Polynomial::var(var);
    let one = Polynomial::lit(&C::FOps::one());

    // d_j = x_j - y_j for each slot
    let diffs: Vec<Polynomial<C::F>> = sides(&x_src, &y_src)
        .iter()
        .map(|s| &s.lhs - &s.rhs)
        .collect();

    // d_j * b = 0 for each slot (b=1 → all d_j=0)
    for d in &diffs {
        ctx.ideal.generating_set.push(d * &b_poly);
    }

    // Σ_j d_j * inv_j + b - 1 = 0 (all d_j=0 → b=1; some d_j≠0 → b=0)
    let mut aggregate = &b_poly - &one;
    for d in &diffs {
        let inv_name = ctx.builder.ns.next_name("equ_inv");
        let inv_var = ctx.sentinel_var(&inv_name, ATyp::scalar());
        let inv_poly = Polynomial::var(&inv_var);
        aggregate = &aggregate + &(d * &inv_poly);
    }
    ctx.ideal.generating_set.push(aggregate);
}

/// The two sides `x_j == y_j` of each coefficient slot `j` of the LUB type of
/// `x` and `y`: `x == y` holds exactly when every slot's sides are equal.
pub(super) fn sides<C: ArkConfig + HasOpFactory>(
    x_src: &PolySource<C>,
    y_src: &PolySource<C>,
) -> Vec<Check<C::F>> {
    let lub = ATyp::lub_equ(x_src.typ(), y_src.typ(), &Nothing).expect("equ_op: lub_equ failed");
    let x_lifted = x_src.lift_to(&lub);
    let y_lifted = y_src.lift_to(&lub);
    x_lifted
        .polys
        .into_iter()
        .zip(y_lifted.polys)
        .map(|(lhs, rhs)| Check { lhs, rhs })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::{Ideal, IdealBuilder};

    use crate::Var;
    use crate::frontend::Polynomial;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::op::mk;
    use graph::{GOp, Op, Ref};
    use lang::ast::BinOp;
    use lang::typ::Qualifier;
    use petgraph::graph::NodeIndex;

    type Fr = ark_bls12_381::Fr;
    type Poly = Polynomial<Fr>;

    /// Build an ideal for `let b = a == c` with the given operand type.
    /// Returns (var_a, var_c, var_b, ideal).
    fn equ_ideal(operand_typ: ATyp) -> (Var, Var, Var, Ideal<ArkBls12_381>) {
        equ_ideal_mixed(operand_typ.clone(), operand_typ)
    }

    /// [`equ_ideal`] with separate operand types for `a` and `c`.
    fn equ_ideal_mixed(a_typ: ATyp, c_typ: ATyp) -> (Var, Var, Var, Ideal<ArkBls12_381>) {
        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), a_typ.clone(), Qualifier::Instance);
        ideal.register(&var_a);
        let var_c = Var::from_node(NodeIndex::new(1), c_typ.clone(), Qualifier::Instance);
        ideal.register(&var_c);

        let var_b = Var::from_node(
            NodeIndex::new(2),
            ATyp::Base(backend::ABase::Bool),
            Qualifier::Witness,
        );
        ideal.register(&var_b);

        let a_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), a_typ));
        let c_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), c_typ));
        let op: GOp<ArkBls12_381> =
            Op::Bin(BinOp::Equ, a_op, c_op, ATyp::Base(backend::ABase::Bool));
        builder.add_op(var_b.clone(), op, &mut ideal);

        (var_a, var_c, var_b, ideal)
    }

    /// The expected `d_j * b = 0` constraint for slot `j`:
    ///   (a_j - c_j) * b
    fn expected_db(a_j: &Var, c_j: &Var, b: &Var) -> Poly {
        let d = &Poly::var(a_j) - &Poly::var(c_j);
        &d * &Poly::var(b)
    }

    /// Check that `ideal.generating_set` contains `expected`.
    fn assert_contains(ideal: &Ideal<ArkBls12_381>, expected: &Poly, label: &str) {
        assert!(
            ideal.generating_set.contains(expected),
            "{label}: expected {:?} not found in generating set {:?}",
            expected,
            ideal.generating_set,
        );
    }

    #[test]
    fn test_equ_scalar_single_slot() {
        // Scalar == Scalar: 1 slot.
        //   d_0 * b = 0  where d_0 = a - c
        //   (a - c) * inv_0 + b - 1 = 0
        let (var_a, var_c, var_b, ideal) = equ_ideal(ATyp::scalar());
        assert_eq!(
            ideal.generating_set.len(),
            2,
            "scalar equ should produce 2 constraints"
        );
        assert_contains(&ideal, &expected_db(&var_a, &var_c, &var_b), "d*b");
    }

    #[test]
    fn test_equ_uni1_two_slots() {
        // Uni(1) == Uni(1): 2 coefficient slots.
        //   d_0 * b = 0  where d_0 = a[0] - c[0]
        //   d_1 * b = 0  where d_1 = a[1] - c[1]
        //   d_0*inv_0 + d_1*inv_1 + b - 1 = 0
        let (var_a, var_c, var_b, ideal) = equ_ideal(ATyp::Uni(1));
        assert_eq!(
            ideal.generating_set.len(),
            3,
            "Uni(1) equ should produce 3 constraints"
        );
        let a0 = var_a.clone().with_index(0).unwrap();
        let a1 = var_a.clone().with_index(1).unwrap();
        let c0 = var_c.clone().with_index(0).unwrap();
        let c1 = var_c.clone().with_index(1).unwrap();
        assert_contains(&ideal, &expected_db(&a0, &c0, &var_b), "d_0*b");
        assert_contains(
            &ideal,
            &expected_db(&a1, &c1, &var_b),
            "d_1*b (regression: was missing)",
        );
    }

    #[test]
    fn test_equ_uni2_three_slots() {
        // Uni(2) == Uni(2): 3 coefficient slots.
        let (var_a, var_c, var_b, ideal) = equ_ideal(ATyp::Uni(2));
        assert_eq!(
            ideal.generating_set.len(),
            4,
            "Uni(2) equ should produce 4 constraints"
        );
        for i in 0..3 {
            let ai = var_a.clone().with_index(i).unwrap();
            let ci = var_c.clone().with_index(i).unwrap();
            assert_contains(
                &ideal,
                &expected_db(&ai, &ci, &var_b),
                &format!("d_{i}*b (regression: was only d_0*b)"),
            );
        }
    }

    #[test]
    fn test_equ_vpoly_2_1_three_slots() {
        // VPoly(2,1) == VPoly(2,1): 3 coefficient slots.
        let (var_a, var_c, var_b, ideal) = equ_ideal(ATyp::VPoly(2, 1));
        assert_eq!(
            ideal.generating_set.len(),
            4,
            "VPoly(2,1) equ should produce 4 constraints"
        );
        for i in 0..3 {
            let ai = var_a.clone().with_index(i).unwrap();
            let ci = var_c.clone().with_index(i).unwrap();
            assert_contains(
                &ideal,
                &expected_db(&ai, &ci, &var_b),
                &format!("d_{i}*b (regression: was only d_0*b)"),
            );
        }
    }

    #[test]
    fn test_equ_vec_single_bool() {
        // Vec(F, 3) == Vec(F, 3): one Bool `b` over 3 slots, so
        // d_i * b = 0 for each i plus a single aggregate, not 3 bools.
        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let (var_a, var_c, var_b, ideal) = equ_ideal(vec_t);
        assert_eq!(
            ideal.generating_set.len(),
            4,
            "Vec(F,3) equ should produce 3 slot constraints and 1 aggregate"
        );
        for i in 0..3 {
            let ai = var_a.clone().with_index(i).unwrap();
            let ci = var_c.clone().with_index(i).unwrap();
            assert_contains(&ideal, &expected_db(&ai, &ci, &var_b), &format!("d_{i}*b"));
        }
    }

    #[test]
    fn test_equ_nested_vec_single_bool() {
        // Vec(Vec(F, 2), 2) == Vec(Vec(F, 2), 2): 4 slots under one Bool.
        let row_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let mat_t = ATyp::Vec(Box::new(row_t), 2);
        let (var_a, var_c, var_b, ideal) = equ_ideal(mat_t);
        assert_eq!(ideal.generating_set.len(), 5);
        for i in 0..2 {
            for j in 0..2 {
                let aij = var_a.clone().with_index(i).unwrap().with_index(j).unwrap();
                let cij = var_c.clone().with_index(i).unwrap().with_index(j).unwrap();
                assert_contains(
                    &ideal,
                    &expected_db(&aij, &cij, &var_b),
                    &format!("d_{i}{j}*b"),
                );
            }
        }
    }

    #[test]
    fn test_equ_vec_of_polys_lifts_each_element() {
        // Vec(Uni(1), 2) == Vec(Uni(2), 2): each element of `a` is zero-padded
        // to Uni(2), so every element contributes 3 slots and the padded top
        // coefficient compares 0 against c[i][2].
        let (var_a, var_c, var_b, ideal) = equ_ideal_mixed(
            ATyp::Vec(Box::new(ATyp::Uni(1)), 2),
            ATyp::Vec(Box::new(ATyp::Uni(2)), 2),
        );
        assert_eq!(ideal.generating_set.len(), 7);
        for i in 0..2 {
            let a_i = var_a.clone().with_index(i).unwrap();
            let c_i = var_c.clone().with_index(i).unwrap();
            for j in 0..2 {
                let aij = a_i.clone().with_index(j).unwrap();
                let cij = c_i.clone().with_index(j).unwrap();
                assert_contains(
                    &ideal,
                    &expected_db(&aij, &cij, &var_b),
                    &format!("d_{i}{j}*b"),
                );
            }
            let c_top = c_i.with_index(2).unwrap();
            let padded = &(&Poly::zero() - &Poly::var(&c_top)) * &Poly::var(&var_b);
            assert_contains(&ideal, &padded, &format!("d_{i}2*b"));
        }
    }
}
