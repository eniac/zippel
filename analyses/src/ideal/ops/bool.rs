//! Bool op encoder: `BinOp::Equ` in computation context (`let b = x == y`).

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::HOp;
use lang::typ::Nothing;
use lang::typ::lub::Lub;

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;

/// Encode `let b = x == y` as polynomial constraints using the standard
/// bool encoding.
///
/// For each scalar slot `j` of the LUB type of `x` and `y`:
///   d_j = x_j - y_j
///   d_j * inv_j + b_j - 1 = 0    (inv_j is a fresh sentinel var)
///   d_j * b_j = 0
///
/// This connects `b` to `x` and `y` in the ideal, so that `assert(b)`
/// (which adds `b - 1 = 0`) lets the GB solver reduce back to
/// `x_j - y_j = 0` via:
///   b_j = 1  (from assert)
///   d_j * b_j = 0  →  d_j = 0  →  x_j - y_j = 0
///
/// For `Vec<Bool, N>` results, the encoding is applied element-wise.
pub fn equ_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    equ_op_inner(ctx, var, &a_src, &b_src);
}

/// Recursively encode `==` as bool constraints. Dispatches on the result
/// type: `Bool` is the base case (scalar bool encoding), `Vec<Bool, N>`
/// recurses element-wise (handles nested vectors like `Vec<Vec<Bool, M>, N>`).
fn equ_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a_src: &PolySource<C>,
    b_src: &PolySource<C>,
) {
    match &var.typ {
        ATyp::Base(ABase::Bool) => {
            equ_leaf(ctx, var, a_src, b_src);
        }
        ATyp::Vec(_, n) => {
            for i in 0..*n {
                let var_i = var.clone().with_index(i).unwrap();
                let a_elem = a_src.at_index(i).unwrap();
                let b_elem = b_src.at_index(i).unwrap();
                equ_op_inner(ctx, &var_i, &a_elem, &b_elem);
            }
        }
        _ => {
            panic!(
                "equ_op: unexpected result type {} (expected Bool or Vec<Bool>)",
                var.typ
            );
        }
    }
}

/// Emit the standard bool encoding for a single Bool slot `b` comparing
/// two operands. Each coefficient slot `j` of the LUB type contributes:
///   d_j = a_j - b_j          (inlined)
///   d_j * b = 0              (b=1 → d_j=0)
///
/// Plus a single aggregate constraint with one witness `inv_j` per slot:
///   Σ_j d_j * inv_j + b - 1 = 0
///
/// This gives: b=1 iff all d_j=0 (i.e. a == b). When all d_j=0, the
/// aggregate forces b=1. When some d_k≠0, set inv_k=1/d_k (others 0)
/// to satisfy the aggregate with b=0.
fn equ_leaf<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    a_src: &PolySource<C>,
    b_src: &PolySource<C>,
) {
    let lub = ATyp::lub_equ(a_src.typ(), b_src.typ(), &Nothing).expect("equ_op: lub_equ failed");
    let a_lifted = a_src.lift_to(&lub);
    let b_lifted = b_src.lift_to(&lub);
    let b_poly = Polynomial::var(var);
    let one = Polynomial::lit(&C::FOps::one());

    // d_j = a_j - b_j for each slot
    let diffs: Vec<Polynomial<C::F>> = a_lifted
        .polys
        .iter()
        .zip(&b_lifted.polys)
        .map(|(a, b)| a - b)
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
        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), operand_typ.clone(), Qualifier::Instance);
        ideal.register(&var_a);
        let var_c = Var::from_node(NodeIndex::new(1), operand_typ.clone(), Qualifier::Instance);
        ideal.register(&var_c);

        let var_b = Var::from_node(
            NodeIndex::new(2),
            ATyp::Base(backend::ABase::Bool),
            Qualifier::Witness,
        );
        ideal.register(&var_b);

        let a_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), operand_typ.clone()));
        let c_op = mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), operand_typ));
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
}
