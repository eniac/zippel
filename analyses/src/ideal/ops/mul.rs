//! Multiplication op encoder: `mul_op`, `mul_op_inner`, `mul_leaf`.
//!
//! For `Vec<T>` × `Vec<T>`, iterates over logical indices and recurses
//! per element. At the leaf level (non-Vec), dispatches to polynomial
//! convolution (VPoly/Uni/Mle) or slot-wise multiplication (base types).

use std::collections::HashMap;

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::HOp;

use crate::Var;
use crate::frontend::Polynomial;

use super::PolySource;
use super::{EncodeCtx, link_to_polys};
use super::{hypercube, multi_indices};

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
                _ => panic!("mul_op_inner Vec×Vec ideal must be Vec"),
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
                _ => panic!("mul_op_inner Vec×_ ideal must be Vec"),
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
                _ => panic!("mul_op_inner _×Vec ideal must be Vec"),
            };
            for i in 0..*nb {
                let t_i = target.with_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                mul_op_inner(&mut *ctx, &t_i, a, &b_elem, r_inner);
            }
        }
        _ => {
            mul_leaf(ctx, target, a, b, r_typ);
        }
    }
}

/// Leaf-level multiplication for non-Vec operands. Dispatches based on
/// operand types:
///
/// - `poly × Scalar` → scalar multiply (each poly slot × scalar)
/// - `Scalar × poly` → scalar multiply (scalar × each poly slot)
/// - `Mle × Mle` (equal arity) → basis-change convolution (Lagrange → monomial)
/// - `Mle × VPoly` / `VPoly × Mle` (equal arity) → basis-change convolution
/// - `poly × poly` (`Uni`/`VPoly`) → VPoly coefficient convolution
/// - `Base × Base` → slot-wise multiply
/// - otherwise → `uncovered_op`
fn mul_leaf<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
) {
    if matches!(b.typ(), ATyp::Base(ABase::Scalar)) && a.is_poly() {
        let prods: Vec<Polynomial<C::F>> = a.polys().iter().map(|ap| ap * &b.polys()[0]).collect();
        link_to_polys(ctx.ideal, target, prods);
    } else if matches!(a.typ(), ATyp::Base(ABase::Scalar)) && b.is_poly() {
        let prods: Vec<Polynomial<C::F>> = b.polys().iter().map(|bp| &a.polys()[0] * bp).collect();
        link_to_polys(ctx.ideal, target, prods);
    } else if matches!(a.typ(), ATyp::Mle(_)) && matches!(b.typ(), ATyp::Mle(_)) {
        mul_mle_mle(ctx, target, a, b, r_typ);
    } else if matches!(a.typ(), ATyp::Mle(_)) && matches!(b.typ(), ATyp::VPoly(_, _))
        || matches!(a.typ(), ATyp::VPoly(_, _)) && matches!(b.typ(), ATyp::Mle(_))
    {
        mul_mle_vpoly(ctx, target, a, b, r_typ);
    } else if a.is_poly() && b.is_poly() {
        mul_vpoly_vpoly(ctx, target, a, b, r_typ);
    } else if !a.is_poly() && !b.is_poly() {
        let prods: Vec<Polynomial<C::F>> = a
            .polys()
            .iter()
            .zip(b.polys())
            .map(|(ap, bp)| ap * bp)
            .collect();
        link_to_polys(ctx.ideal, target, prods);
    } else {
        super::uncovered_op("mul-mixed-poly-nonpoly", target);
    }
}

/// `Mle(n) × Mle(n) → VPoly(n, 2n)`: basis-change convolution.
///
/// Each evaluation slot of the result is a linear combination of
/// `a_eval[i] · b_eval[j]` weighted by the Lagrange-to-monomial
/// change-of-basis coefficients.
fn mul_mle_mle<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
) {
    let (ATyp::Mle(na), ATyp::Mle(nb)) = (a.typ(), b.typ()) else {
        unreachable!("mul_mle_mle called with non-Mle operands");
    };
    assert_eq!(na, nb, "mul_mle_mle: Mle arity mismatch");
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

/// `Mle(n) × VPoly(n, m) → VPoly(n, m+n)`: basis-change convolution.
///
/// The Mle operand is expanded via Lagrange basis polynomials, then
/// convolved with the VPoly coefficient slots.
fn mul_mle_vpoly<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
) {
    let (mle_src, vpoly_src, na, mb) = match (a.typ(), b.typ()) {
        (ATyp::Mle(n), ATyp::VPoly(_, m)) => (a, b, n, m),
        (ATyp::VPoly(_, m), ATyp::Mle(n)) => (b, a, n, m),
        _ => unreachable!("mul_mle_vpoly called with wrong operand types"),
    };
    let ATyp::VPoly(nr, mr) = r_typ else {
        panic!("Mul Mle×VPoly ideal must be VPoly");
    };
    assert!(
        *nr == *na && *mr == *mb + *na,
        "Mul Mle({})×VPoly(_, {}) ideal must be VPoly({}, {}), got VPoly({}, {})",
        na,
        mb,
        na,
        *mb + *na,
        nr,
        mr
    );
    let n = *na;
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

/// `VPoly × VPoly` (including `Uni` as `VPoly(1, m)`): coefficient convolution.
///
/// Normalizes `Uni` to `VPoly(1, m)`, then convolves the multi-index
/// coefficient slots element-wise.
fn mul_vpoly_vpoly<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    r_typ: &ATyp,
) {
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
        (ATyp::VPoly(na, ma), ATyp::VPoly(nb, mb), ATyp::VPoly(nr, mr)) if na == nb && na == nr => {
            let a_idx = multi_indices(*na, *ma);
            let b_idx = multi_indices(*nb, *mb);
            let r_idx = multi_indices(*nr, *mr);
            let r_pos: HashMap<&Vec<usize>, usize> =
                r_idx.iter().enumerate().map(|(i, k)| (k, i)).collect();
            let mut out: Vec<Polynomial<C::F>> = vec![Polynomial::<C::F>::zero(); r_idx.len()];
            for (ia, ka) in a_idx.iter().enumerate() {
                for (ib, kb) in b_idx.iter().enumerate() {
                    let k: Vec<usize> = ka.iter().zip(kb.iter()).map(|(x, y)| x + y).collect();
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

#[cfg(test)]
mod tests {
    use super::super::multi_indices;
    use super::super::{Ideal, IdealBuilder};

    use crate::frontend::Polynomial;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::op::mk;
    use graph::{GOp, Op};

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
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 1), Qualifier::Witness);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Witness);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 2), Qualifier::Witness);
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
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 1), Qualifier::Witness);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 1), Qualifier::Witness);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 2), Qualifier::Witness);
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
        let var_u = Var::from_node(NodeIndex::new(0), ATyp::Mle(1), Qualifier::Witness);
        ideal.register(&var_u);
        let var_v = Var::from_node(NodeIndex::new(1), ATyp::Mle(1), Qualifier::Witness);
        ideal.register(&var_v);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 2), Qualifier::Witness);
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
        let var_u = Var::from_node(NodeIndex::new(0), ATyp::Mle(1), Qualifier::Witness);
        ideal.register(&var_u);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Witness);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 2), Qualifier::Witness);
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
        let var_b = Var::from_node(NodeIndex::new(0), ATyp::VPoly(2, 1), Qualifier::Witness);
        ideal.register(&var_b);
        let var_u = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Witness);
        ideal.register(&var_u);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 3), Qualifier::Witness);
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
        let var_u = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Witness);
        ideal.register(&var_u);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(2, 1), Qualifier::Witness);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(2, 3), Qualifier::Witness);
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
    fn test_mul_scalar_poly_broadcast() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);

        let var_s = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Instance);
        ideal.register(&var_s);

        let var_p = Var::from_node(NodeIndex::new(1), uni2.clone(), Qualifier::Instance);
        ideal.register(&var_p);

        let var_r = Var::from_node(NodeIndex::new(2), uni2.clone(), Qualifier::Instance);
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

        let var_v = Var::from_node(NodeIndex::new(0), v3.clone(), Qualifier::Instance);
        ideal.register(&var_v);

        let var_s = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Instance);
        ideal.register(&var_s);

        let var_r = Var::from_node(NodeIndex::new(2), v3.clone(), Qualifier::Instance);
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

    /// `Vec(VPoly(1,1),2) * VPoly(1,1)` — Vec<Poly> times a bare Poly.
    /// Each element recurses into the leaf poly×poly convolution arm.
    #[test]
    fn test_mul_vec_vpoly_by_vpoly() {
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_a = ATyp::VPoly(1, 1);
        let vec_a = ATyp::Vec(Box::new(elem_a.clone()), 2);
        let b_t = ATyp::VPoly(1, 1);

        let var_a = Var::from_node(NodeIndex::new(0), vec_a.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), b_t.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        // lub_mul(Vec(VPoly(1,1),2), VPoly(1,1))
        //   = Vec(lub_mul(VPoly(1,1), VPoly(1,1)), 2)
        //   = Vec(VPoly(1,2), 2)
        let result_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_a.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), b_t.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        // All result slots populated (2 elements × 3 slots per VPoly(1,2) = 6).
        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Vec(VPoly)*VPoly element {i} slot {j} missing from pl"
                );
            }
        }
    }

    /// `VPoly(1,1) * Vec(VPoly(1,1),2)` — bare Poly times Vec<Poly>.
    /// The poly broadcasts across vector elements.
    #[test]
    fn test_mul_vpoly_by_vec_vpoly() {
        use crate::Var;
        use backend::op::mk;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let a_t = ATyp::VPoly(1, 1);
        let elem_b = ATyp::VPoly(1, 1);
        let vec_b = ATyp::Vec(Box::new(elem_b.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), a_t.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_b.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        // lub_mul(VPoly(1,1), Vec(VPoly(1,1),2))
        //   = Vec(lub_mul(VPoly(1,1), VPoly(1,1)), 2)
        //   = Vec(VPoly(1,2), 2)
        let result_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Mul,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), a_t.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_b.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "VPoly*Vec(VPoly) element {i} slot {j} missing from pl"
                );
            }
        }
    }
}
