//! Interpolation op encoder: `interpolate_op`.

use ark_ff::{Field, One, Zero};

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::{HOp, Op};

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;
use super::lagrange_basis;

/// `Op::Interpolate(points, evals)`: bind `var` to the Lagrange
/// interpolation polynomial through `(points[i], evals[i])`.
///
/// Constant points use precomputed Lagrange basis coefficients.
/// Symbolic points introduce fresh inverse sentinels for non-constant
/// denominators.
///
/// Falls back to opaque if the point values aren't all constant.
pub fn interpolate_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: Var,
    points: &HOp<C>,
    evals: &HOp<C>,
) {
    let evals_polys = PolySource::ref_vars(evals, &ctx.ideal.vars);
    let n = evals_polys.len();

    let xs_polys: Vec<Polynomial<C::F>> = match points.get() {
        Op::Value(v) => PolySource::to_poly_value(v),
        Op::Ref(r, _) => {
            let points_var = ctx.ideal.find_ref(r);
            points_var
                .slots()
                .iter()
                .map(|s| {
                    ctx.ideal.pl.get(s).cloned().unwrap_or_else(|| {
                        panic!(
                            "Interpolate: point slot {} not found in pl — \
                                 points must be materialized before interpolation",
                            s
                        )
                    })
                })
                .collect()
        }
        other => {
            panic!(
                "Interpolate points operand must be Ref or Value; got {:?}",
                std::mem::discriminant(other)
            )
        }
    };

    assert_eq!(
        n,
        xs_polys.len(),
        "Interpolate: points and evals must have same length"
    );

    let all_constant = xs_polys.iter().all(|p| p.is_constant());

    if all_constant {
        let xs: Vec<C::F> = xs_polys.iter().map(|p| p.constant_coeff()).collect();
        for i in 0..xs.len() {
            for j in (i + 1)..xs.len() {
                if xs[i] == xs[j] {
                    super::uncovered_op("duplicate-interpolate-points", &var);
                }
            }
        }
        let lag = lagrange_basis::<C::F>(&xs);
        let pr_slots = var.slots();
        for (k, pf) in pr_slots.iter().enumerate() {
            let mut acc = Polynomial::<C::F>::zero();
            for (i, y_i) in evals_polys.iter().enumerate() {
                if k < lag[i].len() && lag[i][k] != C::F::zero() {
                    let weight = Polynomial::<C::F>::lit(&lag[i][k]);
                    acc += y_i * &weight;
                }
            }
            ctx.ideal.pl.insert(pf, &acc);
            ctx.ideal.generating_set.push(acc - Polynomial::var(pf));
        }
    } else {
        for i in 0..xs_polys.len() {
            for j in (i + 1)..xs_polys.len() {
                let diff = &xs_polys[i] - &xs_polys[j];
                if diff.is_zero() {
                    super::uncovered_op("duplicate-interpolate-points", &var);
                }
            }
        }

        let n_pts = xs_polys.len();
        let mut denom_inverses: Vec<Vec<Option<Var>>> = vec![vec![None; n_pts]; n_pts];
        for i in 0..n_pts {
            for j in 0..n_pts {
                if i == j {
                    continue;
                }
                let diff = &xs_polys[i] - &xs_polys[j];
                if diff.is_constant() {
                    continue;
                }
                let d_name = ctx.builder.ns.next_name("interp_inv");
                let d = ctx.builder.sentinel_var(&d_name, ATyp::scalar(), ctx.ideal);
                ctx.ideal
                    .generating_set
                    .push(Polynomial::var(&d) * diff - Polynomial::<C::F>::lit(&C::F::one()));
                denom_inverses[i][j] = Some(d);
            }
        }

        let pr_slots = var.slots();
        let mut ideal_polys = vec![Polynomial::<C::F>::zero(); pr_slots.len()];

        for (i, y_i) in evals_polys.iter().enumerate() {
            let mut lag_poly = vec![Polynomial::<C::F>::lit(&C::F::one())];

            for (j, xj_poly) in xs_polys.iter().enumerate().take(n_pts) {
                if j == i {
                    continue;
                }
                let neg_xj = xj_poly * &Polynomial::lit(&(-C::F::one()));
                let mut new_lag = vec![Polynomial::<C::F>::zero(); lag_poly.len() + 1];
                for (deg, c) in lag_poly.iter().enumerate() {
                    let shifted = c * &neg_xj;
                    new_lag[deg] = &new_lag[deg] + &shifted;
                    new_lag[deg + 1] = &new_lag[deg + 1] + c;
                }
                lag_poly = new_lag;
            }

            let mut denom_inv = Polynomial::<C::F>::lit(&C::F::one());
            for j in 0..n_pts {
                if j == i {
                    continue;
                }
                let diff = &xs_polys[i] - &xs_polys[j];
                if diff.is_constant() {
                    let c = diff.constant_coeff();
                    denom_inv *= Polynomial::lit(&c.inverse().unwrap());
                } else {
                    let d = denom_inverses[i][j]
                        .as_ref()
                        .expect("d-variable must exist for non-constant diff");
                    denom_inv *= Polynomial::var(d);
                }
            }

            for (k, coeff) in lag_poly.iter().enumerate() {
                let scaled = coeff * &denom_inv;
                ideal_polys[k] = &ideal_polys[k] + &(y_i * &scaled);
            }
        }

        for (pf, poly) in pr_slots.iter().zip(ideal_polys) {
            ctx.ideal.pl.insert(pf, &poly);
            ctx.ideal.generating_set.push(poly - Polynomial::var(pf));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Ideal, IdealBuilder};
    use super::lagrange_basis;

    use crate::frontend::Polynomial;
    use backend::ATyp;
    use backend::ArkBls12_381;
    use backend::Value;
    use backend::op::mk;
    use graph::{GOp, Op};

    #[test]
    fn test_add_op_interpolate_constant_points() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let evals_typ = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let var_evals = Var::from_node(NodeIndex::new(0), evals_typ.clone(), Qualifier::Private);
        ideal.register(&var_evals);

        let points: GOp<ArkBls12_381> =
            Op::Value(Value::VecScalar(vec![Fr::from(0u64), Fr::from(1u64)]));
        let evals: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(0)), evals_typ.clone());

        let ideal_typ = ATyp::uni(2);
        let var_ideal = Var::from_node(NodeIndex::new(1), ideal_typ.clone(), Qualifier::Private);
        ideal.register(&var_ideal);

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(var_ideal.clone(), op, &mut ideal);

        let var_poly = |p: &Var| Polynomial::<Fr>::var(p);

        let r0 = var_ideal.clone().with_index(0).unwrap();
        let r1 = var_ideal.clone().with_index(1).unwrap();
        let r2 = var_ideal.clone().with_index(2).unwrap();

        let y0 = var_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_index(0)
            .unwrap();
        let y1 = var_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_index(0)
            .unwrap();

        let expected_c0 = var_poly(&y0);
        let expected_c1 = -var_poly(&y0) + var_poly(&y1);

        assert_eq!(
            ideal.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0] = var_poly(y0)"
        );
        assert_eq!(
            ideal.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1] = -var_poly(y0) + var_poly(y1)"
        );
        assert_eq!(
            ideal.pl.get(&r2).cloned(),
            Some(Polynomial::<Fr>::zero()),
            "pl[c2] = 0"
        );

        assert!(
            ideal
                .generating_set
                .iter()
                .any(|r| r == &(&expected_c0 - &var_poly(&r0)))
        );
        assert!(
            ideal
                .generating_set
                .iter()
                .any(|r| r == &(&expected_c1 - &var_poly(&r1)))
        );
    }

    #[test]
    fn test_add_op_interpolate_3_constant_points() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let evals_typ = ATyp::Vec(Box::new(ATyp::scalar()), 3);
        let var_evals = Var::from_node(NodeIndex::new(0), evals_typ.clone(), Qualifier::Private);
        ideal.register(&var_evals);

        let points: GOp<ArkBls12_381> = Op::Value(Value::VecScalar(
            [1u64, 2, 3].iter().map(|&x| Fr::from(x)).collect(),
        ));
        let evals: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(0)), evals_typ.clone());

        let ideal_typ = ATyp::uni(3);
        let var_ideal = Var::from_node(NodeIndex::new(1), ideal_typ.clone(), Qualifier::Private);
        ideal.register(&var_ideal);

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(var_ideal.clone(), op, &mut ideal);

        let var_poly = |p: &Var| Polynomial::<Fr>::var(p);

        let r0 = var_ideal.clone().with_index(0).unwrap();
        let r1 = var_ideal.clone().with_index(1).unwrap();
        let r2 = var_ideal.clone().with_index(2).unwrap();
        let r3 = var_ideal.clone().with_index(3).unwrap();

        let y0 = var_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_index(0)
            .unwrap();
        let y1 = var_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_index(0)
            .unwrap();
        let y2 = var_evals
            .clone()
            .with_index(2)
            .unwrap()
            .with_index(0)
            .unwrap();

        let lag = lagrange_basis::<Fr>(&[Fr::from(1u64), Fr::from(2u64), Fr::from(3u64)]);

        let expected_c0 = &(&var_poly(&y0) * &Polynomial::lit(&lag[0][0]))
            + &(&(&var_poly(&y1) * &Polynomial::lit(&lag[1][0]))
                + &(&var_poly(&y2) * &Polynomial::lit(&lag[2][0])));
        let expected_c1 = &(&var_poly(&y0) * &Polynomial::lit(&lag[0][1]))
            + &(&(&var_poly(&y1) * &Polynomial::lit(&lag[1][1]))
                + &(&var_poly(&y2) * &Polynomial::lit(&lag[2][1])));
        let expected_c2 = &(&var_poly(&y0) * &Polynomial::lit(&lag[0][2]))
            + &(&(&var_poly(&y1) * &Polynomial::lit(&lag[1][2]))
                + &(&var_poly(&y2) * &Polynomial::lit(&lag[2][2])));

        assert_eq!(
            ideal.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0]"
        );
        assert_eq!(
            ideal.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1]"
        );
        assert_eq!(
            ideal.pl.get(&r2).cloned(),
            Some(expected_c2.clone()),
            "pl[c2]"
        );
        assert_eq!(
            ideal.pl.get(&r3).cloned(),
            Some(Polynomial::<Fr>::zero()),
            "pl[c3] = 0"
        );
    }

    #[test]
    fn test_add_op_interpolate_ref_with_constant_points_in_pl() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let var_points = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_points);

        let coefs: Vec<_> = [0u64, 1]
            .iter()
            .map(|&n| mk::<ArkBls12_381>(Op::Value(Value::Index(n as usize))))
            .collect();
        builder.add_op(var_points.clone(), Op::Vec(coefs), &mut ideal);

        let var_evals = Var::from_node(NodeIndex::new(1), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_evals);

        let ideal_typ = ATyp::uni(2);
        let var_ideal = Var::from_node(NodeIndex::new(2), ideal_typ.clone(), Qualifier::Private);
        ideal.register(&var_ideal);

        let points: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t.clone());
        let evals: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(1)), vec_t.clone());

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(var_ideal.clone(), op, &mut ideal);

        let var_poly = |p: &Var| Polynomial::<Fr>::var(p);

        let r0 = var_ideal.clone().with_index(0).unwrap();
        let r1 = var_ideal.clone().with_index(1).unwrap();
        let r2 = var_ideal.clone().with_index(2).unwrap();

        let y0 = var_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_index(0)
            .unwrap();
        let y1 = var_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_index(0)
            .unwrap();

        let expected_c0 = var_poly(&y0);
        let expected_c1 = -var_poly(&y0) + var_poly(&y1);

        assert_eq!(
            ideal.pl.get(&r0).cloned(),
            Some(expected_c0.clone()),
            "pl[c0]"
        );
        assert_eq!(
            ideal.pl.get(&r1).cloned(),
            Some(expected_c1.clone()),
            "pl[c1]"
        );
        assert_eq!(
            ideal.pl.get(&r2).cloned(),
            Some(Polynomial::<Fr>::zero()),
            "pl[c2] = 0"
        );
    }

    #[test]
    fn test_add_op_interpolate_symbolic_points() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        // Two symbolic points x0, x1 stored as Var variables
        let scalar_t = ATyp::scalar();
        let vec_t = ATyp::Vec(Box::new(ATyp::scalar()), 2);
        let var_x0 = Var::from_node(NodeIndex::new(0), scalar_t.clone(), Qualifier::Private);
        let var_x1 = Var::from_node(NodeIndex::new(1), scalar_t.clone(), Qualifier::Private);
        ideal.register(&var_x0);
        ideal.register(&var_x1);

        // Points = [x0, x1]
        let var_points = Var::from_node(NodeIndex::new(2), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_points);
        let x0_slot = var_points
            .clone()
            .with_index(0)
            .unwrap()
            .with_index(0)
            .unwrap();
        let x1_slot = var_points
            .clone()
            .with_index(1)
            .unwrap()
            .with_index(0)
            .unwrap();
        ideal.pl.insert(&x0_slot, &Polynomial::var(&var_x0));
        ideal.pl.insert(&x1_slot, &Polynomial::var(&var_x1));

        // Evals = [y0, y1]
        let var_y0 = Var::from_node(NodeIndex::new(3), scalar_t.clone(), Qualifier::Private);
        let var_y1 = Var::from_node(NodeIndex::new(4), scalar_t.clone(), Qualifier::Private);
        ideal.register(&var_y0);
        ideal.register(&var_y1);

        let var_evals = Var::from_node(NodeIndex::new(5), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_evals);
        let y0_slot = var_evals
            .clone()
            .with_index(0)
            .unwrap()
            .with_index(0)
            .unwrap();
        let y1_slot = var_evals
            .clone()
            .with_index(1)
            .unwrap()
            .with_index(0)
            .unwrap();
        ideal.pl.insert(&y0_slot, &Polynomial::var(&var_y0));
        ideal.pl.insert(&y1_slot, &Polynomial::var(&var_y1));

        // Result = interpolate([x0, x1], [y0, y1])
        // p(t) = y0 * (t - x1) / (x0 - x1) + y1 * (t - x0) / (x1 - x0)
        //      = y0 * d01 * t - y0 * d01 * x1 + y1 * d10 * t - y1 * d10 * x0
        // where d01 * (x0 - x1) = 1 and d10 * (x1 - x0) = 1
        let ideal_typ = ATyp::uni(2);
        let var_ideal = Var::from_node(NodeIndex::new(6), ideal_typ.clone(), Qualifier::Private);
        ideal.register(&var_ideal);

        let points: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(2)), vec_t.clone());
        let evals: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(5)), vec_t.clone());

        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));
        builder.add_op(var_ideal.clone(), op, &mut ideal);

        // Verify: basis should contain d-variable equations and ideal equations.
        // For interpolate([x0, x1], [y0, y1]) with 2 symbolic points:
        // L_0(t) = d01*(t - x1), L_1(t) = d10*(t - x0)
        // p[0] = -y0*d01*x1 - y1*d10*x0  (constant term)
        // p[1] = y0*d01 + y1*d10          (linear coefficient)
        // p[2] = 0                         (no quadratic term)
        let r0 = var_ideal.clone().with_index(0).unwrap();
        let r1 = var_ideal.clone().with_index(1).unwrap();
        let r2 = var_ideal.clone().with_index(2).unwrap();

        let d_vars: Vec<_> = ideal
            .var_order
            .iter()
            .filter(|v| v.name.contains("interp_inv"))
            .collect();
        assert_eq!(d_vars.len(), 2, "should have 2 d-variables");
        let d01 = d_vars[0];
        let d10 = d_vars[1];

        let r0_poly = ideal.pl.get(&r0).cloned().unwrap();
        let r1_poly = ideal.pl.get(&r1).cloned().unwrap();
        let r2_poly = ideal.pl.get(&r2).cloned().unwrap();

        let neg_one = -<ark_bls12_381::Fr as ark_ff::One>::one();
        // Expected: p[0] = -y0*d01*x1 - y1*d10*x0, p[1] = y0*d01 + y1*d10
        // evals_polys uses slot Vars (y0_slot, y1_slot) as monomial variables.
        // xs_polys uses resolved Vars from pl (var_x0, var_x1) as monomial variables.
        let expected_r0 = Polynomial::var(&y0_slot)
            * (Polynomial::var(d01) * Polynomial::lit(&neg_one) * Polynomial::var(&var_x1))
            + Polynomial::var(&y1_slot)
                * (Polynomial::var(d10) * Polynomial::lit(&neg_one) * Polynomial::var(&var_x0));
        let expected_r1 = Polynomial::var(&y0_slot) * Polynomial::var(d01)
            + Polynomial::var(&y1_slot) * Polynomial::var(d10);

        assert_eq!(
            r0_poly, expected_r0,
            "p[0] should equal expected constant term"
        );
        assert_eq!(
            r1_poly, expected_r1,
            "p[1] should equal expected linear coefficient"
        );
        assert!(r2_poly.is_zero(), "p[2] should be zero");

        // Verify: ideal equations in basis (p[k] - r_k = 0)
        let r0_eq = &r0_poly - &Polynomial::var(&r0);
        let r1_eq = &r1_poly - &Polynomial::var(&r1);
        let r2_eq = &r2_poly - &Polynomial::var(&r2);
        assert!(
            ideal.generating_set.contains(&r0_eq),
            "basis should contain p[0] - r0 equation"
        );
        assert!(
            ideal.generating_set.contains(&r1_eq),
            "basis should contain p[1] - r1 equation"
        );
        assert!(
            ideal.generating_set.contains(&r2_eq),
            "basis should contain p[2] - r2 equation"
        );
    }

    #[test]
    #[should_panic(
        expected = "ideal: operation has no polynomial-ideal treatment at duplicate-interpolate-points"
    )]
    fn test_add_op_interpolate_duplicate_points_panics_explicitly() {
        use crate::Var;
        use backend::op::mk;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let evals_typ = ATyp::vec_scalar(3);
        let var_evals = Var::from_node(NodeIndex::new(1), evals_typ.clone(), Qualifier::Private);
        ideal.register(&var_evals);

        let var_ideal = Var::from_node(NodeIndex::new(2), ATyp::uni(3), Qualifier::Private);
        ideal.register(&var_ideal);

        let points = Op::Value(Value::VecIndex(vec![0, 0, 1]));
        let evals = Op::Ref(graph::Ref::new(NodeIndex::new(1)), evals_typ);
        let op: GOp<ArkBls12_381> =
            Op::Interpolate(mk::<ArkBls12_381>(points), mk::<ArkBls12_381>(evals));

        builder.add_op(var_ideal, op, &mut ideal);
    }
}
