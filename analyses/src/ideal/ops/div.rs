//! Division and remainder op encoders: `div_rem_op`, `slot_wise_div`,
//! `link_to_witness`, and witness allocation (`alloc_div_witness_pair`).

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::HOp;

use ark_ff::Zero;

use crate::Var;
use crate::frontend::Polynomial;

use super::Ideal;
use super::PolySource;
use super::{EncodeCtx, link_to_witness};

/// Allocate quotient/remainder witness sentinels without registering
/// opaque operations.
fn alloc_div_witness_pair<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    quotient_typ: ATyp,
    remainder_typ: ATyp,
) -> (Var, Var) {
    let q_name = ctx.builder.ns.next_name("div_q");
    let r_name = ctx.builder.ns.next_name("div_r");
    let q_wit = ctx.builder.sentinel_var(&q_name, quotient_typ, ctx.ideal);
    let r_wit = ctx.builder.sentinel_var(&r_name, remainder_typ, ctx.ideal);
    (q_wit, r_wit)
}

/// Unified Div/Rem handler for both `add_op` and `reduce_op`.
///
/// Dispatches based on operand types:
/// - Vec operands recurse element-wise
/// - `Uni / Uni` polynomial division uses witness Vars + degree chain
/// - Polynomial-like dividends divided by scalar-like divisors use slot-wise field division
/// - Non-polynomial Div uses slot-wise field division
/// - Remainder by scalar and unsupported polynomial division (Mle, VPoly
///   by non-scalar) remain `panic!`
pub fn div_rem_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    is_rem: bool,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    div_rem_op_inner(ctx, target, &a_src, &b_src, is_rem);
}

pub(crate) fn div_rem_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    is_rem: bool,
) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            for i in 0..*na {
                let t_i = target.with_index(i).unwrap();
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                div_rem_op_inner(ctx, &t_i, &a_elem, &b_elem, is_rem);
            }
        }
        (ATyp::Vec(_, na), _) => {
            for i in 0..*na {
                let t_i = target.with_index(i).unwrap();
                let a_elem = a.at_index(i).unwrap();
                div_rem_op_inner(ctx, &t_i, &a_elem, b, is_rem);
            }
        }
        (_, ATyp::Vec(_, nb)) => {
            if is_rem {
                panic!(
                    "Rem: scalar-left vector remainder is undefined for {} % {} — type checker should prevent this",
                    a.typ(),
                    b.typ(),
                );
            }
            for i in 0..*nb {
                let t_i = target.with_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                div_rem_op_inner(ctx, &t_i, a, &b_elem, false);
            }
        }
        _ => {
            div_rem_leaf(ctx, target, a, b, is_rem);
        }
    }
}

/// Leaf-level div/rem for non-Vec operands. Dispatches based on
/// operand types:
///
/// - `Uni / Uni` → polynomial long division with fresh witnesses and a
///   degree chain
/// - `Uni / scalar` → slot-wise field division (rem panics)
/// - `Mle / scalar` → slot-wise field division (rem panics)
/// - `VPoly / scalar` → slot-wise field division (rem panics)
/// - `Mle` / non-scalar → unsupported
/// - `VPoly` / non-scalar → unsupported
/// - `non-poly / non-poly` → slot-wise field division (rem panics)
/// - mixed poly/non-poly → unsupported
///
/// Only `Uni` supports polynomial-by-polynomial division. `Mle` and
/// `VPoly` (including univariate `VPoly(1, m)`) are restricted to
/// scalar division — multivariate polynomial division requires a term
/// order and does not satisfy the simple degree-based uniqueness
/// condition that the `Uni` encoding relies on.
fn div_rem_leaf<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    is_rem: bool,
) {
    let label = |s: &str| {
        if is_rem {
            format!("rem-{s}")
        } else {
            format!("div-{s}")
        }
    };
    match a.typ() {
        ATyp::Mle(_) => match b.typ() {
            ATyp::Base(ABase::Scalar | ABase::Fin(_)) => {
                if is_rem {
                    panic!(
                        "Rem: polynomial remainder by scalar is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                enforce_nonzero(ctx, &b.polys()[0]);
                let b_broadcast = b.broadcast_scalar_to(a.typ());
                slot_wise_div(ctx.ideal, target, a.polys(), b_broadcast.polys());
            }
            _ => super::uncovered_op(&label("mle-unsupported"), target),
        },
        ATyp::Uni(_) => match b.typ() {
            ATyp::Base(ABase::Scalar | ABase::Fin(_)) => {
                if is_rem {
                    panic!(
                        "Rem: polynomial remainder by scalar is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                enforce_nonzero(ctx, &b.polys()[0]);
                let b_broadcast = b.broadcast_scalar_to(a.typ());
                slot_wise_div(ctx.ideal, target, a.polys(), b_broadcast.polys());
            }
            ATyp::Uni(_) => {
                div_rem_poly(ctx, target, a, b, is_rem);
            }
            _ => super::uncovered_op(&label("uni-unsupported"), target),
        },
        ATyp::VPoly(_, _) => match b.typ() {
            ATyp::Base(ABase::Scalar | ABase::Fin(_)) => {
                if is_rem {
                    panic!(
                        "Rem: polynomial remainder by scalar is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                enforce_nonzero(ctx, &b.polys()[0]);
                let b_broadcast = b.broadcast_scalar_to(a.typ());
                slot_wise_div(ctx.ideal, target, a.polys(), b_broadcast.polys());
            }
            _ => super::uncovered_op(&label("vpoly-unsupported"), target),
        },
        ATyp::Base(_) => match b.typ() {
            ATyp::Base(_) => {
                if is_rem {
                    panic!(
                        "Rem: non-polynomial remainder is undefined for {} % {} — type checker should prevent this",
                        a.typ(),
                        b.typ(),
                    );
                }
                enforce_nonzero(ctx, &b.polys()[0]);
                slot_wise_div(ctx.ideal, target, a.polys(), b.polys());
            }
            _ => super::uncovered_op(&label("base-unsupported"), target),
        },
        _ => super::uncovered_op(&label("unsupported-type"), target),
    }
}

/// Univariate polynomial long division. Emits the canonical identity
/// `a = b·q + r` as basis rows, plus a degree chain that enforces
/// `deg(r) < deg(b)` for uniqueness, and links the target to `q` (Div)
/// or `r` (Rem).
///
/// Only `Uni` operands reach this function — `div_rem_leaf` rejects
/// `VPoly` and `Mle` polynomial division before dispatch.
///
/// **Bounds**: `ma` and `mb` are declared degree *upper bounds*, not exact
/// degrees, so they say nothing about the actual quotient degree beyond
/// `deg(q) ≤ deg(a) ≤ ma`. The quotient witness therefore has the dividend's
/// bound `Uni(ma)`, matching `lub_div`, and the identity is emitted for every
/// `k ∈ 0..=ma+mb` — the rows above `ma` read a zero dividend coefficient and
/// force the unused high coefficients of `b·q` to vanish. For the same reason
/// `ma < mb` is not a special case: it uses the general encoding.
///
/// **Degree chain**: For each level `d` from `mb` down to `1`, a boolean
/// selector `c_d` indicates whether `coef(b)[d] ≠ 0` (divisor has degree
/// ≥ d). If `c_d = 0`, then `coef(b)[d] = 0` and `r[d-1] = 0` (remainder
/// degree tightened below `d-1`). This chain guarantees uniqueness without
/// assuming the divisor has exact degree `mb`.
///
/// **Optimization**: When the divisor's leading coefficient is a known
/// nonzero constant (detected via the `pl` table), the entire chain is
/// skipped — the type bound `deg(r) < mb` already suffices.
fn div_rem_poly<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    is_rem: bool,
) {
    let (_, ma) = PolySource::<C>::poly_shape_static(a.typ()).unwrap();
    let (_, mb) = PolySource::<C>::poly_shape_static(b.typ()).unwrap();

    if mb == 0 {
        // Divisor is a declared constant: quotient = a / b[0], remainder = 0.
        let r_typ = if is_rem {
            target.typ.clone()
        } else {
            ATyp::Uni(0)
        };
        let (q_wit, r_wit) = alloc_div_witness_pair(ctx, ATyp::Uni(ma), r_typ);
        let b_poly = &b.polys()[0];
        enforce_nonzero(ctx, b_poly);
        for k in 0..=ma {
            let rhs = b_poly * &Polynomial::var(&q_wit.with_index(k).unwrap());
            ctx.ideal.generating_set.push(&a.polys()[k] - &rhs);
        }
        for rf in r_wit.slots() {
            ctx.ideal.generating_set.push(Polynomial::var(&rf));
        }
        let wit = if is_rem { &r_wit } else { &q_wit };
        link_to_witness(ctx.ideal, target, wit);
        return;
    }

    let mr = mb - 1;
    let (q_wit, r_wit) = alloc_div_witness_pair(ctx, ATyp::Uni(ma), ATyp::Uni(mr));

    // Emit a = b·q + r, one row per coefficient of the product bound.
    // For degree k: a[k] = Σ_{i+j=k} b[i]·q[j] + r[k]  (r[k] only if k ≤ mr),
    // where a[k] = 0 for k > ma. Rows above `ma` are what force the high
    // coefficients of b·q to cancel; without them a quotient of full width
    // would be unconstrained above the dividend's bound.
    let identity_bound = ma.checked_add(mb).expect("div_rem_poly: ma + mb overflow");
    let zero = Polynomial::<C::F>::zero();
    for k in 0..=identity_bound {
        let mut rhs = Polynomial::<C::F>::zero();
        let i_max = mb.min(k);
        for i in 0..=i_max {
            let j = k - i;
            if j > ma {
                continue;
            }
            let qf = q_wit.clone().with_index(j).unwrap();
            rhs = &rhs + &(&b.polys()[i] * &Polynomial::var(&qf));
        }
        if k <= mr {
            let rf = r_wit.clone().with_index(k).unwrap();
            rhs = &rhs + &Polynomial::var(&rf);
        }
        let lhs = a.polys().get(k).unwrap_or(&zero);
        ctx.ideal.generating_set.push(lhs - &rhs);
    }

    // Degree chain: enforce deg(r) < deg(b) for uniqueness.
    // Skip if the divisor's leading coefficient is a known nonzero constant.
    if !divisor_lead_known_nonzero::<C>(ctx, b, mb) {
        emit_degree_chain::<C>(ctx, b, &r_wit, mb);
    }

    let wit = if is_rem { &r_wit } else { &q_wit };
    link_to_witness(ctx.ideal, target, wit);
}

fn resolved_constant<C: ArkConfig>(
    ctx: &EncodeCtx<'_, C>,
    poly: &Polynomial<C::F>,
) -> Option<C::F> {
    if poly.is_constant() {
        return Some(poly.constant_coeff());
    }
    let mut current = poly.clone();
    loop {
        let (next, did_change) = current.inline_vars(&ctx.ideal.pl);
        if !did_change {
            return None;
        }
        if next.is_constant() {
            return Some(next.constant_coeff());
        }
        current = next;
    }
}

/// Restrict division constraints to defined program traces by requiring the
/// denominator to be nonzero. A known zero denominator makes the ideal unit;
/// a dynamic denominator gets a fresh inverse witness satisfying `d·inv = 1`.
fn enforce_nonzero<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    denominator: &Polynomial<C::F>,
) {
    if let Some(constant) = resolved_constant(ctx, denominator) {
        if constant.is_zero() {
            ctx.ideal
                .generating_set
                .push(Polynomial::lit(&C::FOps::one()));
        }
        return;
    }

    let name = ctx.builder.ns.next_name("div_inv");
    let inverse = ctx.sentinel_var(&name, ATyp::scalar());
    let inverse_poly = Polynomial::var(&inverse);
    let one = Polynomial::lit(&C::FOps::one());
    ctx.ideal
        .generating_set
        .push(&(denominator * &inverse_poly) - &one);
}

/// Check if the divisor's leading coefficient `b[mb]` resolves through the
/// `pl` table to a nonzero constant. In that case the divisor has exact degree
/// `mb`, so the type-based remainder bound suffices without a degree chain.
fn divisor_lead_known_nonzero<C: ArkConfig>(
    ctx: &EncodeCtx<'_, C>,
    b: &PolySource<C>,
    mb: usize,
) -> bool {
    resolved_constant(ctx, &b.polys()[mb]).is_some_and(|constant| !constant.is_zero())
}

/// Emit the degree chain that enforces `deg(r) < actual_deg(b)` for
/// uniqueness.
///
/// ## Per-level indicator `c_d`
///
/// For each level `d` from `mb` down to `0`, a boolean `c_d` indicates
/// whether `b[d] ≠ 0`:
///   b[d] · inv_d = c_d                (c_d = b[d]·inv_d)
///   b[d] · (1 - c_d) = 0              (c_d=0 → b[d] = 0)
///
/// These two constraints imply `c_d² - c_d = 0` (boolean) for free:
///   From eq2: b[d] = b[d]·c_d. Sub into eq1: b[d]·c_d·inv = c_d,
///   i.e. c_d·(b[d]·inv) = c_d, i.e. c_d² = c_d.
///
/// ## Cumulative boolean `s_d`
///
/// The tightening must only fire when **all** coefficients at level `d`
/// and above are zero — not just when `b[d] = 0`. A cumulative boolean
/// `s_d = "some coefficient at level ≥ d is nonzero"` is built top-down:
///   s_{mb} = c_{mb}
///   s_d = s_{d+1} + c_d - s_{d+1} · c_d   (boolean OR)
///
/// The remainder tightening uses `s_d`, not `c_d`:
///   (1 - s_d) · r[d-1] = 0   (d ≥ 1 only)
///
/// This ensures `r[d-1]` is forced to 0 only when the divisor's actual
/// degree is below `d`, not when an intermediate coefficient happens to
/// be zero. Finally, `s_0 = 1` requires at least one divisor coefficient
/// to be nonzero, excluding malformed division-by-zero traces.
fn emit_degree_chain<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    b: &PolySource<C>,
    r_wit: &Var,
    mb: usize,
) {
    let one = Polynomial::lit(&C::FOps::one());

    // s_{d+1} for the top level is 0 (no coefficients above mb).
    // Built top-down: s_mb = c_mb, s_{mb-1} = s_mb OR c_{mb-1}, etc.
    let mut s_above: Option<Var> = None;

    for d in (0..=mb).rev() {
        let c_name = ctx.builder.ns.next_name("div_c");
        let c_var = ctx.sentinel_var(&c_name, ATyp::scalar());
        let c_poly = Polynomial::var(&c_var);

        let b_d = &b.polys()[d];

        // b[d] · inv_d = c_d  (c_d = 1 iff b[d] ≠ 0)
        // b[d] · (1 - c_d) = 0  (c_d = 0 → b[d] = 0)
        //
        // These two imply c_d² - c_d = 0 (boolean) for free:
        //   From eq2: b[d] = b[d]·c_d. Sub into eq1: b[d]·c_d·inv = c_d,
        //   i.e. c_d·(b[d]·inv) = c_d, i.e. c_d·c_d = c_d.
        let inv_name = ctx.builder.ns.next_name("div_inv");
        let inv_var = ctx.sentinel_var(&inv_name, ATyp::scalar());
        let inv_poly = Polynomial::var(&inv_var);
        ctx.ideal.generating_set.push(&(b_d * &inv_poly) - &c_poly);

        let one_minus_c = &one - &c_poly;
        ctx.ideal.generating_set.push(&one_minus_c * b_d);

        // Build cumulative s_d = s_{d+1} OR c_d.
        // s_d = s_{d+1} + c_d - s_{d+1} · c_d
        let s_d = if let Some(ref s_above_var) = s_above {
            let s_above_poly = Polynomial::var(s_above_var);
            let s_name = ctx.builder.ns.next_name("div_s");
            let s_var = ctx.sentinel_var(&s_name, ATyp::scalar());
            let s_poly = Polynomial::var(&s_var);
            // s_d - (s_{d+1} + c_d - s_{d+1} · c_d) = 0
            ctx.ideal
                .generating_set
                .push(&s_poly - &(&(&s_above_poly + &c_poly) - &(&s_above_poly * &c_poly)));
            s_var
        } else {
            // Top level: s_{mb} = c_{mb}. No extra constraint needed —
            // just alias s to c.
            c_var.clone()
        };

        // (1 - s_d) · r[d-1] = 0  (tighten r only when ALL coeffs ≥ d are 0)
        // Only for d ≥ 1 — there is no r[-1].
        if d >= 1 {
            let s_poly = Polynomial::var(&s_d);
            let one_minus_s = &one - &s_poly;
            let r_slot = r_wit.with_index(d - 1).unwrap();
            let r_poly = Polynomial::var(&r_slot);
            ctx.ideal.generating_set.push(&one_minus_s * &r_poly);
        }

        s_above = Some(s_d);
    }

    let s_zero = s_above.expect("degree chain always includes level zero");
    ctx.ideal
        .generating_set
        .push(&Polynomial::var(&s_zero) - &one);
}

/// Slot-wise field division: emit `a[j] - b[j] * var[j] = 0` for each slot.
/// The caller must first enforce that each logical denominator is nonzero.
pub fn slot_wise_div<C: ArkConfig>(
    ideal: &mut Ideal<C>,
    target: &Var,
    a_polys: &[Polynomial<C::F>],
    b_polys: &[Polynomial<C::F>],
) {
    let target_slots = target.slots();
    assert_eq!(
        target_slots.len(),
        a_polys.len(),
        "slot_wise_div: target has {} slots but a_polys has {}",
        target_slots.len(),
        a_polys.len(),
    );
    assert_eq!(
        target_slots.len(),
        b_polys.len(),
        "slot_wise_div: target has {} slots but b_polys has {}",
        target_slots.len(),
        b_polys.len(),
    );
    for (j, pf) in target_slots.iter().enumerate() {
        ideal
            .generating_set
            .push(a_polys[j].clone() - b_polys[j].clone() * Polynomial::var(pf));
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::super::{Ideal, IdealBuilder};

    use crate::frontend::Polynomial;
    use backend::ArkBls12_381;

    use backend::ATyp;
    use backend::op::mk;
    use graph::{GOp, Op, Ref};
    use lang::ast::BinOp;

    use share::Ctx;

    #[allow(clippy::too_many_arguments)]
    #[test]
    fn test_add_op_uni_div_univariate_identity() {
        // Uni(2) / Uni(1) → Uni(2): both indices are degree upper bounds, so
        // the quotient keeps the dividend's bound.
        //   a has physical_len = 3 slots (a_0, a_1, a_2)
        //   b has physical_len = 2 slots (b_0, b_1)
        //   q_wit: Uni(2), 3 slots (q_0, q_1, q_2)
        //   r_wit: Uni(0), 1 slot  (r_0)
        // Canonical identity rows (from div_rem_poly), k = 0..=ma+mb = 3:
        //   k=0: a_0  -  (b_0·q_0 + r_0)
        //   k=1: a_1  -  (b_0·q_1 + b_1·q_0)
        //   k=2: a_2  -  (b_0·q_2 + b_1·q_1)
        //   k=3:  0   -  b_1·q_2          (dividend coefficient above ma is 0)
        // link_to_witness emits 3 more rows: var(q_wit[j]) - var(ideal[j]), j=0,1,2.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Witness);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(1), Qualifier::Witness);
        ideal.register(&var_b);

        let basis_before = ideal.generating_set.len();
        let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(1))),
            ATyp::Uni(2),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // Recover the q_wit / r_wit Vars (minted by sentinel_var starting
        // at MAX and decrementing: q_wit=MAX, r_wit=MAX-1).
        let q_wit = Var::from_var(
            "__zippel::gb::div_q::0",
            petgraph::graph::NodeIndex::new(usize::MAX),
            ATyp::Uni(2),
            Qualifier::Local,
        );
        let r_wit = Var::from_var(
            "__zippel::gb::div_r::0",
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::Uni(0),
            Qualifier::Local,
        );

        // Per-slot input vars (typ computed by `with_slot`).
        let scl = |p: &Var, i: usize| p.clone().with_index(i).unwrap();
        // Per-slot witness vars. `div_rem_poly` uses `wit.clone().with_index(j).unwrap()`
        // which sets typ appropriately.
        let wit_slot = |p: &Var, i: usize| p.clone().with_index(i).unwrap();
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let a0 = scl(&var_a, 0);
        let a1 = scl(&var_a, 1);
        let a2 = scl(&var_a, 2);
        let b0 = scl(&var_b, 0);
        let b1 = scl(&var_b, 1);
        let q0 = wit_slot(&q_wit, 0);
        let q1 = wit_slot(&q_wit, 1);
        let q2 = wit_slot(&q_wit, 2);
        let r0 = wit_slot(&r_wit, 0);

        // 4 identity rows + 7 degree-chain rows (mb=1: d=1→3, d=0→3, s_0=1) + 3 linking rows.
        assert_eq!(
            ideal.generating_set.len() - basis_before,
            14,
            "expected 4 identity + 7 degree-chain + 3 linking rows"
        );

        // Check identity rows exist in basis.
        let zero = Polynomial::<ark_bls12_381::Fr>::zero();
        let expected_k0 = &var_poly(&a0) - &(&(&var_poly(&b0) * &var_poly(&q0)) + &var_poly(&r0));
        let expected_k1 = &var_poly(&a1)
            - &(&(&var_poly(&b0) * &var_poly(&q1)) + &(&var_poly(&b1) * &var_poly(&q0)));
        let expected_k2 = &var_poly(&a2)
            - &(&(&var_poly(&b0) * &var_poly(&q2)) + &(&var_poly(&b1) * &var_poly(&q1)));
        let expected_k3 = &zero - &(&var_poly(&b1) * &var_poly(&q2));
        for (lbl, expected) in [
            ("k0", &expected_k0),
            ("k1", &expected_k1),
            ("k2", &expected_k2),
            ("k3", &expected_k3),
        ] {
            assert!(
                ideal.generating_set.iter().any(|row| row == expected),
                "basis missing identity row {}",
                lbl
            );
        }

        // link_to_witness: pl[ideal[j]] = var(q_wit[j]) for j=0,1,2.
        for (j, q_slot) in [(0, &q0), (1, &q1), (2, &q2)] {
            assert_eq!(
                ideal.pl.get(&var.clone().with_index(j).unwrap()).cloned(),
                Some(var_poly(q_slot)),
                "pl[ideal[{j}]] should alias q_wit[{j}]"
            );
        }

        // Linking rows: var(q_wit[j]) - var(ideal[j]).
        // link_to_witness uses `ideal.clone().with_index(j).unwrap()` (typ computed by with_slot).
        for (j, q_slot) in [(0, &q0), (1, &q1), (2, &q2)] {
            let target_slot = var.clone().with_index(j).unwrap();
            let link = &var_poly(q_slot) - &var_poly(&target_slot);
            assert!(
                ideal.generating_set.iter().any(|row| row == &link),
                "basis missing link row var_poly(q_wit[{j}]) - var_poly(ideal[{j}])"
            );
        }
    }

    /// The honest execution of `X^4 / 1` must satisfy *every* emitted
    /// equation when the divisor is only declared `Uni(2)`.
    ///
    /// This is the end-to-end statement the old `ma - mb` quotient bound
    /// broke: the quotient `X^4` needs all five declared slots, the identity
    /// must run through `k = ma + mb = 6`, and the dynamic degree chain must
    /// accept a divisor whose top two declared coefficients vanish.
    #[test]
    fn polynomial_division_declared_constant_bound_assignment() {
        use crate::Var;
        use ark_bls12_381::Fr;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;
        use share::Set;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(4), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(2), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        // lub_div(Uni(4), Uni(2)) = Uni(4).
        let target = Var::from_node(NodeIndex::new(2), ATyp::Uni(4), Qualifier::Witness);
        ideal.register(&target);

        let before = ideal.generating_set.len();
        builder.add_op(
            target.clone(),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(4))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(2))),
                ATyp::Uni(4),
            ),
            &mut ideal,
        );

        // 7 identity rows (k = 0..=6) + 11 degree-chain rows (4·mb + 3)
        // + 5 quotient-link rows.
        assert_eq!(
            ideal.generating_set.len() - before,
            23,
            "expected 7 identity + 11 degree-chain + 5 linking rows"
        );

        let basis_vars = ideal
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .collect::<Set<Var>>();
        let slot_indices = |prefix: &str| {
            basis_vars
                .iter()
                .filter(|v| v.name.starts_with(prefix))
                .map(|v| *v.index.last().expect("witness slots are indexed"))
                .collect::<Set<usize>>()
        };
        assert_eq!(
            slot_indices("__zippel::gb::div_q").len(),
            5,
            "the quotient witness must expose all five declared slots"
        );
        assert_eq!(
            slot_indices("__zippel::gb::div_r").len(),
            2,
            "the remainder witness is Uni(mb - 1) = Uni(1)"
        );

        // Honest assignment for a = X^4, b = 1 (declared Uni(2)):
        //   q = X^4, r = 0.
        // Degree-chain auxiliaries are minted top-down, d = mb..0, so the
        // `div_c`/`div_inv` counters run d=2, d=1, d=0 and the `div_s`
        // counters (emitted only below the top level) run d=1, d=0:
        //   c = inv = [0, 0, 1]  (only b[0] is nonzero)
        //   s = [0, 1]           (s_1 = 0, s_0 = 1: the divisor is nonzero)
        let zero = Fr::from(0u64);
        let one = Fr::from(1u64);
        let a_coeffs = [zero, zero, zero, zero, one];
        let b_coeffs = [one, zero, zero];
        let q_coeffs = [zero, zero, zero, zero, one];
        let r_coeffs = [zero, zero];
        let c_by_counter = [zero, zero, one];
        let inv_by_counter = [zero, zero, one];
        let s_by_counter = [zero, one];

        let counter = |name: &str| {
            name.rsplit("::")
                .next()
                .and_then(|c| c.parse::<usize>().ok())
                .expect("sentinel names end in a mint counter")
        };
        let slot = |v: &Var| *v.index.last().expect("value slots are indexed");

        let mut subs: Ctx<Var, Polynomial<Fr>> = Ctx::new();
        for v in basis_vars.iter() {
            let value = if v.name.starts_with("__zippel::gb::div_q") {
                q_coeffs[slot(v)]
            } else if v.name.starts_with("__zippel::gb::div_r") {
                r_coeffs[slot(v)]
            } else if v.name.starts_with("__zippel::gb::div_c") {
                c_by_counter[counter(&v.name)]
            } else if v.name.starts_with("__zippel::gb::div_inv") {
                inv_by_counter[counter(&v.name)]
            } else if v.name.starts_with("__zippel::gb::div_s") {
                s_by_counter[counter(&v.name)]
            } else if v.reference == var_a.reference {
                a_coeffs[slot(v)]
            } else if v.reference == var_b.reference {
                b_coeffs[slot(v)]
            } else if v.reference == target.reference {
                q_coeffs[slot(v)]
            } else {
                panic!("unexpected variable {} in the division basis", v.verbose());
            };
            subs.insert(v, &Polynomial::lit(&value));
        }

        for row in ideal.generating_set.iter() {
            let (evaluated, _) = row.clone().inline_vars(&subs);
            assert!(
                evaluated.is_constant(),
                "row {row} left free variables under the complete assignment"
            );
            assert_eq!(
                evaluated.constant_coeff(),
                zero,
                "honest X^4 / 1 assignment must satisfy row {row}"
            );
        }
    }

    #[test]
    fn test_add_op_uni_rem_univariate_identity() {
        // Uni(2) % Uni(1) → Uni(0).
        // Same witnesses as the Div test, but link ideal to r_wit (1 slot).
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Witness);
        ideal.register(&_var_a);
        let _var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(1), Qualifier::Witness);
        ideal.register(&_var_b);

        let basis_before = ideal.generating_set.len();
        let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(0), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(1))),
            ATyp::Uni(0),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // q_wit=MAX, r_wit=MAX-1 (fresh builder, counter starts at MAX).
        let r_wit = Var::from_var(
            "__zippel::gb::div_r::0",
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::Uni(0),
            Qualifier::Local,
        );
        let scl = |p: &Var, i: usize| p.clone().with_index(i).unwrap();
        let _ = scl; // kept for parity with the Div test; not used here.
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        // r_wit slots: with_slot computes the correct type.
        let r0 = r_wit.clone().with_index(0).unwrap();

        // 4 identity rows + 7 degree-chain rows (mb=1: d=1→3, d=0→3, s_0=1) + 1 linking row.
        assert_eq!(
            ideal.generating_set.len() - basis_before,
            12,
            "expected 4 identity + 7 degree-chain + 1 linking row"
        );

        // pl[ideal[0]] = var(r_wit[0]).
        assert_eq!(
            ideal.pl.get(&var.clone().with_index(0).unwrap()).cloned(),
            Some(var_poly(&r0)),
            "pl[ideal[0]] should alias r_wit[0]"
        );

        // Linking row: link_to_witness uses ideal.with_index(0).unwrap() (type computed by with_slot).
        let r0_slot = var.clone().with_index(0).unwrap();
        let link = &var_poly(&r0) - &var_poly(&r0_slot);
        assert!(
            ideal.generating_set.iter().any(|row| row == &link),
            "basis missing link row var_poly(r_wit[0]) - var_poly(ideal[0])"
        );
    }

    #[test]
    fn test_add_op_uni_div_constant_enforces_nonzero_divisor() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(1), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(0), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let before = ideal.generating_set.len();
        let target = Var::from_node(NodeIndex::new(2), ATyp::Uni(1), Qualifier::Witness);
        builder.add_op(
            target,
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(1))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(0))),
                ATyp::Uni(1),
            ),
            &mut ideal,
        );

        assert_eq!(
            ideal.generating_set.len() - before,
            6,
            "constant polynomial division should emit identity, zero remainder, links, and a nonzero-divisor row"
        );
        let b0 = var_b.with_index(0).unwrap();
        assert!(
            ideal.generating_set.iter().any(|row| {
                row.contains(&b0)
                    && row
                        .vars()
                        .iter()
                        .any(|var| var.name.starts_with("__zippel::gb::div_inv"))
            }),
            "constant polynomial division should enforce `b[0] * inv - 1 = 0`"
        );
    }

    #[test]
    fn test_add_op_div_then_rem_emits_fresh_witnesses() {
        // `a/b` and `a%b` on the same operand pair now each allocate fresh
        // witnesses and emit their own identity rows + degree chain.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Witness);
        ideal.register(&_var_a);
        let _var_b = Var::from_node(NodeIndex::new(1), ATyp::Uni(1), Qualifier::Witness);
        ideal.register(&_var_b);

        let basis_before_div = ideal.generating_set.len();
        let _q_res = {
            let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Witness);
            let op: GOp<ArkBls12_381> = Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(1))),
                ATyp::Uni(2),
            );
            builder.add_op(var.clone(), op, &mut ideal);
            var
        };
        let after_div = ideal.generating_set.len();

        let _r_res = {
            let var = Var::from_node(NodeIndex::new(3), ATyp::Uni(0), Qualifier::Witness);
            let op: GOp<ArkBls12_381> = Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::Uni(1))),
                ATyp::Uni(0),
            );
            builder.add_op(var.clone(), op, &mut ideal);
            var
        };
        let after_rem = ideal.generating_set.len();

        // Div added 4 identity + 7 degree-chain (mb=1: d=1→3, d=0→3, s_0=1) + 3 linking = 14 rows.
        assert_eq!(
            after_div - basis_before_div,
            14,
            "Div emitted 4 identity + 7 degree-chain + 3 linking rows"
        );
        // Rem allocates fresh witnesses: 4 identity + 7 degree-chain (mb=1) + 1 linking = 12 rows.
        assert_eq!(
            after_rem - after_div,
            12,
            "Rem should emit fresh identity + degree-chain + 1 linking row"
        );
    }

    #[test]
    fn test_add_op_div_rem_equivalent_named_derived_operands() {
        // PR #153 regression: two closure-local derived nodes can carry the
        // same named-source expression (`a * b - c`) while still having
        // distinct raw HOp refs. Div and Rem over those equivalent operands
        // each allocate fresh witnesses and emit their own rows.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        for (idx, name, typ) in [
            (0, "a", ATyp::Uni(1)),
            (1, "b", ATyp::Uni(1)),
            (2, "c", ATyp::Uni(2)),
            (3, "d", ATyp::Uni(1)),
        ] {
            let var = Var::from_var(name, NodeIndex::new(idx), typ, Qualifier::Instance);
            ideal.register(&var);
        }

        let mk_ref = |idx, typ| mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(idx)), typ));

        let mut add_derived_operand = |mul_idx, sub_idx| {
            let mul_ref = Var::from_node(NodeIndex::new(mul_idx), ATyp::Uni(2), Qualifier::Witness);
            ideal.register(&mul_ref);
            builder.add_op(
                mul_ref.clone(),
                Op::Bin(
                    BinOp::Mul,
                    mk_ref(0, ATyp::Uni(1)),
                    mk_ref(1, ATyp::Uni(1)),
                    ATyp::Uni(2),
                ),
                &mut ideal,
            );

            let sub_ref = Var::from_node(NodeIndex::new(sub_idx), ATyp::Uni(2), Qualifier::Witness);
            ideal.register(&sub_ref);
            builder.add_op(
                sub_ref.clone(),
                Op::Bin(
                    BinOp::Sub,
                    mk_ref(mul_idx, ATyp::Uni(2)),
                    mk_ref(2, ATyp::Uni(2)),
                    ATyp::Uni(2),
                ),
                &mut ideal,
            );
            sub_ref
        };

        add_derived_operand(10, 11);
        add_derived_operand(12, 13);

        // Uni(2) / Uni(1) keeps the dividend's bound: the quotient is Uni(2).
        let q = Var::from_node(NodeIndex::new(20), ATyp::Uni(2), Qualifier::Witness);
        builder.add_op(
            q,
            Op::Bin(
                BinOp::Div,
                mk_ref(11, ATyp::Uni(2)),
                mk_ref(3, ATyp::Uni(1)),
                ATyp::Uni(2),
            ),
            &mut ideal,
        );

        let r = Var::from_node(NodeIndex::new(21), ATyp::Uni(0), Qualifier::Witness);
        builder.add_op(
            r,
            Op::Bin(
                BinOp::Rem,
                mk_ref(13, ATyp::Uni(2)),
                mk_ref(3, ATyp::Uni(1)),
                ATyp::Uni(0),
            ),
            &mut ideal,
        );

        // Div and Rem each emit fresh identity + degree-chain + linking rows.
        assert!(
            !ideal.generating_set.is_empty(),
            "Div and Rem over equivalent derived operands should emit rows"
        );
    }

    #[test]
    fn test_add_op_div_scalar_fallback() {
        // Scalar / Scalar → Scalar: slot-wise field division (a - b·var(var) = 0).
        // Scalar fallback does not allocate polynomial witnesses or degree chain.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_b);

        let basis_before = ideal.generating_set.len();
        let var = Var::from_node(NodeIndex::new(2), ATyp::scalar(), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
            ATyp::scalar(),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // Scalar division emits one nonzero-divisor row and one quotient row.
        assert_eq!(
            ideal.generating_set.len() - basis_before,
            2,
            "scalar fallback emits a nonzero-divisor row and a quotient row"
        );
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let expected = &var_poly(&var_a) - &(&var_poly(&var_b) * &var_poly(&var));
        assert!(
            ideal.generating_set.iter().any(|row| row == &expected),
            "scalar fallback row should be `a - b · var_poly(ideal)`"
        );
        let inv = Var::from_var(
            "__zippel::gb::div_inv::0",
            NodeIndex::new(usize::MAX),
            ATyp::scalar(),
            Qualifier::Local,
        );
        let expected_nonzero = &(&var_poly(&var_b) * &var_poly(&inv))
            - &Polynomial::lit(&ark_bls12_381::Fr::from(1u64));
        assert!(
            ideal
                .generating_set
                .iter()
                .any(|row| row == &expected_nonzero),
            "scalar fallback should enforce `b * inv - 1 = 0`"
        );
    }

    #[test]
    fn test_add_op_scalar_div_vec_scalar_recurses_without_div_wit() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::vec_scalar(2), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::vec_scalar(2), Qualifier::Witness);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::vec_scalar(2))),
            ATyp::vec_scalar(2),
        );

        let before = ideal.generating_set.len();
        builder.add_op(var.clone(), op, &mut ideal);

        assert_eq!(ideal.generating_set.len() - before, 4);
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        for i in 0..2 {
            let b_i = var_b.clone().with_index(i).unwrap();
            let r_i = var.clone().with_index(i).unwrap();
            let expected = &var_poly(&var_a) - &(&var_poly(&b_i) * &var_poly(&r_i));
            assert!(
                ideal.generating_set.iter().any(|row| row == &expected),
                "basis missing scalar/vector div row {i}"
            );
        }
    }

    #[test]
    fn test_add_op_uni_div_scalar_slot_wise_without_div_wit() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Witness);
        let before = ideal.generating_set.len();
        builder.add_op(
            var.clone(),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Uni(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
                ATyp::Uni(2),
            ),
            &mut ideal,
        );

        assert_eq!(ideal.generating_set.len() - before, 4);
    }

    #[test]
    fn test_add_op_mle_div_scalar_slot_wise_without_div_wit() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Mle(2), Qualifier::Witness);
        let before = ideal.generating_set.len();
        builder.add_op(
            var,
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::Mle(2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
                ATyp::Mle(2),
            ),
            &mut ideal,
        );

        assert_eq!(ideal.generating_set.len() - before, 5);
    }

    #[test]
    fn test_add_op_vector_uni_div_rem_emits_fresh_witnesses() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let vec_typ = ATyp::Vec(Box::new(ATyp::Uni(2)), 2);
        // lub_div: Uni(2) / Uni(2) = Uni(2) (the quotient keeps the dividend bound)
        let div_typ = ATyp::Vec(Box::new(ATyp::Uni(2)), 2);
        // lub_rem: Uni(2) % Uni(2) = Uni(2-1) = Uni(1)
        let rem_typ = ATyp::Vec(Box::new(ATyp::Uni(1)), 2);
        for idx in 0..2 {
            ideal.register(&Var::from_node(
                NodeIndex::new(idx),
                vec_typ.clone(),
                Qualifier::Witness,
            ));
        }

        builder.add_op(
            Var::from_node(NodeIndex::new(2), div_typ.clone(), Qualifier::Witness),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_typ.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_typ.clone())),
                div_typ,
            ),
            &mut ideal,
        );
        let after_div = ideal.generating_set.len();

        builder.add_op(
            Var::from_node(NodeIndex::new(3), rem_typ.clone(), Qualifier::Witness),
            Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_typ.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_typ)),
                rem_typ,
            ),
            &mut ideal,
        );

        // Each element is Uni(2)/Uni(2) (ma=mb=2). Rem emits fresh witnesses per
        // element: 5 identity (k=0..=4) + 11 degree-chain (d=2→3, d=1→4, d=0→3,
        // s_0=1) + 2 linking = 18. 2 elements → 36 rows.
        assert_eq!(
            ideal.generating_set.len() - after_div,
            36,
            "vector Rem should emit fresh identity + degree-chain + linking rows \
             per element (2 elements × 18 = 36)"
        );
    }

    /// Test-local binomial coefficient C(n, k). Assumes `k <= n`.

    #[test]
    fn ideal_nested_div() {
        use lang::id::Tid;
        let src = r#"
            proto nd<F: Field>(instance a: Uni<F, 4>, instance b: Uni<F, 2>, instance c: Uni<F, 2>) where a == a {
                let q = (a / b) / c;
                verify(q == q)
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let tc = trans_clos_from_src_sized(src, &sizes);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Two polynomial divisions: inner (a/b) and outer ((a/b)/c).
        // Each allocates fresh witnesses and emits identity + degree-chain rows.

        // pl should contain entries for the div ideal nodes (linking them to
        // quotient witness slots). Since children are Op::Ref after IR lowering,
        // pl entries are keyed by node index with name=None.
        assert!(
            !gr.pl.is_empty(),
            "pl should have entries for div ideal nodes, got {}",
            gr.pl.len()
        );

        // Basis should contain canonical div identity rows (a = b*q + r)
        // and linking rows for both inner and outer division.
        // Div witness vars (q_wit, r_wit) must appear in basis.vars().
        // GB computation moved to backend; skipped in unit test();
        assert!(
            !gr.generating_set.is_empty(),
            "basis should not be empty after nested div"
        );

        let basis_vars = gr
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        assert!(
            basis_vars
                .iter()
                .any(|p| p.name.starts_with("__zippel::gb::div_q")),
            "basis.vars() should contain div_q witnesses"
        );
        assert!(
            basis_vars
                .iter()
                .any(|p| p.name.starts_with("__zippel::gb::div_r")),
            "basis.vars() should contain div_r witnesses"
        );
    }

    #[test]
    fn ideal_div_rem_separate_witnesses() {
        use lang::id::Tid;
        let src = r#"
            proto sdr<F: Field>(instance a: Uni<F, 4>, instance b: Uni<F, 2>) where a == a {
                verify(a == b * (a / b) + (a % b))
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let tc = trans_clos_from_src_sized(src, &sizes);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Div and rem each allocate fresh witnesses and emit their own
        // identity + degree-chain rows.

        // pl should have entries for the div ideal (n3 → q_wit), mul ideal (n4 → b*q),
        // rem ideal (n5 → r_wit), and sum ideal (n6 → n4 + n5)
        assert!(
            gr.pl.len() >= 8,
            "pl should have entries for div/mul/rem/add chains, got {} entries",
            gr.pl.len()
        );

        // GB computation moved to backend; skipped in unit test();
        assert!(
            !gr.generating_set.is_empty(),
            "basis should not be empty after div/rem"
        );
    }

    #[test]
    fn test_add_op_div_scalar_slot_wise() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var_ideal = Var::from_node(NodeIndex::new(2), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_ideal);

        let a = Op::Ref(graph::Ref::new(NodeIndex::new(0)), ATyp::scalar());
        let b = Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::scalar());
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::scalar(),
        );
        builder.add_op(var_ideal.clone(), op, &mut ideal);

        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);

        let a_slot = var_a.clone();
        let b_slot = var_b.clone();
        let r_slot = var_ideal.clone();
        let expected = &var_poly(&a_slot) - &(&var_poly(&b_slot) * &var_poly(&r_slot));
        assert!(
            ideal.generating_set.iter().any(|r| r == &expected),
            "basis should contain a - b*var_poly(var)"
        );
    }

    #[test]
    #[should_panic(expected = "Rem: non-polynomial remainder")]
    fn test_add_op_rem_scalar_panics() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var_ideal = Var::from_node(NodeIndex::new(2), ATyp::scalar(), Qualifier::Witness);
        ideal.register(&var_ideal);

        let a = Op::Ref(graph::Ref::new(NodeIndex::new(0)), ATyp::scalar());
        let b = Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::scalar());
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::scalar(),
        );
        builder.add_op(var_ideal, op, &mut ideal);
    }

    #[test]
    #[should_panic(expected = "div-mle-unsupported")]
    fn test_add_op_div_mle_panics() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Mle(2), Qualifier::Witness);
        ideal.register(&var);

        let a = Op::Ref(graph::Ref::new(NodeIndex::new(0)), ATyp::Mle(2));
        let b = Op::Ref(graph::Ref::new(NodeIndex::new(1)), ATyp::Mle(2));
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(a),
            mk::<ArkBls12_381>(b),
            ATyp::Mle(2),
        );
        builder.add_op(var, op, &mut ideal);
    }

    #[test]
    fn test_reduce_div_uni_uses_handle_div_rem() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::Uni(3)), 2);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Witness);
        ideal.register(&var_v);

        // lub_div: Uni(3) / Uni(3) = Uni(3) (the quotient keeps the dividend bound)
        let var = Var::from_node(NodeIndex::new(1), ATyp::Uni(3), Qualifier::Witness);
        ideal.register(&var);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        assert!(
            !ideal.generating_set.is_empty(),
            "Reduce Div on Uni should emit identity rows via handle_div_rem"
        );
    }

    /// A declared divisor bound above the dividend's says nothing about the
    /// operands' actual degrees, so `ma < mb` must use the same general
    /// Euclidean encoding as every other positive-bound division — not a
    /// pass-through of the dividend.
    #[test]
    fn poly_rem_smaller_dividend_uses_general_encoding() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let dividend_t = ATyp::Uni(1);
        let divisor_t = ATyp::Uni(3);
        let var_a = Var::from_node(NodeIndex::new(0), dividend_t.clone(), Qualifier::Witness);
        let var_b = Var::from_node(NodeIndex::new(1), divisor_t.clone(), Qualifier::Witness);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Witness);
        ideal.register(&var);

        let before = ideal.generating_set.len();
        builder.add_op(
            var.clone(),
            Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), dividend_t)),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), divisor_t)),
                ATyp::Uni(2),
            ),
            &mut ideal,
        );

        // ma=1, mb=3: 5 identity rows (k = 0..=ma+mb) + 15 degree-chain rows
        // (4·mb + 3) + 3 remainder-link rows.
        assert_eq!(
            ideal.generating_set.len() - before,
            23,
            "smaller declared dividend bound must still use the general encoding"
        );

        // The target aliases the remainder witness rather than the dividend.
        let q_wit = Var::from_var(
            "__zippel::gb::div_q::0",
            NodeIndex::new(usize::MAX),
            ATyp::Uni(1),
            Qualifier::Local,
        );
        let r_wit = Var::from_var(
            "__zippel::gb::div_r::0",
            NodeIndex::new(usize::MAX - 1),
            ATyp::Uni(2),
            Qualifier::Local,
        );
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        for i in 0..3 {
            let target_slot = var.clone().with_index(i).unwrap();
            let r_slot = r_wit.clone().with_index(i).unwrap();
            assert_eq!(
                ideal.pl.get(&target_slot).cloned(),
                Some(var_poly(&r_slot)),
                "remainder slot {i} should alias div_r, not pass the dividend through"
            );
        }

        // The divisor's leading coefficient is dynamic, so the degree chain
        // must supply indicator, inverse, and cumulative witnesses.
        let basis_vars = ideal
            .generating_set
            .iter()
            .flat_map(|p| p.vars())
            .collect::<share::Set<_>>();
        for prefix in [
            "__zippel::gb::div_q",
            "__zippel::gb::div_r",
            "__zippel::gb::div_c",
            "__zippel::gb::div_inv",
            "__zippel::gb::div_s",
        ] {
            assert!(
                basis_vars.iter().any(|v| v.name.starts_with(prefix)),
                "general encoding should emit {prefix} witnesses"
            );
        }

        // The top identity row forces b[3]·q[1] to vanish: the dividend has no
        // coefficient at degree 4.
        let zero = Polynomial::<ark_bls12_381::Fr>::zero();
        let b3 = var_b.clone().with_index(3).unwrap();
        let q1 = q_wit.with_index(1).unwrap();
        let expected_top = &zero - &(&var_poly(&b3) * &var_poly(&q1));
        assert!(
            ideal.generating_set.iter().any(|row| row == &expected_top),
            "basis missing the k = ma + mb identity row"
        );
    }

    /// `Vec(Uni(2),2) / Uni(1)` — Vec<Poly> divided by a bare Poly.
    /// Each element recurses into the leaf poly/poly division arm.
    #[test]
    fn test_div_vec_uni_by_uni() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let elem_a = ATyp::Uni(2);
        let vec_a = ATyp::Vec(Box::new(elem_a.clone()), 2);
        let div_t = ATyp::Uni(1);

        let var_a = Var::from_node(NodeIndex::new(0), vec_a.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), div_t.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        // lub_div(Vec(Uni(2),2), Uni(1)) = Vec(lub_div(Uni(2), Uni(1)), 2)
        //                                   = Vec(Uni(2), 2)
        let result_t = ATyp::Vec(Box::new(ATyp::Uni(2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_a.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), div_t.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        // Each element is Uni(2)/Uni(1) (ma=2, mb=1): 4 identity + 7 degree-chain
        // + 3 linking = 14.

        // All result slots populated.
        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Vec(Uni)/Uni element {i} slot {j} missing from pl"
                );
            }
        }
    }

    /// `Uni(2) / Vec(Uni(1),2)` — bare Poly divided by Vec<Poly>.
    /// The scalar-left vector division broadcasts the dividend across elements.
    #[test]
    fn test_div_uni_by_vec_uni() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let dividend_t = ATyp::Uni(2);
        let elem_b = ATyp::Uni(1);
        let vec_b = ATyp::Vec(Box::new(elem_b.clone()), 2);

        let var_a = Var::from_node(NodeIndex::new(0), dividend_t.clone(), Qualifier::Witness);
        ideal.register(&var_a);

        let var_b = Var::from_node(NodeIndex::new(1), vec_b.clone(), Qualifier::Witness);
        ideal.register(&var_b);

        // lub_div(Uni(2), Vec(Uni(1),2)) = Vec(lub_div(Uni(2), Uni(1)), 2)
        //                                 = Vec(Uni(2), 2)
        let result_t = ATyp::Vec(Box::new(ATyp::Uni(2)), 2);
        let var_r = Var::from_node(NodeIndex::new(2), result_t.clone(), Qualifier::Witness);
        ideal.register(&var_r);

        builder.add_op(
            var_r.clone(),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), dividend_t.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_b.clone())),
                result_t.clone(),
            ),
            &mut ideal,
        );

        // Each element divides the same dividend by a different divisor element.
        // Each element is Uni(2)/Uni(1) (ma=2, mb=1): 4 identity + 7 degree-chain
        // + 3 linking = 14.

        for i in 0..2 {
            let elem = var_r.clone().with_index(i).unwrap();
            for j in 0..3 {
                let slot = elem.clone().with_index(j).unwrap();
                assert!(
                    ideal.pl.contains(&slot),
                    "Uni/Vec(Uni) element {i} slot {j} missing from pl"
                );
            }
        }
    }
}
