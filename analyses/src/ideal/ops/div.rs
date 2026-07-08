//! Division and remainder op encoders: `div_rem_op`, `slot_wise_div`,
//! `link_to_witness`, and the witness-caching machinery
//! (`alloc_div_witness_pair`, `div_witness_key`, `canonical_*` helpers).

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;

use crate::Var;
use crate::frontend::Polynomial;

use super::Ideal;
use super::PolySource;
use super::multi_indices;
use super::{CanonPolyTyp, DivWitnessKey};
use super::{EncodeCtx, link_to_polys, link_to_witness};

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

fn canonical_div_typ<C: ArkConfig>(t: &ATyp) -> Option<CanonPolyTyp> {
    PolySource::<C>::poly_shape_static(t).map(|(num_vars, max_degree)| CanonPolyTyp {
        num_vars,
        max_degree,
    })
}

fn div_witness_key<C: ArkConfig + HasOpFactory>(
    ctx: &EncodeCtx<'_, C>,
    a: &PolySource<C>,
    b: &PolySource<C>,
) -> DivWitnessKey {
    DivWitnessKey {
        dividend_typ: canonical_div_typ::<C>(a.typ()).expect("dividend must be polynomial"),
        divisor_typ: canonical_div_typ::<C>(b.typ()).expect("divisor must be polynomial"),
        dividend_slots: canonical_slot_keys::<C>(a, ctx.ideal),
        divisor_slots: canonical_slot_keys::<C>(b, ctx.ideal),
    }
}

fn canonical_slot_keys<C: ArkConfig>(source: &PolySource<C>, ideal: &Ideal<C>) -> Vec<String> {
    source
        .polys()
        .iter()
        .map(|p| canonical_poly_key::<C>(p, ideal, &mut Vec::new()))
        .collect()
}

fn canonical_poly_key<C: ArkConfig>(
    poly: &Polynomial<C::F>,
    ideal: &Ideal<C>,
    seen: &mut Vec<Var>,
) -> String {
    if poly.is_zero() {
        return "0".to_string();
    }

    let mut terms: Vec<String> = poly
        .terms
        .iter()
        .map(|(term, coeff)| {
            format!(
                "coeff={};monomial={}",
                coeff,
                canonical_monomial_key::<C>(term, ideal, seen)
            )
        })
        .collect();
    terms.sort();
    terms.join("|")
}

fn canonical_monomial_key<C: ArkConfig>(
    term: &crate::frontend::Monomial,
    ideal: &Ideal<C>,
    seen: &mut Vec<Var>,
) -> String {
    let mut factors: Vec<String> = term
        .vars()
        .into_iter()
        .zip(term.powers())
        .map(|(var, power)| canonical_factor_key::<C>(&var, power, ideal, seen))
        .collect();
    factors.sort();
    factors.join("*")
}

fn canonical_factor_key<C: ArkConfig>(
    var: &Var,
    power: usize,
    ideal: &Ideal<C>,
    seen: &mut Vec<Var>,
) -> String {
    // If the var has a polynomial definition, recurse into it — it's
    // a derived value, not a source var.
    if let Some(def) = ideal.pl.get(var)
        && !seen.contains(var)
    {
        seen.push(var.clone());
        let def_key = canonical_poly_key::<C>(def, ideal, seen);
        seen.pop();
        return format!("def=({})^{}", def_key, power);
    }

    format!("{}^{}", canonical_var_key(var), power)
}

fn canonical_var_key(var: &Var) -> String {
    format!(
        "ref={:?};slot={:?};typ={};qual={:?};name={}",
        var.reference, var.index, var.typ, var.qualifier, var.name,
    )
}

/// Unified Div/Rem handler for both `add_op` and `reduce_op`.
///
/// Dispatches based on operand types:
/// - Vec operands recurse element-wise, preserving witness caching for each element
/// - VPoly/Uni polynomial divisions use witness Vars + cache
/// - Polynomial-like dividends divided by scalar-like divisors use slot-wise field division
/// - Non-polynomial Div uses slot-wise field division
/// - Remainder by scalar and unsupported MLE polynomial division remain `panic!`
///
/// Polynomial divisions use a canonical operand-content key in `div_wit`
/// before emitting identity rows, and insert after emission. This ensures
/// Div+Rem on equivalent named operands share witnesses across closures.
pub fn div_rem_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &HOp<C>,
    b: &HOp<C>,
    is_rem: bool,
    cache_witness: bool,
) {
    let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, a);
    let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, b);
    div_rem_op_inner(ctx, target, &a_src, &b_src, is_rem, cache_witness);
}

pub(crate) fn div_rem_op_inner<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    target: &Var,
    a: &PolySource<C>,
    b: &PolySource<C>,
    is_rem: bool,
    cache_witness: bool,
) {
    match (a.typ(), b.typ()) {
        (ATyp::Vec(_, na), ATyp::Vec(_, nb)) if na == nb => {
            for i in 0..*na {
                let t_i = target.with_index(i).unwrap();
                let a_elem = a.at_index(i).unwrap();
                let b_elem = b.at_index(i).unwrap();
                div_rem_op_inner(ctx, &t_i, &a_elem, &b_elem, is_rem, cache_witness);
            }
        }
        (ATyp::Vec(_, na), _) if PolySource::<C>::is_scalar_like(b.typ()) => {
            for i in 0..*na {
                let t_i = target.with_index(i).unwrap();
                let a_elem = a.at_index(i).unwrap();
                div_rem_op_inner(ctx, &t_i, &a_elem, b, is_rem, cache_witness);
            }
        }
        (_, ATyp::Vec(_, nb)) if PolySource::<C>::is_scalar_like(a.typ()) => {
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
                div_rem_op_inner(ctx, &t_i, a, &b_elem, false, cache_witness);
            }
        }
        _ if a.is_poly() && PolySource::<C>::is_scalar_like(b.typ()) => {
            if is_rem {
                panic!(
                    "Rem: polynomial-like remainder by scalar is undefined for {} % {} — type checker should prevent this",
                    a.typ(),
                    b.typ(),
                );
            }
            let b_broadcast = b.broadcast_scalar_to(a.typ());
            slot_wise_div(ctx.ideal, target, a.polys(), b_broadcast.polys());
        }
        _ if matches!(a.typ(), ATyp::Mle(_)) || matches!(b.typ(), ATyp::Mle(_)) => {
            super::uncovered_op(
                if is_rem {
                    "rem-mle-unsupported"
                } else {
                    "div-mle-unsupported"
                },
                target,
            );
        }
        _ if a.is_poly() && b.is_poly() => {
            let key = cache_witness.then(|| div_witness_key(ctx, a, b));
            if let Some((q_wit, r_wit)) = key
                .as_ref()
                .and_then(|key| ctx.builder.ns.div_wit.get(key).cloned())
            {
                let wit = if is_rem { &r_wit } else { &q_wit };
                link_to_witness(ctx.ideal, target, wit);
                return;
            }

            let (na, ma) = PolySource::<C>::poly_shape_static(a.typ()).unwrap();
            let (nb, mb) = PolySource::<C>::poly_shape_static(b.typ()).unwrap();
            if na != nb {
                panic!(
                    "{}: VPoly num_vars mismatch — dividend has n={} but divisor has n={}",
                    if is_rem { "Rem" } else { "Div" },
                    na,
                    nb,
                );
            }
            if na != 1 {
                super::uncovered_op(
                    if is_rem {
                        "rem-multivariate-vpoly"
                    } else {
                        "div-multivariate-vpoly"
                    },
                    target,
                );
            }
            if ma < mb {
                if is_rem {
                    let lifted = a.lift_to(&target.typ);
                    link_to_polys(ctx.ideal, target, lifted.polys);
                    return;
                }
                panic!(
                    "{}: dividend degree < divisor degree ({} < {})",
                    if is_rem { "Rem" } else { "Div" },
                    ma,
                    mb,
                );
            }
            if mb == 0 {
                // Divisor is degree 0 (constant): quotient has degree ma,
                // remainder is 0. Allocate r_wit with target.typ when
                // is_rem so slot counts match for link_to_witness.
                let r_typ = if is_rem {
                    target.typ.clone()
                } else {
                    ATyp::VPoly(na, 0)
                };
                let (q_wit, r_wit) = alloc_div_witness_pair(ctx, ATyp::VPoly(na, ma), r_typ);
                let a_idx = multi_indices(na, ma);
                let b_poly = &b.polys()[0];
                for (ka_pos, _k) in a_idx.iter().enumerate() {
                    let rhs: Polynomial<C::F> =
                        b_poly * &Polynomial::var(&q_wit.with_index(ka_pos).unwrap());
                    ctx.ideal.generating_set.push(&a.polys()[ka_pos] - &rhs);
                }
                for rf in r_wit.slots() {
                    ctx.ideal.generating_set.push(Polynomial::var(&rf));
                }
                let wit = if is_rem { &r_wit } else { &q_wit };
                link_to_witness(ctx.ideal, target, wit);
                if let Some(key) = key {
                    ctx.builder.ns.div_wit.insert(&key, &(q_wit, r_wit));
                }
                return;
            }

            let nr = na;
            let mq = ma - mb;
            let mr = mb - 1;

            let (q_wit, r_wit) =
                alloc_div_witness_pair(ctx, ATyp::VPoly(nr, mq), ATyp::VPoly(nr, mr));

            // Divisor-invertibility constraints are now emitted by
            // `IdealBuilder::build()` for arg polynomials (not per-division).
            // When the divisor is an arg polynomial, the constraint
            // `b_lead · lead_inv - 1 = 0` is already in the ideal's
            // generating set, allowing the GB to cancel `b_lead`.
            // For non-arg (derived/runtime) divisors, no invertibility
            // constraint exists — we cannot assume the leading coefficient
            // is non-zero.

            let a_idx = multi_indices(na, ma);
            let b_idx = multi_indices(nb, mb);
            let q_idx = multi_indices(nr, mq);
            let r_idx = multi_indices(nr, mr);

            debug_assert_eq!(
                a.polys().len(),
                a_idx.len(),
                "a_polys slot count mismatch: {} vs a_idx {}",
                a.polys().len(),
                a_idx.len()
            );
            debug_assert_eq!(
                b.polys().len(),
                b_idx.len(),
                "b_polys slot count mismatch: {} vs b_idx {}",
                b.polys().len(),
                b_idx.len()
            );

            for (ka_pos, k) in a_idx.iter().enumerate() {
                let mut rhs = Polynomial::<C::F>::zero();
                for (i_pos, ki) in b_idx.iter().enumerate() {
                    for (j_pos, kj) in q_idx.iter().enumerate() {
                        let sum: Vec<usize> =
                            ki.iter().zip(kj.iter()).map(|(x, y)| x + y).collect();
                        if sum == *k {
                            let qf = q_wit.clone().with_index(j_pos).unwrap();
                            rhs = &rhs + &(&b.polys()[i_pos] * &Polynomial::var(&qf));
                        }
                    }
                }
                if let Some(r_pos) = r_idx.iter().position(|rk| rk == k) {
                    let rf = r_wit.clone().with_index(r_pos).unwrap();
                    rhs = &rhs + &Polynomial::var(&rf);
                }
                ctx.ideal.generating_set.push(&a.polys()[ka_pos] - &rhs);
            }

            let wit = if is_rem { &r_wit } else { &q_wit };
            link_to_witness(ctx.ideal, target, wit);

            if let Some(key) = key {
                ctx.builder.ns.div_wit.insert(&key, &(q_wit, r_wit));
            }
        }
        _ if !a.is_poly() && !b.is_poly() => {
            if is_rem {
                panic!(
                    "Rem: non-polynomial remainder is undefined for {} % {} — type checker should prevent this",
                    a.typ(),
                    b.typ(),
                );
            }
            slot_wise_div(ctx.ideal, target, a.polys(), b.polys());
        }
        _ => {
            super::uncovered_op(
                if is_rem {
                    "rem-mixed-poly-nonpoly"
                } else {
                    "div-mixed-poly-nonpoly"
                },
                target,
            );
        }
    }
}

/// Slot-wise field division: emit `a[j] - b[j] * var[j] = 0` for each slot.
pub fn slot_wise_div<C: ArkConfig>(
    ideal: &mut Ideal<C>,
    target: &Var,
    a_polys: &[Polynomial<C::F>],
    b_polys: &[Polynomial<C::F>],
) {
    let target_slots = target.slots();
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
    fn test_add_op_vpoly_div_univariate_identity() {
        // VPoly(1,2) / VPoly(1,1) → VPoly(1,1).
        //   a has physical_len = 3 slots (a_0, a_1, a_2)
        //   b has physical_len = 2 slots (b_0, b_1)
        //   q_wit: VPoly(1,1), 2 slots (q_0, q_1)
        //   r_wit: VPoly(1,0), 1 slot  (r_0)
        // Canonical identity rows (from div_witnesses):
        //   k=[0] (total deg 0): a_0  -  (b_0·q_0 + r_0)
        //   k=[1] (total deg 1): a_1  -  (b_0·q_1 + b_1·q_0)
        //   k=[2] (total deg 2): a_2  -  b_1·q_1
        // link_to_witness emits 2 more rows: var(q_wit[j]) - var(ideal[j]), j=0,1.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 2), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Private);
        ideal.register(&var_b);

        let basis_before = ideal.generating_set.len();
        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 1), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 1),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // Recover the q_wit / r_wit Vars (minted by sentinel_var starting
        // at MAX and decrementing: q_wit=MAX, r_wit=MAX-1).
        let q_wit = Var::from_var(
            "__zippel::gb::div_q::0",
            petgraph::graph::NodeIndex::new(usize::MAX),
            ATyp::VPoly(1, 1),
            Qualifier::Local,
        );
        let r_wit = Var::from_var(
            "__zippel::gb::div_r::0",
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::VPoly(1, 0),
            Qualifier::Local,
        );

        // Per-slot input vars (typ computed by `with_slot`).
        let scl = |p: &Var, i: usize| p.clone().with_index(i).unwrap();
        // Per-slot witness vars. `div_witnesses` uses `wit.clone().with_index(j).unwrap()`
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
        let r0 = wit_slot(&r_wit, 0);

        // 3 identity rows + 2 linking rows. Invertibility constraints are
        // now emitted by build() for arg polynomials, not per-division.
        assert_eq!(
            ideal.generating_set.len() - basis_before,
            5,
            "expected 3 identity + 2 linking rows"
        );

        // Check identity rows exist in basis.
        let expected_k0 = &var_poly(&a0) - &(&(&var_poly(&b0) * &var_poly(&q0)) + &var_poly(&r0));
        let expected_k1 = &var_poly(&a1)
            - &(&(&var_poly(&b0) * &var_poly(&q1)) + &(&var_poly(&b1) * &var_poly(&q0)));
        let expected_k2 = &var_poly(&a2) - &(&var_poly(&b1) * &var_poly(&q1));
        for (lbl, expected) in [
            ("k0", &expected_k0),
            ("k1", &expected_k1),
            ("k2", &expected_k2),
        ] {
            assert!(
                ideal.generating_set.iter().any(|row| row == expected),
                "basis missing identity row {}",
                lbl
            );
        }

        // link_to_witness: pl[ideal[j]] = var(q_wit[j]) for j=0,1.
        assert_eq!(
            ideal.pl.get(&var.clone().with_index(0).unwrap()).cloned(),
            Some(var_poly(&q0)),
            "pl[ideal[0]] should alias q_wit[0]"
        );
        assert_eq!(
            ideal.pl.get(&var.clone().with_index(1).unwrap()).cloned(),
            Some(var_poly(&q1)),
            "pl[ideal[1]] should alias q_wit[1]"
        );

        // Linking rows: var(q_wit[j]) - var(ideal[j]).
        // link_to_witness uses `ideal.clone().with_index(j).unwrap()` (typ computed by with_slot).
        let r0_slot = var.clone().with_index(0).unwrap();
        let r1_slot = var.clone().with_index(1).unwrap();
        let link0 = &var_poly(&q0) - &var_poly(&r0_slot);
        let link1 = &var_poly(&q1) - &var_poly(&r1_slot);
        assert!(
            ideal.generating_set.iter().any(|row| row == &link0),
            "basis missing link row var_poly(q_wit[0]) - var_poly(ideal[0])"
        );
        assert!(
            ideal.generating_set.iter().any(|row| row == &link1),
            "basis missing link row var_poly(q_wit[1]) - var_poly(ideal[1])"
        );
        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "div_wit should have one (a,b) entry"
        );
    }

    #[test]
    fn test_add_op_vpoly_rem_univariate_identity() {
        // VPoly(1,2) % VPoly(1,1) → VPoly(1,0).
        // Same witnesses as the Div test, but link ideal to r_wit (1 slot).
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 2), Qualifier::Private);
        ideal.register(&_var_a);
        let _var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Private);
        ideal.register(&_var_b);

        let basis_before = ideal.generating_set.len();
        let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 0), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Rem,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
            ATyp::VPoly(1, 0),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // q_wit=MAX, r_wit=MAX-1 (fresh builder, counter starts at MAX).
        let r_wit = Var::from_var(
            "__zippel::gb::div_r::0",
            petgraph::graph::NodeIndex::new(usize::MAX - 1),
            ATyp::VPoly(1, 0),
            Qualifier::Local,
        );
        let scl = |p: &Var, i: usize| p.clone().with_index(i).unwrap();
        let _ = scl; // kept for parity with the Div test; not used here.
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        // r_wit slots: with_slot computes the correct type.
        let r0 = r_wit.clone().with_index(0).unwrap();

        // 3 identity rows + 1 linking row. Invertibility constraints are
        // now emitted by build() for arg polynomials, not per-division.
        assert_eq!(
            ideal.generating_set.len() - basis_before,
            4,
            "expected 3 identity + 1 linking row"
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
        assert_eq!(builder.ns.div_wit.len(), 1, "one div_wit entry after Rem");
    }

    #[test]
    fn test_add_op_div_then_rem_shares_witness() {
        // Both `a/b` and `a%b` on the same source-level operand pair share the
        // witness side-table. Second op should NOT emit new identity rows.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let _var_a = Var::from_node(NodeIndex::new(0), ATyp::VPoly(1, 2), Qualifier::Private);
        ideal.register(&_var_a);
        let _var_b = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 1), Qualifier::Private);
        ideal.register(&_var_b);

        let basis_before_div = ideal.generating_set.len();
        let _q_res = {
            let var = Var::from_node(NodeIndex::new(2), ATyp::VPoly(1, 1), Qualifier::Private);
            let op: GOp<ArkBls12_381> = Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
                ATyp::VPoly(1, 1),
            );
            builder.add_op(var.clone(), op, &mut ideal);
            var
        };
        let after_div = ideal.generating_set.len();

        let _r_res = {
            let var = Var::from_node(NodeIndex::new(3), ATyp::VPoly(1, 0), Qualifier::Private);
            let op: GOp<ArkBls12_381> = Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::VPoly(1, 2))),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::VPoly(1, 1))),
                ATyp::VPoly(1, 0),
            );
            builder.add_op(var.clone(), op, &mut ideal);
            var
        };
        let after_rem = ideal.generating_set.len();

        // Div added 3 identity + 2 linking = 5 rows. Invertibility is
        // now emitted by build() for arg polynomials, not per-division.
        assert_eq!(
            after_div - basis_before_div,
            5,
            "Div emitted 3 identity + 2 linking rows"
        );
        // Rem added ONLY the linking row (1 slot on VPoly(1,0)) — no new identity.
        assert_eq!(
            after_rem - after_div,
            1,
            "Rem on cached (a,b) should only emit 1 linking row, not re-emit identity"
        );
        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "div_wit unchanged after Rem (cached)"
        );
    }

    #[test]
    fn test_add_op_div_rem_shares_equivalent_named_derived_operands() {
        // PR #153 regression: two closure-local derived nodes can carry the
        // same named-source expression (`a * b - c`) while still having
        // distinct raw HOp refs. Div and Rem over those equivalent operands
        // should share a single witness pair.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;

        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        for (idx, name, typ) in [
            (0, "a", ATyp::VPoly(1, 1)),
            (1, "b", ATyp::VPoly(1, 1)),
            (2, "c", ATyp::VPoly(1, 2)),
            (3, "d", ATyp::VPoly(1, 1)),
        ] {
            let var = Var::from_var(name, NodeIndex::new(idx), typ, Qualifier::Public);
            ideal.register(&var);
        }

        let mk_ref = |idx, typ| mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(idx)), typ));

        let mut add_derived_operand = |mul_idx, sub_idx| {
            let mul_ref = Var::from_node(
                NodeIndex::new(mul_idx),
                ATyp::VPoly(1, 2),
                Qualifier::Private,
            );
            ideal.register(&mul_ref);
            builder.add_op(
                mul_ref.clone(),
                Op::Bin(
                    BinOp::Mul,
                    mk_ref(0, ATyp::VPoly(1, 1)),
                    mk_ref(1, ATyp::VPoly(1, 1)),
                    ATyp::VPoly(1, 2),
                ),
                &mut ideal,
            );

            let sub_ref = Var::from_node(
                NodeIndex::new(sub_idx),
                ATyp::VPoly(1, 2),
                Qualifier::Private,
            );
            ideal.register(&sub_ref);
            builder.add_op(
                sub_ref.clone(),
                Op::Bin(
                    BinOp::Sub,
                    mk_ref(mul_idx, ATyp::VPoly(1, 2)),
                    mk_ref(2, ATyp::VPoly(1, 2)),
                    ATyp::VPoly(1, 2),
                ),
                &mut ideal,
            );
            sub_ref
        };

        add_derived_operand(10, 11);
        add_derived_operand(12, 13);

        let q = Var::from_node(NodeIndex::new(20), ATyp::VPoly(1, 1), Qualifier::Private);
        builder.add_op(
            q,
            Op::Bin(
                BinOp::Div,
                mk_ref(11, ATyp::VPoly(1, 2)),
                mk_ref(3, ATyp::VPoly(1, 1)),
                ATyp::VPoly(1, 1),
            ),
            &mut ideal,
        );

        let r = Var::from_node(NodeIndex::new(21), ATyp::VPoly(1, 0), Qualifier::Private);
        builder.add_op(
            r,
            Op::Bin(
                BinOp::Rem,
                mk_ref(13, ATyp::VPoly(1, 2)),
                mk_ref(3, ATyp::VPoly(1, 1)),
                ATyp::VPoly(1, 0),
            ),
            &mut ideal,
        );

        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "equivalent named derived operands should share one div_wit entry"
        );
    }

    #[test]
    fn test_add_op_div_scalar_fallback() {
        // Scalar / Scalar → Scalar: legacy zip path (a - b·var(var) = 0).
        // Scalar fallback does not build a canonical polynomial witness key, so
        // no witness side-table entry is created.
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_b);

        let basis_before = ideal.generating_set.len();
        let var = Var::from_node(NodeIndex::new(2), ATyp::scalar(), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::scalar())),
            ATyp::scalar(),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        // Legacy zip emits exactly one row: a - b · var(ideal).
        assert_eq!(
            ideal.generating_set.len() - basis_before,
            1,
            "scalar fallback emits 1 row"
        );
        let var_poly = |p: &Var| Polynomial::<ark_bls12_381::Fr>::var(p);
        let expected = &var_poly(&var_a) - &(&var_poly(&var_b) * &var_poly(&var));
        assert!(
            ideal.generating_set.iter().any(|row| row == &expected),
            "scalar fallback row should be `a - b · var_poly(ideal)`"
        );
        assert_eq!(
            builder.ns.div_wit.len(),
            0,
            "div_wit stays empty on scalar Div"
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
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::vec_scalar(2), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::vec_scalar(2), Qualifier::Private);
        let op: GOp<ArkBls12_381> = Op::Bin(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), ATyp::scalar())),
            mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), ATyp::vec_scalar(2))),
            ATyp::vec_scalar(2),
        );

        let before = ideal.generating_set.len();
        builder.add_op(var.clone(), op, &mut ideal);

        assert_eq!(ideal.generating_set.len() - before, 2);
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
        assert_eq!(builder.ns.div_wit.len(), 0);
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
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Uni(2), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Private);
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

        assert_eq!(ideal.generating_set.len() - before, 3);
        assert_eq!(builder.ns.div_wit.len(), 0);
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
        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Mle(2), Qualifier::Private);
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

        assert_eq!(ideal.generating_set.len() - before, 4);
        assert_eq!(builder.ns.div_wit.len(), 0);
    }

    #[test]
    fn test_add_op_vector_poly_div_rem_propagates_witness_cache() {
        use crate::Var;
        use graph::Ref;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();
        let vec_typ = ATyp::Vec(Box::new(ATyp::VPoly(1, 2)), 2);
        // lub_div: VPoly(1,2) / VPoly(1,2) = VPoly(1, 2-2) = VPoly(1,0)
        let div_typ = ATyp::Vec(Box::new(ATyp::VPoly(1, 0)), 2);
        // lub_rem: VPoly(1,2) % VPoly(1,2) = VPoly(1, 2-1) = VPoly(1,1)
        let rem_typ = ATyp::Vec(Box::new(ATyp::VPoly(1, 1)), 2);
        for idx in 0..2 {
            ideal.register(&Var::from_node(
                NodeIndex::new(idx),
                vec_typ.clone(),
                Qualifier::Private,
            ));
        }

        builder.add_op(
            Var::from_node(NodeIndex::new(2), div_typ.clone(), Qualifier::Private),
            Op::Bin(
                BinOp::Div,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_typ.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_typ.clone())),
                div_typ,
            ),
            &mut ideal,
        );
        assert_eq!(builder.ns.div_wit.len(), 2);
        let after_div = ideal.generating_set.len();

        builder.add_op(
            Var::from_node(NodeIndex::new(3), rem_typ.clone(), Qualifier::Private),
            Op::Bin(
                BinOp::Rem,
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(0)), vec_typ.clone())),
                mk::<ArkBls12_381>(Op::Ref(Ref::new(NodeIndex::new(1)), vec_typ)),
                rem_typ,
            ),
            &mut ideal,
        );

        assert_eq!(builder.ns.div_wit.len(), 2);
        assert_eq!(
            ideal.generating_set.len() - after_div,
            4,
            "cached vector Rem should add one link row per slot per element \
             (2 elements × 2 slots per VPoly(1,1) = 4)"
        );
    }

    /// Test-local binomial coefficient C(n, k). Assumes `k <= n`.

    #[test]
    fn ideal_nested_div() {
        use lang::id::Tid;
        let src = r#"
            proto nd<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 2>, public c: Uni<F, 2>) where a == a {
                let q = (a / b) / c;
                verify(q == q)
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let tc = trans_clos_from_src_sized(src, &sizes);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Two div_witnesses calls: inner (a/b) and outer ((a/b)/c).
        // The builder caches one (a,b) entry and one ((a/b),c) entry in div_wit.
        assert_eq!(
            builder.ns.div_wit.len(),
            2,
            "nested div should have 2 div_wit entries (inner + outer), got {}",
            builder.ns.div_wit.len()
        );

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
    fn ideal_shared_div_rem_witnesses() {
        use lang::id::Tid;
        let src = r#"
            proto sdr<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 2>) where a == a {
                verify(a == b * (a / b) + (a % b))
            }"#;
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &4);
        let tc = trans_clos_from_src_sized(src, &sizes);
        let mut builder: IdealBuilder<ArkBls12_381> = IdealBuilder::new();
        let gr = builder.build(tc);

        // Single (a, b) pair → one div_witnesses call → 1 div_wit cache entry (q_wit, r_wit).
        assert_eq!(
            builder.ns.div_wit.len(),
            1,
            "shared div/rem should have 1 div_wit entry for (a, b), got {}",
            builder.ns.div_wit.len()
        );

        // Both div and rem share the same canonical identity — the key invariant.
        // The cached (q_wit, r_wit) pair is what links div and rem nodes.
        let (q_wit, r_wit) = builder
            .ns
            .div_wit
            .values()
            .into_iter()
            .next()
            .expect("div_wit should have exactly one (q_wit, r_wit) entry");
        assert!(
            q_wit.name.contains("div_q"),
            "q_wit should be named div_q..., got {:?}",
            q_wit.name
        );
        assert!(
            r_wit.name.contains("div_r"),
            "r_wit should be named div_r..., got {:?}",
            r_wit.name
        );

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
            "basis should not be empty after shared div/rem"
        );
    }

    #[test]
    fn test_add_op_div_scalar_slot_wise() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var_ideal = Var::from_node(NodeIndex::new(2), ATyp::scalar(), Qualifier::Private);
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

        let a_slot = var_a.with_index(0).unwrap();
        let b_slot = var_b.with_index(0).unwrap();
        let r_slot = var_ideal.with_index(0).unwrap();
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

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::scalar(), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::scalar(), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var_ideal = Var::from_node(NodeIndex::new(2), ATyp::scalar(), Qualifier::Private);
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

        let var_a = Var::from_node(NodeIndex::new(0), ATyp::Mle(2), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), ATyp::Mle(2), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Mle(2), Qualifier::Private);
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
    fn test_reduce_div_vpoly_uses_handle_div_rem() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let vec_t = ATyp::Vec(Box::new(ATyp::VPoly(1, 3)), 2);
        let var_v = Var::from_node(NodeIndex::new(0), vec_t.clone(), Qualifier::Private);
        ideal.register(&var_v);

        // lub_div: VPoly(1,3) / VPoly(1,3) = VPoly(1, 3-3) = VPoly(1,0)
        let var = Var::from_node(NodeIndex::new(1), ATyp::VPoly(1, 0), Qualifier::Private);
        ideal.register(&var);

        let op: GOp<ArkBls12_381> = Op::Reduce(
            BinOp::Div,
            mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), vec_t)),
        );
        builder.add_op(var.clone(), op, &mut ideal);

        assert!(
            !ideal.generating_set.is_empty(),
            "Reduce Div on VPoly should emit identity rows via handle_div_rem"
        );
    }

    #[test]
    fn poly_rem_smaller_dividend_passes_through() {
        use crate::Var;
        use lang::ast::BinOp;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let dividend_t = ATyp::Uni(1);
        let divisor_t = ATyp::Uni(3);
        let var_a = Var::from_node(NodeIndex::new(0), dividend_t.clone(), Qualifier::Private);
        let var_b = Var::from_node(NodeIndex::new(1), divisor_t.clone(), Qualifier::Private);
        ideal.register(&var_a);
        ideal.register(&var_b);

        let var = Var::from_node(NodeIndex::new(2), ATyp::Uni(2), Qualifier::Private);
        ideal.register(&var);

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

        assert_eq!(
            builder.ns.div_wit.len(),
            0,
            "pass-through remainder allocates no div_wit"
        );
        for i in 0..2 {
            let src = var_a.clone().with_index(i).unwrap();
            let dst = var.clone().with_index(i).unwrap();
            assert!(
                ideal
                    .generating_set
                    .iter()
                    .any(|row| row.contains(&src) && row.contains(&dst)),
                "pass-through remainder should bind source slot {i} to the ideal"
            );
        }
        let padded = var.with_index(2).unwrap();
        assert!(
            ideal.generating_set.iter().any(|row| row.contains(&padded)),
            "lifted pass-through remainder should constrain the padded high slot"
        );
    }
}
