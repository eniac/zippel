//! Check op encoder: `assert_op`, `verify_op`, and `check_polys`.

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::{HOp, Op};
use lang::ast::BinOp;

use crate::Var;
use crate::frontend::Polynomial;
use crate::ideal::Check;

use super::EncodeCtx;
use super::PolySource;
use super::bool::sides;

/// Encoder for the `where` clause's `Assert`, the only one in the graph.
/// Traces `&&` chains through the graph and asserts each leaf bool
/// individually, avoiding a high-degree product polynomial in the GB
/// generating set. What the relation asserts is one of its
/// [`conditions`](crate::ideal::Ideal::conditions), not a generator.
pub fn assert_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        let polys = check_polys(ctx, &leaf);
        ctx.ideal.conditions.extend(polys);
    }
}

/// Verifier-side check encoder. Like `assert`, its polynomials go to
/// [`Ideal::conditions`](crate::ideal::Ideal::conditions), not the
/// generators; `verify` also records what each leaf checks.
pub fn verify_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        record_check(ctx, &leaf);
        let polys = check_polys(ctx, &leaf);
        ctx.ideal.conditions.extend(polys);
    }
}

/// Record what the `verify` leaf `exp` checks in `ideal.checks`: `lhs == rhs` per slot
/// when it is an `==`, and `b == 1` for any other bool.
fn record_check<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, exp: &HOp<C>) {
    let op = match exp.get() {
        Op::Ref(r, _) => ctx.builder.node_ops.get(r).cloned(),
        op => Some(op.clone()),
    };
    if let Some(Op::Bin(BinOp::Equ, a, b, _)) = op {
        let a_src = PolySource::from_ref_vars(&ctx.ideal.vars, &a);
        let b_src = PolySource::from_ref_vars(&ctx.ideal.vars, &b);
        ctx.ideal.checks.extend(sides(&a_src, &b_src));
    } else {
        let src = PolySource::from_ref_vars(&ctx.ideal.vars, exp);
        let one = Polynomial::lit(&C::FOps::one());
        let checks = src.polys.into_iter().map(|lhs| Check {
            lhs,
            rhs: one.clone(),
        });
        ctx.ideal.checks.extend(checks);
    }
}

/// Shared core for `assert_op` / `verify_op`: the Bool operand's polys, each
/// minus 1, which vanish exactly when the check holds.
fn check_polys<C: ArkConfig + HasOpFactory>(
    ctx: &EncodeCtx<'_, C>,
    exp: &HOp<C>,
) -> Vec<Polynomial<C::F>> {
    let src = PolySource::from_ref_vars(&ctx.ideal.vars, exp);
    match src.typ() {
        ATyp::Base(ABase::Bool) => {
            let one = Polynomial::lit(&C::FOps::one());
            src.polys.iter().map(|p| p - &one).collect()
        }
        _ => {
            panic!(
                "check_polys: unsupported operand type {} (expected Bool)",
                exp.typ()
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ideal::IdealBuilder;
    use crate::tests::parse_and_concretize;
    use crate::{QualifierPropagation, TransClos};
    use backend::ArkBls12_381;
    use graph::UDags;
    use share::{Ctx, unwrap};

    /// What the relation asserts is a condition, not a generator, and is
    /// not reported as a `verify` check.
    #[test]
    fn an_assert_is_a_condition() {
        let src = r#"
            proto p<F: Field>(witness x: F, instance y: F) where y == x * x {
                verify(y == y)
            }"#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        let mut relation = IdealBuilder::new().build(TransClos::relation(&g));
        relation.substitute_definitions();
        // The `==` itself is computed by the generators; asserting it is the
        // one condition.
        let [condition] = relation.conditions.as_slice() else {
            panic!("one condition, got {:?}", relation.conditions);
        };
        assert!(!relation.generating_set.contains(condition));
        assert!(relation.checks.is_empty());
    }
}
