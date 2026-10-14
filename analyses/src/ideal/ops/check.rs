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
/// generating set.
pub fn assert_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        let polys = check_polys(ctx, &leaf);
        ctx.ideal.generating_set.extend(polys);
    }
}

/// Verifier-side check encoder. The polynomials are the relation's, but they
/// go to [`Ideal::check_polys`](crate::ideal::Ideal::check_polys), not the
/// generators; `verify` also records what each leaf checks.
pub fn verify_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        record_check(ctx, &leaf);
        let polys = check_polys(ctx, &leaf);
        ctx.ideal.check_polys.extend(polys);
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
