//! Check op encoder: `assert_op`, `verify_op`, and `check_op`.

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::HOp;

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;

/// Prover-side assertion encoder. Traces `&&` chains through the graph
/// and asserts each leaf bool individually, avoiding a high-degree
/// product polynomial in the GB generating set.
pub fn assert_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        check_op(ctx, &leaf);
    }
}

/// Verifier-side check encoder. The ideal generation is identical for
/// assert and verify.
pub fn verify_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        check_op(ctx, &leaf);
    }
}

/// Shared core for `assert_op` / `verify_op`.
/// Reads the Bool operand's polys and asserts each equals 1.
fn check_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, exp: &HOp<C>) {
    let src = PolySource::from_ref_vars(&ctx.ideal.vars, exp);
    match src.typ() {
        ATyp::Base(ABase::Bool) => {
            let one = Polynomial::lit(&C::FOps::one());
            for p in &src.polys {
                ctx.ideal.generating_set.push(p - &one);
            }
        }
        _ => {
            panic!(
                "check_op: unsupported operand type {} (expected Bool)",
                exp.typ()
            );
        }
    }
}
