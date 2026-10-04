//! Check op encoders: `assert_op` and `verify_op`.

use backend::op::HasOpFactory;
use backend::{ABase, ATyp, ArkConfig, ArkScalarOps};
use graph::{HOp, Op};
use lang::ast::BinOp;

use crate::Var;
use crate::frontend::Polynomial;

use crate::ideal::{AndLeaf, Check};

use super::EncodeCtx;
use super::PolySource;
use super::bool::sides;

/// Prover-side assertion encoder. Traces `&&` chains through the graph
/// and asserts each leaf bool individually, avoiding a high-degree
/// product polynomial in the GB generating set.
///
/// With [`EncodeOptions::relation_asserts`](crate::ideal::EncodeOptions)
/// set, an `assert` outside it, written in a protocol body, encodes to
/// nothing.
pub fn assert_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, pr: &Var, exp: &HOp<C>) {
    if let Some(relation) = &ctx.builder.options().relation_asserts
        && !relation.contains(&pr.reference)
    {
        return;
    }
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        let required = required(ctx, &leaf);
        ctx.ideal.generating_set.extend(required);
    }
}

/// Verifier-side check encoder. The ideal generation is identical for
/// assert and verify; verify also records what each leaf checks, and with
/// [`EncodeOptions::separate_goals`](crate::ideal::EncodeOptions) puts what
/// it requires in the goals instead of the generating set.
pub fn verify_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    let separate = ctx.builder.options().separate_goals;
    for leaf in leaves {
        record_check(ctx, &leaf);
        let required = required(ctx, &leaf);
        if separate {
            ctx.ideal.goals.extend(required);
        } else {
            ctx.ideal.generating_set.extend(required);
        }
    }
}

/// Record what the `verify` leaf checks in `ideal.checks`: `lhs == rhs` per slot when
/// it is an `==`, or an element of one, and `b == 1` for any other bool.
fn record_check<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, leaf: &AndLeaf<C>) {
    let op = match leaf.exp.get() {
        Op::Ref(r, _) => ctx.builder.node_ops.get(r).cloned(),
        op => Some(op.clone()),
    };
    if let Some(Op::Bin(BinOp::Equ, a, b, _)) = op {
        let a_src = element(PolySource::from_ref_vars(&ctx.ideal.vars, &a), leaf.index);
        let b_src = element(PolySource::from_ref_vars(&ctx.ideal.vars, &b), leaf.index);
        ctx.ideal.checks.extend(sides(&a_src, &b_src));
    } else {
        let src = leaf_source(ctx, leaf);
        let one = Polynomial::lit(&C::FOps::one());
        let checks = src.polys.into_iter().map(|lhs| Check {
            lhs,
            rhs: one.clone(),
        });
        ctx.ideal.checks.extend(checks);
    }
}

/// Element `index` of `src`, or all of it.
fn element<C: ArkConfig>(src: PolySource<C>, index: Option<usize>) -> PolySource<C> {
    match index {
        Some(i) => src
            .at_index(i)
            .unwrap_or_else(|| panic!("check: no element {i} in {}", src.typ())),
        None => src,
    }
}

/// The polys of the bool `leaf` stands for.
fn leaf_source<C: ArkConfig + HasOpFactory>(
    ctx: &EncodeCtx<'_, C>,
    leaf: &AndLeaf<C>,
) -> PolySource<C> {
    element(
        PolySource::from_ref_vars(&ctx.ideal.vars, &leaf.exp),
        leaf.index,
    )
}

/// Shared core for `assert_op` / `verify_op`.
/// Reads the Bool operand's polys and requires each to equal 1: `b − 1`.
fn required<C: ArkConfig + HasOpFactory>(
    ctx: &EncodeCtx<'_, C>,
    leaf: &AndLeaf<C>,
) -> Vec<Polynomial<C::F>> {
    let src = leaf_source(ctx, leaf);
    match src.typ() {
        ATyp::Base(ABase::Bool) => {
            let one = Polynomial::lit(&C::FOps::one());
            src.polys.iter().map(|p| p - &one).collect()
        }
        _ => {
            panic!(
                "check: unsupported operand type {} (expected Bool)",
                src.typ()
            );
        }
    }
}
