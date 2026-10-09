//! Check op encoder: `assert_op`, `verify_op`, and `check_op`.

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
        check_op(ctx, &leaf);
    }
}

/// Verifier-side check encoder. The ideal generation is identical to the
/// relation's; `verify` also records what each leaf checks.
pub fn verify_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, _pr: &Var, exp: &HOp<C>) {
    let leaves = ctx.builder.collect_and_leaves(exp);
    for leaf in leaves {
        record_check(ctx, &leaf);
        check_op(ctx, &leaf);
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

#[cfg(test)]
mod tests {
    use super::super::test_helpers::trans_clos_from_src;
    use crate::ideal::IdealBuilder;
    use backend::ArkBls12_381;

    /// The checks `verify_op` records for the protocol `ex`, as `lhs == rhs`.
    fn checks_of(ex: &str) -> Vec<String> {
        IdealBuilder::<ArkBls12_381>::new()
            .build(trans_clos_from_src(ex))
            .checks
            .iter()
            .map(|c| format!("{} == {}", c.lhs, c.rhs))
            .collect()
    }

    #[test]
    fn checks_record_each_conjunct_of_each_verify() {
        let ex = r#"
            proto conjuncts<F: Field>(witness a: F, witness b: F) where a == b {
                let r = random<F>;
                x <- a * r;
                y <- b * r;
                u <- a * x;
                v <- b * y;
                verify(x == y && u == v);
                verify(u == x)
            }"#;
        assert_eq!(checks_of(ex), ["x == y", "u == v", "u == x"]);
    }

    #[test]
    fn checks_record_each_coefficient_slot() {
        let ex = r#"
            proto slots<F: Field>(instance p: Poly<F, 1, 1>, instance q: Poly<F, 1, 1>) where p == q {
                verify(p == q)
            }"#;
        assert_eq!(checks_of(ex), ["p[0] == q[0]", "p[1] == q[1]"]);
    }

    #[test]
    fn a_checked_message_is_checked_against_one() {
        // `b` is a prover message: the verifier checks it as sent, not the
        // `==` the prover computed it with.
        let ex = r#"
            proto message<F: Field>(instance x: F, instance y: F) where x == y {
                b <- x == y;
                verify(b)
            }"#;
        assert_eq!(checks_of(ex), ["b == 1"]);
    }
}
