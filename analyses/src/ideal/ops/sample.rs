//! Sample op encoder: a `random` or `challenge` sample is drawn again on the
//! values it excludes, so every run has it outside them. For a fresh `t`, the
//! generator is `t·∏ (r − s) − 1` over the excluded values `s`, or
//! `t·(r^n − 1) − 1` for the `n`-th roots of unity. Both products are monic in
//! the fresh sample `r`, so the generator never makes the ideal trivial. A `*`
//! sample needs no generator: `div`'s `known_nonzero` divides by it directly.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, ArkScalarOps, OpExclusion};
use lang::ast::Exclusion;

use crate::Var;
use crate::frontend::Polynomial;

use super::{EncodeCtx, PolySource};

/// Encodes sample `var`, drawn again on the values `exclusion` excludes.
pub(crate) fn sample_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    exclusion: Option<&OpExclusion<C>>,
) {
    let r = Polynomial::var(var);
    let one = Polynomial::lit(&C::FOps::one());
    let excluded = match exclusion {
        None | Some(Exclusion::Zero) => return,
        Some(Exclusion::Values(values)) => PolySource::ref_vars(values, &ctx.ideal.vars)
            .iter()
            .fold(one.clone(), |product, s| &product * &(&r - s)),
        Some(Exclusion::RootsOfUnity(n)) => {
            let mut power = r;
            power.pow(*n);
            &power - &one
        }
    };
    let name = ctx.builder.ns.next_name("excluded_inv");
    let t = Polynomial::var(&ctx.sentinel_var(&name, ATyp::scalar()));
    ctx.ideal.generating_set.push(&(&t * &excluded) - &one);
}
