//! Sample op encoder. A `random` or `challenge` sample is resampled while
//! excluded, so in every run the polynomial whose roots it excludes is
//! nonzero. Unlike a division, which may abort, a sample never takes an
//! excluded value, so the encoder states that as a generator, which every
//! analysis then uses: a division by the sample is then provably defined.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig, ArkScalarOps, OpExclusion};
use lang::ast::Exclusion;

use crate::Var;
use crate::frontend::Polynomial;

use super::{EncodeCtx, PolySource};

/// Encodes sample `var`, resampled while `exclusion`, if any, excludes it.
pub(crate) fn sample_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    exclusion: Option<&OpExclusion<C>>,
) {
    let Some(exclusion) = exclusion else {
        return;
    };
    let r = Polynomial::var(var);
    let one = Polynomial::lit(&C::FOps::one());
    let nonzero = match exclusion {
        Exclusion::Values(values) => PolySource::ref_vars(values, &ctx.ideal.vars)
            .iter()
            .fold(one.clone(), |product, s| &product * &(&r - s)),
        Exclusion::RootsOfUnity(n) => {
            let mut power = r;
            power.pow(*n);
            &power - &one
        }
    };
    // `t·p − 1` for what the exclusion makes nonzero, `p`, and a fresh `t`:
    // it holds exactly when `p ≠ 0`.
    let name = ctx.builder.ns.next_name("excluded_inv");
    let t = Polynomial::var(&ctx.sentinel_var(&name, ATyp::scalar()));
    ctx.ideal.generating_set.push(&(&t * &nonzero) - &one);
}
