//! Sample op encoder. A `random` or `challenge` sample is resampled while
//! excluded, so in every run the polynomial whose roots it excludes is
//! nonzero. The encoder records that polynomial in
//! [`Ideal::excluded`](crate::ideal::Ideal::excluded), and completeness makes
//! it a generator when a checked divisor mentions the sample.

use backend::op::HasOpFactory;
use backend::{ArkConfig, ArkScalarOps, OpExclusion};
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
        Exclusion::Zero => r,
        Exclusion::Values(values) => PolySource::ref_vars(values, &ctx.ideal.vars)
            .iter()
            .fold(one, |product, s| &product * &(&r - s)),
        Exclusion::RootsOfUnity(n) => {
            let mut power = r;
            power.pow(*n);
            &power - &one
        }
    };
    ctx.ideal.excluded.push((var.clone(), nonzero));
}
