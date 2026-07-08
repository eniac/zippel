//! Value literal op encoder: `value_op`.

use backend::op::HasOpFactory;
use backend::{ArkConfig, Value};

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;
use super::link_to_polys;

/// Encode `Op::Value(v)`: pattern-match on the `Value` variant via
/// `to_poly_value`, then bind each slot of `var` to the corresponding
/// literal polynomial. This lets literal constants act as real
/// polynomials in the basis (e.g. `let c = 7; verify(x == c)` folds
/// without needing an opaque `c` variable).
///
/// Supports Scalar / Bool / Index / Vec and the Vec* flavours.
/// Everything else (G1/G2/GT/Poly/Record) panics with `unsupported-value`.
pub fn value_op<C: ArkConfig + HasOpFactory>(ctx: &mut EncodeCtx<'_, C>, var: &Var, v: &Value<C>) {
    let polys_opt: Option<Vec<Polynomial<C::F>>> = match v {
        Value::Scalar(_)
        | Value::Bool(_)
        | Value::Index(_)
        | Value::Vec(_)
        | Value::VecBool(_)
        | Value::VecScalar(_)
        | Value::VecIndex(_) => Some(PolySource::to_poly_value(v)),
        _ => None,
    };
    match polys_opt {
        Some(polys) => {
            link_to_polys(ctx.ideal, var, polys);
        }
        None => {
            panic!(
                "ideal: operation has no polynomial-ideal treatment at unsupported-value for {}",
                var.verbose()
            );
        }
    }
}
