//! Size binding validator — checks that size variables used in types are
//! declared in the typevar list.
//!
//! Size variables are `Size::Var(Tid)` values that appear in:
//! - `Typ::Poly(_, _, N)` — polynomial degree
//! - `Typ::Vec(_, N)` — vector length
//! - `Typ::Fin(Range<N>)` — finite range
//! - `Range<N>` — range bounds in typevar kinds

use std::ops::Range;

use crate::ast::size::Size;
use crate::ast::spanned::Spanned;
use crate::ast::Sig;
use crate::id::Tid;
use crate::typ::Kind;
use crate::typ::{GTyp, Typ};

use super::SemanticError;

/// Check that all size variables used in a signature's types are declared
/// in the typevar list.
pub fn check_size_binding(sig: &Sig<Size>) -> Vec<SemanticError> {
    let mut errors = Vec::new();

    // Collect declared typevar names
    let declared: Vec<Tid> = sig.typevars.node.ids();

    // Check size vars in argument types
    for arg in &sig.args.node.0 {
        collect_size_vars_in_typ(&arg.node.typ, &arg.span, &declared, &mut errors);
    }

    // Check size vars in return type
    if let Some(ret) = &sig.ret {
        collect_size_vars_in_typ(&ret.node, &ret.span, &declared, &mut errors);
    }

    // Check size vars in typevar kinds (e.g. Range bounds)
    for tv in &sig.typevars.node.0 {
        if let Kind::Range(r) = &tv.node.kind {
            collect_size_vars_in_size(&r.start, &declared, &mut errors);
            if let Some(step) = &r.step {
                collect_size_vars_in_size(step, &declared, &mut errors);
            }
            if let Some(end) = &r.end {
                collect_size_vars_in_size(end, &declared, &mut errors);
            }
        }
    }

    errors
}

/// Collect all `Size::Var` names used in a type and check they're declared.
/// `span` is the span of the enclosing type expression — `Size` values inside
/// types don't carry their own spans.
fn collect_size_vars_in_typ(
    typ: &GTyp<Size>,
    span: &Range<usize>,
    declared: &[Tid],
    errors: &mut Vec<SemanticError>,
) {
    match typ {
        Typ::Poly(_, _, n) => {
            collect_size_vars_in_size(&Spanned::new(n.clone(), span.clone()), declared, errors);
        }
        Typ::Vec(inner, n) => {
            collect_size_vars_in_size(&Spanned::new(n.clone(), span.clone()), declared, errors);
            collect_size_vars_in_typ(&inner.node, &inner.span, declared, errors);
        }
        Typ::Base(_) | Typ::Unit => {}
        Typ::Fin(r) => {
            collect_size_vars_in_size(&r.start, declared, errors);
            if let Some(step) = &r.step {
                collect_size_vars_in_size(step, declared, errors);
            }
            if let Some(end) = &r.end {
                collect_size_vars_in_size(end, declared, errors);
            }
        }
        Typ::Record(fields) => {
            for (_, t) in fields.iter() {
                collect_size_vars_in_typ(&t.node, &t.span, declared, errors);
            }
        }
    }
}

/// Collect size variables from a `Spanned<Size>` and check they're declared.
fn collect_size_vars_in_size(
    size: &Spanned<Size>,
    declared: &[Tid],
    errors: &mut Vec<SemanticError>,
) {
    match &size.node {
        Size::Var(id) => {
            if !declared.contains(id) {
                errors.push(SemanticError::UnboundSizeVar {
                    name: id.clone(),
                    use_span: size.span.clone(),
                });
            }
        }
        Size::Lit(_) => {}
        Size::Add(a, b) | Size::Sub(a, b) | Size::Mul(a, b) | Size::Div(a, b) | Size::Pow(a, b) => {
            collect_size_vars_in_size(a, declared, errors);
            collect_size_vars_in_size(b, declared, errors);
        }
    }
}
