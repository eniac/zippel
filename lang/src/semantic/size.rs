//! Size binding validator — checks that size variables used in types are
//! declared in the typevar list.
//!
//! Size variables are `Size::Var(Tid)` values that appear in:
//! - `Typ::Poly(_, _, N)` — polynomial degree
//! - `Typ::Vec(_, N)` — vector length
//! - `Typ::Fin(Range<N>)` — finite range
//! - `Range<N>` — range bounds in typevar kinds

use std::collections::HashSet;
use std::ops::Range;

use crate::ast::size::Size;
use crate::ast::spanned::Spanned;
use crate::ast::Sig;
use crate::diagnostic::{Applicability, Diagnostic, Phase};
use crate::id::Tid;
use crate::typ::Kind;
use crate::typ::{GTyp, Typ};

/// E0003: Use of a size variable not declared in the typevar list.
/// Uses the builder API because `use_spans` produces a variable number of
/// secondary labels.
fn unbound_size_var(
    name: &Tid,
    use_spans: &[Range<usize>],
    typevar_span: &Range<usize>,
    is_empty: bool,
) -> Diagnostic {
    let primary_span = use_spans.first().cloned().unwrap_or(0..0);
    let replacement = if is_empty {
        format!("{name}: Size")
    } else {
        format!("{name}: Size, ")
    };
    let sugg_span = typevar_span.start..typevar_span.start;

    let mut d = Diagnostic::error(
        Phase::Semantic,
        primary_span,
        &format!("unbound size variable `{name}`"),
    )
    .code("E0003")
    .primary_label(&format!("`{name}` is not declared as a type variable"))
    .suggestion(
        &format!("add `{name}: Size` to the type variable list"),
        sugg_span,
        &replacement,
        Applicability::MachineApplicable,
    );

    for s in use_spans.iter().skip(1) {
        d = d.secondary_label(s.clone(), &format!("`{name}` also used here"));
    }

    d
}

/// Check that all size variables used in a signature's types are declared
/// in the typevar list.
pub fn check_size_binding(sig: &Sig<Size>) -> Vec<Diagnostic> {
    // Collect declared typevar names
    let declared: Vec<Tid> = sig.typevars.node.ids();
    let typevar_span = sig.typevars.span.clone();
    let is_empty = declared.is_empty();

    // Collect all unbound size var occurrences, preserving first-seen order.
    let mut unbound: Vec<(Tid, Range<usize>)> = Vec::new();

    // Check size vars in argument types
    for arg in &sig.args.node.0 {
        collect_size_vars_in_typ(&arg.node.typ, &arg.span, &declared, &mut unbound);
    }

    // Check size vars in return type
    if let Some(ret) = &sig.ret {
        collect_size_vars_in_typ(&ret.node, &ret.span, &declared, &mut unbound);
    }

    // Check size vars in typevar kinds (e.g. Range bounds)
    for tv in &sig.typevars.node.0 {
        if let Kind::Range(r) = &tv.node.kind {
            collect_size_vars_in_size(&r.start, &declared, &mut unbound);
            if let Some(step) = &r.step {
                collect_size_vars_in_size(step, &declared, &mut unbound);
            }
            if let Some(end) = &r.end {
                collect_size_vars_in_size(end, &declared, &mut unbound);
            }
        }
    }

    // Group occurrences by name (preserving first-seen order) and emit one
    // diagnostic per name with "also used here" secondary labels.
    let mut errors = Vec::new();
    let mut seen: HashSet<Tid> = HashSet::new();
    for (name, _) in &unbound {
        if !seen.insert(name.clone()) {
            continue;
        }
        let use_spans: Vec<Range<usize>> = unbound
            .iter()
            .filter(|(n, _)| n == name)
            .map(|(_, s)| s.clone())
            .collect();
        errors.push(unbound_size_var(name, &use_spans, &typevar_span, is_empty));
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
    unbound: &mut Vec<(Tid, Range<usize>)>,
) {
    match typ {
        Typ::Poly(_, _, n) => {
            collect_size_vars_in_size(&Spanned::new(n.clone(), span.clone()), declared, unbound);
        }
        Typ::Vec(inner, n) => {
            collect_size_vars_in_size(&Spanned::new(n.clone(), span.clone()), declared, unbound);
            collect_size_vars_in_typ(&inner.node, &inner.span, declared, unbound);
        }
        Typ::Base(_) | Typ::Unit => {}
        Typ::Fin(r) => {
            collect_size_vars_in_size(&r.start, declared, unbound);
            if let Some(step) = &r.step {
                collect_size_vars_in_size(step, declared, unbound);
            }
            if let Some(end) = &r.end {
                collect_size_vars_in_size(end, declared, unbound);
            }
        }
        Typ::Record(fields) => {
            for (_, t) in fields.iter() {
                collect_size_vars_in_typ(&t.node, &t.span, declared, unbound);
            }
        }
    }
}

/// Collect size variables from a `Spanned<Size>` and check they're declared.
fn collect_size_vars_in_size(
    size: &Spanned<Size>,
    declared: &[Tid],
    unbound: &mut Vec<(Tid, Range<usize>)>,
) {
    match &size.node {
        Size::Var(id) => {
            if !declared.contains(id) {
                unbound.push((id.clone(), size.span.clone()));
            }
        }
        Size::Lit(_) => {}
        Size::Add(a, b) | Size::Sub(a, b) | Size::Mul(a, b) | Size::Div(a, b) | Size::Pow(a, b) => {
            collect_size_vars_in_size(a, declared, unbound);
            collect_size_vars_in_size(b, declared, unbound);
        }
    }
}
