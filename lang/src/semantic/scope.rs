//! Scope checker — verifies that all variable references are defined before use.
//!
//! This is a semantic check that runs after parsing but before type checking.
//! It walks the AST and collects:
//! - Variables bound by function arguments
//! - Variables bound by `let` and `log` expressions
//! - Variables bound by `map` comprehensions
//! - Variables bound by `fun` parameters
//!
//! Then verifies that every `Var(x)` reference has a binding in scope.

use std::collections::HashSet;
use std::ops::Range;

use crate::ast::decl::UDecl;
use crate::ast::{Exp, InScope, URef, Visit};
use crate::diagnostic::{Applicability, Diagnostic, Phase};
use crate::id::{Tid, Vid};

use super::levenshtein;

/// An undefined variable occurrence: the name, the use span, and a snapshot
/// of the scope at the point of use (for "did you mean?" suggestions).
struct UndefinedOccurrence {
    name: Vid,
    use_span: Range<usize>,
    scope: Vec<(Vid, Range<usize>)>,
}

/// E0009: Use of a variable before its definition (or undefined variable).
/// Uses the builder API because `similar` and `extra_uses` produce a variable
/// number of secondary labels.
fn undefined_variable(name: &Vid, use_spans: &[Range<usize>], similar: &[Vid]) -> Diagnostic {
    let primary_span = use_spans.first().cloned().unwrap_or(0..0);
    let mut d = Diagnostic::error(
        Phase::Semantic,
        primary_span.clone(),
        &format!("undefined variable `{name}`"),
    )
    .code("E0009")
    .primary_label(&format!("`{name}` is not defined in this scope"));

    // Secondary labels for additional use sites of the same name
    for s in use_spans.iter().skip(1) {
        d = d.secondary_label(s.clone(), &format!("`{name}` also used here"));
    }

    // Add "did you mean?" suggestion if there are similar names.
    // The suggestion points at the error site (primary_span) with the
    // replacement text, so no separate "defined here" label is needed —
    // the suggestion already tells the user which variable to use.
    if !similar.is_empty() {
        let names: Vec<String> = similar.iter().map(|n| format!("`{n}`")).collect();
        d = d.suggestion(
            &format!("did you mean {}?", names.join(", ")),
            primary_span,
            &similar[0].0,
            Applicability::MaybeIncorrect,
        );
    }

    d
}

/// E0014: A range bound names a value; range bounds are sizes.
fn value_in_range_bound(name: &Vid, use_span: Range<usize>, bound_at: Range<usize>) -> Diagnostic {
    Diagnostic::error(
        Phase::Semantic,
        use_span,
        &format!("a range bound is a size, but `{name}` is a value"),
    )
    .code("E0014")
    .primary_label(&format!("`{name}` is a value here, not a size"))
    .secondary_label(bound_at, &format!("`{name}` is bound here as a value"))
    .note("range bounds are sizes: literals, size parameters and `+ - * / ^`")
}

/// Check variable scope in a declaration's body.
/// Returns a list of scope errors (empty if all variables are defined).
pub fn check_scope(decl: &UDecl) -> Vec<Diagnostic> {
    // Collect argument variable names as the initial scope.
    // Typevars (F, N, etc.) are NOT included: they are not values. The parser
    // reads an uppercase name in an expression as a size (`Size::Var`); a
    // lowercase size parameter used as a value is reported undefined here.
    let initial_scope: Vec<(Vid, Range<usize>)> = decl
        .sig
        .args
        .node
        .0
        .iter()
        .map(|a| (a.node.id.node.clone(), a.node.id.span.clone()))
        .collect();

    // Collect all undefined variable occurrences, preserving first-seen order.
    let mut undefined: Vec<UndefinedOccurrence> = Vec::new();
    let mut errors = Vec::new();
    let sizes = super::size_params(decl);
    let mut check = |tree: URef<'_>| {
        check_exp_scope(tree, &initial_scope, &sizes, &mut undefined, &mut errors);
    };

    // Check the body based on declaration kind
    match &decl.body {
        crate::ast::Body::Proto { body, relation } => {
            check(relation.root());
            if let Some(body) = body {
                check(body.root());
            }
        }
        crate::ast::Body::Func { body } => {
            if let Some(body) = body {
                check(body.root());
            }
        }
        crate::ast::Body::TypeAlias => {}
    }

    // Group occurrences by name (preserving first-seen order) and emit one
    // diagnostic per name with "also used here" secondary labels.
    let mut seen: HashSet<Vid> = HashSet::new();
    for occ in &undefined {
        if !seen.insert(occ.name.clone()) {
            continue;
        }
        let use_spans: Vec<Range<usize>> = undefined
            .iter()
            .filter(|o| o.name == occ.name)
            .map(|o| o.use_span.clone())
            .collect();
        // Find similar names in scope at the first occurrence for "did you mean?"
        let similar: Vec<Vid> = occ
            .scope
            .iter()
            .filter(|(n, _)| {
                let dist = levenshtein(&occ.name.0, &n.0);
                dist > 0 && dist <= 2
            })
            .map(|(n, _)| n.clone())
            .collect();
        errors.push(undefined_variable(&occ.name, &use_spans, &similar));
    }

    errors
}

/// Check an expression for undefined variable references. `scope` is what is in scope around
/// it (name, definition span); `undefined` collects every undefined occurrence, which the
/// caller groups by name into one diagnostic each. A value named in a range bound, which must
/// be a size (one of `sizes`), is reported to `errors`.
fn check_exp_scope(
    exp: URef<'_>,
    scope: &[(Vid, Range<usize>)],
    sizes: &[&Tid],
    undefined: &mut Vec<UndefinedOccurrence>,
    errors: &mut Vec<Diagnostic>,
) {
    let mut in_scope = InScope::new();
    for visit in exp.walk() {
        match visit {
            Visit::Bind(x, _) => in_scope.bind(x, ()),
            Visit::Unbind(x) => in_scope.unbind(x),
            Visit::Enter(e) => match e.node() {
                Exp::Range(range) | Exp::Evaluate(_, Some(range), _) => {
                    for (name, at) in super::values_in_range(range, sizes) {
                        let bound_at = in_scope
                            .iter()
                            .filter(|(x, ())| x.node == name)
                            .last()
                            .map(|(x, ())| x.span.clone())
                            .or_else(|| {
                                scope
                                    .iter()
                                    .find(|(n, _)| *n == name)
                                    .map(|(_, s)| s.clone())
                            });
                        if let Some(bound_at) = bound_at {
                            errors.push(value_in_range_bound(&name, at.clone(), bound_at));
                        }
                    }
                }
                Exp::Var(name)
                    if in_scope.get(&name.node).is_none()
                        && !scope.iter().any(|(n, _)| n == &name.node) =>
                {
                    let bound = in_scope
                        .iter()
                        .map(|(x, ())| (x.node.clone(), x.span.clone()));
                    undefined.push(UndefinedOccurrence {
                        name: name.node.clone(),
                        use_span: name.span.clone(),
                        scope: scope.iter().cloned().chain(bound).collect(),
                    });
                }
                _ => {}
            },
            Visit::EnterStmt(_) | Visit::LeaveStmt(_) | Visit::Leave(_) => {}
        }
    }
}
