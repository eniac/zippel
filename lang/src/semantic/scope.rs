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
use crate::ast::spanned::Spanned;
use crate::ast::{Exp, Exps};
use crate::diagnostic::{Applicability, Diagnostic, Phase};
use crate::id::Vid;

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
fn undefined_variable(
    name: &Vid,
    use_spans: &[Range<usize>],
    similar: &[(Vid, Range<usize>)],
) -> Diagnostic {
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
        let names: Vec<String> = similar.iter().map(|(n, _)| format!("`{n}`")).collect();
        d = d.suggestion(
            &format!("did you mean {}?", names.join(", ")),
            primary_span,
            &similar[0].0 .0,
            Applicability::MaybeIncorrect,
        );
    }

    d
}

/// Check variable scope in a declaration's body.
/// Returns a list of scope errors (empty if all variables are defined).
pub fn check_scope(decl: &UDecl) -> Vec<Diagnostic> {
    // Collect argument variable names as the initial scope.
    // Typevars (F, N, etc.) are NOT included — they're type-level identifiers
    // that appear in Size::Var positions, never as Exp::Var. The parser already
    // routes uppercase identifiers to Size::Var, so they can't reach this checker.
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

    // Check the body based on declaration kind
    match &decl.body {
        crate::ast::Body::Proto { body, relation } => {
            check_exp_scope(relation, &initial_scope, &mut undefined);
            if let Some(body) = body {
                check_exp_scope(body, &initial_scope, &mut undefined);
            }
        }
        crate::ast::Body::Func { body } => {
            if let Some(body) = body {
                check_exp_scope(body, &initial_scope, &mut undefined);
            }
        }
        crate::ast::Body::TypeAlias => {}
    }

    // Group occurrences by name (preserving first-seen order) and emit one
    // diagnostic per name with "also used here" secondary labels.
    let mut errors = Vec::new();
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
        let similar: Vec<(Vid, Range<usize>)> = occ
            .scope
            .iter()
            .filter(|(n, _)| {
                let dist = levenshtein(&occ.name.0, &n.0);
                dist > 0 && dist <= 2
            })
            .map(|(n, s)| (n.clone(), s.clone()))
            .collect();
        errors.push(undefined_variable(&occ.name, &use_spans, &similar));
    }

    errors
}

/// Recursively check an expression for undefined variable references.
/// `scope` is the list of (name, definition_span) currently in scope.
/// `undefined` collects occurrences for all undefined references; the caller
/// groups them by name to emit one diagnostic per name.
fn check_exp_scope(
    exp: &Spanned<Exp<crate::ast::Size>>,
    scope: &[(Vid, Range<usize>)],
    undefined: &mut Vec<UndefinedOccurrence>,
) {
    match &exp.node {
        Exp::Var(name) => {
            if !scope.iter().any(|(n, _)| n == &name.node) {
                undefined.push(UndefinedOccurrence {
                    name: name.node.clone(),
                    use_span: name.span.clone(),
                    scope: scope.to_vec(),
                });
            }
        }

        Exp::Lit(_) | Exp::Unit | Exp::Random(_, _) | Exp::Challenge(_, _) | Exp::Range(_) => {}

        Exp::App(_, args) => {
            check_exps_scope(args, scope, undefined);
        }

        Exp::Interpolate(po, e) => {
            if let Some(p) = po {
                check_exp_scope(p, scope, undefined);
            }
            check_exp_scope(e, scope, undefined);
        }

        Exp::Poly(p) | Exp::Coef(p) | Exp::Mle(p) | Exp::Reduce(_, p) => {
            check_exp_scope(p, scope, undefined);
        }

        Exp::Evaluate(p, _, ox) => {
            check_exp_scope(p, scope, undefined);
            if let Some(x) = ox {
                check_exp_scope(x, scope, undefined);
            }
        }

        Exp::Vec(es) => check_exps_scope(es, scope, undefined),

        Exp::Bin(_, a, b) => {
            check_exp_scope(a, scope, undefined);
            check_exp_scope(b, scope, undefined);
        }

        Exp::Neg(a) => check_exp_scope(a, scope, undefined),

        Exp::Map(body, var, iter) => {
            // The iterator is evaluated in the outer scope
            check_exp_scope(iter, scope, undefined);
            // The body is evaluated with `var` in scope
            let mut inner_scope = scope.to_vec();
            inner_scope.push((var.node.clone(), var.span.clone()));
            check_exp_scope(body, &inner_scope, undefined);
        }

        Exp::Ram(a, b) => {
            check_exp_scope(a, scope, undefined);
            check_exp_scope(b, scope, undefined);
        }

        Exp::Pair(a, b) => {
            check_exp_scope(a, scope, undefined);
            check_exp_scope(b, scope, undefined);
        }

        Exp::Let(name, val, cont) => {
            // The value is evaluated in the outer scope
            check_exp_scope(val, scope, undefined);
            // The continuation is evaluated with `name` in scope (if named)
            if let Some(cont) = cont {
                if let Some(name) = name {
                    let mut inner_scope = scope.to_vec();
                    inner_scope.push((name.node.clone(), name.span.clone()));
                    check_exp_scope(cont, &inner_scope, undefined);
                } else {
                    check_exp_scope(cont, scope, undefined);
                }
            }
        }

        Exp::Log(name, val, cont) => {
            // The value is evaluated in the outer scope
            check_exp_scope(val, scope, undefined);
            // The continuation is evaluated with `name` in scope
            if let Some(cont) = cont {
                let mut inner_scope = scope.to_vec();
                inner_scope.push((name.node.clone(), name.span.clone()));
                check_exp_scope(cont, &inner_scope, undefined);
            }
        }

        Exp::Assert(a, b) | Exp::Verify(a, b) => {
            check_exp_scope(a, scope, undefined);
            check_exp_scope(b, scope, undefined);
        }

        Exp::Fun(params, body) => {
            // Function parameters are in scope in the body
            let mut inner_scope = scope.to_vec();
            for p in params {
                inner_scope.push((p.node.clone(), p.span.clone()));
            }
            check_exp_scope(body, &inner_scope, undefined);
        }

        Exp::Record(fields) => {
            for (_, e) in fields.iter() {
                check_exp_scope(e, scope, undefined);
            }
        }

        Exp::Proj(e, _) => check_exp_scope(e, scope, undefined),

        Exp::SetRecord(e, _, val) => {
            check_exp_scope(e, scope, undefined);
            check_exp_scope(val, scope, undefined);
        }
    }
}

/// Check a list of expressions for scope errors.
fn check_exps_scope(
    exps: &Exps<crate::ast::Size>,
    scope: &[(Vid, Range<usize>)],
    undefined: &mut Vec<UndefinedOccurrence>,
) {
    for e in &exps.0 {
        check_exp_scope(e, scope, undefined);
    }
}
