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

use std::ops::Range;

use crate::ast::decl::UDecl;
use crate::ast::spanned::Spanned;
use crate::ast::{Exp, Exps};
use crate::id::Vid;

use super::{levenshtein, SemanticError};

/// Check variable scope in a declaration's body.
/// Returns a list of scope errors (empty if all variables are defined).
pub fn check_scope(decl: &UDecl) -> Vec<SemanticError> {
    let mut errors = Vec::new();

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
        .map(|a| (a.node.id.clone(), a.span.clone()))
        .collect();

    // Check the body based on declaration kind
    match &decl.body {
        crate::ast::Body::Proto { body, relation } => {
            check_exp_scope(relation, &initial_scope, &mut errors);
            if let Some(body) = body {
                check_exp_scope(body, &initial_scope, &mut errors);
            }
        }
        crate::ast::Body::Func { body } => {
            if let Some(body) = body {
                check_exp_scope(body, &initial_scope, &mut errors);
            }
        }
        crate::ast::Body::TypeAlias => {}
    }

    errors
}

/// Recursively check an expression for undefined variable references.
/// `scope` is the list of (name, definition_span) currently in scope.
fn check_exp_scope(
    exp: &Spanned<Exp<crate::ast::Size>>,
    scope: &[(Vid, Range<usize>)],
    errors: &mut Vec<SemanticError>,
) {
    match &exp.node {
        Exp::Var(name) => {
            if !scope.iter().any(|(n, _)| n == name) {
                // Find similar names in scope for "did you mean?" suggestions
                let similar: Vec<(Vid, Range<usize>)> = scope
                    .iter()
                    .filter(|(n, _)| {
                        let dist = levenshtein(&name.0, &n.0);
                        dist > 0 && dist <= 2
                    })
                    .map(|(n, s)| (n.clone(), s.clone()))
                    .collect();
                errors.push(SemanticError::UndefinedVariable {
                    name: name.clone(),
                    use_span: exp.span.clone(),
                    similar,
                });
            }
        }

        Exp::Lit(_) | Exp::Unit | Exp::Random(_, _) | Exp::Challenge(_, _) | Exp::Range(_) => {}

        Exp::App(_, args) => {
            check_exps_scope(args, scope, errors);
        }

        Exp::Interpolate(po, e) => {
            if let Some(p) = po {
                check_exp_scope(p, scope, errors);
            }
            check_exp_scope(e, scope, errors);
        }

        Exp::Poly(p) | Exp::Coef(p) | Exp::Mle(p) | Exp::Reduce(_, p) => {
            check_exp_scope(p, scope, errors);
        }

        Exp::Evaluate(p, _, ox) => {
            check_exp_scope(p, scope, errors);
            if let Some(x) = ox {
                check_exp_scope(x, scope, errors);
            }
        }

        Exp::Vec(es) => check_exps_scope(es, scope, errors),

        Exp::Bin(_, a, b) => {
            check_exp_scope(a, scope, errors);
            check_exp_scope(b, scope, errors);
        }

        Exp::Neg(a) => check_exp_scope(a, scope, errors),

        Exp::Map(body, var, iter) => {
            // The iterator is evaluated in the outer scope
            check_exp_scope(iter, scope, errors);
            // The body is evaluated with `var` in scope
            let mut inner_scope = scope.to_vec();
            inner_scope.push((var.clone(), exp.span.clone()));
            check_exp_scope(body, &inner_scope, errors);
        }

        Exp::Ram(a, b) => {
            check_exp_scope(a, scope, errors);
            check_exp_scope(b, scope, errors);
        }

        Exp::Pair(a, b) => {
            check_exp_scope(a, scope, errors);
            check_exp_scope(b, scope, errors);
        }

        Exp::Let(name, val, cont) => {
            // The value is evaluated in the outer scope
            check_exp_scope(val, scope, errors);
            // The continuation is evaluated with `name` in scope (if named)
            if let Some(cont) = cont {
                if let Some(name) = name {
                    let mut inner_scope = scope.to_vec();
                    inner_scope.push((name.clone(), exp.span.clone()));
                    check_exp_scope(cont, &inner_scope, errors);
                } else {
                    check_exp_scope(cont, scope, errors);
                }
            }
        }

        Exp::Log(name, val, cont) => {
            // The value is evaluated in the outer scope
            check_exp_scope(val, scope, errors);
            // The continuation is evaluated with `name` in scope
            if let Some(cont) = cont {
                let mut inner_scope = scope.to_vec();
                inner_scope.push((name.clone(), exp.span.clone()));
                check_exp_scope(cont, &inner_scope, errors);
            }
        }

        Exp::Assert(a, b) | Exp::Verify(a, b) => {
            check_exp_scope(a, scope, errors);
            check_exp_scope(b, scope, errors);
        }

        Exp::Fun(params, body) => {
            // Function parameters are in scope in the body
            let mut inner_scope = scope.to_vec();
            for p in params {
                inner_scope.push((p.clone(), exp.span.clone()));
            }
            check_exp_scope(body, &inner_scope, errors);
        }

        Exp::Record(fields) => {
            for (_, e) in fields.iter() {
                check_exp_scope(e, scope, errors);
            }
        }

        Exp::Proj(e, _) => check_exp_scope(e, scope, errors),

        Exp::SetRecord(e, _, val) => {
            check_exp_scope(e, scope, errors);
            check_exp_scope(val, scope, errors);
        }
    }
}

/// Check a list of expressions for scope errors.
fn check_exps_scope(
    exps: &Exps<crate::ast::Size>,
    scope: &[(Vid, Range<usize>)],
    errors: &mut Vec<SemanticError>,
) {
    for e in &exps.0 {
        check_exp_scope(e, scope, errors);
    }
}
