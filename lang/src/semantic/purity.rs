//! Relation purity check — proto relations must not contain
//! Challenge/Log/Verify constructs.

use std::ops::Range;

use crate::ast::{Exp, Stmt, UExpr, URef};
use crate::diagnostic::Diagnostic;
use crate::stack_guard;
use lang_derive::Diagnostic as DiagnosticDerive;

/// E0012: A proto relation contains impure constructs (Challenge/Log/Verify).
#[derive(DiagnosticDerive)]
#[diag(
    "impure construct `{$construct}` in proto relation",
    code = "E0012",
    error,
    Semantic
)]
struct ImpureRelation {
    #[span(label = "`{$construct}` is not allowed in a proto relation")]
    span: Range<usize>,
    construct: String,
    #[note("proto relations must be relation-pure (no challenge, log, or verify)")]
    _note: (),
}

/// Find all impure constructs (Challenge/Log/Verify) in an expression.
/// Returns (span, construct_name) for each occurrence.
fn find_impure_constructs(exp: URef<'_>) -> Vec<(Range<usize>, String)> {
    let mut results = Vec::new();
    collect_impure_constructs(exp, &mut results);
    results
}

#[stack_guard]
fn collect_impure_constructs(exp: URef<'_>, out: &mut Vec<(Range<usize>, String)>) {
    match exp.node() {
        Exp::Challenge(_, _) => out.push((exp.span().clone(), "challenge".to_string())),
        Exp::Random(_, x) => {
            if let Some(v) = x.as_ref().and_then(|x| x.values()) {
                collect_impure_constructs(exp.at(*v), out);
            }
        }
        Exp::Verify(_) => out.push((exp.span().clone(), "verify".to_string())),
        // A log statement is reported and ends the walk of its block, as before blocks.
        Exp::Block(stmts, tail) => {
            for stmt in stmts {
                if let Stmt::Log(..) = stmt.node {
                    out.push((stmt.span.clone(), "log".to_string()));
                    return;
                }
                collect_impure_constructs(exp.at(stmt.node.value()), out);
            }
            if let Some(tail) = tail {
                collect_impure_constructs(exp.at(*tail), out);
            }
        }
        Exp::Map(a, _, b) => {
            collect_impure_constructs(exp.at(*a), out);
            collect_impure_constructs(exp.at(*b), out);
        }
        Exp::Vec(v) => {
            for e in v.iter() {
                collect_impure_constructs(exp.at(e), out);
            }
        }
        Exp::Bin(_, a, b) => {
            collect_impure_constructs(exp.at(*a), out);
            collect_impure_constructs(exp.at(*b), out);
        }
        Exp::Neg(a) => collect_impure_constructs(exp.at(*a), out),
        Exp::Pair(a, b) => {
            collect_impure_constructs(exp.at(*a), out);
            collect_impure_constructs(exp.at(*b), out);
        }
        Exp::Ram(a, b) => {
            collect_impure_constructs(exp.at(*a), out);
            collect_impure_constructs(exp.at(*b), out);
        }
        Exp::Interpolate(None, e) => collect_impure_constructs(exp.at(*e), out),
        Exp::Interpolate(Some(p), e) => {
            collect_impure_constructs(exp.at(*p), out);
            collect_impure_constructs(exp.at(*e), out);
        }
        Exp::Coef(p) => collect_impure_constructs(exp.at(*p), out),
        Exp::Poly(p) => collect_impure_constructs(exp.at(*p), out),
        Exp::Mle(p) => collect_impure_constructs(exp.at(*p), out),
        Exp::Reduce(_, p) => collect_impure_constructs(exp.at(*p), out),
        Exp::Evaluate(p, _, ox) => {
            collect_impure_constructs(exp.at(*p), out);
            if let Some(x) = ox {
                collect_impure_constructs(exp.at(*x), out);
            }
        }
        Exp::App(_, args) => {
            for a in args.iter() {
                collect_impure_constructs(exp.at(a), out);
            }
        }
        Exp::Fun(_, body) => collect_impure_constructs(exp.at(*body), out),
        Exp::Record(fields) => {
            for (_, e) in fields.iter() {
                collect_impure_constructs(exp.at(*e), out);
            }
        }
        Exp::Proj(e, _) => collect_impure_constructs(exp.at(*e), out),
        _ => {}
    }
}

/// Check that a proto relation contains no impure constructs.
/// Returns one error per impure construct found.
pub fn check_purity(relation: &UExpr) -> Vec<Diagnostic> {
    find_impure_constructs(relation.root())
        .into_iter()
        .map(|(span, construct)| {
            ImpureRelation {
                span,
                construct,
                _note: (),
            }
            .build()
        })
        .collect()
}
