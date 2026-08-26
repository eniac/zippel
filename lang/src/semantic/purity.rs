//! Relation purity check — proto relations must not contain
//! Challenge/Log/Verify/Assert constructs.

use std::ops::Range;

use crate::ast::spanned::Spanned;
use crate::ast::Exp;
use crate::diagnostic::Diagnostic;
use lang_derive::Diagnostic as DiagnosticDerive;

/// E0012: A proto relation contains impure constructs (Challenge/Log/Verify/Assert).
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
    #[note("proto relations must be relation-pure (no challenge, log, verify, or assert)")]
    _note: (),
}

/// Find all impure constructs (Challenge/Log/Verify/Assert) in an expression.
/// Returns (span, construct_name) for each occurrence.
fn find_impure_constructs(exp: &Spanned<Exp<crate::ast::Size>>) -> Vec<(Range<usize>, String)> {
    let mut results = Vec::new();
    collect_impure_constructs(exp, &mut results);
    results
}

fn collect_impure_constructs(
    exp: &Spanned<Exp<crate::ast::Size>>,
    out: &mut Vec<(Range<usize>, String)>,
) {
    match &exp.node {
        Exp::Challenge(_, _) => out.push((exp.span.clone(), "challenge".to_string())),
        Exp::Log(_, _, _) => out.push((exp.span.clone(), "log".to_string())),
        Exp::Verify(_) => out.push((exp.span.clone(), "verify".to_string())),
        Exp::Assert(_) => out.push((exp.span.clone(), "assert".to_string())),
        Exp::Let(_, val, cont) => {
            collect_impure_constructs(val, out);
            if let Some(c) = cont {
                collect_impure_constructs(c, out);
            }
        }
        Exp::Map(a, _, b) => {
            collect_impure_constructs(a, out);
            collect_impure_constructs(b, out);
        }
        Exp::Vec(v) => {
            for e in &v.0 {
                collect_impure_constructs(e, out);
            }
        }
        Exp::Bin(_, a, b) => {
            collect_impure_constructs(a, out);
            collect_impure_constructs(b, out);
        }
        Exp::Neg(a) => collect_impure_constructs(a, out),
        Exp::Pair(a, b) => {
            collect_impure_constructs(a, out);
            collect_impure_constructs(b, out);
        }
        Exp::Ram(a, b) => {
            collect_impure_constructs(a, out);
            collect_impure_constructs(b, out);
        }
        Exp::Interpolate(None, e) => collect_impure_constructs(e, out),
        Exp::Interpolate(Some(p), e) => {
            collect_impure_constructs(p, out);
            collect_impure_constructs(e, out);
        }
        Exp::Coef(p) => collect_impure_constructs(p, out),
        Exp::Poly(p) => collect_impure_constructs(p, out),
        Exp::Mle(p) => collect_impure_constructs(p, out),
        Exp::Reduce(_, p) => collect_impure_constructs(p, out),
        Exp::Evaluate(p, _, ox) => {
            collect_impure_constructs(p, out);
            if let Some(x) = ox {
                collect_impure_constructs(x, out);
            }
        }
        Exp::App(_, args) => {
            for a in &args.0 {
                collect_impure_constructs(a, out);
            }
        }
        Exp::Fun(_, body) => collect_impure_constructs(body, out),
        Exp::Record(fields) => {
            for (_, e) in fields.iter() {
                collect_impure_constructs(e, out);
            }
        }
        Exp::Proj(e, _) => collect_impure_constructs(e, out),
        _ => {}
    }
}

/// Check that a proto relation contains no impure constructs.
/// Returns one error per impure construct found.
pub fn check_purity(relation: &Spanned<Exp<crate::ast::Size>>) -> Vec<Diagnostic> {
    find_impure_constructs(relation)
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
