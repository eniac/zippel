//! Relation purity check — proto relations must not contain
//! Challenge/Log/Verify constructs.

use std::ops::Range;

use crate::ast::{Exp, UExpr, URef};
use crate::diagnostic::Diagnostic;
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

/// Every impure construct (`challenge`, `verify`, a `<-` statement) in an expression, with its
/// span, in walk order.
fn find_impure_constructs(exp: URef<'_>) -> Vec<(Range<usize>, &'static str)> {
    let mut found = Vec::new();
    for e in exp.subexps() {
        match e.node() {
            Exp::Challenge(..) => found.push((e.span().clone(), "challenge")),
            Exp::Verify(_) => found.push((e.span().clone(), "verify")),
            Exp::Log(..) => found.push((e.span().clone(), "log")),
            _ => {}
        }
    }
    found
}

/// Check that a proto relation contains no impure constructs.
/// Returns one error per impure construct found.
pub fn check_purity(relation: &UExpr) -> Vec<Diagnostic> {
    find_impure_constructs(relation.root())
        .into_iter()
        .map(|(span, construct)| {
            ImpureRelation {
                span,
                construct: construct.to_string(),
                _note: (),
            }
            .build()
        })
        .collect()
}
