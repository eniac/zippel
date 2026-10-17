//! Relation purity check — proto relations must not contain
//! Challenge/Log/Verify constructs.

use std::ops::Range;

use crate::ast::{Effect, UExpr};
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

/// Check that a proto relation contains no impure constructs.
/// Returns one error per impure construct found.
pub fn check_purity(relation: &UExpr) -> Vec<Diagnostic> {
    relation
        .root()
        .effects()
        .filter_map(|(effect, span)| {
            let construct = match effect {
                Effect::Challenge => "challenge",
                Effect::Log => "log",
                Effect::Verify => "verify",
                Effect::Random => return None,
            };
            Some((span, construct))
        })
        .map(|(span, construct)| {
            ImpureRelation {
                span: span.clone(),
                construct: construct.to_string(),
                _note: (),
            }
            .build()
        })
        .collect()
}
