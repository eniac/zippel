//! Parse error conversion — `Rich` → `Diagnostic`.
//!
//! Chumsky's native `Rich` error type is used directly. `rich_to_diagnostic`
//! converts a borrowed `Rich` into an owned `Diagnostic` while the source is
//! still available, following rustc's generic syntax-diagnostic convention:
//! the summary states `expected …, found …`; the primary label repeats only
//! `expected …`.

#[cfg(test)]
mod tests;

use chumsky::error::RichPattern;

use super::RichError;
use super::label::Context;
use crate::diagnostic::{Diagnostic, Phase, SecondaryLabel};

/// Convert a chumsky `Rich` error directly into a `Diagnostic`.
///
/// Called while the source-backed `Rich` error is still valid (before
/// `parse_decls` returns), so token formatting borrows from the source.
pub(super) fn rich_to_diagnostic(e: &RichError<'_>) -> Diagnostic {
    let span = e.span().into_range();
    let found = e
        .found()
        .map(|token| format!("'{token}'"))
        .unwrap_or_else(|| "end of input".to_string());
    let expected = format_expected(&e.expected().map(ToString::to_string).collect::<Vec<_>>());
    let secondary_labels = innermost_context_label(e);

    let summary = format!("expected {expected}, found {found}");
    let primary_label = format!("expected {expected}");

    Diagnostic::error(Phase::Parse, span, &summary)
        .primary_label(&primary_label)
        .secondary_labels(secondary_labels)
}

/// Format the expected-token list from chumsky `RichPattern` display strings.
///
/// - 0 items: `something else`
/// - 1 item: the item
/// - 2 items: `a or b`
/// - 3–5 items: `one of a, b, c`
/// - >5 items: first five followed by `, ...`
fn format_expected(items: &[String]) -> String {
    match items.len() {
        0 => "something else".to_string(),
        1 => items[0].clone(),
        2 => format!("{} or {}", items[0], items[1]),
        n if n <= 5 => format!("one of {}", items.join(", ")),
        _ => format!("one of {}, ...", items[..5].join(", ")),
    }
}

/// Extract at most one secondary label from the innermost known chumsky context.
///
/// `in_context` is called by `LabelledWith::go` after the inner parser runs,
/// so contexts are pushed innermost-first: `[Expression, Declaration]`.
/// We decode the **first** context that matches a known `Context` variant.
fn innermost_context_label(e: &RichError<'_>) -> Vec<SecondaryLabel> {
    e.contexts()
        .filter_map(|(pattern, span)| match pattern {
            RichPattern::Label(cow) => {
                let ctx = Context::try_from(cow.as_ref()).ok()?;
                let determiner = match ctx {
                    Context::GenericParams | Context::CallArgs => "these",
                    _ => "this",
                };
                Some(SecondaryLabel {
                    span: span.into_range(),
                    message: format!("while parsing {determiner} {ctx}"),
                })
            }
            _ => None,
        })
        .next()
        .map(|label| vec![label])
        .unwrap_or_default()
}
