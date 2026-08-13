//! Convert chumsky's `Rich` error into `ParseError`.

use chumsky::error::RichPattern;

use super::super::label::{Context, CtxError, Terminal};
use super::help::detect_help;
use super::{Expected, ParseError};

/// Convert a chumsky `CtxError` into a self-contained `ParseError`.
pub fn rich_to_parse_error(e: &CtxError) -> ParseError {
    let e = &e.0;
    // The error span is a byte-offset range (SimpleSpan).
    let span = e.span().into_range();

    // Capture parser contexts (from .labelled().as_context() calls) for secondary labels.
    let contexts: Vec<(Context, std::ops::Range<usize>)> = e
        .contexts()
        .filter_map(|(p, s)| match p {
            RichPattern::Label(cow) => Context::try_from(cow.as_ref())
                .ok()
                .map(|c| (c, s.into_range())),
            _ => None,
        })
        .collect();

    // Found token — convert borrowed token to owned (detaches from source).
    let found = e.found().map(|t| (*t).clone().into_owned());

    // Expected tokens — convert RichPattern to owned Expected.
    // Context labels never appear here (CtxError's label_with is a no-op
    // for Context), so no filtering needed.
    let expected: Vec<Expected> = e
        .expected()
        .filter_map(|p| match p {
            RichPattern::Token(t) => Some(Expected::Token((**t).clone().into_owned())),
            RichPattern::Label(cow) => Terminal::try_from(cow.as_ref())
                .ok()
                .map(Expected::Terminal),
            RichPattern::Identifier(_) => Some(Expected::Terminal(Terminal::Identifier)),
            RichPattern::EndOfInput => Some(Expected::EndOfInput),
            RichPattern::Any | RichPattern::SomethingElse => None,
            _ => None,
        })
        .collect();

    // Detect common error patterns and generate structured suggestions.
    let suggestions = detect_help(&found, &expected, &contexts, &span);

    ParseError {
        span,
        found,
        expected,
        contexts,
        suggestions,
    }
}
