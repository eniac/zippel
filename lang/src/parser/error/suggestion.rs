//! Keyword suggestion via edit distance.

use super::super::edit_distance::find_best_match;
use super::super::label::Context;
use super::super::lexer::Token;

/// Check if the found token is a misspelled keyword and suggest the correct one.
///
/// Only suggests when the expected list is long (≥4 items) — in that case,
/// `summarize_expected` produces a generic grouped message like "an operator
/// or ']'" that doesn't clearly show individual expected tokens. A "did you
/// mean" suggestion adds value there.
///
/// When the expected list is short (≤3), the error already lists specific
/// tokens (e.g. "expected 'where'"), so a suggestion would be redundant.
pub(super) fn detect_keyword_suggestion(
    found: &Option<Token<'static>>,
    expected: &[super::Expected],
    contexts: &[(Context, std::ops::Range<usize>)],
) -> Option<String> {
    // Only suggest when the expected list is long enough that
    // summarize_expected will produce a generic grouped message.
    if expected.len() < 4 {
        return None;
    }

    let found_text = found.as_ref().and_then(|t| match t {
        Token::Id(s) => Some(&**s),
        _ => None,
    })?;

    let in_decl = contexts.iter().any(|(c, _)| *c == Context::Declaration);
    let in_expr = contexts.iter().any(|(c, _)| *c == Context::Expression);
    let in_type = contexts.iter().any(|(c, _)| *c == Context::Type);
    let in_arg = contexts.iter().any(|(c, _)| *c == Context::Argument);
    let in_where_clause = contexts.iter().any(|(c, _)| *c == Context::WhereClause);

    let candidates = context_keywords(in_decl, in_expr, in_type, in_arg, in_where_clause);
    find_best_match(&candidates, found_text).map(|s| s.to_string())
}

/// Return keyword candidates appropriate for the current parser context.
///
/// Used by the edit-distance fallback in `detect_help` to avoid suggesting
/// keywords that make no sense in the current position (e.g. suggesting `let`
/// in a type context).
fn context_keywords(
    in_decl: bool,
    in_expr: bool,
    in_type: bool,
    in_arg: bool,
    in_where_clause: bool,
) -> Vec<&'static str> {
    // Type keywords are always available in type contexts.
    let type_kws = &[
        "Field", "Group", "Pairing", "Scalar", "Size", "Unit", "Fin", "Poly", "Uni", "Mle",
    ];

    // Expression keywords.
    let expr_kws = &[
        "fun",
        "for",
        "in",
        "interpolate",
        "poly",
        "eval",
        "coef",
        "mle",
        "dot",
        "reduce",
        "random",
        "challenge",
        "assert",
        "verify",
        "pair",
    ];

    // Declaration keywords.
    let decl_kws = &["let", "fn", "proto", "type", "where"];

    // Argument qualifier keywords.
    let qual_kws = &["instance", "witness", "extra", "uniform"];

    let mut kws = Vec::new();

    if in_type {
        kws.extend_from_slice(type_kws);
    }
    if in_expr {
        kws.extend_from_slice(expr_kws);
    }
    if in_decl {
        kws.extend_from_slice(decl_kws);
    }
    if in_arg {
        kws.extend_from_slice(qual_kws);
    }
    if in_where_clause {
        kws.push("where");
    }

    // If no context matched, provide all keywords as a safe fallback.
    if kws.is_empty() {
        kws.extend_from_slice(type_kws);
        kws.extend_from_slice(expr_kws);
        kws.extend_from_slice(decl_kws);
        kws.extend_from_slice(qual_kws);
    }

    kws
}
