//! Summary and label message generation for parse errors.

use super::super::label::Context;
use super::super::lexer::Token;
use super::suggestion::detect_keyword_suggestion;
use super::{Expected, ParseError};

/// Group a list of `Expected` into a user-friendly summary.
/// Instead of listing 20 expression-starting tokens, we say "an expression".
///
/// Uses the parser's **context stack** (set via `.labelled().as_context()`)
/// to determine the category, rather than analyzing the token list. This is
/// robust because the context is set at the parse point — no guessing from
/// output.
///
/// For short lists (≤3 tokens), we list them directly regardless of context,
/// since they're always readable. For long lists, the innermost context
/// determines the summary.
pub fn summarize_expected(
    expected: &[Expected],
    contexts: &[(Context, std::ops::Range<usize>)],
) -> String {
    if expected.is_empty() {
        return "something else".to_string();
    }

    // Format a single Expected as a user-friendly string.
    let fmt_one = |e: &Expected| -> String {
        match e {
            Expected::Terminal(t) => t.to_string(),
            Expected::Token(t) => format!("'{t}'"),
            Expected::EndOfInput => "end of input".to_string(),
        }
    };

    // Short lists — always readable, list directly.
    if expected.len() <= 3 {
        return expected.iter().map(fmt_one).collect::<Vec<_>>().join(", ");
    }

    // Long list — use the context stack to pick a category.
    // Search for the most specific category context (innermost-first).
    let has_ctx = |c: Context| contexts.iter().any(|(ctx, _)| *ctx == c);

    // Check for a closing delimiter in the expected list (e.g. ')', ']', '|}').
    // When present alongside operators/atoms, we append "or ')'" to the summary.
    let closer = expected.iter().find_map(|e| match e {
        Expected::Token(t @ (Token::RParen | Token::RBrack | Token::BarRBrace | Token::RBrace)) => {
            Some(format!("'{t}'"))
        }
        _ => None,
    });

    // Category contexts: check from most specific to least.
    // These contexts are pushed when the corresponding parser is entered.
    if has_ctx(Context::Kind) {
        return "a kind annotation".to_string();
    }
    if has_ctx(Context::Type) {
        return "a type".to_string();
    }
    if has_ctx(Context::WhereClause) {
        // Where-clause continuation: operators + maybe `==` + maybe `}`.
        let has_eqeq = expected.iter().any(|e| e.is_token(&Token::EqEq));
        let has_rbrace = expected.iter().any(|e| e.is_token(&Token::RBrace));
        let mut parts: Vec<&str> = vec![];
        if has_eqeq {
            parts.push("'=='");
        }
        parts.push("an operator");
        if has_rbrace {
            parts.push("'}'");
        }
        if parts.len() == 1 {
            return parts[0].to_string();
        }
        return format!("{} or {}", parts[0], parts[1..].join(" or "));
    }
    if has_ctx(Context::Expression) {
        // Expression context: either atom-start (many expr tokens)
        // or operator-continuation (operators + maybe `,` + maybe a closer).
        // Distinguish by checking if expression-atom keywords are present.
        let has_expr_atoms = expected.iter().any(|e| {
            matches!(
                e,
                Expected::Token(
                    Token::KwFun
                        | Token::KwPoly
                        | Token::KwCoef
                        | Token::KwMle
                        | Token::KwDot
                        | Token::KwReduce
                        | Token::KwPair
                        | Token::KwAssert
                        | Token::KwVerify
                        | Token::KwEval
                        | Token::KwInterpolate
                        | Token::KwRandom
                        | Token::KwChallenge
                        | Token::LBraceBar
                )
            )
        });
        if has_expr_atoms {
            // Atom-start: "an expression" (optionally with a closer).
            if let Some(c) = closer {
                return format!("an expression or {c}");
            }
            return "an expression".to_string();
        } else {
            // Operator-continuation: "an operator", plus `,` if inside a
            // call argument list, and a closer if present.
            let mut parts: Vec<String> = vec!["an operator".to_string()];
            if has_ctx(Context::CallArgs) {
                parts.push("','".to_string());
            }
            if let Some(c) = closer {
                parts.push(c);
            }
            if parts.len() == 1 {
                return parts[0].clone();
            }
            return format!("{} or {}", parts[0], parts[1..].join(" or "));
        }
    }

    // No category context found — list tokens, cap at 5 with "...".
    let quoted: Vec<String> = expected.iter().map(fmt_one).collect();
    if quoted.len() <= 5 {
        quoted.join(", ")
    } else {
        format!("{}, ...", quoted[..5].join(", "))
    }
}

// ── error_summary / error_label_msg ────────────────────────────────────

/// Build a user-friendly top-level summary message for the error.
pub(crate) fn error_summary(error: &ParseError) -> String {
    let found = error
        .found
        .as_ref()
        .map(|t| format!("unexpected '{t}'"))
        .unwrap_or_else(|| "unexpected end of input".to_string());

    // If we have context labels, mention what we were parsing.
    if let Some((label, _)) = error.contexts.first() {
        format!("{found} while parsing this {label}")
    } else if error.expected.is_empty() {
        found
    } else {
        format!(
            "{found}, expected {}",
            summarize_expected(&error.expected, &error.contexts)
        )
    }
}

/// Build the detailed label message for the error span.
pub(crate) fn error_label_msg(error: &ParseError) -> String {
    // Check if the found token is a misspelled keyword not already in expected.
    let suggestion = detect_keyword_suggestion(&error.found, &error.expected, &error.contexts);

    let found = error
        .found
        .as_ref()
        .map(|t| {
            if let Some(sug) = &suggestion {
                format!("found '{t}', there is a keyword with a similar name: `{sug}`")
            } else {
                format!("found '{t}'")
            }
        })
        .unwrap_or_else(|| "found end of input".to_string());

    // When we have a suggestion, skip the generic "expected ..." — it's
    // noise next to a specific keyword recommendation.
    if suggestion.is_some() || error.expected.is_empty() {
        found
    } else {
        format!(
            "{found}, expected {}",
            summarize_expected(&error.expected, &error.contexts)
        )
    }
}
