//! Parse error types and rendering.
//!
//! `ParseError` is a pure data struct. `rich_to_parse_error` converts
//! chumsky's `Rich` error into `ParseError`. `Diagnostic::from(ParseError)`
//! produces a renderable diagnostic.
//!
//! ## Error message style
//!
//! Messages are descriptive statements, never questions. The compiler states
//! what it found and what it suggests — it does not ask the user to confirm.
//! Follows rustc's diagnostics style guide: avoid "did you mean ...?", use
//! "there is a keyword with a similar name: `for`" instead.

mod convert;
mod help;
mod suggestion;
mod summarize;

#[cfg(test)]
mod tests;

use super::label::Context;
use super::lexer::Token;

pub(super) use convert::rich_to_parse_error;
#[cfg(test)]
pub(super) use summarize::summarize_expected;
pub(crate) use summarize::{error_label_msg, error_summary};

// ── Expected ───────────────────────────────────────────────────────────

/// A single expected token or terminal category, owned.
///
/// Distinguishes concrete tokens (e.g. `Token::LParen`) from terminal
/// labels (e.g. `Terminal::Identifier`) so that
/// `Expected::Token(Token::KwType)` (the `type` keyword) and
/// `Expected::Terminal(Terminal::Identifier)` don't collide.
///
/// Construct-level labels (`Context`) are NOT stored here — they appear
/// in `ParseError::contexts` instead, which tells what the parser was
/// doing when the error occurred.
///
/// Tokens are `Token<'static>` (owned) so that `Expected` can outlive the
/// source string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expected {
    /// A concrete token.
    Token(Token<'static>),
    /// A terminal-level label from `.labelled()` (e.g. `Terminal::Identifier`).
    Terminal(super::label::Terminal),
    /// End of input.
    EndOfInput,
}

impl Expected {
    /// Return `true` if this is a `Token` matching the given token.
    pub(super) fn is_token(&self, tok: &Token<'_>) -> bool {
        matches!(self, Expected::Token(t) if t == tok)
    }
}

impl std::fmt::Display for Expected {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expected::Token(t) => write!(f, "'{t}'"),
            Expected::Terminal(t) => write!(f, "{t}"),
            Expected::EndOfInput => write!(f, "end of input"),
        }
    }
}

// ── ParseError ─────────────────────────────────────────────────────────

/// A structured parse error with source span.
///
/// Convert to [`crate::diagnostic::Diagnostic`] for full source-rendered output via ariadne.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Byte span in the source text where the error occurred.
    pub span: std::ops::Range<usize>,
    /// The token that was found (`None` if at end of input).
    /// Owned (`Token<'static>`) so the error can outlive the source.
    pub found: Option<Token<'static>>,
    /// What was expected (typed: token vs label vs end-of-input).
    pub expected: Vec<Expected>,
    /// Parser contexts (context, span) — what the parser was doing when the
    /// error occurred, from chumsky `.labelled().as_context()` calls.
    pub contexts: Vec<(Context, std::ops::Range<usize>)>,
    /// Code suggestions with replacement text and applicability.
    pub suggestions: Vec<crate::diagnostic::Suggestion>,
}

// ── From<ParseError> for Diagnostic ────────────────────────────────────

impl From<ParseError> for crate::diagnostic::Diagnostic {
    fn from(err: ParseError) -> Self {
        use crate::diagnostic::{Diagnostic, Phase, SecondaryLabel, Severity};

        let summary = error_summary(&err);
        let primary_label = error_label_msg(&err);

        // Show only the innermost context as a secondary label.
        // Rustc doesn't stack multiple "while parsing" labels — one is enough.
        let secondary_labels: Vec<SecondaryLabel> = err
            .contexts
            .first()
            .map(|(ctx, span)| {
                vec![SecondaryLabel {
                    span: span.clone(),
                    message: format!("while parsing this {ctx}"),
                }]
            })
            .unwrap_or_default();

        Diagnostic {
            phase: Phase::Parse,
            severity: Severity::Error,
            span: err.span.clone(),
            summary,
            primary_label,
            secondary_labels,
            notes: vec![],
            suggestions: err.suggestions,
            code: None,
        }
    }
}

// ── Token category helper ──────────────────────────────────────────────

/// Extension trait for token category checks used in help detection.
pub(super) trait TokenExt {
    /// Is this a single-character punctuation/operator token?
    /// Used to distinguish identifiers from punctuation in help detection.
    fn is_punctuation(&self) -> bool;
}

impl TokenExt for Token<'_> {
    fn is_punctuation(&self) -> bool {
        matches!(
            self,
            Token::LParen
                | Token::RParen
                | Token::LBrace
                | Token::RBrace
                | Token::LBrack
                | Token::RBrack
                | Token::LAngle
                | Token::RAngle
                | Token::Comma
                | Token::Semi
                | Token::Colon
                | Token::Eq
                | Token::Dot
                | Token::Plus
                | Token::Minus
                | Token::Star
                | Token::Slash
                | Token::Caret
                | Token::Percent
        )
    }
}
