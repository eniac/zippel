//! Code suggestion types and constructors.
//!
//! `Suggestion` carries structured data (span, replacement text, applicability)
//! so that future `--fix` tooling can apply fixes mechanically. The constructor
//! helpers (`replace`, `insert_before`, `hint`) are generic — they don't know
//! about tokens, contexts, or any phase-specific logic. Any compiler phase can
//! use them to build suggestions.

use std::ops::Range;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Suggestion {
    pub message: String,
    /// Span to replace.
    pub span: Range<usize>,
    /// Replacement text for the span.
    pub replacement: String,
    /// Confidence level.
    pub applicability: Applicability,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Applicability {
    /// The fix is definitely correct (e.g. missing `)`).
    MachineApplicable,
    /// The fix might be wrong (e.g. edit-distance keyword suggestion).
    MaybeIncorrect,
}

// ── Constructors ───────────────────────────────────────────────────────

/// Replace the span's content with `replacement`.
/// Use when the found token is wrong (e.g. `=>` should be `->`).
pub fn replace(span: &Range<usize>, msg: &str, replacement: &str) -> Suggestion {
    Suggestion {
        message: msg.to_string(),
        span: span.clone(),
        replacement: replacement.to_string(),
        applicability: Applicability::MachineApplicable,
    }
}

/// Insert `text` before the found token (zero-width span at span.start).
/// Use when a token is missing before the cursor position.
pub fn insert_before(span: &Range<usize>, msg: &str, text: &str) -> Suggestion {
    Suggestion {
        message: msg.to_string(),
        span: span.start..span.start,
        replacement: text.to_string(),
        applicability: Applicability::MachineApplicable,
    }
}

/// Hint without a mechanical fix — the user must provide missing content.
/// Use when the error is clear but can't be auto-fixed (e.g. missing type).
pub fn hint(span: &Range<usize>, msg: &str) -> Suggestion {
    Suggestion {
        message: msg.to_string(),
        span: span.clone(),
        replacement: String::new(),
        applicability: Applicability::MaybeIncorrect,
    }
}
