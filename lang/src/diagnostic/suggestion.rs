//! Code suggestion types and constructors.
//!
//! `Suggestion` carries structured data (span, replacement text, applicability)
//! so that future `--fix` tooling can apply fixes mechanically. The constructor
//! helpers (`replace`, `insert_before`) are generic — they don't know
//! about tokens, contexts, or any phase-specific logic. Any compiler phase can
//! use them to build suggestions.
//!
//! For message-only hints with no code change, use `Note` instead of `Suggestion`.

use std::ops::Range;

/// A machine-applicable code edit proposed by a diagnostic.
///
/// Structured rather than message-only so that `--fix` style tooling can
/// apply the replacement without re-parsing the rendered message.
#[derive(Debug, Clone)]
pub struct Suggestion {
    /// Human-readable description of the proposed edit.
    pub message: String,
    /// Span to replace.
    pub span: Range<usize>,
    /// Replacement text for the span.
    pub replacement: String,
    /// Confidence level.
    pub applicability: Applicability,
}

/// Confidence that applying a [`Suggestion`] yields correct source.
#[derive(Debug, Clone, Copy)]
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
