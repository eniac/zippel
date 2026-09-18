//! Unified diagnostic type and rendering.
//!
//! All compiler phases (parse, semantic, type) produce `Diagnostic`.
//! Phase-specific error types convert via standard `From` impls
//! (defined in their own modules).
//! Rendering uses ariadne, producing source-context reports.

mod suggestion;

pub use suggestion::{insert_before, replace, Applicability, Suggestion};

use std::ops::Range;

use ariadne::{Config, IndexType, Label, Report, ReportKind};

// ── Core types ─────────────────────────────────────────────────────────

/// A diagnostic report produced by any compiler phase.
///
/// Rendered via ariadne by [`render_diagnostic`].
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// Whether this report is a hard error or a non-fatal warning.
    pub severity: Severity,
    /// Which compiler phase produced this diagnostic.
    /// Used for deterministic error ordering.
    pub phase: Phase,
    /// Primary source span — the main location of the issue.
    pub span: Range<usize>,
    /// One-line summary (the "error: ..." header line).
    pub summary: String,
    /// Primary label message (rendered with `^^^` under `span`).
    pub primary_label: String,
    /// Secondary labels — additional spans with messages.
    pub secondary_labels: Vec<SecondaryLabel>,
    /// Notes — spanless context information, rendered as "Note: ...".
    pub notes: Vec<Note>,
    /// Code suggestions with replacement text and confidence.
    pub suggestions: Vec<Suggestion>,
    /// Stable error code (e.g. "E0001") for tooling and test filtering.
    /// `None` for diagnostics that don't warrant a code (e.g. generic parse errors).
    pub code: Option<String>,
}

/// The compiler phase that produced a [`Diagnostic`].
///
/// The derived `Ord` matches pipeline order (parse before semantic before
/// type), which is what `analyze()` sorts on to keep error output
/// deterministic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Phase {
    /// Raised while parsing `.zippel` source with the `pest` PEG grammar.
    Parse,
    /// Raised by post-parse well-formedness checks (scoping, declarations).
    Semantic,
    /// Raised by kind-directed type inference in `lang::typ`.
    Type,
}

/// How serious a [`Diagnostic`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Severity {
    /// Compilation cannot continue past this diagnostic.
    Error,
    /// Reported for review, but compilation continues.
    Warning,
}

/// An additional annotated span shown alongside a diagnostic's primary span.
///
/// Used to point at the other half of a conflict, e.g. the earlier
/// declaration that collides with the one being reported.
#[derive(Debug, Clone)]
pub struct SecondaryLabel {
    /// Byte range in the source file this label underlines.
    pub span: Range<usize>,
    /// Text rendered next to the underlined span.
    pub message: String,
}

/// A spanless piece of context attached to a diagnostic.
///
/// Rendered as a trailing "note: ..." line; use this rather than a
/// [`Suggestion`] when there is no concrete edit to propose.
#[derive(Debug, Clone)]
pub struct Note {
    /// Text of the note.
    pub message: String,
}

// ── Builder API ────────────────────────────────────────────────────────

impl Diagnostic {
    /// Start building an error diagnostic.
    pub fn error(phase: Phase, span: Range<usize>, summary: &str) -> Self {
        Diagnostic {
            severity: Severity::Error,
            phase,
            span,
            summary: summary.to_string(),
            primary_label: String::new(),
            secondary_labels: vec![],
            notes: vec![],
            suggestions: vec![],
            code: None,
        }
    }

    /// Start building a warning diagnostic.
    pub fn warning(phase: Phase, span: Range<usize>, summary: &str) -> Self {
        Diagnostic {
            severity: Severity::Warning,
            phase,
            span,
            summary: summary.to_string(),
            primary_label: String::new(),
            secondary_labels: vec![],
            notes: vec![],
            suggestions: vec![],
            code: None,
        }
    }

    /// Set the error code (e.g. "E0001").
    pub fn code(mut self, code: &str) -> Self {
        self.code = Some(code.to_string());
        self
    }

    /// Set the primary label message (rendered with `^^^` under the span).
    pub fn primary_label(mut self, label: &str) -> Self {
        self.primary_label = label.to_string();
        self
    }

    /// Add a secondary label at the given span.
    pub fn secondary_label(mut self, span: Range<usize>, message: &str) -> Self {
        self.secondary_labels.push(SecondaryLabel {
            span,
            message: message.to_string(),
        });
        self
    }

    /// Set all secondary labels at once.
    pub fn secondary_labels(mut self, labels: Vec<SecondaryLabel>) -> Self {
        self.secondary_labels = labels;
        self
    }

    /// Add a note (spanless context, rendered as "note: ...").
    pub fn note(mut self, message: &str) -> Self {
        self.notes.push(Note {
            message: message.to_string(),
        });
        self
    }

    /// Set all notes at once.
    pub fn notes(mut self, notes: Vec<Note>) -> Self {
        self.notes = notes;
        self
    }

    /// Add a code suggestion.
    pub fn suggestion(
        mut self,
        message: &str,
        span: Range<usize>,
        replacement: &str,
        applicability: Applicability,
    ) -> Self {
        self.suggestions.push(Suggestion {
            message: message.to_string(),
            span,
            replacement: replacement.to_string(),
            applicability,
        });
        self
    }

    /// Set all suggestions at once.
    pub fn suggestions(mut self, suggestions: Vec<Suggestion>) -> Self {
        self.suggestions = suggestions;
        self
    }
}

// ── Rendering ──────────────────────────────────────────────────────────

/// Render a single diagnostic as an ariadne report string.
///
/// `phase` is used for sorting in `analyze()`, not for rendering.
/// `code` is `None` for diagnostics without a code; when present, it could be
/// prepended to the summary (e.g. `error[E0001]: ...`).
pub fn render_diagnostic(diag: &Diagnostic, filename: &str, src: &str) -> String {
    let mut buf = Vec::new();
    let config = Config::new().with_index_type(IndexType::Byte);

    let (kind, color) = match diag.severity {
        Severity::Error => (
            ReportKind::Custom("error", ariadne::Color::Red),
            ariadne::Color::Red,
        ),
        Severity::Warning => (
            ReportKind::Custom("warning", ariadne::Color::Yellow),
            ariadne::Color::Yellow,
        ),
    };

    let mut builder = Report::build(kind, (filename.to_string(), diag.span.clone()))
        .with_config(config)
        .with_message(&diag.summary)
        .with_label(
            Label::new((filename.to_string(), diag.span.clone()))
                .with_message(&diag.primary_label)
                .with_color(color)
                .with_order(0),
        );

    // Secondary labels (yellow) — order 1 so they appear after the primary label
    for label in &diag.secondary_labels {
        builder = builder.with_label(
            Label::new((filename.to_string(), label.span.clone()))
                .with_message(&label.message)
                .with_color(ariadne::Color::Yellow)
                .with_order(1),
        );
    }

    // Notes — rendered as labels with "note:" prefix since ariadne
    // hardcodes "Note:" with a capital N. Order 2 so they appear after secondary
    // labels but before help/suggestions (matching rustc: labels → note → help).
    for note in &diag.notes {
        builder = builder.with_label(
            Label::new((filename.to_string(), diag.span.clone()))
                .with_message(format!("note: {}", note.message))
                .with_color(ariadne::Color::Fixed(115))
                .with_order(2),
        );
    }

    // Suggestions — rendered as labels with "help:" prefix since ariadne
    // hardcodes "Help:" with a capital H. Order 3 so they appear after notes.
    // The label points at the suggestion's own span (where the fix goes),
    // not the primary error span.
    for sugg in &diag.suggestions {
        builder = builder.with_label(
            Label::new((filename.to_string(), sugg.span.clone()))
                .with_message(format!("help: {}", sugg.message))
                .with_color(ariadne::Color::Fixed(115))
                .with_order(3),
        );
    }

    builder
        .finish()
        .write(
            ariadne::sources([(filename.to_string(), src.to_string())]),
            &mut buf,
        )
        .unwrap();

    String::from_utf8(buf).unwrap_or_default()
}
