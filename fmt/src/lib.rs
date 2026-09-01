//! Zippel formatter — canonical style source formatter.
//!
//! Produces canonical-formatted output from Zippel source text.
//! Round-trip safe: `parse(fmt(src)) == parse(src)` (AST equality).
//!
//! # Gap ownership convention
//!
//! Functions that return `Doc<'static>` (not `(TriviaGap, Doc<'static>)`)
//! own their leading gap — they consume it from the cursor and format
//! it internally. Callers must NOT advance the cursor past the
//! expression's start before calling these functions.
//!
//! Functions that return `(TriviaGap, Doc<'static>)` (e.g.
//! `format_exp`) do NOT own their leading gap — they return it to the
//! caller, who is responsible for formatting it with the appropriate
//! `gap_*` function or `format_gap` call.

mod ctx;
mod decl;
mod delim_list;
mod exp;
mod kind;
mod size;
mod style;
mod trivia;
mod typ;

use std::borrow::Cow;

use lang::diagnostic::Diagnostic;
use lang::parser::parse_decls;

pub use style::{Indent, Style};

/// Format source text, returning the formatted output.
/// Returns Err with parse diagnostics on parse failure (no panic).
pub fn format_source(src: &str) -> Result<String, Vec<Diagnostic>> {
    format_source_with_style(src, &Style::default())
}

/// Format source text using an explicit style.
/// Returns Err with parse diagnostics on parse failure.
pub fn format_source_with_style(src: &str, style: &Style) -> Result<String, Vec<Diagnostic>> {
    let (decls, errors) = parse_decls(src);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(decl::format_decls(&decls, src, style))
}

/// Normalize CRLF and lone-CR line endings to LF.
///
/// Formatter output is always LF. Windows checkouts materialize the corpus
/// with CRLF (`core.autocrlf=true`), so callers must compare against
/// normalized input or every file reads as unformatted. Borrows when the
/// input is already LF-only.
pub fn normalize_newlines(src: &str) -> Cow<'_, str> {
    if src.contains('\r') {
        Cow::Owned(src.replace("\r\n", "\n").replace('\r', "\n"))
    } else {
        Cow::Borrowed(src)
    }
}

/// Check if source is already formatted, ignoring line-ending style.
/// Returns `Ok(true)` if canonical, `Ok(false)` if not, `Err(diagnostics)` on parse error.
pub fn check(src: &str) -> Result<bool, Vec<Diagnostic>> {
    let formatted = format_source(src)?;
    Ok(formatted.as_str() == normalize_newlines(src).as_ref())
}
