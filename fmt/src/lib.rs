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

use lang::parser::parse_decls;

pub use style::{Indent, Style};

/// Formatter error.
#[derive(Debug)]
pub enum FormatError {
    /// Source has parse errors.
    Parse(Vec<lang::diagnostic::Diagnostic>),
}

impl std::fmt::Display for FormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FormatError::Parse(errs) => {
                write!(f, "parse errors: {}", errs.len())
            }
        }
    }
}

impl std::error::Error for FormatError {}

/// Format source text, returning the formatted output.
/// Returns Err on parse failure (no panic).
pub fn format_source(src: &str) -> Result<String, FormatError> {
    format_source_with_style(src, &Style::default())
}

/// Format source text using an explicit style.
pub fn format_source_with_style(src: &str, style: &Style) -> Result<String, FormatError> {
    let (decls, errors) = parse_decls(src);
    if !errors.is_empty() {
        return Err(FormatError::Parse(errors));
    }
    Ok(decl::format_decls(&decls, src, style))
}

/// Check if source is already formatted.
/// Returns Ok(()) if canonical, Err(diff) if not.
pub fn check(src: &str) -> Result<(), String> {
    let formatted = format_source(src).map_err(|e| e.to_string())?;
    if formatted == src {
        Ok(())
    } else {
        Err(formatted)
    }
}
