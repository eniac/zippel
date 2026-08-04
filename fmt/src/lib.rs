//! Zippel formatter — canonical style source formatter.
//!
//! Produces canonical-formatted output from Zippel source text.
//! Round-trip safe: `parse(fmt(src)) == parse(src)` (AST equality).

pub mod doc;
pub mod paren;
pub mod style;
pub mod trivia;

use lang::parser::parse_decls;

pub use style::{Indent, Style};

/// Formatter error.
#[derive(Debug)]
pub enum FormatError {
    /// Source has parse errors.
    Parse(Vec<lang::parser::ParseError>),
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
    let (decls, errors) = parse_decls(src);
    if !errors.is_empty() {
        return Err(FormatError::Parse(errors));
    }
    let style = Style::default();
    let tokens = trivia::TokenStream::new(src);
    let comments = trivia::extract_comments(src);
    let line_starts = trivia::compute_line_starts(src);
    Ok(doc::format_decls(
        &decls,
        &tokens,
        &comments,
        &line_starts,
        src.len(),
        &style,
    ))
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
