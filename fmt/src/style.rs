//! Canonical style configuration for the Zippel formatter.

/// Indentation style.
#[derive(Clone, Copy, Debug)]
pub enum Indent {
    Spaces(usize),
}

impl Default for Indent {
    fn default() -> Self {
        Indent::Spaces(4)
    }
}

/// Canonical formatting style. v1 uses only `Style::default()`.
/// This struct is the seam for future scalar config — growing it with
/// new scalar fields is additive.
#[derive(Clone, Copy, Debug)]
pub struct Style {
    /// Maximum line width before breaking. Default: 100.
    pub width: usize,
    /// Indentation style. Default: 4 spaces.
    pub indent: Indent,
    /// Maximum consecutive blank lines. Default: 1.
    pub max_blank_lines: usize,
}

impl Default for Style {
    fn default() -> Self {
        Self {
            width: 100,
            indent: Indent::default(),
            max_blank_lines: 1,
        }
    }
}

impl Style {
    /// Number of spaces for one indentation level.
    pub fn indent_width(&self) -> usize {
        match self.indent {
            Indent::Spaces(n) => n,
        }
    }
}
