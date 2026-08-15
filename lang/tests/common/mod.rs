//! Shared helpers for integration test files.
//!
//! Each test target (parser, semantic) compiles this module separately,
//! so not every function is used in every target. `#[allow(dead_code)]`
//! suppresses the resulting warnings.

use lang::ast::module::UModule;
use lang::diagnostic::{render_diagnostic, Severity};

/// Render all diagnostics for a source string, sorted by span.
/// Disables ANSI colors for clean snapshot text.
#[allow(dead_code)]
pub fn render_all(src: &str) -> String {
    yansi::disable();
    let (_, diags) = UModule::parse(src);
    diags
        .iter()
        .map(|d| render_diagnostic(d, "test.zippel", src))
        .collect::<Vec<_>>()
        .join("\n---\n")
}

/// Render only error diagnostics (filter out warnings).
#[allow(dead_code)]
pub fn render_errors(src: &str) -> String {
    yansi::disable();
    let (_, diags) = UModule::parse(src);
    diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| render_diagnostic(d, "test.zippel", src))
        .collect::<Vec<_>>()
        .join("\n---\n")
}

/// Render only warning diagnostics (filter out errors).
#[allow(dead_code)]
pub fn render_warnings(src: &str) -> String {
    yansi::disable();
    let (_, diags) = UModule::parse(src);
    diags
        .iter()
        .filter(|d| d.severity == Severity::Warning)
        .map(|d| render_diagnostic(d, "test.zippel", src))
        .collect::<Vec<_>>()
        .join("\n---\n")
}

/// Assert a named snapshot in `snap_dir` without the `expression:` header.
/// Follows the gb_snapshots convention: descriptive file names, no
/// test-file prefix.
macro_rules! assert_snap {
    ($snap_dir:expr, $name:expr, $value:expr) => {{
        let mut settings = insta::Settings::clone_current();
        settings.set_snapshot_path($snap_dir);
        settings.set_prepend_module_to_snapshot(false);
        settings.set_omit_expression(true);
        settings.bind(|| insta::assert_snapshot!($name, $value));
    }};
}
pub(crate) use assert_snap;
