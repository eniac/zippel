#![cfg(test)]

use lang::ast::{CModule, UModule};
use lang::id::Tid;
use share::Ctx;

/// Parse source text and concretize with the given sizes.
/// Panics on parse or concretize errors (test-only).
#[track_caller]
pub fn parse_and_concretize(src: &str, sizes: &Ctx<Tid, usize>) -> CModule {
    let (module, diags) = UModule::parse(src);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == lang::diagnostic::Severity::Error)
        .collect();
    assert!(
        errors.is_empty(),
        "unexpected errors parsing test source:\n{}",
        errors
            .iter()
            .map(|d| d.summary.clone())
            .collect::<Vec<_>>()
            .join("\n")
    );
    module
        .expect("parse returned no module but no errors")
        .concretize(sizes)
        .expect("concretize failed")
}
