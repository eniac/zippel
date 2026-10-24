//! Helpers for tests across the workspace: Zippel source to a typed module or to graphs, failing
//! the test on any error.

use crate::{GraphError, Relations, UDags};
use backend::Backend;
use lang::ast::{TypedModule, UModule};
use lang::diagnostic::Severity;
use lang::id::Tid;
use share::Ctx;

/// `src` parsed, concretized at `sizes` and type-checked. A source without a protocol is
/// accepted (E0001), so tests can lower functions alone.
///
/// # Panics
/// On any other error, listing them.
#[track_caller]
pub fn parse_and_check(src: &str, sizes: &Ctx<Tid, usize>) -> TypedModule {
    let (module, diags) = UModule::parse(src);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == Severity::Error && d.code.as_deref() != Some("E0001"))
        .map(|d| d.summary.clone())
        .collect();
    assert!(
        errors.is_empty(),
        "errors parsing test source:\n{}",
        errors.join("\n")
    );
    let module = module
        .expect("a module")
        .concretize(sizes)
        .expect("concretizes");
    module.typecheck().unwrap_or_else(|diags| {
        let errors: Vec<_> = diags.iter().map(|d| d.summary.clone()).collect();
        panic!("errors type-checking test source:\n{}", errors.join("\n"))
    })
}

/// [`parse_and_check`], lowered with every relation.
///
/// # Errors
/// As [`UDags::lower`].
///
/// # Panics
/// As [`parse_and_check`].
#[track_caller]
pub fn lowered<C: Backend>(src: &str, sizes: &Ctx<Tid, usize>) -> Result<UDags<C>, GraphError> {
    UDags::lower(&parse_and_check(src, sizes), Relations::Lower)
}
