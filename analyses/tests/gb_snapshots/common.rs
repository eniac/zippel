//! Shared infrastructure for the GB snapshot test binary: DAG
//! compilation, snapshot assertion, and Singular-on-PATH detection.

use analyses::QualifierPropagation;
use analyses::frontend::Polynomial;
use backend::{ArkBls12_381, ArkConfig};
use graph::UDags;
use lang::ast::UModule;
use lang::diagnostic::Severity;
use lang::id::Tid;
use lang::typ::Qualifier;
use share::{Ctx, unwrap};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock;

type AnalysisDag = graph::Dag<ArkBls12_381, Qualifier>;
type F = <ArkBls12_381 as ArkConfig>::F;

pub(crate) const ANALYSIS_STACK_SIZE: usize = 256 * 1024 * 1024;

/// Snapshot directory, relative to this file's directory
/// (`analyses/tests/gb_snapshots/`) — resolves to
/// `analyses/tests/snapshots/gb_snapshots/`.
const SNAP_DIR: &str = "../snapshots/gb_snapshots";

fn build_sizes_ctx(sizes: &[(&str, usize)]) -> Ctx<Tid, usize> {
    let mut ctx = Ctx::new();
    for &(name, value) in sizes {
        ctx.insert(&Tid::new(name), &value);
    }
    ctx
}

/// Return `true` if the `Singular` binary is on `PATH`.
fn singular_available() -> bool {
    Command::new("Singular")
        .arg("-q")
        .arg("-c")
        .arg("ring r = (integer, 7), (x(1)), dp;")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
}

static SINGULAR_AVAILABLE: OnceLock<bool> = OnceLock::new();

pub(crate) fn singular() -> bool {
    *SINGULAR_AVAILABLE.get_or_init(singular_available)
}

/// Parse + concretize + build the analysis DAG.
#[track_caller]
pub(crate) fn compile_to_dag(path: &PathBuf, sizes: &[(&str, usize)]) -> AnalysisDag {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let (module, diags) = UModule::parse(&source);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    if !errors.is_empty() {
        panic!(
            "failed to parse {}: {}",
            path.display(),
            errors
                .iter()
                .map(|d| d.summary.clone())
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
    let module =
        module.unwrap_or_else(|| panic!("parse returned no module for {}", path.display()));
    let ctx = build_sizes_ctx(sizes);
    let concrete = module
        .concretize(&ctx)
        .unwrap_or_else(|e| panic!("failed to concretize {}: {e}", path.display()));
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(concrete));
    let proto = gs
        .protocols()
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("no protocol found in {}", path.display()));
    QualifierPropagation::from_dag(proto)
}

/// Normalize a GB for deterministic snapshot comparison:
/// sort polynomials by their Display string.
pub(crate) fn normalize_basis(polys: &[Polynomial<F>]) -> String {
    let mut rendered: Vec<String> = polys.iter().map(|p| format!("{p}")).collect();
    rendered.sort();
    rendered.join("\n")
}

/// Assert a snapshot with a custom name, bypassing insta's default naming.
pub(crate) fn assert_named_snapshot(snap_name: &str, value: &str) {
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path(SNAP_DIR);
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| {
        insta::assert_snapshot!(snap_name, value);
    });
}
