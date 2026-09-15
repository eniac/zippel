//! Knowledge snapshot trials. Reuses `completeness::COMPLETENESS_ENTRIES`
//! (same path/sizes shape; knowledge doesn't need soundness's `l_vec`).
//!
//! All knowledge tests are unconditionally ignored; no baseline snapshots
//! have ever been generated for this trial group. TODO: investigate and
//! either enable per-entry (like `completeness`/`soundness`) or record
//! the actual blocker.

use crate::common::{ANALYSIS_STACK_SIZE, assert_named_snapshot, compile_to_dag, normalize_basis};
use crate::completeness::{COMPLETENESS_ENTRIES, CompletenessEntry};
use analyses::{GbBackendKind, KnowledgeAnalysis};
use libtest_mimic::{Failed, Trial};
use std::path::PathBuf;

fn run_knowledge_snapshot(entry: &CompletenessEntry) -> Result<(), Failed> {
    let snap_basis = format!("{}_knowledge_basis", entry.name);
    let snap_rel = format!("{}_knowledge_relation", entry.name);
    let backend = GbBackendKind::Singular;

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();

    let (basis_norm, rel_norm) = std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let dag = compile_to_dag(&path, &sizes);
            let ka = KnowledgeAnalysis::from_input_with_backend(&dag, backend);
            let basis_norm = normalize_basis(&ka.basis.polys);
            let rel_norm = ka
                .relation_basis
                .as_ref()
                .map(|rb| normalize_basis(&rb.polys))
                .unwrap_or_default();
            (basis_norm, rel_norm)
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked");

    assert_named_snapshot(&snap_basis, &basis_norm);
    if !rel_norm.is_empty() {
        assert_named_snapshot(&snap_rel, &rel_norm);
    }
    Ok(())
}

/// Build the `knowledge::*` trials.
pub(crate) fn trials() -> Vec<Trial> {
    COMPLETENESS_ENTRIES
        .iter()
        .map(|entry| {
            let e = entry.clone();
            Trial::test(format!("knowledge::{}", entry.name), move || {
                run_knowledge_snapshot(&e)
            })
            .with_ignored_flag(true)
        })
        .collect()
}
