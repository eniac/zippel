//! Soundness snapshot trials: assert `SpecialSoundnessAnalysis::run()`
//! actually passes, then snapshot the search Gröbner basis for regression
//! detection.

use crate::common::{ANALYSIS_STACK_SIZE, assert_named_snapshot, compile_to_dag, normalize_basis};
use analyses::{GbBackendKind, SpecialSoundnessAnalysis};
use libtest_mimic::{Failed, Trial};
use std::path::PathBuf;
use std::sync::LazyLock;

/// A protocol exercised by the `soundness::*` trial group.
#[derive(Clone)]
pub(crate) struct SoundnessEntry {
    pub(crate) name: &'static str,
    pub(crate) zippel_path: &'static str,
    pub(crate) sizes: &'static [(&'static str, usize)],
    /// Special-soundness round parameters, one per challenge round.
    pub(crate) l_vec: &'static [usize],
    pub(crate) ignored: bool,
}

pub(crate) static SOUNDNESS_ENTRIES: LazyLock<Vec<SoundnessEntry>> = LazyLock::new(|| {
    vec![
        SoundnessEntry {
            name: "schnorr",
            zippel_path: "examples/schnorr/schnorr.zippel",
            sizes: &[],
            l_vec: &[2],
            ignored: false,
        },
        SoundnessEntry {
            name: "schnorr_3round",
            zippel_path: "examples/schnorr_3round/schnorr_3round.zippel",
            sizes: &[],
            l_vec: &[2, 2, 2],
            ignored: false,
        },
        SoundnessEntry {
            name: "cp",
            zippel_path: "examples/cp/cp.zippel",
            sizes: &[],
            l_vec: &[2],
            ignored: false,
        },
        SoundnessEntry {
            name: "okamoto",
            zippel_path: "examples/okamoto/okamoto.zippel",
            sizes: &[],
            l_vec: &[2],
            // Known: "No valid extractor for witness r: NoExtractor".
            ignored: true,
        },
        SoundnessEntry {
            name: "okamoto_elgamal",
            zippel_path: "examples/okamoto_elgamal/okamoto_elgamal.zippel",
            sizes: &[],
            l_vec: &[2],
            ignored: false,
        },
        SoundnessEntry {
            name: "commitment_equality",
            zippel_path: "examples/commitment_equality/commitment_equality.zippel",
            sizes: &[],
            l_vec: &[2],
            // Known: "No valid extractor for witness r1: NoExtractor".
            ignored: true,
        },
        SoundnessEntry {
            name: "pedersen_eq",
            zippel_path: "examples/pedersen_eq/pedersen_eq.zippel",
            sizes: &[],
            l_vec: &[2],
            // Known: "No valid extractor for witness m1:
            // NotVisible(- m2 + m1)".
            ignored: true,
        },
        SoundnessEntry {
            name: "cds",
            zippel_path: "examples/cds/cds.zippel",
            sizes: &[],
            l_vec: &[2],
            ignored: true,
        },
        SoundnessEntry {
            name: "coin_proof",
            zippel_path: "examples/coin_proof/coin_proof.zippel",
            sizes: &[],
            l_vec: &[2],
            ignored: true,
        },
    ]
});

fn run_soundness_snapshot(entry: &SoundnessEntry) -> Result<(), Failed> {
    let snap_name = format!("{}_soundness_search", entry.name);
    let backend = GbBackendKind::Singular;

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    let l_vec = entry.l_vec.to_vec();

    let normalized = std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let dag = compile_to_dag(&path, &sizes);
            let inputs = SpecialSoundnessAnalysis::build_inputs(&dag, l_vec, true)
                .map_err(|e| Failed::from(e.to_string()))?;
            let mut sa = SpecialSoundnessAnalysis::from_inputs(inputs, backend, true)
                .map_err(|e| Failed::from(e.to_string()))?;
            sa.run().map_err(|e| Failed::from(e.to_string()))?;
            Ok::<String, Failed>(normalize_basis(&sa.search_gb.polys))
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked")?;

    assert_named_snapshot(&snap_name, &normalized);
    Ok(())
}

/// Build the `soundness::*` trials.
pub(crate) fn trials(force_ignored: bool) -> Vec<Trial> {
    SOUNDNESS_ENTRIES
        .iter()
        .map(|entry| {
            let e = entry.clone();
            Trial::test(format!("soundness::{}", entry.name), move || {
                run_soundness_snapshot(&e)
            })
            .with_ignored_flag(entry.ignored || force_ignored)
        })
        .collect()
}
