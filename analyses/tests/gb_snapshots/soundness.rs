//! Soundness snapshot trials: assert `SpecialSoundnessAnalysis::run()`
//! actually passes, then snapshot the search Gröbner basis for regression
//! detection.

use crate::common::{assert_named_snapshot, compile_to_dag, normalize_basis};
use analyses::soundness::SoundnessModel;
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
    /// The polynomial model to analyze in; `SymbolicGroup` for arguments.
    pub(crate) model: SoundnessModel,
    pub(crate) ignored: bool,
}

pub(crate) static SOUNDNESS_ENTRIES: LazyLock<Vec<SoundnessEntry>> = LazyLock::new(|| {
    vec![
        SoundnessEntry {
            name: "schnorr",
            zippel_path: "examples/schnorr/schnorr.zippel",
            sizes: &[],
            l_vec: &[2],
            model: SoundnessModel::Plain,
            ignored: false,
        },
        SoundnessEntry {
            name: "schnorr_3round",
            zippel_path: "examples/schnorr_3round/schnorr_3round.zippel",
            sizes: &[],
            l_vec: &[2, 2, 2],
            model: SoundnessModel::Plain,
            ignored: false,
        },
        SoundnessEntry {
            name: "cp",
            zippel_path: "examples/cp/cp.zippel",
            sizes: &[],
            l_vec: &[2],
            model: SoundnessModel::Plain,
            ignored: false,
        },
        SoundnessEntry {
            name: "okamoto",
            zippel_path: "examples/okamoto/okamoto.zippel",
            sizes: &[],
            l_vec: &[2],
            // Argument: extracts under binding w.r.t. {g, h}.
            model: SoundnessModel::SymbolicGroup,
            ignored: false,
        },
        SoundnessEntry {
            name: "okamoto_elgamal",
            zippel_path: "examples/okamoto_elgamal/okamoto_elgamal.zippel",
            sizes: &[],
            l_vec: &[2],
            model: SoundnessModel::Plain,
            ignored: false,
        },
        SoundnessEntry {
            name: "commitment_equality",
            zippel_path: "examples/commitment_equality/commitment_equality.zippel",
            sizes: &[],
            l_vec: &[2],
            model: SoundnessModel::SymbolicGroup,
            // Correctly unextractable even under binding: the protocol only
            // proves knowledge of r1 − r2 (a Schnorr on c1 − c2 = h·(r1−r2)),
            // so the declared witness x is genuinely not special-sound here.
            ignored: true,
        },
        SoundnessEntry {
            name: "pedersen_eq",
            zippel_path: "examples/pedersen_eq/pedersen_eq.zippel",
            sizes: &[],
            l_vec: &[2],
            model: SoundnessModel::SymbolicGroup,
            // Correctly unextractable even under binding: like
            // commitment_equality, it only proves knowledge of r1 − r2, so
            // the declared message witnesses m1/m2 are not special-sound.
            ignored: true,
        },
        SoundnessEntry {
            name: "cds",
            zippel_path: "examples/cds/cds.zippel",
            sizes: &[],
            l_vec: &[2],
            // Unit search ideal, independent of model — a separate modeling
            // issue (pre-existing, out of scope for symbolic group mode).
            model: SoundnessModel::SymbolicGroup,
            ignored: true,
        },
        SoundnessEntry {
            name: "r1cs_sigma",
            zippel_path: "examples/r1cs_sigma/r1cs_sigma.zippel",
            sizes: &[("N", 2), ("n", 1), ("m", 1)],
            // gamma appears quadratically, so three transcripts.
            l_vec: &[3],
            // Argument: extracts under binding w.r.t. {ck, h_base}. The
            // witness is bound only through the masked responses
            // `t_s = w + γ·r`; SymbolicGroupResponses keeps those responses
            // as explicit generators so the GB recovers `w` from two
            // transcripts (w = t_s − γ·r).
            model: SoundnessModel::SymbolicGroupResponses,
            ignored: false,
        },
        SoundnessEntry {
            name: "coin_proof",
            zippel_path: "examples/coin_proof/coin_proof.zippel",
            sizes: &[],
            l_vec: &[2],
            // Argument: extracts under binding w.r.t. {f, g, h, h1, h2}.
            // Plain mode exhausted memory; the split brings it well under.
            model: SoundnessModel::SymbolicGroup,
            ignored: false,
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
    let model = entry.model;

    let normalized = share::thread::run("gb-soundness", move || {
        let dag = compile_to_dag(&path, &sizes);
        let inputs = SpecialSoundnessAnalysis::build_inputs_with_model(&dag, l_vec, true, model)
            .map_err(|e| Failed::from(e.to_string()))?;
        let mut sa = SpecialSoundnessAnalysis::from_inputs(inputs, backend, true)
            .map_err(|e| Failed::from(e.to_string()))?;
        sa.run().map_err(|e| Failed::from(e.to_string()))?;
        Ok::<String, Failed>(normalize_basis(&sa.search_gb.polys))
    })
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
