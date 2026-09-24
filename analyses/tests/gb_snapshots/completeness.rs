//! Completeness snapshot trials: assert `CompletenessAnalysis::run()`
//! actually passes, then snapshot the computed Gröbner basis for
//! regression detection.

use crate::common::{ANALYSIS_STACK_SIZE, assert_named_snapshot, compile_to_dag, normalize_basis};
use analyses::{CompletenessAnalysis, GbBackendKind};
use backend::ArkBls12_381;
use libtest_mimic::{Failed, Trial};
use std::path::PathBuf;
use std::sync::LazyLock;

/// A protocol exercised by the `completeness::*` (and `knowledge::*`)
/// trial group.
#[derive(Clone)]
pub(crate) struct CompletenessEntry {
    pub(crate) name: &'static str,
    pub(crate) zippel_path: &'static str,
    pub(crate) sizes: &'static [(&'static str, usize)],
    pub(crate) ignored: bool,
}

pub(crate) static COMPLETENESS_ENTRIES: LazyLock<Vec<CompletenessEntry>> = LazyLock::new(|| {
    vec![
        // --- Active ---
        CompletenessEntry {
            name: "sumcheck",
            zippel_path: "examples/sumcheck/sumcheck_full.zippel",
            sizes: &[("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "mle_sumcheck",
            zippel_path: "examples/mle_sumcheck/mle_sumcheck.zippel",
            sizes: &[("NUM_VARS", 3), ("MAX_DEGREE_CONST", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "kzg",
            zippel_path: "examples/kzg/kzg.zippel",
            sizes: &[("N", 2)],
            ignored: false,
        },
        CompletenessEntry {
            name: "membership",
            zippel_path: "examples/membership/membership.zippel",
            sizes: &[("N", 2), ("M", 2), ("S", 2)],
            ignored: false,
        },
        CompletenessEntry {
            name: "schnorr",
            zippel_path: "examples/schnorr/schnorr.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "schnorr_3round",
            zippel_path: "examples/schnorr_3round/schnorr_3round.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "cp",
            zippel_path: "examples/cp/cp.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "okamoto",
            zippel_path: "examples/okamoto/okamoto.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "okamoto_elgamal",
            zippel_path: "examples/okamoto_elgamal/okamoto_elgamal.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "commitment_equality",
            zippel_path: "examples/commitment_equality/commitment_equality.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "pedersen_eq",
            zippel_path: "examples/pedersen_eq/pedersen_eq.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "hyrax_pop",
            zippel_path: "examples/hyrax_pop/hyrax_pop.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "bccgp",
            zippel_path: "examples/bccgp/bccgp.zippel",
            sizes: &[("S", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "ipa",
            zippel_path: "examples/ipa/ipa.zippel",
            sizes: &[("S", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "ipa_weighted",
            zippel_path: "examples/ipa_weighted/ipa_weighted.zippel",
            sizes: &[("S", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "hyrax_ipa",
            zippel_path: "examples/hyrax_ipa/hyrax_ipa.zippel",
            sizes: &[("S", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "hyrax_podp",
            zippel_path: "examples/hyrax_podp/hyrax_podp.zippel",
            sizes: &[("S", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "zerocheck",
            zippel_path: "examples/zerocheck/zerocheck.zippel",
            sizes: &[("S", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "hadamard",
            zippel_path: "examples/hadamard/hadamard.zippel",
            sizes: &[("S", 2)],
            ignored: false,
        },
        CompletenessEntry {
            name: "pst13",
            zippel_path: "examples/pst13/pst13.zippel",
            sizes: &[("N", 2)],
            ignored: false,
        },
        CompletenessEntry {
            name: "zeromorph_kzg",
            zippel_path: "examples/zeromorph_kzg/zeromorph_kzg.zippel",
            sizes: &[("N", 2)],
            ignored: false,
        },
        CompletenessEntry {
            name: "zk_kzg",
            zippel_path: "examples/zk_kzg/zk_kzg.zippel",
            sizes: &[("N", 2)],
            ignored: false,
        },
        CompletenessEntry {
            name: "cds",
            zippel_path: "examples/cds/cds.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "kzh",
            zippel_path: "examples/kzh/kzh.zippel",
            sizes: &[("NX", 1), ("NY", 1)],
            ignored: false,
        },
        // --- Ignored: timeout (GB computation too slow for CI) ---
        CompletenessEntry {
            name: "coin_proof",
            zippel_path: "examples/coin_proof/coin_proof.zippel",
            sizes: &[],
            ignored: false,
        },
        CompletenessEntry {
            name: "r1cs_sigma",
            zippel_path: "examples/r1cs_sigma/r1cs_sigma.zippel",
            sizes: &[("N", 2), ("n", 1), ("m", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "hyperplonk_zerocheck",
            zippel_path: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel",
            sizes: &[("S", 3)],
            ignored: false,
        },
        CompletenessEntry {
            name: "hyperplonk_productcheck",
            zippel_path: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel",
            sizes: &[("S", 3)],
            ignored: true,
        },
        CompletenessEntry {
            name: "hyperplonk_multiset",
            zippel_path: "examples/hyperplonk_multiset/hyperplonk_multiset.zippel",
            sizes: &[("S", 3)],
            ignored: true,
        },
        CompletenessEntry {
            name: "hyperplonk_permutation",
            zippel_path: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel",
            sizes: &[("S", 3)],
            ignored: true,
        },
        CompletenessEntry {
            name: "dekart",
            zippel_path: "examples/dekart/dekart.zippel",
            sizes: &[("n", 3), ("b", 2), ("l_chunk", 1)],
            ignored: true,
        },
        CompletenessEntry {
            name: "dory",
            zippel_path: "examples/dory/dory.zippel",
            sizes: &[("S", 2)],
            ignored: true,
        },
        CompletenessEntry {
            name: "groth16",
            zippel_path: "examples/groth16/groth16.zippel",
            sizes: &[("M", 1), ("L", 1), ("H", 1)],
            ignored: false,
        },
        CompletenessEntry {
            name: "hyperplonk",
            zippel_path: "examples/hyperplonk/hyperplonk.zippel",
            sizes: &[("S", 3)],
            ignored: true,
        },
        CompletenessEntry {
            name: "hyrax",
            zippel_path: "examples/hyrax/hyrax.zippel",
            sizes: &[("L", 2), ("M", 2)],
            ignored: true,
        },
        CompletenessEntry {
            name: "pari",
            zippel_path: "examples/pari/pari.zippel",
            sizes: &[("M", 2), ("N", 1), ("KMN", 3)],
            ignored: true,
        },
        CompletenessEntry {
            name: "spartan",
            zippel_path: "examples/spartan/spartan.zippel",
            sizes: &[("M", 3)],
            ignored: true,
        },
    ]
});

fn run_completeness_snapshot(entry: &CompletenessEntry) -> Result<(), Failed> {
    let snap_name = format!("{}_completeness_basis", entry.name);
    let backend = GbBackendKind::Singular;

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();

    let normalized = std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let dag = compile_to_dag(&path, &sizes);
            let inputs = CompletenessAnalysis::<ArkBls12_381>::build_inputs(&dag, true);
            let mut ca = CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, backend);
            ca.run().map_err(|e| Failed::from(e.to_string()))?;
            Ok::<String, Failed>(normalize_basis(&ca.basis.polys))
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked")?;

    assert_named_snapshot(&snap_name, &normalized);
    Ok(())
}

/// Build the `completeness::*` trials.
pub(crate) fn trials(force_ignored: bool) -> Vec<Trial> {
    COMPLETENESS_ENTRIES
        .iter()
        .map(|entry| {
            let e = entry.clone();
            Trial::test(format!("completeness::{}", entry.name), move || {
                run_completeness_snapshot(&e)
            })
            .with_ignored_flag(entry.ignored || force_ignored)
        })
        .collect()
}
