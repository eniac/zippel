//! GB snapshot tests: generate with Singular, verify with ArkGb.
//!
//! The test harness auto-detects the backend per snapshot file:
//! - **File does not exist** → use Singular (generate mode). Fails if
//!   Singular is not on `PATH`.
//! - **File exists** → use ArkGb (verify mode). Compares ArkGb output
//!   against the committed snapshot.
//!
//! When `INSTA_UPDATE` is set (snapshot regeneration mode), Singular is
//! always used regardless of whether the file exists. This prevents
//! accidentally overwriting Singular-generated baselines with ArkGb output.
//! If Singular is not on `PATH` during regeneration, the test fails with a
//! clear error.
//!
//! To (re)generate snapshots:
//! ```sh
//! INSTA_UPDATE=always cargo test -p analyses --test gb_snapshots
//! ```
//! To verify in CI (no Singular needed):
//! ```sh
//! cargo test -p analyses --test gb_snapshots
//! ```

use analyses::frontend::Polynomial;
use analyses::{
    CompletenessAnalysis, GbBackendKind, KnowledgeAnalysis, QualifierPropagation,
    SpecialSoundnessAnalysis,
};
use ark_ff::{One, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use lang::typ::Qualifier;
use libtest_mimic::{Failed, Trial};
use share::{Ctx, unwrap};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock;

use graph::UDags;
use lang::ast::UModule;

type AnalysisDag = graph::Dag<ArkBls12_381, Qualifier>;
type F = <ArkBls12_381 as ArkConfig>::F;

const ANALYSIS_STACK_SIZE: usize = 256 * 1024 * 1024;

/// Snapshot directory (relative to the test file's location, which is in
/// `analyses/tests/`). So this resolves to `analyses/tests/snapshots/gb_snapshots/`.
const SNAP_DIR: &str = "snapshots/gb_snapshots";

/// Function that builds the name-based partial values map for an entry.
/// Returns an empty `Ctx` when partial verification is not used.
type PartialValuesFn = fn() -> Ctx<Vid, Value<ArkBls12_381>>;

/// No partial values — the default for entries that don't use partial
/// verification.
fn no_partial() -> Ctx<Vid, Value<ArkBls12_381>> {
    Ctx::new()
}

/// r1cs_sigma with fixed R1CS matrices: A=[1,0], B=[1,0], C=[1,0].
/// With N=2, n=1, m=1, each matrix is [F; 2] (a 1×2 row).
/// This gives z_A = z_B = z_C = x[0], so the relation is x^2 == x.
fn r1cs_sigma_partial() -> Ctx<Vid, Value<ArkBls12_381>> {
    let one = F::one();
    let zero = F::zero();
    let mat = Value::VecScalar(vec![one, zero]);
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("mat_A".to_string()), mat.clone()),
        (Vid("mat_B".to_string()), mat.clone()),
        (Vid("mat_C".to_string()), mat),
    ])
}

#[derive(Clone, Copy)]
struct TestEntry {
    name: &'static str,
    zippel_path: &'static str,
    sizes: &'static [(&'static str, usize)],
    /// l_vec for soundness analysis. Empty = skip soundness.
    l_vec: &'static [usize],
    /// `true` = test is marked ignored (not run by default).
    /// Reasons:
    ///   "timeout" — GB computation too slow for CI.
    ///   "ark-gb-elim" — ark-gb's 2-block elim order doesn't separate per-block
    ///                   grevlex grading (upstream limitation: tiered path
    ///                   requires first block to be Lex, not GrevLex).
    ignored: bool,
    /// Builds the name-based partial values map. An empty map means no
    /// partial verification.
    partial_values: PartialValuesFn,
}

#[rustfmt::skip]
const EXAMPLES: &[TestEntry] = &[
    // --- Active (completeness + soundness verified Singular ↔ ArkGb) ---
    TestEntry { name: "sumcheck", zippel_path: "examples/sumcheck/sumcheck_full.zippel", sizes: &[("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "mle_sumcheck", zippel_path: "examples/mle_sumcheck/mle_sumcheck.zippel", sizes: &[("NUM_VARS", 3), ("MAX_DEGREE_CONST", 1)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "kzg", zippel_path: "examples/kzg/kzg.zippel", sizes: &[("N", 2)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "membership", zippel_path: "examples/membership/membership.zippel", sizes: &[("N", 2), ("M", 2), ("S", 2)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "schnorr", zippel_path: "examples/schnorr/schnorr.zippel", sizes: &[], l_vec: &[2], ignored: false, partial_values: no_partial },
    TestEntry { name: "schnorr_3round", zippel_path: "examples/schnorr_3round/schnorr_3round.zippel", sizes: &[], l_vec: &[2, 2, 2], ignored: false, partial_values: no_partial },
    TestEntry { name: "cp", zippel_path: "examples/cp/cp.zippel", sizes: &[], l_vec: &[2], ignored: false, partial_values: no_partial },
    TestEntry { name: "okamoto", zippel_path: "examples/okamoto/okamoto.zippel", sizes: &[], l_vec: &[2], ignored: false, partial_values: no_partial },
    TestEntry { name: "okamoto_elgamal", zippel_path: "examples/okamoto_elgamal/okamoto_elgamal.zippel", sizes: &[], l_vec: &[2], ignored: false, partial_values: no_partial },
    TestEntry { name: "commitment_equality", zippel_path: "examples/commitment_equality/commitment_equality.zippel", sizes: &[], l_vec: &[2], ignored: false, partial_values: no_partial },
    TestEntry { name: "pedersen_eq", zippel_path: "examples/pedersen_eq/pedersen_eq.zippel", sizes: &[], l_vec: &[2], ignored: false, partial_values: no_partial },
    TestEntry { name: "hyrax_pop", zippel_path: "examples/hyrax_pop/hyrax_pop.zippel", sizes: &[], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "bccgp", zippel_path: "examples/bccgp/bccgp.zippel", sizes: &[("S", 0)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "ipa", zippel_path: "examples/ipa/ipa.zippel", sizes: &[("S", 0)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "ipa_weighted", zippel_path: "examples/ipa_weighted/ipa_weighted.zippel", sizes: &[("S", 0)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "hyrax_ipa", zippel_path: "examples/hyrax_ipa/hyrax_ipa.zippel", sizes: &[("S", 0)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "hyrax_podp", zippel_path: "examples/hyrax_podp/hyrax_podp.zippel", sizes: &[("S", 1)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "zerocheck", zippel_path: "examples/zerocheck/zerocheck.zippel", sizes: &[("S", 1)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "hadamard", zippel_path: "examples/hadamard/hadamard.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "pst13", zippel_path: "examples/pst13/pst13.zippel", sizes: &[("N", 2)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "zeromorph_kzg", zippel_path: "examples/zeromorph_kzg/zeromorph_kzg.zippel", sizes: &[("N", 2)], l_vec: &[], ignored: false, partial_values: no_partial },
    TestEntry { name: "zk_kzg", zippel_path: "examples/zk_kzg/zk_kzg.zippel", sizes: &[("N", 2)], l_vec: &[], ignored: false, partial_values: no_partial },

    // --- Ignored: ark-gb grevlex bug (single-block GrevLex) ---
    // ark-gb's cmp_degrevlex_packed skips total-degree comparison in the
    // non-saturated path, producing lex instead of grevlex. Upstream fix
    // needed in ark-gb/src/monomial.rs.
    TestEntry { name: "cds", zippel_path: "examples/cds/cds.zippel", sizes: &[], l_vec: &[], ignored: true, partial_values: no_partial },

    // --- Ignored: timeout (GB computation too slow for CI) ---
    TestEntry { name: "coin_proof", zippel_path: "examples/coin_proof/coin_proof.zippel", sizes: &[], l_vec: &[], ignored: true, partial_values: no_partial },
    // r1cs_sigma: partial verification with fixed R1CS matrices (mat_A, mat_B, mat_C).
    // The circuit is A=[1,0], B=[1,0], C=[1,0] → relation x^2 == x.
    // Ignored until a Singular-generated snapshot is committed.
    TestEntry { name: "r1cs_sigma", zippel_path: "examples/r1cs_sigma/r1cs_sigma.zippel", sizes: &[("N", 2), ("n", 1), ("m", 1)], l_vec: &[], ignored: true, partial_values: r1cs_sigma_partial },
    TestEntry { name: "hyperplonk_zerocheck", zippel_path: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "hyperplonk_productcheck", zippel_path: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "hyperplonk_multiset", zippel_path: "examples/hyperplonk_multiset/hyperplonk_multiset.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "hyperplonk_permutation", zippel_path: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "dekart", zippel_path: "examples/dekart/dekart.zippel", sizes: &[("n", 2), ("b", 2), ("l_chunk", 1), ("h_deg", 1)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "dory", zippel_path: "examples/dory/dory.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "groth16", zippel_path: "examples/groth16/groth16.zippel", sizes: &[("M", 2), ("L", 2), ("H", 1)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "hyperplonk", zippel_path: "examples/hyperplonk/hyperplonk.zippel", sizes: &[("S", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "hyrax", zippel_path: "examples/hyrax/hyrax.zippel", sizes: &[("L", 2), ("M", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "kzh", zippel_path: "examples/kzh/kzh.zippel", sizes: &[("NX", 2), ("NY", 2)], l_vec: &[], ignored: true, partial_values: no_partial },
    TestEntry { name: "pari", zippel_path: "examples/pari/pari.zippel", sizes: &[("M", 2), ("N", 1), ("KMN", 3)], l_vec: &[], ignored: true, partial_values: no_partial },
];

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
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
}

static SINGULAR_AVAILABLE: OnceLock<bool> = OnceLock::new();

fn singular() -> bool {
    *SINGULAR_AVAILABLE.get_or_init(singular_available)
}

/// Full path to the snapshot directory (CARGO_MANIFEST_DIR/tests/snapshots/gb_snapshots).
fn snap_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/snapshots/gb_snapshots")
}

/// Determine the backend for a given snapshot file.
///
/// - If `INSTA_UPDATE` is set (regeneration mode) → always Singular, the
///   baseline. Fails if Singular is not on `PATH`.
/// - If the file doesn't exist → Singular (generate mode). Fails if
///   Singular is not on `PATH`.
/// - If the file exists → ArkGb (verify mode).
fn backend_for_snapshot(snap_name: &str) -> Result<GbBackendKind, Failed> {
    // Regeneration mode: always use Singular to preserve baselines.
    if std::env::var("INSTA_UPDATE").is_ok() {
        if !singular() {
            return Err(Failed::from(
                "INSTA_UPDATE is set but Singular is not on PATH. \
                 Snapshots must be (re)generated with Singular to preserve baselines. \
                 Install Singular or unset INSTA_UPDATE to verify with ArkGb."
                    .to_string(),
            ));
        }
        return Ok(GbBackendKind::Singular);
    }

    let snap_full = snap_dir().join(format!("{snap_name}.snap"));
    if snap_full.exists() {
        Ok(GbBackendKind::ArkGb)
    } else {
        if !singular() {
            return Err(Failed::from(format!(
                "Snapshot {snap_name}.snap does not exist and Singular is not on PATH. \
                 Install Singular to generate snapshots."
            )));
        }
        Ok(GbBackendKind::Singular)
    }
}

/// Parse + concretize + build the analysis DAG.
fn compile_to_dag(path: &PathBuf, sizes: &[(&str, usize)]) -> AnalysisDag {
    lang::init_parser();
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    let module = UModule::from_str(&source)
        .unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()));
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
fn normalize_basis(polys: &[Polynomial<F>]) -> String {
    let mut rendered: Vec<String> = polys.iter().map(|p| format!("{p}")).collect();
    rendered.sort();
    rendered.join("\n")
}

/// Assert a snapshot with a custom name, bypassing insta's default naming.
fn assert_named_snapshot(snap_name: &str, value: &str) {
    let mut settings = insta::Settings::clone_current();
    settings.set_snapshot_path(SNAP_DIR);
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| {
        insta::assert_snapshot!(snap_name, value);
    });
}

/// Suffix for the test display name: " (partial)" if the entry uses
/// partial verification, empty otherwise.
fn partial_suffix(entry: &TestEntry) -> &'static str {
    if (entry.partial_values)().is_empty() {
        ""
    } else {
        " (partial)"
    }
}

fn run_completeness_snapshot(entry: &TestEntry) -> Result<(), Failed> {
    let snap_name = format!("{}_completeness_basis", entry.name);
    let backend = backend_for_snapshot(&snap_name)?;

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    let pv_fn = entry.partial_values;

    let normalized = std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let dag = compile_to_dag(&path, &sizes);
            let names = pv_fn();
            let ca = if names.is_empty() {
                CompletenessAnalysis::from_input_with_backend(&dag, backend)
            } else {
                let pv = dag.resolve_partial_values(&names);
                CompletenessAnalysis::from_input_with_partial(&dag, backend, &pv)
            };
            normalize_basis(&ca.basis.polys)
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked");

    assert_named_snapshot(&snap_name, &normalized);
    Ok(())
}

fn run_knowledge_snapshot(entry: &TestEntry) -> Result<(), Failed> {
    let snap_basis = format!("{}_knowledge_basis", entry.name);
    let snap_rel = format!("{}_knowledge_relation", entry.name);
    let backend = backend_for_snapshot(&snap_basis)?;
    // Both knowledge snapshots use the same backend. Check relation snapshot too.
    let rel_path = snap_dir().join(format!("{snap_rel}.snap"));
    if !rel_path.exists() && !singular() {
        return Err(Failed::from(format!(
            "Snapshot {snap_rel}.snap does not exist and Singular is not on PATH."
        )));
    }

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

fn run_soundness_snapshot(entry: &TestEntry) -> Result<(), Failed> {
    let snap_name = format!("{}_soundness_search", entry.name);
    let backend = backend_for_snapshot(&snap_name)?;

    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    let l_vec = entry.l_vec.to_vec();
    let pv_fn = entry.partial_values;

    let normalized = std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let dag = compile_to_dag(&path, &sizes);
            let names = pv_fn();
            let sa = if names.is_empty() {
                SpecialSoundnessAnalysis::from_input_with_backend(&dag, l_vec, backend)
            } else {
                let pv = dag.resolve_partial_values(&names);
                SpecialSoundnessAnalysis::from_input_with_partial(&dag, l_vec, backend, &pv)
            }
            .map_err(|e| Failed::from(e.to_string()))?;
            Ok::<String, Failed>(normalize_basis(&sa.search_gb.polys))
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked")?;

    assert_named_snapshot(&snap_name, &normalized);
    Ok(())
}

fn main() {
    let mut trials: Vec<Trial> = Vec::new();

    for entry in EXAMPLES {
        let entry = *entry;
        let suffix = partial_suffix(&entry);

        // Completeness snapshot
        let e = entry;
        trials.push(
            Trial::test(
                format!("completeness::{}{}", entry.name, suffix),
                move || run_completeness_snapshot(&e),
            )
            .with_ignored_flag(entry.ignored),
        );

        // Knowledge snapshot — all knowledge tests are ignored because
        // ark-gb's 2-block GrevLex/GrevLex elim order (ZippelElimMono)
        // does not correctly separate per-block grevlex grading. The
        // tiered path (ZippelTieredElimMono) handles this correctly but
        // requires the first block to be Lex, not GrevLex. Upstream fix
        // needed: tiered path should support GrevLex-first blocks.
        let e = entry;
        trials.push(
            Trial::test(format!("knowledge::{}{}", entry.name, suffix), move || {
                run_knowledge_snapshot(&e)
            })
            .with_ignored_flag(true),
        );

        // Soundness snapshot (only if l_vec is non-empty)
        if !entry.l_vec.is_empty() {
            let e = entry;
            trials.push(
                Trial::test(format!("soundness::{}{}", entry.name, suffix), move || {
                    run_soundness_snapshot(&e)
                })
                .with_ignored_flag(entry.ignored),
            );
        }
    }

    libtest_mimic::run(&libtest_mimic::Arguments::from_args(), trials).exit();
}
