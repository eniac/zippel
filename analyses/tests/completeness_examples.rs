//! Integration tests: completeness and incompleteness for every example in
//! `examples/` that finishes in reasonable time.
//!
//! This test harness uses `libtest-mimic` so that `cargo test --test
//! completeness_examples -- <filter>` works for individual examples.
//!
//! The GB backend is chosen at runtime: Singular is preferred (faster) if
//! available on `PATH`, falling back to ArkGb.

use analyses::{
    AnalysisError, CompletenessAnalysis, GbBackendKind, QualifierPropagation, UniformityPropagation,
};
use backend::ArkBls12_381;
use lang::id::Tid;
use lang::typ::{Distribution, Qualifier};
use libtest_mimic::{Failed, Trial};
use petgraph::Direction;
use petgraph::visit::EdgeRef;
use share::{Ctx, unwrap};
use std::path::PathBuf;
use std::process::{Command, Stdio};

use graph::UDags;
use lang::ast::UModule;

type AnalysisDag = graph::Dag<ArkBls12_381, (Qualifier, Distribution)>;

const ANALYSIS_STACK_SIZE: usize = 256 * 1024 * 1024;

#[derive(Clone, Copy)]
struct TestEntry {
    name: &'static str,
    zippel_path: &'static str,
    sizes: &'static [(&'static str, usize)],
    ignored: bool,
}

#[rustfmt::skip]
const EXAMPLES: &[TestEntry] = &[
    TestEntry { name: "sumcheck", zippel_path: "examples/sumcheck/sumcheck.zippel", sizes: &[("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)], ignored: false },
    TestEntry { name: "mle_sumcheck", zippel_path: "examples/mle_sumcheck/mle_sumcheck.zippel", sizes: &[("NUM_VARS", 3), ("MAX_DEGREE_CONST", 1)], ignored: false },
    TestEntry { name: "kzg", zippel_path: "examples/kzg/kzg.zippel", sizes: &[("N", 2)], ignored: false },
    TestEntry { name: "membership", zippel_path: "examples/membership/membership.zippel", sizes: &[("N", 2), ("M", 2), ("S", 2)], ignored: false },
    TestEntry { name: "schnorr", zippel_path: "examples/schnorr/schnorr.zippel", sizes: &[], ignored: false },
    TestEntry { name: "schnorr_3round", zippel_path: "examples/schnorr_3round/schnorr_3round.zippel", sizes: &[], ignored: false },
    TestEntry { name: "cp", zippel_path: "examples/cp/cp.zippel", sizes: &[], ignored: false },
    TestEntry { name: "okamoto", zippel_path: "examples/okamoto/okamoto.zippel", sizes: &[], ignored: false },
    TestEntry { name: "okamoto_elgamal", zippel_path: "examples/okamoto_elgamal/okamoto_elgamal.zippel", sizes: &[], ignored: false },
    TestEntry { name: "coin_proof", zippel_path: "examples/coin_proof/coin_proof.zippel", sizes: &[], ignored: true },
    TestEntry { name: "r1cs_sigma", zippel_path: "examples/r1cs_sigma/r1cs_sigma.zippel", sizes: &[("N", 2), ("n", 1), ("m", 1)], ignored: true },
    TestEntry { name: "commitment_equality", zippel_path: "examples/commitment_equality/commitment_equality.zippel", sizes: &[], ignored: false },
    TestEntry { name: "pedersen_eq", zippel_path: "examples/pedersen_eq/pedersen_eq.zippel", sizes: &[], ignored: false },
    TestEntry { name: "hyrax_pop", zippel_path: "examples/hyrax_pop/hyrax_pop.zippel", sizes: &[], ignored: false },
    TestEntry { name: "bccgp", zippel_path: "examples/bccgp/bccgp.zippel", sizes: &[("S", 0)], ignored: false },
    TestEntry { name: "ipa", zippel_path: "examples/ipa/ipa.zippel", sizes: &[("S", 0)], ignored: false },
    TestEntry { name: "ipa_weighted", zippel_path: "examples/ipa_weighted/ipa_weighted.zippel", sizes: &[("S", 0)], ignored: false },
    TestEntry { name: "hyrax_ipa", zippel_path: "examples/hyrax_ipa/hyrax_ipa.zippel", sizes: &[("S", 0)], ignored: false },
    TestEntry { name: "hyrax_podp", zippel_path: "examples/hyrax_podp/hyrax_podp.zippel", sizes: &[("S", 1)], ignored: false },
    TestEntry { name: "zerocheck", zippel_path: "examples/zerocheck/zerocheck.zippel", sizes: &[("S", 1)], ignored: false },
    TestEntry { name: "hyperplonk_zerocheck", zippel_path: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel", sizes: &[("S", 2)], ignored: true },
    TestEntry { name: "hyperplonk_productcheck", zippel_path: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel", sizes: &[("S", 2)], ignored: true },
    TestEntry { name: "hyperplonk_multiset", zippel_path: "examples/hyperplonk_multiset/hyperplonk_multiset.zippel", sizes: &[("S", 2)], ignored: true },
    TestEntry { name: "hyperplonk_permutation", zippel_path: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel", sizes: &[("S", 2)], ignored: true },
    TestEntry { name: "cds", zippel_path: "examples/cds/cds.zippel", sizes: &[], ignored: false },
    TestEntry { name: "hadamard", zippel_path: "examples/hadamard/hadamard.zippel", sizes: &[("S", 2)], ignored: false },
    TestEntry { name: "pst13", zippel_path: "examples/pst13/pst13.zippel", sizes: &[("N", 2)], ignored: false },
    TestEntry { name: "zeromorph_kzg", zippel_path: "examples/zeromorph_kzg/zeromorph_kzg.zippel", sizes: &[("N", 2)], ignored: false },
    TestEntry { name: "zk_kzg", zippel_path: "examples/zk_kzg/zk_kzg.zippel", sizes: &[("N", 2)], ignored: false },
    // --- New examples (ignored until verified to finish in reasonable time) ---
    TestEntry { name: "dekart", zippel_path: "examples/dekart/dekart.zippel", sizes: &[("n", 2), ("b", 2), ("l_chunk", 1), ("h_deg", 1)], ignored: true },
    TestEntry { name: "dory", zippel_path: "examples/dory/dory.zippel", sizes: &[("S", 2)], ignored: true },
    TestEntry { name: "groth16", zippel_path: "examples/groth16/groth16.zippel", sizes: &[("M", 2), ("L", 2), ("H", 1)], ignored: true },
    TestEntry { name: "hyperplonk", zippel_path: "examples/hyperplonk/hyperplonk.zippel", sizes: &[("S", 2)], ignored: true },
    TestEntry { name: "hyrax", zippel_path: "examples/hyrax/hyrax.zippel", sizes: &[("L", 2), ("M", 2)], ignored: true },
    TestEntry { name: "kzh", zippel_path: "examples/kzh/kzh.zippel", sizes: &[("NX", 2), ("NY", 2)], ignored: true },
    TestEntry { name: "pari", zippel_path: "examples/pari/pari.zippel", sizes: &[("M", 2), ("N", 1), ("KMN", 3)], ignored: true },
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

/// Pick the fastest available backend.
fn pick_backend() -> GbBackendKind {
    if singular_available() {
        GbBackendKind::Singular
    } else {
        GbBackendKind::ArkGb
    }
}

/// Parse + concretize + build the analysis DAG (inlines `ZippelHandler::compile`
/// + `build_analyze_graph` without the PDF/caching/public-inputs machinery).
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
    let g_qual = QualifierPropagation::from_dag(proto);
    UniformityPropagation::from_dag(&g_qual).annotate_dag(&g_qual)
}

/// Remove all outgoing edges from the relation node (simulates a protocol
/// with a stripped/incorrect relation).
fn strip_relation(dag: &mut AnalysisDag) {
    let rel_node = dag.relation_node().unwrap();
    let edge_ids: Vec<_> = dag
        .graph
        .edges_directed(rel_node, Direction::Outgoing)
        .map(|e| e.id())
        .collect();
    for eid in edge_ids {
        dag.graph.remove_edge(eid);
    }
}

fn run_completeness(entry: &TestEntry) -> Result<(), Failed> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    let backend = pick_backend();
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let dag = compile_to_dag(&path, &sizes);
            let mut ca = CompletenessAnalysis::from_input_with_backend(&dag, backend);
            ca.run().map_err(|e| Failed::from(e.to_string()))
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked")
}

fn run_incompleteness(entry: &TestEntry) -> Result<(), Failed> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    let backend = pick_backend();
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let mut dag = compile_to_dag(&path, &sizes);
            strip_relation(&mut dag);
            let mut ca = CompletenessAnalysis::from_input_with_backend(&dag, backend);
            match ca.run() {
                Err(AnalysisError::Incomplete(_)) => Ok(()),
                Err(e) => Err(Failed::from(format!("expected Incomplete, got: {e}"))),
                Ok(()) => Err(Failed::from("expected Incomplete, but analysis succeeded")),
            }
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked")
}

fn main() {
    let mut trials: Vec<Trial> = Vec::new();

    for entry in EXAMPLES {
        let entry = *entry;

        let trial = Trial::test(format!("completeness::{}", entry.name), move || {
            run_completeness(&entry)
        })
        .with_ignored_flag(entry.ignored);
        trials.push(trial);

        let trial = Trial::test(format!("incompleteness::{}", entry.name), move || {
            run_incompleteness(&entry)
        })
        .with_ignored_flag(entry.ignored);
        trials.push(trial);
    }

    libtest_mimic::run(&libtest_mimic::Arguments::from_args(), trials).exit();
}
