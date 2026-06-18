use analyses::AnalysisError;
use backend::ArkBls12_381;
use lang::id::Tid;
use libtest_mimic::{Failed, Trial};
use petgraph::Direction;
use petgraph::visit::EdgeRef;
use share::Ctx;
use std::path::PathBuf;
use zippel::{ZippelArgs, ZippelHandler};

const ANALYSIS_STACK_SIZE: usize = 256 * 1024 * 1024;

#[derive(Clone, Copy)]
struct TestEntry {
    name: &'static str,
    zippel_path: &'static str,
    sizes: &'static [(&'static str, usize)],
    ignored: bool,
}

#[rustfmt::skip]
const COMPLETENESS_TESTS: &[TestEntry] = &[
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
    TestEntry { name: "r1cs_sigma", zippel_path: "examples/r1cs_sigma/r1cs_sigma.zippel", sizes: &[], ignored: true },
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
];

#[rustfmt::skip]
const INCOMPLETENESS_TESTS: &[TestEntry] = &[
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
    TestEntry { name: "r1cs_sigma", zippel_path: "examples/r1cs_sigma/r1cs_sigma.zippel", sizes: &[], ignored: true },
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
];

fn build_sizes_ctx(sizes: &[(&str, usize)]) -> Ctx<Tid, usize> {
    let mut ctx = Ctx::new();
    for &(name, value) in sizes {
        ctx.insert(&Tid::new(name), &value);
    }
    ctx
}

fn run_completeness(entry: &TestEntry) -> Result<(), Failed> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let mut handler: ZippelHandler<ArkBls12_381> =
                ZippelHandler::new(ZippelArgs::new(path));
            let ctx = build_sizes_ctx(&sizes);
            handler.compile(&ctx);
            handler
                .analyze_completeness()
                .map_err(|e| Failed::from(e.to_string()))
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked")
}

fn strip_relation(handler: &mut ZippelHandler<ArkBls12_381>) {
    let dag = handler.analyze_graph();
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

fn run_incompleteness(entry: &TestEntry) -> Result<(), Failed> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(entry.zippel_path);
    let sizes = entry.sizes.to_vec();
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let mut handler: ZippelHandler<ArkBls12_381> =
                ZippelHandler::new(ZippelArgs::new(path));
            let ctx = build_sizes_ctx(&sizes);
            handler.compile(&ctx);
            strip_relation(&mut handler);
            match handler.analyze_completeness() {
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

    for entry in COMPLETENESS_TESTS {
        let entry = *entry;
        let trial = Trial::test(format!("completeness::{}", entry.name), move || {
            run_completeness(&entry)
        })
        .with_ignored_flag(entry.ignored);
        trials.push(trial);
    }

    for entry in INCOMPLETENESS_TESTS {
        let entry = *entry;
        let trial = Trial::test(format!("incompleteness::{}", entry.name), move || {
            run_incompleteness(&entry)
        })
        .with_ignored_flag(entry.ignored);
        trials.push(trial);
    }

    libtest_mimic::run(&libtest_mimic::Arguments::from_args(), trials).exit();
}
