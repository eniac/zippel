//! Integration tests for partial verification: concretizing some protocol
//! args to constant values before running completeness/soundness analysis.
//!
//! This reduces the number of free polynomial variables in the Groebner
//! basis, potentially making previously intractable analyses feasible.

use analyses::{
    AnalysisError, CompletenessAnalysis, GbBackendKind, QualifierPropagation,
    SpecialSoundnessAnalysis,
};
use ark_ff::One;
use backend::{ArkBls12_381, Value};
use graph::UDags;
use lang::ast::UModule;
use lang::id::Vid;
use share::{Ctx, unwrap};

use petgraph::Direction;
use petgraph::visit::EdgeRef;

type AnalysisDag = graph::Dag<ArkBls12_381, lang::typ::Qualifier>;

const ANALYSIS_STACK_SIZE: usize = 256 * 1024 * 1024;

const SCHNORR_PROTO: &str = r#"
    proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
        let r = random<F>;
        u <- g*r;
        c <- challenge<F>;
        z <- r + x*c;
        verify(g*z == u + h*c)
    }
"#;

fn compile_schnorr() -> AnalysisDag {
    let m = UModule::from_str(SCHNORR_PROTO)
        .unwrap()
        .concretize(&Ctx::new())
        .unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
    let proto = gs.protocols().into_iter().next().unwrap();
    QualifierPropagation::from_dag(proto)
}

/// Build a partial-values map that concretizes `x` to the scalar 1.
fn schnorr_x_one(dag: &AnalysisDag) -> Ctx<graph::Ref, Value<ArkBls12_381>> {
    let names = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([(
        Vid("x".to_string()),
        Value::Scalar(<ArkBls12_381 as backend::ArkConfig>::F::one()),
    )]);
    dag.resolve_partial_values(&names)
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

#[test]
fn schnorr_partial_completeness_passes() {
    let dag = compile_schnorr();
    let partial = schnorr_x_one(&dag);
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let mut ca = CompletenessAnalysis::from_input_with_partial(
                &dag,
                GbBackendKind::default(),
                &partial,
            );
            ca.run()
                .expect("Schnorr with concretized x should be complete");
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked");
}

#[test]
fn schnorr_partial_incompleteness_detected() {
    let mut dag = compile_schnorr();
    let partial = schnorr_x_one(&dag);
    strip_relation(&mut dag);
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let mut ca = CompletenessAnalysis::from_input_with_partial(
                &dag,
                GbBackendKind::default(),
                &partial,
            );
            match ca.run() {
                Err(AnalysisError::Incomplete(_)) => {}
                Err(e) => panic!("expected Incomplete, got: {e}"),
                Ok(()) => panic!("expected Incomplete, but analysis succeeded"),
            }
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked");
}

/// Soundness with all private witnesses concretized is degenerate:
/// there are no witnesses to extract, so the relation can't be derived
/// from the transcript alone (the extractor is the bridge). This test
/// verifies that the analysis correctly reports `ExtractorInvalid`
/// rather than crashing or giving a false positive.
#[test]
fn schnorr_partial_soundness_all_witnesses_concretized() {
    let dag = compile_schnorr();
    let partial = schnorr_x_one(&dag);
    std::thread::Builder::new()
        .stack_size(ANALYSIS_STACK_SIZE)
        .spawn(move || {
            let result = SpecialSoundnessAnalysis::from_input_with_partial(
                &dag,
                vec![2],
                GbBackendKind::default(),
                &partial,
            )
            .and_then(|mut sa| sa.run());
            match result {
                Err(AnalysisError::ExtractorInvalid(_)) => {}
                other => panic!(
                    "expected ExtractorInvalid (degenerate: no witnesses to extract), got: {:?}",
                    other
                ),
            }
        })
        .expect("failed to spawn thread")
        .join()
        .expect("thread panicked");
}
