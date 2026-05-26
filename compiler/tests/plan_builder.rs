//! Integration tests for the deterministic codegen plan builder.
//!
//! These tests use the Schnorr protocol as a representative Graph IR DAG and
//! verify that `compiler::testing::build_plan` produces a stable, well-formed
//! [`CodegenPlan`].

use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{CodegenMode, CodegenOptions};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

// ---------------------------------------------------------------------------
// Schnorr protocol source (inline to avoid working-directory sensitivity).
// ---------------------------------------------------------------------------

const SCHNORR_SRC: &str = r#"
proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
    let r = random<F>;
    u <- g*r;
    c <- challenge<F*>;
    z <- r + x*c;
    verify(g*z == u + h*c)
}
"#;

// ---------------------------------------------------------------------------
// Helper: build a handler whose prover and verifier graphs are ready.
// ---------------------------------------------------------------------------

fn schnorr_handler() -> ZippelHandler<ArkBls12_381> {
    let dir = tempfile::tempdir().expect("tempdir");
    let path: PathBuf = dir.path().join("schnorr.zippel");
    std::fs::write(&path, SCHNORR_SRC).expect("write schnorr.zippel");
    // Keep `dir` alive for the duration of the call; the handler only needs
    // the path during `compile()`, so it is safe to drop after that.
    let args = ZippelArgs::new(path);
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());
    handler
}

// ---------------------------------------------------------------------------
// Test 1 – Prover plan: stable inputs, transcript, and topological nodes.
// ---------------------------------------------------------------------------

#[test]
fn prover_plan_has_stable_inputs_transcript_and_topological_nodes() {
    let handler = schnorr_handler();
    let dag = handler.prover_graph.as_ref().unwrap();
    let options = CodegenOptions::prover();

    let plan =
        compiler::testing::build_plan(dag, &options).expect("prover plan must build without error");

    // Mode must be Prover.
    assert_eq!(plan.mode, CodegenMode::Prover, "mode must be Prover");

    // Input names must include x, g, and h.
    let input_names: Vec<&str> = plan.inputs.iter().map(|a| a.name.as_str()).collect();
    assert!(
        input_names.contains(&"x"),
        "prover inputs must contain `x`; got {input_names:?}"
    );
    assert!(
        input_names.contains(&"g"),
        "prover inputs must contain `g`; got {input_names:?}"
    );
    assert!(
        input_names.contains(&"h"),
        "prover inputs must contain `h`; got {input_names:?}"
    );

    // At least one transcript node.
    assert!(
        plan.nodes.iter().any(|n| n.is_transcript),
        "prover plan must contain at least one transcript node"
    );

    // Transcript order must have at least two entries.
    assert!(
        plan.transcript_order.len() >= 2,
        "transcript order must have ≥ 2 entries; got {}",
        plan.transcript_order.len()
    );

    // Node variables must be non-empty.
    for n in &plan.nodes {
        assert!(
            !n.var.is_empty(),
            "every plan node must have a non-empty var; index={:?}",
            n.index
        );
    }

    // Topological ordering: for every plan node, every dependency must have
    // either already appeared in `plan.nodes` (at an earlier position) *or*
    // be a non-emitted node (input arg, Inp/Rel marker, or node with an
    // unsupported type) that is considered pre-available.
    //
    // We seed `seen` with every node index that is NOT going to appear in
    // plan.nodes, then walk plan.nodes in order verifying each dependency.
    let plan_node_indices: std::collections::BTreeSet<petgraph::graph::NodeIndex> =
        plan.nodes.iter().map(|n| n.index).collect();

    let mut seen: std::collections::BTreeSet<petgraph::graph::NodeIndex> = dag
        .node_indices()
        .filter(|idx| !plan_node_indices.contains(idx))
        .collect();

    for n in &plan.nodes {
        for &dep in &n.dependencies {
            assert!(
                seen.contains(&dep),
                "dependency {:?} of node {:?} ({}) has not been defined yet — \
                 topological ordering is violated",
                dep,
                n.index,
                n.var
            );
        }
        seen.insert(n.index);
    }
}

// ---------------------------------------------------------------------------
// Test 2 – Verifier plan: check nodes and verifier-mode inputs.
// ---------------------------------------------------------------------------

#[test]
fn verifier_plan_finds_check_nodes() {
    let handler = schnorr_handler();
    let dag = handler.verifier_graph.as_ref().unwrap();
    let options = CodegenOptions::verifier();

    let plan = compiler::testing::build_plan(dag, &options)
        .expect("verifier plan must build without error");

    // Mode must be Verifier.
    assert_eq!(plan.mode, CodegenMode::Verifier, "mode must be Verifier");

    // Exactly one check node.
    assert_eq!(
        plan.checks.len(),
        1,
        "Schnorr verifier must have exactly one check node; got {}",
        plan.checks.len()
    );

    // Verifier inputs must include g and h (public parameters).
    let input_names: Vec<&str> = plan.inputs.iter().map(|a| a.name.as_str()).collect();
    assert!(
        input_names.contains(&"g"),
        "verifier inputs must contain `g`; got {input_names:?}"
    );
    assert!(
        input_names.contains(&"h"),
        "verifier inputs must contain `h`; got {input_names:?}"
    );
}

// ---------------------------------------------------------------------------
// Test 3 – Variable names are sanitised (no empty, no digit-leading identifiers).
// ---------------------------------------------------------------------------

#[test]
fn plan_node_vars_are_valid_rust_idents() {
    let handler = schnorr_handler();
    let dag = handler.prover_graph.as_ref().unwrap();
    let options = CodegenOptions::prover();

    let plan = compiler::testing::build_plan(dag, &options).unwrap();

    for n in &plan.nodes {
        assert!(
            !n.var.is_empty(),
            "var must be non-empty; index={:?}",
            n.index
        );
        let first = n.var.chars().next().unwrap();
        assert!(
            first == '_' || first.is_ascii_alphabetic(),
            "var `{}` starts with an invalid character `{first}`",
            n.var
        );
    }
}

// ---------------------------------------------------------------------------
// Test 4 – Challenge flags are consistent with transcript flags.
// ---------------------------------------------------------------------------

#[test]
fn challenge_nodes_are_always_transcript_nodes() {
    let handler = schnorr_handler();
    let dag = handler.prover_graph.as_ref().unwrap();
    let options = CodegenOptions::prover();

    let plan = compiler::testing::build_plan(dag, &options).unwrap();

    for n in &plan.nodes {
        if n.is_challenge {
            assert!(
                n.is_transcript,
                "challenge node {:?} ({}) must also be flagged as transcript",
                n.index, n.var
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Test 5 – Unsupported input type propagates an error.
// ---------------------------------------------------------------------------

#[test]
fn unsupported_input_type_propagates_error() {
    use backend::{ATyp, ArkBls12_381};
    use compiler::CompilerError;
    use graph::{ArgKind, Dag, Node};
    use lang::id::Vid;
    use lang::typ::{Distribution, Nothing, Qualifier};

    // Build a minimal DAG with a single Arg node whose type (Uni) cannot be
    // rendered to a Rust type string.
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    dag.add_node(Node::Arg(
        Vid::new("p"),
        ATyp::Uni(4),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Input,
    ));

    let options = compiler::CodegenOptions::prover();
    let err = compiler::testing::build_plan(&dag, &options)
        .expect_err("build_plan must fail for an unsupported input type");

    assert!(
        matches!(err, CompilerError::UnsupportedType { .. }),
        "expected UnsupportedType, got {err:?}"
    );
}

// ---------------------------------------------------------------------------
// Test 6 – Unsupported typed non-input node propagates an error.
// ---------------------------------------------------------------------------

#[test]
fn unsupported_typed_node_propagates_error() {
    use backend::{ATyp, ArkBls12_381};
    use compiler::CompilerError;
    use graph::{ArgKind, Dag, Node};
    use lang::id::Vid;
    use lang::typ::{Distribution, Nothing, Qualifier};

    // A Relation-kind Arg node has a type but is not in `input_args()`.
    // build_plan must attempt to render its type and propagate the error.
    let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
    dag.add_node(Node::Arg(
        Vid::new("p"),
        ATyp::Uni(4),
        Qualifier::Public,
        Distribution::Nonuniform,
        ArgKind::Relation,
    ));

    let options = compiler::CodegenOptions::prover();
    let err = compiler::testing::build_plan(&dag, &options)
        .expect_err("build_plan must fail for an unsupported typed non-input node");

    assert!(
        matches!(err, CompilerError::UnsupportedType { .. }),
        "expected UnsupportedType, got {err:?}"
    );
}
