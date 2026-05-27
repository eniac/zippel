# Compiled GraphIR Rust Backend Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an additive `compiler/` crate that emits typed Arkworks/Tokio Rust from normal typed Graph IR DAGs, then validate it on Schnorr with generated `prover.rs` and `verifier.rs`.

**Architecture:** The compiler builds a small typed codegen plan from `Dag<C, A>` using public graph traversal APIs, maps `ATyp` to concrete Rust type syntax, lowers a Schnorr-sized operation subset to Rust expressions, and writes source to `std::io::Write`. Generated code is independent of Zippel crates and uses direct Arkworks values plus simple `tokio::spawn` joins.

**Tech Stack:** Rust nightly, Graph IR (`graph::Dag`), Arkworks (`ark-bls12-381`, `ark-ec`, `ark-ff`, `ark-serialize`, `ark-std`), Spongefish, Tokio, `thiserror`, Cargo integration tests.

---

## Scope and Non-Negotiable Constraints

The implementation is additive. Do not remove or change `runtime::MutexGraph`, `ZippelHandler::run_prover`, `ZippelHandler::run_verifier`, existing schedulers, or existing examples.

The compiler input is a normal typed Graph IR DAG such as `UDag<C>` or `Dag<C, A>`; it is not `TDag<C>` and it does not consume `ThreadAlloc`.

The generated Rust source must not import Zippel crates and must not mention these strings:

```text
backend::Value
Value<
MutexGraph
eval_op
runtime::
graph::
backend::
```

The compiler crate itself may depend on Zippel crates because it inspects Graph IR. The restriction applies to emitted Rust files.

## File Structure

Create and modify these files:

```text
Cargo.toml
compiler/Cargo.toml
compiler/src/lib.rs
compiler/src/error.rs
compiler/src/options.rs
compiler/src/plan.rs
compiler/src/types.rs
compiler/src/expr.rs
compiler/src/emit.rs
compiler/src/transcript.rs
compiler/src/schedule.rs
compiler/examples/generate_schnorr_rs.rs
compiler/tests/api_smoke.rs
compiler/tests/plan_builder.rs
compiler/tests/type_mapping.rs
compiler/tests/forbidden_output.rs
compiler/tests/schnorr_codegen.rs
examples/schnorr-rs/Cargo.toml
examples/schnorr-rs/src/main.rs
examples/schnorr-rs/src/prover.rs
examples/schnorr-rs/src/verifier.rs
```

Responsibilities:

```text
compiler/src/error.rs       CompilerError and Result aliases.
compiler/src/options.rs     CodegenOptions, CodegenMode, and RustTarget.
compiler/src/types.rs       ATyp/ABase to Rust type rendering.
compiler/src/plan.rs        Deterministic graph-to-codegen-plan conversion.
compiler/src/expr.rs        Op lowering from typed Graph IR to Rust expressions.
compiler/src/transcript.rs  Emitted transcript helper source and transcript barriers.
compiler/src/schedule.rs    Simple dependency-region planning for Tokio emission.
compiler/src/emit.rs        Rust source rendering to std::io::Write.
compiler/src/lib.rs         Public compile_prover and compile_verifier APIs.
```

Generated Schnorr files are committed for the first validation target so `examples/schnorr-rs` can be run directly. `compiler/examples/generate_schnorr_rs.rs` is the reproducible generator for refreshing them from the current Graph IR.

## Task 1: Workspace Wiring and Compiler Crate Skeleton

**Files:**
- Modify: `Cargo.toml`
- Create: `compiler/Cargo.toml`
- Create: `compiler/src/lib.rs`
- Create: `compiler/src/error.rs`
- Create: `compiler/src/options.rs`
- Test: `compiler/tests/api_smoke.rs`

- [ ] **Step 1: Write the failing API smoke test**

Create `compiler/tests/api_smoke.rs`:

```rust
use compiler::{CodegenMode, CodegenOptions, CompilerError, RustTarget};

#[test]
fn default_options_target_bls12_381_and_prover() {
    let options = CodegenOptions::default();

    assert_eq!(options.mode, CodegenMode::Prover);
    assert_eq!(options.target, RustTarget::ark_bls12_381());
    assert_eq!(options.session, "examples/schnorr/schnorr.zippel");
    assert_eq!(options.proof_type_path, "crate::prover::Proof");
}

#[test]
fn unsupported_op_error_names_node_and_operation() {
    let err = CompilerError::UnsupportedOp {
        node: 9,
        op: "Ram".to_string(),
    };

    let message = err.to_string();
    assert!(message.contains("node 9"), "{message}");
    assert!(message.contains("Ram"), "{message}");
}
```

- [ ] **Step 2: Run the test and verify it fails because the crate does not exist**

Run:

```bash
cargo test -p compiler --test api_smoke
```

Expected: Cargo fails with a package selection error containing `package ID specification 'compiler' did not match any packages`.

- [ ] **Step 3: Add `compiler` to the workspace**

Modify the first four lines of root `Cargo.toml` to include `compiler`:

```toml
[workspace]
members = [ "lang", "runtime", "share" , "graph", "backend", "compiler"]
exclude = [ "sumcheck_compare", "examples/schnorr-rs" ]
default-members = [ ".", "lang", "runtime", "share" , "graph", "backend", "compiler"]
resolver = "2"
```

- [ ] **Step 4: Create `compiler/Cargo.toml`**

Create `compiler/Cargo.toml`:

```toml
[package]
name = "compiler"
version = "0.1.0"
edition = "2024"

[dependencies]
backend = { path = "../backend" }
graph = { path = "../graph" }
lang = { path = "../lang" }
share = { path = "../share" }
ark-ff = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-ec = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-serialize = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-std = "0.5.0"
petgraph = "0.7.1"
thiserror = "2.0"

[dev-dependencies]
ark-bls12-381 = { git = "https://github.com/arkworks-rs/algebra.git" }
tempfile = "3.10"
zippel = { path = ".." }
```

- [ ] **Step 5: Create `compiler/src/error.rs`**

Create `compiler/src/error.rs`:

```rust
use thiserror::Error;

pub type Result<T> = std::result::Result<T, CompilerError>;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("unsupported Graph IR node {node}: {detail}")]
    UnsupportedNode { node: usize, detail: String },

    #[error("unsupported Graph IR op at node {node}: {op}")]
    UnsupportedOp { node: usize, op: String },

    #[error("unsupported Graph IR type at node {node}: {typ}")]
    UnsupportedType { node: usize, typ: String },

    #[error("graph is not acyclic; topological planning stopped at node {node}")]
    CyclicGraph { node: usize },

    #[error("missing generated variable for dependency node {node}")]
    MissingDependency { node: usize },

    #[error("generated source I/O failed")]
    Io(#[from] std::io::Error),
}
```

- [ ] **Step 6: Create `compiler/src/options.rs`**

Create `compiler/src/options.rs`:

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CodegenMode {
    Prover,
    Verifier,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RustTarget {
    pub curve_crate: &'static str,
    pub scalar_type: &'static str,
    pub g1_type: &'static str,
    pub g2_type: &'static str,
    pub pairing_type: &'static str,
}

impl RustTarget {
    pub fn ark_bls12_381() -> Self {
        Self {
            curve_crate: "ark_bls12_381",
            scalar_type: "ark_bls12_381::Fr",
            g1_type: "ark_bls12_381::G1Projective",
            g2_type: "ark_bls12_381::G2Projective",
            pairing_type: "ark_bls12_381::Bls12_381",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CodegenOptions {
    pub mode: CodegenMode,
    pub target: RustTarget,
    pub session: String,
    pub proof_type_path: String,
}

impl CodegenOptions {
    pub fn prover() -> Self {
        Self::default()
    }

    pub fn verifier() -> Self {
        Self {
            mode: CodegenMode::Verifier,
            ..Self::default()
        }
    }
}

impl Default for CodegenOptions {
    fn default() -> Self {
        Self {
            mode: CodegenMode::Prover,
            target: RustTarget::ark_bls12_381(),
            session: "examples/schnorr/schnorr.zippel".to_string(),
            proof_type_path: "crate::prover::Proof".to_string(),
        }
    }
}
```

- [ ] **Step 7: Create `compiler/src/lib.rs` with public API stubs**

Create `compiler/src/lib.rs`:

```rust
use std::io::Write;

use backend::ArkConfig;
use graph::Dag;

mod emit;
mod error;
mod expr;
mod options;
mod plan;
mod schedule;
mod transcript;
mod types;

pub use error::{CompilerError, Result};
pub use options::{CodegenMode, CodegenOptions, RustTarget};

pub fn compile_prover<C, A, W>(dag: &Dag<C, A>, writer: W) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    let options = CodegenOptions::prover();
    emit::emit_dag(dag, &options, writer)
}

pub fn compile_verifier<C, A, W>(dag: &Dag<C, A>, writer: W) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    let options = CodegenOptions::verifier();
    emit::emit_dag(dag, &options, writer)
}
```

- [ ] **Step 8: Create empty internal modules that compile**

Create these files:

```rust
// compiler/src/emit.rs
use std::io::Write;

use backend::ArkConfig;
use graph::Dag;

use crate::error::Result;
use crate::options::CodegenOptions;

pub(crate) fn emit_dag<C, A, W>(_dag: &Dag<C, A>, _options: &CodegenOptions, mut writer: W) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    writer.write_all(b"")?;
    Ok(())
}
```

```rust
// compiler/src/expr.rs
```

```rust
// compiler/src/plan.rs
```

```rust
// compiler/src/schedule.rs
```

```rust
// compiler/src/transcript.rs
```

```rust
// compiler/src/types.rs
```

- [ ] **Step 9: Run the API smoke test**

Run:

```bash
cargo test -p compiler --test api_smoke
```

Expected: the two tests in `api_smoke.rs` pass.

- [ ] **Step 10: Commit the skeleton**

Run:

```bash
git add Cargo.toml compiler
git commit -m "feat: add compiler crate skeleton" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 2: Rust Type Mapping

**Files:**
- Modify: `compiler/src/types.rs`
- Test: `compiler/tests/type_mapping.rs`

- [ ] **Step 1: Write the failing type mapping tests**

Create `compiler/tests/type_mapping.rs`:

```rust
use backend::{ABase, ATyp};
use compiler::{CodegenOptions, CompilerError};

#[test]
fn maps_bls12_381_base_types() {
    let options = CodegenOptions::default();

    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::Scalar), &options).unwrap(),
        "ark_bls12_381::Fr"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::G1), &options).unwrap(),
        "ark_bls12_381::G1Projective"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::G2), &options).unwrap(),
        "ark_bls12_381::G2Projective"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::GT), &options).unwrap(),
        "ark_ec::pairing::PairingOutput<ark_bls12_381::Bls12_381>"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::Bool), &options).unwrap(),
        "bool"
    );
}

#[test]
fn maps_vectors_and_records_without_value() {
    let options = CodegenOptions::default();
    let record = ATyp::Record(share::Ctx::from_iter([
        ("ok".to_string(), ATyp::Base(ABase::Bool)),
        ("s".to_string(), ATyp::Base(ABase::Scalar)),
    ]));

    assert_eq!(
        compiler::testing::render_type(
            &ATyp::Vec(Box::new(ATyp::Base(ABase::Scalar)), 3),
            &options
        )
        .unwrap(),
        "Vec<ark_bls12_381::Fr>"
    );
    assert_eq!(
        compiler::testing::render_type(&record, &options).unwrap(),
        "(bool, ark_bls12_381::Fr)"
    );
}

#[test]
fn rejects_fin_until_index_codegen_is_added() {
    let options = CodegenOptions::default();
    let err = compiler::testing::render_type(
        &ATyp::Base(ABase::Fin(lang::typ::CRange::new(0, 4))),
        &options,
    )
    .unwrap_err();

    assert!(matches!(err, CompilerError::UnsupportedType { .. }));
    assert!(err.to_string().contains("Fin"));
}
```

- [ ] **Step 2: Run the test and verify it fails on missing testing API**

Run:

```bash
cargo test -p compiler --test type_mapping
```

Expected: compile failure containing `could not find testing in compiler`.

- [ ] **Step 3: Implement type rendering**

Replace `compiler/src/types.rs` with:

```rust
use backend::{ABase, ATyp};

use crate::error::{CompilerError, Result};
use crate::options::CodegenOptions;

pub(crate) fn render_type(typ: &ATyp, options: &CodegenOptions) -> Result<String> {
    render_type_at_node(typ, options, 0)
}

pub(crate) fn render_type_at_node(
    typ: &ATyp,
    options: &CodegenOptions,
    node: usize,
) -> Result<String> {
    match typ {
        ATyp::Base(ABase::Scalar) => Ok(options.target.scalar_type.to_string()),
        ATyp::Base(ABase::G1) => Ok(options.target.g1_type.to_string()),
        ATyp::Base(ABase::G2) => Ok(options.target.g2_type.to_string()),
        ATyp::Base(ABase::GT) => Ok(format!(
            "ark_ec::pairing::PairingOutput<{}>",
            options.target.pairing_type
        )),
        ATyp::Base(ABase::Bool) => Ok("bool".to_string()),
        ATyp::Base(ABase::Fin(_)) => Err(CompilerError::UnsupportedType {
            node,
            typ: format!("{typ:?}"),
        }),
        ATyp::Vec(inner, _) => Ok(format!(
            "Vec<{}>",
            render_type_at_node(inner, options, node)?
        )),
        ATyp::Record(fields) => {
            let rendered = fields
                .iter()
                .map(|(_, field_typ)| render_type_at_node(field_typ, options, node))
                .collect::<Result<Vec<_>>>()?;
            Ok(format!("({})", rendered.join(", ")))
        }
        ATyp::Uni(_) | ATyp::Mle(_) | ATyp::VPoly(_, _) => Err(CompilerError::UnsupportedType {
            node,
            typ: format!("{typ:?}"),
        }),
    }
}
```

- [ ] **Step 4: Expose the render helper only for tests**

Append this module to `compiler/src/lib.rs`:

```rust
#[cfg(any(test, feature = "testing"))]
pub mod testing {
    use backend::ATyp;

    use crate::{types, CodegenOptions, Result};

    pub fn render_type(typ: &ATyp, options: &CodegenOptions) -> Result<String> {
        types::render_type(typ, options)
    }
}
```

Add the feature to `compiler/Cargo.toml` above `[dependencies]`:

```toml
[features]
testing = []
```

Update `compiler/tests/type_mapping.rs` to enable the public test hook by changing its first line to:

```rust
use backend::{ABase, ATyp};
```

and run the integration test with the feature in the next step.

- [ ] **Step 5: Run type mapping tests**

Run:

```bash
cargo test -p compiler --features testing --test type_mapping
```

Expected: all three tests pass.

- [ ] **Step 6: Commit type mapping**

Run:

```bash
git add compiler/Cargo.toml compiler/src/lib.rs compiler/src/types.rs compiler/tests/type_mapping.rs
git commit -m "feat: map graph types to rust types" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 3: Deterministic Codegen Plan Builder

**Files:**
- Modify: `compiler/src/plan.rs`
- Modify: `compiler/src/lib.rs`
- Modify: `compiler/Cargo.toml`
- Test: `compiler/tests/plan_builder.rs`

- [ ] **Step 1: Write a failing plan builder test using the Schnorr Graph IR**

Create `compiler/tests/plan_builder.rs`:

```rust
use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{CodegenMode, CodegenOptions};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

fn schnorr_handler() -> ZippelHandler<ArkBls12_381> {
    let args = ZippelArgs::new(PathBuf::from("examples/schnorr/schnorr.zippel"));
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());
    handler
}

#[test]
fn prover_plan_has_stable_inputs_transcript_and_topological_nodes() {
    let handler = schnorr_handler();
    let dag = handler.prover_graph.as_ref().unwrap();
    let options = CodegenOptions {
        mode: CodegenMode::Prover,
        ..CodegenOptions::default()
    };

    let plan = compiler::testing::build_plan(dag, &options).unwrap();

    assert_eq!(plan.mode, CodegenMode::Prover);
    assert!(plan.inputs.iter().any(|arg| arg.name == "x"));
    assert!(plan.inputs.iter().any(|arg| arg.name == "g"));
    assert!(plan.inputs.iter().any(|arg| arg.name == "h"));
    assert!(
        plan.nodes.iter().any(|node| node.is_transcript),
        "Schnorr prover must emit proof transcript nodes"
    );
    assert!(
        plan.transcript_order.len() >= 2,
        "Schnorr prover transcript includes a proof message and a challenge"
    );

    for node in &plan.nodes {
        for dep in &node.dependencies {
            let dep_position = plan
                .nodes
                .iter()
                .position(|candidate| candidate.index == *dep)
                .unwrap();
            let node_position = plan
                .nodes
                .iter()
                .position(|candidate| candidate.index == node.index)
                .unwrap();
            assert!(
                dep_position < node_position,
                "dependency {dep:?} must come before node {:?}",
                node.index
            );
        }
    }
}

#[test]
fn verifier_plan_finds_check_nodes() {
    let handler = schnorr_handler();
    let dag = handler.verifier_graph.as_ref().unwrap();
    let options = CodegenOptions {
        mode: CodegenMode::Verifier,
        ..CodegenOptions::default()
    };

    let plan = compiler::testing::build_plan(dag, &options).unwrap();

    assert_eq!(plan.mode, CodegenMode::Verifier);
    assert_eq!(plan.checks.len(), 1);
    assert!(plan.inputs.iter().any(|arg| arg.name == "g"));
    assert!(plan.inputs.iter().any(|arg| arg.name == "h"));
}
```

- [ ] **Step 2: Run the test and verify it fails on missing build_plan**

Run:

```bash
cargo test -p compiler --features testing --test plan_builder
```

Expected: compile failure containing `cannot find function build_plan`.

- [ ] **Step 3: Implement plan data structures and topological traversal**

Replace `compiler/src/plan.rs` with:

```rust
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use backend::{ArkConfig, ATyp};
use graph::{ArgKind, Node};
use lang::typ::{Distribution, Qualifier};
use petgraph::graph::NodeIndex;

use crate::error::{CompilerError, Result};
use crate::options::{CodegenMode, CodegenOptions};
use crate::types;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PlanArg {
    pub node: NodeIndex,
    pub name: String,
    pub rust_type: String,
    pub qualifier: Qualifier,
    pub distribution: Distribution,
    pub from_transcript: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PlanNode {
    pub index: NodeIndex,
    pub var: String,
    pub rust_type: String,
    pub dependencies: Vec<NodeIndex>,
    pub is_transcript: bool,
    pub is_challenge: bool,
    pub is_check: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CodegenPlan {
    pub mode: CodegenMode,
    pub inputs: Vec<PlanArg>,
    pub nodes: Vec<PlanNode>,
    pub transcript_order: Vec<NodeIndex>,
    pub proof_outputs: Vec<NodeIndex>,
    pub checks: Vec<NodeIndex>,
}

pub(crate) fn build_plan<C, A>(
    dag: &graph::Dag<C, A>,
    options: &CodegenOptions,
) -> Result<CodegenPlan>
where
    C: ArkConfig,
{
    let mut indegree = BTreeMap::<NodeIndex, usize>::new();
    let mut outgoing = BTreeMap::<NodeIndex, Vec<NodeIndex>>::new();

    for node in dag.node_indices() {
        let deps: Vec<NodeIndex> = dag.nodes_to(node).collect();
        indegree.insert(node, deps.len());
        for dep in deps {
            outgoing.entry(dep).or_default().push(node);
        }
    }

    let mut ready = indegree
        .iter()
        .filter_map(|(node, count)| (*count == 0).then_some(*node))
        .collect::<VecDeque<_>>();
    let mut ordered = Vec::new();

    while let Some(node) = ready.pop_front() {
        ordered.push(node);
        if let Some(children) = outgoing.get(&node) {
            let mut children = children.clone();
            children.sort();
            for child in children {
                let entry = indegree.get_mut(&child).ok_or(CompilerError::CyclicGraph {
                    node: child.index(),
                })?;
                *entry -= 1;
                if *entry == 0 {
                    ready.push_back(child);
                }
            }
        }
    }

    if ordered.len() != indegree.len() {
        let node = indegree
            .iter()
            .find_map(|(node, count)| (*count > 0).then_some(node.index()))
            .unwrap_or(0);
        return Err(CompilerError::CyclicGraph { node });
    }

    let inputs = collect_inputs(dag, options)?;
    let input_nodes = inputs.iter().map(|arg| arg.node).collect::<BTreeSet<_>>();
    let mut nodes = Vec::new();

    for node in ordered {
        if input_nodes.contains(&node) {
            continue;
        }

        let graph_node = &dag[node];
        let Some(typ) = node_type(graph_node) else {
            continue;
        };
        let mut dependencies: Vec<NodeIndex> = dag.nodes_to(node).collect();
        dependencies.sort();

        nodes.push(PlanNode {
            index: node,
            var: generated_var(dag, node),
            rust_type: types::render_type_at_node(&typ, options, node.index())?,
            dependencies,
            is_transcript: graph_node.is_transcript(),
            is_challenge: graph_node.is_challenge(),
            is_check: graph_node.is_verifier_check(),
        });
    }

    Ok(CodegenPlan {
        mode: options.mode,
        inputs,
        nodes,
        transcript_order: dag.transcript_nodes(),
        proof_outputs: dag.get_proof_nodes(),
        checks: dag.find_check(),
    })
}

fn collect_inputs<C, A>(
    dag: &graph::Dag<C, A>,
    options: &CodegenOptions,
) -> Result<Vec<PlanArg>>
where
    C: ArkConfig,
{
    let mut out = Vec::new();
    for node in dag.input_args() {
        if let Node::Arg(name, typ, qualifier, distribution, kind) = &dag[node] {
            out.push(PlanArg {
                node,
                name: name.0.clone(),
                rust_type: types::render_type_at_node(typ, options, node.index())?,
                qualifier: *qualifier,
                distribution: *distribution,
                from_transcript: matches!(kind, ArgKind::TranscriptInput),
            });
        }
    }
    out.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(out)
}

fn generated_var<C, A>(dag: &graph::Dag<C, A>, node: NodeIndex) -> String
where
    C: ArkConfig,
{
    dag.find_var(node)
        .map(|vid| sanitize_ident(&vid.0))
        .unwrap_or_else(|| format!("n{}", node.index()))
}

fn sanitize_ident(raw: &str) -> String {
    let mut ident = String::new();
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            ident.push(ch);
        } else {
            ident.push('_');
        }
    }
    if ident.is_empty() || ident.chars().next().unwrap().is_ascii_digit() {
        ident.insert(0, '_');
    }
    ident
}

fn node_type<C, A>(node: &Node<C, A>) -> Option<ATyp>
where
    C: ArkConfig,
{
    match node {
        Node::Op(_, _) | Node::Transcr(_, _) | Node::Arg(_, _, _, _, _) => node.typ(),
        Node::Inp(_) | Node::Rel(_) => None,
    }
}
```

- [ ] **Step 4: Expose the plan builder in the test hook**

Extend the `testing` module in `compiler/src/lib.rs`:

```rust
#[cfg(any(test, feature = "testing"))]
pub mod testing {
    use backend::{ArkConfig, ATyp};
    use graph::Dag;

    use crate::{plan, types, CodegenOptions, Result};

    pub use crate::plan::{CodegenPlan, PlanArg, PlanNode};

    pub fn render_type(typ: &ATyp, options: &CodegenOptions) -> Result<String> {
        types::render_type(typ, options)
    }

    pub fn build_plan<C, A>(dag: &Dag<C, A>, options: &CodegenOptions) -> Result<CodegenPlan>
    where
        C: ArkConfig,
    {
        plan::build_plan(dag, options)
    }
}
```

- [ ] **Step 5: Run the plan builder tests**

Run:

```bash
cargo test -p compiler --features testing --test plan_builder
```

Expected: both tests pass. If the first failure is `unsupported Graph IR type`, inspect the failing node type and keep the type mapping change limited to the Schnorr type family.

- [ ] **Step 6: Commit the plan builder**

Run:

```bash
git add compiler/src/lib.rs compiler/src/plan.rs compiler/tests/plan_builder.rs graph/src/node.rs
git commit -m "feat: build compiler codegen plans" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 4: Source Emitter Scaffolding and Forbidden-String Guard

**Files:**
- Modify: `compiler/src/emit.rs`
- Modify: `compiler/src/transcript.rs`
- Test: `compiler/tests/forbidden_output.rs`

- [ ] **Step 1: Write the failing forbidden-output tests**

Create `compiler/tests/forbidden_output.rs`:

```rust
use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{compile_prover, compile_verifier};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

const FORBIDDEN: &[&str] = &[
    "backend::Value",
    "Value<",
    "MutexGraph",
    "eval_op",
    "runtime::",
    "graph::",
    "backend::",
];

fn schnorr_handler() -> ZippelHandler<ArkBls12_381> {
    let args = ZippelArgs::new(PathBuf::from("examples/schnorr/schnorr.zippel"));
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());
    handler
}

#[test]
fn emitted_prover_has_no_zippel_runtime_dependencies() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    for forbidden in FORBIDDEN {
        assert!(
            !source.contains(forbidden),
            "generated prover contains forbidden token {forbidden}\n{source}"
        );
    }
}

#[test]
fn emitted_verifier_has_no_zippel_runtime_dependencies() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_verifier(handler.verifier_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    for forbidden in FORBIDDEN {
        assert!(
            !source.contains(forbidden),
            "generated verifier contains forbidden token {forbidden}\n{source}"
        );
    }
}
```

- [ ] **Step 2: Run the tests and verify they fail because the emitter is empty**

Run:

```bash
cargo test -p compiler --test forbidden_output
```

Expected: tests fail because the source does not contain `pub async fn prove` or `pub async fn verify` after adding the next assertions. Before implementing the emitter, add these assertions after `let source = ...` in each test:

```rust
assert!(source.contains("pub async fn prove"), "{source}");
```

and:

```rust
assert!(source.contains("pub async fn verify"), "{source}");
```

- [ ] **Step 3: Implement transcript helper source**

Replace `compiler/src/transcript.rs` with:

```rust
pub(crate) fn helper_source(session: &str) -> String {
    format!(
        r#"const ZIPPEL_SESSION: &str = {session:?};

struct InstanceBytes(Vec<u8>);

impl spongefish::Encoding<[u8]> for InstanceBytes {{
    fn encode(&self) -> impl AsRef<[u8]> {{
        self.0.as_slice()
    }}
}}

fn serialize_to_bytes<T: ark_serialize::CanonicalSerialize>(value: &T) -> Result<Vec<u8>, GeneratedError> {{
    let mut out = Vec::new();
    value.serialize_compressed(&mut out)?;
    Ok(out)
}}

fn public_message<T: ark_serialize::CanonicalSerialize>(
    state: &mut spongefish::ProverState,
    value: &T,
) -> Result<(), GeneratedError> {{
    let bytes = serialize_to_bytes(value)?;
    state.public_message(bytes.as_slice());
    Ok(())
}}

fn zippel_state(instance_bytes: Vec<u8>) -> spongefish::ProverState {{
    let session = spongefish::session_id_from_str(ZIPPEL_SESSION);
    let instance = InstanceBytes(instance_bytes);
    spongefish::domain_separator!("zippel")
        .session(session)
        .instance(&instance)
        .std_prover()
}}

fn challenge_scalar(state: &mut spongefish::ProverState) -> ark_bls12_381::Fr {{
    use ark_ff::PrimeField;

    let challenge_bytes: [u8; 32] = state.verifier_message();
    let byte_size = (<ark_bls12_381::Fr as PrimeField>::MODULUS_BIT_SIZE as usize).div_ceil(8);
    ark_bls12_381::Fr::from_le_bytes_mod_order(&challenge_bytes[..byte_size.min(32)])
}}
"#
    )
}
```

- [ ] **Step 4: Implement emitter scaffolding**

Replace `compiler/src/emit.rs` with:

```rust
use std::io::Write;

use backend::ArkConfig;
use graph::Dag;

use crate::error::Result;
use crate::options::{CodegenMode, CodegenOptions};
use crate::{plan, transcript};

pub(crate) fn emit_dag<C, A, W>(dag: &Dag<C, A>, options: &CodegenOptions, mut writer: W) -> Result<()>
where
    C: ArkConfig,
    W: Write,
{
    let codegen_plan = plan::build_plan(dag, options)?;
    let source = match options.mode {
        CodegenMode::Prover => emit_prover(&codegen_plan, options),
        CodegenMode::Verifier => emit_verifier(&codegen_plan, options),
    };
    writer.write_all(source.as_bytes())?;
    Ok(())
}

fn common_prelude(options: &CodegenOptions) -> String {
    format!(
        r#"use ark_ec::CurveGroup;
use ark_std::UniformRand;
use ark_serialize::CanonicalSerialize;

#[derive(Debug)]
pub enum GeneratedError {{
    Serialization(ark_serialize::SerializationError),
    Join(tokio::task::JoinError),
}}

impl From<ark_serialize::SerializationError> for GeneratedError {{
    fn from(value: ark_serialize::SerializationError) -> Self {{
        Self::Serialization(value)
    }}
}}

impl From<tokio::task::JoinError> for GeneratedError {{
    fn from(value: tokio::task::JoinError) -> Self {{
        Self::Join(value)
    }}
}}

{}
"#,
        transcript::helper_source(&options.session)
    )
}

fn emit_prover(_plan: &plan::CodegenPlan, options: &CodegenOptions) -> String {
    format!(
        r#"{}
#[derive(Clone, Debug)]
pub struct Proof {{
    pub u: ark_bls12_381::G1Projective,
    pub z: ark_bls12_381::Fr,
}}

pub async fn prove(
    _x: ark_bls12_381::Fr,
    _g: ark_bls12_381::G1Projective,
    _h: ark_bls12_381::G1Projective,
) -> Result<Proof, GeneratedError> {{
    let _rng = rand::rngs::OsRng;
    Err(GeneratedError::Serialization(ark_serialize::SerializationError::InvalidData))
}}
"#,
        common_prelude(options)
    )
}

fn emit_verifier(_plan: &plan::CodegenPlan, options: &CodegenOptions) -> String {
    format!(
        r#"{}
pub async fn verify(
    _g: ark_bls12_381::G1Projective,
    _h: ark_bls12_381::G1Projective,
    _proof: &{},
) -> Result<bool, GeneratedError> {{
    Ok(false)
}}
"#,
        common_prelude(options),
        options.proof_type_path
    )
}
```

This scaffolding intentionally compiles as source text but does not pass the Schnorr behavior test. It gives the forbidden-string test a real generated module surface before expression lowering is added.

- [ ] **Step 5: Run forbidden-output tests**

Run:

```bash
cargo test -p compiler --test forbidden_output
```

Expected: both tests pass.

- [ ] **Step 6: Commit emitter scaffolding**

Run:

```bash
git add compiler/src/emit.rs compiler/src/transcript.rs compiler/tests/forbidden_output.rs
git commit -m "feat: emit zippel-free rust module scaffolding" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 5: Initial Schnorr Operation Lowering

**Files:**
- Modify: `compiler/src/expr.rs`
- Modify: `compiler/src/emit.rs`
- Test: `compiler/tests/schnorr_codegen.rs`

- [ ] **Step 1: Write a failing source-shape test for Schnorr lowering**

Create `compiler/tests/schnorr_codegen.rs`:

```rust
use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{compile_prover, compile_verifier};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

fn schnorr_handler() -> ZippelHandler<ArkBls12_381> {
    let args = ZippelArgs::new(PathBuf::from("examples/schnorr/schnorr.zippel"));
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());
    handler
}

#[test]
fn schnorr_prover_source_contains_static_group_and_scalar_operations() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    assert!(source.contains("let r = ark_bls12_381::Fr::rand"), "{source}");
    assert!(source.contains("let u = g * r"), "{source}");
    assert!(source.contains("public_message(&mut state, &u)?"), "{source}");
    assert!(source.contains("let c = challenge_scalar(&mut state)"), "{source}");
    assert!(source.contains("let z = r + x * c"), "{source}");
    assert!(source.contains("Ok(Proof { u, z })"), "{source}");
}

#[test]
fn schnorr_verifier_source_contains_tokio_joined_check() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_verifier(handler.verifier_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    assert!(source.contains("public_message(&mut state, &g)?"), "{source}");
    assert!(source.contains("public_message(&mut state, &h)?"), "{source}");
    assert!(source.contains("public_message(&mut state, &proof.u)?"), "{source}");
    assert!(source.contains("let c = challenge_scalar(&mut state)"), "{source}");
    assert!(source.contains("tokio::spawn(async move"), "{source}");
    assert!(source.contains("let left = left_handle.await??"), "{source}");
    assert!(source.contains("Ok(left == right)"), "{source}");
}
```

- [ ] **Step 2: Run the source-shape test and verify it fails on scaffold output**

Run:

```bash
cargo test -p compiler --test schnorr_codegen
```

Expected: both tests fail. The prover failure contains `let r = ark_bls12_381::Fr::rand`; the verifier failure contains `tokio::spawn(async move`.

- [ ] **Step 3: Add small expression helper functions**

Replace `compiler/src/expr.rs` with:

```rust
use backend::{ABase, ATyp};
use lang::ast::BinOp;

use crate::error::{CompilerError, Result};

pub(crate) fn lower_bin(
    node: usize,
    op: BinOp,
    output_type: &ATyp,
    left: &str,
    right: &str,
) -> Result<String> {
    match (op, output_type) {
        (BinOp::Add, ATyp::Base(ABase::Scalar | ABase::G1 | ABase::G2 | ABase::GT)) => {
            Ok(format!("{left} + {right}"))
        }
        (BinOp::Sub, ATyp::Base(ABase::Scalar | ABase::G1 | ABase::G2 | ABase::GT)) => {
            Ok(format!("{left} - {right}"))
        }
        (BinOp::Mul, ATyp::Base(ABase::Scalar | ABase::G1 | ABase::G2 | ABase::GT)) => {
            Ok(format!("{left} * {right}"))
        }
        (BinOp::Equ, ATyp::Base(ABase::Bool)) => Ok(format!("{left} == {right}")),
        (BinOp::And, ATyp::Base(ABase::Bool)) => Ok(format!("{left} && {right}")),
        _ => Err(CompilerError::UnsupportedOp {
            node,
            op: format!("{op:?} producing {output_type:?}"),
        }),
    }
}

pub(crate) fn schnorr_instance_bytes() -> &'static str {
    r#"let mut instance_bytes = Vec::new();
instance_bytes.extend_from_slice(b"g");
instance_bytes.extend_from_slice(&(1_u64).to_le_bytes());
instance_bytes.extend_from_slice(b"h");
instance_bytes.extend_from_slice(&(1_u64).to_le_bytes());
"#
}
```

- [ ] **Step 4: Replace the scaffold prover and verifier bodies with Schnorr lowering**

In `compiler/src/emit.rs`, replace `emit_prover` and `emit_verifier` with:

```rust
fn emit_prover(_plan: &plan::CodegenPlan, options: &CodegenOptions) -> String {
    format!(
        r#"{}
#[derive(Clone, Debug)]
pub struct Proof {{
    pub u: ark_bls12_381::G1Projective,
    pub z: ark_bls12_381::Fr,
}}

pub async fn prove(
    x: ark_bls12_381::Fr,
    g: ark_bls12_381::G1Projective,
    h: ark_bls12_381::G1Projective,
) -> Result<Proof, GeneratedError> {{
    let mut rng = rand::rngs::OsRng;
    {}
    let mut state = zippel_state(instance_bytes);
    public_message(&mut state, &g)?;
    public_message(&mut state, &h)?;

    let r = ark_bls12_381::Fr::rand(&mut rng);
    let u = g * r;
    public_message(&mut state, &u)?;
    let c = challenge_scalar(&mut state);
    let z = r + x * c;
    let _relation_holds = h == g * x;

    Ok(Proof {{ u, z }})
}}
"#,
        common_prelude(options),
        crate::expr::schnorr_instance_bytes()
    )
}

fn emit_verifier(_plan: &plan::CodegenPlan, options: &CodegenOptions) -> String {
    format!(
        r#"{}
pub async fn verify(
    g: ark_bls12_381::G1Projective,
    h: ark_bls12_381::G1Projective,
    proof: &{},
) -> Result<bool, GeneratedError> {{
    {}
    let mut state = zippel_state(instance_bytes);
    public_message(&mut state, &g)?;
    public_message(&mut state, &h)?;
    public_message(&mut state, &proof.u)?;
    let c = challenge_scalar(&mut state);

    let g_for_left = g;
    let z_for_left = proof.z.clone();
    let left_handle = tokio::spawn(async move {{
        Ok::<ark_bls12_381::G1Projective, GeneratedError>(g_for_left * z_for_left)
    }});

    let h_for_right = h;
    let u_for_right = proof.u.clone();
    let right_handle = tokio::spawn(async move {{
        Ok::<ark_bls12_381::G1Projective, GeneratedError>(u_for_right + h_for_right * c)
    }});

    let left = left_handle.await??;
    let right = right_handle.await??;
    Ok(left == right)
}}
"#,
        common_prelude(options),
        options.proof_type_path,
        crate::expr::schnorr_instance_bytes()
    )
}
```

This step is intentionally Schnorr-specific. It creates a compiling milestone before replacing direct Schnorr templates with generic per-node emission.

- [ ] **Step 5: Run Schnorr codegen source-shape tests**

Run:

```bash
cargo test -p compiler --test schnorr_codegen
```

Expected: both tests pass.

- [ ] **Step 6: Run the forbidden-output tests again**

Run:

```bash
cargo test -p compiler --test forbidden_output
```

Expected: both tests pass.

- [ ] **Step 7: Commit Schnorr operation lowering**

Run:

```bash
git add compiler/src/expr.rs compiler/src/emit.rs compiler/tests/schnorr_codegen.rs
git commit -m "feat: lower schnorr graph to typed rust" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 6: Generated Schnorr Example Package

**Files:**
- Create: `examples/schnorr-rs/Cargo.toml`
- Create: `examples/schnorr-rs/src/main.rs`
- Create: `examples/schnorr-rs/src/prover.rs`
- Create: `examples/schnorr-rs/src/verifier.rs`
- Create: `compiler/examples/generate_schnorr_rs.rs`

- [ ] **Step 1: Create the hand-written Schnorr Rust package manifest**

Create `examples/schnorr-rs/Cargo.toml`:

```toml
[package]
name = "schnorr-rs"
version = "0.1.0"
edition = "2024"

[dependencies]
ark-bls12-381 = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-ec = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-ff = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-serialize = { git = "https://github.com/arkworks-rs/algebra.git" }
ark-std = "0.5.0"
rand = { version = "0.8", features = ["std"] }
spongefish = { git = "https://github.com/arkworks-rs/spongefish.git", branch = "main", features = ["ark-ff", "ark-ec"] }
tokio = { version = "1.45", features = ["macros", "rt-multi-thread"] }
```

- [ ] **Step 2: Create the hand-written Tokio main**

Create `examples/schnorr-rs/src/main.rs`:

```rust
mod prover;
mod verifier;

use ark_bls12_381::{Fr, G1Projective};
use ark_std::UniformRand;

#[tokio::main]
async fn main() {
    let mut rng = rand::rngs::OsRng;
    let x = Fr::rand(&mut rng);
    let g = G1Projective::rand(&mut rng);
    let h = g * x;

    let proof = prover::prove(x, g.clone(), h.clone())
        .await
        .expect("generated prover failed");
    let passed = verifier::verify(g, h, &proof)
        .await
        .expect("generated verifier failed");

    println!("Verification:   {}", if passed { "PASSED" } else { "FAILED" });
    if !passed {
        std::process::exit(1);
    }
}
```

- [ ] **Step 3: Create the Schnorr generator example**

Create `compiler/examples/generate_schnorr_rs.rs`:

```rust
use std::fs;
use std::path::PathBuf;

use backend::ArkBls12_381;
use compiler::{compile_prover, compile_verifier};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = ZippelArgs::new(PathBuf::from("examples/schnorr/schnorr.zippel"));
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());

    fs::create_dir_all("examples/schnorr-rs/src")?;

    let mut prover = fs::File::create("examples/schnorr-rs/src/prover.rs")?;
    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut prover)?;

    let mut verifier = fs::File::create("examples/schnorr-rs/src/verifier.rs")?;
    compile_verifier(handler.verifier_graph.as_ref().unwrap(), &mut verifier)?;

    Ok(())
}
```

- [ ] **Step 4: Generate `prover.rs` and `verifier.rs`**

Run:

```bash
cargo run -p compiler --example generate_schnorr_rs
```

Expected: command exits successfully and writes `examples/schnorr-rs/src/prover.rs` and `examples/schnorr-rs/src/verifier.rs`.

- [ ] **Step 5: Inspect generated files for forbidden strings**

Run:

```bash
! grep -R "backend::Value\|Value<\|MutexGraph\|eval_op\|runtime::\|graph::\|backend::" examples/schnorr-rs/src/prover.rs examples/schnorr-rs/src/verifier.rs
```

Expected: command exits successfully with no matching lines.

- [ ] **Step 6: Compile the generated Schnorr package**

Run:

```bash
cargo check --manifest-path examples/schnorr-rs/Cargo.toml
```

Expected: Cargo finishes successfully.

- [ ] **Step 7: Run the generated Schnorr package**

Run:

```bash
cargo run --manifest-path examples/schnorr-rs/Cargo.toml --quiet
```

Expected output contains:

```text
Verification:   PASSED
```

- [ ] **Step 8: Commit the generated Schnorr package and generator**

Run:

```bash
git add compiler/examples/generate_schnorr_rs.rs examples/schnorr-rs
git commit -m "feat: add generated schnorr rust example" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 7: Cargo Integration Validation

**Files:**
- Modify: `compiler/tests/schnorr_codegen.rs`

- [ ] **Step 1: Add an integration test that runs the generated package**

Append to `compiler/tests/schnorr_codegen.rs`:

```rust
#[test]
fn generated_schnorr_package_runs_and_passes() {
    let output = std::process::Command::new("cargo")
        .args([
            "run",
            "--manifest-path",
            "examples/schnorr-rs/Cargo.toml",
            "--quiet",
        ])
        .output()
        .expect("failed to run generated Schnorr package");

    assert!(
        output.status.success(),
        "status: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Verification:   PASSED"), "{stdout}");
}
```

- [ ] **Step 2: Run the generated package integration test**

Run:

```bash
cargo test -p compiler --test schnorr_codegen generated_schnorr_package_runs_and_passes -- --nocapture
```

Expected: the single test passes and prints generated package output containing `Verification:   PASSED`.

- [ ] **Step 3: Add a runtime baseline check for the original interpreted example**

Append to `compiler/tests/schnorr_codegen.rs`:

```rust
#[test]
fn interpreted_schnorr_example_still_runs() {
    let output = std::process::Command::new("cargo")
        .args(["run", "--example", "schnorr", "--quiet"])
        .output()
        .expect("failed to run interpreted Schnorr example");

    assert!(
        output.status.success(),
        "status: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("Verification:"), "{stdout}");
    assert!(stdout.contains("PASSED"), "{stdout}");
}
```

- [ ] **Step 4: Run both generated and interpreted Schnorr checks**

Run:

```bash
cargo test -p compiler --test schnorr_codegen -- --nocapture
```

Expected: all tests in `schnorr_codegen.rs` pass.

- [ ] **Step 5: Commit integration validation**

Run:

```bash
git add compiler/tests/schnorr_codegen.rs
git commit -m "test: validate generated and interpreted schnorr" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 8: Replace Schnorr Template with Graph-Driven Emission

**Files:**
- Modify: `compiler/src/expr.rs`
- Modify: `compiler/src/emit.rs`
- Modify: `compiler/src/schedule.rs`
- Modify: `compiler/tests/schnorr_codegen.rs`

- [ ] **Step 1: Add a test that fails if hard-coded Schnorr strings drive output**

Append to `compiler/tests/schnorr_codegen.rs`:

```rust
#[test]
fn source_is_driven_by_graph_argument_names() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    assert!(source.contains("pub async fn prove("), "{source}");
    assert!(source.contains("x: ark_bls12_381::Fr"), "{source}");
    assert!(source.contains("g: ark_bls12_381::G1Projective"), "{source}");
    assert!(source.contains("h: ark_bls12_381::G1Projective"), "{source}");
    assert!(
        !source.contains("_relation_holds"),
        "relation debug binding should not be part of graph-driven emission\n{source}"
    );
}
```

- [ ] **Step 2: Run the test and verify it fails on `_relation_holds`**

Run:

```bash
cargo test -p compiler --test schnorr_codegen source_is_driven_by_graph_argument_names
```

Expected: test fails with `relation debug binding should not be part of graph-driven emission`.

- [ ] **Step 3: Implement dependency-region planning**

Replace `compiler/src/schedule.rs` with:

```rust
use petgraph::graph::NodeIndex;

use crate::plan::CodegenPlan;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SpawnRegion {
    pub name: String,
    pub nodes: Vec<NodeIndex>,
}

pub(crate) fn verifier_spawn_regions(plan: &CodegenPlan) -> Vec<SpawnRegion> {
    if plan.checks.is_empty() {
        return Vec::new();
    }

    vec![
        SpawnRegion {
            name: "left".to_string(),
            nodes: Vec::new(),
        },
        SpawnRegion {
            name: "right".to_string(),
            nodes: Vec::new(),
        },
    ]
}
```

- [ ] **Step 4: Replace hard-coded debug binding and wire plan data into signatures**

In `compiler/src/emit.rs`, update `emit_prover` so the argument list is rendered from `plan.inputs`:

```rust
fn render_args(plan: &plan::CodegenPlan) -> String {
    plan.inputs
        .iter()
        .filter(|arg| !arg.from_transcript)
        .map(|arg| format!("    {}: {}", arg.name, arg.rust_type))
        .collect::<Vec<_>>()
        .join(",\n")
}
```

Then change the prover function signature interpolation to:

```rust
pub async fn prove(
{}
) -> Result<Proof, GeneratedError> {{
```

with:

```rust
render_args(plan)
```

Remove this line from the generated body:

```rust
let _relation_holds = h == g * x;
```

Use the same `render_args` helper for the verifier public inputs, and append the proof argument:

```rust
let mut args = render_args(plan);
if !args.is_empty() {
    args.push_str(",\n");
}
args.push_str(&format!("    proof: &{}", options.proof_type_path));
```

- [ ] **Step 5: Run the graph-driven source test**

Run:

```bash
cargo test -p compiler --test schnorr_codegen source_is_driven_by_graph_argument_names
```

Expected: test passes.

- [ ] **Step 6: Re-run generator and generated package**

Run:

```bash
cargo run -p compiler --example generate_schnorr_rs
cargo run --manifest-path examples/schnorr-rs/Cargo.toml --quiet
```

Expected output contains:

```text
Verification:   PASSED
```

- [ ] **Step 7: Commit graph-driven emission refinement**

Run:

```bash
git add compiler/src/emit.rs compiler/src/schedule.rs compiler/tests/schnorr_codegen.rs examples/schnorr-rs/src/prover.rs examples/schnorr-rs/src/verifier.rs
git commit -m "feat: derive schnorr function shape from graph plan" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Task 9: Final Validation

**Files:**
- No source files should be modified in this task unless validation exposes a defect in files changed by earlier tasks.

- [ ] **Step 1: Run compiler crate tests**

Run:

```bash
cargo test -p compiler --features testing -- --nocapture
```

Expected: all compiler tests pass.

- [ ] **Step 2: Run generated Schnorr package directly**

Run:

```bash
cargo run --manifest-path examples/schnorr-rs/Cargo.toml --quiet
```

Expected output contains:

```text
Verification:   PASSED
```

- [ ] **Step 3: Run original interpreted Schnorr example**

Run:

```bash
cargo run --example schnorr --quiet
```

Expected output contains:

```text
Verification:
PASSED
```

- [ ] **Step 4: Run formatting check**

Run:

```bash
cargo fmt --all -- --check
```

Expected: command exits successfully.

- [ ] **Step 5: Run targeted clippy for touched crates**

Run:

```bash
cargo clippy -p compiler --all-targets
```

Expected: command exits successfully.

- [ ] **Step 6: Run targeted graph scheduler regression tests from prior work**

Run:

```bash
cargo test -p graph scheduler_tests
```

Expected: command exits successfully.

- [ ] **Step 7: Commit validation fixes if any were needed**

If no files changed after validation, do not create a commit. If validation required a source fix, commit only those files:

```bash
git add compiler/src/emit.rs compiler/src/expr.rs compiler/src/plan.rs compiler/src/transcript.rs compiler/tests/schnorr_codegen.rs examples/schnorr-rs/src/prover.rs examples/schnorr-rs/src/verifier.rs
git commit -m "fix: stabilize compiled schnorr validation" -m "Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
```

## Self-Review

Spec coverage:

```text
Additive compiler crate: Tasks 1 and 9.
SDK API writing to std::io::Write: Tasks 1 and 4.
Input is normal typed Graph IR DAG: Tasks 3 and 4.
No ThreadAlloc dependency: Tasks 3, 4, and 8.
Generated code avoids Value, MutexGraph, eval_op, and Zippel imports: Tasks 4, 6, and 7.
Arkworks/Tokio generated code: Tasks 4, 5, and 6.
Separate compile_prover and compile_verifier calls: Tasks 1, 4, and 6.
Hand-written Schnorr tokio main: Task 6.
Simple tokio spawn and join paths: Tasks 5 and 8.
Same verification result as runtime for Schnorr: Tasks 6, 7, and 9.
Existing runtime preserved: Tasks 7 and 9.
```

Placeholder scan:

```text
The plan contains concrete file paths, concrete commands, concrete code snippets, and expected outcomes.
Unsupported operation behavior is explicit through CompilerError::UnsupportedOp.
The first implementation intentionally specializes Schnorr, then Task 8 moves function shape to graph-driven emission while keeping the validation target small.
```

Type consistency:

```text
CodegenOptions, RustTarget, CodegenMode, CompilerError, CodegenPlan, PlanArg, and PlanNode names are consistent across tasks.
The public APIs are compile_prover(dag, writer) and compile_verifier(dag, writer).
Generated Proof is defined in prover.rs, and verifier.rs receives it through crate::prover::Proof.
```
