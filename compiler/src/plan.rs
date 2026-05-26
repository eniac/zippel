//! Deterministic code generation plan construction from Graph IR DAGs.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use backend::ArkConfig;
use graph::{ArgKind, Node};
use lang::typ::{Distribution, Qualifier};
use petgraph::graph::NodeIndex;

use crate::error::{CompilerError, Result};
use crate::options::{CodegenMode, CodegenOptions};
use crate::types;

// ---------------------------------------------------------------------------
// Public data structures (re-exported via compiler::testing when the feature
// gate is active; the *module* itself stays private).
// ---------------------------------------------------------------------------

/// A single typed input argument in the codegen plan.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub struct PlanArg {
    pub node: NodeIndex,
    pub name: String,
    pub rust_type: String,
    pub qualifier: Qualifier,
    pub distribution: Distribution,
    pub from_transcript: bool,
}

/// A single non-input node in the codegen plan.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub struct PlanNode {
    pub index: NodeIndex,
    pub var: String,
    pub rust_type: String,
    pub dependencies: Vec<NodeIndex>,
    pub is_transcript: bool,
    pub is_challenge: bool,
    pub is_check: bool,
}

/// A fully-resolved, deterministic codegen plan derived from a Graph IR DAG.
///
/// This plan records everything needed for source emission without any
/// reference back to the DAG: inputs, topologically-ordered nodes,
/// transcript order, proof outputs, and verifier checks.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub struct CodegenPlan {
    pub mode: CodegenMode,
    pub inputs: Vec<PlanArg>,
    pub nodes: Vec<PlanNode>,
    pub transcript_order: Vec<NodeIndex>,
    pub proof_outputs: Vec<NodeIndex>,
    pub checks: Vec<NodeIndex>,
}

// ---------------------------------------------------------------------------
// Identifier sanitization
// ---------------------------------------------------------------------------

/// Sanitize a raw variable name into a valid Rust identifier fragment.
///
/// Rules:
/// - Preserve ASCII alphanumeric characters and `_`.
/// - Replace any other character with `_`.
/// - Prefix with `_` if the result is empty or starts with a digit.
#[allow(dead_code)]
fn sanitize_ident(raw: &str) -> String {
    let mut out: String = raw
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();

    if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

// ---------------------------------------------------------------------------
// Plan builder
// ---------------------------------------------------------------------------

/// Build a deterministic [`CodegenPlan`] from `dag` using `options`.
///
/// # Errors
/// Returns [`CompilerError::CyclicGraph`] if the DAG contains a cycle.
#[allow(dead_code)]
pub(crate) fn build_plan<C, A>(
    dag: &graph::Dag<C, A>,
    options: &CodegenOptions,
) -> Result<CodegenPlan>
where
    C: ArkConfig,
{
    // ------------------------------------------------------------------
    // Step 1 – Kahn-style deterministic topological sort.
    // ------------------------------------------------------------------

    // Count incoming edges for every node so we can identify "ready" roots.
    let all_nodes: Vec<NodeIndex> = {
        let mut v: Vec<NodeIndex> = dag.node_indices().collect();
        v.sort();
        v
    };

    let mut in_degree: BTreeMap<NodeIndex, usize> = BTreeMap::new();
    for &n in &all_nodes {
        in_degree.entry(n).or_insert(0);
        // Collect *unique* predecessors to avoid counting multi-edges.
        let preds: BTreeSet<NodeIndex> = dag.nodes_to(n).collect();
        *in_degree.get_mut(&n).unwrap() += preds.len();
        // Ensure successors also have an entry.
        for s in dag.nodes_from(n) {
            in_degree.entry(s).or_insert(0);
        }
    }

    // Seed the queue with nodes that have no predecessors, in NodeIndex order.
    let mut queue: VecDeque<NodeIndex> = in_degree
        .iter()
        .filter(|&(_, &d)| d == 0)
        .map(|(&n, _)| n)
        .collect();

    let mut topo_order: Vec<NodeIndex> = Vec::with_capacity(all_nodes.len());

    while let Some(n) = queue.pop_front() {
        topo_order.push(n);

        // Collect successors, decrement their in-degree, enqueue newly ready.
        let mut successors: Vec<NodeIndex> = dag
            .nodes_from(n)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        successors.sort();

        for s in successors {
            let d = in_degree.get_mut(&s).expect("successor must be tracked");
            *d = d.saturating_sub(1);
            if *d == 0 {
                queue.push_back(s);
            }
        }
    }

    // If we did not visit all nodes there is a cycle.
    if topo_order.len() != all_nodes.len() {
        // Report the first node we could not reach.
        let visited: BTreeSet<NodeIndex> = topo_order.iter().cloned().collect();
        let unvisited = all_nodes
            .iter()
            .find(|n| !visited.contains(*n))
            .expect("at least one unvisited node");
        return Err(CompilerError::CyclicGraph {
            node: unvisited.index(),
        });
    }

    // ------------------------------------------------------------------
    // Step 2 – Collect input arguments.
    // ------------------------------------------------------------------
    let input_indices: BTreeSet<NodeIndex> = dag.input_args().into_iter().collect();

    let mut inputs: Vec<PlanArg> = input_indices
        .iter()
        .map(|&idx| {
            let graph_node = &dag[idx];
            if let Node::Arg(name, typ, qualifier, distribution, kind) = graph_node {
                let rust_type = types::render_type_at_node(typ, options, idx.index())?;
                Ok(PlanArg {
                    node: idx,
                    name: name.0.clone(),
                    rust_type,
                    qualifier: *qualifier,
                    distribution: *distribution,
                    from_transcript: matches!(kind, ArgKind::TranscriptInput),
                })
            } else {
                // input_args() only returns Arg nodes; this branch is unreachable.
                Err(CompilerError::UnsupportedNode {
                    node: idx.index(),
                    detail: "non-Arg node in input_args()".to_string(),
                })
            }
        })
        .collect::<Result<Vec<_>>>()?;

    // Stable external signatures: sort by name.
    inputs.sort_by(|a, b| a.name.cmp(&b.name));

    // ------------------------------------------------------------------
    // Step 3 – Build PlanNodes for non-input nodes.
    // ------------------------------------------------------------------
    let mut nodes: Vec<PlanNode> = Vec::new();

    for &idx in &topo_order {
        // Skip input arg nodes.
        if input_indices.contains(&idx) {
            continue;
        }

        let graph_node = &dag[idx];

        // Skip structural markers (Inp/Rel) which carry no type.
        let typ = match graph_node.typ() {
            Some(t) => t,
            None => continue,
        };

        let rust_type = types::render_type_at_node(&typ, options, idx.index())?;

        // Variable name: prefer DAG vctx, then arg name, else synthesise.
        let var = match dag.find_var(idx) {
            Some(vid) => sanitize_ident(&vid.0),
            None => format!("n{}", idx.index()),
        };

        // Dependencies: all incoming nodes, deterministically sorted.
        let mut dependencies: Vec<NodeIndex> = dag
            .nodes_to(idx)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        dependencies.sort();

        let plan_node = PlanNode {
            index: idx,
            var,
            rust_type,
            dependencies,
            is_transcript: graph_node.is_transcript(),
            is_challenge: graph_node.is_challenge(),
            is_check: graph_node.is_verifier_check(),
        };
        nodes.push(plan_node);
    }

    // ------------------------------------------------------------------
    // Step 4 – Assemble the plan.
    // ------------------------------------------------------------------
    Ok(CodegenPlan {
        mode: options.mode,
        inputs,
        nodes,
        transcript_order: dag.transcript_nodes(),
        proof_outputs: dag.get_proof_nodes(),
        checks: dag.find_check(),
    })
}
