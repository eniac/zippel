//! Deterministic code generation plan construction from Graph IR DAGs.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use backend::ArkConfig;
use backend::op::Op;
use graph::{ArgKind, Node};
use lang::ast::BinOp;
use lang::typ::{Distribution, Qualifier};
use petgraph::graph::NodeIndex;

use crate::error::{CompilerError, Result};
use crate::options::{CodegenMode, CodegenOptions};
use crate::types;

// ---------------------------------------------------------------------------
// Public data structures (re-exported via compiler::testing when the feature
// gate is active; the *module* itself stays private).
// ---------------------------------------------------------------------------

/// The operation kind for a [`PlanNode`], derived from the Graph IR [`Op`] variant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PlanOpKind {
    /// A random-element sample.
    Random,
    /// A binary arithmetic/logic operation.
    Bin(BinOp),
    /// A random-oracle challenge query.
    Challenge,
    /// A verifier equality check.
    Check,
    /// A transparent reference to another node (Op::Ref — used in verifier Transcr rewrites).
    Ref,
}

/// A single typed input argument in the codegen plan.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub struct PlanArg {
    pub node: NodeIndex,
    /// Original Graph IR argument name.
    pub name: String,
    /// Collision-free Rust binding name reserved for source emission.
    pub rust_name: String,
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
    /// Unique predecessor nodes used for topological readiness/barriers.
    ///
    /// This is deliberately not an ordered operand list. Operation lowering
    /// must preserve operand order and multiplicity separately.
    pub dependencies: Vec<NodeIndex>,
    pub is_transcript: bool,
    pub is_challenge: bool,
    pub is_check: bool,
    /// The kind of operation this node computes.
    pub op_kind: PlanOpKind,
    /// Ordered operand [`NodeIndex`] values from [`Op::references()`].
    pub ordered_operands: Vec<NodeIndex>,
}

/// Deterministic codegen metadata derived from a Graph IR DAG.
///
/// This plan records the stable names, types, coarse dependency barriers,
/// transcript order, proof outputs, and verifier checks that later emission
/// stages build on.
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
/// - Rename bare `_`, which is a Rust wildcard rather than a usable binding.
/// - Suffix Rust keywords with `_`.
#[allow(dead_code)]
fn sanitize_ident(raw: &str) -> String {
    let raw = raw
        .split_once("_NodeIndex(")
        .map_or(raw, |(prefix, _)| prefix);
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
    if out == "_" {
        out = "_zippel".to_string();
    }
    if is_rust_keyword(&out) {
        out.push('_');
    }
    out
}

#[allow(dead_code)]
fn is_rust_keyword(ident: &str) -> bool {
    matches!(
        ident,
        "as" | "async"
            | "await"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "gen"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "Self"
            | "self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "try"
            | "type"
            | "union"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "yield"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "typeof"
            | "unsized"
            | "virtual"
    )
}

#[derive(Default)]
struct NameAllocator {
    used: BTreeSet<String>,
}

impl NameAllocator {
    fn reserve(&mut self, raw: &str) -> String {
        let base = sanitize_ident(raw);
        if self.used.insert(base.clone()) {
            return base;
        }

        let mut suffix = 1usize;
        loop {
            let candidate = format!("{base}_{suffix}");
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
            suffix += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// Plan builder
// ---------------------------------------------------------------------------

fn op_variant_name<C, R>(op: &Op<C, R>) -> &'static str
where
    C: ArkConfig,
{
    match op {
        Op::Value(_) => "Value",
        Op::Ref(_, _) => "Ref",
        Op::Bin(_, _, _, _) => "Bin",
        Op::Ram(_, _) => "Ram",
        Op::Vec(_) => "Vec",
        Op::Record(_) => "Record",
        Op::Random(_, _) => "Random",
        Op::Pair(_, _, _) => "Pair",
        Op::Challenge(_, _) => "Challenge",
        Op::Ifft(_) => "Ifft",
        Op::Interpolate(_, _) => "Interpolate",
        Op::Fft(_) => "Fft",
        Op::Poly(_) => "Poly",
        Op::Mle(_) => "Mle",
        Op::Marginalize(_) => "Marginalize",
        Op::Proj(_, _, _) => "Proj",
        Op::Coef(_) => "Coef",
        Op::Evaluate(_, _) => "Evaluate",
        Op::Check(_) => "Check",
        Op::Reduce(_, _) => "Reduce",
    }
}

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
    // Step 1 - Kahn-style deterministic topological sort.
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
    // Step 2 - Collect input arguments.
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
                    rust_name: String::new(),
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
    inputs.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.node.cmp(&b.node)));

    let mut names = NameAllocator::default();
    for input in &mut inputs {
        input.rust_name = names.reserve(&input.name);
    }

    // ------------------------------------------------------------------
    // Step 3 - Build PlanNodes for non-input nodes.
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

        let (op_kind, ordered_operands) = match graph_node {
            Node::Op(hop, _) | Node::Transcr(hop, _) => {
                let op = &**hop;
                let operands: Vec<NodeIndex> = op.references().iter().map(|r| r.0).collect();
                let kind = match op {
                    Op::Random(_, _) => PlanOpKind::Random,
                    Op::Bin(binop, _, _, _) => PlanOpKind::Bin(*binop),
                    Op::Challenge(_, _) => PlanOpKind::Challenge,
                    Op::Check(_) => PlanOpKind::Check,
                    Op::Ref(_, _) => PlanOpKind::Ref,
                    _ => {
                        return Err(CompilerError::UnsupportedOp {
                            node: idx.index(),
                            op: op_variant_name(op).to_string(),
                        });
                    }
                };
                (kind, operands)
            }
            _ => {
                return Err(CompilerError::UnsupportedNode {
                    node: idx.index(),
                    detail: "typed non-operation node".to_string(),
                });
            }
        };

        // Variable name: prefer DAG vctx, then arg name, else synthesise.
        let raw_var = match dag.find_var(idx) {
            Some(vid) => vid.0.clone(),
            None if matches!(&op_kind, PlanOpKind::Random) => "r".to_string(),
            None if matches!(&op_kind, PlanOpKind::Challenge) => "c".to_string(),
            None => format!("n{}", idx.index()),
        };
        let var = names.reserve(&raw_var);

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
            op_kind,
            ordered_operands,
        };
        nodes.push(plan_node);
    }

    // ------------------------------------------------------------------
    // Step 4 - Assemble the plan.
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::path::PathBuf;

    use backend::ArkBls12_381;
    use share::Ctx;
    use zippel::{ZippelArgs, ZippelHandler};

    use super::{NameAllocator, build_plan};
    use crate::error::CompilerError;
    use crate::options::{CodegenMode, CodegenOptions};

    const SCHNORR_SRC: &str = r#"
proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
    let r = random<F>;
    u <- g*r;
    c <- challenge<F*>;
    z <- r + x*c;
    verify(g*z == u + h*c)
}
"#;

    fn schnorr_handler() -> ZippelHandler<ArkBls12_381> {
        let dir = tempfile::tempdir().expect("tempdir");
        let path: PathBuf = dir.path().join("schnorr.zippel");
        std::fs::write(&path, SCHNORR_SRC).expect("write schnorr.zippel");
        let args = ZippelArgs::new(path);
        let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
        handler.compile(&Ctx::new());
        handler
    }

    fn assert_valid_rust_ident(name: &str) {
        assert!(!name.is_empty(), "identifier must be non-empty");
        assert_ne!(name, "_", "`_` is not a reusable Rust binding");
        let first = name.chars().next().unwrap();
        assert!(
            first == '_' || first.is_ascii_alphabetic(),
            "identifier `{name}` starts with an invalid character `{first}`"
        );
        assert!(
            name.chars().all(|c| c == '_' || c.is_ascii_alphanumeric()),
            "identifier `{name}` contains a non-identifier character"
        );
    }

    #[test]
    fn prover_plan_has_stable_inputs_transcript_and_topological_nodes() {
        let handler = schnorr_handler();
        let dag = handler.prover_graph.as_ref().unwrap();
        let options = CodegenOptions::prover();

        let plan = build_plan(dag, &options).expect("prover plan must build without error");

        assert_eq!(plan.mode, CodegenMode::Prover, "mode must be Prover");

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

        assert!(
            plan.nodes.iter().any(|n| n.is_transcript),
            "prover plan must contain at least one transcript node"
        );
        assert!(
            plan.transcript_order.len() >= 2,
            "transcript order must have >= 2 entries; got {}",
            plan.transcript_order.len()
        );

        let plan_node_indices: BTreeSet<_> = plan.nodes.iter().map(|n| n.index).collect();
        let mut seen: BTreeSet<_> = dag
            .node_indices()
            .filter(|idx| !plan_node_indices.contains(idx))
            .collect();

        for n in &plan.nodes {
            assert_valid_rust_ident(&n.var);
            for &dep in &n.dependencies {
                assert!(
                    seen.contains(&dep),
                    "dependency {:?} of node {:?} ({}) has not been defined yet",
                    dep,
                    n.index,
                    n.var
                );
            }
            seen.insert(n.index);
        }
    }

    #[test]
    fn verifier_plan_finds_check_nodes() {
        let handler = schnorr_handler();
        let dag = handler.verifier_graph.as_ref().unwrap();
        let options = CodegenOptions::verifier();

        let plan = build_plan(dag, &options).expect("verifier plan must build without error");

        assert_eq!(plan.mode, CodegenMode::Verifier, "mode must be Verifier");
        assert_eq!(
            plan.checks.len(),
            1,
            "Schnorr verifier must have exactly one check node; got {}",
            plan.checks.len()
        );

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

    #[test]
    fn plan_names_are_valid_and_unique_rust_idents() {
        let handler = schnorr_handler();
        let dag = handler.prover_graph.as_ref().unwrap();
        let options = CodegenOptions::prover();

        let plan = build_plan(dag, &options).unwrap();

        let mut seen = BTreeSet::new();
        for input in &plan.inputs {
            assert_valid_rust_ident(&input.rust_name);
            assert!(
                seen.insert(input.rust_name.clone()),
                "duplicate input rust name `{}`",
                input.rust_name
            );
        }
        for node in &plan.nodes {
            assert_valid_rust_ident(&node.var);
            assert!(
                seen.insert(node.var.clone()),
                "duplicate plan rust name `{}`",
                node.var
            );
        }
    }

    #[test]
    fn name_allocator_handles_keywords_and_collisions() {
        let mut names = NameAllocator::default();

        assert_eq!(names.reserve("type"), "type_");
        assert_eq!(names.reserve("x'"), "x_");
        assert_eq!(names.reserve("x_"), "x__1");
        assert_eq!(names.reserve("1abc"), "_1abc");
        assert_eq!(names.reserve("_"), "_zippel");
        assert_eq!(names.reserve("n12"), "n12");
        assert_eq!(names.reserve("n12"), "n12_1");
    }

    #[test]
    fn challenge_nodes_are_always_transcript_nodes() {
        let handler = schnorr_handler();
        let dag = handler.prover_graph.as_ref().unwrap();
        let options = CodegenOptions::prover();

        let plan = build_plan(dag, &options).unwrap();

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

    #[test]
    fn unsupported_input_type_propagates_error() {
        use backend::ATyp;
        use graph::{ArgKind, Dag, Node};
        use lang::id::Vid;
        use lang::typ::{Distribution, Nothing, Qualifier};

        let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
        dag.add_node(Node::Arg(
            Vid::new("p"),
            ATyp::Uni(4),
            Qualifier::Public,
            Distribution::Nonuniform,
            ArgKind::Input,
        ));

        let options = CodegenOptions::prover();
        let err = build_plan(&dag, &options)
            .expect_err("build_plan must fail for an unsupported input type");

        assert!(
            matches!(err, CompilerError::UnsupportedType { .. }),
            "expected UnsupportedType, got {err:?}"
        );
    }

    #[test]
    fn unsupported_typed_node_propagates_error() {
        use backend::ATyp;
        use graph::{ArgKind, Dag, Node};
        use lang::id::Vid;
        use lang::typ::{Distribution, Nothing, Qualifier};

        let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
        dag.add_node(Node::Arg(
            Vid::new("p"),
            ATyp::Uni(4),
            Qualifier::Public,
            Distribution::Nonuniform,
            ArgKind::Relation,
        ));

        let options = CodegenOptions::prover();
        let err = build_plan(&dag, &options)
            .expect_err("build_plan must fail for an unsupported typed non-input node");

        assert!(
            matches!(err, CompilerError::UnsupportedType { .. }),
            "expected UnsupportedType, got {err:?}"
        );
    }

    #[test]
    fn unsupported_operation_propagates_error() {
        use backend::Value;
        use backend::op::{Op, mk};
        use graph::{Dag, Node};
        use lang::typ::Nothing;

        let mut dag: Dag<ArkBls12_381, Nothing> = Dag::new();
        let node = dag.add_node(Node::Op(
            mk::<ArkBls12_381>(Op::Value(Value::Bool(true))),
            Nothing,
        ));

        let options = CodegenOptions::prover();
        let err = build_plan(&dag, &options)
            .expect_err("build_plan must fail for an unsupported operation");

        assert!(
            matches!(err, CompilerError::UnsupportedOp { node: n, .. } if n == node.index()),
            "expected UnsupportedOp at node {}, got {err:?}",
            node.index()
        );
    }
}
