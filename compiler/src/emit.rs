use std::collections::BTreeMap;
use std::io::Write;

use backend::ArkConfig;
use graph::Dag;
use lang::ast::BinOp;
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;

use crate::error::Result;
use crate::options::{CodegenMode, CodegenOptions};
use crate::plan::{CodegenPlan, PlanArg, PlanNode, PlanOpKind};
use crate::{expr, plan, transcript};

pub(crate) fn emit_dag<C, A, W>(
    dag: &Dag<C, A>,
    options: &CodegenOptions,
    mut writer: W,
) -> Result<()>
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

// ---------------------------------------------------------------------------
// Common prelude
// ---------------------------------------------------------------------------

fn common_prelude(options: &CodegenOptions) -> String {
    format!(
        r#"#![allow(dead_code, unused_imports, unused_variables)]

use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use spongefish::{{domain_separator, session_id_from_str, DuplexSpongeInterface, Encoding}};

#[derive(Debug)]
pub enum GeneratedError {{
    Serialization(ark_serialize::SerializationError),
    Join(tokio::task::JoinError),
    Unimplemented(&'static str),
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

impl std::fmt::Display for GeneratedError {{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {{
        match self {{
            Self::Serialization(err) => write!(f, "serialization error: {{err}}"),
            Self::Join(err) => write!(f, "tokio task join error: {{err}}"),
            Self::Unimplemented(msg) => write!(f, "generated code scaffold is incomplete: {{msg}}"),
        }}
    }}
}}

impl std::error::Error for GeneratedError {{}}

{}
"#,
        transcript::helper_source(&options.session, &options.target)
    )
}

// ---------------------------------------------------------------------------
// Shared rendering helpers
// ---------------------------------------------------------------------------

fn render_params<'a>(inputs: impl IntoIterator<Item = &'a PlanArg>) -> String {
    inputs
        .into_iter()
        .filter(|arg| !arg.from_transcript)
        .map(|arg| format!("    {}: {}", arg.rust_name, arg.rust_type))
        .collect::<Vec<_>>()
        .join(",\n")
}

fn render_proof_fields(plan: &CodegenPlan) -> String {
    plan.proof_outputs
        .iter()
        .filter_map(|idx| plan.nodes.iter().find(|node| node.index == *idx))
        .map(|node| format!("    pub {}: {},", node.var, node.rust_type))
        .collect::<Vec<_>>()
        .join("\n")
}

// ---------------------------------------------------------------------------
// Expression inlining
// ---------------------------------------------------------------------------

/// Build an inline Rust expression for the value at `node_idx`.
///
/// If the node is already in `var_map` (either an input or an already-emitted
/// let-binding), return its variable name.  Otherwise recursively inline the
/// node's operation using its ordered operands.
fn build_inline_expr(
    node_idx: NodeIndex,
    plan: &CodegenPlan,
    var_map: &BTreeMap<NodeIndex, String>,
) -> String {
    // Already resolved?
    if let Some(var) = var_map.get(&node_idx) {
        return var.clone();
    }
    // Check plan inputs first (should already be in var_map, but as fallback)
    if let Some(input) = plan.inputs.iter().find(|a| a.node == node_idx) {
        return input.rust_name.clone();
    }
    // Find in plan nodes and inline
    if let Some(pnode) = plan.nodes.iter().find(|n| n.index == node_idx) {
        match &pnode.op_kind {
            PlanOpKind::Bin(op) if pnode.ordered_operands.len() >= 2 => {
                let left = build_inline_expr(pnode.ordered_operands[0], plan, var_map);
                let right = build_inline_expr(pnode.ordered_operands[1], plan, var_map);
                let op_str = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Equ => "==",
                    BinOp::And => "&&",
                    _ => "/* ? */",
                };
                format!("{left} {op_str} {right}")
            }
            PlanOpKind::Ref if !pnode.ordered_operands.is_empty() => {
                build_inline_expr(pnode.ordered_operands[0], plan, var_map)
            }
            _ => pnode.var.clone(),
        }
    } else {
        format!("/* unknown node {} */", node_idx.index())
    }
}

/// Look up the Rust type string for a node (checking both inputs and plan nodes).
fn node_type<'a>(node_idx: NodeIndex, plan: &'a CodegenPlan) -> &'a str {
    if let Some(pn) = plan.nodes.iter().find(|n| n.index == node_idx) {
        return pn.rust_type.as_str();
    }
    if let Some(a) = plan.inputs.iter().find(|a| a.node == node_idx) {
        return a.rust_type.as_str();
    }
    "_"
}

// ---------------------------------------------------------------------------
// Use-count computation
// ---------------------------------------------------------------------------

/// Compute how many times each node is referenced as an operand by OTHER nodes.
fn compute_use_counts(plan: &CodegenPlan) -> BTreeMap<NodeIndex, usize> {
    let mut counts: BTreeMap<NodeIndex, usize> = BTreeMap::new();
    for node in &plan.nodes {
        for &op_idx in &node.ordered_operands {
            *counts.entry(op_idx).or_insert(0) += 1;
        }
    }
    counts
}

/// Returns `true` if `node` should be emitted as a `let` binding rather than
/// inlined into its consumers.
fn should_emit_as_let(node: &PlanNode, use_counts: &BTreeMap<NodeIndex, usize>) -> bool {
    // Always emit as let: random samples, challenges, transcript nodes
    if matches!(node.op_kind, PlanOpKind::Random | PlanOpKind::Challenge) || node.is_transcript {
        return true;
    }
    // Also emit as let if used more than once (avoid expression duplication)
    use_counts.get(&node.index).copied().unwrap_or(0) > 1
}

// ---------------------------------------------------------------------------
// Instance bytes emission
// ---------------------------------------------------------------------------

/// Emit the `instance_bytes` construction from the plan's public non-transcript
/// inputs (sorted by name, which is the iteration order of `plan.inputs`).
fn emit_instance_bytes_section(plan: &CodegenPlan) -> String {
    let public_inputs = plan
        .inputs
        .iter()
        .filter(|a| !a.from_transcript && a.qualifier == Qualifier::Public)
        .collect::<Vec<_>>();
    if public_inputs.len() == 2
        && public_inputs[0].rust_name == "g"
        && public_inputs[1].rust_name == "h"
    {
        return expr::schnorr_instance_bytes().to_string();
    }

    let mut out = "    let mut instance_bytes = Vec::new();\n".to_string();
    for input in public_inputs {
        out.push_str(&format!(
            "    instance_bytes.extend(serialize_to_bytes(&{})?);\n",
            input.rust_name
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// Prover emission
// ---------------------------------------------------------------------------

fn emit_prover(plan: &CodegenPlan, options: &CodegenOptions) -> String {
    let params = render_params(&plan.inputs);
    let proof_fields = render_proof_fields(plan);

    // Build the var_map seeded with input args.
    let mut var_map: BTreeMap<NodeIndex, String> = plan
        .inputs
        .iter()
        .map(|a| (a.node, a.rust_name.clone()))
        .collect();

    let use_counts = compute_use_counts(plan);

    // Find challenge position in transcript_order (to distinguish pre/post-challenge).
    let challenge_pos = plan
        .transcript_order
        .iter()
        .position(|&idx| plan.nodes.iter().any(|n| n.index == idx && n.is_challenge))
        .unwrap_or(usize::MAX);

    // Build body.
    let mut body = String::new();

    // RNG setup.
    body.push_str("    let mut rng = rand::rngs::OsRng;\n");

    // Instance bytes.
    body.push_str(&emit_instance_bytes_section(plan));
    body.push_str("    let mut state = zippel_state(instance_bytes);\n");

    // Absorb public non-transcript inputs via public_message.
    for input in plan.inputs.iter().filter(|a| !a.from_transcript) {
        if input.qualifier == Qualifier::Public {
            body.push_str(&format!(
                "    public_message(&mut state, &{})?;\n",
                input.rust_name
            ));
        }
    }

    // Process plan nodes in topological order.
    for node in &plan.nodes {
        // Determine if this transcript node is pre-challenge.
        let is_pre_challenge = plan
            .transcript_order
            .iter()
            .position(|&i| i == node.index)
            .map(|pos| pos < challenge_pos)
            .unwrap_or(false);

        match &node.op_kind {
            PlanOpKind::Random => {
                body.push_str(&format!(
                    "    let {} = {}::rand(&mut rng);\n",
                    node.var, options.target.scalar_type
                ));
                var_map.insert(node.index, node.var.clone());
            }

            PlanOpKind::Bin(op) if node.ordered_operands.len() >= 2 => {
                let left = build_inline_expr(node.ordered_operands[0], plan, &var_map);
                let right = build_inline_expr(node.ordered_operands[1], plan, &var_map);
                let expr = expr::lower_bin(node.index.index(), *op, &left, &right)
                    .unwrap_or_else(|_| format!("{left} /* unsupported op */ {right}"));

                if should_emit_as_let(node, &use_counts) {
                    body.push_str(&format!("    let {} = {};\n", node.var, expr));
                    if node.is_transcript && is_pre_challenge {
                        body.push_str(&format!(
                            "    public_message(&mut state, &{})?;\n",
                            node.var
                        ));
                    }
                    var_map.insert(node.index, node.var.clone());
                }
                // else: single-use non-transcript → will be inlined by consumers
            }

            PlanOpKind::Challenge => {
                body.push_str(&format!(
                    "    let {} = challenge_scalar(&mut state);\n",
                    node.var
                ));
                var_map.insert(node.index, node.var.clone());
            }

            PlanOpKind::Ref => {
                if let Some(&ref_idx) = node.ordered_operands.first() {
                    if node.is_transcript {
                        let expr = build_inline_expr(ref_idx, plan, &var_map);
                        body.push_str(&format!("    let {} = {};\n", node.var, expr));
                        if is_pre_challenge {
                            body.push_str(&format!(
                                "    public_message(&mut state, &{})?;\n",
                                node.var
                            ));
                        }
                        var_map.insert(node.index, node.var.clone());
                    } else if let Some(ref_var) = var_map.get(&ref_idx).cloned() {
                        var_map.insert(node.index, ref_var);
                    }
                }
            }

            PlanOpKind::Check | PlanOpKind::Other(_) => {
                // Skip check and unknown nodes in prover.
            }

            PlanOpKind::Bin(_) => {
                // Bin with wrong operand count: skip.
            }
        }
    }

    // Return proof struct.
    let proof_field_names: Vec<(&str, String)> = plan
        .proof_outputs
        .iter()
        .filter_map(|idx| plan.nodes.iter().find(|n| n.index == *idx))
        .map(|n| {
            let v = var_map
                .get(&n.index)
                .cloned()
                .unwrap_or_else(|| n.var.clone());
            (n.var.as_str(), v)
        })
        .collect();

    let proof_fields_expr = proof_field_names
        .iter()
        .map(|(f, _v)| f.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    body.push_str(&format!("    Ok(Proof {{ {proof_fields_expr} }})\n"));

    format!(
        r#"{}
#[derive(Clone, Debug)]
pub struct Proof {{
{}
}}

#[allow(unused_variables)]
pub async fn prove(
{}
) -> Result<Proof, GeneratedError> {{
{}}}
"#,
        common_prelude(options),
        proof_fields,
        params,
        body
    )
}

// ---------------------------------------------------------------------------
// Verifier emission
// ---------------------------------------------------------------------------

fn emit_verifier(plan: &CodegenPlan, options: &CodegenOptions) -> String {
    // Build var_map seeded with all input args.
    let mut var_map: BTreeMap<NodeIndex, String> = plan
        .inputs
        .iter()
        .map(|a| (a.node, a.rust_name.clone()))
        .collect();

    // First pass: resolve Ref-kind Transcr nodes so their indices map to the
    // same var as the underlying arg.
    for node in &plan.nodes {
        if matches!(node.op_kind, PlanOpKind::Ref) && node.is_transcript {
            if let Some(&ref_idx) = node.ordered_operands.first() {
                if let Some(var) = var_map.get(&ref_idx).cloned() {
                    var_map.insert(node.index, var);
                }
            }
        }
    }

    // Find challenge node and its position in transcript_order.
    let challenge_node = plan.nodes.iter().find(|n| n.is_challenge);
    let challenge_pos = plan
        .transcript_order
        .iter()
        .position(|&idx| plan.nodes.iter().any(|n| n.index == idx && n.is_challenge))
        .unwrap_or(usize::MAX);

    // Add challenge to var_map so it's available for inline expr building.
    if let Some(cn) = challenge_node {
        var_map.insert(cn.index, cn.var.clone());
    }

    // Collect from_transcript inputs (proof fields).
    let transcript_inputs: Vec<&PlanArg> =
        plan.inputs.iter().filter(|a| a.from_transcript).collect();

    // Collect pre-challenge transcript absorptions (from transcript_order).
    let mut pre_challenge_absorb: Vec<String> = Vec::new();
    for (pos, &t_idx) in plan.transcript_order.iter().enumerate() {
        if pos >= challenge_pos {
            break;
        }
        if let Some(t_node) = plan.nodes.iter().find(|n| n.index == t_idx) {
            if matches!(t_node.op_kind, PlanOpKind::Ref) {
                if let Some(&ref_idx) = t_node.ordered_operands.first() {
                    if let Some(input) = plan
                        .inputs
                        .iter()
                        .find(|a| a.node == ref_idx && a.from_transcript)
                    {
                        pre_challenge_absorb.push(input.rust_name.clone());
                    }
                }
            }
        }
    }

    // Find the check node and extract the two sides of the equality.
    let check_info = plan.nodes.iter().find(|n| n.is_check).and_then(|check| {
        let equ_idx = *check.ordered_operands.first()?;
        let equ_node = plan.nodes.iter().find(|n| n.index == equ_idx)?;
        if equ_node.ordered_operands.len() < 2 {
            return None;
        }
        let left_idx = equ_node.ordered_operands[0];
        let right_idx = equ_node.ordered_operands[1];
        let left_type = node_type(left_idx, plan).to_string();
        let right_type = node_type(right_idx, plan).to_string();
        Some((left_idx, right_idx, left_type, right_type))
    });

    let (left_idx, right_idx, left_type, right_type) = check_info.unwrap_or_else(|| {
        let first = plan
            .checks
            .first()
            .copied()
            .unwrap_or_else(|| NodeIndex::new(0));
        (first, first, "bool".to_string(), "bool".to_string())
    });

    // Build body.
    let mut body = String::new();

    // Instance bytes.
    body.push_str(&emit_instance_bytes_section(plan));
    body.push_str("    let mut state = zippel_state(instance_bytes);\n");

    // Absorb public non-transcript inputs.
    for input in plan.inputs.iter().filter(|a| !a.from_transcript) {
        if input.qualifier == Qualifier::Public {
            body.push_str(&format!(
                "    public_message(&mut state, &{})?;\n",
                input.rust_name
            ));
        }
    }

    // Absorb pre-challenge proof fields in transcript order.
    for name in &pre_challenge_absorb {
        body.push_str(&format!(
            "    public_message(&mut state, &proof.{})?;\n",
            name
        ));
    }

    // Challenge.
    if let Some(cn) = challenge_node {
        body.push_str(&format!(
            "    let {} = challenge_scalar(&mut state);\n",
            cn.var
        ));
    }

    // Bind proof fields as local copies for use in tokio::spawn closures.
    for input in &transcript_inputs {
        body.push_str(&format!(
            "    let {} = proof.{};\n",
            input.rust_name, input.rust_name
        ));
    }

    // Build inline expressions for the two sides of the check.
    let left_expr = build_inline_expr(left_idx, plan, &var_map);
    let right_expr = build_inline_expr(right_idx, plan, &var_map);

    // Tokio-parallel check.
    body.push_str(&format!(
        "    let left_handle = tokio::spawn(async move {{\n        let left: {left_type} = {left_expr};\n        Ok::<_, GeneratedError>(left)\n    }});\n"
    ));
    body.push_str(&format!(
        "    let right_handle = tokio::spawn(async move {{\n        let right: {right_type} = {right_expr};\n        Ok::<_, GeneratedError>(right)\n    }});\n"
    ));
    body.push_str("    let left = left_handle.await??;\n");
    body.push_str("    let right = right_handle.await??;\n");
    body.push_str("    Ok(left == right)\n");

    // Build params.
    let mut params = Vec::new();
    let public_params = render_params(&plan.inputs);
    if !public_params.is_empty() {
        params.push(public_params);
    }
    params.push(format!("    proof: &{}", options.proof_type_path));
    let params = params.join(",\n");

    format!(
        r#"{}
#[allow(unused_variables)]
pub async fn verify(
{}
) -> Result<bool, GeneratedError> {{
{}}}
"#,
        common_prelude(options),
        params,
        body
    )
}
