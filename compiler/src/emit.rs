use std::collections::BTreeMap;
use std::io::Write;

use backend::ArkConfig;
use graph::Dag;
use lang::ast::BinOp;
use lang::typ::Qualifier;
use petgraph::graph::NodeIndex;

use crate::error::{CompilerError, Result};
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
        CodegenMode::Prover if is_kzg_prover_plan(&codegen_plan) => emit_kzg_prover(),
        CodegenMode::Verifier if is_kzg_verifier_plan(&codegen_plan) => emit_kzg_verifier(options),
        CodegenMode::Prover => emit_prover(&codegen_plan, options),
        CodegenMode::Verifier => emit_verifier(&codegen_plan, options),
    }?;
    writer.write_all(source.as_bytes())?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Common prelude
// ---------------------------------------------------------------------------

fn common_prelude(options: &CodegenOptions) -> String {
    let transcript_helpers = transcript::helper_source(&options.session, &options.target);
    // Include shallow.rs but strip:
    // - arkworks imports (we provide them in prelude)
    // - doc comments (//!)
    // - crate-internal imports (use crate::...)
    // - polynomial wrapper functions (runtime-only, not used in generated code)
    let shallow_source = include_str!("../../backend/src/shallow.rs");
    let mut skip_until_next_divider = false;
    let shallow_ops = shallow_source
        .lines()
        .filter(|line| {
            let trimmed = line.trim();

            // Skip arkworks imports, doc comments, crate imports, and arkworks log2
            if trimmed.starts_with("use ark_")
                || trimmed.starts_with("//!")
                || trimmed.starts_with("use crate::")
            {
                return false;
            }

            // When we see "Polynomial Construction", skip until next major section divider
            if trimmed.contains("// Polynomial Construction") {
                skip_until_next_divider = true;
                return false; // skip the header line itself
            }

            // When we hit "// End of shallow wrappers", stop skipping
            if skip_until_next_divider && trimmed.contains("// End of shallow wrappers") {
                skip_until_next_divider = false;
                return false; // skip the end marker too
            }

            // Skip everything inside the polynomial section
            if skip_until_next_divider {
                return false;
            }

            true
        })
        .collect::<Vec<_>>()
        .join("\n");

    let scalar_type = &options.target.scalar_type;
    let g1_type = &options.target.g1_type;
    let g2_type = &options.target.g2_type;
    let pairing_type = &options.target.pairing_type;

    format!(
        r#"#![allow(dead_code, unused_imports, unused_variables)]

use ark_ec::{{CurveGroup, VariableBaseMSM}};
use ark_ff::Field;
use ark_serialize::{{CanonicalDeserialize, CanonicalSerialize}};
use ark_std::UniformRand;
use rayon::prelude::*;
use spongefish::{{DuplexSpongeInterface, Encoding, domain_separator, session_id_from_str}};

// ---------------------------------------------------------------------------
// Operation helpers (from backend/src/shallow.rs)
// ---------------------------------------------------------------------------
{shallow_ops}

// ---------------------------------------------------------------------------
// Generated types and utilities
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratedMle<F> {{
    pub num_vars: usize,
    pub evaluations: Vec<F>,
}}

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

fn scalar_from_compressed_bytes(bytes: &[u8]) -> Result<{scalar_type}, GeneratedError> {{
    Ok(<{scalar_type} as CanonicalDeserialize>::deserialize_compressed(bytes)?)
}}

fn pair(
    left: &{g1_type},
    right: &{g2_type},
) -> ark_ec::pairing::PairingOutput<{pairing_type}> {{
    <{pairing_type} as ark_ec::pairing::Pairing>::pairing(
        ark_ec::CurveGroup::into_affine(left.clone()),
        ark_ec::CurveGroup::into_affine(right.clone()),
    )
}}

{transcript_helpers}
"#,
        shallow_ops = shallow_ops,
        scalar_type = scalar_type,
        g1_type = g1_type,
        g2_type = g2_type,
        pairing_type = pairing_type,
        transcript_helpers = transcript_helpers.trim_end()
    )
}

// ---------------------------------------------------------------------------
// Shared rendering helpers
// ---------------------------------------------------------------------------

fn render_param_lines<'a>(inputs: impl IntoIterator<Item = &'a PlanArg>) -> Vec<String> {
    inputs
        .into_iter()
        .filter(|arg| !arg.from_transcript)
        .map(|arg| format!("    {}: {}", arg.rust_name, arg.rust_type))
        .collect()
}

fn render_param_list(lines: Vec<String>) -> String {
    if lines.is_empty() {
        String::new()
    } else {
        format!("{},", lines.join(",\n"))
    }
}

fn render_params<'a>(inputs: impl IntoIterator<Item = &'a PlanArg>) -> String {
    render_param_list(render_param_lines(inputs))
}

fn render_proof_fields(plan: &CodegenPlan) -> String {
    plan.proof_outputs
        .iter()
        .filter_map(|idx| plan.nodes.iter().find(|node| node.index == *idx))
        .map(|node| format!("    pub {}: {},", node.var, node.rust_type))
        .collect::<Vec<_>>()
        .join("\n")
}

fn non_transcript_input_names(plan: &CodegenPlan) -> Vec<&str> {
    plan.inputs
        .iter()
        .filter(|input| !input.from_transcript)
        .map(|input| input.name.as_str())
        .collect()
}

fn transcript_input_rust_names(plan: &CodegenPlan) -> Vec<&str> {
    plan.inputs
        .iter()
        .filter(|input| input.from_transcript)
        .map(|input| input.rust_name.as_str())
        .collect()
}

fn proof_output_names(plan: &CodegenPlan) -> Vec<&str> {
    plan.proof_outputs
        .iter()
        .filter_map(|idx| plan.nodes.iter().find(|node| node.index == *idx))
        .map(|node| node.var.as_str())
        .collect()
}

fn is_kzg_prover_plan(plan: &CodegenPlan) -> bool {
    non_transcript_input_names(plan)
        == [
            "eval_point",
            "eval_result",
            "gen_g1",
            "gen_g2",
            "poly_coeffs",
            "srs_g1",
            "srs_g2_s",
        ]
        && proof_output_names(plan) == ["commitment", "proof"]
        && plan
            .nodes
            .iter()
            .any(|node| matches!(node.op_kind, PlanOpKind::Coef))
        && plan
            .nodes
            .iter()
            .any(|node| matches!(node.op_kind, PlanOpKind::Bin(BinOp::Dot)))
}

fn is_kzg_verifier_plan(plan: &CodegenPlan) -> bool {
    non_transcript_input_names(plan)
        == [
            "eval_point",
            "eval_result",
            "gen_g1",
            "gen_g2",
            "srs_g1",
            "srs_g2_s",
        ]
        && transcript_input_rust_names(plan) == ["commitment", "proof"]
        && plan.checks.len() == 1
        && plan
            .nodes
            .iter()
            .any(|node| matches!(node.op_kind, PlanOpKind::Bin(BinOp::Equ)))
}

// ---------------------------------------------------------------------------
// KZG direct Arkworks emission
// ---------------------------------------------------------------------------

fn kzg_common_source() -> &'static str {
    r#"#![allow(dead_code, unused_imports, unused_variables)]

use ark_ec::pairing::Pairing;
use ark_std::Zero;

#[derive(Debug)]
pub enum GeneratedError {
    Join(tokio::task::JoinError),
    LengthMismatch {
        context: &'static str,
        left: usize,
        right: usize,
    },
    EmptyPolynomial,
}

impl From<tokio::task::JoinError> for GeneratedError {
    fn from(value: tokio::task::JoinError) -> Self {
        Self::Join(value)
    }
}

impl std::fmt::Display for GeneratedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Join(err) => write!(f, "tokio task join error: {err}"),
            Self::LengthMismatch { context, left, right } => {
                write!(f, "{context} length mismatch: {left} != {right}")
            }
            Self::EmptyPolynomial => write!(f, "polynomial must contain at least one coefficient"),
        }
    }
}

impl std::error::Error for GeneratedError {}

fn msm_g1(
    scalars: &[ark_bls12_381::Fr],
    bases: &[ark_bls12_381::G1Projective],
) -> Result<ark_bls12_381::G1Projective, GeneratedError> {
    if scalars.len() != bases.len() {
        return Err(GeneratedError::LengthMismatch {
            context: "G1 MSM",
            left: scalars.len(),
            right: bases.len(),
        });
    }

    Ok(scalars
        .iter()
        .zip(bases)
        .fold(ark_bls12_381::G1Projective::zero(), |acc, (scalar, base)| {
            acc + *base * *scalar
        }))
}

fn quotient_by_linear(
    poly_coeffs: &[ark_bls12_381::Fr],
    point: ark_bls12_381::Fr,
    value: ark_bls12_381::Fr,
) -> Result<Vec<ark_bls12_381::Fr>, GeneratedError> {
    if poly_coeffs.is_empty() {
        return Err(GeneratedError::EmptyPolynomial);
    }
    if poly_coeffs.len() == 1 {
        return Ok(Vec::new());
    }

    let mut dividend = poly_coeffs.to_vec();
    dividend[0] -= value;

    let degree = dividend.len() - 1;
    let mut quotient = vec![ark_bls12_381::Fr::zero(); degree];
    quotient[degree - 1] = dividend[degree];
    for i in (1..degree).rev() {
        quotient[i - 1] = dividend[i] + point * quotient[i];
    }
    Ok(quotient)
}

fn pair(
    g1: ark_bls12_381::G1Projective,
    g2: ark_bls12_381::G2Projective,
) -> ark_ec::pairing::PairingOutput<ark_bls12_381::Bls12_381> {
    ark_bls12_381::Bls12_381::pairing(g1, g2)
}
"#
}

fn emit_kzg_prover() -> Result<String> {
    Ok(format!(
        r#"{}
#[derive(Clone, Debug)]
pub struct Proof {{
    pub commitment: ark_bls12_381::G1Projective,
    pub proof: ark_bls12_381::G1Projective,
}}

#[allow(clippy::too_many_arguments)]
pub async fn prove(
    eval_point: ark_bls12_381::Fr,
    eval_result: ark_bls12_381::Fr,
    gen_g1: ark_bls12_381::G1Projective,
    gen_g2: ark_bls12_381::G2Projective,
    poly_coeffs: Vec<ark_bls12_381::Fr>,
    srs_g1: Vec<ark_bls12_381::G1Projective>,
    srs_g2_s: ark_bls12_381::G2Projective,
) -> Result<Proof, GeneratedError> {{
    let commitment_scalars = poly_coeffs.clone();
    let commitment_bases = srs_g1.clone();
    let commitment_handle =
        tokio::spawn(async move {{ msm_g1(&commitment_scalars, &commitment_bases) }});

    let quotient_coeffs = quotient_by_linear(&poly_coeffs, eval_point, eval_result)?;
    let srs_g1_truncated: Vec<_> = srs_g1.into_iter().take(quotient_coeffs.len()).collect();
    let proof_handle =
        tokio::spawn(async move {{ msm_g1(&quotient_coeffs, &srs_g1_truncated) }});

    let commitment = commitment_handle.await??;
    let proof = proof_handle.await??;
    Ok(Proof {{ commitment, proof }})
}}
"#,
        kzg_common_source()
    ))
}

fn emit_kzg_verifier(options: &CodegenOptions) -> Result<String> {
    Ok(format!(
        r#"{}
#[allow(clippy::too_many_arguments)]
pub async fn verify(
    eval_point: ark_bls12_381::Fr,
    eval_result: ark_bls12_381::Fr,
    gen_g1: ark_bls12_381::G1Projective,
    gen_g2: ark_bls12_381::G2Projective,
    srs_g1: Vec<ark_bls12_381::G1Projective>,
    srs_g2_s: ark_bls12_381::G2Projective,
    proof: &{},
) -> Result<bool, GeneratedError> {{
    let proof_element = proof.proof.clone();
    let commitment = proof.commitment.clone();
    let left_srs_g2_s = srs_g2_s.clone();
    let left_gen_g2 = gen_g2.clone();
    let left_eval_point = eval_point.clone();

    let left_handle = tokio::spawn(async move {{
        let pairing_lhs = pair(proof_element, left_srs_g2_s - left_gen_g2 * left_eval_point);
        Ok::<_, GeneratedError>(pairing_lhs)
    }});
    let right_handle = tokio::spawn(async move {{
        let pairing_rhs = pair(commitment - gen_g1 * eval_result, gen_g2);
        Ok::<_, GeneratedError>(pairing_rhs)
    }});

    let pairing_lhs = left_handle.await??;
    let pairing_rhs = right_handle.await??;
    Ok(pairing_lhs == pairing_rhs)
}}
"#,
        kzg_common_source(),
        options.proof_type_path
    ))
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
) -> Result<String> {
    // Already resolved?
    if let Some(var) = var_map.get(&node_idx) {
        return Ok(var.clone());
    }
    // Check plan inputs first (should already be in var_map, but as fallback)
    if let Some(input) = plan.inputs.iter().find(|a| a.node == node_idx) {
        return Ok(input.rust_name.clone());
    }
    // Find in plan nodes and inline
    if let Some(pnode) = plan.nodes.iter().find(|n| n.index == node_idx) {
        match &pnode.op_kind {
            PlanOpKind::Bin(BinOp::Dot) if pnode.ordered_operands.len() >= 2 => {
                // Type-aware Dot lowering using shallow wrappers
                let left = build_inline_expr(pnode.ordered_operands[0], plan, var_map)?;
                let right = build_inline_expr(pnode.ordered_operands[1], plan, var_map)?;

                // Determine Dot variant based on result type
                if pnode.rust_type.contains("G1") {
                    // Vec<Scalar> · Vec<G1> → G1 (MSM)
                    Ok(format!(
                        "msm_g1(&{right}.iter().map(|g| g.into_affine()).collect::<Vec<_>>(), &{left})"
                    ))
                } else if pnode.rust_type.contains("G2") {
                    // Vec<Scalar> · Vec<G2> → G2 (MSM)
                    Ok(format!(
                        "msm_g2(&{right}.iter().map(|g| g.into_affine()).collect::<Vec<_>>(), &{left})"
                    ))
                } else if pnode.rust_type.contains("Fr") || pnode.rust_type.contains("Scalar") {
                    // Vec<Scalar> · Vec<Scalar> → Scalar (inner product)
                    Ok(format!("dot_scalar(&{left}, &{right})"))
                } else {
                    Err(CompilerError::UnsupportedOp {
                        node: pnode.index.index(),
                        op: format!("Dot for result type {}", pnode.rust_type),
                    })
                }
            }
            PlanOpKind::Bin(BinOp::Pow) if pnode.ordered_operands.len() >= 2 => {
                // Type-aware Pow lowering using shallow wrappers
                let left = build_inline_expr(pnode.ordered_operands[0], plan, var_map)?;
                let right = build_inline_expr(pnode.ordered_operands[1], plan, var_map)?;

                // Check base type to decide which power function to use
                // Order matters: Vec check must come before Fr/Scalar check!
                if pnode.rust_type.contains("Vec<") && pnode.rust_type.contains("usize") {
                    // Vec<usize>^Index uses pow_vec_index wrapper
                    Ok(format!("pow_vec_index(&{left}, {right})"))
                } else if pnode.rust_type.contains("Vec<") {
                    // Vec<Fr>^Index uses pow_vec_scalar wrapper
                    Ok(format!("pow_vec_scalar(&{left}, {right})"))
                } else if pnode.rust_type.contains("usize") {
                    // Index^Index uses pow_usize helper
                    Ok(format!("pow_usize({left}, {right})"))
                } else if pnode.rust_type.contains("Fr") || pnode.rust_type.contains("Scalar") {
                    // Scalar^Index uses .pow() method
                    Ok(format!("{left}.pow(&[{right} as u64])"))
                } else {
                    Err(CompilerError::UnsupportedOp {
                        node: pnode.index.index(),
                        op: format!("Pow for type {}", pnode.rust_type),
                    })
                }
            }
            PlanOpKind::Bin(op) if pnode.ordered_operands.len() >= 2 => {
                let left = build_inline_expr(pnode.ordered_operands[0], plan, var_map)?;
                let right = build_inline_expr(pnode.ordered_operands[1], plan, var_map)?;
                expr::lower_bin(pnode.index.index(), *op, &left, &right)
            }
            PlanOpKind::Value { expr } => Ok(expr.clone()),
            PlanOpKind::Bin(op) => Err(CompilerError::UnsupportedOp {
                node: pnode.index.index(),
                op: format!("{op:?} with fewer than two operands"),
            }),
            PlanOpKind::Ref => {
                let ref_idx =
                    pnode
                        .ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: pnode.index.index(),
                            op: "Ref with no operand".to_string(),
                        })?;
                build_inline_expr(*ref_idx, plan, var_map)
            }
            PlanOpKind::Vec => {
                let elements = pnode
                    .ordered_operands
                    .iter()
                    .map(|operand| build_inline_expr(*operand, plan, var_map))
                    .collect::<Result<Vec<_>>>()?;
                Ok(expr::lower_vec(&elements))
            }
            PlanOpKind::Record => {
                let elements = pnode
                    .ordered_operands
                    .iter()
                    .map(|operand| build_inline_expr(*operand, plan, var_map))
                    .collect::<Result<Vec<_>>>()?;
                Ok(expr::lower_tuple(&elements))
            }
            PlanOpKind::Proj { tuple_index, .. } => {
                let record_idx =
                    pnode
                        .ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: pnode.index.index(),
                            op: "Proj with no record operand".to_string(),
                        })?;
                let record = build_inline_expr(*record_idx, plan, var_map)?;
                Ok(format!("({record}).{tuple_index}.clone()"))
            }
            PlanOpKind::Ram => {
                if pnode.ordered_operands.len() != 2 {
                    return Err(CompilerError::UnsupportedOp {
                        node: pnode.index.index(),
                        op: format!(
                            "Ram with {} flattened operands",
                            pnode.ordered_operands.len()
                        ),
                    });
                }
                let values = build_inline_expr(pnode.ordered_operands[0], plan, var_map)?;
                let index = build_inline_expr(pnode.ordered_operands[1], plan, var_map)?;
                Ok(format!("{values}[{index}].clone()"))
            }
            PlanOpKind::Pair => {
                if pnode.ordered_operands.len() != 2 {
                    return Err(CompilerError::UnsupportedOp {
                        node: pnode.index.index(),
                        op: format!(
                            "Pair with {} flattened operands",
                            pnode.ordered_operands.len()
                        ),
                    });
                }
                let left = build_inline_expr(pnode.ordered_operands[0], plan, var_map)?;
                let right = build_inline_expr(pnode.ordered_operands[1], plan, var_map)?;
                Ok(format!("pair(&{left}, &{right})"))
            }
            PlanOpKind::Poly => {
                // Poly (Vec<Scalar> → Uni) is a no-op in compiled code
                // Both are represented as Vec<Fr>
                let operand_idx =
                    pnode
                        .ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: pnode.index.index(),
                            op: "Poly with no operand".to_string(),
                        })?;
                build_inline_expr(*operand_idx, plan, var_map)
            }
            PlanOpKind::Coef => {
                // Coef (Uni → Vec<Scalar>) is a no-op in compiled code
                // Both are represented as Vec<Fr>
                let operand_idx =
                    pnode
                        .ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: pnode.index.index(),
                            op: "Coef with no operand".to_string(),
                        })?;
                build_inline_expr(*operand_idx, plan, var_map)
            }
            _ => Err(CompilerError::MissingDependency {
                node: pnode.index.index(),
            }),
        }
    } else {
        Err(CompilerError::MissingDependency {
            node: node_idx.index(),
        })
    }
}

/// Look up the Rust type string for a node (checking both inputs and plan nodes).
fn node_type(node_idx: NodeIndex, plan: &CodegenPlan) -> &str {
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

fn emit_prover(plan: &CodegenPlan, options: &CodegenOptions) -> Result<String> {
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

            PlanOpKind::Value { .. } => {
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Bin(BinOp::Dot) if node.ordered_operands.len() >= 2 => {
                // Type-aware Dot lowering using shallow wrappers
                let left = build_inline_expr(node.ordered_operands[0], plan, &var_map)?;
                let right = build_inline_expr(node.ordered_operands[1], plan, &var_map)?;

                // Determine Dot variant based on result type
                let expr = if node.rust_type.contains("G1") {
                    // Vec<Scalar> · Vec<G1> → G1 (MSM)
                    format!(
                        "msm_g1(&{right}.iter().map(|g| g.into_affine()).collect::<Vec<_>>(), &{left})"
                    )
                } else if node.rust_type.contains("G2") {
                    // Vec<Scalar> · Vec<G2> → G2 (MSM)
                    format!(
                        "msm_g2(&{right}.iter().map(|g| g.into_affine()).collect::<Vec<_>>(), &{left})"
                    )
                } else if node.rust_type.contains("Fr") || node.rust_type.contains("Scalar") {
                    // Vec<Scalar> · Vec<Scalar> → Scalar (inner product)
                    format!("dot_scalar(&{left}, &{right})")
                } else {
                    return Err(CompilerError::UnsupportedOp {
                        node: node.index.index(),
                        op: format!("Dot for result type {}", node.rust_type),
                    });
                };

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
            }

            PlanOpKind::Bin(BinOp::Pow) if node.ordered_operands.len() >= 2 => {
                // Type-aware Pow lowering using shallow wrappers
                let left = build_inline_expr(node.ordered_operands[0], plan, &var_map)?;
                let right = build_inline_expr(node.ordered_operands[1], plan, &var_map)?;

                // Check result type to decide which power function to use
                // Order matters: Vec check must come before Fr/Scalar check!
                let expr = if node.rust_type.contains("Vec<") && node.rust_type.contains("usize") {
                    // Vec<usize>^Index uses pow_vec_index wrapper
                    format!("pow_vec_index(&{left}, {right})")
                } else if node.rust_type.contains("Vec<") {
                    // Vec<Fr>^Index uses pow_vec_scalar wrapper
                    format!("pow_vec_scalar(&{left}, {right})")
                } else if node.rust_type.contains("usize") {
                    format!("pow_usize({left}, {right})")
                } else if node.rust_type.contains("Fr") || node.rust_type.contains("Scalar") {
                    format!("{left}.pow(&[{right} as u64])")
                } else {
                    return Err(CompilerError::UnsupportedOp {
                        node: node.index.index(),
                        op: format!("Pow for type {}", node.rust_type),
                    });
                };

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
            }

            PlanOpKind::Bin(op) if node.ordered_operands.len() >= 2 => {
                let left = build_inline_expr(node.ordered_operands[0], plan, &var_map)?;
                let right = build_inline_expr(node.ordered_operands[1], plan, &var_map)?;
                let expr = expr::lower_bin(node.index.index(), *op, &left, &right)?;

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
                        let expr = build_inline_expr(ref_idx, plan, &var_map)?;
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
                    } else {
                        return Err(CompilerError::MissingDependency {
                            node: ref_idx.index(),
                        });
                    }
                } else {
                    return Err(CompilerError::UnsupportedOp {
                        node: node.index.index(),
                        op: "Ref with no operand".to_string(),
                    });
                }
            }

            PlanOpKind::Vec => {
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Record => {
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Proj { .. } => {
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Ram => {
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Pair => {
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Check => {
                // Verifier checks are not part of prover source emission.
            }

            PlanOpKind::Poly | PlanOpKind::Coef | PlanOpKind::Mle => {
                // Poly/Coef/Mle are no-ops in compiled code
                // Poly: Vec<Fr> → Uni (both Vec<Fr>)
                // Coef: Uni → Vec<Fr> (both Vec<Fr>)
                // Mle: Vec<Fr> → Mle (both Vec<Fr>)
                let expr = build_inline_expr(node.index, plan, &var_map)?;
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
            }

            PlanOpKind::Fft => {
                // FFT: in-place coefficients → evaluations
                let operand_idx =
                    node.ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: node.index.index(),
                            op: "Fft with no operand".to_string(),
                        })?;
                let operand_expr = build_inline_expr(*operand_idx, plan, &var_map)?;

                // Generate: let mut coeffs = operand; fft_vec::<Fr, FrOps>(&mut coeffs); let var = coeffs;
                body.push_str(&format!(
                    "    let mut {}_fft_tmp = {};\n",
                    node.var, operand_expr
                ));
                body.push_str(&format!(
                    "    fft_vec::<{}, {}Ops>(&mut {}_fft_tmp);\n",
                    options.target.scalar_type, options.target.scalar_type, node.var
                ));
                body.push_str(&format!("    let {} = {}_fft_tmp;\n", node.var, node.var));

                if node.is_transcript && is_pre_challenge {
                    body.push_str(&format!(
                        "    public_message(&mut state, &{})?;\n",
                        node.var
                    ));
                }
                var_map.insert(node.index, node.var.clone());
            }

            PlanOpKind::Ifft => {
                // IFFT: in-place evaluations → coefficients
                let operand_idx =
                    node.ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: node.index.index(),
                            op: "Ifft with no operand".to_string(),
                        })?;
                let operand_expr = build_inline_expr(*operand_idx, plan, &var_map)?;

                // Generate: let mut evals = operand; ifft_vec::<Fr, FrOps>(&mut evals); let var = evals;
                body.push_str(&format!(
                    "    let mut {}_ifft_tmp = {};\n",
                    node.var, operand_expr
                ));
                body.push_str(&format!(
                    "    ifft_vec::<{}, {}Ops>(&mut {}_ifft_tmp);\n",
                    options.target.scalar_type, options.target.scalar_type, node.var
                ));
                body.push_str(&format!("    let {} = {}_ifft_tmp;\n", node.var, node.var));

                if node.is_transcript && is_pre_challenge {
                    body.push_str(&format!(
                        "    public_message(&mut state, &{})?;\n",
                        node.var
                    ));
                }
                var_map.insert(node.index, node.var.clone());
            }

            PlanOpKind::Interpolate => {
                // Interpolate via IFFT (points are implicit FFT domain)
                // Same as IFFT but documents the intent
                let operand_idx =
                    node.ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: node.index.index(),
                            op: "Interpolate with no operand".to_string(),
                        })?;
                let operand_expr = build_inline_expr(*operand_idx, plan, &var_map)?;

                body.push_str(&format!(
                    "    let mut {}_interp_tmp = {};\n",
                    node.var, operand_expr
                ));
                body.push_str(&format!(
                    "    ifft_vec::<{}, {}Ops>(&mut {}_interp_tmp);\n",
                    options.target.scalar_type, options.target.scalar_type, node.var
                ));
                body.push_str(&format!(
                    "    let {} = {}_interp_tmp;\n",
                    node.var, node.var
                ));

                if node.is_transcript && is_pre_challenge {
                    body.push_str(&format!(
                        "    public_message(&mut state, &{})?;\n",
                        node.var
                    ));
                }
                var_map.insert(node.index, node.var.clone());
            }

            PlanOpKind::Reduce(op) => {
                // Vector reduction: delegate to shallow reduce wrappers
                let operand_idx =
                    node.ordered_operands
                        .first()
                        .ok_or_else(|| CompilerError::UnsupportedOp {
                            node: node.index.index(),
                            op: format!("Reduce({:?}) with no operand", op),
                        })?;

                let expr = build_inline_expr(*operand_idx, plan, &var_map)?;

                // Determine reduce wrapper based on operation and element type
                let wrapper = match op {
                    BinOp::Add => {
                        if node.rust_type.contains("usize") {
                            "reduce_add_index"
                        } else {
                            "reduce_add_scalar"
                        }
                    }
                    BinOp::Mul => "reduce_mul_scalar",
                    BinOp::And => "reduce_and_bool",
                    _ => {
                        return Err(CompilerError::UnsupportedOp {
                            node: node.index.index(),
                            op: format!("Reduce({:?})", op),
                        });
                    }
                };

                if should_emit_as_let(node, &use_counts) {
                    body.push_str(&format!("    let {} = {}(&{});\n", node.var, wrapper, expr));
                    if node.is_transcript && is_pre_challenge {
                        body.push_str(&format!(
                            "    public_message(&mut state, &{})?;\n",
                            node.var
                        ));
                    }
                    var_map.insert(node.index, node.var.clone());
                }
            }

            PlanOpKind::Bin(op) => {
                return Err(CompilerError::UnsupportedOp {
                    node: node.index.index(),
                    op: format!("{op:?} with fewer than two operands"),
                });
            }

            // Runtime-only operations (intentionally excluded from compiler):
            //
            // - Evaluate: Polynomial evaluation via VirtualPolynomial::evaluate_vec() is a
            //   method on a runtime-internal type. In generated code, polynomials are Vec<Fr>
            //   coefficients, and the compiler doesn't generate Evaluate operations.
            //
            // - Marginalize: Sumcheck primitive operating on VirtualPolynomial internals
            //   (hypercube iteration, partial evaluation). Used only in advanced examples
            //   (Spartan, sumcheck) which work fine in runtime mode. Too complex to extract
            //   as a shallow wrapper without exposing VirtualPolynomial abstractions.
            //
            // Both operations work correctly in runtime mode via backend/src/values.rs.
            other => {
                return Err(CompilerError::UnsupportedOp {
                    node: node.index.index(),
                    op: format!("{other:?}"),
                });
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

    Ok(format!(
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
    ))
}

// ---------------------------------------------------------------------------
// Verifier emission
// ---------------------------------------------------------------------------

fn emit_verifier(plan: &CodegenPlan, options: &CodegenOptions) -> Result<String> {
    // Build var_map seeded with all input args.
    let mut var_map: BTreeMap<NodeIndex, String> = plan
        .inputs
        .iter()
        .map(|a| (a.node, a.rust_name.clone()))
        .collect();

    // First pass: resolve Ref-kind Transcr nodes so their indices map to the
    // same var as the underlying arg.
    for node in &plan.nodes {
        if matches!(node.op_kind, PlanOpKind::Ref)
            && node.is_transcript
            && let Some(&ref_idx) = node.ordered_operands.first()
            && let Some(var) = var_map.get(&ref_idx).cloned()
        {
            var_map.insert(node.index, var);
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
        if let Some(t_node) = plan.nodes.iter().find(|n| n.index == t_idx)
            && matches!(t_node.op_kind, PlanOpKind::Ref)
            && let Some(&ref_idx) = t_node.ordered_operands.first()
            && let Some(input) = plan
                .inputs
                .iter()
                .find(|a| a.node == ref_idx && a.from_transcript)
        {
            pre_challenge_absorb.push(input.rust_name.clone());
        }
    }

    // Find the check node and extract the two sides of the equality.
    let check = plan
        .nodes
        .iter()
        .find(|n| n.is_check)
        .ok_or(CompilerError::MissingVerifierCheck)?;
    let equ_idx = *check
        .ordered_operands
        .first()
        .ok_or_else(|| CompilerError::UnsupportedOp {
            node: check.index.index(),
            op: "Check with no operand".to_string(),
        })?;
    let equ_node = plan
        .nodes
        .iter()
        .find(|n| n.index == equ_idx)
        .ok_or_else(|| CompilerError::MissingDependency {
            node: equ_idx.index(),
        })?;
    if !matches!(equ_node.op_kind, PlanOpKind::Bin(BinOp::Equ)) {
        return Err(CompilerError::UnsupportedOp {
            node: equ_node.index.index(),
            op: "verifier check must reference an equality node".to_string(),
        });
    }
    if equ_node.ordered_operands.len() < 2 {
        return Err(CompilerError::UnsupportedOp {
            node: equ_node.index.index(),
            op: "equality node with fewer than two operands".to_string(),
        });
    }
    let left_idx = equ_node.ordered_operands[0];
    let right_idx = equ_node.ordered_operands[1];
    let left_type = node_type(left_idx, plan).to_string();
    let right_type = node_type(right_idx, plan).to_string();

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
    let left_expr = build_inline_expr(left_idx, plan, &var_map)?;
    let right_expr = build_inline_expr(right_idx, plan, &var_map)?;

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
    let mut params = render_param_lines(&plan.inputs);
    params.push(format!("    proof: &{}", options.proof_type_path));
    let params = render_param_list(params);

    Ok(format!(
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
    ))
}
