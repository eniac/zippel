use std::io::Write;

use backend::ArkConfig;
use graph::Dag;

use crate::error::Result;
use crate::options::{CodegenMode, CodegenOptions};
use crate::{plan, transcript};

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

fn common_prelude(options: &CodegenOptions) -> String {
    format!(
        r#"#![allow(dead_code, unused_imports, unused_variables)]

use ark_serialize::CanonicalSerialize;
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

fn render_params<'a>(inputs: impl IntoIterator<Item = &'a plan::PlanArg>) -> String {
    inputs
        .into_iter()
        .filter(|arg| !arg.from_transcript)
        .map(|arg| format!("    {}: {}", arg.rust_name, arg.rust_type))
        .collect::<Vec<_>>()
        .join(",\n")
}

fn render_proof_fields(plan: &plan::CodegenPlan) -> String {
    plan.proof_outputs
        .iter()
        .filter_map(|idx| plan.nodes.iter().find(|node| node.index == *idx))
        .map(|node| format!("    pub {}: {},", node.var, node.rust_type))
        .collect::<Vec<_>>()
        .join("\n")
}

fn emit_prover(plan: &plan::CodegenPlan, options: &CodegenOptions) -> String {
    let params = render_params(&plan.inputs);
    let proof_fields = render_proof_fields(plan);
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
    Err(GeneratedError::Unimplemented("Schnorr operation lowering is not emitted yet"))
}}
"#,
        common_prelude(options),
        proof_fields,
        params
    )
}

fn emit_verifier(plan: &plan::CodegenPlan, options: &CodegenOptions) -> String {
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
    Err(GeneratedError::Unimplemented("Schnorr verifier lowering is not emitted yet"))
}}
"#,
        common_prelude(options),
        params
    )
}
