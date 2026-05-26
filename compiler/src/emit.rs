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
    Err(GeneratedError::Serialization(
        ark_serialize::SerializationError::InvalidData,
    ))
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
