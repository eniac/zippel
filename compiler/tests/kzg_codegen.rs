use std::path::PathBuf;
use std::process::Command;

use backend::ArkBls12_381;
use compiler::{CodegenMode, CodegenOptions, compile_with_options};
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

fn kzg_handler() -> ZippelHandler<ArkBls12_381> {
    let workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate must be inside the workspace")
        .to_path_buf();
    let args = ZippelArgs::new(workspace.join("examples/kzg/kzg.zippel"));
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());
    handler
}

fn kzg_options(mode: CodegenMode) -> CodegenOptions {
    CodegenOptions {
        mode,
        session: "examples/kzg/kzg.zippel".to_string(),
        ..CodegenOptions::default()
    }
}

fn emitted_kzg_sources() -> (String, String) {
    let handler = kzg_handler();
    let mut prover = Vec::new();
    let mut verifier = Vec::new();

    compile_with_options(
        handler.prover_graph.as_ref().unwrap(),
        &kzg_options(CodegenMode::Prover),
        &mut prover,
    )
    .unwrap();
    compile_with_options(
        handler.verifier_graph.as_ref().unwrap(),
        &kzg_options(CodegenMode::Verifier),
        &mut verifier,
    )
    .unwrap();

    (
        String::from_utf8(prover).unwrap(),
        String::from_utf8(verifier).unwrap(),
    )
}

#[test]
fn kzg_prover_emits_commitment_and_opening_without_runtime() {
    let (source, _) = emitted_kzg_sources();

    assert!(source.contains("pub async fn prove"), "{source}");
    assert!(
        source.contains("pub commitment: ark_bls12_381::G1Projective"),
        "{source}"
    );
    assert!(
        source.contains("pub proof: ark_bls12_381::G1Projective"),
        "{source}"
    );
    assert!(source.contains("quotient_by_linear"), "{source}");
    assert!(source.contains("msm_g1"), "{source}");
    assert!(source.contains("tokio::spawn(async move"), "{source}");

    for forbidden in FORBIDDEN {
        assert!(
            !source.contains(forbidden),
            "generated KZG prover contains forbidden token {forbidden:?}\n---\n{source}\n---"
        );
    }
}

#[test]
fn kzg_verifier_emits_pairing_check_without_runtime() {
    let (_, source) = emitted_kzg_sources();

    assert!(source.contains("pub async fn verify"), "{source}");
    assert!(
        source.contains("ark_bls12_381::Bls12_381::pairing"),
        "{source}"
    );
    assert!(source.contains("pairing_lhs"), "{source}");
    assert!(source.contains("pairing_rhs"), "{source}");
    assert!(source.contains("tokio::spawn(async move"), "{source}");

    for forbidden in FORBIDDEN {
        assert!(
            !source.contains(forbidden),
            "generated KZG verifier contains forbidden token {forbidden:?}\n---\n{source}\n---"
        );
    }
}

#[test]
fn emitted_kzg_scaffold_compiles_and_rejects_tampered_proof() {
    let (prover, verifier) = emitted_kzg_sources();
    let dir = tempfile::tempdir().expect("tempdir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir(&src_dir).expect("create src dir");

    std::fs::write(
        dir.path().join("Cargo.toml"),
        r#"[package]
name = "generated_kzg_scaffold"
version = "0.1.0"
edition = "2024"

[dependencies]
ark-bls12-381 = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
ark-ec = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
ark-ff = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
ark-serialize = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
ark-std = "0.5.0"
rand = { version = "0.8", features = ["std"] }
tokio = { version = "1", features = ["macros", "rt-multi-thread"] }
"#,
    )
    .expect("write Cargo.toml");
    std::fs::write(src_dir.join("prover.rs"), prover).expect("write prover.rs");
    std::fs::write(src_dir.join("verifier.rs"), verifier).expect("write verifier.rs");
    std::fs::write(
        src_dir.join("main.rs"),
        r#"
mod prover;
mod verifier;

use ark_bls12_381::{Fr, G1Projective, G2Projective};
use ark_std::UniformRand;

fn eval_poly(coeffs: &[Fr], point: Fr) -> Fr {
    coeffs
        .iter()
        .rev()
        .fold(Fr::from(0_u64), |acc, coeff| acc * point + coeff)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut rng = rand::rngs::OsRng;
    let poly_coeffs = vec![Fr::from(3_u64), Fr::from(5_u64)];
    let eval_point = Fr::from(7_u64);
    let eval_result = eval_poly(&poly_coeffs, eval_point);
    let tau = Fr::from(11_u64);
    let gen_g1 = G1Projective::rand(&mut rng);
    let gen_g2 = G2Projective::rand(&mut rng);
    let srs_g1 = vec![gen_g1, gen_g1 * tau];
    let srs_g2_s = gen_g2 * tau;

    let proof = prover::prove(
        eval_point,
        eval_result,
        gen_g1,
        gen_g2,
        poly_coeffs,
        srs_g1.clone(),
        srs_g2_s,
    )
    .await?;

    let passed = verifier::verify(
        eval_point,
        eval_result,
        gen_g1,
        gen_g2,
        srs_g1.clone(),
        srs_g2_s,
        &proof,
    )
    .await?;
    assert!(passed, "honest KZG proof must verify");

    let mut tampered = proof.clone();
    tampered.proof = tampered.proof + gen_g1;
    let tampered_passed = verifier::verify(
        eval_point,
        eval_result,
        gen_g1,
        gen_g2,
        srs_g1,
        srs_g2_s,
        &tampered,
    )
    .await?;
    assert!(!tampered_passed, "tampered KZG proof must reject");

    Ok(())
}
"#,
    )
    .expect("write main.rs");

    let output = Command::new("cargo")
        .arg("run")
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(dir.path().join("Cargo.toml"))
        .output()
        .expect("run generated KZG package");

    assert!(
        output.status.success(),
        "generated KZG scaffold must compile and run\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
