use std::path::PathBuf;
use std::process::Command;

use backend::ArkBls12_381;
use compiler::{compile_prover, compile_verifier};
use share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

const SCHNORR_SRC: &str = r#"
proto schnorr<G: Group, F: Scalar<G>>(private x: F, public g: G, public h: G) where h == g*x {
    let r = random<F>;
    u <- g*r;
    c <- challenge<F*>;
    z <- r + x*c;
    verify(g*z == u + h*c)
}
"#;

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
    let dir = tempfile::tempdir().expect("tempdir");
    let path: PathBuf = dir.path().join("schnorr.zippel");
    std::fs::write(&path, SCHNORR_SRC).expect("write schnorr.zippel");
    let args = ZippelArgs::new(path);
    let mut handler = ZippelHandler::<ArkBls12_381>::new(args);
    handler.compile(&Ctx::new());
    handler
}

fn emitted_schnorr_sources() -> (String, String) {
    let handler = schnorr_handler();
    let mut prover = Vec::new();
    let mut verifier = Vec::new();

    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut prover).unwrap();
    compile_verifier(handler.verifier_graph.as_ref().unwrap(), &mut verifier).unwrap();

    (
        String::from_utf8(prover).unwrap(),
        String::from_utf8(verifier).unwrap(),
    )
}

#[test]
fn emitted_prover_contains_prove_function() {
    let (source, _) = emitted_schnorr_sources();

    assert!(
        source.contains("pub async fn prove"),
        "generated prover must contain `pub async fn prove`\n---\n{source}\n---"
    );
}

#[test]
fn emitted_verifier_contains_verify_function() {
    let (_, source) = emitted_schnorr_sources();

    assert!(
        source.contains("pub async fn verify"),
        "generated verifier must contain `pub async fn verify`\n---\n{source}\n---"
    );
}

#[test]
fn emitted_prover_has_no_zippel_runtime_dependencies() {
    let (source, _) = emitted_schnorr_sources();

    for forbidden in FORBIDDEN {
        assert!(
            !source.contains(forbidden),
            "generated prover contains forbidden token {forbidden:?}\n---\n{source}\n---"
        );
    }
}

#[test]
fn emitted_verifier_has_no_zippel_runtime_dependencies() {
    let (_, source) = emitted_schnorr_sources();

    for forbidden in FORBIDDEN {
        assert!(
            !source.contains(forbidden),
            "generated verifier contains forbidden token {forbidden:?}\n---\n{source}\n---"
        );
    }
}

#[test]
fn emitted_schnorr_scaffold_compiles_in_standalone_package() {
    let (prover, verifier) = emitted_schnorr_sources();
    let dir = tempfile::tempdir().expect("tempdir");
    let src_dir = dir.path().join("src");
    std::fs::create_dir(&src_dir).expect("create src dir");

    std::fs::write(
        dir.path().join("Cargo.toml"),
        r#"[package]
name = "generated_schnorr_scaffold"
version = "0.1.0"
edition = "2024"

[dependencies]
ark-bls12-381 = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
ark-ff = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
ark-serialize = { git = "https://github.com/arkworks-rs/algebra.git", rev = "c1f4f5665504154a9de2345f464b0b3da72c28ec" }
spongefish = { git = "https://github.com/arkworks-rs/spongefish.git", rev = "bdc640573a102b536d38a7613c1297b2b067fb1e", features = ["ark-ff", "ark-ec"] }
tokio = { version = "1", features = ["rt", "macros"] }
"#,
    )
    .expect("write Cargo.toml");
    std::fs::write(
        src_dir.join("lib.rs"),
        "pub mod prover;\npub mod verifier;\n",
    )
    .expect("write lib.rs");
    std::fs::write(src_dir.join("prover.rs"), prover).expect("write prover.rs");
    std::fs::write(src_dir.join("verifier.rs"), verifier).expect("write verifier.rs");

    let output = Command::new("cargo")
        .arg("check")
        .arg("--quiet")
        .arg("--manifest-path")
        .arg(dir.path().join("Cargo.toml"))
        .output()
        .expect("run cargo check");

    assert!(
        output.status.success(),
        "generated scaffold must compile\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
