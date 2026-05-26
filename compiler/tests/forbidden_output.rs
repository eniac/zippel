use std::path::PathBuf;

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

#[test]
fn emitted_prover_contains_prove_function() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_prover(handler.prover_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("pub async fn prove"),
        "generated prover must contain `pub async fn prove`\n---\n{source}\n---"
    );
}

#[test]
fn emitted_verifier_contains_verify_function() {
    let handler = schnorr_handler();
    let mut out = Vec::new();

    compile_verifier(handler.verifier_graph.as_ref().unwrap(), &mut out).unwrap();
    let source = String::from_utf8(out).unwrap();

    assert!(
        source.contains("pub async fn verify"),
        "generated verifier must contain `pub async fn verify`\n---\n{source}\n---"
    );
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
            "generated prover contains forbidden token {forbidden:?}\n---\n{source}\n---"
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
            "generated verifier contains forbidden token {forbidden:?}\n---\n{source}\n---"
        );
    }
}
