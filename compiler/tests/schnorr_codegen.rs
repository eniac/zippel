//! Tests that the Schnorr prover and verifier codegen contain the
//! expected source snippets.

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
fn prover_contains_rand_sampling() {
    let (src, _) = emitted_schnorr_sources();
    assert!(
        src.contains("let r = ark_bls12_381::Fr::rand"),
        "prover must contain `let r = ark_bls12_381::Fr::rand`\n---\n{src}\n---"
    );
}

#[test]
fn prover_contains_group_mul() {
    let (src, _) = emitted_schnorr_sources();
    assert!(
        src.contains("let u = g * r"),
        "prover must contain `let u = g * r`\n---\n{src}\n---"
    );
}

#[test]
fn prover_absorbs_u_before_challenge() {
    let (src, _) = emitted_schnorr_sources();
    assert!(
        src.contains("public_message(&mut state, &u)?"),
        "prover must absorb u via public_message\n---\n{src}\n---"
    );
}

#[test]
fn prover_derives_challenge() {
    let (src, _) = emitted_schnorr_sources();
    assert!(
        src.contains("let c = challenge_scalar(&mut state)"),
        "prover must derive challenge c\n---\n{src}\n---"
    );
}

#[test]
fn prover_computes_response() {
    let (src, _) = emitted_schnorr_sources();
    assert!(
        src.contains("let z = r + x * c"),
        "prover must compute `let z = r + x * c`\n---\n{src}\n---"
    );
}

#[test]
fn prover_returns_proof() {
    let (src, _) = emitted_schnorr_sources();
    assert!(
        src.contains("Ok(Proof { u, z })"),
        "prover must return `Ok(Proof {{ u, z }})`\n---\n{src}\n---"
    );
}

#[test]
fn verifier_absorbs_public_inputs() {
    let (_, src) = emitted_schnorr_sources();
    assert!(
        src.contains("public_message(&mut state, &g)?"),
        "verifier must absorb g\n---\n{src}\n---"
    );
    assert!(
        src.contains("public_message(&mut state, &h)?"),
        "verifier must absorb h\n---\n{src}\n---"
    );
}

#[test]
fn verifier_absorbs_proof_u() {
    let (_, src) = emitted_schnorr_sources();
    assert!(
        src.contains("public_message(&mut state, &proof.u)?"),
        "verifier must absorb proof.u\n---\n{src}\n---"
    );
}

#[test]
fn verifier_derives_challenge() {
    let (_, src) = emitted_schnorr_sources();
    assert!(
        src.contains("let c = challenge_scalar(&mut state)"),
        "verifier must derive challenge c\n---\n{src}\n---"
    );
}

#[test]
fn verifier_uses_tokio_spawn() {
    let (_, src) = emitted_schnorr_sources();
    assert!(
        src.contains("tokio::spawn(async move"),
        "verifier must use tokio::spawn\n---\n{src}\n---"
    );
}

#[test]
fn verifier_awaits_both_handles() {
    let (_, src) = emitted_schnorr_sources();
    assert!(
        src.contains("let left = left_handle.await??"),
        "verifier must await left_handle\n---\n{src}\n---"
    );
}

#[test]
fn verifier_returns_equality() {
    let (_, src) = emitted_schnorr_sources();
    assert!(
        src.contains("Ok(left == right)"),
        "verifier must return `Ok(left == right)`\n---\n{src}\n---"
    );
}
