//! `ZippelHandler::compile_for_execution` leaves the `where` clause out of
//! the protocol graph. The prover and verifier it projects must be the ones
//! `compile` projects, and the analyses must still see the relation.

use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::{ZippelArgs, ZippelHandler, check_verification};

type Handler = ZippelHandler<ArkBls12_381>;

fn schnorr() -> Handler {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/schnorr/schnorr.zippel");
    ZippelHandler::new(ZippelArgs::new(path))
}

fn schnorr_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &[x])
        .into_iter()
        .next()
        .unwrap();
    Ctx::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::g1(g)),
        (Vid("h".to_string()), Value::g1_affine(h)),
    ])
}

#[test]
fn projects_the_same_prover_and_verifier_as_compile() {
    let mut full = schnorr();
    full.compile(&Ctx::new());
    let mut exec = schnorr();
    exec.compile_for_execution(&Ctx::new());

    assert_eq!(
        full.prover_graph().node_count(),
        exec.prover_graph().node_count()
    );
    assert_eq!(
        full.verifier_graph().node_count(),
        exec.verifier_graph().node_count()
    );

    // Proofs cross over in both directions, so the two compiles also agree
    // on the Fiat-Shamir transcript.
    let inputs = schnorr_inputs();
    let proof = exec.run_prover(inputs.clone()).unwrap();
    assert!(check_verification(
        &full.run_verifier(proof, inputs.clone()).unwrap()
    ));
    let proof = full.run_prover(inputs.clone()).unwrap();
    assert!(check_verification(
        &exec.run_verifier(proof, inputs).unwrap()
    ));
}

#[test]
fn analyses_still_see_the_relation() {
    let mut exec = schnorr();
    exec.compile_for_execution(&Ctx::new());
    assert!(exec.analyze_completeness().is_ok());
}
