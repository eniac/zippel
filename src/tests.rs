use super::*;
use backend::ArkBls12_381;
use lang::{
    ast::UModule,
    id::{Tid, Vid},
};
use runtime::RuntimeError;
use share::Ctx;
use std::collections::HashMap;

/// Inputs by argument name, as the tests pass them.
type TestInputs = HashMap<&'static str, Value<ArkBls12_381>>;

/// A verifier for a protocol whose prover sends a vector of `N = 4`
/// scalars and then a group element, with an honest proof.
fn shapes_protocol() -> (
    CompiledProtocol<ArkBls12_381>,
    TestInputs,
    Vec<Value<ArkBls12_381>>,
) {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let src = r"
proto shapes<G: Group, F: Scalar<G>, N: Size>(witness v: [F; N], instance g: G) where 1 == 1 {
    a <- v;
    b <- g * a[0];
    verify(b == g * a[0])
}
";
    let temp_dir = tempfile::tempdir().unwrap();
    let file_path = temp_dir.path().join("shapes.zippel");
    std::fs::write(&file_path, src).unwrap();
    let module = ParsedModule::load(file_path).expect("parse protocol");
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &4);
    let handler: CompiledProtocol<ArkBls12_381> = module
        .compile(&sizes, CompileOptions::default())
        .expect("compile protocol");
    let mut inputs = HashMap::new();
    inputs.insert("v", Value::vec_scalar((1..=4).map(F::from).collect()));
    inputs.insert("g", Value::g1(<ArkBls12_381 as ArkConfig>::G1::default()));
    let proof = handler.prove(inputs.clone()).expect("run_prover failed");
    (handler, inputs, proof)
}

#[test]
fn the_verifier_accepts_an_honest_proof_of_each_shape() {
    let (handler, inputs, proof) = shapes_protocol();
    assert_eq!(proof.len(), 2);
    let results = handler.verify(proof, inputs).expect("run_verifier failed");
    assert!(check_verification(&results));
}

#[test]
fn the_verifier_rejects_a_proof_with_extra_or_missing_elements() {
    let (handler, inputs, proof) = shapes_protocol();
    let mut longer = proof.clone();
    longer.push(proof[1].clone());
    for (tampered, found) in [(longer, 3), (proof[..1].to_vec(), 1), (Vec::new(), 0)] {
        match handler.verify(tampered, inputs.clone()) {
            Err(RuntimeError::ProofLength {
                expected: 2,
                found: f,
            }) => assert_eq!(f, found),
            other => panic!("a proof of {found} elements gave {other:?}"),
        }
    }
}

#[test]
fn the_verifier_rejects_proof_elements_of_the_wrong_shape() {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let (handler, inputs, proof) = shapes_protocol();
    let short = Value::vec_scalar(vec![F::from(1u64); 3]);
    let scalar = Value::Scalar(F::from(1u64));
    for (index, wrong) in [
        (0, short),
        (0, proof[1].clone()),
        (1, scalar),
        (1, proof[0].clone()),
    ] {
        let mut tampered = proof.clone();
        tampered[index] = wrong;
        match handler.verify(tampered, inputs.clone()) {
            Err(RuntimeError::MalformedProof { index: i, .. }) => assert_eq!(i, index),
            other => panic!("element {index} replaced gave {other:?}"),
        }
    }
}

#[test]
fn the_prover_rejects_inputs_of_the_wrong_shape() {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let (handler, inputs, _) = shapes_protocol();
    // `v: [F; 4]` (witness) one short, and `g: G` (instance) a scalar.
    for (name, wrong) in [
        ("v", Value::vec_scalar(vec![F::from(1u64); 3])),
        ("g", Value::Scalar(F::from(1u64))),
    ] {
        let mut tampered = inputs.clone();
        tampered.insert(name, wrong);
        match handler.prove(tampered) {
            Err(RuntimeError::MalformedInput { name: n, .. }) => assert_eq!(n, name),
            other => panic!("input `{name}` replaced gave {other:?}"),
        }
    }
}

#[test]
fn the_verifier_rejects_instance_inputs_of_the_wrong_shape() {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let (handler, mut inputs, proof) = shapes_protocol();
    inputs.insert("g", Value::Scalar(F::from(1u64)));
    match handler.verify(proof, inputs) {
        Err(RuntimeError::MalformedInput { name, .. }) => assert_eq!(name, "g"),
        other => panic!("instance `g` replaced gave {other:?}"),
    }
}

/// Runtime test: protocol with two verify statements, both passing.
/// Compile, run prover, run verifier, check that verification passes.
#[test]
fn test_runtime_multiple_verify_positive() {
    let src = r"
proto eq_proof<F: Field>(witness a: F, witness b: F) where a == b {
    let r = random<F>;
    x <- a * r;
    y <- b * r;
    verify(x == x);
    verify(x == y)
}
";
    let temp_dir = tempfile::tempdir().unwrap();
    let file_path = temp_dir.path().join("eq_proof_positive.zippel");
    std::fs::write(&file_path, src).unwrap();
    let module = ParsedModule::load(file_path).expect("parse protocol");
    let handler: CompiledProtocol<ArkBls12_381> = module
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol");

    let mut inputs = HashMap::<&str, Value<ArkBls12_381>>::new();
    inputs.insert(
        "a",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );
    inputs.insert(
        "b",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );

    let proof = handler.prove(inputs.clone()).expect("run_prover failed");
    let verifier_result = handler.verify(proof, inputs).expect("run_verifier failed");
    let passed = check_verification(&verifier_result);
    assert!(passed, "eq_proof with a == b should pass verification");
}

/// Regression for issue #157: re-logging earlier transcript values after a
/// challenge must preserve every proof element and verifier alignment.
#[test]
fn test_runtime_issue_157_transcript_relogs_after_challenge() {
    const EXPECTED_PROOF_VALUES: usize = 6;
    let src = r"
proto repro<F: Field>(witness s: F) where s == s {
    c <- challenge<F>;
    a <- c;
    b <- a;
    d <- c;
    e <- c;
    f <- c;
    g <- c;
    verify(a == g)
}
";

    let temp_dir = tempfile::tempdir().unwrap();
    let file_path = temp_dir.path().join("issue_157_relogs.zippel");
    std::fs::write(&file_path, src).unwrap();
    let module = ParsedModule::load(file_path).expect("parse protocol");
    let handler: CompiledProtocol<ArkBls12_381> = module
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol");

    let mut inputs = HashMap::<&str, Value<ArkBls12_381>>::new();
    inputs.insert(
        "s",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );

    let proof = handler.prove(inputs.clone()).expect("run_prover failed");
    assert_eq!(
        proof.len(),
        EXPECTED_PROOF_VALUES,
        "issue #157 repro should emit all six non-challenge transcript proof values"
    );

    let verifier_result = handler.verify(proof, inputs).expect("run_verifier failed");
    let passed = check_verification(&verifier_result);
    assert!(
        passed,
        "issue #157 repro should pass verification after transcript relogs"
    );
}

/// Runtime test: protocol where a verify condition is deliberately false.
/// The verification should FAIL when c ≠ 0.
#[test]
fn test_runtime_multiple_verify_negative_wrong_condition() {
    let src = r"
proto bad_check<F: Field>(witness a: F, witness b: F, instance c: F) where a == b {
    let r = random<F>;
    x <- a * r;
    y <- b * r;
    verify(x == y);
    verify(c == 0)
}
";
    let temp_dir = tempfile::tempdir().unwrap();
    let file_path = temp_dir.path().join("bad_check_negative.zippel");
    std::fs::write(&file_path, src).unwrap();
    let module = ParsedModule::load(file_path).expect("parse protocol");
    let handler: CompiledProtocol<ArkBls12_381> = module
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol");

    let mut inputs = HashMap::<&str, Value<ArkBls12_381>>::new();
    inputs.insert(
        "a",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );
    inputs.insert(
        "b",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );
    inputs.insert(
        "c",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(42u64)),
    );

    let proof = handler.prove(inputs.clone()).expect("run_prover failed");
    let verifier_result = handler.verify(proof, inputs).expect("run_verifier failed");
    let passed = check_verification(&verifier_result);
    assert!(
        !passed,
        "bad_check with c = 42 should fail verification since c != 0"
    );
}

const SCHNORR: &str = include_str!("../examples/schnorr/schnorr.zippel");

fn schnorr() -> CompiledProtocol<ArkBls12_381> {
    ParsedModule::parse("schnorr.zippel", SCHNORR)
        .unwrap()
        .compile(&Ctx::new(), CompileOptions::default())
        .unwrap()
}

fn schnorr_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    use ark_std::UniformRand;
    use backend::ArkGroupOps;
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
fn transcript_session_defaults_to_source_name_and_can_be_overridden() {
    let original = schnorr();
    assert_eq!(original.domain_separator_session(), "schnorr.zippel");
    let relocated = ParsedModule::parse("relocated.zippel", SCHNORR)
        .unwrap()
        .compile::<ArkBls12_381>(
            &Ctx::new(),
            CompileOptions {
                domain_separator_session: Some("schnorr.zippel".to_owned()),
                ..CompileOptions::default()
            },
        )
        .unwrap();
    let inputs = schnorr_inputs();
    let proof = original.prove(inputs.clone()).unwrap();
    assert!(check_verification(
        &relocated.verify(proof, inputs.clone()).unwrap()
    ));
    let proof = relocated.prove(inputs.clone()).unwrap();
    assert!(check_verification(&original.verify(proof, inputs).unwrap()));
}

#[test]
fn parsed_source_compiles_without_a_file() {
    let dir = tempfile::tempdir().unwrap();
    let module = ParsedModule::parse(
        dir.path().join("missing.zippel").display().to_string(),
        SCHNORR,
    )
    .unwrap();
    let protocol = module
        .compile::<ArkBls12_381>(&Ctx::new(), CompileOptions::default())
        .unwrap();
    let inputs = schnorr_inputs();
    let proof = protocol.prove(inputs.clone()).unwrap();
    assert!(check_verification(&protocol.verify(proof, inputs).unwrap()));
}

#[test]
fn source_errors_return_diagnostics() {
    let parse_error = ParsedModule::parse("invalid.zippel", "proto")
        .err()
        .expect("parse error");
    assert!(!parse_error.diagnostics().is_empty());
    assert!(parse_error.to_string().contains("invalid.zippel"));
    let invalid_types = "proto mismatch<G: Group, F: Scalar<G>>(instance g: G, instance x: F) where 1 == 1 { verify(g == x) }";
    let missing_sizes =
        "proto sized<F: Field, N: Size>(instance v: [F; N]) where 1 == 1 { verify(v[0] == v[0]) }";
    for (source, protocol) in [
        (invalid_types, None),
        (missing_sizes, None),
        (SCHNORR, Some("missing")),
    ] {
        let module = ParsedModule::parse("invalid.zippel", source).unwrap();
        let error = module
            .compile::<ArkBls12_381>(
                &Ctx::new(),
                CompileOptions {
                    protocol: protocol.map(str::to_owned),
                    ..CompileOptions::default()
                },
            )
            .err()
            .expect("compilation error");
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|d| d.severity == lang::diagnostic::Severity::Error)
        );
        assert!(error.to_string().contains("invalid.zippel"));
    }
}

/// Execution compilation preserves the graphs and transcript of full relation lowering.
#[test]
fn execution_matches_full_relation_lowering() {
    let exec = schnorr();
    let mut full = schnorr();
    let (module, diagnostics) = UModule::parse(SCHNORR);
    assert!(diagnostics.is_empty());
    let concrete = module.unwrap().concretize(&Ctx::new()).unwrap();
    let graphs = graph::UDags::<ArkBls12_381>::from_module(concrete).unwrap();
    let graph = graphs.get_proto(&"schnorr".to_owned()).unwrap();
    full.prover_graph = graph.get_prover().0;
    full.verifier_graph = graph.get_verifier().unwrap();
    assert_eq!(
        full.prover_graph().node_count(),
        exec.prover_graph().node_count()
    );
    assert_eq!(
        full.verifier_graph().node_count(),
        exec.verifier_graph().node_count()
    );
    let inputs = schnorr_inputs();
    let proof = exec.prove(inputs.clone()).unwrap();
    assert!(check_verification(
        &full.verify(proof, inputs.clone()).unwrap()
    ));
    let proof = full.prove(inputs.clone()).unwrap();
    assert!(check_verification(&exec.verify(proof, inputs).unwrap()));
}

/// Prepared analysis owns the full relation graph independently of execution.
#[test]
fn analysis_preparation_keeps_the_relation() {
    let protocol = schnorr();
    let prepared = protocol.prepare_analysis().unwrap();
    drop(protocol);
    assert!(
        prepared
            .run(Analysis::Completeness, analyses::GbBackendKind::ArkGb)
            .is_ok()
    );
}
