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
    CompiledProver<ArkBls12_381>,
    CompiledVerifier<ArkBls12_381>,
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
    let protocol: CompiledProtocol<ArkBls12_381> = module
        .compile(&sizes, CompileOptions::default())
        .expect("compile protocol");
    let mut inputs = HashMap::new();
    inputs.insert("v", Value::vec_scalar((1..=4).map(F::from).collect()));
    inputs.insert("g", Value::g1(<ArkBls12_381 as ArkConfig>::G1::default()));
    let prover = protocol.project_prover();
    let verifier = protocol.project_verifier().expect("project verifier");
    drop(protocol);
    let proof = prover.prove(inputs.clone()).expect("run_prover failed");
    (prover, verifier, inputs, proof)
}

#[test]
fn the_verifier_accepts_an_honest_proof_of_each_shape() {
    let (_, verifier, inputs, proof) = shapes_protocol();
    assert_eq!(proof.len(), 2);
    let passed = verifier.verify(proof, inputs).expect("run_verifier failed");
    assert!(passed);
}

#[test]
fn the_verifier_rejects_a_proof_with_extra_or_missing_elements() {
    let (_, verifier, inputs, proof) = shapes_protocol();
    let mut longer = proof.clone();
    longer.push(proof[1].clone());
    for (tampered, found) in [(longer, 3), (proof[..1].to_vec(), 1), (Vec::new(), 0)] {
        match verifier.verify(tampered, inputs.clone()) {
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
    let (_, verifier, inputs, proof) = shapes_protocol();
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
        match verifier.verify(tampered, inputs.clone()) {
            Err(RuntimeError::MalformedProof { index: i, .. }) => assert_eq!(i, index),
            other => panic!("element {index} replaced gave {other:?}"),
        }
    }
}

#[test]
fn the_prover_rejects_inputs_of_the_wrong_shape() {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let (prover, _, inputs, _) = shapes_protocol();
    // `v: [F; 4]` (witness) one short, and `g: G` (instance) a scalar.
    for (name, wrong) in [
        ("v", Value::vec_scalar(vec![F::from(1u64); 3])),
        ("g", Value::Scalar(F::from(1u64))),
    ] {
        let mut tampered = inputs.clone();
        tampered.insert(name, wrong);
        match prover.prove(tampered) {
            Err(RuntimeError::MalformedInput { name: n, .. }) => assert_eq!(n, name),
            other => panic!("input `{name}` replaced gave {other:?}"),
        }
    }
}

#[test]
fn the_verifier_rejects_instance_inputs_of_the_wrong_shape() {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let (_, verifier, mut inputs, proof) = shapes_protocol();
    inputs.insert("g", Value::Scalar(F::from(1u64)));
    match verifier.verify(proof, inputs) {
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
    let protocol: CompiledProtocol<ArkBls12_381> = module
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol");
    let prover = protocol.project_prover();
    let verifier = protocol.project_verifier().expect("project verifier");

    let mut inputs = HashMap::<&str, Value<ArkBls12_381>>::new();
    inputs.insert(
        "a",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );
    inputs.insert(
        "b",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );

    let proof = prover.prove(inputs.clone()).expect("run_prover failed");
    let passed = verifier.verify(proof, inputs).expect("run_verifier failed");
    assert!(passed, "eq_proof with a == b should pass verification");
}

/// The protocol `src`, compiled at no sizes.
fn compile_src(src: &str) -> CompiledProtocol<ArkBls12_381> {
    let temp_dir = tempfile::tempdir().unwrap();
    let file_path = temp_dir.path().join("protocol.zippel");
    std::fs::write(&file_path, src).unwrap();
    ParsedModule::load(file_path)
        .expect("parse protocol")
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol")
}

fn scalar(x: u64) -> Value<ArkBls12_381> {
    Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(x))
}

#[test]
fn the_verifier_rejects_a_proof_that_makes_it_divide_by_zero() {
    let protocol = compile_src(
        "proto divides<F: Field>(witness a: F, instance b: F) where a == b {
            m <- a;
            verify(b / m == 1)
        }",
    );
    let verifier = protocol.project_verifier().expect("project verifier");
    let inputs = HashMap::from([("a", scalar(5)), ("b", scalar(5))]);
    let proof = protocol.project_prover().prove(inputs.clone()).unwrap();
    assert!(matches!(verifier.verify(proof, inputs.clone()), Ok(true)));
    assert!(matches!(
        verifier.verify([scalar(0)], inputs),
        Err(RuntimeError::DivisionByZero)
    ));
}

#[test]
fn a_prover_that_divides_by_zero_fails() {
    let protocol = compile_src(
        "proto inverts<F: Field>(witness a: F) where a == a {
            m <- 1 / a;
            verify(m == m)
        }",
    );
    let inputs = HashMap::from([("a", scalar(0))]);
    assert!(matches!(
        protocol.project_prover().prove(inputs),
        Err(RuntimeError::DivisionByZero)
    ));
}

/// Samples with exclusions run end to end, the verifier computing a
/// challenge's excluded values from the instance.
#[test]
fn samples_with_exclusions_prove_and_verify() {
    let protocol = compile_src(
        "proto excludes<F: Field>(witness a: F, instance b: F) where a == b {
            let r = random<F - roots_of_unity(4)>;
            m <- a / (r ^ 4 - 1);
            n <- r ^ 4 - 1;
            c <- challenge<F - [b, 1]>;
            verify(m * n / ((c - b) * (c - 1)) == b / ((c - b) * (c - 1)))
        }",
    );
    let inputs = HashMap::from([("a", scalar(5)), ("b", scalar(5))]);
    let proof = protocol.project_prover().prove(inputs.clone()).unwrap();
    let verifier = protocol.project_verifier().expect("project verifier");
    assert!(matches!(verifier.verify(proof, inputs), Ok(true)));
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
    let protocol: CompiledProtocol<ArkBls12_381> = module
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol");
    let prover = protocol.project_prover();
    let verifier = protocol.project_verifier().expect("project verifier");

    let mut inputs = HashMap::<&str, Value<ArkBls12_381>>::new();
    inputs.insert(
        "s",
        Value::Scalar(<ArkBls12_381 as ArkConfig>::F::from(5u64)),
    );

    let proof = prover.prove(inputs.clone()).expect("run_prover failed");
    assert_eq!(
        proof.len(),
        EXPECTED_PROOF_VALUES,
        "issue #157 repro should emit all six non-challenge transcript proof values"
    );

    let passed = verifier.verify(proof, inputs).expect("run_verifier failed");
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
    let protocol: CompiledProtocol<ArkBls12_381> = module
        .compile(&Ctx::new(), CompileOptions::default())
        .expect("compile protocol");
    let prover = protocol.project_prover();
    let verifier = protocol.project_verifier().expect("project verifier");

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

    let proof = prover.prove(inputs.clone()).expect("run_prover failed");
    let passed = verifier.verify(proof, inputs).expect("run_verifier failed");
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
    let original_prover = original.project_prover();
    let original_verifier = original.project_verifier().unwrap();
    let relocated_prover = relocated.project_prover();
    let relocated_verifier = relocated.project_verifier().unwrap();
    let inputs = schnorr_inputs();
    let proof = original_prover.prove(inputs.clone()).unwrap();
    assert!(relocated_verifier.verify(proof, inputs.clone()).unwrap());
    let proof = relocated_prover.prove(inputs.clone()).unwrap();
    assert!(original_verifier.verify(proof, inputs).unwrap());
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
    let prover = protocol.project_prover();
    let verifier = protocol.project_verifier().unwrap();
    drop(protocol);
    drop(module);
    let inputs = schnorr_inputs();
    for _ in 0..2 {
        let proof = prover.prove(inputs.clone()).unwrap();
        assert!(verifier.verify(proof, inputs.clone()).unwrap());
    }
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

/// Joint compilation succeeds before projection checks the verifier's visibility.
#[test]
fn verifier_projection_returns_source_diagnostics_for_private_dependencies() {
    for (source, private_name) in [
        (
            "proto leak<F: Field>(witness s: F) where s == s { verify(s == s) }",
            "s",
        ),
        (
            "proto leak<F: Field>() where 1 == 1 { let r = random<F>; verify(r == r) }",
            "r",
        ),
    ] {
        let module = ParsedModule::parse("private.zippel", source).unwrap();
        let protocol = module
            .compile::<ArkBls12_381>(&Ctx::new(), CompileOptions::default())
            .unwrap();
        let error = protocol
            .project_verifier()
            .err()
            .expect("private dependency");
        let diagnostic = &error.diagnostics()[0];
        assert_eq!(&source[diagnostic.span.clone()], private_name);
        assert!(error.to_string().contains("private.zippel"));
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
    let typed = concrete.typecheck().unwrap();
    let graphs = graph::UDags::<ArkBls12_381>::lower(&typed, graph::Relations::Lower).unwrap();
    let graph = graphs.protocol(&"schnorr".to_owned()).unwrap();
    full.graph = graph.clone();
    let full_prover = full.project_prover();
    let full_verifier = full.project_verifier().unwrap();
    let exec_prover = exec.project_prover();
    let exec_verifier = exec.project_verifier().unwrap();
    assert_eq!(
        full_prover.graph().node_count(),
        exec_prover.graph().node_count()
    );
    assert_eq!(
        full_verifier.graph().node_count(),
        exec_verifier.graph().node_count()
    );
    let inputs = schnorr_inputs();
    let proof = exec_prover.prove(inputs.clone()).unwrap();
    assert!(full_verifier.verify(proof, inputs.clone()).unwrap());
    let proof = full_prover.prove(inputs.clone()).unwrap();
    assert!(exec_verifier.verify(proof, inputs).unwrap());
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

/// A protocol over `a: Mle<F, 2>`, `b: Mle<F, 3>`, `q: Poly<F, 2, 2>`,
/// `p: Poly<F, 3, 2>`, `u: Uni<F, 2>` and a point `x: [F; 3]` that sends `sent`
/// and checks it equals `expected`; `helpers` are function declarations `sent`
/// may call.
fn polynomial_mix_source(helpers: &str, sent: &str, expected: &str) -> String {
    format!(
        "{helpers}
        proto mix<F: Field>(
            instance a: Mle<F, 2>, instance b: Mle<F, 3>, instance q: Poly<F, 2, 2>,
            instance p: Poly<F, 3, 2>, instance u: Uni<F, 2>, instance x: [F; 3],
        ) where x[0] == x[0] {{
            y <- {sent};
            verify(y == {expected})
        }}"
    )
}

/// Polynomials over different numbers of variables never combine, join or fit:
/// no layer agrees on lifting one to more variables (the runtime cannot
/// evaluate the mix, and the analysis would zero-pad an MLE table).
#[test]
fn polynomials_over_different_numbers_of_variables_are_rejected() {
    let combine = "polynomials over different numbers of variables never combine";
    let join = combine;
    let first = "fn first<F: Field>(instance a: Mle<F, 2>, instance b: Mle<F, 3>) -> Mle<F, 3> {
        let v = [a, b];
        v[0]
    }";
    let widen = "fn widen<F: Field>(instance p: Poly<F, 3, 2>) -> Poly<F, 3, 2> { p }";
    for (helpers, sent, reason) in [
        ("", "eval(a + b, x)", combine),
        ("", "eval(a - b, x)", combine),
        ("", "eval(a * b, x)", combine),
        ("", "eval(a + p, x)", combine),
        ("", "eval(a * p, x)", combine),
        ("", "eval(q + p, x)", combine),
        ("", "eval(u + b, x)", combine),
        ("", "eval(u * p, x)", combine),
        ("", "eval(reduce(+, [a, b]), x)", join),
        (first, "eval(first(a, b), x)", join),
        (
            widen,
            "eval(widen(q), x)",
            "No definition of `widen` accepts arguments of type Poly<F, 2, 2>",
        ),
    ] {
        let source = polynomial_mix_source(helpers, sent, "y");
        let compiled = ParsedModule::parse("mix.zippel", source)
            .and_then(|m| m.compile::<ArkBls12_381>(&Ctx::new(), CompileOptions::default()));
        let Err(CompileError::Diagnostics { diagnostics, .. }) = compiled else {
            panic!("`{sent}` should not typecheck");
        };
        // The diagnostics' own text, not the source they quote.
        let text: Vec<String> = diagnostics
            .iter()
            .flat_map(|d| {
                [d.summary.clone(), d.primary_label.clone()]
                    .into_iter()
                    .chain(d.notes.iter().map(|n| n.message.clone()))
            })
            .collect();
        assert!(
            text.iter().any(|t| t.contains(reason)),
            "`{sent}` should fail with `{reason}`: {text:?}"
        );
    }
}

/// Over the same variables, polynomials of different encodings and degrees
/// combine, and the analysis and the runtime agree on the result.
#[test]
fn polynomials_over_the_same_variables_combine_in_analysis_and_runtime() {
    use ark_ff::UniformRand;
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = ark_std::test_rng();
    let mut rand = |n: usize| (0..n).map(|_| F::rand(&mut rng)).collect::<Vec<_>>();
    let a = backend::VirtualPolynomial::dense_mle(2, rand(4));
    let b = backend::VirtualPolynomial::dense_mle(3, rand(8));
    let inputs: TestInputs = HashMap::from([
        ("a", Value::poly(a.clone())),
        ("b", Value::poly(b.clone())),
        ("q", Value::poly(a.poly_mul(&a))),
        ("p", Value::poly(b.poly_mul(&b))),
        (
            "u",
            Value::poly(backend::VirtualPolynomial::univariate(rand(3))),
        ),
        ("x", Value::vec_scalar(rand(3))),
    ]);
    let at_uni = "fn at_uni<F: Field>(instance p: Uni<F, 4>, instance t: F) -> F { p(t) }";
    let x01 = "[x[0], x[1]]";
    for (helpers, sent, expected) in [
        (
            "",
            "eval(b + p, x)".to_string(),
            "eval(b, x) + eval(p, x)".to_string(),
        ),
        (
            "",
            "eval(b * p, x)".to_string(),
            "eval(b, x) * eval(p, x)".to_string(),
        ),
        (
            "",
            format!("eval(a + q, {x01})"),
            format!("eval(a, {x01}) + eval(q, {x01})"),
        ),
        (at_uni, "at_uni(u, x[0])".to_string(), "u(x[0])".to_string()),
    ] {
        let protocol = compile_src(&polynomial_mix_source(helpers, &sent, &expected));
        let analysis = protocol.prepare_analysis().expect("prepare analysis");
        let completeness = analysis.run(Analysis::Completeness, analyses::GbBackendKind::ArkGb);
        assert!(
            completeness.is_ok(),
            "completeness of `{sent}`: {completeness:?}"
        );
        let proof = protocol
            .project_prover()
            .prove(inputs.clone())
            .expect("prove");
        let verifier = protocol.project_verifier().expect("project verifier");
        assert!(
            matches!(verifier.verify(proof, inputs.clone()), Ok(true)),
            "`{sent}` should verify"
        );
    }
}

/// `==` on polynomials means the same polynomial in both the completeness
/// analysis and the runtime, whatever the storage: equal polynomials stored as
/// a univariate, a dense table or a sparse table compare equal, and a join of
/// two encodings keeps each value.
#[test]
fn polynomial_equality_agrees_in_analysis_and_runtime() {
    use ark_ff::UniformRand;
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = ark_std::test_rng();
    let (a, b, x) = (F::rand(&mut rng), F::rand(&mut rng), F::rand(&mut rng));
    let zero = F::from(0u64);
    // `u`, `m` and `ms` are all a + b·x; `m2` differs.
    let inputs: TestInputs = HashMap::from([
        (
            "u",
            Value::poly(backend::VirtualPolynomial::univariate(vec![
                a, b, zero, zero,
            ])),
        ),
        (
            "m",
            Value::poly(backend::VirtualPolynomial::dense_mle(1, vec![a, a + b])),
        ),
        (
            "ms",
            Value::poly(backend::VirtualPolynomial::sparse_mle(
                1,
                vec![(0, a), (1, a + b)],
            )),
        ),
        (
            "m2",
            Value::poly(backend::VirtualPolynomial::dense_mle(
                1,
                vec![a, a + b + F::from(1u64)],
            )),
        ),
        ("x", Value::Scalar(x)),
    ]);
    // (relation, body, whether the honest run verifies)
    for (relation, body, verifies) in [
        ("u == m", "verify(u == m)", true),
        ("m == ms", "verify(m == ms)", true),
        ("x == x", "verify(u == m2)", false),
        (
            "x == x",
            "let v = [u, m];\n let w = v[1];\n y <- w(x);\n verify(y == m(x))",
            true,
        ),
        (
            "x == x",
            "let v = [u, m];\n let w = v[0];\n y <- w(x);\n verify(y == u(x))",
            true,
        ),
    ] {
        let protocol = compile_src(&format!(
            "proto eq<F: Field>(
                instance u: Uni<F, 3>, instance m: Mle<F, 1>, instance ms: Mle<F, 1>,
                instance m2: Mle<F, 1>, instance x: F,
            ) where {relation} {{
                {body}
            }}"
        ));
        let analysis = protocol.prepare_analysis().expect("prepare analysis");
        let completeness = analysis.run(Analysis::Completeness, analyses::GbBackendKind::ArkGb);
        assert_eq!(
            completeness.is_ok(),
            verifies,
            "completeness of `{body}`: {completeness:?}"
        );
        let proof = protocol
            .project_prover()
            .prove(inputs.clone())
            .expect("prove");
        let verifier = protocol.project_verifier().expect("project verifier");
        assert_eq!(
            verifier.verify(proof, inputs.clone()).ok(),
            Some(verifies),
            "runtime of `{body}`"
        );
    }
}
