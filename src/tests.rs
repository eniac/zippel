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
    type F = <ArkBls12_381 as Backend>::F;
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
    inputs.insert("g", Value::g1(<ArkBls12_381 as Backend>::G1::default()));
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
    type F = <ArkBls12_381 as Backend>::F;
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
    type F = <ArkBls12_381 as Backend>::F;
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
    type F = <ArkBls12_381 as Backend>::F;
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
    inputs.insert("a", Value::Scalar(<ArkBls12_381 as Backend>::F::from(5u64)));
    inputs.insert("b", Value::Scalar(<ArkBls12_381 as Backend>::F::from(5u64)));

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
    Value::Scalar(<ArkBls12_381 as Backend>::F::from(x))
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
    inputs.insert("s", Value::Scalar(<ArkBls12_381 as Backend>::F::from(5u64)));

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
    inputs.insert("a", Value::Scalar(<ArkBls12_381 as Backend>::F::from(5u64)));
    inputs.insert("b", Value::Scalar(<ArkBls12_381 as Backend>::F::from(5u64)));
    inputs.insert(
        "c",
        Value::Scalar(<ArkBls12_381 as Backend>::F::from(42u64)),
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
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let g = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let h = backend::Group::batch_mul(&g, &[x])
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

/// The diagnostic `source` raises when compiled for `C`.
fn compile_error<C: backend::Backend>(source: &str, sizes: &[(&str, usize)]) -> String {
    let module = ParsedModule::parse("test.zippel", source).expect("parses");
    let sizes: Ctx<Tid, usize> = sizes.iter().map(|(k, v)| (Tid::new(k), *v)).collect();
    let Err(e) = module.compile::<C>(&sizes, CompileOptions::default()) else {
        panic!("compiles for {}", std::any::type_name::<C>());
    };
    e.diagnostics()
        .iter()
        .map(|d| d.summary.clone())
        .collect::<Vec<_>>()
        .join("\n")
}

/// A backend without what a protocol needs rejects it when the protocol is
/// compiled, with a diagnostic at the operation, rather than panicking at run
/// time: a pairing on Curve25519, which has none, and an 8-point FFT over its
/// scalar field, whose largest FFT domain has 4 points.
#[test]
fn compile_rejects_what_the_backend_lacks() {
    let kzg = std::fs::read_to_string("examples/kzg/kzg.zippel").unwrap();
    let error = compile_error::<backend::ArkCurve25519>(&kzg, &[("N", 4)]);
    assert!(error.contains("needs a pairing"), "{error}");
    assert!(
        ParsedModule::parse("kzg.zippel", kzg)
            .unwrap()
            .compile::<ArkBls12_381>(
                &Ctx::from_iter([(Tid::new("N"), 4)]),
                CompileOptions::default()
            )
            .is_ok()
    );

    let fft = "proto f<G: Group, F: Scalar<G>>(instance v: [F; 8]) where v == v {
    let p = interpolate(v);
    verify(coef(p) == v)
}
";
    let error = compile_error::<backend::ArkCurve25519>(fft, &[]);
    assert!(error.contains("an FFT over 8 points"), "{error}");
}

/// Schnorr proves and verifies on the `ff`/`group` backends, and a tampered proof
/// fails, as on arkworks.
#[test]
fn schnorr_runs_on_ff_group_backends() {
    fn run<C: backend::Backend>() {
        use backend::{Field, Group};
        let protocol = ParsedModule::parse("schnorr.zippel", SCHNORR)
            .unwrap()
            .compile::<C>(&Ctx::new(), CompileOptions::default())
            .unwrap();
        let mut rng = rand::rngs::OsRng;
        let x = C::F::rand(&mut rng);
        let g = C::G1::rand(&mut rng);
        let inputs = Ctx::from_iter([
            (Vid("x".to_string()), Value::<C>::Scalar(x)),
            (Vid("g".to_string()), Value::g1(g)),
            (Vid("h".to_string()), Value::g1(g * x)),
        ]);
        let prover = protocol.project_prover();
        let verifier = protocol.project_verifier().unwrap();
        let proof = prover.prove(inputs.clone()).unwrap();
        assert!(verifier.verify(proof.clone(), inputs.clone()).unwrap());
        let mut tampered = proof;
        tampered[0] = Value::g1(g);
        assert!(!verifier.verify(tampered, inputs).unwrap());
    }
    run::<backend::DalekRistretto>();
    run::<backend::PastaPallas>();
}

mod challenger {
    use super::*;
    use backend::{Backend, Group};
    use runtime::Challenger;

    type C = ArkBls12_381;
    type F = <C as Backend>::F;

    /// A transcript that hands out fixed challenges and keeps what it absorbs.
    #[derive(Default)]
    struct Scripted {
        challenges: Vec<F>,
        absorbed: Vec<Value<C>>,
    }

    impl Scripted {
        fn new(challenges: &[u64]) -> Self {
            Self {
                challenges: challenges.iter().rev().map(|&c| F::from(c)).collect(),
                absorbed: Vec::new(),
            }
        }
    }

    impl Challenger<C> for Scripted {
        fn instance(&mut self, value: &Value<C>) {
            self.absorbed.push(value.clone());
        }

        fn message(&mut self, value: &Value<C>) {
            self.absorbed.push(value.clone());
        }

        fn challenge(&mut self) -> Value<C> {
            Value::Scalar(self.challenges.pop().expect("a scripted challenge"))
        }
    }

    /// Schnorr under another transcript: Zippel absorbs the instance and the
    /// commitment before the challenge, the proof satisfies the verifier's
    /// equation for that challenge, and it verifies under that transcript only.
    #[test]
    fn a_challenger_drives_schnorr() {
        let protocol = schnorr();
        let x = F::from(5u64);
        let g = <C as Backend>::G1::generator();
        let h = g * x;
        let inputs = || {
            Ctx::from_iter([
                (Vid::from("x"), Value::Scalar(x)),
                (Vid::from("g"), Value::g1(g)),
                (Vid::from("h"), Value::g1(h)),
            ])
        };
        let mut transcript = Scripted::new(&[11]);
        let proof = protocol
            .project_prover()
            .prove_with(inputs(), &mut transcript)
            .unwrap();
        assert_eq!(transcript.absorbed.len(), 3, "g, h, then u");
        assert!(Value::equ(&transcript.absorbed[2], &proof[0]));
        let Value::Scalar(z) = proof[1] else {
            panic!("z is a scalar")
        };
        let rhs = proof[0].clone() + Value::g1(h * F::from(11u64));
        assert!(Value::equ(&Value::g1(g * z), &rhs), "g·z = u + h·c");
        let verifier = protocol.project_verifier().unwrap();
        assert!(
            verifier
                .verify_with(proof.clone(), inputs(), &mut Scripted::new(&[11]))
                .unwrap()
        );
        assert!(!verifier.verify(proof, inputs()).unwrap());
    }

    /// An excluded challenge is replaced by the transcript's next one.
    #[test]
    fn an_excluded_challenge_is_drawn_again() {
        let src = "proto p<G: Group, F: Scalar<G>>(instance g: G) where g == g {
    c <- challenge<F - [0]>;
    echo <- c;
    verify(g == g)
}
";
        let protocol = ParsedModule::parse("t.zippel", src)
            .unwrap()
            .compile::<C>(&Ctx::new(), CompileOptions::default())
            .unwrap();
        let inputs = Ctx::from_iter([(Vid::from("g"), Value::g1(<C as Backend>::G1::generator()))]);
        let proof = protocol
            .project_prover()
            .prove_with(inputs, &mut Scripted::new(&[0, 5]))
            .unwrap();
        assert_eq!(proof, [Value::Scalar(F::from(5u64))]);
    }
}
