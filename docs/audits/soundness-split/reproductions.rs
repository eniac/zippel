use analyses::soundness::SoundnessModel;
use analyses::{
    CompletenessAnalysis, GbBackendKind, QualifierPropagation, SpecialSoundnessAnalysis,
};
use backend::ArkBls12_381;
use graph::UDags;
use lang::ast::UModule;
use share::Ctx;

fn dag(src: &str) -> graph::QDag<ArkBls12_381> {
    let (module, diagnostics) = UModule::parse(src);
    assert!(
        !diagnostics
            .iter()
            .any(|d| d.severity == lang::diagnostic::Severity::Error),
        "{diagnostics:?}"
    );
    let concrete = module.unwrap().concretize(&Ctx::new()).unwrap();
    assert!(
        concrete.typecheck().is_empty(),
        "type errors: {:?}",
        concrete.typecheck()
    );
    let graphs = UDags::<ArkBls12_381>::from_module(concrete).unwrap();
    QualifierPropagation::from_dag(graphs.protocols()[0])
}

fn soundness(src: &str, model: SoundnessModel, inline: bool) -> Result<(), String> {
    let g = dag(src);
    let inputs = SpecialSoundnessAnalysis::build_inputs_with_model(&g, vec![2], inline, model)
        .map_err(|e| e.to_string())?;
    eprintln!(
        "model={model:?}, inline={inline}, assumptions={:?}, goals={}",
        inputs.assumptions,
        inputs.rel_goals.len()
    );
    let backend = if std::env::var_os("ZIPPEL_AUDIT_SINGULAR").is_some() {
        GbBackendKind::Singular
    } else {
        GbBackendKind::default()
    };
    SpecialSoundnessAnalysis::from_inputs(inputs, backend, inline)
        .map_err(|e| e.to_string())?
        .run()
        .map_err(|e| e.to_string())
}

#[test]
fn empty_group_basis_must_not_erase_goals() {
    let src = r#"
        proto bad<G: Group, F: Scalar<G>>(
            witness x: F, instance g: G, instance h: G, instance y: F,
        ) where g == h && h == g * x && x == y {
            t <- g;
            c <- challenge<F>;
            z <- x + c - c;
            verify(z == y)
        }
    "#;
    assert!(soundness(src, SoundnessModel::Plain, true).is_err());
    let results: Vec<_> = [
        SoundnessModel::SymbolicGroup,
        SoundnessModel::SymbolicGroupResponses,
    ]
    .into_iter()
    .map(|model| (model, soundness(src, model, true)))
    .collect();
    assert!(
        results.iter().all(|(_, r)| r.is_err()),
        "invalid protocol accepted: {results:?}"
    );
}

#[test]
fn scalar_bool_relation_requires_local_semantics() {
    let src = r#"
        proto valid<F: Field>(witness x: F, instance y: F) where (x == y) == (y == y) {
            t <- x;
            c <- challenge<F>;
            z <- x + c;
            verify(t == y && z == y + c)
        }
    "#;
    let results: Vec<_> = [true, false]
        .into_iter()
        .map(|inline| (inline, soundness(src, SoundnessModel::Plain, inline)))
        .collect();
    assert!(
        results.iter().all(|(_, r)| r.is_ok()),
        "valid bool relation rejected: {results:?}"
    );
}

#[test]
fn body_assert_completeness_probe() {
    let src = r#"
        proto bad<F: Field>(witness x: F) where x == 0 {
            assert(x == 1);
            t <- x;
            verify(t == 0)
        }
    "#;
    let g = dag(src);
    let inputs = CompletenessAnalysis::build_inputs(&g, true);
    eprintln!("body assertions: {}", inputs.body_asserts);
    let result =
        CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default()).run();
    assert!(
        result.is_err(),
        "aborting prover called complete: {result:?}"
    );
}

#[test]
fn vector_response_must_be_fresh_in_plain_mode() {
    let src = r#"
        proto bad<G: Group, F: Scalar<G>>(
            witness x: F, instance g: G, instance h: G,
        ) where h == g * x && h == (g - g) {
            let r = random<F>;
            t <- g * r;
            c <- challenge<F>;
            z <- [r + x * c];
            verify(g * z[0] == t + h * c)
        }
    "#;
    let result = soundness(src, SoundnessModel::Plain, true);
    assert!(result.is_err(), "unchecked h == 0 accepted: {result:?}");
}

#[test]
fn symbolic_constant_witness_can_be_extracted() {
    let src = r#"
        proto valid<F: Field>(witness x: F) where x == 0 {
            t <- x;
            c <- challenge<F>;
            z <- x + c;
            verify(t == 0 && z == c)
        }
    "#;
    assert!(soundness(src, SoundnessModel::Plain, true).is_ok());
    let result = soundness(src, SoundnessModel::SymbolicGroup, true);
    assert!(
        result.is_ok(),
        "constant witness should be extractable: {result:?}"
    );
}

#[test]
fn completeness_boolean_transcript_is_opaque_to_verifier() {
    let src = r#"
        proto valid<F: Field>(witness x: F, instance y: F) where x == y {
            t <- x == y;
            verify(t)
        }
    "#;
    let g = dag(src);
    let inputs = CompletenessAnalysis::build_inputs(&g, true);
    let result =
        CompletenessAnalysis::<ArkBls12_381>::from_inputs(inputs, GbBackendKind::default()).run();
    assert!(result.is_ok(), "valid Boolean message rejected: {result:?}");
}
