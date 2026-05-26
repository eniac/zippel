use backend::{ABase, ATyp};
use compiler::{CodegenOptions, CompilerError};
use lang::typ::CRange;
use share::Ctx;

fn opts() -> CodegenOptions {
    CodegenOptions::prover()
}

#[test]
fn maps_bls12_381_base_types() {
    let opts = opts();

    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::Scalar), &opts).unwrap(),
        "ark_bls12_381::Fr"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::G1), &opts).unwrap(),
        "ark_bls12_381::G1Projective"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::G2), &opts).unwrap(),
        "ark_bls12_381::G2Projective"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::GT), &opts).unwrap(),
        "ark_ec::pairing::PairingOutput<ark_bls12_381::Bls12_381>"
    );
    assert_eq!(
        compiler::testing::render_type(&ATyp::Base(ABase::Bool), &opts).unwrap(),
        "bool"
    );
}

#[test]
fn maps_vectors_and_records_without_value() {
    let opts = opts();

    // Vec<scalar>
    let vec_typ = ATyp::Vec(Box::new(ATyp::Base(ABase::Scalar)), 3);
    assert_eq!(
        compiler::testing::render_type(&vec_typ, &opts).unwrap(),
        "Vec<ark_bls12_381::Fr>"
    );

    // Record: "ok" -> Bool, "s" -> Scalar.
    // share::Ctx iterates in key-sorted order ("ok" < "s"), which happens to
    // match the insertion order here, yielding (bool, ark_bls12_381::Fr).
    let mut fields: Ctx<String, ATyp> = Ctx::new();
    fields.insert(&"ok".to_string(), &ATyp::Base(ABase::Bool));
    fields.insert(&"s".to_string(), &ATyp::Base(ABase::Scalar));
    let record_typ = ATyp::Record(fields);
    assert_eq!(
        compiler::testing::render_type(&record_typ, &opts).unwrap(),
        "(bool, ark_bls12_381::Fr)"
    );
}

#[test]
fn record_iteration_is_key_sorted_not_insertion_order() {
    let opts = opts();

    // Insert "z" before "a"; key-sorted order produces "a" first, then "z",
    // so the Rust tuple should be (ark_bls12_381::Fr, bool).
    let mut fields: Ctx<String, ATyp> = Ctx::new();
    fields.insert(&"z".to_string(), &ATyp::Base(ABase::Bool));
    fields.insert(&"a".to_string(), &ATyp::Base(ABase::Scalar));
    let record_typ = ATyp::Record(fields);
    assert_eq!(
        compiler::testing::render_type(&record_typ, &opts).unwrap(),
        "(ark_bls12_381::Fr, bool)"
    );
}

#[test]
fn record_empty_renders_unit_tuple() {
    let opts = opts();
    let empty: Ctx<String, ATyp> = Ctx::new();
    assert_eq!(
        compiler::testing::render_type(&ATyp::Record(empty), &opts).unwrap(),
        "()"
    );
}

#[test]
fn record_single_field_renders_one_element_tuple() {
    let opts = opts();
    let mut fields: Ctx<String, ATyp> = Ctx::new();
    fields.insert(&"x".to_string(), &ATyp::Base(ABase::Scalar));
    assert_eq!(
        compiler::testing::render_type(&ATyp::Record(fields), &opts).unwrap(),
        "(ark_bls12_381::Fr,)"
    );
}

#[test]
fn maps_nested_vec_of_records() {
    let opts = opts();

    // Vec<(bool, ark_bls12_381::Fr)>
    let mut fields: Ctx<String, ATyp> = Ctx::new();
    fields.insert(&"b".to_string(), &ATyp::Base(ABase::Bool));
    fields.insert(&"s".to_string(), &ATyp::Base(ABase::Scalar));
    let record_typ = ATyp::Record(fields);
    let nested = ATyp::Vec(Box::new(record_typ), 2);
    assert_eq!(
        compiler::testing::render_type(&nested, &opts).unwrap(),
        "Vec<(bool, ark_bls12_381::Fr)>"
    );
}

#[test]
fn rejects_fin_until_index_codegen_is_added() {
    let opts = opts();
    let fin_typ = ATyp::Base(ABase::Fin(CRange::new(0, 4)));
    let err = compiler::testing::render_type(&fin_typ, &opts).unwrap_err();

    assert!(
        matches!(err, CompilerError::UnsupportedType { .. }),
        "expected UnsupportedType, got {err:?}"
    );
    assert!(
        err.to_string().contains("Fin"),
        "error message should mention Fin, got: {err}"
    );
}

#[test]
fn rejects_polynomial_types() {
    let opts = opts();

    for typ in [ATyp::Uni(4), ATyp::Mle(3), ATyp::VPoly(2, 3)] {
        let err = compiler::testing::render_type(&typ, &opts).unwrap_err();
        assert!(
            matches!(err, CompilerError::UnsupportedType { .. }),
            "expected UnsupportedType for {typ:?}, got {err:?}"
        );
    }
}

#[test]
fn render_type_at_node_propagates_node_id_in_error() {
    let opts = opts();
    let fin_typ = ATyp::Base(ABase::Fin(CRange::new(0, 4)));

    // Use a non-zero node to verify the id is threaded through correctly.
    let err = compiler::testing::render_type_at_node(&fin_typ, &opts, 42).unwrap_err();

    match err {
        CompilerError::UnsupportedType { node, .. } => {
            assert_eq!(node, 42, "node id must be propagated verbatim");
        }
        other => panic!("expected UnsupportedType, got {other:?}"),
    }
}

#[test]
fn verifier_options_render_same_base_types() {
    // CodegenOptions::verifier() shares the same RustTarget as prover(); the
    // rendered type strings must be identical regardless of codegen mode.
    let prover_opts = CodegenOptions::prover();
    let verifier_opts = CodegenOptions::verifier();

    for typ in [ATyp::Base(ABase::Scalar), ATyp::Base(ABase::G1)] {
        assert_eq!(
            compiler::testing::render_type(&typ, &prover_opts).unwrap(),
            compiler::testing::render_type(&typ, &verifier_opts).unwrap(),
            "prover and verifier must render {typ:?} identically"
        );
    }
}

#[test]
fn maps_vec_of_vec_scalar() {
    let opts = opts();
    // Vec<Vec<Scalar>> - recursive rendering must compose correctly.
    let inner = ATyp::Vec(Box::new(ATyp::Base(ABase::Scalar)), 4);
    let outer = ATyp::Vec(Box::new(inner), 3);
    assert_eq!(
        compiler::testing::render_type(&outer, &opts).unwrap(),
        "Vec<Vec<ark_bls12_381::Fr>>"
    );
}
