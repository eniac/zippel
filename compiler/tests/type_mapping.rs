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

    // Record: ok -> Bool, s -> Scalar  (insertion order preserved)
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
