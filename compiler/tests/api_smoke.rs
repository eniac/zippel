use compiler::{CodegenMode, CodegenOptions, CompilerError, RustTarget};

#[test]
fn default_options_target_bls12_381_and_prover() {
    let options = CodegenOptions::default();

    assert_eq!(options.mode, CodegenMode::Prover);
    assert_eq!(options.target, RustTarget::ark_bls12_381());
    assert_eq!(options.session, "examples/schnorr/schnorr.zippel");
    assert_eq!(options.proof_type_path, "crate::prover::Proof");
}

#[test]
fn unsupported_op_error_names_node_and_operation() {
    let err = CompilerError::UnsupportedOp {
        node: 9,
        op: "Ram".to_string(),
    };

    let message = err.to_string();
    assert!(message.contains("node 9"), "{message}");
    assert!(message.contains("Ram"), "{message}");
}
