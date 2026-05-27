//! TDD tests for binary operation lowering (Pow, Concat, Div, Rem, Dot).

use backend::{
    ArkBls12_381 as TestConfig,
    op::{GOp, mk},
    types::ATyp,
};
use graph::{ArgKind, Dag, Node};
use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::{CRange, Distribution, Nothing, Qualifier};

use compiler::compile_prover;

/// Helper: build minimal prover DAG with single binary operation.
fn build_binary_op_dag(op: BinOp, left_typ: ATyp, right_typ: ATyp) -> Dag<TestConfig, Nothing> {
    let mut dag = Dag::new();

    // Create input argument nodes for operands
    let left_id = dag.add_node(Node::Arg(
        Vid::new("left"),
        left_typ.clone(),
        Qualifier::Private,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    let right_id = dag.add_node(Node::Arg(
        Vid::new("right"),
        right_typ.clone(),
        Qualifier::Private,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    // Determine result type
    let result_typ = match op {
        BinOp::Pow => left_typ.clone(), // result type same as base
        BinOp::Concat => {
            // Concat result is Vec with left's element type
            match &left_typ {
                ATyp::Vec(elem, _) => ATyp::Vec(elem.clone(), 0), // size unknown
                _ if matches!(&right_typ, ATyp::Vec(_, _)) => right_typ.clone(),
                _ => unimplemented!("Concat type for {:?} ++ {:?}", left_typ, right_typ),
            }
        }
        BinOp::Div => left_typ.clone(), // result type same as dividend
        BinOp::Rem => left_typ.clone(), // result type same as dividend
        BinOp::Dot => {
            // Dot result type depends on right operand:
            // Vec<Scalar> · Vec<Scalar> → Scalar (inner product)
            // Vec<Scalar> · Vec<G1> → G1 (MSM)
            // Vec<Scalar> · Vec<G2> → G2 (MSM)
            match &right_typ {
                ATyp::Vec(elem, _) => (**elem).clone(),
                _ => unimplemented!("Dot type for {:?} · {:?}", left_typ, right_typ),
            }
        }
        _ => unimplemented!("Type for {:?} not implemented", op),
    };

    // Create binary operation using GOp::bin helper
    let bin_op = mk(GOp::bin(
        op,
        GOp::underscore(left_id, left_typ),
        GOp::underscore(right_id, right_typ),
        result_typ.clone(),
    ));

    // Add transcript output
    dag.add_node(Node::Transcr(bin_op, Nothing));

    dag
}

#[test]
fn prover_lowers_scalar_pow_index() {
    // RED: Write failing test for Scalar^Index
    let dag = build_binary_op_dag(
        BinOp::Pow,
        ATyp::scalar(),
        ATyp::fin(CRange::new(0, 10)), // Index type with range [0,10)
    );

    let mut output = Vec::new();

    // This should fail with UnsupportedOp until we implement Pow
    let result = compile_prover(&dag, &mut output);

    // Once implemented, this assertion will pass:
    assert!(
        result.is_ok(),
        "Expected Pow lowering to succeed, got: {:?}",
        result.err()
    );

    let generated = String::from_utf8(output).unwrap();

    // Verify generated code contains power operation
    assert!(
        generated.contains(".pow("),
        "Expected generated code to contain .pow( call, got:\n{}",
        generated
    );
}

#[test]
fn prover_lowers_index_pow_index() {
    // RED: Write failing test for Index^Index
    let dag = build_binary_op_dag(
        BinOp::Pow,
        ATyp::fin(CRange::new(0, 100)), // Index base
        ATyp::fin(CRange::new(0, 10)),  // Index exponent
    );

    let mut output = Vec::new();

    let result = compile_prover(&dag, &mut output);
    assert!(
        result.is_ok(),
        "Expected Pow lowering to succeed, got: {:?}",
        result.err()
    );

    let generated = String::from_utf8(output).unwrap();

    // Verify generated code uses pow_usize helper
    assert!(
        generated.contains("pow_usize"),
        "Expected generated code to contain pow_usize helper, got:\n{}",
        generated
    );
}

#[test]
fn prover_lowers_vec_scalar_pow_index() {
    // RED: Write failing test for Vec<Scalar>^Index (elementwise)
    let dag = build_binary_op_dag(
        BinOp::Pow,
        ATyp::vec_scalar(5),           // Vec<Scalar>
        ATyp::fin(CRange::new(0, 10)), // Index exponent
    );

    let mut output = Vec::new();

    let result = compile_prover(&dag, &mut output);
    assert!(
        result.is_ok(),
        "Expected Pow lowering to succeed, got: {:?}",
        result.err()
    );

    let generated = String::from_utf8(output).unwrap();

    // Verify generated code does elementwise power
    assert!(
        generated.contains("par_iter") || generated.contains("iter"),
        "Expected generated code to iterate over vector, got:\n{}",
        generated
    );
    assert!(
        generated.contains(".pow("),
        "Expected generated code to use pow on elements, got:\n{}",
        generated
    );
}

// === Concat Tests ===

#[test]
fn prover_lowers_vec_concat_vec() {
    // RED: Write failing test for Vec<Scalar> ++ Vec<Scalar>
    let dag = build_binary_op_dag(
        BinOp::Concat,
        ATyp::vec_scalar(3), // Vec<Scalar, 3>
        ATyp::vec_scalar(2), // Vec<Scalar, 2>
    );

    let mut output = Vec::new();

    let result = compile_prover(&dag, &mut output);
    assert!(
        result.is_ok(),
        "Expected Concat lowering to succeed, got: {:?}",
        result.err()
    );

    let generated = String::from_utf8(output).unwrap();

    // Verify generated code uses concat or chain+collect
    assert!(
        generated.contains("concat") || generated.contains("chain") || generated.contains("extend"),
        "Expected generated code to contain vector concatenation, got:\n{}",
        generated
    );
}

// === Div Tests ===

#[test]
fn prover_lowers_scalar_div_scalar() {
    // RED: Write failing test for Scalar / Scalar
    let dag = build_binary_op_dag(BinOp::Div, ATyp::scalar(), ATyp::scalar());

    let mut output = Vec::new();

    let result = compile_prover(&dag, &mut output);
    assert!(
        result.is_ok(),
        "Expected Div lowering to succeed, got: {:?}",
        result.err()
    );

    let generated = String::from_utf8(output).unwrap();

    // Verify generated code uses inverse for division
    assert!(
        generated.contains("inverse") || generated.contains("inv"),
        "Expected generated code to use field inversion, got:\n{}",
        generated
    );
}

// === Rem Tests ===

#[test]
fn prover_lowers_index_rem_index() {
    // RED: Write failing test for Index % Index
    let dag = build_binary_op_dag(
        BinOp::Rem,
        ATyp::fin(CRange::new(0, 100)), // Index dividend
        ATyp::fin(CRange::new(1, 10)),  // Index divisor (non-zero)
    );

    let mut output = Vec::new();

    let result = compile_prover(&dag, &mut output);
    assert!(
        result.is_ok(),
        "Expected Rem lowering to succeed, got: {:?}",
        result.err()
    );

    let generated = String::from_utf8(output).unwrap();

    // Verify generated code uses modulo operator
    assert!(
        generated.contains('%'),
        "Expected generated code to use modulo operator, got:\n{}",
        generated
    );
}

#[test]
fn prover_lowers_vec_scalar_dot_vec_scalar() {
    // RED: Test Vec<Scalar> · Vec<Scalar> → Scalar (scalar inner product)
    let dag = build_binary_op_dag(BinOp::Dot, ATyp::vec_scalar(3), ATyp::vec_scalar(3));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    // Should use scalar inner product implementation
    // Looking for parallel zip + reduce pattern
    assert!(prover_code.contains("par_iter"));
    assert!(prover_code.contains("zip"));
}

#[test]
fn prover_lowers_vec_scalar_dot_vec_g1() {
    // RED: Test Vec<Scalar> · Vec<G1> → G1 (MSM G1)
    let dag = build_binary_op_dag(BinOp::Dot, ATyp::vec_scalar(5), ATyp::vec_g1(5));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    // Should use msm_g1 shallow wrapper
    assert!(
        prover_code.contains("msm_g1"),
        "Expected msm_g1 wrapper call"
    );
    assert!(
        prover_code.contains("into_affine"),
        "Expected affine conversion"
    );
}

#[test]
fn prover_lowers_vec_scalar_dot_vec_g2() {
    // RED: Test Vec<Scalar> · Vec<G2> → G2 (MSM G2)
    let dag = build_binary_op_dag(BinOp::Dot, ATyp::vec_scalar(5), ATyp::vec_g2(5));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    // Should use msm_g2 shallow wrapper
    assert!(
        prover_code.contains("msm_g2"),
        "Expected msm_g2 wrapper call"
    );
    assert!(
        prover_code.contains("into_affine"),
        "Expected affine conversion"
    );
}
