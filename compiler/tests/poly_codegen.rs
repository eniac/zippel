//! TDD tests for polynomial operation lowering (Poly construction, Coef extraction).

use backend::{
    ArkBls12_381 as TestConfig,
    op::{GOp, mk},
    types::ATyp,
};
use graph::{ArgKind, Dag, Node};
use lang::id::Vid;
use lang::typ::{Distribution, Nothing, Qualifier};

use compiler::compile_prover;

#[test]
fn prover_lowers_poly_construction() {
    // RED: Test Vec<Scalar> → Uni (polynomial construction)
    // This is almost a no-op in compiled code since both are Vec<Fr>

    let mut dag = Dag::<TestConfig, Nothing>::new();

    let coeffs_typ = ATyp::vec_scalar(5); // Vec<Scalar, 5>

    // Add input node
    let coeffs_id = dag.add_node(Node::Arg(
        Vid::new("coeffs"),
        coeffs_typ.clone(),
        Qualifier::Public,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    // Poly operation: wrap Vec as polynomial
    // GOp::poly computes result type (Uni) from input type automatically
    let poly_op = mk(GOp::poly(GOp::underscore(coeffs_id, coeffs_typ)));

    // Add transcript output
    dag.add_node(Node::Transcr(poly_op, Nothing));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    // Poly is essentially a no-op in compiled code (both Vec<Fr>)
    // Should just reference the input variable or clone it
    assert!(
        prover_code.contains("coeffs"),
        "Expected poly construction to reference input: {}",
        prover_code
    );
}

#[test]
fn prover_lowers_coef_extraction() {
    // RED: Test Uni → Vec<Scalar> (coefficient extraction)
    // This is the inverse of Poly, also almost a no-op

    let mut dag = Dag::<TestConfig, Nothing>::new();

    let poly_typ = ATyp::uni(4); // Uni(4) = polynomial of degree 4 (5 coefficients)

    // Add input node
    let poly_id = dag.add_node(Node::Arg(
        Vid::new("poly"),
        poly_typ.clone(),
        Qualifier::Public,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    // Coef operation: extract coefficients from polynomial
    // GOp::coef computes result type (Vec<Scalar>) from input type automatically
    let coef_op = mk(GOp::coef(GOp::underscore(poly_id, poly_typ)));

    // Add transcript output
    dag.add_node(Node::Transcr(coef_op, Nothing));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    // Coef is essentially a no-op in compiled code (both Vec<Fr>)
    // Should just reference the input variable or clone it
    assert!(
        prover_code.contains("poly"),
        "Expected coef extraction to reference input: {}",
        prover_code
    );
}
