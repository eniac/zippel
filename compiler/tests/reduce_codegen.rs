//! TDD tests for vector reduction operation lowering (sum, product, and).

use backend::{
    ArkBls12_381 as TestConfig,
    op::{GOp, mk},
    types::ATyp,
};
use graph::{ArgKind, Dag, Node};
use lang::ast::BinOp;
use lang::id::Vid;
use lang::typ::{Distribution, Nothing, Qualifier, Range};

use compiler::compile_prover;

#[test]
fn prover_lowers_reduce_add() {
    // RED: Test Vec<Scalar> → Scalar via sum reduction
    // Should emit: reduce_add_scalar(&vec)

    let mut dag = Dag::<TestConfig, Nothing>::new();

    let vec_typ = ATyp::vec_scalar(10); // Vec<Scalar, 10>

    // Add input node
    let vec_id = dag.add_node(Node::Arg(
        Vid::new("values"),
        vec_typ.clone(),
        Qualifier::Public,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    // Reduce operation: sum all elements
    let reduce_op = mk(GOp::reduce(BinOp::Add, GOp::underscore(vec_id, vec_typ)));

    // Add transcript output
    dag.add_node(Node::Transcr(reduce_op, Nothing));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    // Should call reduce_add_scalar wrapper
    assert!(
        prover_code.contains("reduce_add_scalar"),
        "Expected reduce_add_scalar call, got: {}",
        prover_code
    );
    assert!(
        prover_code.contains("values"),
        "Expected reference to input vector: {}",
        prover_code
    );
}

#[test]
fn prover_lowers_reduce_mul() {
    // RED: Test Vec<Scalar> → Scalar via product reduction
    // Should emit: reduce_mul_scalar(&vec)

    let mut dag = Dag::<TestConfig, Nothing>::new();

    let vec_typ = ATyp::vec_scalar(5);

    let vec_id = dag.add_node(Node::Arg(
        Vid::new("factors"),
        vec_typ.clone(),
        Qualifier::Public,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    let reduce_op = mk(GOp::reduce(BinOp::Mul, GOp::underscore(vec_id, vec_typ)));

    dag.add_node(Node::Transcr(reduce_op, Nothing));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    assert!(
        prover_code.contains("reduce_mul_scalar"),
        "Expected reduce_mul_scalar call, got: {}",
        prover_code
    );
}

#[test]
fn prover_lowers_reduce_and() {
    // RED: Test Vec<Bool> → Bool via and reduction
    // Should emit: reduce_and_bool(&vec)

    let mut dag = Dag::<TestConfig, Nothing>::new();

    let vec_typ = ATyp::vec_bool(8);

    let vec_id = dag.add_node(Node::Arg(
        Vid::new("flags"),
        vec_typ.clone(),
        Qualifier::Public,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    let reduce_op = mk(GOp::reduce(BinOp::And, GOp::underscore(vec_id, vec_typ)));

    dag.add_node(Node::Transcr(reduce_op, Nothing));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    assert!(
        prover_code.contains("reduce_and_bool"),
        "Expected reduce_and_bool call, got: {}",
        prover_code
    );
}

#[test]
fn prover_lowers_reduce_index() {
    // RED: Test Vec<Index> → Index via sum reduction
    // Should emit: reduce_add_index(&vec)

    let mut dag = Dag::<TestConfig, Nothing>::new();

    // Use vec_fin for index vectors with Range<usize>
    let vec_typ = ATyp::vec_fin(Range::new(0, 10), 6);

    let vec_id = dag.add_node(Node::Arg(
        Vid::new("indices"),
        vec_typ.clone(),
        Qualifier::Public,
        Distribution::Uniform,
        ArgKind::Input,
    ));

    let reduce_op = mk(GOp::reduce(BinOp::Add, GOp::underscore(vec_id, vec_typ)));

    dag.add_node(Node::Transcr(reduce_op, Nothing));

    let mut output = Vec::new();
    compile_prover(&dag, &mut output).expect("compilation should succeed");
    let prover_code = String::from_utf8(output).expect("valid UTF-8");

    assert!(
        prover_code.contains("reduce_add_index"),
        "Expected reduce_add_index call, got: {}",
        prover_code
    );
}
