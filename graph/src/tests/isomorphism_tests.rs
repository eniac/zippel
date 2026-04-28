use crate::tests::test_helpers::{GraphBuilder, TestConfig};
use crate::{GOp, UDag};
use backend::{ABase, ATyp};
use lang::ast::BinOp;

/// Build a simple graph: input(x, y) → add(x, y)
fn make_add_graph() -> UDag<TestConfig> {
    let mut builder: GraphBuilder<TestConfig> = GraphBuilder::new();
    let x = builder.add_input("x", ATyp::scalar());
    let y = builder.add_input("y", ATyp::scalar());
    let _sum = builder.add_op(GOp::bin(
        BinOp::Add,
        GOp::Ref(x, ATyp::scalar()),
        GOp::Ref(y, ATyp::scalar()),
        ATyp::scalar(),
    ));
    builder.build()
}

/// Build a simple graph: input(x, y) → mul(x, y)
fn make_mul_graph() -> UDag<TestConfig> {
    let mut builder: GraphBuilder<TestConfig> = GraphBuilder::new();
    let x = builder.add_input("x", ATyp::scalar());
    let y = builder.add_input("y", ATyp::scalar());
    let _prod = builder.add_op(GOp::bin(
        BinOp::Mul,
        GOp::Ref(x, ATyp::scalar()),
        GOp::Ref(y, ATyp::scalar()),
        ATyp::scalar(),
    ));
    builder.build()
}

/// Build a chain: input(x) → add(x, x) → mul(result, result)
fn make_chain_graph() -> UDag<TestConfig> {
    let mut builder: GraphBuilder<TestConfig> = GraphBuilder::new();
    let x = builder.add_input("x", ATyp::scalar());
    let sum = builder.add_op(GOp::bin(
        BinOp::Add,
        GOp::Ref(x.clone(), ATyp::scalar()),
        GOp::Ref(x, ATyp::scalar()),
        ATyp::scalar(),
    ));
    let _prod = builder.add_op(GOp::bin(
        BinOp::Mul,
        GOp::Ref(sum.clone(), ATyp::scalar()),
        GOp::Ref(sum, ATyp::scalar()),
        ATyp::scalar(),
    ));
    builder.build()
}

#[test]
fn test_empty_graphs_are_equal() {
    let g1: UDag<TestConfig> = UDag::new();
    let g2: UDag<TestConfig> = UDag::new();
    assert!(g1 == g2);
}

#[test]
fn test_graph_equals_itself() {
    let g = make_add_graph();
    assert!(g == g);
}

#[test]
fn test_clone_is_equal() {
    let g1 = make_add_graph();
    let g2 = g1.clone();
    assert!(g1 == g2);
}

#[test]
fn test_identical_builds_are_equal() {
    let g1 = make_add_graph();
    let g2 = make_add_graph();
    assert!(g1 == g2);
}

#[test]
fn test_different_operations_not_equal() {
    let g_add = make_add_graph();
    let g_mul = make_mul_graph();
    assert!(g_add != g_mul);
}

#[test]
fn test_different_topology_not_equal() {
    let g_simple = make_add_graph();
    let g_chain = make_chain_graph();
    assert!(g_simple != g_chain);
}

#[test]
fn test_different_variable_names_not_equal() {
    let g1 = make_add_graph(); // uses x, y

    // Build same structure with different variable names
    let mut builder: GraphBuilder<TestConfig> = GraphBuilder::new();
    let a = builder.add_input("a", ATyp::scalar());
    let b = builder.add_input("b", ATyp::scalar());
    let _sum = builder.add_op(GOp::bin(
        BinOp::Add,
        GOp::Ref(a, ATyp::scalar()),
        GOp::Ref(b, ATyp::scalar()),
        ATyp::scalar(),
    ));
    let g2 = builder.build();

    assert!(g1 != g2);
}

#[test]
fn test_chain_equals_itself() {
    let g1 = make_chain_graph();
    let g2 = make_chain_graph();
    assert!(g1 == g2);
}

#[test]
fn test_empty_vs_nonempty_not_equal() {
    let empty: UDag<TestConfig> = UDag::new();
    let nonempty = make_add_graph();
    assert!(empty != nonempty);
}

#[test]
fn test_different_types_not_equal() {
    let g1 = make_add_graph();

    let group_typ = ATyp::Base(ABase::G1);
    let mut builder: GraphBuilder<TestConfig> = GraphBuilder::new();
    let x = builder.add_input("x", group_typ.clone());
    let y = builder.add_input("y", group_typ.clone());
    let _sum = builder.add_op(GOp::bin(
        BinOp::Add,
        GOp::Ref(x, group_typ.clone()),
        GOp::Ref(y, group_typ.clone()),
        group_typ,
    ));
    let g2 = builder.build();

    assert!(g1 != g2);
}
