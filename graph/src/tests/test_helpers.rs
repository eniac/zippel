use crate::dep::Dep;
use crate::node::ArgKind;
/// Test helpers for graph operations testing
///
/// This module provides utilities for building graphs to test their
/// structure; `runtime` executes lowered graphs in its own tests.
use crate::{GOp, Node, Ref, UDag, mk};
use backend::op::HasOpFactory;
use backend::{ATyp, ArkBls12_381, ArkConfig, ArkScalarOps, Value};
use lang::ast::{CModule, UModule};
use lang::id::{Tid, Vid};
use lang::typ::{Distribution, Nothing, Qualifier};
use petgraph::graph::NodeIndex;
use share::Ctx;

/// Type alias for test configuration (BLS12-381 curve)
pub type TestConfig = ArkBls12_381;

/// Parse source text and concretize with the given sizes.
/// Panics on parse or concretize errors (test-only).
#[track_caller]
pub fn parse_and_concretize(src: &str, sizes: &Ctx<Tid, usize>) -> CModule {
    let (module, diags) = UModule::parse(src);
    let errors: Vec<_> = diags
        .iter()
        // E0001 (NoProtoDeclaration) is a file-structure rule, not relevant
        // to unit tests using fn-only sources. Suppress by error code.
        .filter(|d| {
            d.severity == lang::diagnostic::Severity::Error && d.code.as_deref() != Some("E0001")
        })
        .collect();
    assert!(
        errors.is_empty(),
        "unexpected errors parsing test source:\n{}",
        errors
            .iter()
            .map(|d| d.summary.clone())
            .collect::<Vec<_>>()
            .join("\n")
    );
    module
        .expect("parse returned no module but no errors")
        .concretize(sizes)
        .expect("concretize failed")
}

/// Helper to create a simple DAG for testing operations
pub struct GraphBuilder<C: ArkConfig> {
    dag: UDag<C>,
    input_node: NodeIndex,
}

impl<C: HasOpFactory> GraphBuilder<C> {
    /// Create a new graph builder with an input node
    pub fn new() -> Self {
        let mut dag = UDag::new();
        let input_node = dag.add_node(Node::Inp(Vid::from("inputs")), 0..0);
        GraphBuilder { dag, input_node }
    }

    /// Add a variable input as an `Arg` node connected to the input marker.
    pub fn add_input(&mut self, name: &str, typ: ATyp) -> Ref {
        let vid = Vid::from(name);
        let arg = self.dag.add_node(
            Node::Arg(
                vid,
                typ,
                Qualifier::Witness,
                Distribution::Nonuniform,
                ArgKind::Input,
            ),
            0..0,
        );
        self.dag.add_edge(self.input_node, arg, Dep::data());
        Ref(arg)
    }

    /// Add an operation node to the graph
    pub fn add_op(&mut self, op: GOp<C>) -> Ref {
        use crate::DepType;
        let hop = mk::<C>(op.clone());
        let node = self.dag.add_node(Node::Op(hop, Nothing), 0..0);
        // Add edges from dependencies to this node
        self.dag.add_edges(DepType::Data, node, op);
        Ref(node)
    }

    /// Build and return the DAG
    pub fn build(self) -> UDag<C> {
        self.dag
    }
}

/// Create a scalar field value for testing
pub fn scalar<C: ArkConfig>(n: u64) -> Value<C> {
    Value::Scalar(C::FOps::from_usize(n as usize))
}

/// Create a zero scalar
pub fn zero_scalar<C: ArkConfig>() -> Value<C> {
    Value::Scalar(C::FOps::zero())
}

/// Create a one scalar
pub fn one_scalar<C: ArkConfig>() -> Value<C> {
    Value::Scalar(C::FOps::one())
}

/// Compare two values for equality (within epsilon for floating point)
pub fn values_equal<C: ArkConfig>(a: &Value<C>, b: &Value<C>) -> bool {
    match (a, b) {
        (Value::Scalar(a), Value::Scalar(b)) => a == b,
        (Value::G1(a), Value::G1(b)) => a == b,
        (Value::G2(a), Value::G2(b)) => a == b,
        (Value::GT(a), Value::GT(b)) => a == b,
        (Value::VecScalar(a), Value::VecScalar(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
        }
        (Value::VecG1(a), Value::VecG1(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
        }
        (Value::VecG2(a), Value::VecG2(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
        }
        (Value::VecGT(a), Value::VecGT(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
        }
        (Value::Vec(a), Value::Vec(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        _ => false,
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_graph_builder_basic() {
        let mut builder = GraphBuilder::<TestConfig>::new();
        let _a_ref = builder.add_input("a", ATyp::scalar());
        let _b_ref = builder.add_input("b", ATyp::scalar());

        let dag = builder.build();
        // 1 Inp node + 2 Arg nodes (one per input)
        assert_eq!(dag.node_count(), 3);
    }

    #[test]
    fn test_scalar_creation() {
        let s: Value<TestConfig> = scalar(42);
        let zero: Value<TestConfig> = zero_scalar();
        let one: Value<TestConfig> = one_scalar();

        assert!(!values_equal(&s, &zero));
        assert!(!values_equal(&s, &one));
    }
}
