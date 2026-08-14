use crate::dep::Dep;
use crate::eval::eval_op;
use crate::node::ArgKind;
/// Test helpers for graph operations testing
///
/// This module provides utilities for creating and executing graphs
/// to test algebraic properties and semantic correctness.
use crate::{GOp, Node, Op, Ref, UDag, mk};
use backend::op::HasOpFactory;
use backend::{ATyp, ArkBls12_381, ArkConfig, ArkScalarOps, Value};
use lang::ast::{CModule, UModule};
use lang::id::{Tid, Vid};
use lang::typ::{Distribution, Nothing, Qualifier};
use petgraph::graph::NodeIndex;
use rand::rngs::ThreadRng;
use share::Ctx;
use std::collections::HashMap;
use std::sync::Arc;

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
        let input_node = dag.add_node(Node::Inp(Vid::from("inputs")));
        GraphBuilder { dag, input_node }
    }

    /// Add a variable input as an `Arg` node connected to the input marker.
    pub fn add_input(&mut self, name: &str, typ: ATyp) -> Ref {
        let vid = Vid::from(name);
        let arg = self.dag.add_node(Node::Arg(
            vid,
            typ,
            Qualifier::Witness,
            Distribution::Nonuniform,
            ArgKind::Input,
        ));
        self.dag.add_edge(self.input_node, arg, Dep::data());
        Ref(arg)
    }

    /// Add an operation node to the graph
    pub fn add_op(&mut self, op: GOp<C>) -> Ref {
        use crate::DepType;
        let hop = mk::<C>(op.clone());
        let node = self.dag.add_node(Node::Op(hop, Nothing));
        // Add edges from dependencies to this node
        self.dag.add_edges(DepType::Data, node, op);
        Ref(node)
    }

    /// Build and return the DAG
    pub fn build(self) -> UDag<C> {
        self.dag
    }
}

/// Execute a graph with given inputs and return the value computed by the
/// last visited Op/Transcr node in topological order.
///
/// Walks the DAG topologically and routes each Op/Transcr node through
/// the canonical `graph::eval::eval_op` — the same dispatcher the runtime
/// uses for per-node value computation.
#[track_caller]
pub fn execute_graph<C: ArkConfig>(dag: &UDag<C>, inputs: Ctx<Vid, Value<C>>) -> Option<Value<C>> {
    let (_computed, last) = execute_graph_inner(dag, inputs);
    last
}

/// Execute a graph with given inputs and return all computed node values.
/// Useful for inspecting individual node results (e.g. multiple Check nodes).
#[track_caller]
pub fn execute_graph_all<C: ArkConfig>(
    dag: &UDag<C>,
    inputs: Ctx<Vid, Value<C>>,
) -> HashMap<NodeIndex, Value<C>> {
    let (computed, _last) = execute_graph_inner(dag, inputs);
    computed
}

/// Shared implementation for `execute_graph` / `execute_graph_all`.
///
/// Pre-populates the `Ref` → `Value<C>` env with input bindings for each
/// `Node::Arg`, then walks the DAG in topological order and calls
/// `eval_op` on every Op/Transcr node, inserting each result into the env
/// keyed by `Ref(node_idx)`. Returns both the populated NodeIndex→Value
/// map (used by `execute_graph_all`) and the last computed value (used by
/// `execute_graph`).
#[track_caller]
fn execute_graph_inner<C: ArkConfig>(
    dag: &UDag<C>,
    inputs: Ctx<Vid, Value<C>>,
) -> (HashMap<NodeIndex, Value<C>>, Option<Value<C>>) {
    use petgraph::visit::Topo;

    let graph = dag.inner_graph();
    let mut env: HashMap<Ref, Arc<Value<C>>> = HashMap::new();
    let mut computed: HashMap<NodeIndex, Value<C>> = HashMap::new();

    // Pre-populate env with input bindings: every Arg node referenced from
    // an Op gets resolved through `inputs[vid]`.
    for node_idx in graph.node_indices() {
        if let Node::Arg(vid, _, _, _, _) = &dag[node_idx]
            && let Some(val) = inputs.get(vid)
        {
            env.insert(Ref(node_idx), Arc::new(val.clone()));
        }
    }

    let mut rng = ThreadRng::default();
    let mut topo = Topo::new(graph);
    let mut last_op_value = None;

    while let Some(node_idx) = topo.next(graph) {
        match &dag[node_idx] {
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => {}
            Node::Op(op, _) | Node::Transcr(op, _) => {
                let mut check_sink = Vec::new();
                let value_arc = eval_op(op, &env, &mut rng, &mut check_sink)
                    .expect("execute_graph: eval_op should not fail on a well-formed DAG");
                env.insert(Ref(node_idx), Arc::clone(&value_arc));
                computed.insert(node_idx, (*value_arc).clone());
                last_op_value = Some((*value_arc).clone());
            }
        }
    }

    (computed, last_op_value)
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

/// Create test inputs context
pub fn test_inputs<C: ArkConfig>() -> Ctx<Vid, Value<C>> {
    Ctx::new()
}

/// Add a scalar input to context
pub fn add_scalar_input<C: ArkConfig>(ctx: &mut Ctx<Vid, Value<C>>, name: &str, value: u64) {
    ctx.insert(&Vid::from(name), &scalar(value));
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

    #[test]
    fn test_execute_simple_addition() {
        let mut builder = GraphBuilder::<TestConfig>::new();
        let a_ref = builder.add_input("a", ATyp::scalar());
        let b_ref = builder.add_input("b", ATyp::scalar());

        let add_op = Op::add(
            Op::Ref(a_ref, ATyp::scalar()),
            Op::Ref(b_ref, ATyp::scalar()),
            ATyp::scalar(),
        );
        builder.add_op(add_op);

        let dag = builder.build();

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 3);
        add_scalar_input(&mut inputs, "b", 4);

        let result = execute_graph(&dag, inputs);
        assert!(result.is_some());

        let expected: Value<TestConfig> = scalar(7);
        assert!(values_equal(&result.unwrap(), &expected));
    }

    #[test]
    fn test_proj_op() {
        let mut builder = GraphBuilder::<TestConfig>::new();
        let mut fields = Ctx::new();
        fields.insert(&"x".to_string(), &mk(Op::Value(scalar::<TestConfig>(7))));
        fields.insert(&"y".to_string(), &mk(Op::Value(scalar::<TestConfig>(9))));
        let rec = Op::Record(fields);
        let proj_x = Op::Proj(mk(rec), "x".to_string(), ATyp::scalar());
        builder.add_op(proj_x);

        let dag = builder.build();
        let result = execute_graph(&dag, test_inputs()).expect("expected projection result");
        assert!(values_equal(&result, &scalar::<TestConfig>(7)));
    }

    #[test]
    fn test_execute_multiple_checks() {
        use crate::UDags;
        use share::Ctx;

        // Protocol with two separate verify statements → two Check nodes
        let src = r#"
            proto two_checks<F: Field>(instance x: F, instance y: F) where 1 == 1 {
                verify(x == x);
                verify(y == y)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_verify();
        assert_eq!(
            checks.len(),
            2,
            "Protocol with two verify statements should have two check nodes"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 5);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // Verify both check nodes produce Unit (Check always returns Unit)
        for (i, &check_idx) in checks.iter().enumerate() {
            match computed.get(&check_idx) {
                Some(Value::Unit) => {}
                Some(v) => panic!("Check node {} produced {:?}, expected Unit", i, v),
                None => panic!("Check node {} was not computed", i),
            }
        }
    }

    #[test]
    fn test_execute_scattered_checks() {
        use crate::UDags;
        use share::Ctx;

        // Protocol with scattered verify statements throughout the body
        let src = r#"
            proto scattered<F: Field>(instance x: F, instance y: F) where 1 == 1 {
                a <- x + y;
                verify(a == a);
                b <- a + x;
                verify(b == b)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_verify();
        assert_eq!(
            checks.len(),
            2,
            "Scattered verify statements should produce 2 check nodes"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 3);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // Verify all check nodes produce Unit (Check always returns Unit)
        for (i, &check_idx) in checks.iter().enumerate() {
            match computed.get(&check_idx) {
                Some(Value::Unit) => {}
                Some(v) => panic!("Check node {} produced {:?}, expected Unit", i, v),
                None => panic!("Check node {} was not computed", i),
            }
        }
    }

    #[test]
    fn test_execute_checks_negative_second_fails() {
        use crate::UDags;
        use share::Ctx;

        // Second verify has a false condition (x != y)
        let src = r#"
            proto neg<F: Field>(instance x: F, instance y: F) where 1 == 1 {
                verify(x == x);
                verify(x == y)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_verify();
        assert_eq!(checks.len(), 2, "Should have 2 check nodes");

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 3);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // The second check should produce Unit (Check always returns Unit)
        match computed.get(&checks[1]) {
            Some(Value::Unit) => {}
            Some(v) => panic!("Second check node produced {:?}, expected Unit", v),
            None => panic!("Second check node was not computed"),
        }
    }

    #[test]
    fn test_execute_checks_negative_first_fails() {
        use crate::UDags;
        use share::Ctx;

        // First verify has a false condition (x != y)
        let src = r#"
            proto neg2<F: Field>(instance x: F, instance y: F) where 1 == 1 {
                verify(x == y);
                verify(y == y)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_verify();
        assert_eq!(checks.len(), 2, "Should have 2 check nodes");

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 3);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // The first check should produce Unit (Check always returns Unit)
        match computed.get(&checks[0]) {
            Some(Value::Unit) => {}
            Some(v) => panic!("First check node produced {:?}, expected Unit", v),
            None => panic!("First check node was not computed"),
        }
    }

    /// Cross-function boundary: inlined verify from a called function passes.
    /// fn checked(x) { verify(x == x); x } inlined into protocol → both checks true.
    #[test]
    fn test_execute_cross_fn_verify_positive() {
        use crate::UDags;
        use share::Ctx;

        let src = r#"
            fn checked<F: Field>(x: F) -> F {
                verify(x == x);
                x
            }
            proto caller<F: Field>(instance v: F) where v == v {
                a <- checked(v);
                verify(a == v)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();

        let proto = gs.protocols()[0];
        let checks = proto.find_verify();
        assert_eq!(
            checks.len(),
            2,
            "Should have 2 check nodes (inlined + protocol)"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "v", 5);
        let computed = execute_graph_all(proto, inputs);

        for (i, &idx) in checks.iter().enumerate() {
            match computed.get(&idx) {
                Some(Value::Unit) => {}
                Some(v) => panic!("Check {} produced {:?}, expected Unit", i, v),
                None => panic!("Check {} was not computed", i),
            }
        }
    }

    /// Cross-function boundary: inlined verify from a called function fails.
    /// fn checked(x, y) { verify(x == y); x } — when x ≠ y the inlined check fails.
    #[test]
    fn test_execute_cross_fn_verify_negative() {
        use crate::UDags;
        use share::Ctx;

        let src = r#"
            fn checked<F: Field>(x: F, y: F) -> F {
                verify(x == y);
                x
            }
            proto caller<F: Field>(instance a: F, instance b: F) where a == a {
                r <- checked(a, b);
                verify(r == a)
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();

        let proto = gs.protocols()[0];
        let checks = proto.find_verify();
        assert_eq!(
            checks.len(),
            2,
            "Should have 2 check nodes (inlined + protocol)"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "a", 3);
        add_scalar_input(&mut inputs, "b", 7);
        let computed = execute_graph_all(proto, inputs);

        // The inlined verify(a == b) should fail; the protocol's own verify(r == a) passes.
        match computed.get(&checks[0]) {
            Some(Value::Unit) => {}
            Some(v) => panic!("First check node produced {:?}, expected Unit", v),
            None => panic!("First check node was not computed"),
        }
        match computed.get(&checks[1]) {
            Some(Value::Unit) => {}
            Some(v) => panic!("Second check node produced {:?}, expected Unit", v),
            None => panic!("Second check node was not computed"),
        }
    }

    /// Direct `verify(() == ())` — Unit == Unit, trivially true.
    #[test]
    fn test_execute_verify_unit_eq_unit() {
        use crate::UDags;
        use share::Ctx;

        let src = r#"
            proto unit_eq<F: Field>() where 1 == 1 {
                verify(() == ())
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_verify();
        assert_eq!(checks.len(), 1, "Should have 1 check node");

        let inputs = test_inputs();
        let computed = execute_graph_all(dag, inputs);

        match computed.get(&checks[0]) {
            Some(Value::Unit) => {}
            Some(v) => panic!("Check node produced {:?}, expected Unit", v),
            None => panic!("Check node was not computed"),
        }
    }

    /// `let a = verify(1 == 1); verify(a == ())` — Check returns Unit,
    /// so `a` is Unit, and `verify(a == ())` compares Unit == Unit.
    /// Uses a wrapper function because `verify(...)` greedily consumes `;`
    /// as its continuation, preventing direct `let` binding.
    #[test]
    fn test_execute_verify_let_check_then_unit_eq() {
        use crate::UDags;
        use share::Ctx;

        let src = r#"
            fn do_check<F: Field>(x: F) -> Unit {
                verify(x == x)
            }
            proto let_check<F: Field>(instance x: F) where x == x {
                let a = do_check(x);
                verify(a == ())
            }
        "#;
        let m = parse_and_concretize(src, &Ctx::new());
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_verify();
        // The inlined verify(x == x) may be merged or lack transcript edges;
        // the protocol's own verify(a == ()) is the one we care about.
        assert!(!checks.is_empty(), "Should have at least 1 check node");

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 5);
        let computed = execute_graph_all(dag, inputs);

        for (i, &check_idx) in checks.iter().enumerate() {
            match computed.get(&check_idx) {
                Some(Value::Unit) => {}
                Some(v) => panic!("Check node {} produced {:?}, expected Unit", i, v),
                None => panic!("Check node {} was not computed", i),
            }
        }
    }
}
