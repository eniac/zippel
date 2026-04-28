/// Test helpers for graph operations testing
///
/// This module provides utilities for creating and executing graphs
/// to test algebraic properties and semantic correctness.
use crate::{GOp, Node, Op, PRef, Ref, UDag, mk};
use backend::op::HasOpFactory;
use backend::values::marginalize as backend_marginalize;
use backend::{ATyp, ArkBls12_381, ArkConfig, ArkScalarOps, Value};
use lang::id::Vid;
use lang::typ::{Distribution, Nothing, Qualifier};
use petgraph::graph::NodeIndex;
use share::Ctx;
use std::collections::HashMap;
use std::sync::Arc;

/// Type alias for test configuration (BLS12-381 curve)
pub type TestConfig = ArkBls12_381;

/// Helper to create a simple DAG for testing operations
pub struct GraphBuilder<C: ArkConfig> {
    dag: UDag<C>,
    input_node: NodeIndex,
}

impl<C: HasOpFactory> GraphBuilder<C> {
    /// Create a new graph builder with an input node
    pub fn new() -> Self {
        let mut dag = UDag::new();
        let input_node = dag.add_node(Node::Inp(Vid::from("inputs"), vec![]));
        GraphBuilder { dag, input_node }
    }

    /// Add a variable input
    pub fn add_input(&mut self, name: &str, typ: ATyp) -> Ref {
        let vid = Vid::from(name);
        match &mut self.dag[self.input_node] {
            Node::Inp(_, args) => {
                let pref = PRef::from_var(
                    vid.clone(),
                    self.input_node,
                    typ.clone(),
                    0,
                    Qualifier::Private,
                    Distribution::Nonuniform,
                );
                args.push(pref);
            }
            _ => unreachable!(),
        }
        Ref::Var(vid, self.input_node)
    }

    /// Add an operation node to the graph
    pub fn add_op(&mut self, op: GOp<C>) -> Ref {
        use crate::DepType;
        let hop = mk::<C>(op.clone());
        let node = self.dag.add_node(Node::Op(hop, Nothing));
        // Add edges from dependencies to this node
        self.dag.add_edges(DepType::Data, node, op);
        Ref::Node(node)
    }

    /// Build and return the DAG
    pub fn build(self) -> UDag<C> {
        self.dag
    }
}

/// Execute a graph with given inputs and return the result
/// This is a simplified executor for testing purposes
pub fn execute_graph<C: HasOpFactory>(
    dag: &UDag<C>,
    inputs: Ctx<Vid, Value<C>>,
) -> Option<Value<C>> {
    use petgraph::visit::Topo;

    let mut computed: HashMap<NodeIndex, Value<C>> = HashMap::new();
    let inputs_arc = Arc::new(inputs);

    // Get topological order using petgraph's Topo iterator
    let graph = dag.inner_graph();
    let mut topo = Topo::new(graph);
    let mut last_op_value = None;

    while let Some(node_idx) = topo.next(graph) {
        match &dag[node_idx] {
            Node::Inp(_, _) | Node::Rel(_, _) => {
                // Skip input nodes
            }
            Node::Op(op, _) | Node::Transcr(op, _) => {
                let value = evaluate_op(&**op, &computed, &inputs_arc);
                computed.insert(node_idx, value.clone());
                last_op_value = Some(value);
            }
        }
    }

    last_op_value
}

/// Execute a graph with given inputs and return all computed node values.
/// This is useful for inspecting individual node results (e.g. multiple Check nodes).
pub fn execute_graph_all<C: HasOpFactory>(
    dag: &UDag<C>,
    inputs: Ctx<Vid, Value<C>>,
) -> HashMap<NodeIndex, Value<C>> {
    use petgraph::visit::Topo;

    let mut computed: HashMap<NodeIndex, Value<C>> = HashMap::new();
    let inputs_arc = Arc::new(inputs);

    let graph = dag.inner_graph();
    let mut topo = Topo::new(graph);

    while let Some(node_idx) = topo.next(graph) {
        match &dag[node_idx] {
            Node::Inp(_, _) | Node::Rel(_, _) => {}
            Node::Op(op, _) | Node::Transcr(op, _) => {
                let value = evaluate_op(&**op, &computed, &inputs_arc);
                computed.insert(node_idx, value);
            }
        }
    }

    computed
}

/// Evaluate an operation recursively
fn evaluate_op<C: HasOpFactory>(
    op: &GOp<C>,
    computed: &HashMap<NodeIndex, Value<C>>,
    inputs: &Arc<Ctx<Vid, Value<C>>>,
) -> Value<C> {
    match op {
        Op::Value(v) => v.clone(),
        Op::Ref(r, _) => match r {
            Ref::Node(n) => computed.get(n).expect("Node should be computed").clone(),
            Ref::Var(vid, node_idx) => {
                // Resolves by `node_idx` first to ensure variable shadowing works.
                if let Some(v) = computed.get(node_idx) {
                    v.clone()
                } else if let Some(v) = inputs.get(vid) {
                    v.clone()
                } else {
                    panic!("Variable should be computed or provided as input")
                }
            }
        },
        Op::Bin(binop, a, b, _typ) => {
            let a_val = evaluate_op(a, computed, inputs);
            let b_val = evaluate_op(b, computed, inputs);
            use lang::ast::BinOp;
            match binop {
                BinOp::Add => a_val + b_val,
                BinOp::Sub => a_val - b_val,
                BinOp::Mul => a_val * b_val,
                BinOp::Div => a_val / b_val,
                BinOp::Rem => a_val % b_val,
                BinOp::Pow => a_val ^ b_val,
                BinOp::And => a_val & b_val,
                BinOp::Dot => a_val.dot(b_val),
                BinOp::Concat => a_val.value_concat(b_val),
                BinOp::Equ => a_val.value_equ(&b_val),
            }
        }
        Op::Vec(ops) => {
            let values: Vec<Value<C>> = ops
                .iter()
                .map(|o| evaluate_op(o, computed, inputs))
                .collect();
            Value::value_vec(values)
        }
        Op::Ram(v, idx) => {
            let v_val = evaluate_op(v, computed, inputs);
            let idx_val = evaluate_op(idx, computed, inputs);
            v_val.ram(idx_val)
        }
        Op::Pair(a, b, _) => {
            let a_val = evaluate_op(a, computed, inputs);
            let mut b_val = evaluate_op(b, computed, inputs);
            a_val.value_pair(&mut b_val);
            b_val
        }
        Op::Check(a) => evaluate_op(a, computed, inputs),
        Op::Random(typ, _) => {
            use rand::rngs::ThreadRng;
            let mut rng = ThreadRng::default();
            Value::random(&mut rng, typ)
        }
        Op::Challenge(typ, _) => {
            use rand::rngs::ThreadRng;
            let mut rng = ThreadRng::default();
            Value::random(&mut rng, typ)
        }
        Op::Record(fields) => {
            let evaluated_fields: Ctx<String, Value<C>> = fields
                .iter()
                .map(|(k, v)| (k.clone(), evaluate_op(v, computed, inputs)))
                .collect();
            Value::Record(evaluated_fields)
        }
        Op::Poly(a) => {
            let a_val = evaluate_op(a, computed, inputs);
            a_val.value_poly()
        }
        Op::Marginalize(a) => {
            let (poly_val, challenge_val, round_val, num_variables_val, max_degree_val) = match &**a
            {
                Op::Record(fields) => {
                    let poly_op = fields
                        .get(&"poly".to_string())
                        .expect("marginalize: missing field 'poly'");
                    let challenge_op = fields
                        .get(&"challenge".to_string())
                        .expect("marginalize: missing field 'challenge'");
                    let round_op = fields.get(&"round".to_string());
                    let num_variables_op = fields.get(&"num_variables".to_string());
                    let max_degree_op = fields.get(&"max_degree".to_string());

                    let poly_val = evaluate_op(poly_op, computed, inputs);
                    let challenge_val = evaluate_op(challenge_op, computed, inputs);
                    let round_val = round_op.map(|op| evaluate_op(op, computed, inputs));
                    let num_variables_val =
                        num_variables_op.map(|op| evaluate_op(op, computed, inputs));
                    let max_degree_val = max_degree_op.map(|op| evaluate_op(op, computed, inputs));
                    (
                        poly_val,
                        challenge_val,
                        round_val,
                        num_variables_val,
                        max_degree_val,
                    )
                }
                _ => {
                    let cfg_val = evaluate_op(a, computed, inputs);
                    let Value::Record(record) = cfg_val else {
                        unreachable!()
                    };
                    let poly_val = record.get(&"poly".to_string()).cloned().unwrap();
                    let challenge_val = record.get(&"challenge".to_string()).cloned().unwrap();
                    let round_val = record.get(&"round".to_string()).cloned();
                    let num_variables_val = record.get(&"num_variables".to_string()).cloned();
                    let max_degree_val = record.get(&"max_degree".to_string()).cloned();
                    (
                        poly_val,
                        challenge_val,
                        round_val,
                        num_variables_val,
                        max_degree_val,
                    )
                }
            };

            let poly = poly_val.into_poly().clone();
            let challenge = Some(challenge_val.into_scalar());
            let round = round_val.map(|v| v.into_index()).unwrap_or(0usize);
            let num_variables = if let Some(v) = num_variables_val {
                v.into_index()
            } else {
                let current_poly_vars = poly.num_vars().unwrap_or(1);
                if round == 0 {
                    current_poly_vars
                } else {
                    current_poly_vars + (round - 1)
                }
            };
            let max_degree = max_degree_val
                .map(|v| v.into_index())
                .unwrap_or_else(|| poly.degree());

            let (evals, next_poly) =
                backend_marginalize::<C>(&poly, num_variables, max_degree, round, challenge);
            let mut out_fields = Ctx::new();
            out_fields.insert(&"evaluations".to_string(), &Value::VecScalar(evals));
            out_fields.insert(&"next_poly".to_string(), &Value::Poly(next_poly));
            Value::Record(out_fields)
        }
        Op::Proj(record_op, field_name, _) => {
            let rec_val = evaluate_op(record_op, computed, inputs);
            let Value::Record(record) = rec_val else {
                unreachable!()
            };
            record.get(&field_name).cloned().unwrap()
        }
        Op::Interpolate(_, _) | Op::Fft(_) | Op::Mle(_) | Op::Coef(_) | Op::Eval(_, _) => {
            unimplemented!("FFT/polynomial operations not yet supported in test executor")
        }
        Op::Reduce(binop, v) => {
            let v_val = evaluate_op(v, computed, inputs);
            v_val.value_reduce(*binop)
        }
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
        assert_eq!(dag.node_count(), 1); // Only input node
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
    fn test_marginalize_op() {
        let mut builder = GraphBuilder::<TestConfig>::new();

        let poly = Value::<TestConfig>::VecIndex(vec![1, 2, 3]).value_poly();
        let mut cfg_fields = Ctx::new();
        cfg_fields.insert(&"poly".to_string(), &mk(Op::Value(poly)));
        cfg_fields.insert(
            &"challenge".to_string(),
            &mk(Op::Value(Value::Scalar(
                <TestConfig as ArkConfig>::FOps::zero(),
            ))),
        );
        cfg_fields.insert(&"round".to_string(), &mk(Op::Value(Value::Index(0))));
        cfg_fields.insert(
            &"num_variables".to_string(),
            &mk(Op::Value(Value::Index(1))),
        );
        cfg_fields.insert(&"max_degree".to_string(), &mk(Op::Value(Value::Index(2))));
        let cfg = Op::Record(cfg_fields);

        builder.add_op(Op::Marginalize(mk(cfg)));

        let dag = builder.build();
        let result = execute_graph(&dag, test_inputs()).expect("expected marginalize result");
        let Value::Record(fields) = result else {
            panic!("expected Value::Record from marginalize");
        };
        let evals = fields
            .get(&"evaluations".to_string())
            .expect("evaluations field");
        let next_poly = fields
            .get(&"next_poly".to_string())
            .expect("next_poly field");
        match evals {
            Value::VecScalar(v) => assert_eq!(v.len(), 3),
            other => panic!("expected VecScalar evaluations, got {other:?}"),
        }
        match next_poly {
            Value::Poly(_) => {}
            other => panic!("expected Poly next_poly, got {other:?}"),
        }
    }

    #[test]
    fn test_execute_multiple_checks() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        // Protocol with two separate verify statements → two Check nodes
        let src = r#"
            proto two_checks<F: Field>(public x: F, public y: F) where true {
                verify(x == x);
                verify(y == y)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_check();
        assert_eq!(
            checks.len(),
            2,
            "Protocol with two verify statements should have two check nodes"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 5);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // Verify both check nodes produce Bool(true)
        for (i, &check_idx) in checks.iter().enumerate() {
            match computed.get(&check_idx) {
                Some(Value::Bool(true)) => {}
                Some(v) => panic!("Check node {} produced {:?}, expected Bool(true)", i, v),
                None => panic!("Check node {} was not computed", i),
            }
        }
    }

    #[test]
    fn test_execute_single_check_conjunction() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        // Protocol with single verify using && → one Check node
        let src = r#"
            proto and_check<F: Field>(public x: F, public y: F) where true {
                verify(x == x && y == y)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_check();
        assert_eq!(
            checks.len(),
            1,
            "Protocol with single verify (&&) should have one check node"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 5);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // The single check node should produce Bool(true)
        match computed.get(&checks[0]) {
            Some(Value::Bool(true)) => {}
            Some(v) => panic!("Check node produced {:?}, expected Bool(true)", v),
            None => panic!("Check node was not computed"),
        }
    }

    #[test]
    fn test_execute_scattered_checks() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        // Protocol with scattered verify statements throughout the body
        let src = r#"
            proto scattered<F: Field>(public x: F, public y: F) where true {
                a <- x + y;
                verify(a == a);
                b <- a + x;
                verify(b == b)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_check();
        assert_eq!(
            checks.len(),
            2,
            "Scattered verify statements should produce 2 check nodes"
        );

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 3);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // Verify all check nodes produce Bool(true)
        for (i, &check_idx) in checks.iter().enumerate() {
            match computed.get(&check_idx) {
                Some(Value::Bool(true)) => {}
                Some(v) => panic!("Check node {} produced {:?}, expected Bool(true)", i, v),
                None => panic!("Check node {} was not computed", i),
            }
        }
    }

    #[test]
    fn test_execute_checks_negative_second_fails() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        // Second verify has a false condition (x != y)
        let src = r#"
            proto neg<F: Field>(public x: F, public y: F) where true {
                verify(x == x);
                verify(x == y)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_check();
        assert_eq!(checks.len(), 2, "Should have 2 check nodes");

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 3);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // The second check should produce Bool(false)
        match computed.get(&checks[1]) {
            Some(Value::Bool(false)) => {}
            Some(v) => panic!("Second check node produced {:?}, expected Bool(false)", v),
            None => panic!("Second check node was not computed"),
        }
    }

    #[test]
    fn test_execute_checks_negative_first_fails() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        // First verify has a false condition (x != y)
        let src = r#"
            proto neg2<F: Field>(public x: F, public y: F) where true {
                verify(x == y);
                verify(y == y)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();
        let dag = &gs[0];

        let checks = dag.find_check();
        assert_eq!(checks.len(), 2, "Should have 2 check nodes");

        let mut inputs = test_inputs();
        add_scalar_input(&mut inputs, "x", 3);
        add_scalar_input(&mut inputs, "y", 7);
        let computed = execute_graph_all(dag, inputs);

        // The first check should produce Bool(false)
        match computed.get(&checks[0]) {
            Some(Value::Bool(false)) => {}
            Some(v) => panic!("First check node produced {:?}, expected Bool(false)", v),
            None => panic!("First check node was not computed"),
        }
    }

    /// Cross-function boundary: inlined verify from a called function passes.
    /// fn checked(x) { verify(x == x); x } inlined into protocol → both checks true.
    #[test]
    fn test_execute_cross_fn_verify_positive() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        let src = r#"
            fn checked<F: Field>(x: F) -> F {
                verify(x == x);
                x
            }
            proto caller<F: Field>(public v: F) where v == v {
                a <- checked(v);
                verify(a == v)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();

        let proto = gs.protocols()[0];
        let checks = proto.find_check();
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
                Some(Value::Bool(true)) => {}
                Some(v) => panic!("Check {} produced {:?}, expected Bool(true)", i, v),
                None => panic!("Check {} was not computed", i),
            }
        }
    }

    /// Cross-function boundary: inlined verify from a called function fails.
    /// fn checked(x, y) { verify(x == y); x } — when x ≠ y the inlined check fails.
    #[test]
    fn test_execute_cross_fn_verify_negative() {
        use crate::UDags;
        use lang::ast::UModule;
        use share::Ctx;

        let src = r#"
            fn checked<F: Field>(x: F, y: F) -> F {
                verify(x == y);
                x
            }
            proto caller<F: Field>(public a: F, public b: F) where a == a {
                r <- checked(a, b);
                verify(r == a)
            }
        "#;
        let m = UModule::from_str(src)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = UDags::<TestConfig>::from_module(m).unwrap();

        let proto = gs.protocols()[0];
        let checks = proto.find_check();
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
            Some(Value::Bool(false)) => {}
            Some(v) => panic!("First check node produced {:?}, expected Bool(false)", v),
            None => panic!("First check node was not computed"),
        }
        match computed.get(&checks[1]) {
            Some(Value::Bool(true)) => {}
            Some(v) => panic!("Second check node produced {:?}, expected Bool(true)", v),
            None => panic!("Second check node was not computed"),
        }
    }
}
