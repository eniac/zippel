/// Test helpers for graph operations testing
/// 
/// This module provides utilities for creating and executing graphs
/// to test algebraic properties and semantic correctness.

use crate::{UDag, Node, Op, GOp, Ref, PRef};
use backend::{ArkConfig, ArkBls12_381, Value, ATyp, ArkScalarOps};
use lang::id::Vid;
use lang::typ::{Nothing, Qualifier, Distribution};
use petgraph::graph::NodeIndex;
use share::Ctx;
use std::sync::Arc;
use std::collections::HashMap;

/// Type alias for test configuration (BLS12-381 curve)
pub type TestConfig = ArkBls12_381;

/// Helper to create a simple DAG for testing operations
pub struct GraphBuilder<C: ArkConfig> {
    dag: UDag<C>,
    input_node: NodeIndex,
}

impl<C: ArkConfig> GraphBuilder<C> {
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
                    Distribution::Nonuniform
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
        let node = self.dag.add_node(Node::Op(op.clone(), Nothing));
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
pub fn execute_graph<C: ArkConfig>(
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
                let value = evaluate_op(op, &computed, &inputs_arc);
                computed.insert(node_idx, value.clone());
                last_op_value = Some(value);
            }
        }
    }
    
    last_op_value
}

/// Evaluate an operation recursively
fn evaluate_op<C: ArkConfig>(
    op: &GOp<C>,
    computed: &HashMap<NodeIndex, Value<C>>,
    inputs: &Arc<Ctx<Vid, Value<C>>>,
) -> Value<C> {
    match op {
        Op::Value(v) => v.clone(),
        Op::Ref(r, _) => match r {
            Ref::Node(n) => computed.get(n).expect("Node should be computed").clone(),
            Ref::Var(vid, _) => inputs.get(vid).expect("Variable should exist").clone(),
        },
        Op::Bin(binop, box a, box b, _typ) => {
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
            let values: Vec<Value<C>> = ops.iter()
                .map(|o| evaluate_op(o, computed, inputs))
                .collect();
            Value::value_vec(values)
        }
        Op::Ram(box v, box idx) => {
            let v_val = evaluate_op(v, computed, inputs);
            let idx_val = evaluate_op(idx, computed, inputs);
            v_val.ram(idx_val)
        }
        Op::Pair(box a, box b, _) => {
            let a_val = evaluate_op(a, computed, inputs);
            let mut b_val = evaluate_op(b, computed, inputs);
            a_val.value_pair(&mut b_val);
            b_val
        }
        Op::Check(box a) => evaluate_op(a, computed, inputs),
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
        Op::Ifft(_) | Op::Fft(_) | Op::Poly(_) | Op::Mle(_) | 
        Op::Coef(_) | Op::Eval(_, _) => {
            unimplemented!("FFT/polynomial operations not yet supported in test executor")
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
pub fn add_scalar_input<C: ArkConfig>(
    ctx: &mut Ctx<Vid, Value<C>>,
    name: &str,
    value: u64,
) {
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
}
