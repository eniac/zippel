# Algebraic Property Tests for Zippel Graph Operations

## Overview

This document describes **semantic algebraic property tests** for graph operations. These tests verify that operations like `Op::add`, `Op::mul`, etc., satisfy mathematical laws (commutativity, associativity, distributivity, etc.) by actually executing the graphs and comparing results.

**Key Insight**: Instead of just testing that operations construct nodes correctly, we test that they behave correctly according to algebraic laws when **executed with the backend**.

## Motivation

Graph operations in Zippel represent mathematical operations on cryptographic types. To ensure semantic correctness, we need to verify:

1. **Algebraic Laws Hold**: Addition is commutative, multiplication distributes over addition, etc.
2. **Type-Specific Behavior**: Laws hold for scalars, G1 points, G2 points, vectors, etc.
3. **Execution Correctness**: The compiled backend produces correct results
4. **Cross-Type Interactions**: Scalar multiplication of curve points, pairings, etc.

## Test Architecture

### Structure

```rust
// Test pattern:
// 1. Create graph with operation(s)
// 2. Execute graph with backend
// 3. Verify algebraic property holds in execution results

#[test]
fn test_add_commutativity_scalars() {
    // Build two graphs: a + b and b + a
    let graph1 = build_graph(|g| Op::add(g.input_a(), g.input_b()));
    let graph2 = build_graph(|g| Op::add(g.input_b(), g.input_a()));
    
    // Execute both with same inputs
    let inputs = test_inputs_scalar();
    let result1 = execute_graph(graph1, inputs.clone());
    let result2 = execute_graph(graph2, inputs);
    
    // Verify: a + b == b + a
    assert_eq!(result1, result2, "Addition should be commutative");
}
```

### Test Infrastructure Needed

```rust
// graph/tests/algebraic_properties/mod.rs

use backend::execute::GraphExecutor;
use graph::*;

/// Helper to build test graphs
pub struct GraphBuilder {
    graph: Graph,
    prover_inputs: Vec<NodeIndex>,
}

impl GraphBuilder {
    pub fn new() -> Self {
        Self {
            graph: Graph::new(),
            prover_inputs: Vec::new(),
        }
    }
    
    pub fn input_scalar(&mut self, name: &str) -> NodeIndex {
        let idx = self.graph.add_prover_input(Type::Scalar, name);
        self.prover_inputs.push(idx);
        idx
    }
    
    pub fn input_g1(&mut self, name: &str) -> NodeIndex {
        let idx = self.graph.add_prover_input(Type::G1, name);
        self.prover_inputs.push(idx);
        idx
    }
    
    pub fn input_vec_scalar(&mut self, name: &str, len: usize) -> NodeIndex {
        let idx = self.graph.add_prover_input(Type::VecScalar(len), name);
        self.prover_inputs.push(idx);
        idx
    }
    
    pub fn build(self) -> Graph {
        self.graph
    }
}

/// Execute graph and return result
pub fn execute_with_inputs(graph: Graph, inputs: HashMap<String, Value>) -> HashMap<NodeIndex, Value> {
    let executor = GraphExecutor::new(graph);
    executor.execute(inputs)
}
```

---

## Phase 1: Scalar Field Operations

### 1.1 Addition Properties

#### Commutativity: `a + b = b + a`

```rust
#[test]
fn test_add_scalar_commutativity() {
    for (a, b) in test_scalar_pairs() {
        let mut g1 = GraphBuilder::new();
        let a_node = g1.input_scalar("a");
        let b_node = g1.input_scalar("b");
        let result = g1.graph.add_node(Op::add(a_node, b_node));
        
        let mut g2 = GraphBuilder::new();
        let a_node = g2.input_scalar("a");
        let b_node = g2.input_scalar("b");
        let result2 = g2.graph.add_node(Op::add(b_node, a_node));
        
        let inputs = hashmap!{"a" => a, "b" => b};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "a + b should equal b + a for a={:?}, b={:?}", a, b);
    }
}
```

#### Associativity: `(a + b) + c = a + (b + c)`

```rust
#[test]
fn test_add_scalar_associativity() {
    for (a, b, c) in test_scalar_triples() {
        // Build graph for (a + b) + c
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let c1 = g1.input_scalar("c");
        let ab = g1.graph.add_node(Op::add(a1, b1));
        let abc1 = g1.graph.add_node(Op::add(ab, c1));
        
        // Build graph for a + (b + c)
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let c2 = g2.input_scalar("c");
        let bc = g2.graph.add_node(Op::add(b2, c2));
        let abc2 = g2.graph.add_node(Op::add(a2, bc));
        
        let inputs = hashmap!{"a" => a, "b" => b, "c" => c};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[abc1];
        let r2 = execute_with_inputs(g2.build(), inputs)[abc2];
        
        assert_eq!(r1, r2, "(a+b)+c should equal a+(b+c)");
    }
}
```

#### Identity: `a + 0 = a`

```rust
#[test]
fn test_add_scalar_identity() {
    for a in test_scalars() {
        let mut g = GraphBuilder::new();
        let a_node = g.input_scalar("a");
        let zero_node = g.graph.add_node(Op::lit(Fp::zero()));
        let result = g.graph.add_node(Op::add(a_node, zero_node));
        
        let inputs = hashmap!{"a" => a};
        let r = execute_with_inputs(g.build(), inputs)[result];
        
        assert_eq!(r, a, "a + 0 should equal a");
    }
}
```

#### Inverse: `a + (-a) = 0`

```rust
#[test]
fn test_add_scalar_inverse() {
    for a in test_scalars() {
        let mut g = GraphBuilder::new();
        let a_node = g.input_scalar("a");
        let neg_a = g.graph.add_node(Op::neg(a_node));
        let result = g.graph.add_node(Op::add(a_node, neg_a));
        
        let inputs = hashmap!{"a" => a};
        let r = execute_with_inputs(g.build(), inputs)[result];
        
        assert_eq!(r, Fp::zero(), "a + (-a) should equal 0");
    }
}
```

### 1.2 Multiplication Properties

#### Commutativity: `a * b = b * a`

```rust
#[test]
fn test_mul_scalar_commutativity() {
    for (a, b) in test_scalar_pairs() {
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let ab = g1.graph.add_node(Op::mul(a1, b1));
        
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let ba = g2.graph.add_node(Op::mul(b2, a2));
        
        let inputs = hashmap!{"a" => a, "b" => b};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[ab];
        let r2 = execute_with_inputs(g2.build(), inputs)[ba];
        
        assert_eq!(r1, r2, "a * b should equal b * a");
    }
}
```

#### Associativity: `(a * b) * c = a * (b * c)`

```rust
#[test]
fn test_mul_scalar_associativity() {
    for (a, b, c) in test_scalar_triples() {
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let c1 = g1.input_scalar("c");
        let ab = g1.graph.add_node(Op::mul(a1, b1));
        let abc1 = g1.graph.add_node(Op::mul(ab, c1));
        
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let c2 = g2.input_scalar("c");
        let bc = g2.graph.add_node(Op::mul(b2, c2));
        let abc2 = g2.graph.add_node(Op::mul(a2, bc));
        
        let inputs = hashmap!{"a" => a, "b" => b, "c" => c};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[abc1];
        let r2 = execute_with_inputs(g2.build(), inputs)[abc2];
        
        assert_eq!(r1, r2, "(a*b)*c should equal a*(b*c)");
    }
}
```

#### Identity: `a * 1 = a`

```rust
#[test]
fn test_mul_scalar_identity() {
    for a in test_scalars() {
        let mut g = GraphBuilder::new();
        let a_node = g.input_scalar("a");
        let one_node = g.graph.add_node(Op::lit(Fp::one()));
        let result = g.graph.add_node(Op::mul(a_node, one_node));
        
        let inputs = hashmap!{"a" => a};
        let r = execute_with_inputs(g.build(), inputs)[result];
        
        assert_eq!(r, a, "a * 1 should equal a");
    }
}
```

#### Inverse: `a * a⁻¹ = 1` (for a ≠ 0)

```rust
#[test]
fn test_mul_scalar_inverse() {
    for a in test_nonzero_scalars() {
        let mut g = GraphBuilder::new();
        let a_node = g.input_scalar("a");
        let inv_a = g.graph.add_node(Op::inv(a_node));
        let result = g.graph.add_node(Op::mul(a_node, inv_a));
        
        let inputs = hashmap!{"a" => a};
        let r = execute_with_inputs(g.build(), inputs)[result];
        
        assert_eq!(r, Fp::one(), "a * a⁻¹ should equal 1");
    }
}
```

### 1.3 Distributivity

#### Left Distributivity: `a * (b + c) = a*b + a*c`

```rust
#[test]
fn test_mul_add_left_distributivity() {
    for (a, b, c) in test_scalar_triples() {
        // Build a * (b + c)
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let c1 = g1.input_scalar("c");
        let bc = g1.graph.add_node(Op::add(b1, c1));
        let result1 = g1.graph.add_node(Op::mul(a1, bc));
        
        // Build a*b + a*c
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let c2 = g2.input_scalar("c");
        let ab = g2.graph.add_node(Op::mul(a2, b2));
        let ac = g2.graph.add_node(Op::mul(a2, c2));
        let result2 = g2.graph.add_node(Op::add(ab, ac));
        
        let inputs = hashmap!{"a" => a, "b" => b, "c" => c};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "a*(b+c) should equal a*b + a*c");
    }
}
```

#### Right Distributivity: `(a + b) * c = a*c + b*c`

```rust
#[test]
fn test_mul_add_right_distributivity() {
    for (a, b, c) in test_scalar_triples() {
        // Build (a + b) * c
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let c1 = g1.input_scalar("c");
        let ab = g1.graph.add_node(Op::add(a1, b1));
        let result1 = g1.graph.add_node(Op::mul(ab, c1));
        
        // Build a*c + b*c
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let c2 = g2.input_scalar("c");
        let ac = g2.graph.add_node(Op::mul(a2, c2));
        let bc = g2.graph.add_node(Op::mul(b2, c2));
        let result2 = g2.graph.add_node(Op::add(ac, bc));
        
        let inputs = hashmap!{"a" => a, "b" => b, "c" => c};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "(a+b)*c should equal a*c + b*c");
    }
}
```

---

## Phase 2: Group Operations (G1, G2)

### 2.1 G1 Point Addition

#### Commutativity: `P + Q = Q + P`

```rust
#[test]
fn test_add_g1_commutativity() {
    for (p, q) in test_g1_pairs() {
        let mut g1 = GraphBuilder::new();
        let p1 = g1.input_g1("P");
        let q1 = g1.input_g1("Q");
        let pq = g1.graph.add_node(Op::add(p1, q1));
        
        let mut g2 = GraphBuilder::new();
        let p2 = g2.input_g1("P");
        let q2 = g2.input_g1("Q");
        let qp = g2.graph.add_node(Op::add(q2, p2));
        
        let inputs = hashmap!{"P" => p, "Q" => q};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[pq];
        let r2 = execute_with_inputs(g2.build(), inputs)[qp];
        
        assert_eq!(r1, r2, "P + Q should equal Q + P for G1 points");
    }
}
```

#### Associativity: `(P + Q) + R = P + (Q + R)`

```rust
#[test]
fn test_add_g1_associativity() {
    for (p, q, r) in test_g1_triples() {
        let mut g1 = GraphBuilder::new();
        let p1 = g1.input_g1("P");
        let q1 = g1.input_g1("Q");
        let r1 = g1.input_g1("R");
        let pq = g1.graph.add_node(Op::add(p1, q1));
        let pqr1 = g1.graph.add_node(Op::add(pq, r1));
        
        let mut g2 = GraphBuilder::new();
        let p2 = g2.input_g1("P");
        let q2 = g2.input_g1("Q");
        let r2 = g2.input_g1("R");
        let qr = g2.graph.add_node(Op::add(q2, r2));
        let pqr2 = g2.graph.add_node(Op::add(p2, qr));
        
        let inputs = hashmap!{"P" => p, "Q" => q, "R" => r};
        
        let res1 = execute_with_inputs(g1.build(), inputs.clone())[pqr1];
        let res2 = execute_with_inputs(g2.build(), inputs)[pqr2];
        
        assert_eq!(res1, res2, "(P+Q)+R should equal P+(Q+R)");
    }
}
```

#### Identity: `P + O = P` (O is point at infinity)

```rust
#[test]
fn test_add_g1_identity() {
    for p in test_g1_points() {
        let mut g = GraphBuilder::new();
        let p_node = g.input_g1("P");
        let identity = g.graph.add_node(Op::g1_identity());
        let result = g.graph.add_node(Op::add(p_node, identity));
        
        let inputs = hashmap!{"P" => p};
        let r = execute_with_inputs(g.build(), inputs)[result];
        
        assert_eq!(r, p, "P + O should equal P");
    }
}
```

#### Inverse: `P + (-P) = O`

```rust
#[test]
fn test_add_g1_inverse() {
    for p in test_g1_points() {
        let mut g = GraphBuilder::new();
        let p_node = g.input_g1("P");
        let neg_p = g.graph.add_node(Op::neg(p_node));
        let result = g.graph.add_node(Op::add(p_node, neg_p));
        
        let inputs = hashmap!{"P" => p};
        let r = execute_with_inputs(g.build(), inputs)[result];
        
        assert_eq!(r, G1::identity(), "P + (-P) should equal identity");
    }
}
```

### 2.2 Scalar Multiplication of G1

#### Distributivity over Scalars: `(a + b) * P = a*P + b*P`

```rust
#[test]
fn test_scalar_mul_g1_distributive_over_scalars() {
    for (a, b, p) in test_scalar_pair_g1_point() {
        // Build (a + b) * P
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let p1 = g1.input_g1("P");
        let ab = g1.graph.add_node(Op::add(a1, b1));
        let result1 = g1.graph.add_node(Op::mul(ab, p1));
        
        // Build a*P + b*P
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let p2 = g2.input_g1("P");
        let ap = g2.graph.add_node(Op::mul(a2, p2));
        let bp = g2.graph.add_node(Op::mul(b2, p2));
        let result2 = g2.graph.add_node(Op::add(ap, bp));
        
        let inputs = hashmap!{"a" => a, "b" => b, "P" => p};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "(a+b)*P should equal a*P + b*P");
    }
}
```

#### Distributivity over Points: `a * (P + Q) = a*P + a*Q`

```rust
#[test]
fn test_scalar_mul_g1_distributive_over_points() {
    for (a, p, q) in test_scalar_g1_pair() {
        // Build a * (P + Q)
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let p1 = g1.input_g1("P");
        let q1 = g1.input_g1("Q");
        let pq = g1.graph.add_node(Op::add(p1, q1));
        let result1 = g1.graph.add_node(Op::mul(a1, pq));
        
        // Build a*P + a*Q
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let p2 = g2.input_g1("P");
        let q2 = g2.input_g1("Q");
        let ap = g2.graph.add_node(Op::mul(a2, p2));
        let aq = g2.graph.add_node(Op::mul(a2, q2));
        let result2 = g2.graph.add_node(Op::add(ap, aq));
        
        let inputs = hashmap!{"a" => a, "P" => p, "Q" => q};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "a*(P+Q) should equal a*P + a*Q");
    }
}
```

#### Associativity: `(a * b) * P = a * (b * P)`

```rust
#[test]
fn test_scalar_mul_g1_associativity() {
    for (a, b, p) in test_scalar_pair_g1_point() {
        // Build (a * b) * P
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let p1 = g1.input_g1("P");
        let ab = g1.graph.add_node(Op::mul(a1, b1));
        let result1 = g1.graph.add_node(Op::mul(ab, p1));
        
        // Build a * (b * P)
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let p2 = g2.input_g1("P");
        let bp = g2.graph.add_node(Op::mul(b2, p2));
        let result2 = g2.graph.add_node(Op::mul(a2, bp));
        
        let inputs = hashmap!{"a" => a, "b" => b, "P" => p};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "(a*b)*P should equal a*(b*P)");
    }
}
```

---

## Phase 3: Pairing Properties

### 3.1 Bilinearity

#### Bilinearity in First Argument: `e(a*P, Q) = e(P, Q)^a`

```rust
#[test]
fn test_pairing_bilinear_first_arg() {
    for (a, p, q) in test_scalar_g1_g2() {
        // Build e(a*P, Q)
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let p1 = g1.input_g1("P");
        let q1 = g1.input_g2("Q");
        let ap = g1.graph.add_node(Op::mul(a1, p1));
        let result1 = g1.graph.add_node(Op::pairing(ap, q1));
        
        // Build e(P, Q)^a
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let p2 = g2.input_g1("P");
        let q2 = g2.input_g2("Q");
        let epq = g2.graph.add_node(Op::pairing(p2, q2));
        let result2 = g2.graph.add_node(Op::pow(epq, a2));
        
        let inputs = hashmap!{"a" => a, "P" => p, "Q" => q};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "e(a*P, Q) should equal e(P, Q)^a");
    }
}
```

#### Bilinearity in Second Argument: `e(P, b*Q) = e(P, Q)^b`

```rust
#[test]
fn test_pairing_bilinear_second_arg() {
    for (b, p, q) in test_scalar_g1_g2() {
        // Build e(P, b*Q)
        let mut g1 = GraphBuilder::new();
        let b1 = g1.input_scalar("b");
        let p1 = g1.input_g1("P");
        let q1 = g1.input_g2("Q");
        let bq = g1.graph.add_node(Op::mul(b1, q1));
        let result1 = g1.graph.add_node(Op::pairing(p1, bq));
        
        // Build e(P, Q)^b
        let mut g2 = GraphBuilder::new();
        let b2 = g2.input_scalar("b");
        let p2 = g2.input_g1("P");
        let q2 = g2.input_g2("Q");
        let epq = g2.graph.add_node(Op::pairing(p2, q2));
        let result2 = g2.graph.add_node(Op::pow(epq, b2));
        
        let inputs = hashmap!{"b" => b, "P" => p, "Q" => q};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "e(P, b*Q) should equal e(P, Q)^b");
    }
}
```

#### Non-degeneracy: `e(G, H) ≠ 1` for generators

```rust
#[test]
fn test_pairing_non_degenerate() {
    let mut g = GraphBuilder::new();
    let g1_gen = g.graph.add_node(Op::g1_generator());
    let g2_gen = g.graph.add_node(Op::g2_generator());
    let result = g.graph.add_node(Op::pairing(g1_gen, g2_gen));
    
    let inputs = hashmap!{};
    let r = execute_with_inputs(g.build(), inputs)[result];
    
    assert_ne!(r, GT::identity(), "e(G, H) should not equal identity");
}
```

---

## Phase 4: Vector Operations

### 4.1 Vector Addition

#### Commutativity: `v + w = w + v`

```rust
#[test]
fn test_add_vec_commutativity() {
    for (v, w) in test_vec_pairs() {
        let len = v.len();
        
        let mut g1 = GraphBuilder::new();
        let v1 = g1.input_vec_scalar("v", len);
        let w1 = g1.input_vec_scalar("w", len);
        let result1 = g1.graph.add_node(Op::add(v1, w1));
        
        let mut g2 = GraphBuilder::new();
        let v2 = g2.input_vec_scalar("v", len);
        let w2 = g2.input_vec_scalar("w", len);
        let result2 = g2.graph.add_node(Op::add(w2, v2));
        
        let inputs = hashmap!{"v" => v, "w" => w};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "v + w should equal w + v for vectors");
    }
}
```

### 4.2 Inner Product

#### Commutativity: `⟨v, w⟩ = ⟨w, v⟩`

```rust
#[test]
fn test_inner_product_commutativity() {
    for (v, w) in test_vec_pairs() {
        let len = v.len();
        
        let mut g1 = GraphBuilder::new();
        let v1 = g1.input_vec_scalar("v", len);
        let w1 = g1.input_vec_scalar("w", len);
        let result1 = g1.graph.add_node(Op::inner_product(v1, w1));
        
        let mut g2 = GraphBuilder::new();
        let v2 = g2.input_vec_scalar("v", len);
        let w2 = g2.input_vec_scalar("w", len);
        let result2 = g2.graph.add_node(Op::inner_product(w2, v2));
        
        let inputs = hashmap!{"v" => v, "w" => w};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "⟨v,w⟩ should equal ⟨w,v⟩");
    }
}
```

#### Distributivity: `⟨a*v + b*w, u⟩ = a*⟨v,u⟩ + b*⟨w,u⟩`

```rust
#[test]
fn test_inner_product_distributivity() {
    for (a, b, v, w, u) in test_scalars_and_vecs() {
        let len = v.len();
        
        // Build ⟨a*v + b*w, u⟩
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_scalar("a");
        let b1 = g1.input_scalar("b");
        let v1 = g1.input_vec_scalar("v", len);
        let w1 = g1.input_vec_scalar("w", len);
        let u1 = g1.input_vec_scalar("u", len);
        let av = g1.graph.add_node(Op::mul(a1, v1));
        let bw = g1.graph.add_node(Op::mul(b1, w1));
        let avbw = g1.graph.add_node(Op::add(av, bw));
        let result1 = g1.graph.add_node(Op::inner_product(avbw, u1));
        
        // Build a*⟨v,u⟩ + b*⟨w,u⟩
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_scalar("a");
        let b2 = g2.input_scalar("b");
        let v2 = g2.input_vec_scalar("v", len);
        let w2 = g2.input_vec_scalar("w", len);
        let u2 = g2.input_vec_scalar("u", len);
        let vu = g2.graph.add_node(Op::inner_product(v2, u2));
        let wu = g2.graph.add_node(Op::inner_product(w2, u2));
        let avu = g2.graph.add_node(Op::mul(a2, vu));
        let bwu = g2.graph.add_node(Op::mul(b2, wu));
        let result2 = g2.graph.add_node(Op::add(avu, bwu));
        
        let inputs = hashmap!{"a" => a, "b" => b, "v" => v, "w" => w, "u" => u};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "⟨a*v + b*w, u⟩ should equal a*⟨v,u⟩ + b*⟨w,u⟩");
    }
}
```

---

## Phase 5: Multi-Scalar Multiplication (MSM)

### 5.1 Linearity

#### MSM Linearity: `MSM([a₁,...,aₙ], [P₁,...,Pₙ]) = Σ aᵢ*Pᵢ`

```rust
#[test]
fn test_msm_equals_sum_of_scalar_muls() {
    for (scalars, points) in test_scalar_vec_point_vec_pairs() {
        let n = scalars.len();
        
        // Build MSM(scalars, points)
        let mut g1 = GraphBuilder::new();
        let s1 = g1.input_vec_scalar("scalars", n);
        let p1 = g1.input_vec_g1("points", n);
        let msm_result = g1.graph.add_node(Op::msm(s1, p1));
        
        // Build Σ aᵢ*Pᵢ
        let mut g2 = GraphBuilder::new();
        let s2 = g2.input_vec_scalar("scalars", n);
        let p2 = g2.input_vec_g1("points", n);
        
        let mut sum = g2.graph.add_node(Op::g1_identity());
        for i in 0..n {
            let si = g2.graph.add_node(Op::index(s2, i));
            let pi = g2.graph.add_node(Op::index(p2, i));
            let mul = g2.graph.add_node(Op::mul(si, pi));
            sum = g2.graph.add_node(Op::add(sum, mul));
        }
        
        let inputs = hashmap!{"scalars" => scalars, "points" => points};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[msm_result];
        let r2 = execute_with_inputs(g2.build(), inputs)[sum];
        
        assert_eq!(r1, r2, "MSM should equal sum of scalar multiplications");
    }
}
```

#### MSM Homomorphic: `MSM(a+b, P) = MSM(a, P) + MSM(b, P)`

```rust
#[test]
fn test_msm_homomorphic_in_scalars() {
    for (a, b, points) in test_vec_pair_and_points() {
        let n = a.len();
        
        // Build MSM(a+b, P)
        let mut g1 = GraphBuilder::new();
        let a1 = g1.input_vec_scalar("a", n);
        let b1 = g1.input_vec_scalar("b", n);
        let p1 = g1.input_vec_g1("points", n);
        let ab = g1.graph.add_node(Op::add(a1, b1));
        let result1 = g1.graph.add_node(Op::msm(ab, p1));
        
        // Build MSM(a, P) + MSM(b, P)
        let mut g2 = GraphBuilder::new();
        let a2 = g2.input_vec_scalar("a", n);
        let b2 = g2.input_vec_scalar("b", n);
        let p2 = g2.input_vec_g1("points", n);
        let msm_a = g2.graph.add_node(Op::msm(a2, p2));
        let msm_b = g2.graph.add_node(Op::msm(b2, p2));
        let result2 = g2.graph.add_node(Op::add(msm_a, msm_b));
        
        let inputs = hashmap!{"a" => a, "b" => b, "points" => points};
        
        let r1 = execute_with_inputs(g1.build(), inputs.clone())[result1];
        let r2 = execute_with_inputs(g2.build(), inputs)[result2];
        
        assert_eq!(r1, r2, "MSM(a+b, P) should equal MSM(a,P) + MSM(b,P)");
    }
}
```

---

## Test Data Generators

```rust
// graph/tests/algebraic_properties/test_data.rs

use ark_ff::Field;
use ark_ec::CurveGroup;

/// Generate pairs of test scalars
pub fn test_scalar_pairs() -> Vec<(Fp, Fp)> {
    vec![
        (Fp::from(0), Fp::from(0)),
        (Fp::from(1), Fp::from(1)),
        (Fp::from(2), Fp::from(3)),
        (Fp::from(5), Fp::from(7)),
        (Fp::from(100), Fp::from(200)),
        (-Fp::from(1), Fp::from(1)),
        (Fp::rand(), Fp::rand()),
        (Fp::rand(), Fp::rand()),
        (Fp::rand(), Fp::rand()),
    ]
}

/// Generate triples of test scalars
pub fn test_scalar_triples() -> Vec<(Fp, Fp, Fp)> {
    vec![
        (Fp::from(1), Fp::from(2), Fp::from(3)),
        (Fp::from(5), Fp::from(7), Fp::from(11)),
        (Fp::rand(), Fp::rand(), Fp::rand()),
        (Fp::rand(), Fp::rand(), Fp::rand()),
    ]
}

/// Generate non-zero scalars
pub fn test_nonzero_scalars() -> Vec<Fp> {
    vec![
        Fp::from(1),
        Fp::from(2),
        Fp::from(100),
        -Fp::from(1),
        Fp::rand(),
        Fp::rand(),
    ]
}

/// Generate G1 point pairs
pub fn test_g1_pairs() -> Vec<(G1, G1)> {
    vec![
        (G1::generator(), G1::generator()),
        (G1::generator(), G1::generator() * Fp::from(2)),
        (G1::rand(), G1::rand()),
        (G1::rand(), G1::rand()),
    ]
}

/// Generate G1 point triples
pub fn test_g1_triples() -> Vec<(G1, G1, G1)> {
    vec![
        (G1::generator(), G1::generator(), G1::generator()),
        (G1::rand(), G1::rand(), G1::rand()),
        (G1::rand(), G1::rand(), G1::rand()),
    ]
}

/// Generate scalar and G1 point pairs
pub fn test_scalar_g1_pair() -> Vec<(Fp, G1, G1)> {
    vec![
        (Fp::from(2), G1::generator(), G1::generator()),
        (Fp::from(3), G1::rand(), G1::rand()),
        (Fp::rand(), G1::rand(), G1::rand()),
    ]
}

/// Generate vector pairs
pub fn test_vec_pairs() -> Vec<(Vec<Fp>, Vec<Fp>)> {
    vec![
        (vec![Fp::from(1), Fp::from(2)], vec![Fp::from(3), Fp::from(4)]),
        (vec![Fp::from(5), Fp::from(7), Fp::from(11)], 
         vec![Fp::from(2), Fp::from(3), Fp::from(5)]),
        ((0..10).map(|_| Fp::rand()).collect(), 
         (0..10).map(|_| Fp::rand()).collect()),
    ]
}
```

---

## Integration into Test Plan

### Updated Phase 1 Test Count

**Original**: 35 tests for Graph Operations  
**With Algebraic Properties**: 65+ tests

New breakdown:
- **A. Basic Functionality** (10 tests) - Construction and type checking
- **B. Scalar Algebraic Properties** (25 tests)
  - Addition: commutativity, associativity, identity, inverse (4)
  - Multiplication: commutativity, associativity, identity, inverse (4)
  - Distributivity: left, right (2)
  - Mixed properties (5)
  - Property-based variants (10)
- **C. Group Operations** (15 tests) - G1, G2 properties
- **D. Pairing Properties** (8 tests) - Bilinearity, non-degeneracy
- **E. Vector Operations** (7 tests) - Vector algebra

### Coverage Impact

These semantic tests will:
1. **Increase confidence** in backend correctness
2. **Catch subtle bugs** in type conversions
3. **Document behavior** through executable specifications
4. **Enable refactoring** with confidence
5. **Serve as regression tests** for algebraic properties

### Priority

🔴 **CRITICAL** - These tests validate the **mathematical correctness** of the entire system. Without them, we only know operations compile, not that they're correct.

---

## Summary

**Total Algebraic Property Tests**: 80+

- Scalar field: 25 tests
- Group operations: 20 tests
- Pairing: 8 tests
- Vectors: 12 tests
- MSM: 8 tests
- Cross-type: 15+ tests

**Estimated Effort**: 40 hours (1 week with infrastructure)

**ROI**: Very High - Validates semantic correctness of entire system

**Dependencies**: 
- Backend execution infrastructure
- Test data generators
- Graph builder utilities

**Next Steps**:
1. Set up test infrastructure (`GraphBuilder`, execution helpers)
2. Implement scalar field property tests (Week 1)
3. Add group operation tests (Week 2)
4. Add pairing and vector tests (Week 3)
5. Expand with property-based testing (Week 4+)
