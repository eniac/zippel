# Critical Untested Functions - Priority List

## 🔴 CRITICAL PRIORITY

### Graph Operations (`graph/src/op.rs`) - 47 untested functions

**Arithmetic Operations** (HIGH RISK - Core functionality):
- `pub fn add()` - Addition operation
- `pub fn sub()` - Subtraction operation  
- `pub fn mul()` - Multiplication operation
- `pub fn div()` - Division operation
- `pub fn neg()` - Negation operation
- `pub fn inv()` - Inverse operation

**Binary/Logical Operations**:
- `pub fn bin()` - Binary decomposition
- `pub fn concat()` - Concatenation
- `pub fn index()` - Array indexing
- `pub fn eval()` - Polynomial evaluation

**Cryptographic Operations**:
- `pub fn msm()` - Multi-scalar multiplication
- `pub fn pairing()` - Pairing operation
- `pub fn hash()` - Hash function
- `pub fn commit()` - Commitment operation

**Type Operations**:
- `pub fn ram()` - RAM access
- `pub fn value()` - Value extraction
- `pub fn typ()` - Type information

### Graph Nodes (`graph/src/node.rs`) - 31 untested functions

**Node Queries** (SECURITY CRITICAL):
- `pub fn is_op()` - Check if node is operation
- `pub fn is_input()` - Check if node is input
- `pub fn is_relation()` - Check if node is relation
- `pub fn is_verifier_check()` - Check if verifier validation
- `pub fn is_transcript()` - Check if transcript node

**Node Manipulation** (CORRECTNESS CRITICAL):
- `pub fn references()` - Get node references
- `pub fn map_node_indices()` - Transform node indices
- `pub fn args()` - Get node arguments
- `pub fn op()` - Extract operation

**Annotation Handling**:
- `pub fn add_annotation()` - Add metadata
- `pub fn drop_annotation()` - Remove metadata

## 🟡 HIGH PRIORITY

### Backend Types (`backend/src/types.rs`) - 26 untested functions

**Type Constructors** (TYPE SAFETY):
- `pub fn scalar()` - Scalar field element
- `pub fn g1()` - G1 curve point
- `pub fn g2()` - G2 curve point
- `pub fn gt()` - GT target group
- `pub fn bool()` - Boolean type
- `pub fn vec()` - Vector type
- `pub fn mle()` - Multilinear extension
- `pub fn fin()` - Finite field element
- `pub fn uni()` - Univariate polynomial

**Vector Types**:
- `pub fn vec_scalar()`, `vec_g1()`, `vec_g2()`, etc.

### Sparse Polynomials (`graph/src/analyses/groebner/sparsepoly.rs`) - 15 untested

**Core Operations** (GROEBNER CORRECTNESS):
- `pub fn mul_by_term_and_scalar()` - Scale by term
- `pub fn isolate_elimination_vars()` - Variable isolation
- `pub fn flat_map_vars()` - Variable transformation
- `pub fn degree()` - Polynomial degree
- `pub fn is_constant()` - Constant check
- `pub fn vars()` - Extract variables

### Monomial Operations (`graph/src/analyses/groebner/monomial.rs`) - 4 untested

**Elimination Support** (GROEBNER ELIMINATION):
- `pub fn eliminate_var()` - Check elimination status
- `pub fn eliminate()` - Eliminate variables
- Iterator implementations for ElimTerm, GrevLexTerm

### Runtime (`runtime/src/graph.rs`) - 7 untested functions

**Execution** (END-TO-END CRITICAL):
- All 7 functions untested - entire runtime has NO coverage
- Critical for actual protocol execution
- Need integration tests

## 🟢 MEDIUM PRIORITY  

### PRef (`graph/src/pref.rs`) - 16 untested functions
- Reference handling and comparison
- Variable lookups

### Dep (`graph/src/dep.rs`) - 10 untested functions  
- Dependency tracking
- Graph analysis support

### Groebner Mod (`graph/src/analyses/groebner/mod.rs`) - 9 untested
- Module-level exports and utilities

### Scheduler (`graph/src/scheduler/`) - 12 untested functions
- Cost estimation (8 functions)
- Local scheduling (2 functions)
- Module exports (2 functions)

## Recommended Test Addition Order

### Week 1: Foundation
1. **Graph Operations** (20 tests)
   - Arithmetic: add, sub, mul, div (8 tests)
   - Binary/Logical: bin, concat, index (6 tests)
   - Crypto: msm, pairing, hash (6 tests)

2. **Graph Nodes** (15 tests)
   - Node queries: is_* methods (5 tests)
   - Manipulation: references, map_node_indices (5 tests)
   - Annotations (5 tests)

### Week 2: Types & Polynomials
3. **Backend Types** (15 tests)
   - Scalar and curve types (8 tests)
   - Vector types (4 tests)
   - MLE and univariate (3 tests)

4. **Sparse Polynomials** (10 tests)
   - mul_by_term_and_scalar (2 tests)
   - isolate_elimination_vars (3 tests)
   - degree, vars, flat_map (5 tests)

### Week 3: Elimination & Runtime
5. **Monomial Operations** (8 tests)
   - eliminate_var predicate (2 tests)
   - eliminate operation (3 tests)
   - Iterators (3 tests)

6. **Runtime** (10 tests)
   - Basic execution (5 tests)
   - Integration scenarios (5 tests)

### Week 4: Supporting Infrastructure
7. **PRef & Dep** (12 tests)
8. **Scheduler** (8 tests)
9. **Groebner Mod** (5 tests)

## Test Metrics Target

| Component | Current | Target (1 month) |
|-----------|---------|------------------|
| Graph Ops | 0% | 80% |
| Graph Nodes | 0% | 70% |
| Backend Types | 0% | 60% |
| Sparse Poly | 0% | 70% |
| Monomials | 0% | 80% |
| Runtime | 0% | 50% |
| **Overall** | **19%** | **40%** |

## Property-Based Testing Candidates

For complex mathematical operations, consider **property-based testing**:

1. **Polynomial Operations**:
   - Commutativity: `f + g == g + f`
   - Associativity: `(f + g) + h == f + (g + h)`
   - Distributivity: `f * (g + h) == f*g + f*h`

2. **Monomial Operations**:
   - LCM/GCD properties
   - Division properties

3. **Type System**:
   - Type construction round-trips
   - Subtyping transitivity

Use `proptest` or `quickcheck` crate for implementation.
