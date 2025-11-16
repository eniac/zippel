# Comprehensive Test Plan for Zippel
**Created**: 2025-11-16  
**Goal**: Increase coverage from 19% to 50%+ over 6 weeks  
**Priority**: Security-critical and core infrastructure first

---

## Executive Summary

This plan outlines a systematic approach to increasing test coverage across the Zippel codebase from the current 19% to 50%+ through targeted testing of critical infrastructure.

**Total Estimated Tests**: 220+ new tests  
**Estimated Effort**: ~320 hours (~8 weeks at 40hrs/week)  
**Coverage Target**: 55%+  

### Phased Approach

1. **Phase 1 (Weeks 1-2)**: Graph Operations & Nodes - Foundation (90 tests)
   - Basic functionality (35 tests)
   - **Algebraic properties** (30 tests) ⭐ NEW
   - Node operations (25 tests)
2. **Phase 2 (Weeks 3-4)**: Backend Types & Polynomials (45 tests)  
3. **Phase 3 (Weeks 5-6)**: Monomials, Runtime & Integration (35 tests)
4. **Phase 4 (Weeks 7-8)**: Advanced Algebraic & Property-Based Testing (50+ tests) ⭐ EXPANDED
   - Group operations (20 tests)
   - Pairing properties (8 tests)
   - Vector operations (12 tests)
   - Property-based tests (10+ tests)

---

## Phase 1: Critical Infrastructure (Weeks 1-2)
**Target**: Graph operations and nodes + algebraic properties  
**Tests**: 90 tests  
**Coverage Goal**: 19% → 30%

### 1.1 Graph Operations Tests (`graph/src/op.rs`)
**Priority**: 🔴 CRITICAL  
**Tests**: 65 tests (35 basic + 30 algebraic properties)  
**Current Coverage**: 0%  
**Target Coverage**: 80%

**See Also**: [ALGEBRAIC_PROPERTY_TESTS.md](./ALGEBRAIC_PROPERTY_TESTS.md) for detailed semantic tests

#### Test Categories

**A. Arithmetic Operations - Basic Functionality (10 tests)**
- `test_add_scalars` - Basic scalar addition
- `test_add_vectors` - Vector element-wise addition
- `test_add_type_mismatch` - Error handling for type mismatches
- `test_sub_scalars` - Scalar subtraction
- `test_mul_scalars` - Scalar multiplication (verify commutativity)
- `test_mul_scalar_by_vector` - Scalar-vector multiplication
- `test_div_scalars` - Division with non-zero divisor
- `test_div_by_zero` - Division by zero handling
- `test_neg_scalar` - Negation: verify a + (-a) == 0
- `test_inv_scalar` - Multiplicative inverse: verify a * inv(a) == 1

**B. Cryptographic Operations (8 tests)**
- `test_msm_basic` - Multi-scalar multiplication with valid inputs
- `test_msm_empty` - MSM with empty vectors returns identity
- `test_msm_single_element` - Single element MSM equals scalar mul
- `test_pairing_basic` - Basic pairing e(G1, G2) → GT
- `test_pairing_bilinearity` - Verify e(aP, bQ) == e(P,Q)^(ab)
- `test_commit_basic` - Create commitment to value
- `test_hash_basic` - Hash function correctness
- `test_hash_different_inputs` - Different inputs yield different hashes

**C. Binary/Logic Operations (8 tests)**
- `test_bin_scalar_to_bits` - Convert scalar to binary representation
- `test_bin_bit_length` - Verify bit vector length
- `test_concat_vectors` - Concatenate two vectors
- `test_concat_length` - Verify concatenated length
- `test_index_vector` - Valid array indexing
- `test_index_out_of_bounds` - Out of bounds handling
- `test_eval_polynomial` - Polynomial evaluation
- `test_eval_zero_polynomial` - Zero polynomial evaluates to zero

**D. Complex Operations (9 tests)**
- `test_ifft_basic` - Inverse FFT correctness
- `test_fft_ifft_roundtrip` - Verify fft(ifft(x)) == x
- `test_mle_basic` - Multilinear extension construction
- `test_ram_read` - RAM read operation
- `test_ram_write` - RAM write operation
- `test_value_extraction` - Extract value from wrapped type
- `test_typ_information` - Type information retrieval
- `test_challenge_generation` - Fiat-Shamir challenge
- `test_observe_transcript` - Transcript append operation

**E. Algebraic Properties - Semantic Correctness (30 tests)** ⭐ NEW

These tests verify that operations satisfy mathematical laws by executing graphs with the backend:

*Scalar Field Addition Properties (5 tests)*
- `test_add_scalar_commutativity` - Verify `a + b = b + a` via execution
- `test_add_scalar_associativity` - Verify `(a+b)+c = a+(b+c)` via execution
- `test_add_scalar_identity` - Verify `a + 0 = a` via execution
- `test_add_scalar_inverse` - Verify `a + (-a) = 0` via execution
- `test_add_scalar_property_based` - Property test with random inputs

*Scalar Field Multiplication Properties (5 tests)*
- `test_mul_scalar_commutativity` - Verify `a * b = b * a` via execution
- `test_mul_scalar_associativity` - Verify `(a*b)*c = a*(b*c)` via execution
- `test_mul_scalar_identity` - Verify `a * 1 = a` via execution
- `test_mul_scalar_inverse` - Verify `a * a⁻¹ = 1` for a ≠ 0 via execution
- `test_mul_scalar_property_based` - Property test with random inputs

*Distributivity (4 tests)*
- `test_mul_add_left_distributivity` - Verify `a*(b+c) = a*b + a*c` via execution
- `test_mul_add_right_distributivity` - Verify `(a+b)*c = a*c + b*c` via execution
- `test_distributivity_property_based` - Property test
- `test_distributivity_cross_types` - Test with vectors, G1 points

*Vector Operations (6 tests)*
- `test_add_vec_commutativity` - Vector addition commutativity
- `test_add_vec_associativity` - Vector addition associativity
- `test_scalar_vec_distributivity` - `a*(v+w) = a*v + a*w`
- `test_inner_product_commutativity` - `⟨v,w⟩ = ⟨w,v⟩`
- `test_inner_product_distributivity` - `⟨a*v+b*w, u⟩ = a*⟨v,u⟩ + b*⟨w,u⟩`
- `test_vector_property_based` - Property test for vectors

*Cross-Type Operations (10 tests)*
- `test_scalar_mul_g1_distributive_scalars` - `(a+b)*P = a*P + b*P`
- `test_scalar_mul_g1_distributive_points` - `a*(P+Q) = a*P + a*Q`
- `test_scalar_mul_g1_associativity` - `(a*b)*P = a*(b*P)`
- `test_scalar_mul_g2_properties` - Same for G2
- `test_msm_linearity` - `MSM([a],[P]) = Σ aᵢ*Pᵢ`
- `test_msm_homomorphic_scalars` - `MSM(a+b,P) = MSM(a,P)+MSM(b,P)`
- `test_msm_homomorphic_points` - `MSM(a,P+Q) = MSM(a,P)+MSM(a,Q)`
- `test_mixed_operations_consistency` - Complex expression evaluation
- `test_type_preservation` - Types preserved through operations
- `test_algebraic_property_based_mixed` - Property test across types

**Implementation Note**: These tests require:
1. Backend execution infrastructure
2. Test data generators (random scalars, points, vectors)
3. Graph builder utilities for clean test construction
4. See [ALGEBRAIC_PROPERTY_TESTS.md](./ALGEBRAIC_PROPERTY_TESTS.md) for detailed implementation

### 1.2 Graph Node Tests (`graph/src/node.rs`)
**Priority**: 🔴 CRITICAL  
**Tests**: 25 tests  
**Current Coverage**: 0%  
**Target Coverage**: 70%

#### Test Categories

**A. Node Construction and Queries (10 tests)**
- `test_create_op_node` - Operation node creation
- `test_create_input_node` - Input node creation
- `test_create_relation_node` - Relation/constraint node creation
- `test_is_op_true` - Verify is_op() on Op nodes
- `test_is_op_false` - Verify is_op() on non-Op nodes
- `test_is_input_query` - Test is_input() predicate
- `test_is_relation_query` - Test is_relation() predicate
- `test_is_verifier_check` - Identify verifier validation nodes
- `test_is_transcript_query` - Identify transcript nodes
- `test_set_transcript` - Mark node as transcript, verify query

**B. Node Manipulation (8 tests)**
- `test_get_references` - Extract all PRef references
- `test_map_node_indices_simple` - Simple index transformation
- `test_map_node_indices_complex` - Complex graph transformation
- `test_args_extraction` - Get operation arguments
- `test_op_extraction` - Extract Op from Node::Op
- `test_into_op_success` - Convert Node::Op to Op
- `test_into_op_failure` - Failed conversion handling
- `test_into_ann_conversion` - Convert to annotated node

**C. Annotation Handling (7 tests)**
- `test_add_annotation_single` - Add single annotation
- `test_add_annotation_multiple` - Add multiple annotations
- `test_drop_annotation_single` - Remove specific annotation
- `test_drop_annotation_preserve_others` - Remove one, keep others
- `test_annotation_on_op_node` - Annotations on Op nodes
- `test_annotation_on_input_node` - Annotations on Input nodes
- `test_name_annotation` - Test name() method with/without annotation

---

## Phase 2: Type System and Polynomials (Weeks 3-4)
**Target**: Backend types and sparse polynomials  
**Tests**: 45 tests  
**Coverage Goal**: 28% → 38%

### 2.1 Backend Type Tests (`backend/src/types.rs`)
**Priority**: 🟡 HIGH  
**Tests**: 25 tests  
**Current Coverage**: 0%  
**Target Coverage**: 60%

#### Test Categories

**A. Basic Type Construction (10 tests)**
- `test_scalar_type` - Create scalar type, verify properties
- `test_g1_type` - G1 curve point type
- `test_g2_type` - G2 curve point type
- `test_gt_type` - GT target group type
- `test_bool_type` - Boolean type
- `test_fin_type` - Finite field type with specific size
- `test_uni_type` - Univariate polynomial type
- `test_type_equality` - Verify type equality semantics
- `test_type_display` - String representation
- `test_type_clone` - Type cloning

**B. Vector and Composite Types (8 tests)**
- `test_vec_scalar` - Vector of scalars
- `test_vec_g1` - Vector of G1 points
- `test_vec_nested` - Vector of vectors
- `test_vec_length_preservation` - Type carries length info
- `test_mle_type` - Multilinear extension type
- `test_tuple_type` - Tuple types (if supported)
- `test_struct_type` - Struct types (if supported)
- `test_type_compatibility` - Type compatibility rules

**C. Type Operations (7 tests)**
- `test_subtype_relation` - Subtyping (if exists)
- `test_type_unification` - Unify two types
- `test_type_substitution` - Type variable substitution
- `test_type_checking_add` - Type check addition
- `test_type_checking_mul` - Type check multiplication
- `test_type_checking_pairing` - Type check pairing
- `test_type_inference` - Infer types from operations

### 2.2 Sparse Polynomial Tests (`graph/src/analyses/groebner/sparsepoly.rs`)
**Priority**: 🟡 HIGH  
**Tests**: 20 tests  
**Current Coverage**: 0%  
**Target Coverage**: 70%

#### Test Categories

**A. Polynomial Construction and Properties (8 tests)**
- `test_zero_polynomial` - Zero poly: is_zero() == true
- `test_constant_polynomial` - Constant: is_constant() == true
- `test_lit_polynomial` - Create from literal coefficient
- `test_var_polynomial` - Single variable poly
- `test_degree_simple` - Degree of univariate poly
- `test_degree_multivariate` - Degree of multivariate poly
- `test_leading_term` - Extract leading term
- `test_vars_extraction` - Extract all variables

**B. Polynomial Operations (12 tests)**
- `test_mul_by_term_and_scalar` - Multiply by monomial and scalar
- `test_mul_by_term_preserves_structure` - Term count verification
- `test_square_polynomial` - (x+y)² = x²+2xy+y²
- `test_pow_polynomial` - (x+1)³ expansion
- `test_contains_term` - Check monomial existence
- `test_flat_map_vars` - Variable transformation
- `test_isolate_elimination_vars_simple` - Separate elim/non-elim vars
- `test_isolate_elimination_vars_complex` - Multiple elim vars
- `test_s_poly_edge_cases` - S-poly with coprime terms, zero result
- `test_polynomial_addition` - Term cancellation
- `test_polynomial_subtraction` - Subtraction correctness
- `test_polynomial_negation` - Negation correctness

---

## Phase 3: Elimination and Advanced Features (Weeks 5-6)
**Target**: Monomials, elimination, runtime  
**Tests**: 35 tests  
**Coverage Goal**: 38% → 50%+

### 3.1 Monomial Operation Tests (`graph/src/analyses/groebner/monomial.rs`)
**Priority**: 🟡 MEDIUM  
**Tests**: 12 tests  
**Current Coverage**: 0%  
**Target Coverage**: 80%

#### Test Categories

**A. Elimination Predicates (4 tests)**
- `test_eliminate_var_true` - Elim var returns true
- `test_eliminate_var_false` - Non-elim var returns false
- `test_eliminate_removes_vars` - Removes all elim vars
- `test_eliminate_preserves_others` - Non-elim vars preserved

**B. Monomial Operations (8 tests)**
- `test_monomial_lcm` - LCM(x²y, xy²) = x²y²
- `test_monomial_gcd` - GCD(x²y, xy²) = xy
- `test_monomial_division` - x²y / xy = x
- `test_is_divided_true` - Divisibility check true case
- `test_is_divided_false` - Divisibility check false case
- `test_is_coprime_true` - Coprimality check true case
- `test_is_coprime_false` - Coprimality check false case
- `test_monomial_iterator` - Iterate over vars and powers

### 3.2 Runtime Tests (`runtime/src/graph.rs`)
**Priority**: 🟡 HIGH  
**Tests**: 15 tests  
**Current Coverage**: 0%  
**Target Coverage**: 50%

#### Test Categories

**A. Basic Execution (8 tests)**
- `test_execute_simple_computation` - Execute a + b
- `test_execute_arithmetic_chain` - (a+b)*(c-d)
- `test_execute_with_constraints` - With verifier checks
- `test_execute_transcript_operations` - Fiat-Shamir transcript
- `test_execute_commitment` - Commitment and opening
- `test_execute_pairing_check` - Pairing-based verification
- `test_execute_zero_knowledge_protocol` - Simple ZK protocol
- `test_execution_failure_detection` - Invalid witness detection

**B. Integration Tests (7 tests)**
- `test_schnorr_protocol` - Complete Schnorr proof
- `test_range_proof` - Range proof (accept/reject)
- `test_polynomial_commitment` - KZG-style commitment
- `test_sum_check_protocol` - Multi-round sum-check
- `test_plonk_gates` - PLONK gates (add, mul, custom)
- `test_lookup_argument` - Lookup table proof
- `test_recursive_proof` - Proof of proof (if supported)

### 3.3 Supporting Infrastructure Tests
**Priority**: 🟢 MEDIUM  
**Tests**: 8 tests

**A. PRef Tests (4 tests)**
- `test_pref_creation` - Create program reference
- `test_pref_comparison` - Equality and ordering
- `test_pref_var_lookup` - Get variable from PRef
- `test_pref_index` - Array element reference

**B. Dependency Tests (4 tests)**
- `test_dep_creation` - Create dependency
- `test_dep_tracking` - Track data flow
- `test_dep_graph_construction` - Build dep graph
- `test_dep_cycle_detection` - Detect cycles

---

## Phase 4: Advanced Algebraic & Property-Based Testing (Weeks 7-8) ⭐ EXPANDED
**Target**: Group operations, pairings, advanced properties  
**Tests**: 50+ tests  
**Coverage Goal**: 50%+ → 60%+

### 4.1 Group Operation Properties (20 tests)

**G1 Point Addition (5 tests)**
- `test_add_g1_commutativity` - `P + Q = Q + P` via execution
- `test_add_g1_associativity` - `(P+Q)+R = P+(Q+R)` via execution
- `test_add_g1_identity` - `P + O = P` via execution
- `test_add_g1_inverse` - `P + (-P) = O` via execution
- `test_add_g1_property_based` - Property test with random G1 points

**G2 Point Addition (5 tests)**
- Same properties as G1 but for G2 points

**G1 Scalar Multiplication (5 tests)**
- `test_scalar_mul_g1_distributive_over_scalars` - `(a+b)*P = a*P + b*P`
- `test_scalar_mul_g1_distributive_over_points` - `a*(P+Q) = a*P + a*Q`
- `test_scalar_mul_g1_associativity` - `(a*b)*P = a*(b*P)`
- `test_scalar_mul_g1_zero` - `0*P = O`
- `test_scalar_mul_g1_one` - `1*P = P`

**G2 Scalar Multiplication (5 tests)**
- Same properties as G1 scalar multiplication but for G2

### 4.2 Pairing Properties (8 tests)

**Bilinearity (4 tests)**
- `test_pairing_bilinear_first_arg` - `e(a*P, Q) = e(P,Q)^a`
- `test_pairing_bilinear_second_arg` - `e(P, b*Q) = e(P,Q)^b`
- `test_pairing_bilinear_both` - `e(a*P, b*Q) = e(P,Q)^(a*b)`
- `test_pairing_bilinearity_property_based` - Property test

**Non-Degeneracy and Properties (4 tests)**
- `test_pairing_non_degenerate` - `e(G, H) ≠ 1` for generators
- `test_pairing_identity_left` - `e(O, Q) = 1`
- `test_pairing_identity_right` - `e(P, O) = 1`
- `test_pairing_sum` - `e(P+Q, R) = e(P,R) * e(Q,R)`

### 4.3 Advanced Vector Operations (12 tests)

**Inner Product Properties (5 tests)**
- `test_inner_product_commutativity` - `⟨v,w⟩ = ⟨w,v⟩`
- `test_inner_product_distributivity` - `⟨a*v+b*w, u⟩ = a*⟨v,u⟩ + b*⟨w,u⟩`
- `test_inner_product_scalar_homogeneous` - `⟨a*v, w⟩ = a*⟨v,w⟩`
- `test_inner_product_zero` - `⟨v, 0⟩ = 0`
- `test_inner_product_self_positive` - `⟨v, v⟩ ≥ 0` (if applicable)

**MSM Properties (7 tests)**
- `test_msm_equals_sum` - `MSM([a],[P]) = Σ aᵢ*Pᵢ`
- `test_msm_empty` - `MSM([], []) = O`
- `test_msm_single` - `MSM([a], [P]) = a*P`
- `test_msm_homomorphic_scalars` - `MSM(a+b, P) = MSM(a,P) + MSM(b,P)`
- `test_msm_homomorphic_points` - `MSM(a, P+Q) = MSM(a,P) + MSM(a,Q)`
- `test_msm_scalar_distributive` - `MSM(c*a, P) = c*MSM(a, P)`
- `test_msm_property_based` - Property test with random inputs

### 4.4 Property-Based Tests (10+ tests)

**Polynomial Properties**

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_polynomial_addition_commutative(
        p in arbitrary_polynomial(),
        q in arbitrary_polynomial()
    ) {
        assert_eq!(p.clone() + q.clone(), q + p);
    }
    
    #[test]
    fn prop_polynomial_addition_associative(
        p in arbitrary_polynomial(),
        q in arbitrary_polynomial(),
        r in arbitrary_polynomial()
    ) {
        assert_eq!((p.clone() + q.clone()) + r.clone(), 
                   p + (q + r));
    }
    
    #[test]
    fn prop_polynomial_distributive(
        p in arbitrary_polynomial(),
        q in arbitrary_polynomial(),
        r in arbitrary_polynomial()
    ) {
        assert_eq!(p.clone() * (q.clone() + r.clone()),
                   p.clone() * q + p * r);
    }
}
```

**Property Tests to Add**:
1. Polynomial commutativity (p+q == q+p)
2. Polynomial associativity ((p+q)+r == p+(q+r))
3. Polynomial distributivity (p*(q+r) == p*q + p*r)
4. Zero identity (p+0 == p)
5. Degree monotonicity (deg(p*q) <= deg(p)+deg(q))
6. Monomial LCM commutativity
7. Monomial GCD divides both
8. Division consistency
9. Type equality reflexivity
10. Subtype transitivity

---

## Implementation Strategy

### Week-by-Week Breakdown

**Week 1**: Graph Operations Foundation + Algebraic Properties
- Days 1-2: Arithmetic tests (add, sub, mul, div) + basic type checking
- Day 3: Scalar field algebraic properties (commutativity, associativity, identity, inverse)
- Day 4: Distributivity and mixed scalar operations
- Day 5: Vector algebraic properties
- **Deliverable**: 28 tests (10 basic + 18 algebraic), ~12% → 18% coverage

**Week 2**: Graph Operations Complete + Nodes  
- Days 1-2: Cross-type algebraic properties (scalar*G1, MSM homomorphic)
- Day 3: Cryptographic operations (pairing basic, commit, hash)
- Days 4-5: Node construction, manipulation, and queries
- **Deliverable**: 37 tests total (65 cumulative), 18% → 24% coverage

**Week 3**: Nodes Complete + Backend Types Start
- Days 1-2: Node manipulation, annotations, and integration
- Days 3-5: Backend type construction, composites, and operations
- **Deliverable**: 25 tests (90 cumulative), 24% → 32% coverage

**Week 4**: Backend Types + Polynomials
- Days 1-2: Type operations and checking
- Days 3-5: Polynomial construction and operations
- **Deliverable**: 30 tests (120 cumulative), 32% → 40% coverage

**Week 5**: Monomials + Runtime Start
- Days 1-2: Monomial operations
- Days 3-5: Runtime basic execution
- **Deliverable**: 20 tests (140 cumulative), 40% → 47% coverage

**Week 6**: Runtime Integration + Core Property Tests
- Days 1-3: Runtime integration tests
- Days 4-5: Core property-based tests setup
- **Deliverable**: 20 tests (160 cumulative), 47% → 52% coverage

**Week 7**: Advanced Algebraic Properties ⭐ NEW
- Days 1-2: Group operation properties (G1, G2 addition and scalar mul)
- Days 3-4: Pairing bilinearity tests
- Day 5: Vector and inner product properties
- **Deliverable**: 28 tests (188 cumulative), 52% → 56% coverage

**Week 8**: MSM Properties + Expanded Property Tests ⭐ NEW
- Days 1-2: MSM linearity and homomorphic properties
- Days 3-5: Expanded property-based tests across all types
- **Deliverable**: 22+ tests (210+ cumulative), 56% → 60%+ coverage

### Testing Infrastructure Setup

**Test Utilities** (`graph/src/test_utils.rs`):
```rust
pub fn arbitrary_polynomial() -> impl Strategy<Value = SparsePolynomial>;
pub fn arbitrary_monomial() -> impl Strategy<Value = Monomial>;
pub fn arbitrary_type() -> impl Strategy<Value = Type>;
pub fn simple_graph() -> Graph;
pub fn create_prover_input(value: Fp) -> NodeIndex;
pub fn assert_polynomial_equal(p: &Poly, q: &Poly);
```

**Continuous Integration**:
```yaml
# .github/workflows/coverage.yml
- name: Check coverage threshold
  run: |
    COVERAGE=$(cargo llvm-cov --summary-only)
    if (( $COVERAGE < 40 )); then exit 1; fi
```

---

## Coverage Milestones

| Milestone | Coverage | Tests | Timeline |
|-----------|----------|-------|----------|
| Current | 19% | 102 | Week 0 |
| Phase 1 Complete | 32% | 192 | Week 2 |
| Phase 2 Complete | 40% | 237 | Week 4 |
| Phase 3 Complete | 52% | 277 | Week 6 |
| Algebraic Properties | 60%+ | 310+ | Week 8 |

### Critical Path Coverage

After completion:
- ✅ Graph Operations: 0% → 75%
- ✅ Graph Nodes: 0% → 70%
- ✅ Backend Types: 0% → 60%
- ✅ Sparse Polynomials: 0% → 70%
- ✅ Monomials: 0% → 80%
- ✅ Runtime: 0% → 50%
- ✅ Knowledge Analysis: 71% → 85%
- ✅ Groebner Buchberger: 33% → 60%

---

## Success Metrics

**Quantitative**:
- Coverage increase: 19% → 60%+
- Test count: 102 → 310+
- Files with 0% coverage: 14 → 2
- Critical modules tested: 4/8 → 8/8
- **Algebraic properties verified**: 80+ ⭐ NEW

**Qualitative**:
- All arithmetic operations validated
- All cryptographic primitives tested
- Type system correctness verified
- End-to-end protocols working
- Property-based tests catching edge cases
- **Mathematical correctness proven through execution** ⭐ NEW
- **Semantic properties documented through tests** ⭐ NEW

---

## Tools and Automation

### Scripts

**Generate Test Skeleton**:
```bash
#!/bin/bash
# scripts/generate_test.sh CRATE MODULE FUNCTION
./scripts/generate_test.sh graph op add
```

**Coverage Report**:
```bash
#!/bin/bash
# scripts/coverage.sh
cargo llvm-cov --lib --html
xdg-open target/llvm-cov/html/index.html
```

**Run Tests by Phase**:
```bash
cargo test --test phase1_graph_ops
cargo test --test phase2_types_polys  
cargo test --test phase3_runtime
cargo test --lib proptest
```

### Benchmarking

```rust
// benches/groebner_bench.rs
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_buchberger(c: &mut Criterion) {
    c.bench_function("buchberger_small", |b| {
        b.iter(|| /* benchmark */);
    });
}

criterion_group!(benches, bench_buchberger);
criterion_main!(benches);
```

---

## Risk Mitigation

**Risks**:
1. Tests take longer than estimated
2. Uncovered complexity in modules
3. CI/CD failures
4. Test maintenance burden

**Mitigations**:
1. Start with high-impact tests first
2. Parallel development (multiple phases)
3. Incremental integration
4. Good test documentation
5. Property tests reduce manual test count

---

## Maintenance Plan

**After Initial Push**:
- Add test for every bug fix
- Require tests for new features
- Monthly coverage review
- Quarterly refactoring of test utilities
- Annual property test expansion

**Documentation**:
- Tests serve as usage examples
- Link tests to documentation
- Keep test plan updated

---

## Expected Outcomes

**By Week 8** ⭐ UPDATED:
- ✅ 60%+ coverage (from 19%)
- ✅ 310+ tests (from 102)
- ✅ All critical paths tested
- ✅ Property tests running
- ✅ CI/CD enforcing coverage
- ✅ Reduced bug count
- ✅ Faster development velocity
- ✅ Confident refactoring capability
- ✅ **80+ algebraic properties verified** ⭐ NEW
- ✅ **Mathematical correctness proven** ⭐ NEW
- ✅ **Semantic tests as executable specification** ⭐ NEW

**Long-term Benefits**:
- Regression prevention
- Documentation through tests
- Onboarding aid for new developers
- Foundation for fuzzing
- Performance tracking via benchmarks

---

**Total Effort**: ~320 hours  
**Timeline**: 8 weeks  
**ROI**: Very High - Foundation for reliable, maintainable codebase with **proven mathematical correctness** ⭐

**Key Innovation**: Algebraic property tests validate that graph operations not only compile correctly but **execute correctly** according to mathematical laws. This provides unprecedented confidence in the semantic correctness of the Zippel language.

**See Also**: 
- [ALGEBRAIC_PROPERTY_TESTS.md](./ALGEBRAIC_PROPERTY_TESTS.md) - Detailed algebraic test specifications
- [TEST_COVERAGE_REPORT.md](./TEST_COVERAGE_REPORT.md) - Current coverage analysis
- [UNTESTED_CRITICAL_FUNCTIONS.md](./UNTESTED_CRITICAL_FUNCTIONS.md) - Priority untested functions
