# Test Coverage Analysis Report
**Generated**: 2025-11-15  
**Method**: Static analysis of public functions vs test functions

## Executive Summary

| Crate | Functions | Tests | Approx Coverage |
|-------|-----------|-------|-----------------|
| **Graph** | 237 | 21 | **8.86%** |
| **Lang** | 202 | 76 | **37.62%** |
| **Backend** | 85 | 5 | **5.88%** |
| **Runtime** | 7 | 0 | **0.00%** |
| **TOTAL** | **531** | **102** | **19.21%** |

## Critical Findings

### 🔴 **HIGH PRIORITY - Untested Core Modules**

#### 1. Graph Operations (`graph/src/op.rs`)
- **47 public functions, 0 tests**
- **Status**: CRITICAL - No test coverage
- Core operations include: `add`, `sub`, `mul`, `div`, `bin`, `concat`, `eval`, etc.
- **Recommendation**: Add integration tests for arithmetic and binary operations

#### 2. Graph Nodes (`graph/src/node.rs`)  
- **31 public functions, 0 tests**
- **Status**: CRITICAL - No test coverage
- Core node operations: `is_op`, `is_input`, `references`, `map_node_indices`, etc.
- **Recommendation**: Add tests for node manipulation and graph transformations

#### 3. Backend Types (`backend/src/types.rs`)
- **26 public functions, 0 tests**
- **Status**: HIGH - No test coverage
- Type constructors: `scalar`, `g1`, `g2`, `gt`, `vec`, `mle`, etc.
- **Recommendation**: Add tests for type construction and validation

#### 4. Runtime Module (`runtime/src/graph.rs`)
- **7 public functions, 0 tests**
- **Status**: HIGH - No test coverage  
- **Recommendation**: Add runtime execution tests

### 🟡 **MEDIUM PRIORITY - Partially Tested**

#### 1. Groebner Basis Module (11.9% coverage)

**Buchberger Algorithm** (`graph/src/analyses/groebner/buchberger.rs`)
- **15 functions, 5 tests** (~33% coverage)
- ✅ **Tested**:
  - `buchberger()` - S-polynomial generation
  - `reduce()` - Polynomial reduction
  - `s_poly()` - S-polynomial computation
  - Ordering comparisons (grevlex, elimination)
- ❌ **Untested**:
  - `eliminate_var()` - Variable elimination
  - `eliminate_monomial()` - Monomial elimination
  - `skip_pair()` - Buchberger criteria
  - `pairs_reduce()` - F4 reduction (placeholder)
  - `reduce_groebner_basis()` - Basis minimization (partially tested)

**Sparse Polynomials** (`graph/src/analyses/groebner/sparsepoly.rs`)
- **15 functions, 0 tests** (0% coverage)
- ❌ **Untested**:
  - `mul_by_term_and_scalar()` - Term multiplication
  - `isolate_elimination_vars()` - Variable isolation
  - `flat_map_vars()` - Variable mapping
  - `degree()`, `is_constant()` - Polynomial properties
  - Arithmetic operations (tested implicitly through buchberger)

**Monomial Operations** (`graph/src/analyses/groebner/monomial.rs`)
- **4 functions, 0 tests** (0% coverage)
- ❌ **Untested**:
  - `eliminate_var()` - Check if variable should be eliminated
  - `eliminate()` - Eliminate variables from monomial
  - Iterator implementations

#### 2. Knowledge Analysis (`graph/src/analyses/knowledge.rs`)
- **7 functions, 5 tests** (~71% coverage)
- ✅ **Well tested**: Core leak detection working
- ❌ **Could improve**: Edge cases, error handling

### 🟢 **GOOD COVERAGE**

#### 1. AST Expressions (`lang/src/ast/exp.rs`)
- **45 functions, 24 tests** (~53% coverage)
- Good parser test coverage
- Could add more semantic validation tests

#### 2. Lang Module Overall
- **202 functions, 76 tests** (~38% coverage)
- Best overall coverage among crates
- Strong parser and type system tests

## Detailed Module Breakdown

### Graph Crate (8.86% coverage)

#### Files with NO tests (10 files):

| File | Functions | Priority |
|------|-----------|----------|
| `op.rs` | 47 | 🔴 CRITICAL |
| `node.rs` | 31 | 🔴 CRITICAL |
| `sparsepoly.rs` | 17 | 🟡 MEDIUM |
| `pref.rs` | 16 | 🟡 MEDIUM |
| `dep.rs` | 10 | 🟡 MEDIUM |
| `groebner/mod.rs` | 9 | 🟡 MEDIUM |
| `scheduler/asymptotic_cost.rs` | 8 | 🟢 LOW |
| `monomial.rs` | 6 | 🟡 MEDIUM |
| `scheduler/local_scheduler.rs` | 2 | 🟢 LOW |
| `scheduler/mod.rs` | 2 | 🟢 LOW |

### Backend Crate (5.88% coverage)

#### Files with NO tests:
- **`types.rs`**: 26 functions - Type system core, needs comprehensive tests

### Runtime Crate (0% coverage)  

#### Files with NO tests:
- **`graph.rs`**: 7 functions - Runtime execution, needs integration tests

## Recommendations by Priority

### 🔴 **IMMEDIATE (Week 1-2)**

1. **Add Graph Operation Tests** (`graph/src/op.rs`)
   - Test arithmetic: `add`, `sub`, `mul`, `div`
   - Test logical: `and`, `or`, `not`, `bin`
   - Test collections: `concat`, `index`, `eval`
   - **Estimated**: 20-30 tests

2. **Add Graph Node Tests** (`graph/src/node.rs`)  
   - Test node construction and querying
   - Test graph transformations: `map_node_indices`
   - Test annotation handling
   - **Estimated**: 15-20 tests

3. **Complete Groebner Tests** (sparse polynomials)
   - Test `mul_by_term_and_scalar()`
   - Test `isolate_elimination_vars()`  
   - Test degree and constant checks
   - **Estimated**: 10-15 tests

### 🟡 **NEAR-TERM (Week 3-4)**

4. **Backend Type Tests** (`backend/src/types.rs`)
   - Test type construction
   - Test type equality and validation
   - Test vector and MLE types
   - **Estimated**: 15-20 tests

5. **Monomial Operation Tests**
   - Test elimination predicates
   - Test LCM, GCD operations
   - Test divisibility checks
   - **Estimated**: 8-10 tests

6. **PRef and Dep Tests**
   - Test reference creation and comparison
   - Test dependency tracking
   - **Estimated**: 10-15 tests

### 🟢 **LONG-TERM (Week 5+)**

7. **Runtime Integration Tests**
   - End-to-end protocol execution
   - Performance benchmarks
   - **Estimated**: 10-15 tests

8. **Scheduler Tests**
   - Cost estimation validation
   - Scheduling algorithm correctness
   - **Estimated**: 8-10 tests

9. **Increase Lang Coverage** (from 38% to 60%+)
   - More semantic validation tests
   - Error handling edge cases
   - **Estimated**: 30-40 tests

## Test Quality Metrics

### Current Test Distribution

```
Knowledge Analysis:  5 tests (71% coverage) ✅ GOOD
Groebner Buchberger: 5 tests (33% coverage) 🟡 FAIR
Lang AST:           24 tests (53% coverage) ✅ GOOD  
Lang Overall:       76 tests (38% coverage) 🟡 FAIR
Backend:             5 tests (6% coverage)  🔴 POOR
Runtime:             0 tests (0% coverage)  🔴 POOR
```

### Critical Path Coverage

Security-critical components:
- ✅ **Knowledge Analysis**: Well tested (5/5 tests passing)
- ✅ **Groebner Basis Core**: Basic tests (5/5 tests passing)
- ❌ **Graph Operations**: No coverage
- ❌ **Type System**: Minimal coverage

## Suggested Test Plan

### Phase 1: Foundation (2 weeks)
- [ ] Add 30 tests for graph operations
- [ ] Add 20 tests for graph nodes  
- [ ] Add 15 tests for sparse polynomials
- **Target**: Bring graph crate from 9% to 25% coverage

### Phase 2: Correctness (2 weeks)
- [ ] Add 20 tests for backend types
- [ ] Add 10 tests for monomial operations
- [ ] Add 15 tests for PRef/Dep
- **Target**: Backend crate from 6% to 30% coverage

### Phase 3: Integration (2 weeks)
- [ ] Add 15 runtime tests
- [ ] Add 10 scheduler tests
- [ ] Add 40 additional lang tests
- **Target**: Overall coverage from 19% to 40%+

## Coverage Goals

| Timeframe | Target Coverage | Focus Areas |
|-----------|----------------|-------------|
| **Current** | 19% | Knowledge analysis (done) |
| **1 Month** | 30% | Graph ops, nodes, polynomials |
| **2 Months** | 40% | Backend types, monomials |
| **3 Months** | 50%+ | Runtime, integration, lang |

## Notes

- Coverage percentages are **approximate** based on function count ratio
- Actual line coverage would require instrumentation (cargo-llvm-cov)
- Many functions are tested **indirectly** through integration tests
- Priority should be on **security-critical** paths first
- Consider adding **property-based tests** for polynomial operations

## Tools Used

- Static analysis of function definitions
- Test function counting
- Manual code inspection

For precise coverage, run:
```bash
cargo llvm-cov --lib --html
```
Then view `target/llvm-cov/html/index.html`
