# Testing Quick Start Guide

## For Developers: How to Add Tests

### Running Tests

```bash
# Run all tests
cargo test

# Run tests for specific crate
cargo test -p graph

# Run specific test
cargo test test_add_scalars

# Run tests with output
cargo test -- --nocapture

# Run tests in parallel (default)
cargo test -- --test-threads=4

# Generate coverage report
cargo llvm-cov --lib --html
# View: target/llvm-cov/html/index.html
```

### Test Template

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_function_name_basic() {
        // Arrange: Set up test data
        let input = create_test_input();
        
        // Act: Call the function
        let result = function_under_test(input);
        
        // Assert: Verify result
        assert_eq!(result, expected_value);
    }
    
    #[test]
    fn test_function_name_edge_case() {
        // Test boundary conditions
        let edge_input = EdgeCase::new();
        let result = function_under_test(edge_input);
        assert!(result.is_valid());
    }
    
    #[test]
    #[should_panic(expected = "error message")]
    fn test_function_name_error_case() {
        // Test error handling
        function_under_test(invalid_input);
    }
}
```

### Property-Based Test Template

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_function_maintains_invariant(
        input in arbitrary_input()
    ) {
        let result = function_under_test(input.clone());
        // Check invariant holds
        assert!(invariant_check(input, result));
    }
}

// Define input generator
fn arbitrary_input() -> impl Strategy<Value = InputType> {
    (0..100u32, 0..100u32)
        .prop_map(|(a, b)| InputType::new(a, b))
}
```

### Where to Add Tests

| Module | Test Location | Priority |
|--------|---------------|----------|
| `graph/src/op.rs` | `graph/src/op.rs` (bottom) or `graph/tests/op_tests.rs` | 🔴 Critical |
| `graph/src/node.rs` | `graph/src/node.rs` (bottom) or `graph/tests/node_tests.rs` | 🔴 Critical |
| `backend/src/types.rs` | `backend/src/types.rs` (bottom) | 🟡 High |
| `graph/src/analyses/groebner/` | Within each file or `graph/tests/groebner/` | 🟡 High |
| `runtime/src/` | `runtime/tests/` | 🟡 High |

### Test Naming Conventions

- `test_<function>_<scenario>` - Unit test
- `test_<module>_integration` - Integration test
- `prop_<property>` - Property-based test
- `bench_<operation>` - Benchmark

### Common Assertions

```rust
// Equality
assert_eq!(actual, expected);
assert_ne!(actual, unexpected);

// Boolean conditions
assert!(condition);
assert!(!condition);

// Floating point (use approx crate)
assert_relative_eq!(float1, float2, epsilon = 1e-10);

// Custom messages
assert_eq!(actual, expected, "Expected {} but got {}", expected, actual);

// Results
assert!(result.is_ok());
assert!(result.is_err());
assert_eq!(result.unwrap(), expected);

// Panics
assert!(panic::catch_unwind(|| dangerous_operation()).is_err());
```

### Test Organization

```
crate/
├── src/
│   ├── lib.rs          # May contain test module
│   ├── module.rs       # May contain test module at bottom
│   └── ...
├── tests/              # Integration tests
│   ├── integration_test.rs
│   └── ...
└── benches/            # Benchmarks
    └── benchmark.rs
```

### Coverage Goals by Module

| Module | Current | Week 2 | Week 4 | Week 6 |
|--------|---------|--------|--------|--------|
| Graph Ops | 0% | 50% | 70% | 75% |
| Graph Nodes | 0% | 40% | 60% | 70% |
| Backend Types | 0% | 20% | 50% | 60% |
| Polynomials | 0% | 30% | 60% | 70% |
| Runtime | 0% | 0% | 30% | 50% |

### Getting Started Checklist

- [ ] Pick a module from the test plan
- [ ] Read existing tests in that module
- [ ] Create test file or add to existing
- [ ] Write 3-5 tests:
  - [ ] Basic happy path test
  - [ ] Edge case test
  - [ ] Error handling test
- [ ] Run tests: `cargo test`
- [ ] Check coverage: `cargo llvm-cov`
- [ ] Submit PR with tests

### Example: Adding Test for `add` Operation

**File**: `graph/src/op.rs`

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::*;
    
    #[test]
    fn test_add_scalars() {
        // Create a simple graph
        let mut graph = Graph::new();
        
        // Create two scalar inputs
        let a = create_prover_input(&mut graph, Fp::from(5));
        let b = create_prover_input(&mut graph, Fp::from(3));
        
        // Add operation
        let result = Op::add(a, b);
        let result_node = graph.add_node(Node::Op(result));
        
        // Execute and verify
        let output = graph.execute();
        assert_eq!(output[result_node], Fp::from(8));
    }
    
    #[test]
    fn test_add_type_mismatch() {
        let mut graph = Graph::new();
        let scalar = create_prover_input(&mut graph, Fp::from(5));
        let g1_point = create_g1_input(&mut graph);
        
        // This should fail type checking
        let result = Op::add(scalar, g1_point);
        assert!(graph.type_check(&result).is_err());
    }
}
```

### Tips for Writing Good Tests

1. **Test One Thing** - Each test should verify one behavior
2. **Use Descriptive Names** - Name should describe what's being tested
3. **Arrange-Act-Assert** - Structure tests clearly
4. **Independent Tests** - Tests shouldn't depend on each other
5. **Fast Tests** - Keep tests fast (< 1 second each)
6. **Deterministic** - Tests should always produce same result
7. **Clean Up** - Clean up resources after tests

### Common Pitfalls

❌ **Don't**:
- Test implementation details
- Write flaky tests
- Ignore test failures
- Skip edge cases
- Copy-paste tests without understanding

✅ **Do**:
- Test behavior and contracts
- Keep tests deterministic
- Fix failures immediately  
- Test boundary conditions
- Understand what you're testing

### Resources

- [Test Plan](./COMPREHENSIVE_TEST_PLAN.md) - Detailed test strategy
- [Coverage Report](./TEST_COVERAGE_REPORT.md) - Current coverage status
- [Rust Testing Guide](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [Proptest Book](https://altsysrq.github.io/proptest-book/intro.html)
- [Criterion Benchmarking](https://bheisler.github.io/criterion.rs/book/)

### Questions?

- Check existing tests for examples
- Read the test plan for context
- Ask in team chat
- Pair program with someone experienced

---

**Remember**: Every test you write makes the codebase more reliable! 🎯
