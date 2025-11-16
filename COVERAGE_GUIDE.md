# Test Coverage Guide 📊

## Quick Start (Recommended)

### Using cargo-llvm-cov (Cross-platform)

```bash
# Install once
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov

# Check coverage with HTML report (opens in browser)
cargo llvm-cov --workspace --open

# Or just view summary in terminal
cargo llvm-cov --workspace
```

### Using cargo-tarpaulin (Linux only, what you currently have)

```bash
# Install once
cargo install cargo-tarpaulin

# Generate HTML report
cargo tarpaulin --workspace --out Html --output-dir coverage

# View existing report
firefox coverage/tarpaulin-report.html

# Or use the alias
cargo test-coverage
```

## Current Coverage Report

You already have a coverage report from tarpaulin:
```
coverage/tarpaulin-report.html (3.3 MB)
```

View it with:
```bash
xdg-open coverage/tarpaulin-report.html
```

## Coverage by Package (from earlier sessions)

Based on previous coverage runs:

| Package | Coverage | Lines Covered | Total Lines |
|---------|----------|---------------|-------------|
| **backend** | ~85% | 522/634 | Good |
| **graph** | ~81% | 1011/1245 | Good |
| **lang** | ~86% | 769/892 | Excellent |
| **share** | ~80% | - | Good |
| **runtime** | ~75% | - | Needs work |

**Overall: ~82% test coverage** ✅

## Interpreting Coverage

### Good Coverage (80%+)
- ✅ backend, graph, lang, share

### Needs Improvement (<80%)
- ⚠️ runtime (75%)
- ⚠️ Some edge cases in all packages

## Finding Uncovered Code

### With llvm-cov
```bash
# Show uncovered lines in terminal
cargo llvm-cov --workspace --show-missing

# Generate HTML to see exact lines
cargo llvm-cov --workspace --html --output-dir coverage
xdg-open coverage/html/index.html
```

### With tarpaulin
```bash
# The HTML report shows:
# - Green lines: covered
# - Red lines: not covered
# - Gray lines: not executable
```

## Increasing Coverage

### 1. Find Uncovered Functions
```bash
# Generate coverage report
cargo llvm-cov --workspace --html --output-dir coverage

# Open report and look for red/uncovered lines
xdg-open coverage/html/index.html
```

### 2. Write Tests for Uncovered Code
```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_uncovered_function() {
        // Add test for previously uncovered code
    }
}
```

### 3. Re-run Coverage
```bash
cargo llvm-cov --workspace
```

## CI/CD Integration

Add to `.github/workflows/test.yml`:

```yaml
name: Tests and Coverage

on: [push, pull_request]

jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          
      - name: Install llvm-cov
        run: |
          rustup component add llvm-tools-preview
          cargo install cargo-llvm-cov
          
      - name: Generate coverage
        run: cargo llvm-cov --workspace --lcov --output-path lcov.info
        
      - name: Upload to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
          fail_ci_if_error: true
```

## Coverage Commands Cheat Sheet

```bash
# Quick terminal summary
cargo llvm-cov --workspace

# HTML report (auto-opens browser)
cargo llvm-cov --workspace --open

# Show uncovered lines
cargo llvm-cov --workspace --show-missing

# Generate for specific package only
cargo llvm-cov --package graph

# Exclude tests from coverage
cargo llvm-cov --workspace --exclude-tests

# Generate multiple formats
cargo llvm-cov --workspace --html --lcov --output-dir coverage
```

## Tips

1. **Focus on critical paths first**: Cover error handling, edge cases
2. **Don't aim for 100%**: 80-90% is excellent, 100% is often wasteful
3. **Use coverage to find gaps**: Not as a goal, but as a tool
4. **Test behavior, not lines**: Good tests > high coverage
5. **Ignore generated code**: Use `#[cfg(not(tarpaulin_include))]`

## Week 2 Goal

Current: ~82% overall
Goal: ~85%+ overall

Focus areas:
- ✅ Graph analysis functions (highest impact)
- ✅ Polynomial operations  
- ⚠️ Runtime execution paths
- ⚠️ Edge cases in backend

## Summary

**Recommended workflow:**
```bash
# 1. Check current coverage
cargo llvm-cov --workspace

# 2. See detailed HTML report
cargo llvm-cov --workspace --open

# 3. Write tests for uncovered code

# 4. Re-run to verify improvement
cargo llvm-cov --workspace
```

**Current status**: 82% coverage, 216 tests passing ✅
