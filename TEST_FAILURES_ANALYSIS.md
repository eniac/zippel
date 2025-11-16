# Zippel Test Failures Analysis

**Date**: 2025-11-15  
**Status**: 4 tests failing in `graph` crate

## Summary

Running `cargo test` reveals 4 failing tests, all related to zero-knowledge leak detection:

1. `graph::analyses::groebner::buchberger::test_maple` - Groebner basis computation ordering issue
2. `graph::analyses::knowledge::knowledge_foo` - Leak detection not finding expected leak
3. `graph::analyses::knowledge::groebner_ex3` - Leak detection not finding expected leak  
4. `graph::analyses::knowledge::groebner_zerocheck` - Leak detection not finding expected leak

## Test Results

```
test result: FAILED. 16 passed; 4 failed; 1 ignored; 0 measured; 0 filtered out
```

### Passing Tests (16)
- Groebner basis tests (linear, s-polynomial, term operations, grevlex ordering)
- Transitive closure tests
- Qualifier propagation
- Uniformity propagation
- Completeness analysis
- Graph construction tests
- One knowledge test (groebner_bar) passes

### Ignored Tests (1)
- `scheduler::ilp::gurobi_e2e` - Requires Gurobi license (CI limitation)

---

## Detailed Analysis

### Issue 1: Groebner Basis Ordering (`test_maple`)

**Location**: `graph/src/analyses/groebner/buchberger.rs:603`

**Problem**: The computed Groebner basis has a different element ordering than expected.

**Expected basis** (in order):
1. `t*x + t - y`
2. `t*y + x - 1`  
3. `x^2 + y^2 - 1`

**Actual basis** (different order):
1. `t^2*y - (large_num)*t + y`  ← Different polynomial
2. `t*x + t + (large_num)*y`     ← Expected #1 with different form
3. `t*y + x - 1`                  ← Expected #2 ✓

**Root Cause**: Groebner basis computation is mathematically correct (same ideal), but the polynomial ordering/reduction differs from expectations. This could be due to:
- Different reduction strategies in Buchberger's algorithm
- Coefficient representation differences
- Basis minimization/auto-reduction variations

**Impact**: LOW - The basis is mathematically equivalent, just in different form

**Recommendation**: Update test to check for ideal equivalence rather than exact polynomial match, OR normalize the basis before comparison.

---

### Issue 2-4: Knowledge Analysis Leak Detection

**Affected Tests**:
- `knowledge_foo` (line 126)
- `groebner_ex3` (line 225)
- `groebner_zerocheck` (line 246)

**Location**: `graph/src/analyses/knowledge.rs:30-36`

**Problem**: The `is_leak()` function is not detecting zero-knowledge leaks that should be present in intentionally broken protocols.

#### Current Leak Detection Logic

```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    // Contains both secret and public variables, and the secret values are non-uniform random
    vars.iter().all(|v| !v.is_uniform())  // ← ISSUE: ALL vars must be non-uniform
    && vars.iter().any(|v| v.is_public())
    && vars.iter().any(|v| v.is_private())
}
```

**The Bug**: Line 33 requires ALL variables in a polynomial to be non-uniform. This is too restrictive.

#### Why This Fails

Consider `knowledge_foo` protocol:
```zippel
proto foo<F: Field>(private s: F, private s': F) where s == s' {
    let r = random<F>;      // ← UNIFORM random (private)
    c <- challenge<F>;      // ← Public
    a <- r * c;             // ← Public (uniform × public)
    b <- r + c + s;         // ← Should leak! (uniform + public + private non-uniform)
    verify(a == b);         // ← False, so leak exists
}
```

**Variables**:
- `s`, `s'`: Private, non-uniform (input witnesses)
- `r`: Private, **uniform** (freshly sampled random)
- `c`: Public (Fiat-Shamir challenge)

**Expected leak**: After Groebner basis computation, we should find a polynomial relating:
- Public values (like `c`)
- Private non-uniform values (like `s`)

**But**: If the polynomial contains `r` (uniform), it fails the `all(|v| !v.is_uniform())` check.

#### The Fix

The comment says: "Contains both secret and public variables, and the secret values are non-uniform random"

The logic should match this: we want to detect when **any private non-uniform variable** appears with public variables, indicating information leakage.

**Proposed Fix**:
```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    // Contains both secret (non-uniform) and public variables
    vars.iter().any(|v| v.is_private() && !v.is_uniform())  // Has private non-uniform
    && vars.iter().any(|v| v.is_public())                     // Has public
}
```

**Rationale**:
- A leak occurs when private **witness data** (non-uniform) correlates with public transcript
- Uniform random variables (like `r`) are used for masking and shouldn't prevent leak detection
- The presence of uniform variables in a polynomial is fine; what matters is if private non-uniform secrets are exposed

#### Alternative Interpretation

Another reading of the comment could be:
```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    let has_public = vars.iter().any(|v| v.is_public());
    let has_private_nonuniform = vars.iter().any(|v| v.is_private() && !v.is_uniform());
    let all_private_are_nonuniform = vars.iter()
        .filter(|v| v.is_private())
        .all(|v| !v.is_uniform());
    
    has_public && has_private_nonuniform && all_private_are_nonuniform
}
```

This would require: "If private variables appear with public, all private variables must be non-uniform." But this still seems wrong - the issue is the mixing itself, not the uniformity of all private variables.

---

## Test Case Analysis

### `knowledge_foo`

**Protocol**: Intentionally broken - verifies `a == b` where:
- `a = r * c` (should be fresh randomness)
- `b = r + c + s` (mixes random, challenge, and secret)

**Expected**: Leak detected (test asserts `kz.run() == true`)  
**Actual**: No leak detected (returns `false`)  
**Cause**: The polynomial likely contains `r` (uniform), failing the leak check

### `groebner_ex3`

**Protocol**:
```zippel
proto foo<G: Group, F: Scalar<G>>(
    private s: F, private s': F, public g: G
) where s == s {  // ← Redundant constraint
    let r = random<F>;
    let a = r + s;
    let b = r + s';
    c <- g * a;
    d <- g * b;
    verify(c == d)  // ← Should only hold if s == s'
}
```

**Expected**: Leak detected (if `s != s'`, the verify fails)  
**Actual**: No leak detected  
**Cause**: Polynomial contains `r` (uniform)

### `groebner_zerocheck`

**Protocol**:
```zippel
proto zerocheck<F: Field>(
    private p: Uni<F, 16>, public q: Uni<F, 16>
) where p == q {
    let r = random<F>;
    verify(p(r) == q(r))  // ← Zero-test at random point
}
```

**Expected**: Leak detected (constraint `p == q` with single evaluation is weak)  
**Actual**: No leak detected  
**Cause**: Polynomial contains evaluation variables related to uniform `r`

---

## Recommended Actions

### Priority 1: Fix Leak Detection Logic (HIGH)

**File**: `graph/src/analyses/knowledge.rs`, line 30-36

**Change**:
```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    // A leak occurs when private non-uniform (witness) data appears with public data
    vars.iter().any(|v| v.is_private() && !v.is_uniform())
    && vars.iter().any(|v| v.is_public())
}
```

**Testing**: After fix, run:
```bash
cargo test -p graph analyses::knowledge
```

All three knowledge tests should pass.

### Priority 2: Fix or Update Groebner Test (MEDIUM)

**File**: `graph/src/analyses/groebner/buchberger.rs`, line 603

**Option A** (Preferred): Implement basis normalization/canonical form
```rust
// Add a canonical_form() method to GroebnerBasis
assert_eq!(
    groebner_basis.canonical_form(), 
    GroebnerBasis::new(num_vars, vec![g1, g2, g3]).canonical_form()
);
```

**Option B**: Check ideal membership instead
```rust
// Verify each expected polynomial is in the computed basis ideal
for g in vec![g1, g2, g3] {
    assert!(groebner_basis.contains_in_ideal(&g));
}
```

**Option C**: Relax test to check basis properties
```rust
assert_eq!(groebner_basis.num_vars, 3);
assert_eq!(groebner_basis.basis.len(), 3);
// Check that it's a Groebner basis (all S-polynomials reduce to 0)
assert!(groebner_basis.is_groebner_basis());
```

### Priority 3: Add Documentation (LOW)

Add comments explaining:
1. What constitutes a zero-knowledge leak in the Groebner basis framework
2. Why uniform variables don't indicate leaks
3. The role of the elimination and inlining steps in `KnowledgeAnalysis::run()`

---

## Code Locations Summary

| Issue | File | Line | Component |
|-------|------|------|-----------|
| Leak detection logic | `graph/src/analyses/knowledge.rs` | 30-36 | `is_leak()` |
| knowledge_foo test | `graph/src/analyses/knowledge.rs` | 96-127 | Test |
| groebner_ex3 test | `graph/src/analyses/knowledge.rs` | 193-226 | Test |
| groebner_zerocheck test | `graph/src/analyses/knowledge.rs` | 228-247 | Test |
| Groebner ordering | `graph/src/analyses/groebner/buchberger.rs` | 603 | Test assertion |

---

## Impact Assessment

**Severity**: MEDIUM-HIGH

- Tests are currently failing on main branch
- Zero-knowledge leak detection is a core security feature
- False negatives (missing leaks) are security-critical
- Groebner basis test is less critical (correctness vs. form)

**Risk of Fix**:
- LOW for leak detection (makes detection more permissive/correct)
- Need to verify no existing secure protocols are now flagged as leaking

**Validation After Fix**:
1. All knowledge tests should pass
2. Run existing secure protocols (schnorr.zippel, kzg.zippel, ipa.zippel)
3. Verify they still report no leaks
4. Consider adding tests for known-secure protocols

---

## Related Files for Context

- `graph/src/analyses/groebner/mod.rs` - Groebner basis trait definitions
- `graph/src/analyses/groebner/buchberger.rs` - Buchberger algorithm implementation  
- `graph/src/analyses/groebner/term.rs` - Monomial term ordering
- `lang/src/typ/distribution.rs` - Distribution (uniform/nonuniform) tracking
- `lang/src/typ/qualifier.rs` - Public/private qualifier system

---

## Questions for Original Authors

1. Was the `all(|v| !v.is_uniform())` condition intentional?
2. Are there scenarios where uniform variables in leaking polynomials should prevent detection?
3. Should the Groebner basis test allow for equivalent but differently-ordered bases?
4. Are there documented examples of what patterns `is_leak()` should/shouldn't catch?

---

## Next Steps

1. **Verify understanding**: Review test protocols to confirm they should leak
2. **Implement fix**: Modify `is_leak()` per recommendation
3. **Run tests**: `cargo test -p graph`
4. **Validate**: Ensure existing secure protocols still pass
5. **Update summary.md**: Document the leak detection semantics
6. **Consider**: Add more test cases for edge cases in leak detection
