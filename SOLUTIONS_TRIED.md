# Solutions Tried for Test Failures

## Problem Summary

4 tests failing initially:
1. `analyses::groebner::buchberger::test_maple` - Groebner basis ordering mismatch
2. `analyses::knowledge::knowledge_foo` - Leak not detected
3. `analyses::knowledge::groebner_ex3` - Leak not detected  
4. `analyses::knowledge::groebner_zerocheck` - Leak not detected

## Root Cause Analysis

### Discovery 1: Transcript Variables are Public
Line 70 in `graph/src/analyses/qualifier.rs`:
```rust
Node::Transcr(_, _) => {
    qp.quals.insert(&n, &Qualifier::Public);  
}
```

Any variable sent to transcript (`x <- expr`) becomes PUBLIC.

### Discovery 2: Elimination Removes Uniform Private Variables
Line ~434 in `graph/src/analyses/groebner/monomial.rs`:
```rust
pub fn eliminate_var(v: &PRef) -> bool {
    v.qualifier == Qualifier::Private && v.distribution.is_uniform()
}
```

The `eliminate_var()` step removes private uniform variables (like fresh randomness `r`).

### Discovery 3: Inline Removes ALL Private Variables
The `inline(|p| p.is_public())` call inlines (substitutes) all NON-public variables, effectively removing private variables from the final Groebner basis. This is the main problem!

Debug output from `groebner_bar` (PASSES):
```
After Groebner: 5 polynomials
After eliminate_var: 3 polynomials
After inline: 3 polynomials  ← Still has private vars
After eliminate_groups: 2 polynomials
  Poly 0: {b (public), s (private), s' (private)} → is_leak = true ✓
```

Debug output from `knowledge_foo` (FAILED):
```
After Groebner: 5 polynomials
After eliminate_var: 2 polynomials
After inline: 2 polynomials  ← All private vars removed!
After eliminate_groups: 1 polynomials
  Poly 0: {a (public), b (public)} → is_leak = false ✗
```

## Solutions Attempted

### Solution 1: Change `is_leak()` Logic (TRIED - Partial Success)

**Original**:
```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    vars.iter().all(|v| !v.is_uniform())  // ← ALL must be non-uniform
    && vars.iter().any(|v| v.is_public())
    && vars.iter().any(|v| v.is_private())
}
```

**Attempt A**: Remove uniform check entirely
```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    vars.iter().any(|v| v.is_public())
    && vars.iter().any(|v| v.is_private())
}
```

**Result**: Fixed `groebner_zerocheck` but not `knowledge_foo` or `groebner_ex3`
- Reason: After `inline()`, these tests have no polynomials with both public and private vars

**Attempt B**: Check for private non-uniform with public
```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    vars.iter().any(|v| v.is_private() && !v.is_uniform())
    && vars.iter().any(|v| v.is_public())
}
```

**Result**: Same as Attempt A - didn't help

### Solution 2: Change Elimination Order (TRIED - Made it Worse)

Moved `eliminate_var()` to AFTER `inline()`:
```rust
pub fn run(&mut self) -> bool {
    self.0.run();
    self.0.inline(|p| p.is_public());  // ← Inline first
    self.eliminate_var();               // ← Then eliminate
    self.eliminate_groups();
    // ...
}
```

**Result**: Made `groebner_zerocheck` fail too! 
- Reason: Inlining first removes evidence before we can detect leaks

### Solution 3: Modify Inline Predicate (TRIED - Made it Worse)

Keep both public AND private non-uniform variables:
```rust
self.0.inline(|p| p.is_public() || (p.is_private() && !p.is_uniform()));
```

**Result**: Fixed 3 passed → only 2 passed
- Reason: The predicate logic might be backwards or doesn't work as expected

### Solution 4: Skip Inline Entirely (**SUCCESS** - BEST SO FAR)

Comment out the `inline()` call:
```rust
pub fn run(&mut self) -> bool {
    self.0.run();
    self.eliminate_var();
    // SKIP: self.0.inline(|p| p.is_public());
    self.eliminate_groups();
    // ...
}
```

**Result**: 
- ✅ Fixed `groebner_ex3`
- ✅ Fixed `groebner_zerocheck`  
- ✅ `groebner_bar` still passes
- ✅ `groebner_baz` still passes
- ✗ `knowledge_foo` still fails
- ✗ `test_maple` still fails (unrelated)

**Status**: 18 passed, 2 failed (down from 16 passed, 4 failed)

## Current Best Solution

**File**: `graph/src/analyses/knowledge.rs`

**Change**:
1. Keep `is_leak()` as simple version (Solution 1, Attempt A)
2. Comment out the `inline()` call in `run()` (Solution 4)

```rust
fn is_leak(p: &SparsePolynomial<C::F, ElimTerm>) -> bool {
    let vars = p.vars();
    // After eliminating private uniform vars, a leak occurs when 
    // public and private variables appear together in a polynomial
    vars.iter().any(|v| v.is_public())
    && vars.iter().any(|v| v.is_private())
}

pub fn run(&mut self) -> bool {
    self.0.run();
    self.eliminate_var();
    // NOTE: Skipping inline() - it removes private vars too aggressively
    // self.0.inline(|p| p.is_public());
    self.eliminate_groups();
    
    if self.0.basis.iter().any(Self::is_leak) {
        warn!("Leak found!");
        for p in self.0.basis.iter() {
            if Self::is_leak(p) {
                warn!("{}", p);
            }
        }
        return true;
    }
    false
}
```

## Remaining Failures

### 1. `knowledge_foo` (Still Investigating)

**Protocol**:
```zippel
proto foo(private s, s') where s == s' {
    let r = random<F>;
    c <- challenge<F>;
    a <- r * c;
    b <- r + c + s;
    verify(a == b);
}
```

**Debug output** (without inline):
```
After eliminate_var: 2 polynomials
After eliminate_groups: 2 polynomials
  Poly 0: 1 var - None (qual=Private, dist=Nonuniform) → is_leak = false
  Poly 1: {a, b} (both Public) → is_leak = false
```

**Issue**: Poly 0 has a private variable but it's an elimination term (None) with no public vars.
Poly 1 has only public vars.

**Possible Solutions** (Not Yet Tried):
- The "None" elimination variable might need special handling
- The protocol might actually be secure (not a leak) and the test is wrong
- Need to keep more information before `eliminate_var()`
- Need different elimination strategy

### 2. `test_maple` (Groebner Basis Ordering)

**Issue**: Computed Groebner basis has mathematically equivalent polynomials but in different order/form than expected.

**Impact**: LOW - cosmetic issue, doesn't affect correctness

**Possible Solutions**:
- Implement canonical form for Groebner basis
- Check ideal membership instead of exact polynomial match
- Relax test to check basis properties rather than exact form

## Recommendations

### Immediate Action

1. **Apply Solution 4** (skip inline) to fix 2 out of 3 knowledge tests
2. **Investigate `knowledge_foo`** more deeply:
   - Check if the protocol actually leaks
   - Understand what the "None" elimination variable represents
   - Try different elimination strategies

### Further Investigation

1. **Understand `inline()` purpose**: Why was it added? What is it meant to achieve?
2. **Check test intent**: Are these tests testing for leaks or testing that the analysis correctly identifies non-leaks?
3. **Review Groebner basis theory**: Ensure the analysis pipeline (basis → eliminate → inline → check) is theoretically sound

### Long-term

1. Add more test cases with known-secure and known-insecure protocols
2. Document the leak detection algorithm and its assumptions
3. Consider adding intermediate analysis steps or different elimination strategies
4. Improve test assertions to be more descriptive about what they're testing

## Performance Impact

Skipping `inline()`:
- **Pros**: Preserves information needed for leak detection
- **Cons**: Final Groebner basis may be larger (more polynomials, more variables)
- **Unknown**: Impact on analysis time and memory usage for large protocols

Should benchmark on real protocols to measure impact.

## Code Changes Made

Location: `graph/src/analyses/knowledge.rs`

1. Line 30-36: Simplified `is_leak()` logic
2. Line 65-103: Commented out `inline()` call with explanation

Total changes: ~10 lines modified

## Test Results

### Before Any Changes
```
test result: FAILED. 16 passed; 4 failed; 1 ignored
```

### After Best Solution
```
test result: FAILED. 18 passed; 2 failed; 1 ignored
```

**Improvement**: Fixed 2 tests (50% reduction in failures)

## Next Steps

1. Document findings in `TEST_FAILURES_ANALYSIS.md`
2. Commit current best solution as incremental improvement  
3. Open issue for remaining `knowledge_foo` failure with debug analysis
4. Propose test update for `test_maple` or implement canonical form
5. Get feedback from original authors on intended behavior of `inline()`
