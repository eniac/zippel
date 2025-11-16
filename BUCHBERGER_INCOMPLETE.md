# Buchberger Algorithm Incomplete S-Polynomial Generation

## Problem
The Buchberger algorithm in `graph/src/analyses/groebner/buchberger.rs` is not generating all necessary S-polynomials, causing `test_maple` to fail.

## Evidence

### Manual Trace (Expected)
For ideal `I = <t^2*y - 2*t + y, t^2*x + t^2 + x - 1>`:

1. Initial: `{f1, f2}`
2. After S(f1, f2): `{f1, f2, t*x + t - y}`
3. After S(f1, g1): `{f1, f2, g1, t*y + x - 1}`
4. After S(g1, g2): `{f1, f2, g1, g2, x^2 + y^2 - 1}` ← **SHOULD GENERATE THIS**
5. After reduction: `{t*x + t - y, t*y + x - 1, x^2 + y^2 - 1}`

### Actual Behavior
```
After Buchberger (before reduction):
  [0] t^2*y + (-2)*t + y
  [1] t^2*x + t^2 + x - 1
  [2] (-1)*t*x + (-1)*t + 2*y

After reduction:
  [0] t*x + t - y
  [1] t*y + x - 1
```

**Missing**: `x^2 + y^2 - 1`

## Root Cause Hypotheses

1. **Parallel Processing Issue**: Lines 195-239 use `par_iter()` to compute S-polynomials in parallel. The indices for new pairs (line 224: `k = g.len() - 1`) might be incorrect when multiple polynomials are added simultaneously.

2. **Critical Pair Selection**: The `skip_pair()` function (lines 252-274) implements Buchberger's criteria. It might be incorrectly skipping the pair that would generate `x^2 + y^2 - 1`.

3. **Premature Termination**: The algorithm might not be generating S-polynomials between newly added basis elements.

## Tests That Expose The Bug

- `test_maple`: Expects `{t*x+t-y, t*y+x-1, x^2+y^2-1}`, gets `{t*x+t-y, t*y+x-1}`
- `test_linear_elimination`: Gets different (but equivalent) basis
- `test_simple_square_elimination`: **PASSES** - simpler case works

## Proposed Fixes

### Option 1: Fix Index Calculation
Line 224 should be:
```rust
let k = g.len(); // Index where polynomial WILL be added
```
Not `g.len() - 1`.

### Option 2: Sequential S-Polynomial Generation
Replace `par_iter()` with sequential processing to avoid race conditions in index assignment.

### Option 3: Re-compute All Pairs After Adding
After adding new polynomials, explicitly recompute all critical pairs with ALL existing basis elements, not just those before the parallel batch.

### Option 4: Iterate Until Convergence
Keep computing S-polynomials until no new polynomials are generated (currently it only processes initial pairs).

## Next Steps

1. Add detailed logging to track which S-polynomials are computed
2. Verify that S(t*x+t-y, t*y+x-1) is being computed and what it reduces to
3. Check if Buchberger's criteria is skipping it incorrectly
4. Test with sequential (non-parallel) version to isolate parallelization issues
5. Compare with a reference implementation (Sage, Macaulay2)

## Impact

- **test_maple**: FAILS  
- **Knowledge analysis**: PASSES (uses simpler cases)
- **Real protocols**: Unknown - may hit this in complex scenarios

This is a correctness bug that needs to be fixed for the Groebner basis implementation to be complete.
