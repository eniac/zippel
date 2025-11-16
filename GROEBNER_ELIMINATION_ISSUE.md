# Groebner Basis Elimination Test Failure Analysis

## Issue
`test_maple` fails because the Groebner basis computation with elimination ordering doesn't fully reduce to the expected minimal basis.

## Expected vs Actual

**Computed Basis**:
```
[0] t^2*y + (-2)*t + y
[1] t*x + t - y
[2] t*y + x - 1
```

**Expected Basis (from Maple)**:
```
[0] t*x + t - y
[1] t*y + x - 1  
[2] x^2 + y^2 - 1
```

## Analysis

### What's Correct
- Polynomials [1] and [2] match expected [0] and [1]
- The simple elimination test (`test_elim_reduction_simple`) passes
- The ordering implementation is correct (elimination vars ordered as smallest)

### What's Wrong
- Polynomial [0] has `t^2` term which should be eliminated
- Missing the polynomial `x^2 + y^2 - 1` which comes from further reduction

### Root Cause
The `reduce_groebner_basis()` function performs inter-reduction, but it's not sufficient for this case. The polynomial `t^2*y + (-2)*t + y` needs to be:

1. Reduced by `t*x + t - y` to eliminate `t` terms
2. Reduced by `t*y + x - 1` to eliminate remaining `t` terms  
3. This should yield `x^2 + y^2 - 1`

But this isn't happening, suggesting either:
- The reduction isn't iterating enough times
- The order of reductions matters and we're not doing them in the right order
- There's a bug in the `reduce()` function for elimination ordering

## Unit Tests Created

I've added two diagnostic tests:

1. **`test_elim_ordering_comparison`** - Verifies the elimination ordering
2. **`test_elim_reduction_simple`** - Tests simple t^2 elimination (PASSES)

## Next Steps

This requires deeper investigation into the Buchberger algorithm implementation:

1. Add detailed tracing to `reduce_groebner_basis()` to see which polynomials are being reduced
2. Compare step-by-step with Maple's Buchberger algorithm  
3. Possibly implement Gebauer-Möller optimization (standard for elimination)
4. Check if we need multiple passes of inter-reduction
5. Verify the `reduce()` function works correctly for elimination ordering

## Priority

Given that:
- The knowledge analysis (security-critical) is now fixed (3/4 tests passing)
- Simple elimination works (`test_elim_reduction_simple` passes)
- The issue is specifically with this complex Maple test case
- No real protocols are known to hit this issue

**Recommendation**: Medium priority. The Groebner basis algorithm works for most cases but needs refinement for complete elimination in complex scenarios.

## Workaround

For now, can either:
1. Mark `test_maple` as `#[ignore]` with TODO comment
2. Relax the test to check that computed basis generates the same ideal (weaker but valid)
3. Continue investigating the reduction algorithm

## Files Modified

- `graph/src/analyses/groebner/buchberger.rs` - Added tests: `test_elim_ordering_comparison`, `test_elim_reduction_simple`, debug output for `test_maple`

## Update: Iterative Reduction Implemented

Added iterative reduction to `reduce_groebner_basis()` which successfully eliminates the `t^2*y` term.

### What Works Now
- Iterative reduction properly eliminates polynomials that reduce to zero
- The problematic `t^2*y - 2t + y` now correctly reduces to zero in iteration 2

### What's Still Missing
The computed basis is:
- `t*x + t - y`
- `t*y + x - 1`

But expected (from Maple) includes:
- `t*x + t - y`
- `t*y + x - 1`
- `x^2 + y^2 - 1` ← **MISSING**

### Root Cause
The polynomial `x^2 + y^2 - 1` should be generated during the **Buchberger algorithm** phase (S-polynomial computation), NOT during reduction.

This means the Buchberger algorithm is terminating early or not generating all necessary S-polynomials. Specifically, the S-polynomial of `{t*x + t - y, t*y + x - 1}` should eventually reduce to `x^2 + y^2 - 1`.

### Next Investigation Needed
1. Trace S-polynomial generation in `buchberger()` function
2. Check if all critical pairs are being computed
3. Verify the criterion for adding polynomials to the basis  
4. May need to implement Gebauer-Möller criterion properly

The iterative reduction was a good fix and makes the algorithm more robust, but the missing polynomial indicates an issue earlier in the pipeline.
