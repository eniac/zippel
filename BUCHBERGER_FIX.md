# Buchberger Algorithm Fix

## Problem
The `test_maple` test was failing because the Groebner basis algorithm was not correctly computing the elimination ideal. The test expected:
- g1: `t*x + t - y` (leading term: tx)
- g2: `t*y + x - 1` (leading term: ty)
- g3: `x^2 + y^2 - 1` (leading term: x^2)

But was getting a polynomial with leading term `t^2*y` instead of `x^2 + y^2 - 1`.

## Root Cause
When converting the Buchberger algorithm from parallel to sequential execution, a critical bug was introduced in how new critical pairs were generated.

The original parallel code computed new pairs for each S-polynomial independently:
```rust
let reduced_ps: Vec<(SparsePolynomial<F, T>, VecDeque<(usize, usize)>)> = ps
  .par_iter()  // Parallel iteration
  .filter_map(|&(i, j)| {
    // ... compute S-polynomial and reduce ...
    let k = g.len() - 1;  // WRONG when using sequential iteration!
    // ... generate pairs with index k ...
  }).collect();
```

When converted to sequential iteration (`.iter()` instead of `.par_iter()`), the value of `k` was computed before adding any polynomials to the basis. But then multiple polynomials could be added in a batch, making the computed indices incorrect for all but the first polynomial.

## Solution
Restructured the code to:
1. First collect all reduced S-polynomials (without pair generation)
2. Then add each polynomial to the basis one at a time
3. Generate new pairs using the correct index immediately after adding each polynomial

```rust
let reduced_ps: Vec<SparsePolynomial<F, T>> = ps
  .iter()
  .filter_map(|&(i, j)| {
    // ... compute and reduce S-polynomial ...
    // Return just the polynomial, not pairs
  }).collect();

// Add polynomials one at a time with correct index
for s_reduced in reduced_ps {
    let k = g.len(); // Correct index for the polynomial we're about to add
    g.push(s_reduced);
    
    // Generate pairs with the correct index k
    for l in 0..k {
        if !Self::skip_pair(l, k, &g, &seen) {
            pairs.push_back((l, k));
        }
    }
}
```

## Additional Changes
Also removed all parallel iteration from the Buchberger algorithm:
- Changed `.par_iter()` to `.iter()` in the main S-polynomial reduction loop
- Changed `.par_iter().find_any()` to `.iter().find()` in the polynomial reduction
- Changed `.into_par_iter().any()` to `.any()` in the Buchberger skip criteria

This ensures deterministic behavior and correctness, though it may be slower for large problems.

## Test Results
- `test_maple` now passes ✓
- All other tests continue to pass ✓
- The algorithm now correctly computes Groebner bases with elimination ordering
