# Polynomial Feature - Quick Reference

## Syntax

### Univariate Polynomials
```zippel
// Single variable, any degree
let p = fun x => x^5 + 3*x^3 + 2*x + 1;      // Type: Uni<F, 5>
let q = fun x => 2*x^2 + 5*x + 7;            // Type: Uni<F, 2>
let r = fun x => x + 1;                      // Type: Uni<F, 1>
```

### Multilinear Polynomials
```zippel
// Multiple variables, each term degree ≤ 1
let m1 = fun x, y => x*y + x + y;                    // Type: Mle<F, 2> ✓
let m2 = fun x, y, z => x*y + y*z + x*z;            // Type: Mle<F, 3> ✓
let m3 = fun a, b, c => a*b + b*c + a + b + c;      // Type: Mle<F, 3> ✓
```

### Invalid Examples
```zippel
// ❌ Not univariate, not multilinear
let bad1 = fun x, y => x^2*y + x*y^2;    // ERROR: degree > 1

// ❌ Variable x appears twice in term x*x*y
let bad2 = fun x, y => x*x*y;            // ERROR: not multilinear

// ❌ Mixed: x^2 has degree 2
let bad3 = fun x, y, z => x^2 + y*z;     // ERROR: not multilinear
```

## Rules

### Univariate (1 variable)
- ✅ Any degree N
- ✅ Can use powers: `x^5`, `x^100`, etc.
- ✅ Can mix terms: `x^3 + x^2 + x + 1`

### Multilinear (M variables)
- ✅ Each term has total degree ≤ 1
- ✅ Can multiply different variables: `x*y*z`
- ✅ Can add terms: `x*y + y*z + x*z`
- ❌ Cannot use powers > 1: `x^2` not allowed
- ❌ Cannot repeat variables in a term: `x*x` not allowed

## Type Inference

```zippel
// Univariate: infers degree automatically
fun x => x^3 + 2*x^2 + x      →  Uni<F, 3>
fun x => x + 5                →  Uni<F, 1>

// Multilinear: counts variables
fun x, y => x*y + x + y       →  Mle<F, 2>
fun x, y, z => x*y*z          →  Mle<F, 3>
```

## Common Operations

```zippel
// Evaluation
let p = fun x => x^2 + 2*x + 1;
let y = eval(p, 5);              // Evaluates p(5) = 36

// Coefficients
let coeffs = coef(p);            // Gets [1, 2, 1]

// FFT/IFFT (for univariate)
let p_eval = fft(p);
let p_coef = ifft(p_eval);

// MLE operations (for multilinear)
let m = mle([1, 2, 3, 4]);       // Create from evaluations
```

## Error Messages

When you try to create an unsupported polynomial:

```
PolyFunError: Polynomial function must be either univariate (1 variable) 
or multilinear (all terms degree 1):
    F, {} |- fun x, y => x^2 * y
    General M-variable, N-degree polynomials are not yet supported in the backend.
```

**Fix:** Make it either:
1. Univariate: `fun x => x^2 * c` (where c is constant)
2. Multilinear: `fun x, y => x * y` (no powers > 1)

## Examples

### Univariate Examples
```zippel
// Quadratic
let quadratic = fun x => x^2 + 2*x + 1;

// Cubic
let cubic = fun x => x^3 - 3*x^2 + 3*x - 1;

// High degree
let poly = fun x => x^10 + x^5 + 1;
```

### Multilinear Examples
```zippel
// Bilinear
let bilinear = fun x, y => x*y + 2*x + 3*y + 4;

// Trilinear  
let trilinear = fun x, y, z => x*y + y*z + x*z + x + y + z;

// Symmetric
let symmetric = fun x, y, z => x*y + x*z + y*z;
```

## Cheat Sheet

| Expression | Variables | Type | Valid? |
|------------|-----------|------|--------|
| `x^2 + 2*x + 1` | 1 | Uni<F,2> | ✓ |
| `x*y + x + y` | 2 | Mle<F,2> | ✓ |
| `x^2 * y` | 2 | - | ❌ Not multilinear |
| `x^5` | 1 | Uni<F,5> | ✓ |
| `x*y*z` | 3 | Mle<F,3> | ✓ |
| `x*x` | 1 | Uni<F,2> | ✓ (rewrites to x^2) |
| `x*x*y` | 2 | - | ❌ x appears twice |

## Testing

Run polynomial tests:
```bash
cargo test --lib poly_degree multilinear
```

Run all tests:
```bash
cargo test --lib
```

## Documentation

- **POLYNOMIAL_FEATURE_IMPLEMENTATION.md** - Full technical details
- **POLYNOMIAL_EXAMPLES.md** - Usage examples and patterns  
- **POLYNOMIAL_BACKEND_VALIDATION.md** - Validation algorithms
- **POLYNOMIAL_COMPLETE_SUMMARY.md** - Complete implementation summary
- **This file** - Quick reference
