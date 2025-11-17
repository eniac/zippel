# Polynomial Feature Examples

This document demonstrates the new polynomial syntax features in Zippel.

## Example 1: Univariate Polynomial

Before (using poly command):
```zippel
// Define polynomial 1 + 2x + 3x^2 using coefficient vector
let p = poly([1, 2, 3]);
```

After (using fun syntax):
```zippel
// Define the same polynomial using function syntax
let p = fun x => 1 + 2*x + 3*x^2;
```

## Example 2: Multivariate Polynomial

```zippel
// Quadratic form: x^2 + xy + y^2
let quadratic = fun x, y => x^2 + x*y + y^2;

// Bilinear form: 2*x*y + 3*x*z
let bilinear = fun x, y, z => 2*x*y + 3*x*z;
```

## Example 3: Type Annotations

```zippel
// Explicitly typed polynomial
let p: Poly<F, 2, 3> = fun x, y => x^3 + x^2*y + x*y^2 + y^3;
// This is a polynomial of 2 variables (x, y) with degree at most 3

// Univariate polynomial (backward compatible)
let q: Uni<F, 5> = fun x => x^5 + 2*x^3 + x;

// Multilinear polynomial (backward compatible)
let r: Mle<F, 3> = fun x, y, z => x*y + y*z + x*z;
```

## Example 4: Complex Expressions

```zippel
// Nested polynomial definition
let outer = fun x => {
    let inner = fun y => x*y + y^2;
    inner
};

// Polynomial composition
let f = fun x => x^2 + 1;
let g = fun x => 2*x;
// Can evaluate f(g(x)) = (2x)^2 + 1 = 4x^2 + 1
```

## Example 5: Integration with Existing Features

```zippel
// Using polynomial in a protocol
proto polynomial_commitment<F: Field>(
    private polynomial: Poly<F, 1, 10>,
    public point: F
) where eval(polynomial, point) == commitment {
    // Define a polynomial using fun syntax
    let p = fun x => x^3 + 2*x^2 + 3*x + 4;
    
    // Evaluate at a point
    let y = eval(p, point);
    
    // Verify the evaluation
    verify(y == commitment);
}
```

## Type System Examples

```zippel
// General polynomial type
Poly<F, M, N>  // M variables, degree N

// Special cases (still supported)
Uni<F, N>      // Equivalent to polynomial with 1 variable
Mle<F, M>      // Multilinear (degree 1) polynomial with M variables

// Vector of polynomials
[Poly<F, 2, 3>; 5]  // Array of 5 polynomials, each with 2 vars and degree 3

// Field element (scalar)
F  // Base field element
```

## Comparison: Before and After

### Before: Coefficient-based approach
```zippel
// Had to work with coefficient vectors
let p_coeffs = [1, 2, 3, 4, 5];  // represents 1 + 2x + 3x^2 + 4x^3 + 5x^4
let p = poly(p_coeffs);
let y = eval(p, 2);  // evaluate at x=2
```

### After: Function-based approach  
```zippel
// Can write polynomials naturally
let p = fun x => 1 + 2*x + 3*x^2 + 4*x^3 + 5*x^4;
let y = eval(p, 2);  // evaluate at x=2
```

## Advanced Examples

### Symmetric Polynomials
```zippel
// Elementary symmetric polynomial e_2(x,y,z) = xy + xz + yz
let e2 = fun x, y, z => x*y + x*z + y*z;

// Power sum p_2(x,y,z) = x^2 + y^2 + z^2  
let p2 = fun x, y, z => x^2 + y^2 + z^2;
```

### Polynomial Interpolation
```zippel
// Lagrange basis polynomial
let L0 = fun x => (x - 1)*(x - 2) / ((0 - 1)*(0 - 2));
let L1 = fun x => (x - 0)*(x - 2) / ((1 - 0)*(1 - 2));
let L2 = fun x => (x - 0)*(x - 1) / ((2 - 0)*(2 - 1));

// Interpolating polynomial through points (0,y0), (1,y1), (2,y2)
let interpolate = fun x => y0*L0(x) + y1*L1(x) + y2*L2(x);
```

### Error Locator Polynomial (Reed-Solomon codes)
```zippel
// Error locator polynomial for Reed-Solomon decoding
let error_locator = fun x => (x - e1)*(x - e2)*(x - e3);
```

## Benefits of the New Syntax

1. **Readability**: Mathematical notation matches the code
2. **Composability**: Easy to build complex polynomials from simple ones
3. **Type Safety**: Compiler can check variable counts and degrees
4. **Flexibility**: Works with both simple and complex polynomial expressions
5. **Backward Compatible**: All existing code continues to work

## Notes

- The `fun` syntax is syntactic sugar that gets type-checked and processed
- Variables are automatically bound to field elements
- The type system tracks the number of variables and maximum degree
- Evaluation and other operations work the same as before
