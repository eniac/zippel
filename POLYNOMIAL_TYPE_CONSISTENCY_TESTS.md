# Polynomial Type Consistency Test Plan

## Objective
Ensure that type rules in `lang/src/typ/lub.rs` perfectly match runtime behavior in `backend/src/poly_variant.rs` and `backend/src/values.rs`.

## Type System Rules vs Runtime Behavior

### Addition Rules

| Type Rule (lub.rs) | Runtime Behavior (poly_variant.rs) | Status |
|-------------------|-----------------------------------|--------|
| `Poly(F, 1, n) + Poly(F, 1, m) → Poly(F, 1, max(n,m))` | `DenseUni + DenseUni → DenseUni` | ✅ Match |
| `Poly(F, n, 1) + Poly(F, m, 1) → Poly(F, max(n,m), 1)` | `DenseMle + DenseMle → DenseMle` (with num_vars check) | ✅ Match |
| `Poly(F, 1, n) + Scalar → Poly(F, 1, n)` | `poly_add_scalar()` | ✅ Match |
| `Poly(F, n, 1) + Scalar → Poly(F, n, 1)` | `poly_add_scalar()` | ✅ Match |
| `Scalar + Poly → Poly` | Symmetric | ✅ Match |

### Subtraction Rules

| Type Rule (lub.rs) | Runtime Behavior (poly_variant.rs) | Status |
|-------------------|-----------------------------------|--------|
| `Poly(F, 1, n) - Poly(F, 1, m) → Poly(F, 1, max(n,m))` | `DenseUni - DenseUni → DenseUni` | ✅ Match |
| `Poly(F, n, 1) - Poly(F, m, 1) → Poly(F, max(n,m), 1)` | `DenseMle - DenseMle → DenseMle` | ✅ Match |
| `Poly - Scalar` | `poly_sub_scalar()` | ✅ Match |
| `Scalar - Poly` | `scalar_sub_poly()` | ✅ Match |

### Multiplication Rules

| Type Rule (lub.rs) | Runtime Behavior (poly_variant.rs) | Status |
|-------------------|-----------------------------------|--------|
| `Poly(F, 1, n) * Poly(F, 1, m) → Poly(F, 1, n+m-1)` | `DenseUni * DenseUni → DenseUni` | ✅ Match |
| `Poly(F, n, 1) * Poly(F, m, 1)` | ❌ Runtime Error | ⚠️ Need type rule |
| `Poly(F, 1, n) * Scalar → Poly(F, 1, n)` | `poly_mul_scalar()` | ✅ Match |
| `Poly(F, n, 1) * Scalar → Poly(F, n, 1)` | `poly_mul_scalar()` | ✅ Match |
| `Poly(F, 1, n) * Poly(F, m, 1)` | ❌ Runtime Error | ⚠️ Need type rule |

### Division Rules

| Type Rule (lub.rs) | Runtime Behavior (poly_variant.rs) | Status |
|-------------------|-----------------------------------|--------|
| `Poly(F, 1, n) / Poly(F, 1, m) → Poly(F, 1, n-m+1)` | `DenseUni / DenseUni → DenseUni` | ✅ Match |
| `Poly(F, n, 1) / _` | ❌ No type rule? | ⚠️ Runtime rejects |
| `Poly / Scalar` | `poly_div_scalar()` | ✅ Match |
| `Scalar / Poly` | Only if Poly is constant | ⚠️ Check type rule |

### Remainder/Modulo Rules

| Type Rule (lub.rs) | Runtime Behavior (poly_variant.rs) | Status |
|-------------------|-----------------------------------|--------|
| `Poly(F, 1, n) % Poly(F, 1, m) → Poly(F, 1, m-1)` | `DenseUni % DenseUni → DenseUni` | ✅ Match |
| `Poly(F, n, 1) % _` | ❌ Runtime Error | ⚠️ Check type rule |

## Critical Mismatches to Investigate

### 1. MLE * MLE
**Type System**: No rule (should error at type checking)
**Runtime**: Explicit error "Cannot multiply two multilinear polynomials"
**Action**: ✅ Consistent - both reject

### 2. Univariate * MLE
**Type System**: No rule (should error at type checking)
**Runtime**: Explicit error "Cannot multiply univariate and multilinear"
**Action**: ✅ Consistent - both reject

### 3. MLE Division
**Type System**: Need to verify no rule exists
**Runtime**: Explicit error "Division not supported for multilinear"
**Action**: ⚠️ Verify type system rejects this

### 4. Scalar / Poly
**Type System**: Need to check if rule exists
**Runtime**: Only works if Poly is degree-0 constant
**Action**: ⚠️ Verify type system handles this correctly

## Test Strategy

### Unit Tests for PolyVariant

Create `backend/src/poly_variant_tests.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use ark_test_curves::bls12_381::Fr;
    
    // Addition tests
    #[test]
    fn test_uni_add_uni() {
        // Poly(x) = x + 1
        let p1 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![Fr::from(1), Fr::from(1)]));
        // Poly(x) = x^2
        let p2 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![Fr::from(0), Fr::from(0), Fr::from(1)]));
        
        let result = p1.poly_add(&p2).unwrap();
        // Should be x^2 + x + 1
        assert_eq!(result.degree(), Some(2));
    }
    
    #[test]
    fn test_mle_add_mle() {
        // Test MLE addition
        let mle1 = DenseMultilinearExtension::from_evaluations_vec(2, vec![Fr::from(0), Fr::from(1), Fr::from(2), Fr::from(3)]);
        let mle2 = DenseMultilinearExtension::from_evaluations_vec(2, vec![Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(1)]);
        
        let p1 = PolyVariant::DenseMle(mle1);
        let p2 = PolyVariant::DenseMle(mle2);
        
        let result = p1.poly_add(&p2).unwrap();
        assert!(result.is_multilinear());
        assert_eq!(result.num_vars(), Some(2));
    }
    
    #[test]
    fn test_mle_add_wrong_dims() {
        let mle1 = DenseMultilinearExtension::from_evaluations_vec(2, vec![Fr::from(0), Fr::from(1), Fr::from(2), Fr::from(3)]);
        let mle2 = DenseMultilinearExtension::from_evaluations_vec(3, vec![Fr::from(1); 8]);
        
        let p1 = PolyVariant::DenseMle(mle1);
        let p2 = PolyVariant::DenseMle(mle2);
        
        let result = p1.poly_add(&p2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("different number of variables"));
    }
    
    // Multiplication tests
    #[test]
    fn test_uni_mul_uni() {
        // (x + 1) * (x + 2) = x^2 + 3x + 2
        let p1 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![Fr::from(1), Fr::from(1)]));
        let p2 = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![Fr::from(2), Fr::from(1)]));
        
        let result = p1.poly_mul(&p2).unwrap();
        assert_eq!(result.degree(), Some(2));
    }
    
    #[test]
    fn test_mle_mul_mle_fails() {
        let mle1 = DenseMultilinearExtension::from_evaluations_vec(2, vec![Fr::from(0), Fr::from(1), Fr::from(2), Fr::from(3)]);
        let mle2 = DenseMultilinearExtension::from_evaluations_vec(2, vec![Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(1)]);
        
        let p1 = PolyVariant::DenseMle(mle1);
        let p2 = PolyVariant::DenseMle(mle2);
        
        let result = p1.poly_mul(&p2);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not be multilinear"));
    }
    
    #[test]
    fn test_uni_mul_mle_fails() {
        let uni = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![Fr::from(1), Fr::from(1)]));
        let mle = PolyVariant::DenseMle(DenseMultilinearExtension::from_evaluations_vec(2, vec![Fr::from(0), Fr::from(1), Fr::from(2), Fr::from(3)]));
        
        let result = uni.poly_mul(&mle);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("incompatible types"));
    }
    
    // Scalar operations tests
    #[test]
    fn test_poly_add_scalar() {
        let p = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(vec![Fr::from(1), Fr::from(1)]));
        let result = p.poly_add_scalar(Fr::from(5));
        
        // (x + 1) + 5 = x + 6
        if let PolyVariant::DenseUni(poly) = result {
            assert_eq!(poly.coeffs[0], Fr::from(6));
            assert_eq!(poly.coeffs[1], Fr::from(1));
        } else {
            panic!("Expected DenseUni");
        }
    }
    
    // Evaluation tests
    #[test]
    fn test_uni_evaluate() {
        // p(x) = x^2 + 2x + 1
        let p = PolyVariant::DenseUni(DensePolynomial::from_coefficients_vec(
            vec![Fr::from(1), Fr::from(2), Fr::from(1)]
        ));
        
        let result = p.evaluate(&Fr::from(3));
        // p(3) = 9 + 6 + 1 = 16
        assert_eq!(result, Fr::from(16));
    }
    
    #[test]
    fn test_mle_evaluate() {
        // Simple 2-variable MLE
        let mle = DenseMultilinearExtension::from_evaluations_vec(
            2, 
            vec![Fr::from(0), Fr::from(1), Fr::from(2), Fr::from(3)]
        );
        let p = PolyVariant::DenseMle(mle);
        
        let result = p.evaluate_mle(&[Fr::from(0), Fr::from(0)]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Fr::from(0));
        
        let result = p.evaluate_mle(&[Fr::from(1), Fr::from(1)]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Fr::from(3));
    }
}
```

### Integration Tests

Create `backend/tests/poly_type_consistency.rs`:

```rust
/// Test that type system rules match runtime behavior
#[test]
fn test_type_runtime_consistency() {
    // For each operation:
    // 1. Create expression in lang
    // 2. Type check it
    // 3. Compile to backend
    // 4. Execute and verify it doesn't panic with runtime error
    // 5. Verify result type matches inferred type
}
```

### Property-Based Tests

Use `proptest` or `quickcheck` to generate random polynomials and verify:

1. **Addition commutative**: `p1 + p2 == p2 + p1`
2. **Addition associative**: `(p1 + p2) + p3 == p1 + (p2 + p3)`
3. **Multiplication associative** (for univariate): `(p1 * p2) * p3 == p1 * (p2 * p3)`
4. **Distributive**: `p1 * (p2 + p3) == p1*p2 + p1*p3`
5. **Identity**: `p + 0 == p`, `p * 1 == p`
6. **Degree bounds**: `deg(p1 + p2) <= max(deg(p1), deg(p2))`
7. **Degree multiplication**: `deg(p1 * p2) = deg(p1) + deg(p2)` (for univariate)

## Action Items

1. ✅ Review type rules in lub.rs for all operations
2. ⚠️ Verify MLE operations are properly rejected in type system
3. ⚠️ Add type rule to reject `Poly(F, n, 1) * Poly(F, m, 1)` if not present
4. ⚠️ Check scalar/poly division type rule
5. 📝 Implement unit tests for PolyVariant
6. 📝 Implement integration tests
7. 📝 Implement property-based tests
8. 📝 Document any intentional mismatches (if any)

## Expected Outcomes

After completing tests:
- ✅ All type system rules have corresponding runtime behavior
- ✅ All runtime errors are caught at type checking time
- ✅ No runtime errors occur for well-typed programs
- ✅ Degree tracking is accurate
- ✅ MLE variable count tracking is accurate
