# Polynomial Architecture Refactoring - Status

## Objective
Redesign polynomial representation to use explicit arkworks polynomial types throughout the stack,
eliminating ad-hoc validation and leveraging type safety.

## Completed Work

### 1. Backend PolyVariant Enum ✅
Created `PolyVariant<F>` enum in `backend/src/values.rs`:
```rust
pub enum PolyVariant<F: Field> {
    DenseUni(DensePolynomial<F>),
    SparseUni(SparsePolynomial<F>),
    DenseMle(DenseMultilinearExtension<F>),
    SparseMle(SparseMultilinearExtension<F>),
}
```

### 2. PolyVariant Methods ✅
- `degree()` - Get degree for univariate polynomials
- `num_vars()` - Get number of variables for multilinear
- `is_univariate()` - Check if univariate
- `is_multilinear()` - Check if multilinear  
- `serialize_compressed()` - Serialization support
- `PartialEq` and `Eq` implementations

### 3. Value Enum Updated ✅
Changed from:
```rust
Poly(DensePolynomial<C::F>),
Mle(DenseMultilinearExtension<C::F>),
```

To:
```rust
Poly(PolyVariant<C::F>),
```

### 4. Partial Backend Updates ✅
- PartialEq implementation updated
- Serialization updated for `serialize_value_internal`
- `discriminant_order()` updated
- `zero()` function updated for Uni and Mle types

## Remaining Work

### Backend (backend/src/values.rs)
- [ ] Update ~38 occurrences of `Value::Mle` pattern matches to `Value::Poly(PolyVariant::DenseMle(...))`
- [ ] Update operations (Add, Mul, etc.) to work with PolyVariant
- [ ] Update `random()` function
- [ ] Update `typ()` function to return correct types
- [ ] Update evaluation and other polynomial-specific operations

### Type Inference (lang/src/typ/infer.rs)
- [x] Already updated to infer polynomial types correctly
- [x] Removed explicit validation methods (poly_degree, is_multilinear)
- [x] Using type system to track polynomial structure

### Compilation (lang -> backend)
- [ ] When compiling `Fun` expressions, construct appropriate `PolyVariant`
- [ ] Determine when to use Dense vs Sparse variants (based on coefficient density)
- [ ] Add validation that polynomial constraints are met

## Design Decisions

### Where Polynomial Lives
**Decision:** PolyVariant is a **backend-only** type.

**Rationale:**
- Frontend AST (`Exp::Fun`) remains simple and generic
- Polynomial construction happens during compilation (lang -> backend)
- Validation happens naturally at construction time
- Backend has explicit, type-safe polynomial representations

### Dense vs Sparse Selection
**Strategy:** Start with Dense by default, add Sparse optimization later.

For now:
- Univariate: Use `DenseUni` 
- Multilinear: Use `DenseMle`

Future: Analyze coefficient density and choose appropriately.

### Type System Integration  
The type system already correctly represents polynomials as `Poly(F, M, N)`:
- `Poly(F, 1, N)` = univariate of degree N
- `Poly(F, M, 1)` = multilinear with M variables

Type inference tracks this through LUB operations automatically.

## Benefits of This Approach

1. **Type Safety** - Polynomial types are explicit, not ad-hoc
2. **Clear Semantics** - Easy to query degree, num_vars, etc.
3. **Extensibility** - Easy to add new polynomial types (e.g., sparse)
4. **No Duplication** - Single unified representation
5. **Natural Validation** - Construction enforces constraints

## Next Steps

To complete this refactoring:

1. Systematically update all `Value::Mle` references in backend/src/values.rs
   - Use find-and-replace carefully for each pattern
   - Test after each batch of changes

2. Update compilation in backend to construct PolyVariant from Fun expressions

3. Add integration tests to verify polynomial operations work correctly

4. Consider adding sparse polynomial support based on coefficient density

## Estimated Effort
- Mechanical updates: ~2-3 hours (38+ pattern matches to update)
- Testing and fixes: ~1 hour
- Total: ~3-4 hours

## Status: IN PROGRESS
Started: 2025-11-17
Last Updated: 2025-11-17

## Update 2025-11-17 02:00 UTC

### Progress Made
1. ✅ Added coercion methods to PolyVariant:
   - `to_dense()` - convert sparse to dense
   - `try_to_scalar()` - extract scalar from degree-0 polynomial
   - `from_scalar()` - create degree-0 polynomial from scalar

2. ✅ Updated Value::Add operations for polynomials:
   - Index + Poly
   - Scalar + Poly
   - Poly + Poly (with type matching and dense/sparse coercion)

3. ⏳ Partially updated values.rs (still ~15 Value::Mle references remaining)

### Blocking Issues Found

The refactoring reveals that PolyVariant needs operator overloading to work seamlessly:

1. **Arithmetic Operators**: Need to implement Add, Sub, Mul, Div for PolyVariant
   - Currently: `p1 + p2` doesn't work on PolyVariant
   - Need: Match on variants and delegate to inner types

2. **Accessors**: Need wrapper methods for:
   - `.coeffs` - get coefficients
   - `.evaluate()` - evaluate polynomial
   - Other DensePolynomial/DenseMLE methods

3. **Pattern Matching**: ~15 places still use `Value::Mle(x)` pattern
   - Need: Change to `Value::Poly(PolyVariant::DenseMle(x))`

### Recommended Next Steps

**Option 1: Complete the refactoring (4-6 hours)**
- Implement Add/Sub/Mul/Div for PolyVariant
- Add all necessary accessor/wrapper methods  
- Update remaining pattern matches
- Fix compilation errors
- Test thoroughly

**Option 2: Simplify the approach (1-2 hours)**
- Keep Dense variants only for now (remove Sparse)
- This reduces combinations and complexity
- Still get benefits of unified polynomial type
- Can add Sparse later as optimization

**Option 3: Defer the refactoring**
- Revert to previous working state
- Document the design for future implementation
- Current type system approach (Poly(F, M, N)) already works well

### Recommendation
Given complexity, I recommend **Option 2**: Simplify to Dense-only for now. This gives us:
- Unified PolyVariant with just DenseUni and DenseMle
- Cleaner implementation (fewer type combinations)
- All the architectural benefits
- Extensible to Sparse later

This would take ~1-2 hours to complete vs 4-6 hours for full implementation.

## Final Update 2025-11-17 02:37 UTC

### Major Architectural Improvement ✅

**Created `backend/src/poly_variant.rs`** - Separated polynomial operations into dedicated module:

#### New Structure:
```
backend/
  ├── poly_variant.rs    # PolyVariant enum + all poly operations
  ├── values.rs          # Value enum + value operations  
  └── ...
```

#### PolyVariant Operations Implemented:
- ✅ `poly_add(other)` - Add two polynomials (with type checking)
- ✅ `poly_add_scalar(scalar)` - Add scalar to polynomial
- ✅ `poly_sub(other)` - Subtract polynomials
- ✅ `poly_sub_scalar(scalar)` - Subtract scalar from polynomial
- ✅ `scalar_sub_poly(scalar, poly)` - Subtract polynomial from scalar
- ✅ `poly_mul(other)` - Multiply polynomials (univariate only)
- ✅ `poly_mul_scalar(scalar)` - Multiply polynomial by scalar
- ✅ `poly_div(other)` - Divide polynomials (univariate only)
- ✅ `poly_div_scalar(scalar)` - Divide polynomial by scalar
- ✅ `scalar_div_poly(scalar, poly)` - Divide scalar by constant polynomial
- ✅ `poly_rem(other)` - Polynomial remainder/modulo
- ✅ `evaluate(point)` - Evaluate univariate at point
- ✅ `evaluate_mle(point)` - Evaluate MLE at boolean hypercube point

#### Runtime Error Handling:
- MLE * MLE → Error: "result would not be multilinear"
- Univariate * MLE → Error: "incompatible types"  
- MLE division → Error: "not supported for multilinear"
- Mismatched dimensions → Appropriate error messages

#### Benefits Achieved:
1. **Separation of Concerns** - Polynomial logic isolated from Value logic
2. **Cleaner Code** - `values.rs` operations now just call `poly.poly_add(...)` etc.
3. **Centralized Validation** - All polynomial constraints enforced in one place
4. **Easier Testing** - Can test polynomial operations independently
5. **Better Error Messages** - Clear runtime errors for invalid operations

### Values.rs Simplification Example:

**Before:**
```rust
Value::Poly(a) => match &other {
    Value::Poly(b) => {
        match (a, b) {
            (PolyVariant::DenseUni(p1), PolyVariant::DenseUni(p2)) => {
                *other = Value::Poly(PolyVariant::DenseUni(p1 + p2));
            }
            // ... many more cases
        }
    }
    // ... more complexity
}
```

**After:**
```rust
Value::Poly(a) => match &other {
    Value::Poly(b) => {
        *other = Value::Poly(a.poly_add(b).expect("Polynomial addition failed"));
    },
    Value::Scalar(_) | Value::Index(_) => {
        *other = Value::Poly(a.poly_add_scalar(other.into_scalar()));
    },
    _ => panic!("Expected polynomial or scalar, found {}", other)
},
```

### Next Steps to Complete:

The pattern is now established. To complete the refactoring:

1. Update remaining arithmetic operations in values.rs (Sub, Mul, Div, Rem)
   - Replace manual matching with calls to poly_sub, poly_mul, etc.
   - ~2-3 hours of mechanical updates

2. Update remaining ~15 Value::Mle pattern matches
   - Change to Value::Poly(PolyVariant::DenseMle(...))
   - ~1 hour

3. Test and debug
   - ~1 hour

**Total remaining:** ~4-5 hours

**Status:** Architecture is sound, pattern is clear, execution is straightforward.
