# Future Improvements for Zippel Crate Type System

This document outlines key design critiques, recommendations, and code quality improvements for the type system, grammar, and unification API in the Zippel language frontend `lang` crate. These items are ranked by their criticality to the safety, soundness, and usability of the compiler.

---

## 1. High Criticality (Bugs, Type Soundness, and Compiler Safety)

These items address actual compiler bugs, incorrect diagnostic reporting, type soundness issues, or potential crashes (stack overflows).

### Protocol Body Typecheck Diagnostic Bug
* **Location**: `CBody::typecheck` in [decl.rs](src/ast/decl.rs)
* **Critique**: If either the `relation` or the `body` of a protocol does not typecheck to `Bool`, the compiler reports `TypeError::bool(&kctx, &vctx, relation)`. If the relation is valid but the body is not, the reported error misleadingly blames the relation.
* **Proposed Solution**: Distinguish between the two failures:
  ```rust
  let tr = relation.infer(&kctx, fctx, &vctx)?;
  if tr != CTyp::Bool {
      return Err(TypeError::decl(&sig.name, TypeError::bool(&kctx, &vctx, relation)));
  }
  let br = body.infer(&kctx, fctx, &vctx)?;
  if br != CTyp::Bool {
      return Err(TypeError::decl(&sig.name, TypeError::bool(&kctx, &vctx, body)));
  }
  ```

### Type Alias Cycle Safety (Stack Overflow Prevention)
* **Location**: `UModule::from_str` in [module.rs](src/ast/module.rs) / [typ/mod.rs](src/typ/mod.rs)
* **Critique**: Type alias inlining is recursive. If a cyclic type alias is defined (e.g., `type A = B; type B = A;`), calling `type_inline` on `A` results in an infinite recursion stack overflow, crashing the compiler.
* **Proposed Solution**: Build a dependency graph of type alias declarations to check for cycles before inlining, or track visited type variables during inlining.

### Unification Diagnostic Mistake
* **Location**: `Tid::unify` in [unify.rs](src/typ/unify.rs)
* **Critique**: If the second type variable `b` is missing from the kind context (line 64), the error incorrectly blames the first type variable `a`:
  ```rust
  let kb = ctx.get(b).ok_or(UnifyError::kind_not_found(a))?;
  ```
* **Proposed Solution**: Fix the typo to return `UnifyError::kind_not_found(b)`.

### Fragile Type Coercion Fallback in `to_scalar`
* **Location**: `Typ::to_scalar` in [typ/mod.rs](src/typ/mod.rs)
* **Critique**: When coercing `Fin` to a scalar field type, `to_scalar` eagerly returns the alphabetically first field in the kind context `ctx`. If multiple fields are defined (e.g. `<E: Field, F: Field>`), this arbitrary choice is fragile and leads to incorrect type resolutions.
* **Proposed Solution**: Retain generic type information on `Fin` or lazily unify it with the expected target type context instead of eagerly resolving to the first field.

### `lub_concat` Arm Precedence for Nested Vectors
* **Location**: `CTyp::lub_concat` in [lub/mod.rs](src/typ/lub/mod.rs)
* **Critique**: Concatenating a vector `B` to a vector of vectors `Vec<B, n>` should append `B` as an element. However, because the `Vec ++ Vec` arm is matched first, it treats it as concatenating two vectors of elements and tries to unify `Vec` with `Base`, leading to a type mismatch error.
* **Proposed Solution**: Verify and compare element levels before choosing to concatenate or append.

---

## 2. Medium Criticality (Grammar Limitations and API Hazards)

These items address limitations in grammar expressiveness or API design hazards that make the code prone to programmer error.

### Support Arbitrary Indexing in Pest Grammar
* **Location**: `zippel.pest` in [zippel.pest](src/parser/zippel.pest) / [exp.rs](src/ast/exp.rs)
* **Critique**: The Pest grammar defines indexing as `ram_exp = { id ~ "[" ~ exp ~ "]" }`. This limits indexing strictly to simple variable identifiers. However, the AST representation `Exp::Ram(Box<Exp<N>>, Box<Exp<N>>)` fully supports indexing on arbitrary left-hand side expressions. Currently, multi-dimensional indexing (e.g., `matrix[i][j]`) or indexing record fields (e.g., `record.field[0]`) is blocked by the parser.
* **Proposed Solution**: Redefine indexing as a postfix operator or map-infix rule in the Pratt parser (e.g., `index_op = { "[" ~ exp ~ "]" }`) to match the AST's expressive capabilities.

### `CRange` Iterator Mutation Hazard
* **Location**: `CRange` Iterator impl in [range.rs](src/typ/range.rs)
* **Critique**: Implementing `Iterator` directly on `CRange` is a design hazard because iterating over it mutates the range itself (specifically its `start` field), meaning the range is consumed and becomes empty after a single iteration.
* **Proposed Solution**: Implement `IntoIterator` on `CRange` and define a separate `RangeIter` struct for the actual iteration.

---

## 3. Low Criticality (Optimizations and Cleanups)

These items address code refactorings, dead code removal, minor syntax convenience features, or performance improvements inside the crate.

### Boxing Large Payloads in `TypeError` & `LubError`
* **Location**: `TypeError` in [infer/error.rs](src/typ/infer/error.rs) / `LubError` in [lub/error.rs](src/typ/lub/error.rs)
* **Critique**: The `TypeError` and `LubError` enums carry large payloads (such as environment contexts and AST nodes) by value. This leads to large enum layouts and increases stack-frame sizes for recursive typechecking calls. This is why the crate root currently requires `#![allow(clippy::result_large_err)]`.
* **Proposed Solution**: Identify the largest enum variants and wrap their internal payload components in `Box` (e.g. `Box<Ctx<Vid, CTyp>>` or `Box<CExp>`). This keeps the size of `Result<CTyp, TypeError>` small and improves stack usage.

### Type Inference Context Grouping
* **Location**: `Typeable::infer` in [infer/mod.rs](src/typ/infer/mod.rs)
* **Critique**: Passing `kctx`, `fctx`, and `vctx` individually results in verbose function signatures throughout all typechecking logic.
* **Proposed Solution**: Introduce a unified `InferEnv<'a>` struct:
  ```rust
  pub struct InferEnv<'a, V> {
      pub kctx: &'a Ctx<Tid, CKind>,
      pub fctx: &'a Set<CSig>,
      pub vctx: &'a Ctx<Vid, V>,
  }
  ```
  And simplify `infer` to:
  ```rust
  fn infer(&self, env: &InferEnv<Self::Context>) -> Result<CTyp, TypeError>;
  ```

### Union-Find Complexity for Equivalence Closure
* **Location**: `AliasSubsts::add_equ` in [subst.rs](src/typ/subst.rs)
* **Critique**: `AliasSubsts::add_equ` maintains equivalence classes transitively by iterating over and updating all elements of the class in $O(N)$ time per union.
* **Proposed Solution**: Implement a standard disjoint-set union-find algorithm with path compression and rank/weight heuristics, optimizing unions to near $O(1)$ amortized complexity ($O(\alpha(N))$).

### Unused `impl Typeable for CBody`
* **Location**: `CBody` Typeable impl in [infer/mod.rs](src/typ/infer/mod.rs)
* **Critique**: `CBody` implements the `Typeable` trait, but this implementation is never called anywhere in the codebase. Compilation typechecks declarations via `CBody::typecheck` directly. Furthermore, `CBody::infer` is incomplete as it misses the purity checks and Range typevar mappings that `CBody::typecheck` performs.
* **Proposed Solution**: Remove the dead `impl Typeable for CBody` to keep the code clean and prevent logic drift.

### Identifier Generation Duplication
* **Location**: `Tid::fresh` / `Vid::fresh` in [id.rs](src/id.rs)
* **Critique**: Both `Tid::fresh` and `Vid::fresh` duplicate identical split-and-loop search algorithms.
* **Proposed Solution**: Extract the search loop into a generic helper function `fn generate_fresh<T, F>(root: &str, s: &mut Set<T>, make: F) -> T` where `T: Ord + Clone` and `F: Fn(String) -> T`.

### Symbolic Size Simplification
* **Location**: `Size` AST in [size.rs](src/typ/size.rs)
* **Critique**: As size expressions are substituted, they can become complex (e.g., `2^(N-1) * 2`). There is no symbolic simplification pass to keep them clean.
* **Proposed Solution**: Implement a `Size::simplify` pass for basic constant folding (e.g., `2 * 3` -> `6`) and algebraic simplification (e.g., `N + 0` -> `N`).

### Trailing Comma Support
* **Location**: `zippel.pest` in [zippel.pest](src/parser/zippel.pest)
* **Critique**: The rules for argument lists (`args`), vectors (`vec_exp`), and records (`record_exp`, `record_ty`) do not permit trailing commas, which is a common convenience in modern languages.
* **Proposed Solution**: Update list matching rules (e.g., `(arg ~ ("," ~ arg)* ~ ","?)?`) to optionally allow trailing commas.

---

## 4. Least Critical (Interface Boundaries & Downstream Crate Dependencies)

These items require changes to, or directly impact, downstream crates outside the `lang` crate.

### Extensibility of the `Lub` Trait
* **Location**: `Lub` trait definition in [lub/mod.rs](src/typ/lub/mod.rs)
* **Critique**: The `Lub` trait generic design is implemented both in the frontend `lang` crate (for `CTyp` / `Range` / `Tid`) and the `backend` crate (for `ATyp` / `ABase`).
* **Design Note**: Any future updates to the unification rules must ensure the trait signatures remain generic so that downstream crates (specifically the `backend` crate) can continue implementing their custom type unification pipelines without disruption.
