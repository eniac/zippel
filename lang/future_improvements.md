# Future Improvements for Zippel Crate Type System

This document outlines key design critiques, recommendations, and code quality improvements for the type system, grammar, and unification API in the Zippel language frontend `lang` crate. These items are ranked by their criticality to the safety, soundness, and usability of the compiler.

---

## 1. High Criticality (Bugs, Type Soundness, and Compiler Safety)

These items address type system soundness, verification correctness, or correctness of compiler checks.

### Let-Binding Type Annotation Checks
* **Location**: `FromPest for UExp` in [exp.rs](src/ast/exp.rs) / `CExp::infer` in [infer/mod.rs](src/typ/infer/mod.rs)
* **Critique**: The Pest grammar parses optional type annotations on let-bindings (e.g. `let x: Group = 5;`), but the AST mapping currently discards them (`let _ = typ_ann;`). Consequently, type annotations on let-bindings are never verified against their assigned values, allowing mismatched types to compile silently.
* **Proposed Solution**: Modify `Exp::Let` to store the annotation: `Let(Option<Vid>, Option<GTyp<N>>, Box<Exp<N>>, Box<Exp<N>>)`. Update AST traversals, mapper, and pretty-printer. During type inference of let-expressions in `CExp::infer`, unify the RHS inferred type with the type annotation (if present) using `CTyp::lub_equ`.

### Environment-Aware Protocol Purity Checks
* **Location**: `CBody::typecheck` in [decl.rs](src/ast/decl.rs) / `Exp::is_pure` in [exp.rs](src/ast/exp.rs)
* **Critique**: Specification relations (`where` clauses) are required to be pure. Currently, the purity checker `Exp::is_pure` operates shallowly on function application nodes (`App`), only checking if the arguments are pure. This allows relations calling impure protocols or functions containing side-effects (such as `verify()` or `challenge<F>`) to be bypass-accepted as pure.
* **Proposed Solution**: Update `Exp::is_pure` to accept a set of impure function names: `is_pure(&self, impure_funcs: &Set<Vid>)`. Prior to typechecking, perform a static fixed-point dependency analysis over all module declarations to compute the set of all impure protocols and functions. Reject any relation that calls any function in this set.

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
