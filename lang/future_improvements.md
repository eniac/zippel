# Future Improvements for Zippel Crate Type System

This document outlines key design critiques and recommendations for the type system and unification API in the Zippel language frontend `lang` crate. These improvements are deferred to avoid unnecessary code churn during the modularization refactor.

## 1. Type Inference Context Grouping
Currently, `Typeable::infer` requires passing three separate contexts:
```rust
pub trait Typeable {
    type Context;
    fn infer(
        &self,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Self::Context,
    ) -> Result<CTyp, TypeError>;
}
```
* **Critique**: Passing these contexts individually results in verbose function signatures throughout all typechecking logic.
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

## 2. Boxing Large Payloads in `TypeError` & `LubError`
* **Critique**: The `TypeError` and `LubError` enums carry large payloads (such as environment contexts and AST nodes) by value. This leads to large enum layouts and increases stack-frame sizes for recursive typechecking calls. This is why the crate root currently requires `#![allow(clippy::result_large_err)]`.
* **Proposed Solution**: Identify the largest enum variants and wrap their internal payload components in `Box` (e.g. `Box<Ctx<Vid, CTyp>>` or `Box<CExp>`). This keeps the size of `Result<CTyp, TypeError>` small and improves stack usage.

## 3. Extensibility of the `Lub` Trait
* **Critique**: The `Lub` trait generic design is highly effective and must be preserved:
  ```rust
  pub trait Lub {
      type Context;
      fn lub_equ(a: &Self, b: &Self, ctx: &Self::Context) -> Result<Self, LubError>;
      // ...
  }
  ```
  It is implemented both in the frontend `lang` crate (for `CTyp` / `Range` / `Tid`) and the `backend` crate (for `ATyp` / `ABase`).
* **Design Note**: Any future updates to the unification rules must ensure the trait signatures remain generic so that downstream crates can continue implementing their custom type unification pipelines without disruption.
