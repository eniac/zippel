# Copilot Instructions for Zippel

Zippel is a compiler for cryptographic protocols (zero-knowledge proofs, commitment schemes, etc.). It compiles `.zippel` source files into optimized prover and verifier code, then executes them against arkworks cryptographic backends.

## Build & Test

Requires **Rust nightly** (pinned in `rust-toolchain.toml` at the repo root, mirrored in `share/rust-toolchain.toml`). The `.cargo/config.toml` sets `RUST_MIN_STACK = "33554432"` (32 MB) and `SYMBOLICA_HIDE_BANNER = "1"` — needed because deep recursion in graph passes can otherwise overflow the default thread stack during tests.

```bash
cargo build                              # build everything (workspace)
cargo test --workspace                   # run all tests across all crates (also: cargo test-all)
cargo test -p graph                      # test a single crate
cargo test -p graph op_unit_tests        # run a specific test module
cargo test -p graph -- --test scalar     # run tests matching "scalar"
cargo test -- --nocapture                # show stdout/stderr (also: cargo test-verbose)
cargo run --example ipa                  # run an example (from repo root)
cargo bench --bench graph_execution      # Criterion benchmark
```

Aliases live in `.cargo/config.toml`: `test-all`, `test-verbose`, `test-coverage` (the latter requires `cargo-tarpaulin`).

CI runs on GitHub Actions (`.github/workflows/ci.yml`) inside the `rustlang/rust:nightly` container. The exact CI commands are:

```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets
cargo test --workspace
```

Run these locally before pushing — clippy in particular is strict about the whole workspace including `--all-targets` (tests, examples, benches).

## Architecture

### Compilation Pipeline

```
.zippel source
  → lang::UModule        (parse via PEG grammar)
  → lang::CModule        (concretize symbolic sizes to concrete usize)
  → graph::UDags         (build DAG IR per protocol/function)
  → graph::QDags         (qualifier propagation: Public/Private)
  → graph::DQDags        (uniformity propagation: Uniform/Nonuniform)
  → Prover/Verifier      (project subgraphs via get_prover/get_verifier)
  → graph::TDags         (schedule with LocalScheduler)
  → runtime::MutexGraph  (parallel execution)
```

The entry point is `ZippelHandler<C: ArkConfig>` in `src/lib.rs`. It is parameterized by a cryptographic backend `C`.

### Workspace Crates

- **`lang`** — Parser (PEG via `pest`, grammar in `lang/src/parser/zippel.pest`), AST (`Exp<N>`, `Decl<N>`, `Module<N>`), and type system (`Typ`, `Qualifier`, `Distribution`, type inference).
- **`share`** — Shared utilities: `Ctx<K,V>` (ordered map), `Pretty` (Wadler-style pretty printing), `Traversal` (generic tree walkers).
- **`graph`** — DAG intermediate representation (`Dag<C, A>`) parameterized by crypto config and annotation. Contains operations (`Op<C, R>` enum), nodes, static analyses (qualifier/uniformity/completeness/knowledge), scheduler, and Gröbner basis computation.
- **`backend`** — Cryptographic backend abstracting arkworks. Defines `ArkConfig` trait with associated types for fields/curves/pairings, `Value<C>` enum for runtime values (scalars, group elements, polynomials, vectors, records), and concrete curve configs (BLS12-381, BN254, Secp256k1, Pallas, Vesta, etc.).
- **`runtime`** — Execution engine. `MutexGraph<C>` wraps a scheduled DAG with per-node `Arc<Mutex<...>>` for thread-safe parallel execution.
- Top-level `src/lib.rs` defines `ZippelHandler<C>` / `ZippelArgs` — the high-level driver wired up in every example (`compile`, `default_schedule_prover`, `run_prover`, `default_schedule_verifier`, `run_verifier`).

Examples live in `examples/` and are registered as `[[example]]` targets in the root `Cargo.toml`. Each example has a `main.rs` and reads a `.zippel` file from `examples/`. **Adding a new example requires registering its `[[example]]` entry in the root `Cargo.toml`** — there's no glob discovery.

Integration tests at the repo root (`tests/groebner_correctness.rs`, `tests/groebner_sage.rs`) and Criterion benchmarks under `benches/` (`graph_execution`, `groebner`) are part of the workspace.

The formal language definition is in `docs/grammar.ott` (Ott source) and built to `docs/grammar.pdf` via `docs/Makefile` — consult it when reasoning about Zippel surface syntax or typing rules.

### Key Types & Their Flow

| Type | Crate | Role |
|---|---|---|
| `UModule` / `CModule` | lang | Parsed module (symbolic / concrete sizes) |
| `Dag<C, A>` | graph | Core DAG IR, parameterized by annotation `A` |
| `UDag<C>` = `Dag<C, Nothing>` | graph | Unanalyzed DAG |
| `QDag<C>` = `Dag<C, Qualifier>` | graph | After qualifier propagation |
| `DQDag<C>` = `Dag<C, (Qualifier, Distribution)>` | graph | After uniformity propagation |
| `TDag<C>` = `Dag<C, ThreadAlloc>` | graph | After scheduling |
| `Op<C, R>` / `GOp<C>` | graph | Typed operations (arithmetic, polynomial, crypto) |
| `Value<C>` | backend | Runtime values (scalars, group elements, polynomials) |
| `ArkConfig` | backend | Trait unifying field/curve/pairing types |
| `Ctx<K, V>` | share | Ordered map used everywhere for environments |
| `Vid` / `Tid` | lang | Variable and type identifiers with gensym |

### Static Analyses

All implement `StaticAnalysis<C, A>` trait in `graph/src/analyses/`:
- **QualifierPropagation** — Tags nodes as Public/Private (Private ≤ Public).
- **UniformityPropagation** — Tags nodes as Uniform/Nonuniform for security analysis.
- **CompletenessAnalysis** — Checks protocol completeness.
- **KnowledgeAnalysis** — Detects information leakage.

### Verification Results

`run_verifier()` returns `Vec<Value<C>>`. Use `check_verification()` to interpret as pass/fail (all `Bool(true)` = pass). Use `proof_size_bytes()` to measure proof certificate size. Examples exit with code 1 on verification failure.

## Conventions

- **Error handling**: `thiserror` throughout. Each domain has its own error type (`InputError`, `TypeError`, `RangeError`, `GraphError`, `DeclError`, `ModuleError`, `SigError`).
- **Cryptographic generics**: Most types are parameterized by `C: ArkConfig`. The default test config is `ArkBls12_381` (aliased as `TestConfig` in graph tests).
- **Testing**: Graph tests use `GraphBuilder` and `execute_graph` helpers from `graph/src/tests/test_helpers.rs`. Property-based testing uses `arbtest`/`arbitrary` crates. `Op::Record` fields must be evaluated recursively via `evaluate_op` to produce `Value::Record`.
- **Pretty printing**: Types implement the `Pretty` trait from `share` for Wadler-style output.
- **Logging**: `log` crate with `env_logger`. Enable with `RUST_LOG=debug`. Library code uses `log` macros only — no `println!` in library crates.
- **Qualifier semantics**: `Private ≤ Public` — qualifier propagation computes the join (least upper bound).
- **Identifier conventions in `.zippel` source**: identifiers starting with an **uppercase** letter are size-type variables (`Tid`); those starting **lowercase** are value variables (`Vid`). This is enforced in `lang/src/ast/exp.rs` `FromPest` parsing, not just stylistic.
- **Polynomial encoding**: `Uni(m)` stores `m+1` coefficients, `VPoly(n,m)` stores `C(m+n,n)` slots, `Mle(n)` stores `2^n` slots. See `backend/src/types.rs` and `backend/src/poly_variant.rs`.
- **Polynomial and Vec are distinct types**: `lub(Poly, Vec)` is a type error. A `Vec(F, k)` is **not** implicitly reinterpreted as a polynomial's coefficient list (or MLE evaluation table) under `+ / - / · / ++`. Use explicit `poly([...])` / `mle([...])` to lift a `Vec` into a polynomial, or `coef(p)` to extract a coefficient `Vec` from a polynomial. Polynomial ↔ polynomial coercion across `Uni` / `Mle` / `VPoly` still works via the general `(Poly, Poly)` lub arms and produces a `VPoly`. See `lang/src/typ/lub.rs`.
- **Univariate evaluation**: `p(x)` for `p: Uni<F, n>` and `x: F` desugars to `Op::Evaluate(p, x)` (single-scalar variant), not `dot(p, [x^0, x^1, ..., x^n])`. The dot-based form would require an implicit `Poly ↔ Vec` coercion that no longer exists. See `graph/src/lib.rs` `CExp::App` handling.
- **Arkworks deps** are pulled from git (`arkworks-rs/algebra`, `arkworks-rs/spongefish`), not crates.io — expect occasional API drift when bumping.

## Type System & `Op<C, R>` Type Preservation

Zippel has **two type levels** that must be kept consistent:

| Level | Module | Type | Notes |
|---|---|---|---|
| Source | `lang::typ` | `Typ<T, N>` | T = base type tag (`Tid`), N = size repr (`Size` symbolic / `usize` concrete) |
| IR / runtime | `backend` | `ATyp` (+ `ABase`) | Arkworks-typed; polynomial variants are split out |

Aliases: `UTyp = Typ<Tid, Size>` (post-parse, symbolic sizes), `CTyp = Typ<Tid, usize>` (post-concretize). At the IR level, `ATyp` distinguishes `Uni(n)`, `Mle(n)`, `VPoly(num_vars, max_degree)` rather than the source-level unified `Typ::Poly(Tid, m, n)`. Source helpers `CTyp::as_uni()` / `as_mle()` recognize the encodings (`Poly(_, 1, n)` is univariate of degree n; `Poly(_, m, 1)` is multilinear in m vars).

### Kinds and the kind context

Type inference is **kind-directed**. `Kind<N>` (`UKind` / `CKind`) is one of `Field | Group | Scalar(Set<Tid>) | Pairing(Tid, Tid) | Range(Range<N>) | SizeVar`. The `kctx: Ctx<Tid, CKind>` is threaded through every inference and conversion step — it's how a bare `Typ::Base(Tid)` resolves to a concrete arkworks element. Conversion `ATyp::from_ctyp(typ, kctx)` (in `backend/src/types.rs`) collapses scalar-shaped kinds to `ABase::Scalar` and routes `Group` Tids to `G1` vs `G2` by searching `kctx` for a `Pairing(...)` kind that references them.

### The inference pipeline

The `Typeable` trait in `lang/src/typ/infer.rs` is the entry:

```rust
fn infer(&self, kctx: &Ctx<Tid, CKind>, fctx: &Set<CSig>, vctx: &Self::Context)
    -> Result<CTyp, TypeError>;
```

Three contexts flow together: kinds (`kctx`), function signatures (`fctx`), and variables (`vctx`). Inference relies on two helper traits:

- `Lub` (`lang/src/typ/lub.rs`) — least-upper-bound for equality (`lub_equ`) and per-`BinOp` lubs (`lub_add`, `lub_mul`, `lub_op`, etc.). `Op::Vec` lub-equs all element types; `Op::Reduce` calls `lub_op` on the element type to derive the result.
- `Unify` (`lang/src/typ/unify.rs`) — kind-aware unification with `AliasSubsts`. Returns `UnifyError` rather than panicking.

`TypeError` is a large enum with one variant per source-level construct (`Vec`, `Interpolate`, `Poly`, `Evaluate`, `Coef`, `Mle`, `MleApp`, …). Each variant captures `kctx`, `vctx`, and the offending expression so error messages can pretty-print the full typing judgement. **Add a new variant rather than reusing `CExp` when a new construct gets a custom check** — the helpers in `infer.rs` follow this pattern consistently.

### `Op<C, R>` typing discipline

`Op<C, R>` (in `backend/src/op.rs`) is the typed IR operation enum. `R` is the reference flavor — `GOp<C> = Op<C, Ref>` is the on-graph form; `HOp<C> = HConsed<GOp<C>>` is the hash-consed handle minted via `HasOpFactory::op_factory()` and `mk::<C>(op)`. Since equality and hashing are structural, **`Op::typ()` must be deterministic for any given children** — never read mutable state.

Every `Op` variant exposes `.typ() -> ATyp`. Types are preserved in **two complementary ways**:

1. **Stored explicitly** (the variant carries an `ATyp` field) when the output type isn't recoverable from inputs alone:
   - `Op::Bin(_, _, _, ATyp)`, `Op::Pair(_, _, ATyp)`, `Op::Ref(_, ATyp)`, `Op::Proj(_, _, ATyp)`, `Op::Random(ATyp, _)`, `Op::Challenge(ATyp, _)`.
   - These types are **chosen at construction time** by the lowering code in `graph::add_exp` / `graph::lib.rs` and by `GOp::bin`. The `ATyp` is canonical and authoritative — downstream passes must trust it.

2. **Computed structurally** in `Op::typ()` when the output type is a function of children's types:
   - `Vec`, `Record` — combine child types (`Vec` lub-equs all element types, panicking via `expect` if mismatched).
   - `Ifft`/`Fft`/`Poly`/`Mle`/`Coef`/`Interpolate`/`Marginalize` — these **must return the polynomial result type, not delegate to a child**. E.g. `Op::Poly` on `Vec(Scalar, n)` returns `ATyp::uni(n)`; `Op::Coef` on `Uni(n)` returns `ATyp::vec_scalar(n)`; `Op::Mle` requires power-of-two length and returns `Mle(log2(n))`. Earlier bugs (commit `03bee5f`) where these delegated to `child.typ()` broke `TransClos` because consumers downstream of `Op::Ref` resolution depend on the correct type.
   - `Evaluate(_, x)` returns `x.typ()` (point shape determines result shape).
   - `Reduce` lub-ops the element type.

When **adding a new `Op` variant**:
1. Decide whether the output type is recoverable from children. If not, store `ATyp` in the variant.
2. Add an arm to `Op::typ()` that returns the correct `ATyp` and `panic!`s on shape violations (this matches the existing `Op::Ifft`/`Op::Mle`/`Op::Poly` style — these are *invariants*, not user errors; user-facing checks happen at the `lang`-level `infer()`).
3. Add a `discriminant_order` entry to keep ordering stable for hash-consing.
4. If the op is a polynomial transform, audit `graph/src/analyses/trans_clos.rs` — it calls `op.typ()` when materializing `Op::Ref(r, op.typ())` and any incorrect type propagates everywhere.

## Custom Agents

`.github/agents/testing-agent.md` defines a `tester` custom agent that focuses on coverage-driven test generation (algebraic property tests, error-path coverage, dense/sparse cross-variant equivalence). Invoke via the Copilot CLI when working on test coverage tasks.
