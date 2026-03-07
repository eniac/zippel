# Copilot Instructions for Zippel

Zippel is a compiler for cryptographic protocols (zero-knowledge proofs, commitment schemes, etc.). It compiles `.zippel` source files into optimized prover and verifier code, then executes them against arkworks cryptographic backends.

## Build & Test

Requires **Rust nightly** (specified in `share/rust-toolchain.toml`).

```bash
cargo build                          # build everything (workspace)
cargo test                           # run all tests (workspace, via .cargo alias)
cargo test -p graph                  # test a single crate
cargo test -p graph op_unit_tests    # run a specific test module
cargo test -p graph -- --test scalar # run tests matching "scalar"
cargo run --example ipa              # run an example (from repo root)
```

CI runs in Docker via CircleCI (see `.circleci/config.yml`).

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

Examples live in `examples/` and are registered as `[[example]]` targets in the root `Cargo.toml`. Each example has a `main.rs` and reads a `.zippel` file from `examples/`.

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
