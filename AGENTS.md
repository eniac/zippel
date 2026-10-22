# AGENTS.md

Guidance for AI coding agents working in this repository. See `paper.pdf`
for the full design and evaluation; `README.md` and `CONTRIBUTING.md` for
human-facing setup docs. This file focuses on where things live and how
the pieces fit together, so an agent can find the right place to make a
change without re-deriving the architecture from scratch.

## What Zippel is

Zippel is a *choreographic* language, compiler, runtime, and static
analyzer for cryptographic proof systems (Sigma protocols, SNARKs,
polynomial commitment schemes, etc.). A single `.zippel` source file
describes both the Prover's and Verifier's behavior together, the way a
cryptography paper's pseudocode would. The compiler:

1. Parses and type-checks the `.zippel` source (`lang`).
2. Lowers it into a DAG intermediate representation called **Graph IR**
   (`graph`), monomorphizing sizes and flattening expressions into
   single-operator nodes.
3. **Projects** the joint graph into separate Prover and Verifier
   subgraphs via reachability/visibility analysis (also `graph`).
4. Executes those subgraphs on a work-stealing, auto-parallelizing
   scheduler backed by `arkworks` (`runtime`, concrete types in
   `backend`).
5. Optionally runs fully automated **completeness** and **special
   soundness** analyses on the (unprojected) graph, by encoding node
   semantics as polynomial ideals and checking ideal containment via
   Gröbner bases (`analyses`).

The pipeline is: `.zippel` source → `lang` (parse/typecheck/concretize) →
`graph` (Graph IR + projection) → `runtime`/`backend` (execution) and,
independently, `graph` → `analyses` (completeness/soundness). `src/lib.rs`
(`ParsedModule`, `CompiledProtocol`, `CompiledProver`, `CompiledVerifier`,
`PreparedAnalysis`) wires all of this together and is the top-level interface
that examples and external users call into.

## Workspace layout

| Crate / directory | Role |
|---|---|
| [`src/`](src/lib.rs) | Top-level `zippel` crate. `ParsedModule` loads/parses source; `compile::<C>` returns a joint `CompiledProtocol<C>`; explicit `project_prover`/`project_verifier` return owned `CompiledProver<C>`/`CompiledVerifier<C>` that prove/verify independently. Explicit `prepare_analysis` returns `PreparedAnalysis<C>` with relations lowered and qualifiers propagated; its `run` performs a pass with an explicit backend. `compiler.rs`, `execution.rs`, and `analysis.rs` own these stages. Re-exports the member crates so downstream users only depend on `zippel`. |
| [`lang/`](lang) | The Zippel language: lexer/parser (`parser/`), AST (`ast/`), type system incl. sized/visibility types (`typ/`), semantic checks like dead-variable and purity analysis (`semantic/`), diagnostics (`diagnostic/`). Has its own proc-macro helper crate, `lang/lang-derive`. |
| [`graph/`](graph) | Graph IR: node definitions (`node.rs`), dependency/sequencing edges (`dep.rs`), the domain separator / Fiat–Shamir transcript machinery (`domain_separator.rs`), and prover/verifier projection. |
| [`backend/`](backend) | Concrete algebraic types and operations backed by `arkworks` (`ark-ff`, `ark-ec`, `ark-poly`, ...): field/group/pairing config (`config.rs`, `types.rs`), runtime values (`values.rs`), the operator implementations (`op.rs`), polynomial representations (`poly_variant.rs`, `virtual_polynomial.rs`). `nothing/` is a no-op backend used where no concrete curve is needed (e.g., some analysis paths). |
| [`runtime/`](runtime) | Executes a projected Graph IR DAG: work-stealing scheduler (`queue.rs`), graph execution and transcript/Fiat-Shamir handling (`graph.rs`), the single-operation interpreter (`eval/`; `eval/graph_tests/` executes lowered graphs), error types (`error.rs`). |
| [`analyses/`](analyses) | Completeness (`completeness.rs`) and (generalized) special-soundness (`soundness.rs`) analyses, plus zero-knowledge/qualifier propagation (`knowledge.rs`, `qualifier.rs`). Encodes Graph IR as polynomial ideals (`ideal/`, `frontend/`) and checks ideal membership via a Gröbner-basis backend (`backend/`, including an optional Singular integration in `backend/singular.rs`). `extractor.rs` builds candidate knowledge extractors for the soundness check. |
| [`share/`](share) | Small utilities shared across the workspace: a generic `Ctx` map keyed by identifiers and `ScopedCtx`, a `Ctx` with an undo log for lexical environments (`context.rs`), stack growth for recursive passes (`stack.rs`), tree traversal helpers (`traversal.rs`), pretty-printing (`pretty.rs`), macros (`macros.rs`). |
| [`fmt/`](fmt) | `zippel-fmt`, the source formatter for `.zippel` files (binary in `fmt/src/bin/zippel-fmt.rs`). |
| [`check/`](check) | `zippel-check`: every compile-time check, no harness or inputs. A thin driver (`check/src/main.rs`) over the same stages and diagnostics as compilation plus explicit projection: `UModule::parse`, `UModule::concretize`, `CModule::typecheck`, and Graph IR construction/projection, with every error turned into a `Diagnostic` via `From` (`TypeError`, `ModuleError`, `GraphError`); it only adds default sizes (`lang::ast::minimal_sizes`). `check/tests/examples.rs` runs it over every example using automatic defaults. |
| [`experiments/`](experiments) | The `experiments` crate: Zippel against existing (native/upstream) implementations of the same protocols. Vendored baselines (`*_upstream/` subdirs), Zippel harnesses, the `bench_all` time/memory driver behind the paper's Figure 7 (the artifact's Experiment 1), and cross-verification tests. Not a default workspace member (see below). Distinct from `benches/`, the Criterion benchmarks of Zippel alone. |
| [`tools/`](tools) | Internal developer tools, not shipped. `stack-probe` measures the compile stages' stack use: `min-stack` binary-searches the smallest thread stack that compiles generated deep inputs (a child process per attempt, since an overflow aborts), and `frames` lists the largest prologue frames of a debug binary via objdump (x86-64). A minimum that grows with input size means some pass recurses per statement or nesting level. |
| [`examples/`](examples) | 30+ protocol implementations. Each `examples/<name>/` has a `<name>.zippel` source file and a `main.rs` harness that compiles it against a concrete curve and runs prover/verifier/analyses. `examples/main.rs` is the single dispatch binary (`cargo zrun run <name> --size NAME=VALUE ...`; `cargo zrun analyze <name> [completeness|zk|soundness]`). Each module registers `spec()` with its source, curve, size defaults, input generator and analyses (soundness owns its round parameters). `examples/common/cli.rs` handles common size/backend arguments; `examples/common/mod.rs` owns size resolution, execution, analysis and uniform reporting. It prepares the analysis graph before timing passes. |
| [`artifact/`](artifact) | Docker image and scripts (`artifact/scripts/`) to reproduce the paper's compilation/runtime benchmarks and completeness/soundness analysis results. |
| [`docs/`](docs/library-usage.md) | How to depend on Zippel as a library from an external crate. |
| `paper.pdf` | The design/evaluation paper this repo implements. |

Workspace members (`Cargo.toml`): `lang`, `lang/lang-derive`, `runtime`,
`share`, `graph`, `backend`, `analyses`, `fmt`, `check`, `experiments`, `tools`.
Only a subset are **default members** (`.`, `lang`, `runtime`, `share`, `graph`,
`backend`, `analyses`, `check`) — `fmt`, `experiments` and `tools` require
`--workspace` or `-p <crate>` explicitly, and `experiments` additionally needs `gcc`, `m4`,
`pkg-config` (arkworks/GMP) and pulls in upstream comparison libraries.

## Language quick reference

A `.zippel` file declares one or more `proto`s, generic over curve/field
types (`G: Group`, `F: Scalar<G>`, `GT: Pairing<G1, G2>`), with arguments
qualified `witness` (prover-secret), `instance` (public to both), or
`extra` (prover-only, not part of the witness/transcript). An optional
`where` clause states the relation being proven (used only by the static
analyses, not executed). Inside the body: `random<T>` samples blinding
values, `challenge<T>` draws a Fiat–Shamir challenge, `<-` both computes
and appends a value to the transcript, `let` is a local (non-transcript)
binding, and `verify(...)` is the final check. A sample is resampled while
excluded: `F - v` excludes the entries of a vector `v` (`F - [0]` samples a
nonzero value; for a challenge, `v` is one the verifier computes), and
`F - roots_of_unity(n)` every `x` with `x^n == 1`. The analyses encode each
exclusion as a generator, in every analysis. A division by zero fails the run with
`RuntimeError::DivisionByZero`, and completeness must prove every
prover/verifier divisor nonzero (see `analyses/src/ideal/ops/div.rs` and
`sample.rs`), so divide by what the exclusions make nonzero, such as `c - a`
for `c <- challenge<F - [a]>`. See
`CONTRIBUTING.md`'s "Creating a new protocol with Zippel" section for a
full worked example, or any file under `examples/*/*.zippel`. The parser
requires size-type variables to start uppercase and values lowercase.

## Build, test, and format

Requires **nightly Rust** (pinned in `rust-toolchain.toml`, resolved
automatically by `rustup`) — Zippel does not build on stable.

```bash
cargo build                       # default members only
cargo test                        # default members only
cargo test --workspace            # everything, incl. benchmarks (needs gcc/m4/pkg-config)
cargo zrun                        # list example protocols
cargo zrun run kzg --size N=2      # prove and verify
cargo zrun analyze kzg --size N=2  # static analyses only
cargo zrunr run hyperplonk_piop --size S=3 # release build

# run every compile-time check without a harness; unset Size params get minimal defaults
cargo zcheck [--size N=2]... FILE...

cargo fmt --all -- --check              # Rust formatting
cargo clippy --workspace --all-targets  # lints
cargo clippy -p experiments --all-targets --features dhat  # lints the heap-profiling code
cargo zfmt --check examples/*/*.zippel  # .zippel formatting (--write to reformat)
```

`zrun`, `zrunr`, `zcheck`, and `zfmt` are aliases in `.cargo/config.toml` (e.g.
`zcheck` = `run -q -p check --bin zippel-check --`). The last four commands plus
`cargo test --workspace` and every example with
`cargo zrunr run <name> --size NAME=VALUE ...` are what CI runs
(`.github/workflows/ci.yml`: one lint job, three test jobs, one examples job;
tests built optimized, `--locked`); run them before committing. Some `analyses`
tests use an optional Singular backend for Gröbner bases and are skipped with a
warning if `singular` is not on `PATH`.

CI also rejects any path component that is a reserved Windows device
name (`con`, `prn`, `aux`, `nul`, `com1`-`com9`, `lpt1`-`lpt9`,
case-insensitive, extension ignored).

## Adding a new protocol

See `CONTRIBUTING.md` → "Creating a new protocol with Zippel" for the full
step-by-step (create `examples/<name>/{<name>.zippel,main.rs}`, register it in
`examples/main.rs`, register an `ExampleSpec<ArkBls12_381>`). Input generators
read the explicit size context; shared code owns compilation, execution,
analysis and output. With no size flags, defaults apply. Any explicit sizes
replace the entire default set and must cover every declared Size. CI runs each
registration at its defaults.

Iterate on the `.zippel` file with `cargo zcheck` before writing the harness: if
it passes, compilation and projection will too. It reports errors with source
locations, including a `verify` that depends on a witness or on a `random`
value; fix those by sending what the check needs with `<-`, never by reading the
witness. Checks run at concrete sizes. Automatic defaults satisfy size/operator
constraints and cover overloads in function groups reachable from protocols;
unused helpers are still typechecked. Use `--size` to check specific sizes.

## Conventions worth knowing

- `[lints.rust] missing_docs = "warn"` and Clippy `pedantic`/`nursery`
  are warn-level workspace-wide (`Cargo.toml`); public items are
  expected to have doc comments.
- The default dev profile trims debug info (`line-tables-only`, and 0
  for dependencies) to keep `target/` small, since arkworks' generics
  otherwise bloat debug info; use `CARGO_PROFILE_DEV_DEBUG=2` for full
  backtraces when needed.
- Tests live alongside source as `tests/` submodules inside each crate's
  `src/` (e.g., `graph/src/tests/`, `analyses/src/tests/`) as well as
  top-level `<crate>/tests/` integration tests (snapshot tests for
  `lang`, `fmt`, `analyses` live under `tests/snapshots` /
  `tests/gb_snapshots`).
- Expressions live in an append-only arena (`lang::ast::Exprs`, children before
  parents, nodes never rewritten in place). `Exp::Block` owns a `Block` with
  `Vec<Spanned<Stmt>>` and an optional tail expression. `Stmt::{Let, Log, Discard}`
  hold expression IDs; statements themselves never go in the arena. `lang` has no
  expression printer: diagnostics label spans. A pass that doesn't depend on what a
  node means uses `lang/src/ast/walk.rs` instead of matching every `Exp` variant:
  `Exp::for_each_child`/`for_each_child_mut`, or `ExpRef::walk` (iterative, evaluation
  order; `Bind`/`Unbind` events mark where each variable's scope starts and ends, each
  `Bind` saying what the variable is bound to (`Bound`: a statement's value, a
  comprehension domain's elements, a `fun` parameter), and `InScope` resolves names
  from them, holding a pass's record per binding). The binder
  rules live only there.
  Direct syntactic effects for purity queries and relation diagnostics are
  described in `ast/effect.rs`; their different purity policies remain explicit.
  Type inference is such a walk too: each rule in `lang/src/typ/infer/` types a
  node from its children's types (`Env::typ`). The `TypeTable` also stores resolved
  calls (declaration, instantiated signature and substitution); lowering reads
  these records and infers fresh records for appended bodies. Lowering borrows
  immutable definitions and shares a signature set across scopes. Only lowering
  and `zippel-fmt` recurse, under `#[lang::stack_guard]`. The formatter's methods
  share a cursor/style context; documents borrow its per-call arena independently
  of the context's mutable borrow.
- No pass relies on a large thread stack: walks are iterative, the rest recurse
  under `#[lang::stack_guard]`, and the workspace sets no `RUST_MIN_STACK` or
  big worker threads. Environments that enter and leave scopes (inference's and
  lowering's variables) bind into a `share::ScopedCtx` and roll back to a mark
  instead of cloning a map; `Ctx` is a plain `BTreeMap`, so its clones copy.
  `tools`' `stack-probe min-stack` shows whether a change made stack use grow
  with input size.
- The `nothing` module in `backend` is a placeholder/no-op curve
  implementation, not a real backend — don't confuse it with
  `ArkBls12_381` etc. when picking a concrete type for new code.
- If a build runs out of disk, `cargo clean -p <crate>` for crates you
  aren't rebuilding.
