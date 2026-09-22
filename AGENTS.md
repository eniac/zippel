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

The pipeline is: `.zippel` source → `lang` (parse/typecheck/concretize)
→ `graph` (Graph IR + projection) → `runtime`/`backend` (execution) and,
independently, `graph` → `analyses` (completeness/soundness). `src/lib.rs`
(`ZippelHandler`) wires all of this together and is the top-level API
that examples and external users call into.

## Workspace layout

| Crate / directory | Role |
|---|---|
| [`src/`](src/lib.rs) | Top-level `zippel` crate. `ZippelHandler<C>` drives the whole pipeline for one `arkworks` backend `C`: parse → concretize → build Graph IR → project prover/verifier → run → analyze. Re-exports the member crates so downstream users only depend on `zippel`. |
| [`lang/`](lang) | The Zippel language: lexer/parser (`parser/`), AST (`ast/`), type system incl. sized/visibility types (`typ/`), semantic checks like dead-variable and purity analysis (`semantic/`), diagnostics (`diagnostic/`). Has its own proc-macro helper crate, `lang/lang-derive`. |
| [`graph/`](graph) | Graph IR: node definitions (`node.rs`), dependency/sequencing edges (`dep.rs`), the domain separator / Fiat–Shamir transcript machinery (`domain_seperator.rs`), and prover/verifier projection. `eval/` evaluates operations for testing. |
| [`backend/`](backend) | Concrete algebraic types and operations backed by `arkworks` (`ark-ff`, `ark-ec`, `ark-poly`, ...): field/group/pairing config (`config.rs`, `types.rs`), runtime values (`values.rs`), the operator implementations (`op.rs`), polynomial representations (`poly_variant.rs`, `virtual_polynomial.rs`). `nothing/` is a no-op backend used where no concrete curve is needed (e.g., some analysis paths). |
| [`runtime/`](runtime) | Executes a projected Graph IR DAG: work-stealing scheduler (`queue.rs`), graph execution and transcript/Fiat-Shamir handling (`graph.rs`), error types (`error.rs`). |
| [`analyses/`](analyses) | Completeness (`completeness.rs`) and (generalized) special-soundness (`soundness.rs`) analyses, plus zero-knowledge/qualifier propagation (`knowledge.rs`, `qualifier.rs`). Encodes Graph IR as polynomial ideals (`ideal/`, `frontend/`) and checks ideal membership via a Gröbner-basis backend (`backend/`, including an optional Singular integration in `backend/singular.rs`). `extractor.rs` builds candidate knowledge extractors for the soundness check. |
| [`share/`](share) | Small utilities shared across the workspace: a generic `Ctx` map keyed by identifiers (`context.rs`), tree traversal helpers (`traversal.rs`), pretty-printing (`pretty.rs`), macros (`macros.rs`). |
| [`fmt/`](fmt) | `zippel-fmt`, the source formatter for `.zippel` files (binary in `fmt/src/bin/zippel-fmt.rs`). |
| [`check/`](check) | `zippel-check`: every compile-time check, no harness or inputs. `lang::check` (`lang/src/check.rs`) parses, concretizes sizes, and type-checks; `check/src/lib.rs` then builds the Graph IR and projects prover/verifier exactly like `ZippelHandler::compile`, mapping graph errors back to source spans. `check/tests/examples.rs` runs it over every example; `EXAMPLE_SIZES` there lists the examples that need non-default sizes. |
| [`benchmarks/`](benchmarks) | Criterion-style benchmarks comparing Zippel-generated code against hand-optimized native/upstream baselines (`*_upstream/` subdirs) for protocols like Schnorr, KZG, IPA, Hyrax, Spartan, PST13, Pari. Not a default workspace member (see below). |
| [`examples/`](examples) | 30+ protocol implementations. Each `examples/<name>/` has a `<name>.zippel` source file and a `main.rs` harness that compiles it against a concrete curve and runs prover/verifier/analyses. `examples/main.rs` is the single dispatch binary (`cargo zrun <name>`); `examples/common/analysis.rs` has shared harness helpers (`time_analysis!` macro, etc.). |
| [`artifact/`](artifact) | Docker image and scripts (`artifact/scripts/`) to reproduce the paper's compilation/runtime benchmarks and completeness/soundness analysis results. |
| [`docs/`](docs/library-usage.md) | How to depend on Zippel as a library from an external crate. |
| `paper.pdf` | The design/evaluation paper this repo implements. |

Workspace members (`Cargo.toml`): `lang`, `lang/lang-derive`, `runtime`,
`share`, `graph`, `backend`, `analyses`, `fmt`, `check`, `benchmarks`. Only a
subset are **default members** (`.`, `lang`, `runtime`, `share`, `graph`,
`backend`, `analyses`, `check`) — `fmt` and `benchmarks` require `--workspace` or
`-p <crate>` explicitly, and `benchmarks` additionally needs `gcc`, `m4`,
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
binding, and `verify(...)` is the final check. See
`CONTRIBUTING.md`'s "Creating a new protocol with Zippel" section for a
full worked example, or any file under `examples/*/*.zippel`.

## Build, test, and format

Requires **nightly Rust** (pinned in `rust-toolchain.toml`, resolved
automatically by `rustup`) — Zippel does not build on stable.

```bash
cargo build                       # default members only
cargo test                        # default members only
cargo test --workspace            # everything, incl. benchmarks (needs gcc/m4/pkg-config)
cargo zrun                        # list example protocols
cargo zrun kzg                    # run one, e.g. kzg, schnorr, spartan, ...
cargo zrunr hyperplonk            # same, release build

# run every compile-time check without a harness; unset Size params get minimal defaults
cargo zcheck [--size N=2]... [--verbose] FILE...

cargo fmt --all -- --check              # Rust formatting
cargo clippy --workspace --all-targets  # lints
cargo zfmt --check examples/*/*.zippel  # .zippel formatting (--write to reformat)
```

`zrun`, `zrunr`, `zcheck`, and `zfmt` are aliases in `.cargo/config.toml`
(e.g. `zcheck` = `run -q -p check --bin zippel-check --`). The last three
commands plus `cargo test --workspace` are what CI runs (CI spells out the
aliases); run them before committing. Some `analyses` tests use an
optional Singular backend for Gröbner bases and are skipped with a
warning if `singular` is not on `PATH`.

CI also rejects any path component that is a reserved Windows device
name (`con`, `prn`, `aux`, `nul`, `com1`-`com9`, `lpt1`-`lpt9`,
case-insensitive, extension ignored).

## Adding a new protocol

See `CONTRIBUTING.md` → "Creating a new protocol with Zippel" for the
full step-by-step (create `examples/<name>/{<name>.zippel,main.rs}`,
register it in `examples/main.rs`, write a harness using
`ZippelHandler<ArkBls12_381>`). Reuse `examples/common::run_prover_and_verify`
and `examples/common::time_analysis!` rather than duplicating harness
boilerplate.

Iterate on the `.zippel` file with `cargo zcheck` before writing the
harness: if it passes, `compile` will too. It reports errors with source
locations, including a `verify` that depends on a witness or on a
`random` value; fix those by sending what the check needs with `<-`,
never by reading the witness. Checks run at concrete sizes, so pass
`--size` values the protocol actually supports. If the example needs
non-default sizes, add it to `EXAMPLE_SIZES` in `check/tests/examples.rs`.

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
- The `nothing` module in `backend` is a placeholder/no-op curve
  implementation, not a real backend — don't confuse it with
  `ArkBls12_381` etc. when picking a concrete type for new code.
