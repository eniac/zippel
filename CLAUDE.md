# Zippel

## Overview

Zippel is a compiler for cryptographic protocols (zero-knowledge proofs, commitment schemes) that compiles `.zippel` source files into optimized prover and verifier code with static analyses for soundness, completeness, and zero-knowledge.

## Project Structure

| Path | Type | Purpose |
| ---- | ---- | ------- |
| `lang/` | crate | Parser (PEG), AST, type system |
| `graph/` | crate | DAG IR, operations, static analyses, scheduler |
| `backend/` | crate | Arkworks cryptographic backend abstraction |
| `runtime/` | crate | Parallel execution engine |
| `share/` | crate | Shared utilities (Ctx, Pretty, Traversal) |
| `src/` | crate | Top-level driver (ZippelHandler) |
| `examples/` | dir | 40+ protocol examples (.zippel + main.rs) |
| `docs/` | dir | Formal grammar (Ott format) |

## Quick Reference

### Languages and Tooling

- Languages: Rust (nightly)
- LSPs: rust-analyzer
- Parser: pest (PEG grammar in `lang/src/parser/zippel.pest`)

### Commands

```bash
cargo build                           # Build entire workspace
cargo test --workspace                # Run all tests (alias: cargo test-all)
cargo test -p graph                   # Test single crate
cargo fmt --all -- --check            # Check formatting
cargo clippy --workspace --all-targets # Lint all code
cargo run --example ipa               # Run an example
cargo bench --bench graph_execution   # Run benchmarks
```

### Environment

- Requires Rust nightly (pinned in `rust-toolchain.toml`)
- `RUST_MIN_STACK=33554432` (32 MB) set in `.cargo/config.toml` for deep recursion

## Progressive Disclosure

| Topic | Location |
| ----- | -------- |
| Compilation pipeline | `.github/copilot-instructions.md:36-46` |
| Type system details | `.github/copilot-instructions.md:105-157` |
| Key types & flow | `.github/copilot-instructions.md:65-79` |
| Static analyses | `graph/src/analyses/` |
| Formal grammar | `docs/grammar.ott` |
| PEG parser grammar | `lang/src/parser/zippel.pest` |

## Universal Rules

1. Run `cargo fmt --all -- --check && cargo clippy --workspace --all-targets && cargo test --workspace` before commits
2. Keep PRs focused on a single concern
3. Adding a new example requires registering its `[[example]]` entry in root `Cargo.toml`
4. Most types are parameterized by `C: ArkConfig` for cryptographic generics
5. Use `log` crate macros for logging, no `println!` in library crates

## Code Quality

Formatting and linting are handled by automated tools:

- `cargo fmt --all -- --check` — rustfmt
- `cargo clippy --workspace --all-targets` — clippy (strict, includes tests/examples/benches)

Run before committing. CI enforces these checks.
