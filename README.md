# Zippel

[![CI](https://github.com/eniac/zippel/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/eniac/zippel/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)
[![rustc nightly](https://img.shields.io/badge/rustc-nightly-orange.svg)](rust-toolchain.toml)

Zippel is a choreographic language, compiler, and runtime for cryptographic
proof systems. A single `.zippel` source file describes a protocol the way a
cryptography paper would, and Zippel compiles it into a computation graph
(the Graph IR) from which it derives:

- optimized, auto-parallelized prover and verifier binaries built on
  [`arkworks`](https://github.com/arkworks-rs), and
- fully automated static analyses that check completeness and special
  soundness directly from the protocol's specification, using ideal
  membership over Gröbner bases.

Over 30 proof systems are implemented in `examples/`, ranging from
textbook Sigma protocols (Schnorr, Chaum-Pedersen) to modern SNARKs and
polynomial commitment schemes (Groth16, Spartan, HyperPlonk, KZG,
Bulletproofs, Hyrax, PST13, Dory).

> **Status: research prototype.** Zippel has not been independently
> audited. Do not use it to protect anything of value.

## Repository structure

| Crate / directory | Description |
|---|---|
| [`lang`](lang) | Zippel language: parser, type checker, size concretization |
| [`graph`](graph) | Graph IR construction and prover/verifier projection |
| [`backend`](backend) | Concrete curve and field types backed by `arkworks` |
| [`analyses`](analyses) | Completeness and special-soundness analyses over Gröbner bases |
| [`runtime`](runtime) | Executes projected prover/verifier graphs on a work-stealing scheduler |
| [`share`](share) | Utilities shared across the workspace |
| [`fmt`](fmt) | `zippel-fmt`, the source formatter |
| [`benchmarks`](benchmarks) | Zippel vs. hand-optimized native baselines |
| [`examples`](examples) | Protocol implementations and their Rust harnesses |
| [`artifact`](artifact) | Docker image and scripts to reproduce our evaluation results |

## Installation

Zippel requires [Rust](https://www.rust-lang.org/) nightly; the exact
toolchain is pinned in [`rust-toolchain.toml`](rust-toolchain.toml) and
resolved automatically by `rustup`. Zippel does not build on stable Rust.

```bash
git clone https://github.com/eniac/zippel
cd zippel
cargo build
```

## Usage

All protocol examples are compiled into one binary, dispatched by name:

```bash
cargo run --example zippel -- ipa       # run the IPA example
cargo run --example zippel -- schnorr   # run the Schnorr protocol
cargo run --example zippel -- kzg       # run the KZG commitment scheme
cargo ex ipa                            # shorthand alias (dev profile)
cargo exr hyperplonk                    # shorthand alias (release profile)
cargo run --example zippel              # list every available example
```

### Testing

```bash
cargo test           # test the default workspace members
cargo test-all       # test every crate in the workspace
cargo test-verbose   # as above, with test output unsuppressed
```

Some tests (`analyses`' Gröbner-basis regression suite) use
[Singular](https://www.singular.uni-kl.de/) as a backend when it is on
`PATH`, and are skipped with a warning otherwise.

## Reproducing our evaluation

`artifact/` contains a Dockerfile and scripts that build Zippel and
reproduce the benchmarks, completeness analyses, and special-soundness
analyses reported in our IEEE S&P 2027 submission. See
[`artifact/README.md`](artifact/README.md) for details.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for development setup, the
checks run in CI, and how to add a new protocol example.

## License

Zippel is licensed under the [MIT license](LICENSE-MIT).

Copyright (c) 2024-2026 University of Pennsylvania, Distributed Systems Lab.