# Zippel Compiler

[![CI](https://github.com/elefthei/zippel/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/elefthei/zippel/actions/workflows/ci.yml)

Zippel compiles cryptographic protocols written in the Zippel language into optimized prover and verifier code, with static analyses for soundness, completeness, and zero-knowledge. **Prototype — not for production use.**

## Installation

Requires [Rust](https://www.rust-lang.org/) nightly.

```bash
git clone https://github.com/elefthei/zippel
cd zippel
cargo build
```

## Usage

```bash
cargo run --example ipa          # run the IPA example
cargo run --example schnorr      # run Schnorr protocol
cargo run --example kzg          # run KZG commitment
cargo test                       # run all tests
```

Available examples: `ipa`, `ipa_optimized`, `ipa_field`, `schnorr`, `cp`, `kzg`, `sumcheck`, `zerocheck`, `hadamard`, `mle`, `toy_record`, `marginalize`.

To add a new example, create a `.zippel` file in `examples/` and a corresponding `examples/<name>/main.rs` entry with a `[[example]]` target in the root `Cargo.toml`.

## License

MIT — Copyright (c) 2024 University of Pennsylvania | Distributed Systems Lab
