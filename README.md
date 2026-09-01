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

All protocol examples are compiled into one binary, dispatched by name:

```bash
cargo run --example zippel -- ipa       # run the IPA example
cargo run --example zippel -- schnorr   # run Schnorr protocol
cargo run --example zippel -- kzg       # run KZG commitment
cargo ex ipa                            # shorthand alias (dev)
cargo exr hyperplonk                    # shorthand alias (release)
cargo run --example zippel              # list every available example
cargo test                              # run all tests
```

A single example target keeps `target/` small: one link product and one
debug-info file for all protocols instead of one per protocol.

To add an example, create `examples/<name>/<name>.zippel` and
`examples/<name>/main.rs` exposing `pub fn run(_args: &[String])`, then add a
`#[path] mod` line and an `EXAMPLES` row in `examples/main.rs`. No
`Cargo.toml` change is needed.

## License

MIT — Copyright (c) 2024 University of Pennsylvania | Distributed Systems Lab
