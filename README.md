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

## Quick start

Clone the repository and build it with [Rust](https://www.rust-lang.org/)
nightly; the exact toolchain is pinned in
[`rust-toolchain.toml`](rust-toolchain.toml) and resolved automatically
by `rustup`. Zippel does not build on stable Rust.

```bash
git clone https://github.com/eniac/zippel
cd zippel
cargo build
```

### Running examples

```bash
cargo run --example zippel -- ipa       # run the IPA example
cargo run --example zippel -- schnorr   # run the Schnorr protocol
cargo run --example zippel -- kzg       # run the KZG commitment scheme
cargo run --example zippel              # list every available example
```

### Testing

```bash
cargo test
```

Some tests (`analyses`' Gröbner-basis regression suite) use
[Singular](https://www.singular.uni-kl.de/) as a backend when it is on
`PATH`, and are skipped with a warning otherwise.

## Writing your own protocol

Zippel is not published on crates.io; depend on it directly from git:

```toml
[dependencies]
zippel = { git = "https://github.com/eniac/zippel" }
```

A protocol is a `.zippel` file describing the prover/verifier
choreography, for example the full Schnorr protocol,
[`examples/schnorr/schnorr.zippel`](examples/schnorr/schnorr.zippel):

```
proto schnorr<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) where h == g * x {
    let r = random<F>;
    u <- g * r;
    c <- challenge<F*>;
    z <- r + x * c;
    verify(g * z == u + h * c)
}
```

A Rust harness compiles it against a concrete curve, supplies witness and
instance values, and runs the prover and verifier:

```rust
use std::path::PathBuf;
use zippel::backend::ArkBls12_381;
use zippel::share::Ctx;
use zippel::{ZippelArgs, ZippelHandler};

let args = ZippelArgs::new(PathBuf::from("path/to/protocol.zippel"));
let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
handler.compile(&Ctx::new()); // size parameters for generic protocols, empty here

let proof = handler.run_prover(&inputs)?;
let result = handler.run_verifier(&proof, &inputs)?;
```

The same handler also exposes `analyze_completeness()`,
`analyze_knowledge()`, and `analyze_special_soundness(l_vec)` for the
static analyses. See [`examples/`](examples) for complete harnesses
covering all 30+ protocols.

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