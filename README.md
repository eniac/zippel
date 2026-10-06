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

The commands below use Cargo aliases defined in
[`.cargo/config.toml`](.cargo/config.toml), which work from anywhere
inside the repository.

### Running examples

```bash
cargo zrun ipa               # run the IPA example
cargo zrun schnorr           # run the Schnorr protocol
cargo zrun kzg               # run the KZG commitment scheme
cargo zrun                   # list every available example
cargo zrunr hyperplonk_piop  # run in release mode
```

See [`examples/`](examples) for 30+ more protocols implemented in
Zippel.

### Typechecking a protocol

If you are developing a new Zippel protocol and just want to typecheck it to make
sure your syntax is correct and there are no obvious bugs, you can use `cargo zcheck`.
Note that typechecking does not invoke any of our static analyses. This only ensures
the program is valid and the verifier is not using prover-only variables
(instance, extra, random). Since Zippel has sized types, you can also specify the
sizes. Some examples:

```bash
cargo zcheck examples/kzg/kzg.zippel
cargo zcheck --size N=2 examples/marlin_kzg/marlin_kzg.zippel
```

Pass `--size NAME=VALUE` for the sizes you care about; unset `Size` parameters default to the smallest
value that keeps every range non-empty.

### Formatting

```bash
cargo zfmt --check examples/*/*.zippel   # report unformatted files
cargo zfmt --write examples/kzg/kzg.zippel
```

### Testing

```bash
cargo test
```

Some tests use the Singular backend (see Optional dependencies below)
and are skipped with a warning when it isn't found on `PATH`.

## Optional dependencies

[Singular](https://www.singular.uni-kl.de/) provides an alternative
Gröbner-basis backend for the completeness and soundness analyses. It
must be on `PATH` to be used.

## Using Zippel as a library

See [`docs/library-usage.md`](docs/library-usage.md) for how to depend
on Zippel from your own crate, then write, compile, run, and analyze a
protocol.

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
