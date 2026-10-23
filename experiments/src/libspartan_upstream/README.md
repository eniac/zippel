# Spartan 0.9.0 test copy

Source: the `spartan` 0.9.0 crate resolved by `Cargo.lock`, published from
[Microsoft Spartan](https://github.com/microsoft/Spartan). `LICENSE` and
`NOTICE.md` are copied with the Rust sources. The native benchmark still uses
that exact crates.io dependency.

This module is compiled only for experiments library tests. Changes from the
crate are limited to module-relative imports, aliases for its original digest
and SHA3 dependencies, crate-visible proof fields/modules, and generic
proof-transcript parameters. The existing `ProofTranscript` trait supplies the injection point;
its message encoding defaults are shared by Merlin and the test challenges.
`random.rs` still uses real Merlin and `OsRng`; fixed challenges do not replace
prover randomness. `compatibility_tests.rs` is new.

Spartan cross-tests pass the shared `cross::Challenges` sequence directly as the
native proof transcript. Ordinary native tests and the compatibility tests pass
`merlin::Transcript`. The compatibility tests exchange serialized proofs with the
actual dependency in both directions using real Fiat–Shamir.

```sh
cargo test --locked -j 6 -p experiments --lib spartan::cross_tests
cargo test --locked -j 6 -p experiments --lib compatibility_tests
```

For ark-spartan, the cross-test adapter supplies `rho = 1` for the PCS batching
challenge absent from that older implementation. See `docs/CROSS_VERIFY_PLAN.md`
for the protocol differences and current coverage.
