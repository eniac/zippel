# ark-gb

Gröbner-basis engine over [arkworks](https://github.com/arkworks-rs/algebra) fields.

This crate is a fork of [BrentBaccala/rustgb](https://github.com/BrentBaccala/rustgb)
(a Rust port of [Singular](https://www.singular.uni-kl.de/)'s `bba`
engine), generalized so the coefficient ring is any `F: ark_ff::Field`
instead of the hardcoded `Z/p` (`p < 2^31`, u32 + Barrett reduction)
of upstream.

The Singular `cdylib` integration and the C FFI shim from upstream
have been **removed** — this fork is a pure Rust library aimed at
embedding inside arkworks-based protocol pipelines (e.g. zippel).

## Scope

What's in the crate today:

- Field: `F: ark_ff::Field` (work-in-progress on the
  `arkworks-port` branch — `master` still carries upstream's
  `Z/p` until the field generalization lands).
- Monomial: packed-exponent layout (8 bits/variable, 4×u64
  words), supports up to 31 variables. Cached SEV (short
  exponent vector) and total-degree on the struct.
- Polynomial: two backend implementations behind a Cargo
  feature flag — flat parallel-array (default) and singly-linked
  list (`linked_list_poly`). Optional thread-local Node pool for
  the linked-list backend (`linked_list_poly_pool`).
- bba driver: full Buchberger algorithm with the geobucket
  reducer (default) or a heap-based Monagan-Pearce reducer
  (`heap_reducer`). Pair generation, `chainCritNormal`,
  `enterOnePairNormal`, and the LSet structure.
- SIMD: AVX2 paths for the SEV scan
  (`gm::chain_crit_normal`, `bba::reduce_lobject` candidate
  filter) and `Monomial::div`. Compiled in only when AVX2 is
  available at build time.
- Parallel reduction: experimental, behind `ARK_GB_THREADS`
  env var (default 1, serial). Serial path is bit-for-bit
  deterministic; parallel path is not yet validated against
  the staging suite.
- Constraints: degrevlex ordering by default; an `Elim`
  block-elimination order is planned on the `arkworks-port`
  branch.

What's tracked in the ADR ledger
([`docs/design-decisions.md`](docs/design-decisions.md)) — read
that before any non-trivial structural change. Every decision
records its rationale against both Singular (the reference
implementation) and FLINT (a second polynomial-layer reference,
when applicable).

## Building

```bash
cargo build --release
cargo test --release
```

For benchmark builds on AVX2-capable hosts, enable native
codegen so the SIMD paths in `src/simd.rs` get compiled in:

```bash
RUSTFLAGS="-C target-cpu=native" cargo build --release
```

Cargo features:

| Feature                  | Default | Effect                                                  |
|--------------------------|:-------:|---------------------------------------------------------|
| `heap_reducer`           |   on    | Monagan-Pearce reducer (ADR-008). Disable with `--no-default-features` to use the geobucket (ADR-002). |
| `linked_list_poly`       |   off   | Linked-list `Poly` backend instead of flat array        |
| `linked_list_poly_pool`  |   off   | Thread-local Node pool for the list backend (requires `linked_list_poly`) |

The Singular-side integration is exercised through the
staging-validation script described in
[`~/Singular-rustgb/CLAUDE.md`](../Singular-rustgb/CLAUDE.md).

## Layout

```
src/
├── lib.rs              crate root
├── ring.rs             Ring (BITS_PER_VAR, MAX_VARS, ordering, field)
├── ordering.rs         MonoOrder enum (degrevlex only)
├── field.rs            Z/p with Barrett reduction
├── monomial.rs         packed-exponent monomial + arithmetic + cmp
├── poly/
│   ├── mod.rs          backend dispatcher (feature-flag re-exports)
│   ├── poly_vec.rs     flat parallel-array backend (default)
│   ├── poly_list.rs    singly-linked-list backend
│   └── node_pool.rs    thread-local Node allocator (pool / forwarder)
├── bba.rs              Buchberger driver
├── kbucket.rs          geobucket
├── reducer.rs          PolyCursor + heap reducer
├── sbasis.rs           SBasis (S, T mirrors of Singular)
├── lobject.rs          LObject — pending S-pair record
├── lset.rs             LSet — sorted pair queue
├── pair.rs             Pair record
├── bset.rs             B-set (active basis indices used in chain crit)
├── gm.rs               chainCritNormal + enterOnePairNormal
├── computation.rs      compute_gb driver
├── parallel.rs         parallel reduction (experimental)
├── simd.rs             AVX2 SEV scan + scalar fallback
└── ffi.rs              C-ABI surface for Singular

tests/
├── field_props.rs      proptest properties, Z/p
├── monomial_props.rs   proptest properties, monomial arithmetic
├── poly_props.rs       proptest properties, polynomial ops
├── kbucket_props.rs    proptest properties, geobucket invariants
├── lset_props.rs       proptest properties, LSet invariants
├── sbasis_props.rs     proptest properties, SBasis invariants
├── gm_props.rs         proptest properties, chain criterion
├── bba_props.rs        cross-validation: heap vs geobucket reducer
├── bba_fixtures.rs     committed regression fixtures
├── ffi.rs              FFI surface tests
├── cancel.rs           cancellation/abort path tests
└── fixtures/           expected-output fixtures

examples/
├── compute_gb.rs       reference driver
├── sanity.rs           timing for Poly::add and Poly::sub_mul_term
├── kbucket_bench.rs    geobucket microbenchmark
├── gm_bench.rs         pair-criterion microbenchmark
├── perf_cyclic5.rs     end-to-end perf harness on cyclic-5
└── mul_probe.rs        codegen probe for Monomial::mul
```

## Reference reading

- [`docs/design-decisions.md`](docs/design-decisions.md) — ADR-style
  ledger of architectural choices, with Singular and FLINT
  comparisons. Read before making non-trivial structural changes.
- Singular: `~/Singular/kernel/GBEngine/` (`kstd2.cc`,
  `kInline.h`, `kBuckets.cc`) — primary reference
  implementation.
- FLINT: `~/flint/src/{mpoly,nmod_mpoly}/` — secondary reference
  for polynomial-layer decisions; explicitly N/A for GB-engine
  decisions (FLINT has no GB engine).
- mathicgb (`~/mathicgb/src/mathicgb/`) — structural templates
  consulted, not vendored.
- feanor-math `zn_64` — structural model for the `Z/p`
  implementation.

License: GPL-3.0-or-later. No code from the references above was
vendored or directly copied; algorithms are re-derived in Rust.

---

*This crate was researched and written by an AI assistant (Claude)
on behalf of Brent Baccala (cosine@freesoft.org). The ADR ledger
([`docs/design-decisions.md`](docs/design-decisions.md)) records
the architectural decisions and the references they were derived
from.*

## Reproducible benchmarks

`bench-baseline.sh <name>` runs the `groebner` Criterion suite with
`RUSTFLAGS="-C target-cpu=native"` and saves a baseline next to a
provenance manifest under `target/criterion/.baselines/`.

```bash
./bench-baseline.sh before-i1                  # full sweep
./bench-baseline.sh before-i1 --quick          # ~1 minute smoke
CARGO_BENCH_ARGS="--features linked_list_poly" ./bench-baseline.sh after-list
```

`.cargo/config.toml` already pins `target-cpu=native` for repo-local
builds, so the AVX2 sev-sweep path in `src/simd.rs`
(`#[cfg(target_feature = "avx2")]`) is compiled in by default.
