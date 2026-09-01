# benchmarks

Wall-clock comparison between **zippel-compiled protocols** and **native Rust
baselines** for nine SNARK / commitment / signature schemes. Each system runs
both sides on the same machine, same curve, same input size, inside the same
rayon thread pool — only the implementation differs.

Systems benched: `schnorr`, `sumcheck`, `ipa`, `kzg`, `pari`, `groth16`,
`pst13`, `hyrax`, `spartan`.

For every (system, log_size, threads) point the bench measures:

- `prover_time_ms` — zippel prover wall-clock
- `verifier_time_ms` — zippel verifier wall-clock
- `native_prover_time_ms` — native baseline prover wall-clock
- `native_verifier_time_ms` — native baseline verifier wall-clock
- `compiler` — zippel compile time (source → executable graph)
- `zippel_ncloc`, `native_ncloc` — non-comment source lines, one number per side

All times in milliseconds, written to a single CSV.

## Quick start

From the repository root:

```sh
benchmarks/run_all.sh
```

Default: every system, threads ∈ {1, 2, 4, 8, 16}, full-size grid, output to
`bench_results.csv`. Takes a long time at log_size=18-20 single-thread —
expect tens of minutes per system per thread count.

For iteration, narrow the sweep with environment variables:

```sh
SYSTEMS=hyrax THREADS=1,4,8 OUT=hyrax.csv PROVER_SAMPLES=3 benchmarks/run_all.sh
```

On a multi-socket NUMA box (e.g. Xeon Platinum with several CPU nodes), pin
to one socket so memory locality is consistent across thread counts:

```sh
SYSTEMS=hyrax THREADS=1,2,4,8 OUT=hyrax.csv numactl --cpunodebind=0 --membind=0 benchmarks/run_all.sh
```

## Folder layout

```
benchmarks/
├── Cargo.toml             excluded from the workspace — see Cargo.toml notes
├── run_all.sh             orchestrator: sweeps threads × systems → one CSV
├── run_sweep.sh           older orchestrator (mostly superseded by run_all.sh)
├── run_sweep_safe.sh      older orchestrator with crash-recovery
├── README.md              this file
├── src/
│   ├── lib.rs             public surface: re-exports each system + Timing + PROVER_SAMPLES
│   ├── cache.rs           on-disk SRS cache (artifacts/*.bin); skips long keygens on re-run
│   │
│   ├── schnorr.rs         each *.rs file holds two pub mods:
│   ├── sumcheck.rs           - zippel_side::Setup     compiles .zippel, holds inputs
│   ├── ipa.rs                - native_side::Setup     calls the upstream crate / vendored copy
│   ├── kzg.rs              both expose `Setup::new(...)` + `Setup::time_protocol(...) -> Timing`
│   ├── pari.rs
│   ├── groth16.rs
│   ├── pst13.rs
│   ├── hyrax.rs
│   ├── spartan.rs
│   │
│   ├── pari_upstream/     vendored garuda-pari (was outside arkworks-0.6 / fixes for fair compare)
│   ├── pst13_upstream/    vendored ark-poly-commit::multilinear_pc with two open() fixes
│   ├── hyrax_upstream/    vendored ark-poly-commit::hyrax with flat-matrix row_mul rewrite
│   ├── sumcheck_upstream/ vendored hyperplonk sumcheck (ported to ark 0.6)
│   │
│   └── bin/
│       ├── bench_all.rs           main entry point used by run_all.sh
│       ├── schnorr.rs, sumcheck.rs, …   single-system one-shot runners (legacy / debug)
│       ├── groth16_profile.rs     groth16 profiling harness
│       ├── spartan_bench.rs       libspartan-only timing
│       └── spartan_compare.rs     spartan zippel vs native side-by-side
│
├── benches/               criterion benches for a couple of systems (rarely used now)
├── artifacts/             auto-created at runtime — on-disk SRS cache (see cache.rs)
└── *.csv                  sample / saved bench outputs
```

`*_upstream/` modules exist where the original upstream code had a bug,
performance issue, or used an older arkworks version. The vendored copy is
the actual baseline the bench measures against (so the comparison is "zippel
vs a well-implemented native PST13", not "zippel vs ark-poly-commit-0.6's
known-buggy MSM scheduler"). Each `*_upstream/mod.rs` documents what was
changed and why at the top of the file.

## Driver: `run_all.sh`

Wrapper around the `bench_all` binary that sweeps `RAYON_NUM_THREADS`. In-
process pool reconfiguration via `rayon::ThreadPool::install` hangs on
arkworks' parallel paths, so the script re-invokes the binary once per
thread count and appends each iteration's rows to the same CSV. Ctrl-C
between iterations preserves rows that completed.

Environment variables:

| var | default | meaning |
|-----|---------|---------|
| `THREADS` | `1,2,4,8,16` | comma-separated thread counts to sweep |
| `OUT` | `bench_results.csv` | output CSV path |
| `SYSTEMS` | (all) | comma-separated subset, e.g. `hyrax,pst13` |
| `QUICK` | `0` | set `1` for a smaller log_size grid (iteration mode) |
| `PROVER_SAMPLES` | `1` | how many prover samples to average per measurement |

`PROVER_SAMPLES > 1` is recommended at low thread counts to average over
server jitter — single-sample t=1 timings can vary 20-50% on a loaded box.
Each measurement runs the prover `PROVER_SAMPLES` times back-to-back and
records the mean.

## Driver internals: `bench_all` binary

`run_all.sh` builds and invokes `<workspace root>/target/release/bench_all`. Its flags map
mostly to the script's env vars but can be used directly for one-off runs:

```sh
cargo run --release --manifest-path benchmarks/Cargo.toml --bin bench_all -- \
    --systems hyrax,pst13 \
    --sizes 16,18 \
    --out custom.csv \
    --threads-label 8
```

Flags:

- `--out PATH` — output CSV path (default `bench_results.csv`)
- `--systems S1,S2,...` — restrict to a subset of systems
- `--sizes N1,N2,...` — override the per-system log_size grid
- `--quick` — small grid for fast iteration
- `--threads-label N` — overrides the `threads` CSV column (the script uses
  this so `RAYON_NUM_THREADS=N`'s value shows up consistently even when
  rayon's pool reports something else)
- `--no-header --append` — used by `run_all.sh` to concatenate
  multi-thread-count runs into one CSV

Single-system entry points in `src/bin/` (e.g. `cargo run --release --bin
hyrax`) exist for debugging one system in isolation without spinning up
others — they're independent of `bench_all` and don't share CSV output.

## CSV format

```
system,threads,log_size,prover_time_ms,verifier_time_ms,native_prover_time_ms,native_verifier_time_ms,zippel_ncloc,native_ncloc,compiler
```

`log_size` is log₂ of each system's natural complexity parameter (so points
plot linearly on a log-size x-axis):

- `schnorr` — `0` (fixed protocol, no size knob)
- `sumcheck` — `num_vars` (hypercube has 2^nv points)
- `ipa` — `S` (vector length N = 2^S)
- `kzg` — log₂(N) where N = coefficient count
- `pari` — `M` (K = 2^M constraints)
- `groth16` — log₂(num_constraints)
- `pst13` — `N` (polynomial has 2^N coefficients)
- `hyrax` — `N` (multilinear poly has 2^N evaluations; N must be even)
- `spartan` — `M` (num_cons = 2^M)

`compiler` is the zippel compile time alone: source parse + concretization
+ graph construction + prover/verifier projection. It excludes the Rust
compiler (which builds the bench binary once, outside any measurement) and
excludes runtime scheduling and the prove/verify execution.

`zippel_ncloc` is line count of the proto (or its rendered instance, for
systems where the proto is template-generated). `native_ncloc` is the line
count of the native module file or vendored upstream copy. Both are
non-comment, non-blank lines.

## Output caching

Setup-phase artifacts (SRS, universal params, large preprocessed data) are
cached in `artifacts/` keyed by `(system, log_size)`. First run at a given
size builds + saves (cache miss), subsequent runs deserialize from disk
(cache hit). Cache messages are printed to stderr during the bench.

Override the cache directory with `BENCH_ARTIFACTS_DIR=/path/to/dir`. The
cache is always populated outside any timed region (callers wrap setup in
`setup_pool().install(...)`), so cache I/O never enters a measured number.

Delete `artifacts/` to force a clean rebuild — useful after curve or
serialization-format changes.

## Tips

- **Bench runs are long.** At log_size=20 single-thread some systems take
  10+ minutes per iteration. Use `QUICK=1` or `--sizes` for development.
- **Don't compare across machines.** Apple Silicon and Xeon have different
  per-core characteristics and different rayon overheads; absolute numbers
  vary 5-10× between architectures.
- **t=1 numbers are noisy.** Single-sample timings at one thread on a
  loaded server jitter 20-50%. Use `PROVER_SAMPLES=3` (or higher) when t=1
  matters for your analysis.
- **`numactl` for Xeon multi-socket.** Without pinning, the bench scatters
  threads across sockets and adds NUMA crossbar costs that confound the
  scaling story. Pin to a single NUMA node for clean scaling curves.
