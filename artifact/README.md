# Zippel: IEEE S&P 2027 Artifact

Zippel is a language, compiler, and runtime for cryptographic proof
systems, with Gröbner-basis-based static analyses that check
completeness and special soundness directly from a protocol's source.
This artifact builds the system in Docker and reproduces the results of
the paper's evaluation (Section 9).

**What it reproduces.**

| Paper | Contents | Reproduced by |
|---|---|---|
| §8 | Size of Zippel's own Rust code, per component | `report_rust_loc.py` |
| Figure 6 | Each protocol's LoC | `report_loc.py` |
| Figure 6, Complete column | Completeness marks and analysis times (§9.3) | Experiment 3 |
| Figure 6, Spec. Sound column | Special-soundness marks and analysis times (§9.3) | Experiment 2 |
| Figure 7 | LoC, Graph IR sizes, prover/verifier speedups and prover peak memory against existing implementations (§9.2) | Experiment 1 |
| §9.1 | Compile times | Experiment 1 |

The protocols the artifact reports on are exactly the paper's: the rows
of Figures 6 and 7, listed in `artifact/scripts/paper.py`. Differences
from the submitted paper are explained where they arise below and
collected in [`index.html`](index.html).

## Repository layout

| Path | What it is |
|---|---|
| `lang/` | Zippel language: parser, type checker, size concretization |
| `graph/` | Graph IR construction and prover/verifier projection |
| `backend/` | arkworks-backed concrete curve/field types |
| `analyses/` | Completeness and special-soundness analyses (Gröbner bases) |
| `runtime/` | Executes the projected prover/verifier graphs |
| `share/` | Shared utilities (`Ctx`, `Set`, etc.) used across crates |
| `fmt/` | `zippel-fmt` formatter; keeps `examples/*.zippel` in the canonical style |
| `examples/` | 30+ `.zippel` protocol implementations and their Rust harnesses |
| `benches/analysis/` | Analysis benches behind Experiments 2 and 3 |
| `benchmarks/` | Zippel vs. native performance comparison (Experiment 1) |
| `analyses/tests/gb_snapshots/` | Analysis correctness and Gröbner-basis regression tests |
| `artifact/` | This package: `Dockerfile` and `scripts/` |

## Setup

Requires [Docker](https://www.docker.com/). Give Docker at least 8 CPU
threads and 64 GB of RAM; the paper's numbers come from an AWS
`m4.4xlarge` instance (16 vCPUs, 64 GB).

- On macOS, open Docker Desktop, go to Settings > Resources to
  configure CPUs and Memory, then Apply & restart. The available memory
  is shared with other containers.

Build the image from the repository root, not from `artifact/`. The
image builds and runs as a non-root user matching your own UID/GID, so
`--build-arg` is required:

```sh
docker build -f artifact/Dockerfile -t zippel-ae \
  --build-arg UID=$(id -u) --build-arg GID=$(id -g) .
```

This installs the nightly Rust toolchain pinned by
`rust-toolchain.toml`, `gcc` and Singular via apt, and prebuilds the
workspace in release mode. The build takes about 10 minutes, produces a
roughly 6 GB image, and needs network access to pull the base image and
fetch crates.

To verify the environment:

```sh
docker run --rm zippel-ae bash artifact/scripts/smoke_test.sh
```

This builds and runs three example protocols, one completeness trial
through Singular, and one `analysis`-bench check. It is not one of the
experiments; it only checks that the toolchain and the Singular
integration work. It finishes in well under a minute and ends with:

```
Smoke test passed.
```

All experiment commands below write their results to
`artifact/output/`, mounted into the container. Create it once:

```sh
mkdir -p artifact/output
```

## Line counts (Figures 6 and 7)

Figure 6's LoC column counts each protocol's non-comment source lines
directly from its `.zippel` file:

```sh
docker run --rm zippel-ae python3 artifact/scripts/report_loc.py
```

Figure 7's two LoC columns (Zippel and the existing implementation)
come from Experiment 1's table. To print them alone, without running
any benchmark:

```sh
docker run --rm zippel-ae \
  cargo run -q --release -p benchmarks --bin bench_all -- --ncloc-only
```

**Difference from the submitted paper.** Most Zippel counts differ from
the submitted paper's. Two changes account for this:

1. `zippel-fmt` did not exist at submission time, so the example files
   were not yet in its canonical style; reformatting them changed line
   counts without changing any semantics.
2. Several protocols' `where`-clause constraints were revised after
   submission (see Experiment 3).

This does not affect the conciseness claim. Only two native counts
moved, slightly (Sumcheck 1544 to 1559, Bulletproofs 166 to 170); the
rest of the movement is on the Zippel side, and Zippel stays
substantially shorter than every existing implementation in Figure 7:

| System | LoC Zippel | LoC Native | Native / Zippel |
|---|---|---|---|
| Sumcheck | 58 → 87 | 1544 → 1559 | 26.6x → 17.9x |
| Schnorr | 7 → 7 | 186 | 26.6x → 26.6x |
| KZG | 14 → 24 | 527 | 37.6x → 22.0x |
| PST13 | 54 → 81 | 250 | 4.6x → 3.1x |
| Groth16 | 36 → 88 | 458 | 12.7x → 5.2x |
| Bulletproofs | 79 → 77 | 166 → 170 | 2.1x → 2.2x |
| Hyrax | 47 → 49 | 277 | 5.9x → 5.7x |
| Spartan (Arkworks) | — → 422 | 2037 | — → 4.8x |
| Spartan (Microsoft) | 461 → 422 | 1867 | 4.0x → 4.4x |
| Dory PCS | — → 304 | 766 | — → 2.5x |
| HyperPlonk | — → 441 | 2828 | — → 6.4x |
| KZH | — → 53 | 221 | — → 4.2x |
| DeKART | — → 130 | 846 | — → 6.5x |
| Pari | 79 → 119 | 1141 | 14.4x → 9.6x |

Each cell reads "submitted → now"; "—" marks a row added to Figure 7
after submission. Groth16 changed the most, yet remains 5.2x shorter
than its native baseline; Spartan's line count decreased.

## Size of Zippel's implementation (Section 8)

Section 8 gives the size of Zippel's own Rust code per component. To
count it:

```sh
docker run --rm zippel-ae python3 artifact/scripts/report_rust_loc.py
```

A line counts if it holds code once comments and blank lines are
removed. Test code (`#[test]` and `#[cfg(test)]` items, and files under
`tests/`) is reported on its own row rather than in its component, and
code vendored from other projects as benchmark baselines
(`benchmarks/src/*_upstream/`) is left out. The script reads the
sources directly, so it needs no build.

## Experiments

| # | Scripts | Produces | Paper |
|---|---|---|---|
| 1 | `run_benchmark.sh`, `process_benchmark.py` | Comparison with existing implementations; compile times | Figure 7; §9.1 |
| 2 | `run_soundness.sh`, `process_soundness.py` | Special-soundness marks and analysis times | Figure 6 (Spec. Sound); §9.3 |
| 3 | `run_completeness.sh`, `process_completeness.py` | Completeness marks and analysis times | Figure 6 (Complete); §9.3 |

---

### Experiment 1: performance and compile time (Figure 7, §9.1)

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" \
  zippel-ae bash -c '
    artifact/scripts/run_benchmark.sh &&
    python3 artifact/scripts/process_benchmark.py'
```

This runs every Figure 7 row at instance size `2^18` (Schnorr has no
size parameter), with the prover at 1, 2, 4 and 8 threads and the
verifier at 1 thread. By default each measurement is taken once; the
paper reports the mean of 10 runs, which you can match with
`-e BENCH_SAMPLES=10` at roughly ten times the runtime. The pinned
results in `benchmarks/*_results.csv` use 10 runs.

To run a subset, pick systems and thread counts:

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" \
  -e SYSTEMS=schnorr,kzg -e THREADS=1,2 \
  zippel-ae bash -c '
    artifact/scripts/run_benchmark.sh &&
    python3 artifact/scripts/process_benchmark.py'
```

For retries, `-e BENCH_ARTIFACTS_DIR=artifact/output/cache` keeps the
SRS caches in the mounted output directory after the container exits.

**What to expect.** The processor prints two tables:

- **Figure 7**, one row per Figure 7 row and in its order:
  - LoC of the Zippel protocol and of the existing implementation;
  - Zippel's prover and verifier Graph IR node counts;
  - prover speedup (existing implementation's time / Zippel's time) at
    each thread count, and verifier speedup at 1 thread;
  - prover peak memory ratio: existing implementation / Zippel prover
    peak heap at 1 thread, where it is deterministic (see
    `benchmarks/README.md`).
- **Compile time** (§9.1): each system's Zippel compile time at the
  benchmark size (parsing, size concretization, type checking, and
  Graph IR construction and projection), then the minimum, maximum and
  median.

Differences from the submitted paper:

- Spartan (Arkworks), Dory PCS, HyperPlonk, KZH and DeKART were added to
  the comparison after submission, as were the Graph IR sizes (in
  response to reviewer feedback) and the prover peak memory ratio.
- **Hyrax**: the submitted paper claimed a prover speedup of up to 6.05x
  at one thread; this was corrected to 1.11x during review, as already
  discussed with the reviewers.

**Runtime**: about 2.5 hours for all systems and all four thread
counts.

---

### Experiment 2: special soundness (Figure 6, §9.3)

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" \
  zippel-ae bash -c '
    artifact/scripts/run_soundness.sh --timeout 120 &&
    python3 artifact/scripts/process_soundness.py'
```

This analyzes Figure 6's seven special-soundness candidates (the rows
with a mark in its Spec. Sound column) with Singular, a 2-minute
timeout and a 16 GiB memory limit per protocol. Results go to
`artifact/output/soundness_results.json` and the raw log to
`artifact/output/soundness_all.log`. To run a subset, add for example
`--protocols schnorr,okamoto` after `--timeout 120`.

**What to expect.** A table of outcomes, analysis times (ideal
construction, Gröbner basis and check) and failure reasons, then a
summary line:

```
| Protocol | Pass | Time | Status | Reason |
|---|---|---|---|---|
| Schnorr | ✓ | ... | ok |  |
| Multi-Schnorr | ✓ | ... | ok |  |
| Okamoto | ✗ | ... | failed | No valid extractor for witness r: NoExtractor |
...

soundness pass=4 failed=2 timeout=1 unexpected=0
```

Schnorr, Multi-Schnorr, ElGamal and Chaum-Pedersen pass, matching
Figure 6's check marks. Okamoto and CDS fail with a reason, and E-Cash
Coin reaches the timeout (it may report `failed` instead, depending on
`--timeout`). The run reproduces the paper if it reports
`unexpected=0`. A cross means the analysis could not establish special
soundness, not that the protocol is unsound.

**Runtime**: about 3 minutes, mostly the E-Cash Coin timeout.

---

### Experiment 3: completeness (Figure 6, §9.3)

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" \
  zippel-ae bash -c '
    artifact/scripts/run_completeness.sh --timeout 300 &&
    python3 artifact/scripts/process_completeness.py'
```

This analyzes all 34 Figure 6 protocols with a 5-minute timeout and a
16 GiB memory limit per run. To run a subset, add for example
`--protocols schnorr,groth16,ipa` after `--timeout 300`.

**Note on the timeout.** §9.3 budgets 20 minutes per protocol. Every
protocol that completes takes far less (the slowest, Multiset, takes
133 seconds on the paper's testbed), so a 5-minute timeout keeps the
full run short.

**What to expect.** A table of outcomes and analysis times in Figure 6
order, then a summary:

```
| Protocol | Pass | Time |
|---|---|---|
| Sumcheck | ✓ | ... |
| Schnorr | ✓ | ... |
...

Automatically verified complete: 28 of 34 Figure 6 protocols present in this run.
Unexpected outcomes: 0
```

The analysis verifies the 28 protocols Figure 6 marks with a check.
The other six are Figure 6's crosses: Spartan, Dory IPA, Permutation,
Dekart and Pari reach the timeout, and HyperPlonk exceeds the memory
limit. The run reproduces the paper if it reports
`Unexpected outcomes: 0`.

**Difference from the submitted paper.** The submitted paper verified
20 of its 30 protocols. Since submission we fixed `where` clauses that
were incomplete and had kept the analysis from proving those protocols
complete.

**Runtime**: about 30 minutes, mostly the five protocols that reach the
timeout.

---

## Paper-to-code index

[`artifact/index.html`](index.html) maps each central claim in the
paper to the source declaration that backs it, and lists every known
difference from the submitted paper (completeness count, LoC drift, the
Hyrax speedup correction) in one place.

## Writing your own protocol

This artifact only reproduces the paper's evaluation. To create your
own protocol and try Zippel, see
[`docs/library-usage.md`](../docs/library-usage.md); it also links to
[`CONTRIBUTING.md`](../CONTRIBUTING.md#creating-a-new-protocol-with-zippel)
for adding a protocol to this repository's own `examples/`.
