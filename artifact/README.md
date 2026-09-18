# Zippel: IEEE S&P 2027 Artifact

Zippel is a language, compiler, and runtime for cryptographic proof
systems, with Gröbner-basis-based static analyses that check completeness
and special soundness directly from a protocol's source. This artifact
builds the system in Docker and runs the three experiments described in
the paper's evaluation section.

**Note on scope.** This artifact reproduces the submitted paper's Figures
6 and 7 (pages 12-13) and the completeness and special-soundness claims
of Section 9.3. It additionally produces two supplementary tables not
included in the submitted paper (a per-protocol Graph IR node-count
table and a 30-protocol inline/no-inline completeness breakdown), added
in response to reviewer feedback. The submitted paper therefore has no
corresponding table for these two. Each experiment below identifies
which figure, if any, it corresponds to.

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
| `benches/inline/` | Inline vs. no-inline completeness sweep (Experiment 3) |
| `benchmarks/` | Zippel vs. native performance comparison (Experiment 1) |
| `analyses/tests/gb_snapshots/` | Special-soundness regression suite (Experiment 2) |
| `artifact/` | This package: `Dockerfile` and `scripts/` |

## Setup

Build the image from the repository root, not from `artifact/`. The
image builds and runs as a non-root user matching your own UID/GID, so
`--build-arg` is required:

```sh
docker build -f artifact/Dockerfile -t zippel-ae \
  --build-arg UID=$(id -u) --build-arg GID=$(id -g) .
```

This installs the nightly Rust toolchain pinned by `rust-toolchain.toml`,
the build dependencies `gcc`, `m4`, and `pkg-config`, and Singular via
apt, and prebuilds the workspace in release mode. The build takes
approximately 10 minutes, produces a roughly 6GB image, and requires
network access to pull the base image and fetch crates.

To verify the environment:

```sh
docker run --rm zippel-ae bash artifact/scripts/smoke_test.sh
```

This builds and runs three example protocols, one completeness trial
through Singular, and one `inline`-bench check. It is not one of the
three experiments; it only verifies that the toolchain and Singular
integration function correctly. It completes in well under a minute and
ends with:

```
Smoke test passed.
```

## Line counts for all 30 protocols (Figure 6)

This command reproduces the submitted paper's Figure 6 line-count table
by counting non-comment source lines directly from each of the 30
protocols' `.zippel` files:

```sh
docker run --rm zippel-ae python3 artifact/scripts/report_loc.py
```

**What to expect:**

These figures will not match the submitted paper's Figure 6 for most
protocols. Two changes account for this. First, `zippel-fmt` (see the
repository layout above) did not exist at submission time, so the
example files were not yet written in its canonical style; reformatting
them afterward altered line counts independently of any semantic change.
Second, several protocols' `where`-clause constraints were revised after
submission (see the completeness-count accounting under Experiment 3).

This does not undermine the paper's conciseness claim. The native
baseline side of each comparison is unaffected, since that code is
vendored and neither formatted nor edited by this project; all of the
movement above occurs on the Zippel side. Zippel remains substantially
shorter than its native baseline for every one of the nine systems that
Experiment 1 benchmarks:

| System | LoC Zippel (submitted to now) | LoC Native | Native/Zippel (submitted to now) |
|---|---|---|---|
| Schnorr | 7 to 7 | 186 | 26.6x to 26.6x |
| Sumcheck | 58 to 90 | 1544 | 26.6x to 17.2x |
| Bulletproofs | 79 to 77 | 166 | 2.1x to 2.1x |
| KZG | 14 to 24 | 527 | 37.6x to 22.0x |
| Pari | 79 to 101 | 1141 | 14.4x to 11.3x |
| Groth16 | 36 to 88 | 458 | 12.7x to 5.2x |
| PST13 | 54 to 82 | 250 | 4.6x to 3.0x |
| Hyrax | 47 to 49 | 277 | 5.9x to 5.7x |
| Spartan | 461 to 419 | 1867 | 4.0x to 4.5x |

Groth16 changed the most, yet remains 5.2x shorter than its native
baseline. Every other system changed less, and Spartan's line count
decreased.

## Experiments

| # | Script | Produces | Paper reference |
|---|---|---|---|
| 1 | `run_benchmark.sh` + `process_benchmark.py` | Zippel-vs-native speedup table; Graph IR node-count table | Figure 7 (p.13); the node-count table is supplementary |
| 2 | `run_correctness.sh` | Pass/fail/ignored counts for special soundness | §9.3 prose |
| 3 | `run_inline.sh` + `process_inline.py` | 30-protocol inline/no-inline completeness table | §9.3 prose; the table itself is supplementary |

---

### Experiment 1: performance benchmark and graph sizes (Figure 7)

This experiment reproduces the submitted paper's Figure 7 performance
comparison (and adds a supplementary graph-size table).

```sh
mkdir -p artifact/output
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" zippel-ae \
  bash -c "artifact/scripts/run_benchmark.sh && python3 artifact/scripts/process_benchmark.py"
```

Runs all nine systems benchmarked in the paper (Schnorr, Sumcheck,
Bulletproofs IPA, KZG, Pari, Groth16, PST13, Hyrax, Spartan) at each
system's paper-reported instance size (`2^18`, fixed for Schnorr) across
thread counts `{1, 2, 4, 8}`, then renders two markdown tables from the
resulting CSV. To run a smaller subset instead of the full sweep:

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" -e SYSTEMS=schnorr,kzg -e THREADS=1,2 zippel-ae \
  bash -c "artifact/scripts/run_benchmark.sh && python3 artifact/scripts/process_benchmark.py"
```

**What to expect:**

- **Performance table** (Figure 7, page 13): non-comment line counts for
  the Zippel protocol and its native baseline, the ratio of native
  baseline time to Zippel time at each thread count, and the
  single-thread verifier ratio. Hyrax's prover speedup differs sharply
  between one and two threads; this is expected and has already been
  discussed with the paper's reviewers.
  <!-- TODO: revisit this paragraph once a full 9-system x 4-thread run
  is available. -->
- **Graph-size table** (prover and verifier Graph IR node counts): not
  included in the submitted paper; added in response to reviewer
  feedback.

---

### Experiment 2: special-soundness correctness suite (§9.3)

This experiment reproduces the submitted paper's special-soundness claim
in Section 9.3.

```sh
docker run --rm zippel-ae bash artifact/scripts/run_correctness.sh
```

Runs the `soundness::*` trials in `analyses/tests/gb_snapshots` (the
same test binary also contains `completeness::*` and `knowledge::*`
trials unrelated to this claim), which assert that the special-soundness
analysis succeeds. It prints a summary and produces no other output.
The run completes in a few seconds.

**What to expect:**

```
running 9 tests
...
test result: ok. 4 passed; 0 failed; 5 ignored; ...

== Summary ==
soundness pass=4   ignored=5   failed=0
```

This suite covers all 6 of the paper's special-sound candidates
(Schnorr, Multi-Schnorr, Chaum-Pedersen, Okamoto, CDS,
E-Cash Coin) plus 3 protocols not discussed in the paper
(`okamoto_elgamal`, `commitment_equality`, `pedersen_eq`). 4 pass
(Schnorr, Multi-Schnorr, Chaum-Pedersen, `okamoto_elgamal`) and 5 are
marked ignored (Okamoto, CDS, E-Cash Coin,
`commitment_equality`, `pedersen_eq`).

A pass requires `0 failed`; the `ignored` count is expected. Among the
paper's 6 candidates, Okamoto, CDS, and E-Cash Coin fail for the
reasons given in its Section 9.3, matching its result exactly.

---

### Experiment 3: inline vs. no-inline completeness sweep (§9.3)

This experiment reproduces the submitted paper's completeness claim in
Section 9.3 (and adds a supplementary inline/no-inline breakdown).

```sh
mkdir -p artifact/output
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" zippel-ae \
  bash -c "artifact/scripts/run_inline.sh && python3 artifact/scripts/process_inline.py"
```

Runs all 30 protocols from the paper, both with and without the
inlining pass, through the completeness analysis, with a 20-minute
timeout and a 16 GiB memory limit per run.

To sanity-check a small subset of protocols instead of running all
60 configurations:

```sh
docker run --rm -v "$(pwd)/artifact/output:/zippel/artifact/output" zippel-ae \
  bash -c "artifact/scripts/run_inline.sh --timeout 90 --protocols schnorr,groth16,ipa,hyperplonk && python3 artifact/scripts/process_inline.py"
```

**What to expect, and why it differs from the paper.** The submitted
paper states in Section 9.3: "All 30 protocols are perfectly complete...
Zippel can automatically verify 20 of them (66.7%)." Since submission,
real bugs were found and fixed in the protocol encodings, and the
corrected count is **18 of 30**, not 20:

- **Minus 5** (previously reported complete but were not): the entire
  HyperPlonk family and Dekart were false positives caused by a bug that
  has since been fixed.
- **Plus 3** (previously reported incomplete but were complete):
  Groth16, KZH, and Bulletproofs (`ipa`) each had a `where` clause
  missing required constraints. This has been fixed.
- Net: 20 minus 5 plus 3 equals **18**. The "20" will be corrected in the
  next revision of the paper.

A full run of this experiment will therefore not match the submitted
paper's "20 of 30"; it should match 18.

The following is a sample row from a validation run:

```
| Protocol | Nodes | P/V/D Inline | P/V/D No-inline | Time Inline | Time No-inline |
| groth16  | 150   | 50/70/5      | 210/230/2       | 15.4s       | timeout        |
```

`P/V/D` is the ideal's generating set, measured before Gröbner basis
computation: Polynomial count / Variable count / max Degree. Inlining
trades this off in one direction (fewer polynomials, more variables per
polynomial, higher degree) versus not inlining (more, smaller,
lower-degree polynomials). When the analysis confirms completeness,
the Time Inline/Time No-inline column reports elapsed time, as `15.4s`
does above; otherwise, that column reports why no time is available:
`timeout` means the 20-minute limit was exceeded; `oom` means the
memory limit was reached; `crashed` and `incomplete` mean, respectively,
a caught panic and a completeness check that ran to completion but
failed.

**Runtime**: a full 30x2 sweep takes approximately 5.3 hours.

## Note on recompiles

The Docker image prebuilds the entire workspace. However, each of
`run_correctness.sh`, `run_benchmark.sh`, and `run_inline.sh`
will trigger a partial recompilation the first time that command is run.
Depending on the command, this may take roughly tens of seconds.
This is expected behavior.

Because containers created with `docker run --rm` are ephemeral, this
recompilation cost is incurred on every separate invocation. If these
scripts need to be run repeatedly for evaluation, the cost can be
avoided by additionally mounting a persistent volume at
`/zippel/target`:

```sh
docker volume create zippel-ae-target
docker run --rm \
  -v zippel-ae-target:/zippel/target \
  -v "$(pwd)/artifact/output:/zippel/artifact/output" \
  zippel-ae bash -c "..."
```

Subsequent runs against the same volume reuse whatever was compiled previously.