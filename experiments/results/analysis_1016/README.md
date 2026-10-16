# Figure 6 analysis results — 2026-10-16

Measured on an AWS `m4.4xlarge` (16 vCPUs, 64 GB; Ubuntu 26.04) with
Singular 4.4.1 and `nightly-2026-09-13`, one run per protocol, serial
soundness and completeness sweeps, natively (no Docker). Source: commit
`fac811db` plus the uncommitted registration of Hyrax's Dot Product and
Product Proof as soundness candidates. Commands as in
`artifact/README.md`: `run_soundness.sh --timeout 120` and
`run_completeness.sh --timeout 300`, each with the default 16,384 MiB
memory limit.

Timing is `build_ms + gb_ms + run_ms`: polynomial encoding, Gröbner basis
computation, and checking. It excludes Rust compilation and Graph IR
preparation. The raw JSON retains partial metrics and failure reasons. The
Markdown tables are rendered by `artifact/scripts/process_soundness.py` and
`artifact/scripts/process_completeness.py`.

Completeness: 33/35 pass; Spartan and HyperPlonk exceed the memory limit.
Soundness: five pass; Okamoto, CDS, Dot Product and Product Proof fail,
and E-Cash Coin reaches the timeout.
