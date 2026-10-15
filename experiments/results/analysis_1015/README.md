# Figure 6 analysis results — 2026-10-15

Measured with Singular 4.4.1, one run per protocol, serial soundness and
completeness sweeps. Each run had
a 1,200-second timeout and a 16,384 MiB memory limit.

Timing is `build_ms + gb_ms + run_ms`: polynomial encoding, Gröbner basis
computation, and checking. It excludes Rust compilation and Graph IR
preparation. The raw JSON retains partial metrics and failure reasons. The
Markdown tables are rendered by `artifact/scripts/process_soundness.py` and
`artifact/scripts/process_completeness.py`.

Completeness: 33/35 pass; Spartan and HyperPlonk exceed the memory limit.
Soundness: five pass, Okamoto and CDS fail, and E-Cash Coin reaches the timeout.
