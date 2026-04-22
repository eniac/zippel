# Sumcheck compare benchmark (manual-sync grid)

For each cell, `examples/sumcheck/sumcheck.zippel` and `sumcheck_compare` defaults were set to the same `NUM_VARS` / `MAX_DEGREE`, then `cargo run --release -- both` was run. Files were restored to 10/10 after the sweep.

**Δ%** = `(Zippel prover − HyperPlonk prover) / HyperPlonk prover × 100%`. Positive means Zippel is slower; negative means Zippel is faster.

**Speedup** matches `sumcheck_compare` timing output: the faster backend is named first, with `slower / faster` as the multiplicative gap (same as `print_prover_timing_comparison`).

## Prover times by degree and num_vars

Rows are sorted by **degree**, then **num_vars**. The **is x faster** column matches the Speedup phrasing from the run output (same as `print_prover_timing_comparison`).

| degree | num_vars | zippel | hyperplonk | is x faster |
|--------|----------|--------|------------|-------------|
| 1 | 5 | 847.625µs | 549.084µs | HyperPlonk is faster by 1.54× over Zippel |
| 1 | 10 | 1.660ms | 832.750µs | HyperPlonk is faster by 1.99× over Zippel |
| 1 | 15 | 8.623ms | 2.413ms | HyperPlonk is faster by 3.57× over Zippel |
| 1 | 20 | 203.449ms | 42.348ms | HyperPlonk is faster by 4.80× over Zippel |
| 5 | 5 | 1.691ms | 709.084µs | HyperPlonk is faster by 2.38× over Zippel |
| 5 | 10 | 1.506ms | 970.417µs | HyperPlonk is faster by 1.55× over Zippel |
| 5 | 15 | 14.662ms | 7.016ms | HyperPlonk is faster by 2.09× over Zippel |
| 5 | 20 | 443.088ms | 187.789ms | HyperPlonk is faster by 2.36× over Zippel |
| 10 | 5 | 1.501ms | 922.333µs | HyperPlonk is faster by 1.63× over Zippel |
| 10 | 10 | 2.548ms | 1.739ms | HyperPlonk is faster by 1.47× over Zippel |
| 10 | 15 | 28.732ms | 28.700ms | HyperPlonk is faster by 1.00× over Zippel |
| 10 | 20 | 909.042ms | 559.441ms | HyperPlonk is faster by 1.62× over Zippel |
| 15 | 5 | 2.043ms | 1.103ms | HyperPlonk is faster by 1.85× over Zippel |
| 15 | 10 | 2.888ms | 2.267ms | HyperPlonk is faster by 1.27× over Zippel |
| 15 | 15 | 49.836ms | 38.889ms | HyperPlonk is faster by 1.28× over Zippel |
| 15 | 20 | 1.568s | 1.159s | HyperPlonk is faster by 1.35× over Zippel |
| 20 | 5 | 1.615ms | 1.726ms | Zippel is faster by 1.07× over HyperPlonk |
| 20 | 10 | 4.360ms | 3.645ms | HyperPlonk is faster by 1.20× over Zippel |
| 20 | 15 | 85.954ms | 70.001ms | HyperPlonk is faster by 1.23× over Zippel |
| 20 | 20 | 2.588s | 2.007s | HyperPlonk is faster by 1.29× over Zippel |

### Full run matrix (num_vars × degree)

| num_vars | degree | ok | Zippel prover | HyperPlonk prover | Δ% (Z vs HP) | Speedup | wall_s |
|----------|--------|----|---------------|-------------------|--------------|---------|--------|
| 5 | 1 | True | 847.625µs | 549.084µs | +54.37% | HyperPlonk is faster by 1.54× over Zippel | 17.51 |
| 5 | 5 | True | 1.691ms | 709.084µs | +138.48% | HyperPlonk is faster by 2.38× over Zippel | 16.11 |
| 5 | 10 | True | 1.501ms | 922.333µs | +62.74% | HyperPlonk is faster by 1.63× over Zippel | 15.64 |
| 5 | 15 | True | 2.043ms | 1.103ms | +85.22% | HyperPlonk is faster by 1.85× over Zippel | 16.05 |
| 5 | 20 | True | 1.615ms | 1.726ms | -6.43% | Zippel is faster by 1.07× over HyperPlonk | 15.6 |
| 10 | 1 | True | 1.660ms | 832.750µs | +99.34% | HyperPlonk is faster by 1.99× over Zippel | 15.36 |
| 10 | 5 | True | 1.506ms | 970.417µs | +55.19% | HyperPlonk is faster by 1.55× over Zippel | 15.06 |
| 10 | 10 | True | 2.548ms | 1.739ms | +46.52% | HyperPlonk is faster by 1.47× over Zippel | 14.86 |
| 10 | 15 | True | 2.888ms | 2.267ms | +27.39% | HyperPlonk is faster by 1.27× over Zippel | 15.11 |
| 10 | 20 | True | 4.360ms | 3.645ms | +19.62% | HyperPlonk is faster by 1.20× over Zippel | 15.44 |
| 15 | 1 | True | 8.623ms | 2.413ms | +257.36% | HyperPlonk is faster by 3.57× over Zippel | 15.15 |
| 15 | 5 | True | 14.662ms | 7.016ms | +108.98% | HyperPlonk is faster by 2.09× over Zippel | 15.4 |
| 15 | 10 | True | 28.732ms | 28.700ms | +0.11% | HyperPlonk is faster by 1.00× over Zippel | 15.18 |
| 15 | 15 | True | 49.836ms | 38.889ms | +28.15% | HyperPlonk is faster by 1.28× over Zippel | 15.28 |
| 15 | 20 | True | 85.954ms | 70.001ms | +22.79% | HyperPlonk is faster by 1.23× over Zippel | 15.39 |
| 20 | 1 | True | 203.449ms | 42.348ms | +380.42% | HyperPlonk is faster by 4.80× over Zippel | 16.11 |
| 20 | 5 | True | 443.088ms | 187.789ms | +135.95% | HyperPlonk is faster by 2.36× over Zippel | 16.69 |
| 20 | 10 | True | 909.042ms | 559.441ms | +62.49% | HyperPlonk is faster by 1.62× over Zippel | 18.22 |
| 20 | 15 | True | 1.568s | 1.159s | +35.29% | HyperPlonk is faster by 1.35× over Zippel | 21.41 |
| 20 | 20 | True | 2.588s | 2.007s | +28.95% | HyperPlonk is faster by 1.29× over Zippel | 25.01 |

<details><summary>JSON</summary>

```json
[
  {
    "num_vars": 5,
    "degree": 1,
    "ok": true,
    "rc": 0,
    "zippel": "847.625\u00b5s",
    "hyperplonk": "549.084\u00b5s",
    "wall_s": 17.51,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 16.95s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 54.37,
    "speedup_phrase": "HyperPlonk is faster by 1.54\u00d7 over Zippel"
  },
  {
    "num_vars": 5,
    "degree": 5,
    "ok": true,
    "rc": 0,
    "zippel": "1.691ms",
    "hyperplonk": "709.084\u00b5s",
    "wall_s": 16.11,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 15.70s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 138.48,
    "speedup_phrase": "HyperPlonk is faster by 2.38\u00d7 over Zippel"
  },
  {
    "num_vars": 5,
    "degree": 10,
    "ok": true,
    "rc": 0,
    "zippel": "1.501ms",
    "hyperplonk": "922.333\u00b5s",
    "wall_s": 15.64,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 15.24s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 62.74,
    "speedup_phrase": "HyperPlonk is faster by 1.63\u00d7 over Zippel"
  },
  {
    "num_vars": 5,
    "degree": 15,
    "ok": true,
    "rc": 0,
    "zippel": "2.043ms",
    "hyperplonk": "1.103ms",
    "wall_s": 16.05,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 15.66s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 85.22,
    "speedup_phrase": "HyperPlonk is faster by 1.85\u00d7 over Zippel"
  },
  {
    "num_vars": 5,
    "degree": 20,
    "ok": true,
    "rc": 0,
    "zippel": "1.615ms",
    "hyperplonk": "1.726ms",
    "wall_s": 15.6,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 15.22s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": -6.43,
    "speedup_phrase": "Zippel is faster by 1.07\u00d7 over HyperPlonk"
  },
  {
    "num_vars": 10,
    "degree": 1,
    "ok": true,
    "rc": 0,
    "zippel": "1.660ms",
    "hyperplonk": "832.750\u00b5s",
    "wall_s": 15.36,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.90s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 99.34,
    "speedup_phrase": "HyperPlonk is faster by 1.99\u00d7 over Zippel"
  },
  {
    "num_vars": 10,
    "degree": 5,
    "ok": true,
    "rc": 0,
    "zippel": "1.506ms",
    "hyperplonk": "970.417\u00b5s",
    "wall_s": 15.06,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.61s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 55.19,
    "speedup_phrase": "HyperPlonk is faster by 1.55\u00d7 over Zippel"
  },
  {
    "num_vars": 10,
    "degree": 10,
    "ok": true,
    "rc": 0,
    "zippel": "2.548ms",
    "hyperplonk": "1.739ms",
    "wall_s": 14.86,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.41s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 46.52,
    "speedup_phrase": "HyperPlonk is faster by 1.47\u00d7 over Zippel"
  },
  {
    "num_vars": 10,
    "degree": 15,
    "ok": true,
    "rc": 0,
    "zippel": "2.888ms",
    "hyperplonk": "2.267ms",
    "wall_s": 15.11,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.64s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 27.39,
    "speedup_phrase": "HyperPlonk is faster by 1.27\u00d7 over Zippel"
  },
  {
    "num_vars": 10,
    "degree": 20,
    "ok": true,
    "rc": 0,
    "zippel": "4.360ms",
    "hyperplonk": "3.645ms",
    "wall_s": 15.44,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.96s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 19.62,
    "speedup_phrase": "HyperPlonk is faster by 1.20\u00d7 over Zippel"
  },
  {
    "num_vars": 15,
    "degree": 1,
    "ok": true,
    "rc": 0,
    "zippel": "8.623ms",
    "hyperplonk": "2.413ms",
    "wall_s": 15.15,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.51s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 257.36,
    "speedup_phrase": "HyperPlonk is faster by 3.57\u00d7 over Zippel"
  },
  {
    "num_vars": 15,
    "degree": 5,
    "ok": true,
    "rc": 0,
    "zippel": "14.662ms",
    "hyperplonk": "7.016ms",
    "wall_s": 15.4,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.74s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 108.98,
    "speedup_phrase": "HyperPlonk is faster by 2.09\u00d7 over Zippel"
  },
  {
    "num_vars": 15,
    "degree": 10,
    "ok": true,
    "rc": 0,
    "zippel": "28.732ms",
    "hyperplonk": "28.700ms",
    "wall_s": 15.18,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.46s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 0.11,
    "speedup_phrase": "HyperPlonk is faster by 1.00\u00d7 over Zippel"
  },
  {
    "num_vars": 15,
    "degree": 15,
    "ok": true,
    "rc": 0,
    "zippel": "49.836ms",
    "hyperplonk": "38.889ms",
    "wall_s": 15.28,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.49s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 28.15,
    "speedup_phrase": "HyperPlonk is faster by 1.28\u00d7 over Zippel"
  },
  {
    "num_vars": 15,
    "degree": 20,
    "ok": true,
    "rc": 0,
    "zippel": "85.954ms",
    "hyperplonk": "70.001ms",
    "wall_s": 15.39,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.40s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 22.79,
    "speedup_phrase": "HyperPlonk is faster by 1.23\u00d7 over Zippel"
  },
  {
    "num_vars": 20,
    "degree": 1,
    "ok": true,
    "rc": 0,
    "zippel": "203.449ms",
    "hyperplonk": "42.348ms",
    "wall_s": 16.11,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.65s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 380.42,
    "speedup_phrase": "HyperPlonk is faster by 4.80\u00d7 over Zippel"
  },
  {
    "num_vars": 20,
    "degree": 5,
    "ok": true,
    "rc": 0,
    "zippel": "443.088ms",
    "hyperplonk": "187.789ms",
    "wall_s": 16.69,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.31s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 135.95,
    "speedup_phrase": "HyperPlonk is faster by 2.36\u00d7 over Zippel"
  },
  {
    "num_vars": 20,
    "degree": 10,
    "ok": true,
    "rc": 0,
    "zippel": "909.042ms",
    "hyperplonk": "559.441ms",
    "wall_s": 18.22,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.10s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 62.49,
    "speedup_phrase": "HyperPlonk is faster by 1.62\u00d7 over Zippel"
  },
  {
    "num_vars": 20,
    "degree": 15,
    "ok": true,
    "rc": 0,
    "zippel": "1.568s",
    "hyperplonk": "1.159s",
    "wall_s": 21.41,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.69s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 35.29,
    "speedup_phrase": "HyperPlonk is faster by 1.35\u00d7 over Zippel"
  },
  {
    "num_vars": 20,
    "degree": 20,
    "ok": true,
    "rc": 0,
    "zippel": "2.588s",
    "hyperplonk": "2.007s",
    "wall_s": 25.01,
    "err_tail": "\nwarning: `runtime` (lib) generated 2 warnings\n   Compiling sumcheck_compare v0.1.0 (/Users/sydniesheacohen/SydnieShea/zippel/sumcheck_compare)\n    Finished `release` profile [optimized] target(s) in 14.59s\n     Running `/var/folders/s2/gww3vxzn69vcvd4w53cr5w7h0000gn/T/cursor-sandbox-cache/37e2d75c1f44b6cb72906d228f8c9a5d/cargo-target/release/sumcheck_compare both`",
    "delta_pct_z_over_hp": 28.95,
    "speedup_phrase": "HyperPlonk is faster by 1.29\u00d7 over Zippel"
  }
]
```
</details>
