# Historical experiment results

These files were moved intact from `experiments/results/` during the experiments
source cleanup. Filenames and contents are preserved, including original source
paths recorded inside generated tables. Those paths describe their location
when measured, not the current file location.

- `bench_results_1014.csv`: the ten-sample benchmark data used by the paper's
  printed Spartan ratios; retain as the paper-era reference.
- `*_results.csv`, `aws_bench_2p18.csv`, and older CSV formats: previous native
  comparison runs. Their formats and timing boundaries vary; identify the
  originating run before comparing values.
- `analysis_1015/`, `analysis_1016/`: dated completeness/soundness sweeps, raw
  logs/JSON and rendered tables. Each directory's README records its method.

New benchmark output paths remain user-selected through `bench_all --out` or
`run_all.sh`'s `OUT`; this directory is the archive of recorded results.
