#!/usr/bin/env python3
"""Render run_benchmark.sh's CSV into markdown tables:

1. Figure 7 (comparison with existing implementations): per row, LoC of
   Zippel and the baseline, Graph IR node counts (prover, verifier),
   prover speedup (baseline/zippel) at each thread count present in the
   CSV, verifier speedup at threads=1, and prover peak memory ratio
   (baseline/zippel prover peak heap at threads=1, where the peak is
   deterministic; see benchmarks/README.md). Rows and labels are the
   paper's, from paper.py; a row missing from the CSV is left out.

2. Zippel compile time per system, then its minimum, maximum and
   median (reported in the text of the paper's §9.1, Compilation
   Performance, not in a figure).

Each system is reported at its largest instance size in the CSV (2^18
for every system but Schnorr in a default run).

Usage:
    artifact/scripts/process_benchmark.py [CSV_PATH]

CSV_PATH defaults to artifact/output/bench_results.csv. The CSV holds one
row per sample; the tables use each measurement's mean over its samples.
"""

import csv
import statistics
import sys

from paper import FIGURE_7

DEFAULT_CSV = "artifact/output/bench_results.csv"


def load_rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def mean_over_samples(rows):
    """One row per (system, baseline, threads, log_size): the mean of every
    *_ms and *_mib column over that point's samples."""
    groups = {}
    for r in rows:
        key = (r["system"], r["baseline"], r["threads"], r["log_size"])
        groups.setdefault(key, []).append(r)
    out = []
    for group in groups.values():
        row = dict(group[0])
        for col in row:
            if col.endswith("_ms") or col.endswith("_mib"):
                row[col] = str(sum(float(g[col]) for g in group) / len(group))
        row.pop("sample", None)
        out.append(row)
    return out


def instance_size_label(log_size):
    log_size = int(log_size)
    return "fixed" if log_size == 0 else f"2^{log_size}"


def fmt_ms(ms):
    return f"{ms:.1f}ms" if ms < 1000 else f"{ms / 1000:.1f}s"


def ratio(baseline, zippel):
    baseline, zippel = float(baseline), float(zippel)
    if zippel <= 0:
        return "N/A"
    r = baseline / zippel
    # The CSV rounds to 0.001; a tiny baseline peak (Schnorr) can be 0.
    return "<0.01x" if r < 0.01 else f"{r:.2f}x"


def largest_size(rows):
    """(system, baseline) -> {threads: row}, keeping each system's largest
    log_size."""
    top = {}
    for r in rows:
        top[r["system"]] = max(top.get(r["system"], 0), int(r["log_size"]))
    out = {}
    for r in rows:
        if int(r["log_size"]) == top[r["system"]]:
            out.setdefault((r["system"], r["baseline"]), {})[int(r["threads"])] = r
    return out


def render_performance_table(points, all_threads):
    header = (
        "| Proof System | LoC Zippel | LoC Baseline | Prover (nodes) | Verifier (nodes) | "
        + " | ".join(f"P Speedup ({t})" for t in all_threads)
        + " | V Speedup | Prover Peak Memory Ratio |"
    )
    lines = [header, "|---" * (7 + len(all_threads)) + "|"]
    for label, system, baseline in FIGURE_7:
        by_thread = points.get((system, baseline))
        if by_thread is None:
            continue
        any_row = next(iter(by_thread.values()))
        cells = [label, any_row["zippel_ncloc"], any_row["baseline_ncloc"],
                 any_row["prover_nodes"], any_row["verifier_nodes"]]
        for t in all_threads:
            r = by_thread.get(t)
            cells.append("N/A" if r is None else ratio(r["baseline_prover_ms"], r["zippel_prover_ms"]))
        # Verifier and peak memory at threads=1, per the paper's methodology.
        r1 = by_thread.get(1)
        if r1 is None:
            cells += ["N/A", "N/A"]
        else:
            cells.append(ratio(r1["baseline_verifier_ms"], r1["zippel_verifier_ms"]))
            cells.append(ratio(r1["baseline_prover_peak_mib"], r1["zippel_prover_peak_mib"]))
        lines.append("| " + " | ".join(str(c) for c in cells) + " |")
    return "\n".join(lines)


def render_compile_table(points):
    """Compile time does not depend on threads or baseline, so this takes
    each system's mean over all its rows at that size."""
    lines = ["| Proof System | Instance size | Compile time |", "|---|---|---|"]
    times = []
    seen = set()
    for label, system, baseline in FIGURE_7:
        if system in seen:
            continue
        rows = [r for (s, _), by_thread in points.items() if s == system
                for r in by_thread.values()]
        if not rows:
            continue
        seen.add(system)
        ms = statistics.mean(float(r["compile_ms"]) for r in rows)
        label = label.split(" (")[0]
        times.append((ms, label))
        lines.append(f"| {label} | {instance_size_label(rows[0]['log_size'])} | {fmt_ms(ms)} |")
    if times:
        times.sort()
        median = statistics.median(ms for ms, _ in times)
        lines.append("")
        lines.append(f"Compile time: min {fmt_ms(times[0][0])} ({times[0][1]}), "
                     f"max {fmt_ms(times[-1][0])} ({times[-1][1]}), median {fmt_ms(median)}.")
    return "\n".join(lines)


def main():
    csv_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_CSV
    samples = load_rows(csv_path)
    if not samples:
        sys.exit(f"no rows in {csv_path}")
    rows = mean_over_samples(samples)
    points = largest_size(rows)
    all_threads = sorted({int(r["threads"]) for r in rows})

    print(f"Source: {csv_path} ({len(samples)} samples, {len(rows)} points)")
    print()
    print("## Performance table (Figure 7)")
    print()
    print(render_performance_table(points, all_threads))
    print()
    print("## Compile time (§9.1)")
    print()
    print(render_compile_table(points))


if __name__ == "__main__":
    main()
