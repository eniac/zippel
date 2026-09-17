#!/usr/bin/env python3
"""Render run_benchmark.sh's CSV into two markdown tables:

1. Graph-size table (supplementary, not present in the submitted paper):
   per-system Graph IR node counts (prover graph, verifier graph).
   Thread-independent, one row per system, taken from whichever row
   happens to be first for that system.

2. Performance table (the submitted paper's Figure 7, page 13):
   per-system LoC, prover speedup (native/zippel) at each thread count
   present in the CSV, and verifier speedup at threads=1 (matches the
   paper's methodology: "we evaluate the prover with 1-8 threads and the
   verifier with 1 thread").

See ../README.md for more on why the first table has no paper figure to
check it against.

Usage:
    artifact/scripts/process_benchmark.py [CSV_PATH]

CSV_PATH defaults to artifact/output/bench_results.csv.
"""

import csv
import sys
from collections import defaultdict

DEFAULT_CSV = "artifact/output/bench_results.csv"


def load_rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def instance_size_label(log_size):
    log_size = int(log_size)
    return "fixed" if log_size == 0 else f"2^{log_size}"


def render_graph_size_table(rows):
    seen = {}
    for r in rows:
        seen.setdefault(r["system"], r)

    lines = [
        "| Proof System | Instance size | Prover (nodes) | Verifier (nodes) |",
        "|---|---|---|---|",
    ]
    for system, r in seen.items():
        lines.append(
            f"| {system} | {instance_size_label(r['log_size'])} "
            f"| {r['prover_nodes']} | {r['verifier_nodes']} |"
        )
    return "\n".join(lines)


def render_performance_table(rows):
    by_system = defaultdict(dict)
    for r in rows:
        by_system[r["system"]][int(r["threads"])] = r

    all_threads = sorted({int(r["threads"]) for r in rows})

    header = (
        "| Proof System | LoC Zippel | LoC Base | "
        + " | ".join(f"P Speedup ({t})" for t in all_threads)
        + " | V Speedup |"
    )
    sep = "|---|---|---|" + "---|" * len(all_threads) + "---|"
    lines = [header, sep]

    for system, by_thread in by_system.items():
        any_row = next(iter(by_thread.values()))
        cells = [system, any_row["zippel_ncloc"], any_row["native_ncloc"]]
        for t in all_threads:
            r = by_thread.get(t)
            if r is None:
                cells.append("N/A")
                continue
            zippel_ms = float(r["prover_time_ms"])
            native_ms = float(r["native_prover_time_ms"])
            cells.append(f"{native_ms / zippel_ms:.2f}x" if zippel_ms > 0 else "N/A")
        # Verifier speedup at threads=1, per the paper's methodology.
        r1 = by_thread.get(1)
        if r1 is not None and float(r1["verifier_time_ms"]) > 0:
            v_speedup = float(r1["native_verifier_time_ms"]) / float(r1["verifier_time_ms"])
            cells.append(f"{v_speedup:.2f}x")
        else:
            cells.append("N/A")
        lines.append("| " + " | ".join(str(c) for c in cells) + " |")

    return "\n".join(lines)


def main():
    csv_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_CSV
    rows = load_rows(csv_path)
    if not rows:
        sys.exit(f"no rows in {csv_path}")

    print(f"Source: {csv_path} ({len(rows)} rows)")
    print()
    print("## Graph-size table (supplementary, not in the submitted paper)")
    print()
    print(render_graph_size_table(rows))
    print()
    print("## Performance table (Figure 7, page 13)")
    print()
    print(render_performance_table(rows))


if __name__ == "__main__":
    main()
