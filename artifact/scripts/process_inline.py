#!/usr/bin/env python3
"""Render run_inline.sh's JSON output into a markdown table (supplementary,
not present in the submitted paper, which only has prose in Section 9.3).
See ../README.md for the completeness-count accounting this table's `ok`
column substantiates.

Columns:
    Protocol | Nodes | P/V/D Inline | P/V/D No-inline | Time Inline | Time No-inline

P/V/D is generating-set polynomial count / variable count / max degree,
measured before Groebner basis computation (`gen_set_size` /
`gen_set_num_vars` / `gen_set_max_degree` in the JSON). Time is total_ms
(build+gb+run) formatted as ms/s when status is "ok", else the status
string itself (timeout/crashed/failed/incomplete/oom).

Usage:
    artifact/scripts/process_inline.py [JSON_PATH]

JSON_PATH defaults to artifact/output/inline_results.json.
"""

import json
import sys

DEFAULT_JSON = "artifact/output/inline_results.json"


def total_ms(r):
    parts = [r.get("build_ms"), r.get("gb_ms"), r.get("run_ms")]
    if any(p is None for p in parts):
        return None
    return sum(parts)


def fmt_time(r):
    if r.get("status") != "ok":
        return r.get("status", "?")
    ms = total_ms(r)
    if ms is None:
        return "?"
    return f"{ms:.1f}ms" if ms < 1000 else f"{ms / 1000:.1f}s"


def fmt_pvd(r):
    if r.get("status") == "failed" and r.get("gen_set_size") is None:
        return "--"
    p = r.get("gen_set_size")
    v = r.get("gen_set_num_vars")
    d = r.get("gen_set_max_degree")
    if p is None or v is None or d is None:
        return "--"
    return f"{p}/{v}/{d}"


def main():
    json_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_JSON
    with open(json_path) as f:
        data = json.load(f)

    results = data["results"]
    by_protocol = {}
    for r in results:
        entry = by_protocol.setdefault(r["protocol"], {})
        entry[r["inline"]] = r

    print(f"Source: {json_path} ({len(results)} rows, timeout={data.get('timeout_s')}s, "
          f"memory_limit_mb={data.get('memory_limit_mb')})")
    print()
    print("| Protocol | Nodes | P/V/D Inline | P/V/D No-inline | Time Inline | Time No-inline |")
    print("|---|---|---|---|---|---|")
    for protocol, variants in by_protocol.items():
        inline = variants.get(1, {})
        no_inline = variants.get(0, {})
        nodes = inline.get("graph_size", no_inline.get("graph_size", "?"))
        print(
            f"| {protocol} | {nodes} | {fmt_pvd(inline)} | {fmt_pvd(no_inline)} "
            f"| {fmt_time(inline)} | {fmt_time(no_inline)} |"
        )

    ok_count = sum(1 for r in results if r.get("status") == "ok" and r.get("inline") == 1)
    total_protocols = len(by_protocol)
    print()
    print(f"Automatically verified complete (inline): {ok_count} of {total_protocols} protocols present in this run.")


if __name__ == "__main__":
    main()
