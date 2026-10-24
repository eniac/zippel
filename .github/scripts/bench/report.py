"""Validate untrusted measurements and update only their authorized PR report."""

import argparse
from datetime import datetime, timezone
import math
import os
from pathlib import Path
import re
import statistics

from common import CATALOG, GitHub, read_json, validate_config
from run import SAMPLES, phases


def number(value):
    return type(value) in (int, float) and math.isfinite(value) and 0 <= value < 1e15


def validate_results(data, request):
    result = read_json(data)
    identity = {"mode": request["mode"], "examples": request["examples"],
                "base_sha": request["base_sha"], "head_sha": request["head_sha"]}
    if type(result) is not dict or any(result.get(key) != value for key, value in identity.items()):
        raise ValueError("result identity differs from the trusted request")
    if "measurement_seconds" in result and not number(result["measurement_seconds"]):
        raise ValueError("invalid measurement duration")
    if "build_seconds" in result:
        builds = result["build_seconds"]
        if type(builds) is not dict or set(builds) != {"base", "head"} or not all(number(v) for v in builds.values()):
            raise ValueError("invalid build durations")
    rows = result.get("rows")
    if not isinstance(rows, list) or [r.get("example") for r in rows if type(r) is dict] != request["examples"]:
        raise ValueError("result does not contain the exact requested example list")
    expected = set(phases(request["mode"]))
    for row in rows:
        if set(row) != {"example", "base", "head"}:
            raise ValueError("unexpected result row fields")
        for side in ("base", "head"):
            measured = row[side]
            if type(measured) is not dict or set(measured) - {"status", "ms", "instructions", "instruction_status", "workload", "config"}:
                raise ValueError("unexpected measurement fields")
            if measured.get("status") not in ("ok", "failed", "timeout", "budget", "incompatible"):
                raise ValueError("unknown case status")
            if "workload" in measured and not re.fullmatch(r"[a-f0-9]{64}", str(measured["workload"])):
                raise ValueError("invalid workload identity")
            times = measured.get("ms")
            if measured["status"] == "ok":
                if type(times) is not dict or set(times) != expected:
                    raise ValueError("incomplete native timing phases")
                for samples in times.values():
                    if not isinstance(samples, list) or len(samples) != SAMPLES or not all(number(v) for v in samples):
                        raise ValueError("invalid native timing samples")
                if "workload" not in measured:
                    raise ValueError("missing workload identity")
                config = validate_config(measured.get("config"), request["mode"])
                sizes = request.get("sizes")
                if sizes is None:
                    sizes = CATALOG["examples"][row["example"]][request["mode"]]["sizes"] or None
                if sizes is not None and config["sizes"] != sizes:
                    raise ValueError("resolved sizes differ from the requested sizes")
            elif times != {}:
                raise ValueError("failed cases cannot provide successful samples")
            if measured.get("instruction_status") not in ("ok", "timeout", "unavailable"):
                raise ValueError("unknown instruction status")
            counters = measured.get("instructions")
            if measured["instruction_status"] == "ok":
                if measured["status"] != "ok" or type(counters) is not dict or set(counters) != expected:
                    raise ValueError("incomplete instruction phases")
                for count in counters.values():
                    if type(count) is not dict or set(count) != {"parent", "children"}:
                        raise ValueError("incomplete parent/child counts")
                    if not all(isinstance(v, list) and len(v) == SAMPLES
                               and all(type(n) is int and 0 <= n < 2**64 for n in v) for v in count.values()):
                        raise ValueError("invalid instruction units/counts")
            elif counters is not None:
                raise ValueError("incomplete profiles cannot provide counts")
    return result


def change(base, head):
    """Median change; a change inside both sides' sample ranges is noise."""
    low, high = statistics.median(base), statistics.median(head)
    if low <= 0:
        return "—"
    text = f"{100 * (high / low - 1):+.1f}%"
    return text + " (noise)" if max(min(base), min(head)) <= min(max(base), max(head)) else text


def time_cell(samples):
    return f"{statistics.median(samples):.3f} [{min(samples):.3f}–{max(samples):.3f}]"


def ir_cell(samples):
    median = statistics.median(samples)
    spread = 100 * (max(samples) - min(samples)) / 2 / median if median else 0
    return f"{round(median):,} ±{spread:.1f}%"


def describe_config(config):
    parts = [config["curve"]]
    parts += [f"{name}={value}" for name, value in config["sizes"].items()]
    if config["analysis"]:
        parts.append(config["analysis"])
    if config["rounds"]:
        parts.append("rounds=" + ",".join(map(str, config["rounds"])))
    return ", ".join(parts)


def render(request, run_url, result=None, failure=None):
    marker = f"<!-- zippel-benchmark-report:{request['mode']} -->"
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    lines = [marker, f"### Zippel benchmarks · {request['mode']}",
             f"Examples: {', '.join('`' + name + '`' for name in request['examples'])}.",
             f"Base `{request['base_sha'][:12]}` → head `{request['head_sha'][:12]}` · one Rayon worker · {stamp}",
             "", f"Native times are milliseconds: median [min–max] of {SAMPLES} samples per process. CI timing is advisory."]
    if request.get("local_working_trees"):
        lines.append("Local working-tree verification; commit labels do not include uncommitted changes.")
    if result is not None:
        if "build_seconds" in result:
            builds = result["build_seconds"]
            lines.append(f"Rust builds: base {builds['base']:.1f}s, head {builds['head']:.1f}s.")
        if "measurement_seconds" in result:
            lines.append(f"Measurement: {result['measurement_seconds']:.1f}s (runner setup excluded).")
    configs = []
    for name in request["examples"]:
        row = next((row for row in result["rows"] if row["example"] == name), None) if result else None
        if row and row["base"]["status"] == "ok" and row["head"]["status"] == "ok":
            base, head = row["base"]["config"], row["head"]["config"]
            label = describe_config(base) if base == head else f"base {describe_config(base)} → head {describe_config(head)}"
        else:
            spec = CATALOG["examples"][name][request["mode"]]
            sizes = request.get("sizes") if request.get("sizes") is not None else spec["sizes"]
            label = ", ".join(f"{k}={v}" for k, v in sizes.items()) or "registered defaults"
            if request["mode"] == "analyze":
                label = (spec["pass"] or "registered analysis") + ", " + label
        configs.append(f"`{name}`: {label}")
    lines.append("; ".join(configs) + ".")
    if request["mode"] == "run":
        lines.append("Existing example inputs and protocol randomness differ per sample, so Ir varies too. Prove/verify exclude input generation.")
    else:
        lines.append("Singular; compile, graph preparation, and the selected analysis pass are measured separately. Analysis Ir includes profiled Singular children.")
    if result is None:
        lines += ["", f"No valid comparison: {failure}."]
    else:
        lines += ["", f"Ir is the median of {SAMPLES} profiled samples ± half their range.",
                  "", "| Example / phase | Base Ir | Head Ir | Δ Ir | Base ms | Head ms | Δ time |",
                  "|---|---:|---:|---:|---:|---:|---:|"]
        for row in result["rows"]:
            base, head = row["base"], row["head"]
            name = row["example"]
            if base["status"] != "ok" or head["status"] != "ok":
                lines.append(f"| {name} | {base['status']} | {head['status']} | — | — | — | — |")
                continue
            comparable = base["workload"] == head["workload"] and base["config"] == head["config"]
            for phase in phases(request["mode"]):
                counts = []
                for side in (base, head):
                    value = side["instructions"]
                    counts.append([p + c for p, c in zip(value[phase]["parent"], value[phase]["children"])]
                                  if value is not None else None)
                count_cells = [ir_cell(count) if count is not None else side["instruction_status"]
                               for count, side in zip(counts, (base, head))]
                di = change(*counts) if comparable and all(v is not None for v in counts) else "—"
                bt, ht = base["ms"][phase], head["ms"][phase]
                dt = change(bt, ht) if comparable else "—"
                label = f"{name} / {phase}" + (" (workload changed)" if not comparable else "")
                lines.append(f"| {label} | {count_cells[0]} | {count_cells[1]} | {di} | {time_cell(bt)} | {time_cell(ht)} | {dt} |")
        lines += ["", "Ir is executed instructions, not elapsed-time speedup. A change marked (noise) lies inside both sides' sample ranges. Missing/timeout profiles have no instruction delta."]
    if run_url is not None:
        lines += ["", f"[Workflow run]({run_url}) · [Raw results and profiles]({run_url}#artifacts)"]
    return "\n".join(lines)


def publish(api, request, run_url, result=None, failure=None):
    pr = api.api(api.repo_path(f"pulls/{request['pr']}"))
    if pr["state"] != "open":
        return False
    if ((request["selectors"]["head"] is None and pr["head"]["sha"] != request["observed_head_sha"])
            or (request["selectors"]["base"] is None and pr["base"]["sha"] != request["observed_base_sha"])):
        # Numbers for a superseded tip would mislead; say why there are none.
        result, failure = None, "the PR's base or head moved after the request; comment the command again to measure the new tip"
    body = render(request, run_url, result, failure)
    marker = f"<!-- zippel-benchmark-report:{request['mode']} -->"
    matches = [c for c in api.pages(api.repo_path(f"issues/{request['pr']}/comments"))
               if c["user"]["login"] == "github-actions[bot]" and c["body"].startswith(marker + "\n")]
    if matches:
        api.api(api.repo_path(f"issues/comments/{matches[-1]['id']}"), "PATCH", {"body": body})
    else:
        api.comment(request["pr"], body)
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("publish", "local"))
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--request", type=Path, help="local only: request.json written by run.py local")
    parser.add_argument("--output", type=Path, help="local only: Markdown destination")
    args = parser.parse_args()
    if args.action == "local":
        request = read_json(args.request.read_bytes())
        result = validate_results(args.results.read_bytes(), request)
        local = {**request, "pr": 0, "repository": "eniac/zippel"}
        args.output.write_text(render(local, None, result))
        return
    # The request comes from the trusted request job; only the results
    # artifact was produced next to PR code, so only it is validated.
    request = read_json(os.environ["REQUEST"].encode())
    run_url = f"https://github.com/{request['repository']}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
    try:
        if args.results.is_symlink():
            raise ValueError("results must be a regular file")
        result, failure = validate_results(args.results.read_bytes(), request), None
    except (OSError, ValueError, KeyError, TypeError):
        result, failure = None, "build/run failed or results were missing/invalid; see the workflow logs"
    publish(GitHub(), request, run_url, result, failure)


if __name__ == "__main__":
    main()
