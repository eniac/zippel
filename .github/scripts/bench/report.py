"""Validate untrusted measurements and update only their authorized PR report."""

import argparse
from datetime import datetime, timezone
import math
import os
from pathlib import Path
import re
import statistics

from common import GitHub, read_json, validate_config
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
            expected = None
            if measured["status"] == "ok":
                config = validate_config(measured.get("config"), request["mode"])
                expected = set(phases(request["mode"], config))
                if type(times) is not dict or set(times) != expected:
                    raise ValueError("incomplete native timing phases")
                for samples in times.values():
                    if not isinstance(samples, list) or len(samples) != SAMPLES or not all(number(v) for v in samples):
                        raise ValueError("invalid native timing samples")
                if "workload" not in measured:
                    raise ValueError("missing workload identity")
                sizes = request.get("sizes")
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
    """Median change: bold when the two sides' samples do not overlap,
    "(noise)" when they do."""
    low, high = statistics.median(base), statistics.median(head)
    if low <= 0:
        return "—"
    text = f"{100 * (high / low - 1):+.1f}%"
    if max(min(base), min(head)) <= min(max(base), max(head)):
        return f"{text} (noise)"
    return f"**{text}**"


def ms_cell(samples):
    median = statistics.median(samples)
    digits = 0 if median >= 100 else 1 if median >= 10 else 2 if median >= 1 else 3
    return f"{median:.{digits}f}"


def describe_config(config):
    parts = [config["curve"], *(f"{name}={value}" for name, value in config["sizes"].items())]
    if config["analysis"]:
        parts += config["analysis"]
    if config["rounds"]:
        parts.append("rounds " + ",".join(map(str, config["rounds"])))
    return ", ".join(parts)


def describe_example(request, name, row):
    if row and row["base"]["status"] == "ok" and row["head"]["status"] == "ok":
        base, head = describe_config(row["base"]["config"]), describe_config(row["head"]["config"])
        label = base if base == head else f"base {base}; head {head}"
    else:
        label = ", ".join(f"{k}={v}" for k, v in (request.get("sizes") or {}).items())
    return f"`{name}` ({label})" if label else f"`{name}`"


def render(request, run_url, result=None, failure=None):
    rows = {row["example"]: row for row in result["rows"]} if result else {}
    lines = [f"<!-- zippel-benchmark-report:{request['mode']} -->",
             f"### Zippel benchmarks: {request['mode']}", "",
             f"Base `{request['base_sha'][:12]}` → head `{request['head_sha'][:12]}`", ""]
    if result is None:
        lines.append(f"No comparison: {failure}.")
    else:
        lines += ["| Example / phase | Base Ir | Head Ir | Δ Ir | Base ms | Head ms | Δ time |",
                  "|---|---:|---:|---:|---:|---:|---:|"]
        for row in result["rows"]:
            base, head = row["base"], row["head"]
            name = row["example"]
            if base["status"] != "ok" or head["status"] != "ok":
                lines.append(f"| {name} | {base['status']} | {head['status']} | — | — | — | — |")
                continue
            changed = base["workload"] != head["workload"] or base["config"] != head["config"]
            # A revision can register different analyses; show the union.
            names = dict.fromkeys(phases(request["mode"], head["config"]) + phases(request["mode"], base["config"]))
            for phase in names:
                counts, times = [], []
                for side in (base, head):
                    value = side["instructions"]
                    present = phase in side["ms"]
                    counts.append([p + c for p, c in zip(value[phase]["parent"], value[phase]["children"])]
                                  if value is not None and present else None)
                    times.append(side["ms"].get(phase))
                count_cells = [f"{round(statistics.median(count)):,}" if count is not None
                               else side["instruction_status"] if phase in side["ms"] else "—"
                               for count, side in zip(counts, (base, head))]
                di = change(*counts) if all(v is not None for v in counts) else "—"
                time_cells = [ms_cell(t) if t is not None else "—" for t in times]
                dt = change(*times) if all(t is not None for t in times) else "—"
                label = f"{name} / {phase}" + (" (workload changed)" if changed else "")
                lines.append(f"| {label} | {count_cells[0]} | {count_cells[1]} | {di} | {time_cells[0]} | {time_cells[1]} | {dt} |")
    examples = ", ".join(describe_example(request, name, rows.get(name)) for name in request["examples"])
    samples = f"median of {SAMPLES} per side on one runner with one Rayon worker"
    if request["mode"] == "run":
        samples += "; fresh example inputs per sample, generated outside the measured phases"
    else:
        samples += "; analysis Ir includes Singular"
    lines += ["", f"- **Examples:** {examples}"]
    if result is not None:
        lines.append(f"- **Samples:** {samples}")
    if result is not None and "build_seconds" in result:
        builds = result["build_seconds"]
        duration = f"builds {builds['base']:.0f} s (base) and {builds['head']:.0f} s (head)"
        if "measurement_seconds" in result:
            duration += f"; measurement {result['measurement_seconds']:.0f} s"
        lines.append(f"- **Duration:** {duration}")
    run = [datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")]
    if run_url is not None:
        run += [f"[workflow]({run_url})", f"[raw results and profiles]({run_url}#artifacts)"]
    if request.get("local_working_trees"):
        run.append("local working trees, so uncommitted changes are not in the commit labels")
    lines.append(f"- **Run:** {' · '.join(run)}")
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
