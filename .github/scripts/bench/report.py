"""Report job: validate results.json against the trusted request and update the
PR's report comment for the mode."""

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import statistics

from github import GitHub
from model import SAMPLES, Results
from untrusted import load

HEADER = ["| Example / phase | Base Ir | Head Ir | Δ Ir | Base ms | Head ms | Δ time |",
          "|---|---:|---:|---:|---:|---:|---:|"]


def marker(mode):
    """The first line of the bot's report comment for a mode."""
    return f"<!-- zippel-benchmark-report:{mode} -->"


def code(value):
    """Untrusted text as inline code: no mentions, links or HTML, and no way out
    of the code span or the table cell."""
    value = " ".join(str(value).split()).replace("|", "\\|")
    fence = "`" * (max(map(len, re.findall("`+", value)), default=0) + 1)
    return f"{fence} {value} {fence}"


def change(base, head):
    """Median change: bold when the two sides' samples do not overlap, "(noise)"
    when they do."""
    if base is None or head is None:
        return "—"
    low, high = statistics.median(base), statistics.median(head)
    if low <= 0:
        return "—"
    text = f"{100 * (high / low - 1):+.1f}%"
    if max(min(base), min(head)) <= min(max(base), max(head)):
        return f"{text} (noise)"
    return f"**{text}**"


def ms_cell(samples):
    if samples is None:
        return "—"
    median = statistics.median(samples)
    digits = 0 if median >= 100 else 1 if median >= 10 else 2 if median >= 1 else 3
    return f"{median:.{digits}f}"


def ir_cell(case, phase):
    if case.instructions is not None and phase in case.instructions:
        return f"{round(statistics.median(case.instructions[phase].totals())):,}"
    # A phase this side measured but did not profile says why.
    return case.instruction_status if phase in case.measurement.ms else "—"


def table_rows(row):
    """One line per phase, or one line saying why the example was not compared."""
    base, head = row.base, row.head
    name = code(row.example)
    if base.status != "ok" or head.status != "ok":
        return [f"| {name} | {base.status} | {head.status} | — | — | — | — |"]
    changed = base.workload != head.workload or base.measurement.config != head.measurement.config
    lines = []
    # A revision can register different analyses; show the union.
    for phase in dict.fromkeys(head.measurement.phases + base.measurement.phases):
        times = [case.measurement.ms.get(phase) for case in (base, head)]
        counts = [case.instructions[phase].totals() if case.instructions and phase in case.instructions else None
                  for case in (base, head)]
        label = f"{name} / {code(phase)}" + (" (workload changed)" if changed else "")
        cells = [label, ir_cell(base, phase), ir_cell(head, phase), change(*counts),
                 ms_cell(times[0]), ms_cell(times[1]), change(*times)]
        lines.append(f"| {' | '.join(cells)} |")
    return lines


def describe_config(config):
    parts = [config.curve, *(f"{name}={value}" for name, value in config.sizes.items())]
    parts += config.analysis or []
    if config.rounds:
        parts.append("rounds " + ",".join(map(str, config.rounds)))
    return ", ".join(map(code, parts))


def describe_example(request, name, row):
    if row is not None and row.base.status == "ok" and row.head.status == "ok":
        base, head = (describe_config(case.measurement.config) for case in (row.base, row.head))
        label = base if base == head else f"base {base}; head {head}"
    else:
        label = ", ".join(code(f"{size}={value}") for size, value in (request.get("sizes") or {}).items())
    return f"{code(name)} ({label})" if label else code(name)


def render(request, run_url, results=None, failure=None):
    mode = request["mode"]
    lines = [marker(mode), f"### Zippel benchmarks: {mode}", "",
             f"Base `{request['base_sha'][:12]}` → head `{request['head_sha'][:12]}`", ""]
    if results is None:
        lines.append(f"No comparison: {failure}.")
    else:
        lines += HEADER
        for row in results.rows:
            lines += table_rows(row)
    rows = {row.example: row for row in results.rows} if results else {}
    examples = ", ".join(describe_example(request, name, rows.get(name)) for name in request["examples"])
    lines += ["", f"- **Examples:** {examples}"]
    if results is not None:
        samples = f"median of {SAMPLES} per side on one runner with one Rayon worker"
        samples += ("; fresh example inputs per sample, generated outside the measured phases" if mode == "run"
                    else "; analysis Ir includes Singular")
        lines.append(f"- **Samples:** {samples}")
        if results.build_seconds is not None:
            builds = results.build_seconds
            duration = f"builds {builds['base']:.0f} s (base) and {builds['head']:.0f} s (head)"
            if results.measurement_seconds is not None:
                duration += f"; measurement {results.measurement_seconds:.0f} s"
            lines.append(f"- **Duration:** {duration}")
    run = [datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
           f"[workflow]({run_url})", f"[raw results and profiles]({run_url}#artifacts)"]
    lines.append(f"- **Run:** {' · '.join(run)}")
    return "\n".join(lines)


def publish(api, request, run_url, results=None, failure=None):
    """Create or update the mode's report on an open PR; False if it is closed."""
    pr = api.api(api.repo_path(f"pulls/{request['pr']}"))
    if pr["state"] != "open":
        return False
    if ((request["selectors"]["head"] is None and pr["head"]["sha"] != request["observed_head_sha"])
            or (request["selectors"]["base"] is None and pr["base"]["sha"] != request["observed_base_sha"])):
        # Numbers for a superseded tip would mislead; say why there are none.
        results, failure = None, ("the PR's base or head moved after the request; "
                                  "comment the command again to measure the new tip")
    body = render(request, run_url, results, failure)
    first_line = marker(request["mode"]) + "\n"
    reports = [comment for comment in api.pages(api.repo_path(f"issues/{request['pr']}/comments"))
               if comment["user"]["login"] == "github-actions[bot]" and comment["body"].startswith(first_line)]
    if reports:
        api.api(api.repo_path(f"issues/comments/{reports[-1]['id']}"), "PATCH", {"body": body})
    else:
        api.comment(request["pr"], body)
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, required=True)
    args = parser.parse_args()
    # The request comes from the trusted request job; only the results
    # artifact was produced next to PR code, so only it is validated.
    request = load(os.environ["REQUEST"].encode())
    run_url = f"https://github.com/{request['repository']}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
    try:
        if args.results.is_symlink():
            raise ValueError("results must be a regular file")
        results, failure = Results.from_json(args.results.read_bytes(), request), None
    except (OSError, ValueError):
        results, failure = None, "build/run failed or results were missing/invalid; see the workflow logs"
    publish(GitHub(), request, run_url, results, failure)


if __name__ == "__main__":
    main()
