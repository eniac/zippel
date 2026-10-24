"""Reproduce the local control-path, counter, and real benchmark checks."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import CATALOG, canonical
from report import render, validate_results
from run import comparison, instruction_total, local_request

ROOT = Path(__file__).resolve().parents[4]


def compile_target(arguments, name, directory):
    log = directory / f"build-{name}.jsonl"
    with log.open("w") as stream:
        subprocess.run(["cargo", "build", "--locked", "--release", "--offline",
                        "--message-format=json", *arguments], cwd=ROOT, stdout=stream, check=True)
    rows = [json.loads(line) for line in log.read_text().splitlines()]
    paths = {row["executable"] for row in rows if row.get("reason") == "compiler-artifact"
             and row.get("target", {}).get("name") == name and row.get("executable")}
    if len(paths) != 1:
        raise ValueError("Cargo did not produce the expected executable")
    return paths.pop()


def counter_controls(directory):
    probe = directory / "profile-probe"
    subprocess.run(["rustc", "-O", str(ROOT / ".github/scripts/bench/verification/profile_probe.rs"), "-o", str(probe)], check=True)
    counts = {}
    for name, inside, outside in (("baseline", 100, 100), ("inside", 100000, 100), ("outside", 100, 100000)):
        stage = directory / name
        stage.mkdir()
        subprocess.run(["valgrind", "--tool=callgrind", "--instr-atstart=no",
                        f"--callgrind-out-file={stage}/parent.%p", f"--log-file={stage}/valgrind.log",
                        str(probe), str(inside), str(outside)],
                       env={**os.environ, "ZIPPEL_BENCH_PROFILE_DIR": str(stage)}, check=True, timeout=15)
        files = [p for p in stage.glob("parent.*") if "Client Request: prove" in p.read_text()]
        if len(files) != 1:
            raise ValueError("worker control did not produce one measured part")
        counts[name] = instruction_total(files[0].read_text())
    if counts["inside"] <= counts["baseline"] + 400000:
        raise ValueError("counter missed worker-thread work")
    if abs(counts["outside"] - counts["baseline"]) >= 50000:
        raise ValueError("counter included excluded work")
    (directory / "counter-controls.json").write_bytes(canonical(counts))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, required=True, help="new scratch directory")
    args = parser.parse_args()
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    if not shutil.which("valgrind") or not shutil.which("Singular"):
        parser.error("put Valgrind and Singular on PATH")
    subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", str(Path(__file__).parent.parent / "tests"), "-p", "test_*.py"], check=True)
    binary = compile_target(["-p", "zippel", "--bench", "ci"], "ci", directory)
    counter_controls(directory)
    for mode, names in (("run", ["pst13", "kzg"]), ("analyze", ["pst13", "kzg", "schnorr"])):
        stage = directory / mode
        stage.mkdir()
        request = local_request(mode, names, ROOT)
        result = comparison(request, {"base": ROOT, "head": ROOT},
                            {"base": binary, "head": binary}, stage,
                            time.monotonic() + CATALOG["budget_seconds"])
        raw = canonical(result)
        validate_results(raw, request)
        for row in result["rows"]:
            for side in ("base", "head"):
                if row[side]["status"] != "ok" or row[side]["instruction_status"] != "ok":
                    raise ValueError(f"real {mode} case failed: {row['example']} {side}: {row[side]}")
        if mode == "analyze":
            soundness = next(row for row in result["rows"] if row["example"] == "schnorr")
            if not any(count["children"] > 0 for count in soundness["base"]["instructions"].values()):
                raise ValueError("soundness profile missed Singular children")
        (stage / "results.json").write_bytes(raw)
        (stage / "request.json").write_bytes(canonical(request))
        (stage / "report.md").write_text(render(request, None, result))
    print(f"Verified parser/provenance tests, worker controls and real run/analyze results: {directory}")


if __name__ == "__main__":
    main()
