"""Bounded local/Actions comparison of the registered example specifications."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import time

from common import ANALYSES, CATALOG, canonical, parse_command, read_json, validate_config

# Native timings and instruction profiles each take this many samples per phase.
SAMPLES = 3


def execute(args, cwd, environment, timeout, log):
    """Keep output on disk and kill descendants even after a successful parent exit."""
    with log.open("wb") as stream, log.with_suffix(".stderr").open("wb") as errors:
        child = subprocess.Popen(args, cwd=cwd, env=environment, stdout=stream,
                                 stderr=errors, start_new_session=True)
        try:
            code = child.wait(timeout=max(0.01, timeout))
            if code:
                raise ValueError(f"process exited {code}; see {log.name}")
        finally:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
    if log.stat().st_size > 32 * 1024 * 1024:
        raise ValueError("process output exceeds limit")


def environment():
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("ACTIONS_", "GH_", "AWS_", "SSH_"))
           and key not in ("GITHUB_TOKEN", "GITHUB_ENV", "GITHUB_OUTPUT", "GITHUB_PATH")}
    env.update(RAYON_NUM_THREADS="1", CARGO_TERM_COLOR="never")
    env.pop("ZIPPEL_BENCH_PROFILE_DIR", None)
    return env


def build(tree, directory, target_directory, timeout):
    """Build the revision's own CI harness, which matches its library API."""
    directory.mkdir(parents=True, exist_ok=True)
    env = environment()
    env["CARGO_TARGET_DIR"] = str(target_directory)
    start = time.monotonic()
    log = directory / "build.jsonl"
    try:
        execute(["cargo", "build", "--locked", "--release", "--message-format=json",
                 "-p", "zippel", "--bench", "ci"], tree, env, timeout, log)
    except ValueError:
        # The logs are not uploaded; put Cargo's errors in the job log.
        print(f"{tree.name} build failed:", file=sys.stderr)
        for line in log.read_text().splitlines() if log.exists() else []:
            row = json.loads(line)
            if row.get("reason") == "compiler-message" and row["message"]["level"] == "error":
                print(row["message"]["rendered"], file=sys.stderr)
        errors = log.with_suffix(".stderr")
        print("\n".join(errors.read_text().splitlines()[-20:]) if errors.exists() else "", file=sys.stderr)
        raise
    executables = {row["executable"] for line in log.read_text().splitlines()
                   if (row := json.loads(line)).get("reason") == "compiler-artifact"
                   and row.get("target", {}).get("name") == "ci" and row.get("executable")}
    if len(executables) != 1:
        raise ValueError("Cargo did not identify one benchmark executable")
    # Both revisions share the target directory, so keep this one's copy.
    binary = directory / "ci"
    shutil.copy2(next(iter(executables)), binary)
    return str(binary), time.monotonic() - start


def phases(mode, config):
    """Measured phases; `analyze` times each analysis the example registers."""
    if mode == "run":
        return ("compile", "prove", "verify")
    return ("compile", "prepare", *config["analysis"])


def arguments(binary, mode, name, sizes=None):
    """Without sizes, the harness uses the example's own defaults for the mode."""
    args = [binary, mode, name]
    for key, value in (sizes or {}).items():
        args += ["--size", f"{key}={value}"]
    return args


def final_record(path):
    rows = [read_json(line.encode()) for line in path.read_text().splitlines() if line.startswith("{")]
    if not rows or rows[-1].get("status") != "ok":
        raise ValueError("benchmark did not report final status ok")
    return rows[-1]


def native(binary, tree, mode, name, directory, timeout, sizes=None):
    log = directory / "native.jsonl"
    env = environment()
    execute(arguments(binary, mode, name, sizes) + ["--samples", str(SAMPLES)], tree, env, timeout, log)
    row = final_record(log)
    config = validate_config(row.get("config"), mode)
    if set(row.get("ms", {})) != set(phases(mode, config)):
        raise ValueError("harness did not report the requested phases")
    if any(not isinstance(samples, list) or len(samples) != SAMPLES
           or any(type(v) not in (int, float) or not 0 <= v < 1e15 for v in samples)
           for samples in row["ms"].values()):
        raise ValueError("harness did not report three native samples per phase")
    return {"ms": row["ms"], "config": config}


def parse_profiles(directory, expected, samples=SAMPLES):
    """Per phase, the parent and Singular-children Ir of each sample, in order."""
    parent = {}
    children = {(phase, index): 0 for phase in expected for index in range(samples)}
    for path in directory.glob("parent.*"):
        if path.suffix == ".log":
            continue
        content = path.read_text()
        label = re.search(r"Client Request: ([a-z]+)\.([0-9]+)$", content, re.MULTILINE)
        if label is None:
            continue
        key = (label[1], int(label[2]))
        if key not in children:
            raise ValueError("unexpected parent profile sample")
        if key in parent:
            raise ValueError("duplicate parent profile sample")
        parent[key] = instruction_total(content)
    for path in directory.glob("child.*"):
        if path.suffix == ".log":
            continue
        parts = path.name.split(".")
        key = (parts[1], int(parts[2])) if len(parts) > 2 and parts[2].isdigit() else None
        if key not in children:
            raise ValueError("unattributed Singular child profile")
        children[key] += instruction_total(path.read_text())
    if set(parent) != set(children):
        raise ValueError("missing parent profile samples")
    launched = directory / "children"
    if launched.exists():
        names = launched.read_text().splitlines()
        if len(names) != len(list(directory.glob("child.*.out"))):
            raise ValueError("missing Singular child profile")
    return {phase: {"parent": [parent[phase, i] for i in range(samples)],
                    "children": [children[phase, i] for i in range(samples)]} for phase in expected}


def instruction_total(content):
    events = next((line.split()[1:] for line in content.splitlines() if line.startswith("events:")), [])
    # Client-request dumps can have a zero summary placeholder. The final
    # totals line is the completed, non-inclusive event count for this part.
    values = next((line.split()[1:] for line in content.splitlines() if line.startswith("totals:")), [])
    if "Ir" not in events or len(events) != len(values):
        raise ValueError("incomplete Callgrind summary")
    value = int(values[events.index("Ir")])
    if value <= 0:
        raise ValueError("empty instruction profile")
    return value


def profile(binary, tree, mode, name, directory, timeout, expected, sizes=None):
    valgrind = shutil.which("valgrind")
    if not valgrind:
        raise FileNotFoundError("valgrind is not installed")
    directory = directory.resolve()
    env = environment()
    env["ZIPPEL_BENCH_PROFILE_DIR"] = str(directory)
    if mode == "analyze":
        singular = shutil.which("Singular")
        if not singular:
            raise FileNotFoundError("Singular is not installed")
        wrapper_dir = directory / "bin"
        wrapper_dir.mkdir()
        wrapper = wrapper_dir / "Singular"
        wrapper.write_text(f'''#!{sys.executable}
import os
from pathlib import Path
import sys
root = Path({str(directory)!r})
phase = (root / "phase").read_text()
name, _, index = phase.partition(".")
if name not in {("compile", "prepare", *ANALYSES)!r} or not index.isdigit():
    raise ValueError("Singular launched outside a measured analysis phase")
with (root / "children").open("a") as stream:
    stream.write(phase + "\\n")
os.execv({valgrind!r}, [{valgrind!r}, "--tool=callgrind", "--instr-atstart=yes",
    "--callgrind-out-file=" + str(root / ("child." + phase + ".%p.out")),
    "--log-file=" + str(root / "child.%p.log"), {singular!r}, *sys.argv[1:]])
''')
        wrapper.chmod(0o755)
        env["PATH"] = str(wrapper_dir) + os.pathsep + env["PATH"]
    args = [valgrind, "--tool=callgrind", "--instr-atstart=no", "--separate-threads=no",
            f"--callgrind-out-file={directory}/parent.%p", f"--log-file={directory}/parent.log"]
    execute(args + arguments(binary, mode, name, sizes) + ["--samples", str(SAMPLES)], tree, env, timeout,
            directory / "profile.jsonl")
    final_record(directory / "profile.jsonl")
    return parse_profiles(directory, expected)


def workload(tree, name, source):
    common = sorted(path.relative_to(tree).as_posix() for path in (tree / "examples/common").glob("*.rs"))
    paths = [source, *common, f"examples/{name}/main.rs"]
    payload = b"".join(path.encode() + (tree / path).read_bytes() for path in paths)
    payload += b"".join(file.encode() + (tree / "benches/ci" / file).read_bytes() for file in ("main.rs", "profile.rs"))
    return hashlib.sha256(payload).hexdigest()


def comparison(request, trees, binaries, directory, deadline):
    """Measure until the deadline; cases that do not fit are reported as budget."""
    mode = request["mode"]
    started = time.monotonic()
    rows = []
    for name in request["examples"]:
        row = {"example": name}
        for side in ("base", "head"):
            row[side] = {"status": "budget", "ms": {}, "instructions": None, "instruction_status": "unavailable"}
        rows.append(row)
    for index, row in enumerate(rows):
        name = row["example"]
        for side in (("base", "head") if index % 2 == 0 else ("head", "base")):
            result = row[side]
            if result["status"] not in ("budget", "ok") or time.monotonic() >= deadline:
                continue
            stage = directory / f"{index}-{side}-native"
            stage.mkdir()
            try:
                measured = native(binaries[side], trees[side], mode, name, stage,
                                  deadline - time.monotonic(),
                                  request.get("sizes"))
                result.update(status="ok", **measured, workload=workload(trees[side], name, measured["config"]["source"]))
            except (ValueError, OSError, subprocess.TimeoutExpired) as error:
                print(f"{name} {side} native: {error!r}", file=sys.stderr)
                result.update(status="timeout" if isinstance(error, subprocess.TimeoutExpired) else "failed", ms={})
        for side in ("base", "head"):
            result = row[side]
            if result["status"] != "ok" or time.monotonic() >= deadline:
                continue
            stage = directory / f"{index}-{side}-instructions"
            stage.mkdir()
            try:
                result["instructions"] = profile(binaries[side], trees[side], mode, name, stage,
                                                 deadline - time.monotonic(),
                                                 phases(mode, result["config"]), request.get("sizes"))
                result["instruction_status"] = "ok"
            except (ValueError, OSError, subprocess.TimeoutExpired) as error:
                print(f"{name} {side} profile: {error!r}", file=sys.stderr)
                result["instruction_status"] = "timeout" if isinstance(error, subprocess.TimeoutExpired) else "unavailable"
    versions = {}
    for name, args in (("rust", ["rustc", "--version"]), ("valgrind", ["valgrind", "--version"]),
                       ("singular", ["Singular", "--version"])):
        try:
            versions[name] = subprocess.check_output(args, text=True, stderr=subprocess.STDOUT, timeout=5).splitlines()[0][:200]
        except (OSError, subprocess.SubprocessError, IndexError):
            versions[name] = "unavailable"
    cpu = platform.machine()
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        cpu = next((line.partition(":")[2].strip() for line in cpuinfo.read_text().splitlines()
                    if line.startswith("model name")), cpu)
    return {"mode": mode,
            "examples": request["examples"], "base_sha": request["base_sha"], "head_sha": request["head_sha"],
            "rows": rows, "measurement_seconds": time.monotonic() - started, "environment": {"platform": platform.platform(), "cpu": cpu, "threads": 1, **versions}}


def local_request(mode, names, tree, head=None, sizes=None):
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=tree, text=True).strip()
    head_sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=head or tree, text=True).strip()
    return {"mode": mode, "examples": names, "base_sha": sha, "head_sha": head_sha,
            "local_working_trees": True, "sizes": sizes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("compare", "local"))
    parser.add_argument("--base-dir", type=Path, required=True)
    parser.add_argument("--head-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mode", choices=("run", "analyze"))
    parser.add_argument("--examples", nargs="+")
    parser.add_argument("--size", "-s", action="append", default=[])
    parser.add_argument("--binaries", type=Path, help="local test only: JSON paths to already-built executables")
    args = parser.parse_args()
    if args.action == "local" and args.mode is None:
        parser.error("local comparison requires --mode")
    # Binaries live under the output's siblings and run from each checkout,
    # so every derived path must be absolute.
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    if args.action == "local":
        command = parse_command("/bench " + args.mode + " " + " ".join(args.examples or [])
                                + "".join(" --size " + size for size in args.size))
        request = local_request(command.mode, command.examples, args.base_dir, args.head_dir, command.sizes)
    else:
        # The trusted request job's output, passed through the environment.
        request = read_json(os.environ["REQUEST"].encode())
    (args.output / "request.json").write_bytes(canonical(request))
    trees = {"base": args.base_dir.resolve(), "head": args.head_dir.resolve()}
    if args.action != "local":
        for side in trees:
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=trees[side], text=True).strip()
            if actual != request[f"{side}_sha"]:
                raise ValueError("checkout does not match the frozen request")
    # The one budget covers builds and measurement; bench.yml's job
    # timeout only adds runner setup and uploads on top.
    deadline = time.monotonic() + CATALOG["budget_seconds"]
    if args.binaries:
        if args.action != "local":
            raise ValueError("binary reuse is only supported in local checks")
        binaries = read_json(args.binaries.read_bytes())
    else:
        binaries = {}
        build_seconds = {}
        for side in trees:
            build_dir = args.output.parent / f"{args.output.name}-build-{side}"
            binaries[side], build_seconds[side] = build(
                trees[side], build_dir, args.output.parent / f"{args.output.name}-target",
                deadline - time.monotonic())
    result = comparison(request, trees, binaries, args.output, deadline)
    if not args.binaries:
        result["build_seconds"] = build_seconds
    (args.output / "results.json").write_bytes(canonical(result))


if __name__ == "__main__":
    main()
