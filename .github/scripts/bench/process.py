"""Running revision code: output kept on disk and bounded, a time limit, and no
process left behind."""

import os
import signal
import subprocess

MAX_OUTPUT = 32 * 1024 * 1024


def execute(args, cwd, env, timeout, log):
    """Run `args` with stdout in `log` and stderr beside it. Raises ValueError on a
    nonzero exit and TimeoutExpired past `timeout`; the whole process group is
    killed either way, even after a successful parent exit."""
    with log.open("wb") as stream, log.with_suffix(".stderr").open("wb") as errors:
        child = subprocess.Popen(args, cwd=cwd, env=env, stdout=stream, stderr=errors, start_new_session=True)
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
    if log.stat().st_size > MAX_OUTPUT:
        raise ValueError("process output exceeds limit")


def environment(**overrides):
    """The runner's environment without credentials or Actions plumbing,
    single-threaded, plus `overrides`."""
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("ACTIONS_", "GH_", "AWS_", "SSH_", "ZIPPEL_BENCH_"))
           and key not in ("GITHUB_TOKEN", "GITHUB_ENV", "GITHUB_OUTPUT", "GITHUB_PATH")}
    env.update(RAYON_NUM_THREADS="1", CARGO_TERM_COLOR="never", **overrides)
    return env
