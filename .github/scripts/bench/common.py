"""Command grammar, harness configuration checks and GitHub access for PR benchmarks."""

from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CATALOG = json.loads((HERE / "suite.json").read_bytes())
registry_match = re.search(r"\$callback!\s*\{([^}]+)\}", (HERE.parents[2] / "examples/registry.rs").read_text())
if registry_match is None:
    raise ValueError("missing shared example registry")
REGISTERED = [name.strip() for name in registry_match[1].split(",") if name.strip()]
if any(not re.fullmatch(r"[a-z][a-z0-9_]*", name) for name in REGISTERED):
    raise ValueError("invalid shared example registry")
presets = CATALOG["examples"]
CATALOG["examples"] = {
    name: {"run": {"sizes": {}},
           "analyze": {"sizes": {}, "pass": None}, **presets.get(name, {})}
    for name in REGISTERED
}
MAX_JSON = 1024 * 1024
SHA = re.compile(r"[0-9a-f]{40}\Z")
USAGE = "usage: /bench run|analyze [example ...] [--base COMMIT] [--head COMMIT] [--size NAME=VALUE ...]"


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def read_json(data, limit=MAX_JSON):
    if len(data) > limit:
        raise ValueError("JSON exceeds size limit")
    def invalid(value):
        raise ValueError(f"nonfinite JSON number: {value}")
    try:
        return json.loads(data, object_pairs_hook=_object, parse_constant=invalid)
    except (RecursionError, UnicodeError) as error:
        raise ValueError("invalid JSON") from error


@dataclass(frozen=True)
class Command:
    mode: str
    examples: list[str]
    base: str | None = None
    head: str | None = None
    sizes: dict[str, int] | None = None


def is_command(body):
    words = body.split(maxsplit=1)
    return bool(words) and words[0] == "/bench"


def parse_command(body):
    if not is_command(body):
        return None
    line = body.strip()
    if len(line) > 4096 or "\n" in line or "\r" in line:
        raise ValueError("use one command line")
    words = line.split()
    if len(words) < 2 or words[1] not in ("run", "analyze"):
        raise ValueError(USAGE)
    mode = words[1]
    names = []
    selectors = {}
    sizes = None
    index = 2
    while index < len(words):
        word = words[index]
        if word in ("--base", "--head"):
            if word in selectors or index + 1 == len(words):
                raise ValueError("each commit option requires one value and may appear once")
            selector = words[index + 1]
            if selector not in ("main", "pr") and not re.fullmatch(r"[a-fA-F0-9]{7,40}", selector):
                raise ValueError("commit must be main, pr, or a 7–40 character commit SHA")
            selectors[word] = selector.lower()
            index += 2
        elif word in ("--size", "-s"):
            if index + 1 == len(words):
                raise ValueError("--size requires NAME=VALUE")
            name, separator, value = words[index + 1].partition("=")
            if (not separator or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name)
                    or not re.fullmatch(r"[0-9]+", value) or int(value) >= 2**64):
                raise ValueError("size must be NAME=VALUE with a nonnegative machine integer")
            if sizes is None:
                sizes = {}
            if name in sizes:
                raise ValueError(f"size {name} is given twice")
            sizes[name] = int(value)
            index += 2
        else:
            names.append(word)
            index += 1
    names = list(dict.fromkeys(names or CATALOG["defaults"]))
    unsupported = [name for name in names if mode not in CATALOG["examples"].get(name, {})]
    if unsupported:
        choices = [name for name, spec in CATALOG["examples"].items() if mode in spec]
        raise ValueError(f"unsupported {mode} examples: {', '.join(unsupported)}; choose: {', '.join(choices)}")
    return Command(mode, names, selectors.get("--base"), selectors.get("--head"), sizes)


def positive(value):
    return type(value) is int and value > 0


def validate_config(config, mode):
    """The harness runs PR code, so its self-description is checked before it is shown."""
    if type(config) is not dict or set(config) != {"sizes", "source", "curve", "analysis", "rounds"}:
        raise ValueError("invalid harness configuration")
    sizes = config["sizes"]
    if (type(sizes) is not dict or len(sizes) > 32
            or any(len(key) > 64 or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key)
                   or type(value) is not int or not 0 <= value < 2**64 for key, value in sizes.items())):
        raise ValueError("invalid resolved sizes")
    if not isinstance(config["source"], str) or len(config["source"]) > 512 or not re.fullmatch(r"examples/[A-Za-z0-9_/-]+\.zippel", config["source"]):
        raise ValueError("invalid protocol source path")
    if not isinstance(config["curve"], str) or len(config["curve"]) > 128 or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", config["curve"]):
        raise ValueError("invalid curve name")
    if config["analysis"] not in ((None,) if mode == "run" else ("completeness", "zk", "soundness")):
        raise ValueError("invalid analysis selection")
    rounds = config["rounds"]
    if not isinstance(rounds, list) or len(rounds) > 64 or any(not positive(value) or value >= 2**64 for value in rounds):
        raise ValueError("invalid soundness rounds")
    if config["analysis"] == "soundness":
        if not rounds or any(value < 2 for value in rounds):
            raise ValueError("soundness requires transcript counts of at least two")
    elif rounds:
        raise ValueError("unexpected soundness rounds")
    return config


def output(**values):
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a", encoding="utf-8") as stream:
            for key, value in values.items():
                text = str(value)
                if "\n" in text or "\r" in text:
                    raise ValueError("multiline output")
                stream.write(f"{key}={text}\n")


class GitHub:
    def __init__(self, repository=None):
        self.repository = repository or os.environ["GITHUB_REPOSITORY"]

    def api(self, path, method="GET", data=None, select=None):
        args = ["gh", "api", "--method", method, path]
        if select is not None:
            args += ["--jq", select]
        if data is not None:
            args += ["--input", "-"]
        result = subprocess.run(args, input=canonical(data) if data is not None else None,
                                capture_output=True, timeout=30)
        if result.returncode:
            # Callers may handle the failure, but the log should say why.
            sys.stderr.write(f"gh api {method} {path}: {result.stderr.decode(errors='replace')}")
            raise subprocess.CalledProcessError(result.returncode, args, result.stdout, result.stderr)
        return read_json(result.stdout or b"null", limit=16 * MAX_JSON)

    def pages(self, path):
        separator = "&" if "?" in path else "?"
        for page in range(1, 101):
            items = self.api(f"{path}{separator}per_page=100&page={page}")
            yield from items
            if len(items) < 100:
                return
        raise ValueError("pagination limit exceeded")

    def repo_path(self, suffix):
        return f"repos/{self.repository}/{suffix}"

    def permission(self, login):
        if not re.fullmatch(r"[A-Za-z0-9-]+", login):
            raise ValueError("invalid author")
        response = self.api(self.repo_path(f"collaborators/{login}/permission"))
        return response.get("permission") in ("admin", "maintain", "write")

    def comment(self, pr, body):
        self.api(self.repo_path(f"issues/{pr}/comments"), "POST", {"body": body})

    def react(self, comment_id, content):
        self.api(self.repo_path(f"issues/comments/{comment_id}/reactions"), "POST", {"content": content})
