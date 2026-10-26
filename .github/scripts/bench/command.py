"""Request job: authorize a `/bench` comment and freeze it into the request the
later jobs run."""

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess

from github import GitHub, output
from untrusted import load

SUITE = json.loads(Path(__file__).with_name("suite.json").read_bytes())
SHA = re.compile(r"[0-9a-f]{40}\Z")
# Names, sizes and analyses are each revision's to define (`ci list`); a request
# only bounds how many examples one PR comment reports.
MAX_EXAMPLES = 64


@dataclass(frozen=True)
class Command:
    mode: str
    examples: list[str]
    base: str | None = None
    head: str | None = None
    sizes: dict[str, int] | None = None


class _Parser(argparse.ArgumentParser):
    """Raises instead of exiting, so the bot can reply with the message."""

    def error(self, message):
        raise ValueError(f"{message}\n{self.format_usage()}")


def _commit(value):
    if value in ("main", "pr") or re.fullmatch(r"[0-9a-fA-F]{7,40}", value):
        return value.lower()
    raise argparse.ArgumentTypeError("expected main, pr, or a 7–40 character commit SHA")


def _size(value):
    name, separator, number = value.partition("=")
    if not separator or not name or not re.fullmatch(r"[0-9]+", number) or int(number) >= 2**64:
        raise argparse.ArgumentTypeError("expected NAME=VALUE with a nonnegative machine integer")
    return name, int(number)


PARSER = _Parser(prog="/bench", add_help=False, allow_abbrev=False)
PARSER.add_argument("mode", choices=("run", "analyze"))
PARSER.add_argument("examples", nargs="*", metavar="example")
PARSER.add_argument("--base", type=_commit, metavar="COMMIT")
PARSER.add_argument("--head", type=_commit, metavar="COMMIT")
PARSER.add_argument("-s", "--size", type=_size, action="append", dest="sizes", metavar="NAME=VALUE")


def is_command(body):
    words = body.split(maxsplit=1)
    return bool(words) and words[0] == "/bench"


def parse_command(body):
    """The command in a comment, or None for other comments."""
    if not is_command(body):
        return None
    line = body.strip()
    if len(line) > 4096 or "\n" in line or "\r" in line:
        raise ValueError("use one command line")
    # Intermixed, so names may come before and after options.
    args = PARSER.parse_intermixed_args(line.split()[1:])
    names = list(dict.fromkeys(args.examples or SUITE["defaults"]))
    if len(names) > MAX_EXAMPLES:
        raise ValueError(f"at most {MAX_EXAMPLES} examples per request")
    sizes = None if args.sizes is None else dict(args.sizes)
    if sizes is not None and len(sizes) != len(args.sizes):
        raise ValueError("a size is given twice")
    return Command(args.mode, names, args.base, args.head, sizes)


class Unauthorized(ValueError):
    """The commenter may not start benchmarks; they get a reaction, not a reply."""


def select_revisions(api, command, pr, default_branch):
    base = (pr["base"]["sha"], api.repository)
    head = (pr["head"]["sha"], pr["head"]["repo"]["full_name"])
    if command.base is None and command.head is None:
        return base, head
    main = api.api(api.repo_path(f"commits/{default_branch}"), select="{sha:.sha}")["sha"]
    if not isinstance(main, str) or not SHA.fullmatch(main):
        raise ValueError("default branch did not resolve to a commit")
    # Each permitted tip has a repository from which checkout can fetch it.
    histories = [(api.repository, main), (head[1], head[0]), (base[1], base[0])]

    def select(selector, default):
        if selector is None:
            return default
        if selector == "main":
            return main, api.repository
        if selector == "pr":
            return head
        for repository in dict.fromkeys(repo for repo, _ in histories):
            try:
                sha = api.api(f"repos/{repository}/commits/{selector}", select="{sha:.sha}")["sha"]
                break
            except subprocess.CalledProcessError:
                continue
        else:
            raise ValueError("commit could not be resolved in this repository or PR")
        if not isinstance(sha, str) or not SHA.fullmatch(sha):
            raise ValueError("selection did not resolve to a full commit SHA")
        for repository, tip in histories:
            if sha == tip:
                return sha, repository
            try:
                compared = api.api(f"repos/{repository}/compare/{sha}...{tip}", select="{status:.status}")
            except subprocess.CalledProcessError:
                continue
            if compared["status"] in ("ahead", "identical"):
                return sha, repository
        raise ValueError("commit is outside the default branch, PR base, and this PR's history")

    return select(command.base, base), select(command.head, head)


def prepare(api, event):
    if (not event.get("issue", {}).get("pull_request") or event["comment"]["user"]["type"] != "User"
            or not is_command(event["comment"]["body"])):
        return None
    # Authorize before parsing so only writers get replies about their syntax.
    if not api.permission(event["comment"]["user"]["login"]):
        raise Unauthorized("benchmark command requires repository write access")
    parsed = parse_command(event["comment"]["body"])
    pr = api.api(api.repo_path(f"pulls/{event['issue']['number']}"))
    if pr["state"] != "open":
        raise ValueError("benchmark requires an open PR")
    base, head = select_revisions(api, parsed, pr, event["repository"]["default_branch"])
    return {
        "repository": api.repository, "pr": pr["number"], "comment_id": event["comment"]["id"],
        "mode": parsed.mode, "examples": parsed.examples, "sizes": parsed.sizes,
        "selectors": {"base": parsed.base, "head": parsed.head},
        "base_sha": base[0], "head_sha": head[0],
        "base_repository": base[1], "head_repository": head[1],
        "observed_base_sha": pr["base"]["sha"], "observed_head_sha": pr["head"]["sha"],
    }


def reply(api, pr, message):
    # The message can quote the comment; a code block keeps it inert.
    text = message.replace("`", "'")
    api.comment(pr, f"Benchmark request not started:\n\n```text\n{text}\n```")


def main():
    api = GitHub()
    event = load(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes())
    try:
        request = prepare(api, event)
    except Unauthorized:
        api.react(event["comment"]["id"], "-1")
        return
    except ValueError as error:
        reply(api, event["issue"]["number"], str(error))
        return
    if request is None:
        return
    api.react(request["comment_id"], "eyes")
    output(request=json.dumps(request, sort_keys=True), pr=request["pr"], mode=request["mode"],
           base_sha=request["base_sha"], head_sha=request["head_sha"],
           base_repository=request["base_repository"], head_repository=request["head_repository"])


if __name__ == "__main__":
    main()
