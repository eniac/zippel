"""GitHub access through `gh`, and step outputs for later jobs."""

import os
import re
import subprocess
import sys

from untrusted import MAX_JSON, dump, load


class GitHub:
    def __init__(self, repository=None):
        self.repository = repository or os.environ["GITHUB_REPOSITORY"]

    def api(self, path, method="GET", data=None, select=None):
        args = ["gh", "api", "--method", method, path]
        if select is not None:
            args += ["--jq", select]
        if data is not None:
            args += ["--input", "-"]
        result = subprocess.run(args, input=dump(data) if data is not None else None,
                                capture_output=True, timeout=30)
        if result.returncode:
            # Callers may handle the failure, but the log should say why.
            sys.stderr.write(f"gh api {method} {path}: {result.stderr.decode(errors='replace')}")
            raise subprocess.CalledProcessError(result.returncode, args, result.stdout, result.stderr)
        return load(result.stdout or b"null", limit=16 * MAX_JSON)

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
        # GitHub's login format; the login goes into a URL path.
        if not re.fullmatch(r"[A-Za-z0-9-]+", login):
            raise ValueError("invalid author")
        response = self.api(self.repo_path(f"collaborators/{login}/permission"))
        return response.get("permission") in ("admin", "maintain", "write")

    def comment(self, pr, body):
        self.api(self.repo_path(f"issues/{pr}/comments"), "POST", {"body": body})

    def react(self, comment_id, content):
        self.api(self.repo_path(f"issues/comments/{comment_id}/reactions"), "POST", {"content": content})


def output(**values):
    """Write step outputs (`GITHUB_OUTPUT`), one line each."""
    path = os.environ.get("GITHUB_OUTPUT")
    if path:
        with open(path, "a", encoding="utf-8") as stream:
            for key, value in values.items():
                text = str(value)
                if "\n" in text or "\r" in text:
                    raise ValueError("multiline output")
                stream.write(f"{key}={text}\n")
