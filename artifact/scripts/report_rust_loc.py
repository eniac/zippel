#!/usr/bin/env python3
"""Count Zippel's Rust source lines per component (Section 8, Implementation:
"Zippel is written in ~110K lines of Rust...").

A line counts if it still holds code once comments are removed: `//`,
`///`, `//!` and (nested) `/* */` comments do not count, nor do blank
lines; string, raw-string and char literals are lexed so comment markers
inside them are not mistaken for comments.

Test code is reported on its own row instead of in its component:
  - items marked `#[test]` or `#[cfg(test)]` (and `#[cfg(all(test, ...))]`),
  - files declared through such an item (`#[cfg(test)] mod tests;`),
  - files under a `tests/` directory, and `tests.rs` files.

Code vendored from other projects as benchmark baselines
(benchmarks/src/*_upstream/) is not Zippel's; it is reported separately
and left out of the total.

Needs no build: reads the source files directly. Run from anywhere:

    python3 artifact/scripts/report_rust_loc.py
"""

import os
import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

# Paper component -> top-level paths. Checked in order; first match wins.
COMPONENTS = [
    ("Parser, optimizer, and type checker", ["lang"]),
    ("Graph IR and projection", ["graph"]),
    ("Analyses", ["analyses"]),
    ("Runtime", ["runtime", "backend"]),
    ("Other library code", ["src", "share", "fmt", "check"]),
    ("Benchmarks", ["benches", "benchmarks"]),
    ("Examples", ["examples"]),
]
VENDORED = re.compile(r"^benchmarks/src/[^/]+_upstream/")
SKIP_DIRS = {"target", "output"}


# --- Rust lexing -----------------------------------------------------------

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
NUMBER = re.compile(r"[0-9][0-9A-Za-z_.]*")
RAW_STRING = re.compile(r'(?:br|cr|r)(#*)"')


def lex(src):
    """Tokens of `src` as (text, first_line, last_line), comments dropped.
    String and char literals are single tokens; other punctuation is one
    char per token, which is all the item matching below needs."""
    tokens = []
    i, line, n = 0, 1, len(src)

    def push(start, start_line):
        tokens.append((src[start:i], start_line, line))

    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
        elif c.isspace():
            i += 1
        elif src.startswith("//", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src.startswith("/*", i):
            depth = 0
            while i < n:
                if src.startswith("/*", i):
                    depth += 1
                    i += 2
                elif src.startswith("*/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    line += src[i] == "\n"
                    i += 1
        elif (m := RAW_STRING.match(src, i)) and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")):
            start, start_line = i, line
            close = '"' + m.group(1)
            j = src.find(close, m.end())
            j = n if j < 0 else j + len(close)
            line += src.count("\n", i, j)
            i = j
            push(start, start_line)
        elif c == '"' or (c in "bc" and src.startswith('"', i + 1)):
            start, start_line = i, line
            i = src.index('"', i) + 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    i += 1
                line += src[i] == "\n"
                i += 1
            i += 1
            push(start, start_line)
        elif c == "'" or (c == "b" and src.startswith("'", i + 1)):
            start, start_line = i, line
            j = src.index("'", i) + 1
            if j < n and src[j] == "\\":  # escaped char literal
                j += 2
                while j < n and src[j] != "'":
                    j += 1
                i = j + 1
            elif j + 1 < n and src[j + 1] == "'":  # 'x'
                i = j + 2
            else:  # lifetime or label: 'a
                m = IDENT.match(src, j)
                i = m.end() if m else j
            push(start, start_line)
        elif m := IDENT.match(src, i):
            tokens.append((m.group(), line, line))
            i = m.end()
        elif m := NUMBER.match(src, i):
            tokens.append((m.group(), line, line))
            i = m.end()
        else:
            tokens.append((c, line, line))
            i += 1
    return tokens


def cfg_args(tokens):
    """Top-level comma-separated arguments of a `(...)` token list."""
    args, cur, depth = [], [], 0
    for t in tokens:
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
        if t == "," and depth == 0:
            args.append(cur)
            cur = []
        else:
            cur.append(t)
    return args + [cur] if cur else args


def is_test_attr(body):
    """Whether attribute tokens (between `#[` and `]`) mark test code:
    `#[test]`, `#[some::path::test]` (e.g. `#[tokio::test]`),
    `#[cfg(test)]`, or `#[cfg(all(..., test, ...))]`."""
    if body == ["test"] or body[-3:] == [":", ":", "test"]:
        return True
    if body[:2] == ["cfg", "("]:
        inner = body[2:-1]
        if inner == ["test"]:
            return True
        if inner[:2] == ["all", "("]:
            return ["test"] in cfg_args(inner[2:-1])
    return False


# First tokens an item (or `let` statement) can start with, after its
# attributes. A test attribute anywhere else (a struct field, enum
# variant, match arm, ...) is not supported and is reported, rather than
# guessed at.
ITEM_START = {
    "pub", "unsafe", "async", "const", "extern", "default", "fn", "mod",
    "use", "struct", "enum", "union", "trait", "type", "static", "impl",
    "macro_rules", "let",
}


def attr_end(tokens, k):
    """Index just past the attribute whose `#` is at k (outer or inner)."""
    j = k + 1 + (tokens[k + 1][0] == "!")
    depth = 0
    while j < len(tokens):
        t = tokens[j][0]
        if t == "[":
            depth += 1
        elif t == "]":
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return j


def item_end(tokens, k):
    """Index just past the item starting at k: its first `;` at depth 0,
    or the `}` matching its first `{` at depth 0."""
    depth = 0
    j = k
    while j < len(tokens):
        t = tokens[j][0]
        if t in "([":
            depth += 1
        elif t in ")]":
            depth -= 1
        elif t == ";" and depth == 0:
            return j + 1
        elif t == "{":
            if depth == 0:
                braces = 0
                while j < len(tokens):
                    if tokens[j][0] == "{":
                        braces += 1
                    elif tokens[j][0] == "}":
                        braces -= 1
                        if braces == 0:
                            # `use a::{b, c};` ends at the `;`, not the `}`.
                            if j + 1 < len(tokens) and tokens[j + 1][0] == ";":
                                return j + 2
                            return j + 1
                    j += 1
                return j
            depth += 1
        elif t == "}":
            depth -= 1
        j += 1
    return j


def split_tests(tokens):
    """(code_tokens, test_tokens, test_mod_names) for one file. A file
    whose inner attribute is `#![cfg(test)]` is all test code."""
    code, test, mods = [], [], []
    k = 0
    while k < len(tokens):
        if tokens[k][0] == "#" and k + 1 < len(tokens) and tokens[k + 1][0] in ("[", "!"):
            end = attr_end(tokens, k)
            inner = tokens[k + 1][0] == "!"
            body = [t[0] for t in tokens[k + 2 + inner:end - 1]]
            if is_test_attr(body):
                if inner:
                    return [], tokens, []
                stop = end
                while stop < len(tokens) and tokens[stop][0] == "#":  # more attributes
                    stop = attr_end(tokens, stop)
                first = tokens[stop][0] if stop < len(tokens) else ""
                macro = stop + 1 < len(tokens) and tokens[stop + 1][0] == "!"
                if first not in ITEM_START and not macro:
                    raise ValueError(
                        f"line {tokens[k][1]}: test attribute on something other "
                        f"than an item (`{first}`); not supported")
                stop = item_end(tokens, stop)
                item = tokens[k:stop]
                words = [t[0] for t in item[end - k:]]
                if "mod" in words and words[-1] == ";":
                    mods.append(words[words.index("mod") + 1])
                test.extend(item)
                k = stop
                continue
            code.extend(tokens[k:end])
            k = end
            continue
        code.append(tokens[k])
        k += 1
    return code, test, mods


def lines_of(tokens):
    covered = set()
    for _, first, last in tokens:
        covered.update(range(first, last + 1))
    return len(covered)


# --- Files -----------------------------------------------------------------

def rust_files():
    for root, dirs, files in os.walk(REPO):
        dirs[:] = sorted(d for d in dirs if not d.startswith(".") and d not in SKIP_DIRS)
        for f in sorted(files):
            if f.endswith(".rs"):
                yield Path(root) / f


def module_dir(path):
    """Directory holding the files of `mod x;` declared in `path`."""
    if path.name in ("mod.rs", "lib.rs", "main.rs"):
        return path.parent
    return path.parent / path.stem


def component(rel):
    for name, roots in COMPONENTS:
        if any(rel == r or rel.startswith(r + "/") for r in roots):
            return name
    return "Other library code"


def main():
    files = list(rust_files())
    parsed = {}
    test_paths = set()
    for path in files:
        code, test, mods = split_tests(lex(path.read_text(encoding="utf-8")))
        parsed[path] = (code, test)
        for name in mods:
            d = module_dir(path)
            test_paths.update([d / f"{name}.rs", d / name])

    counts = {name: 0 for name, _ in COMPONENTS}
    tests = vendored = 0
    for path in files:
        rel = path.relative_to(REPO).as_posix()
        code, test = parsed[path]
        if VENDORED.match(rel):
            vendored += lines_of(code + test)
            continue
        is_test_file = (
            "tests" in Path(rel).parts[:-1]
            or path.name == "tests.rs"
            or any(path == t or t in path.parents for t in test_paths)
        )
        if is_test_file:
            tests += lines_of(code + test)
        else:
            # A line holding both code and test code counts once, as test.
            test_lines = lines_of(test)
            counts[component(rel)] += lines_of(code + test) - test_lines
            tests += test_lines

    total = sum(counts.values()) + tests
    print("| Component | Paths | Lines |")
    print("|---|---|---|")
    for name, roots in COMPONENTS:
        paths = ", ".join(f"`{r}/`" for r in roots)
        print(f"| {name} | {paths} | {counts[name]:,} |")
    print(f"| Tests | test items and test files in every path above | {tests:,} |")
    print(f"| **Total** | | **{total:,}** |")
    print()
    print(f"Not counted: {vendored:,} lines vendored from other projects as "
          "benchmark baselines (benchmarks/src/*_upstream/).")


if __name__ == "__main__":
    main()
