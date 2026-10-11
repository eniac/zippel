#!/usr/bin/env python3
"""Summarize dhat heap profiles written by `bench_all --features dhat`.

For each profile, prints the bytes live at the global peak (t-gmax) grouped
by the innermost frame in our own code: zippel's crates, the benchmark
harness, or a vendored `*_upstream` baseline. Allocator, std, arkworks and
rayon frames are skipped, so a buffer allocated by `Vec::with_capacity`
inside an arkworks call made from `backend/src/values.rs` is charged to
that line of `values.rs`. A site with no own frame at all (typically
arkworks scratch allocated on a rayon pool thread, whose stack has lost the
caller) is named by its first non-plumbing frame, marked with `~`.

With `--total`, sites are ranked by the bytes and blocks they allocated over
the whole run instead: churn that never shows at the peak. With `--diff`,
two profiles (say, before and after a change) are compared site by site at
their peaks, largest increases first.

    benchmarks/dhat_top.py dhat/*.json            # top 15 sites per profile
    benchmarks/dhat_top.py -n 30 -d 3 dhat/00-*.json   # 30 sites, 3 own frames each
    benchmarks/dhat_top.py --total dhat/00-*.json      # by total bytes allocated
    benchmarks/dhat_top.py --diff before.json after.json   # change at the peak
"""

import argparse
import json
import re
import sys

FRAME = re.compile(r"^0x[0-9a-f]+: (.*) \(([^()]*):(\d+):\d+\)$")
OWN = re.compile(
    r"^(backend|runtime|graph|lang|share|analyses|zippel)/src/"
    r"|^src/(eval|[a-z0-9_]+_upstream)/"
    r"|^[a-z0-9_]+_upstream/"
    r"|^benchmarks/src/(?!lib\.rs)"
)
# Std, allocator and rayon plumbing: skipped when naming a site that has no
# own frame (e.g. arkworks MSM scratch allocated on a rayon pool thread).
PLUMBING = re.compile(
    r"^(alloc|core|std|sys)/|^src/(raw_vec|vec|slice|iter|join|thread_pool|ops|panic|alloc|boxed)/"
    r"|^(iter|slice)/|^rayon(-core)?-|^dhat-|^benchmarks/src/lib\.rs|^\?\?\?"
)


def own_frames(ftbl, fs):
    """Own-code frames of one allocation stack, innermost first."""
    out = []
    for i in fs:
        m = FRAME.match(ftbl[i])
        if m and OWN.search(m.group(2)):
            func = re.sub(r"<.*", "", m.group(1))
            out.append(f"{func} ({m.group(2)}:{m.group(3)})")
    return out


def foreign_frame(ftbl, fs):
    """First non-plumbing frame, for a stack with no own frame."""
    for i in fs:
        m = FRAME.match(ftbl[i])
        if m and not PLUMBING.search(m.group(2)):
            func = re.sub(r"<.*", "", m.group(1))
            return f"~{func} ({m.group(2)}:{m.group(3)})"
    return "<no own frame>"


def mib(b):
    return f"{b / 2**20:9.2f}"


def sites(path, depth, field):
    """Bytes and blocks per site for `field`: "g" (live at t-gmax) or "t"
    (allocated over the whole run). Returns (total bytes, {site: [bytes, blocks]})."""
    d = json.load(open(path))
    ftbl, pps = d["ftbl"], d["pps"]
    total = sum(p[field + "b"] for p in pps)
    out = {}
    for p in pps:
        if not p[field + "b"]:
            continue
        key = tuple(own_frames(ftbl, p["fs"])[:depth]) or (foreign_frame(ftbl, p["fs"]),)
        s = out.setdefault(key, [0, 0])
        s[0] += p[field + "b"]
        s[1] += p[field + "bk"]
    return total, out


def print_site(key):
    print(f"  {key[0]}")
    for f in key[1:]:
        print(f"{'':6}<- {f}")


def report(path, top, depth, field):
    total, by_site = sites(path, depth, field)
    print(f"== {path}")
    what = "at t-gmax" if field == "g" else "allocated in total"
    print(f"   {what}: {mib(total).strip()} MiB")
    for key, (b, n) in sorted(by_site.items(), key=lambda kv: -kv[1][0])[:top]:
        print(f"{mib(b)} MiB {100 * b / max(total, 1):5.1f}% {n:7d} blk  {key[0]}")
        for f in key[1:]:
            print(f"{'':36}<- {f}")
    print()


def diff(before, after, top, depth):
    tb, b = sites(before, depth, "g")
    ta, a = sites(after, depth, "g")
    # KiB for small profiles (a verifier's peak is often under 1 MiB).
    scale, unit = (2**10, "KiB") if max(tb, ta) < 16 * 2**20 else (2**20, "MiB")
    fmt = lambda x: f"{x / scale:9.2f}"  # noqa: E731
    print(f"== {before} -> {after}")
    print(f"   at t-gmax: {fmt(tb).strip()} -> {fmt(ta).strip()} {unit}")
    change = {k: a.get(k, [0, 0])[0] - b.get(k, [0, 0])[0] for k in set(a) | set(b)}
    ranked = sorted((k for k in change if change[k]), key=lambda k: -change[k])
    for title, keys in (("increases", ranked[:top]), ("decreases", ranked[::-1][:top])):
        keys = [k for k in keys if (change[k] > 0) == (title == "increases")]
        if not keys:
            continue
        print(f"   {title}:")
        for k in keys:
            was, now = b.get(k, [0, 0])[0], a.get(k, [0, 0])[0]
            print(f"{fmt(was)} -> {fmt(now).strip()} {unit} ({change[k] / scale:+.2f})", end="")
            print_site(k)
    print()


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("files", nargs="+")
    ap.add_argument("-n", type=int, default=15, help="sites per profile")
    ap.add_argument("-d", type=int, default=1, help="own frames per site")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument(
        "--total", action="store_true", help="rank by bytes allocated over the run"
    )
    mode.add_argument(
        "--diff", action="store_true", help="compare two profiles at their peaks"
    )
    a = ap.parse_args()
    if a.diff:
        if len(a.files) != 2:
            ap.error("--diff takes exactly two profiles: BEFORE AFTER")
        diff(a.files[0], a.files[1], a.n, a.d)
        return
    for f in a.files:
        report(f, a.n, a.d, "t" if a.total else "g")


if __name__ == "__main__":
    sys.exit(main())
