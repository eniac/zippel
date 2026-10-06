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

    benchmarks/dhat_top.py dhat/*.json            # top 15 sites per profile
    benchmarks/dhat_top.py -n 30 -d 3 dhat/00-*.json   # 30 sites, 3 own frames each
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


def report(path, top, depth):
    d = json.load(open(path))
    ftbl, pps = d["ftbl"], d["pps"]
    total = sum(p["gb"] for p in pps)
    sites = {}
    for p in pps:
        if not p["gb"]:
            continue
        key = tuple(own_frames(ftbl, p["fs"])[:depth]) or (foreign_frame(ftbl, p["fs"]),)
        s = sites.setdefault(key, [0, 0])
        s[0] += p["gb"]
        s[1] += p["gbk"]
    print(f"== {path}")
    print(f"   at t-gmax: {mib(total).strip()} MiB live")
    for key, (b, n) in sorted(sites.items(), key=lambda kv: -kv[1][0])[:top]:
        print(f"{mib(b)} MiB {100 * b / max(total, 1):5.1f}% {n:7d} blk  {key[0]}")
        for f in key[1:]:
            print(f"{'':36}<- {f}")
    print()


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("files", nargs="+")
    ap.add_argument("-n", type=int, default=15, help="sites per profile")
    ap.add_argument("-d", type=int, default=1, help="own frames per site")
    a = ap.parse_args()
    for f in a.files:
        report(f, a.n, a.d)


if __name__ == "__main__":
    sys.exit(main())
