#!/usr/bin/env python3
# Moves simp call sites to rsimp, by a simp shadow's log (SLC_SHADOW=rsimp,
# slc/proof/src/shadow.rs). Each logged call has its text as written (up
# to whitespace); a call rsimp proved (rsimp, types or rsimp+arith -- not
# much slower than simp) is found in its step (the step's line and its
# continuation lines, more indented) and written `rsimp(`, when every
# occurrence there of its text is a proven call (none of the calls rsimp
# did not prove has it). Then each changed file is checked (scripts/check.sh FILE, with the
# caches) and a step the checker rejects is put back, until the file
# checks.
#
#   scripts/migrate-simp.py LOG [--only PATH-SUBSTRING] [--dry]
import collections
import re
import subprocess
import sys

args = sys.argv[1:]
log = args[0]
only = args[args.index("--only") + 1] if "--only" in args else None
dry = "--dry" in args
GOOD = {"rsimp", "types", "rsimp+arith"}

calls = collections.defaultdict(list)  # (file, line) -> [(by, text)]
f = None
for line in open(log):
    line = line.rstrip("\n")
    if line.startswith("tidy-file\t"):
        f = line.split("\t")[1]
    elif line.startswith("shadow-r\t"):
        p = line.split("\t")
        if len(p) < 8:
            continue
        by = p[4]
        # (much slower than simp: over 10 times its time and 20 ms)
        if by in GOOD and float(p[5]) > max(10 * float(p[3]), 0.02):
            by = "slow"
        calls[(f, int(p[1]))].append((by, p[7]))

SIMP = re.compile(r"(?<![A-Za-z0-9_.])simp\(")
norm = lambda s: re.sub(r"\s+", "", s)


def call_at(text, i):
    """the balanced call starting at text[i] (`simp(`), or None"""
    d = 0
    for j in range(i, len(text)):
        c = text[j]
        if c in "([{":
            d += 1
        elif c in ")]}":
            d -= 1
            if d == 0:
                return text[i : j + 1]
    return None


def renamed(call):
    """`simp(..)` as `rsimp(..)`, its `keep(..)` arguments dropped (rsimp
    unfolds only what it is given)"""
    inner = call[len("simp(") : -1]
    parts, d, cur = [], 0, ""
    for c in inner:
        if c in "([{":
            d += 1
        elif c in ")]}":
            d -= 1
        if c == "," and d == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip() or parts:
        parts.append(cur)
    parts = [p for p in parts if not p.strip().startswith("keep(")]
    return "rsimp(" + ",".join(parts).strip() + ")" if parts else "rsimp()"


def region(ls, i):
    """the step's lines: line i and the more-indented ones after it"""
    ind = len(ls[i]) - len(ls[i].lstrip())
    j = i + 1
    while j < len(ls) and ls[j].strip() and len(ls[j]) - len(ls[j].lstrip()) > ind:
        j += 1
    return range(i, j)


def check(f):
    r = subprocess.run(["scripts/check.sh", f], capture_output=True, text=True)
    out = r.stdout + r.stderr
    if "ok: all declarations" in out and "error" not in out:
        return None
    m = re.search(r"error: " + re.escape(f) + r": line (\d+)[^:]*: proof of `[^`]*`, line (\d+)", out)
    return int(m.group(2)) if m else -1


byfile = collections.defaultdict(list)
for (f, l), cs in calls.items():
    if f and (f.startswith("proofs/") or f.startswith("core/")) and (not only or only in f):
        byfile[f].append((l, cs))

total = 0
for f in sorted(byfile):
    ls = open(f).read().split("\n")
    orig = list(ls)
    # (line in the file -> the step's first line, for putting back)
    moved = {}
    for l, cs in sorted(byfile[f]):
        if l - 1 >= len(ls):
            continue
        good = collections.Counter(norm(t) for b, t in cs if b in GOOD)
        bad = set(norm(t) for b, t in cs if b not in GOOD)
        lines = region(ls, l - 1)
        # (the occurrences of each proven call's text in the step)
        occ = collections.defaultdict(list)
        for i in lines:
            for m in SIMP.finditer(ls[i]):
                c = call_at(ls[i], m.start())
                if c is not None:
                    occ[norm(c)].append((i, m.start(), c))
        edits = []
        # (a text whose every occurrence in the step is a proven call: all
        # renamed -- `simp()` twice in one step, both proven)
        for t, n in good.items():
            if t in bad or len(occ.get(t, [])) != n:
                continue
            edits.extend(occ[t])
        # (right to left within a line: the offsets stay valid)
        for i, col, c in sorted(edits, key=lambda x: (x[0], -x[1])):
            ls[i] = ls[i][:col] + renamed(c) + ls[i][col + len(c) :]
            moved.setdefault(i + 1, l)
    if not moved:
        continue
    print("%s: %d lines" % (f, len(moved)), flush=True)
    if dry:
        total += len(moved)
        continue
    open(f, "w").write("\n".join(ls))
    while True:
        badl = check(f)
        if badl is None:
            break
        # (the rejected step's changed lines put back)
        step = moved.get(badl, badl if badl in moved.values() else None)
        back = [i for i, s in moved.items() if s == step] if step is not None else []
        if not back:
            print("  an error not at a changed step (%s): the file put back" % badl, flush=True)
            open(f, "w").write("\n".join(orig))
            moved = {}
            break
        for i in back:
            ls[i - 1] = orig[i - 1]
            del moved[i]
        open(f, "w").write("\n".join(ls))
        print("  step at line %d put back" % step, flush=True)
    total += len(moved)
print("lines changed: %d" % total)
