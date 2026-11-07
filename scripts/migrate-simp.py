#!/usr/bin/env python3
# Moves simp call sites to rsimp, by a simp shadow's log (SLC_SHADOW=rsimp,
# slc/proof/src/shadow.rs): a proof step whose every simp goal call
# rsimp proved (rsimp, types or rsimp+arith; none a program path's) has
# its `simp(` written `rsimp(` -- on the step's line, when that line holds
# all of the step's calls. Then each changed file is checked
# (scripts/check.sh FILE, with the caches) and a step the checker rejects
# is put back, until the file checks.
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

steps = collections.defaultdict(list)  # (file, line) -> [by]
f = None
for line in open(log):
    line = line.rstrip("\n")
    if line.startswith("tidy-file\t"):
        f = line.split("\t")[1]
    elif line.startswith("shadow-r\t"):
        p = line.split("\t")
        # (a call the attempt proves much slower than simp: not moved --
        # over 10 times simp's time and 20 ms)
        by = p[4]
        if by in ("rsimp", "types", "rsimp+arith") and float(p[5]) > max(10 * float(p[3]), 0.02):
            by = "slow"
        steps[(f, int(p[1]))].append(by)

SIMP = re.compile(r"(?<![A-Za-z0-9_.])simp\(")
todo = collections.defaultdict(list)  # file -> [line]
for (f, l), bys in steps.items():
    if f is None or not f.startswith("proofs/") and not f.startswith("core/"):
        continue
    if only and only not in f:
        continue
    if all(b in GOOD for b in bys):
        todo[f].append(l)


def lines_of(f):
    return open(f).read().split("\n")


def write(f, ls):
    open(f, "w").write("\n".join(ls))


def check(f):
    r = subprocess.run(["scripts/check.sh", f], capture_output=True, text=True)
    out = r.stdout + r.stderr
    m = re.search(r"error: " + re.escape(f) + r": line (\d+)[^:]*: proof of `[^`]*`, line (\d+)", out)
    if "ok: all declarations" in out and "error" not in out:
        return None
    if m:
        return int(m.group(2))
    return -1


total = 0
for f in sorted(todo):
    ls = lines_of(f)
    changed = []
    for l in sorted(set(todo[f])):
        i = l - 1
        if i >= len(ls):
            continue
        n = len(SIMP.findall(ls[i]))
        if n == 0 or n != len(steps[(f, l)]):
            continue
        ls[i] = SIMP.sub("rsimp(", ls[i])
        changed.append(l)
    if not changed:
        continue
    print("%s: %d steps" % (f, len(changed)), flush=True)
    if dry:
        total += len(changed)
        continue
    orig = lines_of(f)
    write(f, ls)
    # (a rejected step put back, the file checked again)
    while True:
        bad = check(f)
        if bad is None:
            break
        if bad in changed:
            ls[bad - 1] = orig[bad - 1]
            changed.remove(bad)
            write(f, ls)
            print("  line %d put back" % bad, flush=True)
            continue
        # (an error elsewhere: the whole file put back)
        print("  an error not at a changed step (%s): the file put back" % bad, flush=True)
        write(f, orig)
        changed = []
        break
    total += len(changed)
print("steps moved: %d" % total)
