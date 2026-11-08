#!/usr/bin/env python3
# Summarizes scripts/sample-stacks.py's samples: the innermost slc frame
# of each sample (where the time is spent) and the functions on the
# stacks (inclusive: what the time is spent under).
#
#   scripts/sample-report.py FILE [N] [--within NAME] [--callers NAME]
#
# --within NAME: only the samples with a frame whose function's name
# contains NAME (e.g. untrusted_simp)
# --callers NAME: also the slc frames calling NAME's innermost frame (the
# first three of them, as call paths)
import collections
import sys


def opt(name):
    if name not in sys.argv:
        return None
    i = sys.argv.index(name)
    v = sys.argv[i + 1]
    del sys.argv[i : i + 2]
    return v


within = opt("--within")
callers = opt("--callers")

samples, cur = [], []
for line in open(sys.argv[1]):
    line = line.rstrip("\n")
    if line == "=== sample":
        if cur:
            samples.append(cur)
        cur = []
    else:
        cur.append(line)
if cur:
    samples.append(cur)
# (a thread waiting to join another: not working)
samples = [s for s in samples if not any("Thread>::join" in f for f in s[:6])]
if within:
    samples = [s for s in samples if any(within in f.partition(" ")[0] for f in s)]
n = int(sys.argv[2]) if len(sys.argv) > 2 else 30
print("samples", len(samples))


def ours(f):
    return ".rs:" in f and not f.startswith(("core::", "alloc::", "std::", "<alloc", "<core", "<std", "hashbrown"))


def short(f):
    name, _, loc = f.partition(" ")
    return "%s %s" % (name.split("::")[-1], loc)


inner = collections.Counter()
incl = collections.Counter()
for s in samples:
    fs = [f for f in s if ours(f)]
    if fs:
        inner[short(fs[0])] += 1
    seen = set()
    for f in fs:
        name, _, loc = f.partition(" ")
        k = "%s [%s]" % (name.split("::")[-1], loc.split(":")[0])
        if k not in seen:
            seen.add(k)
            incl[k] += 1
print("== innermost")
for k, v in inner.most_common(n):
    print("%5d %s" % (v, k))
print("== inclusive")
for k, v in incl.most_common(n):
    print("%5d %s" % (v, k))
if callers:
    paths = collections.Counter()
    for s in samples:
        fs = [f for f in s if ours(f)]
        at = next((i for i, f in enumerate(fs) if callers in f.partition(" ")[0]), None)
        if at is not None:
            paths[" <- ".join(short(f) for f in fs[at + 1 : at + 4])] += 1
    print("== callers of", callers)
    for k, v in paths.most_common(n):
        print("%5d %s" % (v, k))
