#!/usr/bin/env python3
# Summarizes scripts/sample-stacks.py's samples: the innermost slc frame
# of each sample (where the time is spent) and the functions on the
# stacks (inclusive: what the time is spent under).
#
#   scripts/sample-report.py FILE [N]
import collections
import sys

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
