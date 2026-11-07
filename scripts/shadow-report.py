#!/usr/bin/env python3
# Summarizes a simp shadow's log (SLC_SHADOW=rsimp, slc/proof/src/shadow.rs):
# per way of proof (rsimp, types, rsimp+arith, failed, `-` = a program
# path's simp), the calls and the time of the untrusted attempt and of
# simp; the attempts' time distribution; the files with the most time.
#
#   scripts/shadow-report.py LOG [--files N] [--failed N]
#
# --failed N: N sample goals simp proves and the attempt does not.
import collections
import random
import sys

args = sys.argv[1:]
log = args[0]
nfiles = int(args[args.index("--files") + 1]) if "--files" in args else 10
nfailed = int(args[args.index("--failed") + 1]) if "--failed" in args else 0

rows = []
f = None
for line in open(log):
    line = line.rstrip("\n")
    if line.startswith("tidy-file\t"):
        f = line.split("\t")[1]
    elif line.startswith("shadow-r\t"):
        p = line.split("\t")
        rows.append({"file": f, "line": int(p[1]), "call": int(p[2]), "simp": float(p[3]), "by": p[4], "t": float(p[5]), "goal": p[6]})

by = collections.defaultdict(lambda: [0, 0.0, 0.0])
for r in rows:
    b = by[r["by"]]
    b[0] += 1
    b[1] += r["t"]
    b[2] += r["simp"]
print("%-12s %7s %12s %10s" % ("by", "calls", "untrusted s", "simp s"))
for k, (n, t, s) in sorted(by.items(), key=lambda x: -x[1][0]):
    print("%-12s %7d %12.1f %10.1f" % (k, n, t, s))

ok = sorted(r["t"] for r in rows if r["by"] not in ("-", "failed"))
if ok:
    q = lambda x: ok[min(len(ok) - 1, int(len(ok) * x))]
    print("proven attempts: median %.4f s, p90 %.4f, p99 %.4f, max %.4f" % (q(0.5), q(0.9), q(0.99), ok[-1]))

per = collections.defaultdict(lambda: [0, 0.0])
for r in rows:
    if r["by"] not in ("-", "failed"):
        per[r["file"]][0] += 1
        per[r["file"]][1] += r["t"]
print("files by the proven attempts' time:")
for k, (n, t) in sorted(per.items(), key=lambda x: -x[1][1])[:nfiles]:
    print("  %7.1f s %5d %s" % (t, n, k))

if nfailed:
    fails = [r for r in rows if r["by"] == "failed"]
    random.seed(1)
    print("failed (sample):")
    for r in random.sample(fails, min(nfailed, len(fails))):
        print("  %s:%d  %s" % (r["file"], r["line"], r["goal"][:150]))
