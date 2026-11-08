#!/usr/bin/env python3
# Counts the proof steps by their shape: the step's command and the goal
# rule or fact form it ends with (`have h: .. by simp(..)` -> `have/by
# simp`), over the proof files. For finding the glue that recurs.
#
#   scripts/step-shapes.py [N] [FILES..]   (default: proofs/ and core/)
import collections
import glob
import re
import sys

args = sys.argv[1:]
n = int(args[0]) if args and args[0].isdigit() else 40
files = [a for a in args if not a.isdigit()] or glob.glob("proofs/**/*.core", recursive=True) + glob.glob("core/*.core")

shapes = collections.Counter()
lines_of = collections.Counter()
RULE = re.compile(r"\bby\s+([a-z_][a-z_0-9.]*)\(")
FORM = re.compile(r":=\s*([a-z_][a-z_0-9.]*)\(")
for f in files:
    in_proof = False
    for line in open(f):
        s = line.strip()
        if s == "proof" or s.endswith(" proof"):
            in_proof = True
        if not in_proof or not s or s.startswith("//"):
            continue
        if s == "qed":
            continue
        cmd = s.split()[0]
        m = RULE.search(s) or FORM.search(s)
        key = cmd + ("/" + m.group(1) if m else "")
        shapes[key] += 1
        lines_of[f] += 1
total = sum(shapes.values())
print("proof lines", total)
for k, v in shapes.most_common(n):
    print("%7d %5.1f%% %s" % (v, 100.0 * v / total, k))
print("== files with the most proof lines")
for k, v in lines_of.most_common(12):
    print("%7d %s" % (v, k))
