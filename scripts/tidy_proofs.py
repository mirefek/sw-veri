#!/usr/bin/env python3
"""Tidy hand-written proofs (a mechanical rewrite, checked afterwards):

- `assume h: phi` where phi is exactly the goal's next premise becomes
  `assume h` (the checker reports these: SLC_TIDY=1 slc kernel-check
  --no-cache ...);
- consecutive name-only `assume` lines at one indentation merge into one
  (`assume h1 h2 h3`), as do consecutive `fix x` lines (`fix x y z`).

Usage:
  SLC_TIDY=1 slc/target/release/slc kernel-check --no-cache FILES... 2> report.txt
  scripts/tidy_proofs.py report.txt
Then check again. Generated certificates (*_tr.core) and files outside
core/ and proofs/ are left alone.
"""

import re
import sys
from collections import defaultdict

ASSUME = re.compile(r"^(\s*)assume ([A-Za-z0-9_]+):")
NAMES = re.compile(r"^(\s*)(assume|fix) ([A-Za-z0-9_]+(?: [A-Za-z0-9_]+)*)\s*$")


def indent(line):
    return len(line) - len(line.lstrip(" "))


def tidy(lines, redundant):
    # 1. redundant `assume h: phi` (with phi's continuation lines) -> `assume h`
    out = []
    i = 0
    while i < len(lines):
        m = ASSUME.match(lines[i])
        if m and (i + 1) in redundant:
            ind = indent(lines[i])
            j = i + 1
            # continuation lines: indented deeper than the step
            while j < len(lines) and lines[j].strip() and indent(lines[j]) > ind:
                j += 1
            out.append(f"{m.group(1)}assume {m.group(2)}\n")
            i = j
        else:
            out.append(lines[i])
            i += 1
    # 2. merge runs of name-only `assume` / `fix` lines at one indentation
    merged = []
    for line in out:
        m = NAMES.match(line.rstrip("\n"))
        if m and merged:
            p = NAMES.match(merged[-1].rstrip("\n"))
            if p and p.group(1) == m.group(1) and p.group(2) == m.group(2):
                merged[-1] = f"{p.group(1)}{p.group(2)} {p.group(3)} {m.group(3)}\n"
                continue
        merged.append(line)
    return merged


def main():
    reports = defaultdict(set)
    files = []
    cur = None
    for line in open(sys.argv[1]):
        parts = line.rstrip("\n").split("\t")
        if parts[0] == "tidy-file":
            cur = parts[1]
            files.append(cur)
        elif parts[0] == "tidy-assume" and cur is not None:
            reports[cur].add(int(parts[1]))
    for f in files:
        if not (f.startswith("core/") or f.startswith("proofs/")) or f.endswith("_tr.core"):
            continue
        lines = open(f).readlines()
        new = tidy(lines, reports[f])
        if new != lines:
            open(f, "w").writelines(new)
            print(f"{f}: {len(lines)} -> {len(new)} lines")


if __name__ == "__main__":
    main()
