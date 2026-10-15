#!/usr/bin/env python3
"""Moves declarations a file uses before their place up, just above their
first use (a stable reordering: nothing else moves). A declaration takes
its comment lines along (those right above it). Names given an earlier
`lemma` are not moved: that is what an open lemma is for.

Usage:
  scripts/reorder.py FILE...      reorder in place, the moves listed
  scripts/reorder.py -n FILE...   only list the moves

Then check again (a theorem moved above a `simp` line sees fewer rewrite
rules; a cycle -- two declarations using each other -- is reported, not
resolved: one of them needs a `lemma`).
"""

import re
import sys

DECL = re.compile(r"^(theorem|lemma|claim|def|abbrev|const|axiom|refines|c1|simp|irreducible|mem_view|mem_frame|mem_closure|bit_rule)\s+([A-Za-z_][A-Za-z0-9_.']*)")
# (registering an existing name: defining none)
REGISTERS = {"simp", "irreducible", "mem_view", "mem_frame", "mem_closure", "bit_rule"}
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def chunks(lines):
    """the head (before the first declaration) and the declarations: (kind,
    name, lines), each with the comment lines right above it"""
    starts = []
    for i, l in enumerate(lines):
        if DECL.match(l):
            s = i
            while s > 0 and lines[s - 1].startswith("//") and (not starts or s - 1 >= starts[-1]):
                s -= 1
            starts.append(s)
    head = lines[: starts[0]] if starts else lines
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        body = lines[s:e]
        m = next(DECL.match(l) for l in body if DECL.match(l))
        out.append((m.group(1), m.group(2), body))
    return head, out


def reorder(text):
    lines = text.split("\n")
    head, cs = chunks(lines)
    first = {}
    for i, (kind, name, _) in enumerate(cs):
        if kind not in REGISTERS:
            first.setdefault(name, i)
    order, state, moves, cycles = [], {}, [], []

    def place(i, user):
        if state.get(i) == "done":
            return
        if state.get(i) == "busy":
            cycles.append(cs[i][1])
            return
        state[i] = "busy"
        kind, name, body = cs[i]
        for t in TOKEN.findall("\n".join(l for l in body if not l.lstrip().startswith("//"))):
            j = first.get(t)
            if j is not None and j > i and t != name:
                place(j, name)
        if user is not None and i > first.get(user, -1):
            moves.append((name, user))
        state[i] = "done"
        order.append(i)

    for i in range(len(cs)):
        place(i, None)
    new = head + [l for i in order for l in cs[i][2]]
    return "\n".join(new), moves, cycles


def main(argv):
    dry = "-n" in argv
    for f in [a for a in argv if a != "-n"]:
        text = open(f).read()
        new, moves, cycles = reorder(text)
        for name, user in moves:
            print(f"{f}: `{name}` moved above `{user}`")
        for name in cycles:
            print(f"{f}: `{name}` is in a cycle: declare one of them first as a `lemma`")
        if not dry and new != text:
            open(f, "w").write(new)


if __name__ == "__main__":
    main(sys.argv[1:])
