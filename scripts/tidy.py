#!/usr/bin/env python3
"""Shorten proof files without slowing them: scripts/tidy.py [OPTIONS] FILE..

Passes, in order (each from the file as the previous pass left it):
  inst    instantiations `L[x := t]` apply infers (SLC_INST_AUDIT), and
          `mp(all_elim(L, {t}..), ..)` as `apply(L, ..)` (`*elim`)
  args    a goal rule's / apply's arguments it does without (SLC_ARG_AUDIT)
  unused  `have` steps whose names nothing after them mentions

A pass's edits are diff hunks against the file before it. All are applied;
while the file fails to check, the hunk at (or before) the error's line is
dropped. Then the file's proof time (SLC_TIMES) is compared with its time
before tidying (every pass against that one, so the slack does not add
up): a set of hunks that is slower (5% + 30 ms, a slower time measured
twice) is halved, recursively, so only edits that cost nothing stay. Every check rechecks FILE alone (the
rest from the cache); files after it are not rechecked -- run the full
check (scripts/check.sh --no-cache) before committing.

Options:
  --passes P,..   the passes (default inst,args,unused)
  --no-time       keep every hunk that checks (no timing)
  --symex         audit symex's arguments too (SLC_ARG_AUDIT=all: slow,
                  its failing trials search -- a file at a time)
  --dry           report what each pass would change, then restore the file
  -v              each check's outcome

FILE: a path in the chain (proofs/.., core/..), from the repository root.
"""
import argparse
import difflib
import os
import re
import resource
import subprocess
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MEM = 6_000_000_000  # (the checker's memory limit, bytes)
VERBOSE = False


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (MEM, MEM))


def run_check(f, extra=None):
    """FILE rechecked (the rest cached): (ok, the first error line, FILE's
    proof time, all output)"""
    env = dict(os.environ, SLC_CACHE_AS="any", SLC_RECHECK=f, SLC_TIMES="1")
    env.update(extra or {})
    r = subprocess.run(["scripts/check.sh"], cwd=ROOT, env=env, capture_output=True, text=True, preexec_fn=limit)
    out = r.stdout + r.stderr
    lines = out.split("\n")
    ok = any(l.startswith("ok:") for l in lines)
    err = next((l for l in lines if l.startswith("error")), "")
    t = None
    for l in lines:
        if l.endswith(f) and " MB " in l:
            try:
                t = float(l.split()[0].rstrip("s"))
            except ValueError:
                pass
    if VERBOSE:
        print("   check:", "ok" if ok else err[:160], f"{t}s" if t is not None else "", flush=True)
    return ok, err, (t if t is not None else 1e9), out


def err_line(err):
    """the failing step's line: the last `line N:` (not a note's `line N's`)"""
    m = re.findall(r"line (\d+):", err)
    return int(m[-1]) if m else None


# ----------------------------------------------------------------------
# text helpers


def close_of(s, i):
    """s[i] an opening bracket: its match"""
    d = 0
    for j in range(i, len(s)):
        if s[j] in "([{":
            d += 1
        elif s[j] in ")]}":
            d -= 1
            if d == 0:
                return j
    return None


def split_top(s):
    """s split at its top-level commas"""
    out, d, cur = [], 0, ""
    for c in s:
        if c in "([{":
            d += 1
        elif c in ")]}":
            d -= 1
        if c == "," and d == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


def top_args(s, i):
    """s[i] == '(': the (start, end) of its top-level arguments, and its ')'"""
    d, start, out = 0, i + 1, []
    for j in range(i, len(s)):
        c = s[j]
        if c in "([{":
            d += 1
        elif c in ")]}":
            d -= 1
            if d == 0:
                if s[start:j].strip():
                    out.append((start, j))
                return out, j
        elif c == "," and d == 1:
            out.append((start, j))
            start = j + 1
    return None, None


def ws(x):
    return re.sub(r"\s+", "", x)


# ----------------------------------------------------------------------
# passes: the file's text -> a new text


def audit(f, var, tag, val="1"):
    _, _, _, out = run_check(f, {var: val})
    return [l.split("\t") for l in out.split("\n") if l.startswith(tag + "\t")]


def pass_inst(f, lines):
    want, mps = defaultdict(set), set()
    for p in audit(f, "SLC_INST_AUDIT", "inst-audit"):
        if len(p) >= 5 and p[1].isdigit():
            want[(int(p[1]), p[3])].add(p[4])
            if p[2] == "mp":
                mps.add((int(p[1]), p[3]))
    lines = list(lines)
    for (n, name), vs in sorted(want.items()):
        for k in range(n - 1, min(n + 6, len(lines))):
            s = lines[k]
            if "*elim" in vs:
                # `mp(all_elim(L, {t}..), ..)` / `apply(all_elim(L, ..), ..)`
                m = re.search(r"(?<![\w.])(mp|apply)\(all_elim\(" + re.escape(name) + r",", s)
                if not m:
                    continue
                j = close_of(s, m.start(0) + len(m.group(1)) + 1 + len("all_elim"))
                if j is not None:
                    lines[k] = s[: m.start(0)] + "apply(" + name + s[j + 1 :]
                break
            m = re.search(r"(?<![\w.])" + re.escape(name) + r"\[", s)
            if not m:
                continue
            i = m.end() - 1
            j = close_of(s, i)
            if j is None:
                break
            if "*" in vs:
                new = s[:i] + s[j + 1 :]
            else:
                bs = [b for b in split_top(s[i + 1 : j]) if b.split(":=")[0].strip() not in vs]
                new = s[:i] + ("[" + ", ".join(bs) + "]" if bs else "") + s[j + 1 :]
            if (n, name) in mps:
                a = i - len(name)
                if not new[:a].endswith("mp("):
                    break
                new = new[: a - 3] + "apply(" + new[a:]
            lines[k] = new
            break
    return lines


SYMEX = False


def pass_args(f, lines):
    reports, seen = [], set()
    for p in audit(f, "SLC_ARG_AUDIT", "arg-audit", "all" if SYMEX else "1"):
        if len(p) >= 5 and p[1].isdigit():
            key = (int(p[1]), p[2], ws(p[3]))
            if key not in seen:
                seen.add(key)
                reports.append((*key, [int(x) for x in p[4].split(",")]))
    lines = list(lines)
    for n, rule, args, drop in reports:
        lo, hi = n - 1, min(n + 9, len(lines))
        text = "\n".join(lines[lo:hi])
        # (the first call of the rule in the step's lines with these
        # arguments)
        for m in re.finditer(r"(?<![\w.])" + re.escape(rule) + r"\(", text):
            i = m.end() - 1
            a, j = top_args(text, i)
            if a is None or ws(",".join(text[x:y] for x, y in a)) != args:
                continue
            if any(k >= len(a) for k in drop) or any("\n" in text[a[k][0] : a[k][1]] for k in drop):
                break
            if "\n" in text[i + 1 : j]:
                # (a call over lines: the trailing dropped ones from the last
                # kept one's end, each other one with its comma)
                new, ks = text, set(drop)
                t = len(a)
                while t > 0 and t - 1 in ks:
                    t -= 1
                if t < len(a):
                    px = a[t - 1][1] if t > 0 else i + 1
                    new = new[:px] + new[a[-1][1] :]
                for k in sorted((k for k in drop if k < t), reverse=True):
                    x, y = a[k]
                    xs = x + (len(new[x:y]) - len(new[x:y].lstrip(" ")))
                    new = new[:xs] + new[y + 1 :].lstrip(" ")
                if new.count("\n") != text.count("\n"):
                    break
                text = new
            else:
                kept = [text[x:y].strip() for k, (x, y) in enumerate(a) if k not in drop]
                text = text[: i + 1] + ", ".join(kept) + text[j:]
            lines[lo:hi] = text.split("\n")
            break
    return lines


def pass_unused(f, lines):
    ind = lambda l: len(l) - len(l.lstrip())

    def item_end(i):
        j = i + 1
        while j < len(lines) and not (lines[j] and not lines[j][0].isspace()):
            j += 1
        return j

    gone = set()
    for i, l in enumerate(lines):
        m = re.match(r"^(\s+)have ([\w ]+?)\s*(:=|:)", l)
        if not m:
            continue
        names = m.group(2).split()
        if not names or "_" in names:
            continue
        d = len(m.group(1))
        # (its extent: the deeper lines after it, and a `proof`'s `qed`)
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or ind(lines[j]) > d):
            j += 1
        if j < len(lines) and lines[j].strip() == "qed" and ind(lines[j]) == d:
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        # (not its block's last step)
        k = j
        while k < len(lines) and not lines[k].strip():
            k += 1
        if k >= len(lines) or ind(lines[k]) != d or lines[k].strip() == "qed":
            continue
        rest = "\n".join(lines[j : item_end(i)])
        if any(re.search(rf"(?<![\w.]){re.escape(n)}(?!\w)", rest) for n in names):
            continue
        gone.update(range(i, j))
    return [l for k, l in enumerate(lines) if k not in gone]


PASSES = {"inst": pass_inst, "args": pass_args, "unused": pass_unused}

# ----------------------------------------------------------------------
# hunks: kept as far as the file checks and is no slower


class Hunks:
    def __init__(self, old, new):
        self.old, self.new = old, new
        self.h = [op for op in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes() if op[0] != "equal"]

    def text(self, keep):
        """the old text with the hunks `keep` applied; each kept hunk's first
        line in it"""
        out, starts, i = [], {}, 0
        for k, (_, i1, i2, j1, j2) in enumerate(self.h):
            out += self.old[i:i1]
            if k in keep:
                starts[k] = len(out)
                out += self.new[j1:j2]
            else:
                out += self.old[i1:i2]
            i = i2
        out += self.old[i:]
        return out, starts


def keep_checking(f, hs, keep):
    """the hunks kept while the file fails: the one at its error dropped"""
    keep = set(keep)
    while True:
        text, starts = hs.text(keep)
        write(f, text)
        ok, err, t, _ = run_check(f)
        if ok:
            return keep, t
        n = err_line(err)
        cands = [k for k in keep if n is not None and starts[k] <= n - 1]
        if not cands:
            print(f"   giving up the pass: {err[:200]}", flush=True)
            return set(), None
        keep.discard(max(cands, key=lambda k: starts[k]))


def keep_fast(f, hs, keep, base):
    limit_t = base * 1.05 + 0.03
    kept = set()

    def solve(ks):
        text, _ = hs.text(kept | set(ks))
        write(f, text)
        ok, _, t, _ = run_check(f)
        # (a slower time measured again before it counts: noise)
        if ok and t > limit_t:
            t = min(t, run_check(f)[2])
        if ok and t <= limit_t:
            kept.update(ks)
        elif len(ks) > 1:
            h = len(ks) // 2
            solve(ks[:h])
            solve(ks[h:])

    solve(sorted(keep))
    return kept


def write(f, lines):
    with open(os.path.join(ROOT, f), "w") as o:
        o.write("\n".join(lines))


def tidy(f, passes, timing, dry):
    path = os.path.join(ROOT, f)
    start = open(path).read().split("\n")
    ok, err, base, _ = run_check(f)
    if not ok:
        print(f"{f}: does not check before tidying: {err[:200]}")
        return
    base = min(base, run_check(f)[2])
    print(f"{f}: {len(start)} lines, {base:.2f} s", flush=True)
    for name in passes:
        old = open(path).read().split("\n")
        new = PASSES[name](f, old)
        hs = Hunks(old, new)
        if not hs.h:
            print(f"  {name}: nothing", flush=True)
            continue
        if dry:
            print(f"  {name}: {len(hs.h)} hunks ({len(new) - len(old):+d} lines)", flush=True)
            write(f, old)
            continue
        keep, _ = keep_checking(f, hs, range(len(hs.h)))
        if keep and timing:
            # (against the file's time before tidying, not this pass's start:
            # the passes' slack would add up)
            keep = keep_fast(f, hs, keep, base)
        text, _ = hs.text(keep)
        write(f, text)
        print(f"  {name}: {len(keep)} of {len(hs.h)} hunks kept ({len(text) - len(old):+d} lines)", flush=True)
    end = open(path).read().split("\n")
    ok, err, t, _ = run_check(f)
    if ok:
        t = min(t, run_check(f)[2])
    if not ok:
        write(f, start)
        print(f"{f}: the result fails ({err[:200]}) -- restored")
        return
    size = lambda ls: sum(len(l) + 1 for l in ls)
    print(f"{f}: {len(end) - len(start):+d} lines, {size(end) - size(start):+d} bytes, {base:.2f} -> {t:.2f} s", flush=True)


def main():
    global VERBOSE
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--passes", default="inst,args,unused")
    ap.add_argument("--no-time", action="store_true")
    ap.add_argument("--dry", action="store_true")
    ap.add_argument("-v", action="store_true")
    ap.add_argument("--symex", action="store_true")
    a = ap.parse_args()
    VERBOSE = a.v
    global SYMEX
    SYMEX = a.symex
    passes = a.passes.split(",")
    for p in passes:
        if p not in PASSES:
            sys.exit(f"no pass `{p}` (passes: {', '.join(PASSES)})")
    for f in a.files:
        tidy(f, passes, not a.no_time, a.dry)


if __name__ == "__main__":
    main()
