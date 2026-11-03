#!/usr/bin/env python3
"""Location maps for the C1 engine: where each local of a readable-GIMPLE
procedure lives in the -O0 code's frame.

For each mallocng source, the object is compiled once more as the musl
build compiled it, with -g added (at -O0, GCC's code is the same with or
without -g), and its DWARF read (objdump --dwarf=info): each named local's
frame offset (DW_OP_fbreg, from the call frame's CFA: the entry's rsp + 8)
and the address range of its scope (the function's, or its lexical
block's). The locals of the readable procedure (its `var`s, in order: the
locals tuple of its GIMPLE semantics) are matched by name (a struct's
field held as a variable, `var x_f: .. // x + OFF`: x's, OFF on).

Written to build/locmap_O0.core, one definition per procedure:

  def loc.SPEC() := pair(pair(K, pair(KEY, pair(LO, HI))), pair(.., empty))

K the local's position in the tuple, KEY its home's key (the offset from
the entry's rsp, modulo 2^64: the engine's), LO..HI the scope's addresses
as offsets from the function's start; and for a procedure with stack
objects (address-taken locals, `alloc_objs`), their keys in order:

  def loc_objs.SPEC() := pair(KEY, pair(.., empty))
 Untrusted: the engine only uses it
to choose which home holds which local; the kernel checks every step.

usage: scripts/locmap.py   (after scripts/build-musl.sh -O0 and
                            slc gimple --readable)
"""
import os
import re
import shlex
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OBJ = os.path.join(ROOT, "build", "musl-O0-obj")
LOG = os.path.join(ROOT, "build", "musl-O0-make.log")
SOURCES = [
    ("src/malloc/mallocng/malloc.c", "build/gimple-O0/sl/c_mallocng_malloc.sl", "c_src_malloc_mallocng_malloc"),
    ("src/malloc/mallocng/free.c", "build/gimple-O0/sl/c_mallocng_free.sl", "c_src_malloc_mallocng_free"),
    # the leaves: musl's errno, syscall and mman wrappers
    ("src/errno/__errno_location.c", "build/gimple-O0/sl/c_errno_location.sl", "c_src_errno___errno_location"),
    ("src/internal/syscall_ret.c", "build/gimple-O0/sl/c_syscall_ret.sl", "c_src_internal_syscall_ret"),
    ("src/mman/mprotect.c", "build/gimple-O0/sl/c_mman_mprotect.sl", "c_src_mman_mprotect"),
    ("src/mman/mmap.c", "build/gimple-O0/sl/c_mman_mmap.sl", "c_src_mman_mmap"),
    # the startup code on the path to main
    ("crt/crt1.c", "build/gimple-O0/sl/c_crt1.sl", "c_crt_crt1"),
    ("src/env/__libc_start_main.c", "build/gimple-O0/sl/c_libc_start_main.sl", "c_src_env___libc_start_main"),
    ("src/env/__init_tls.c", "build/gimple-O0/sl/c_init_tls.sl", "c_src_env___init_tls"),
    # the exit path after main
    ("src/exit/exit.c", "build/gimple-O0/sl/c_exit.sl", "c_src_exit_exit"),
    ("src/exit/_Exit.c", "build/gimple-O0/sl/c__Exit.sl", "c_src_exit__Exit"),
    # the test program (its -g object from scripts/dump-gimple.sh)
    ("tests/test_malloc.c", "build/gimple-O0/sl/c_test_malloc.sl", "c_tests_test_malloc"),
]
P64 = 1 << 64


def compile_g(src, out):
    """the source compiled as the build did, with -g"""
    for line in open(LOG):
        if line.startswith("gcc ") and line.rstrip().endswith(src):
            args = shlex.split(line)
            i = args.index("-o")
            args[i + 1] = out
            args.insert(1, "-g")
            subprocess.run(args, cwd=OBJ, check=True)
            return
    sys.exit("no compile command for " + src)


def dwarf_locals(obj):
    """per function: (name, fbreg, lo, hi) for each named local"""
    text = subprocess.run(["objdump", "--dwarf=info", obj], capture_output=True, text=True, check=True).stdout
    funcs = {}
    stack = []  # (depth, kind, attrs)
    cur = None
    for line in text.splitlines():
        m = re.match(r"\s*<(\d+)><[0-9a-f]+>: Abbrev Number: \d+ \((DW_TAG_\w+)\)", line)
        if m:
            depth, tag = int(m.group(1)), m.group(2)
            cur = {"tag": tag, "depth": depth}
            while stack and stack[-1]["depth"] >= depth:
                stack.pop()
            stack.append(cur)
            continue
        if cur is None:
            continue
        m = re.match(r"\s*<[0-9a-f]+>\s+(DW_AT_\w+)\s*:\s*(.*)", line)
        if not m:
            continue
        at, val = m.group(1), m.group(2).strip()
        if at == "DW_AT_name":
            cur["name"] = val.split(": ")[-1].strip()
        elif at == "DW_AT_low_pc":
            cur["lo"] = int(val, 16)
        elif at == "DW_AT_high_pc":
            cur["len"] = int(val, 16)
        elif at == "DW_AT_location":
            fb = re.search(r"DW_OP_fbreg: (-?\d+)", val)
            if fb:
                cur["fbreg"] = int(fb.group(1))
                # the local: its function, its scope (innermost block or the
                # function with a range)
                fn = next((x for x in stack if x["tag"] == "DW_TAG_subprogram"), None)
                scope = next((x for x in reversed(stack[:-1]) if "lo" in x and "len" in x), None)
                if fn is not None and scope is not None and "name" in cur and "name" in fn:
                    # (offsets from the function's start: its own section's
                    # 0 in musl's objects, -ffunction-sections; the test's
                    # functions share one)
                    f0 = fn.get("lo", 0)
                    funcs.setdefault(fn["name"], []).append((cur["name"], cur["fbreg"], scope["lo"] - f0, scope["lo"] + scope["len"] - f0))
    return funcs


def readable_vars(sl):
    """per procedure: its vars' names in order, and its stack objects'
    (the `alloc_objs` line's comment, in order)"""
    procs = {}
    objs = {}
    name = None
    for line in open(sl):
        m = re.match(r"proc\[\w+\] (\w+)\(", line)
        if m:
            name = m.group(1)
            procs[name] = []
            continue
        m = re.match(r"  var (\w+):[^/]*(?://\s*(\S+) \+ (\d+))?\s*$", line)
        if m and name is not None:
            # (a struct's field held as a variable: the struct's C name,
            # the field's offset)
            if m.group(2):
                procs[name].append((m.group(1), m.group(2), int(m.group(3))))
            else:
                procs[name].append((m.group(1), m.group(1), 0))
            continue
        m = re.match(r"  let objs = alloc_objs\(.*\)  // (.*)$", line)
        if m and name is not None:
            objs[name] = [x.strip() for x in m.group(1).split(",")]
        if name is not None and not line.startswith("  var "):
            name = None
    return procs, objs


def main():
    out = ["// Generated by scripts/locmap.py: the -O0 locals' homes (see there).", ""]
    with tempfile.TemporaryDirectory() as tmp:
        for src, sl, prefix in SOURCES:
            if src.startswith("tests/"):
                obj = os.path.join(ROOT, "build", "gimple-O0", src.replace("/", "_") + ".o")
            else:
                obj = os.path.join(tmp, os.path.basename(src) + ".o")
                compile_g(src, obj)
            dl = dwarf_locals(obj)
            procs, objs = readable_vars(os.path.join(ROOT, sl))
            # (the stack objects' frame keys, in order)
            for proc, names in objs.items():
                keys = []
                for nm in names:
                    ks = [(fb + 8) % P64 for (dn, fb, lo, hi) in dl.get(proc, []) if dn == nm]
                    if len(ks) != 1:
                        sys.exit("%s: object %s: %d locations" % (proc, nm, len(ks)))
                    keys.append(ks[0])
                t = "empty"
                for key in reversed(keys):
                    t = "pair(%d, %s)" % (key, t)
                out.append("def loc_objs.%s.%s() := %s" % (prefix, proc, t))
            for proc, names in procs.items():
                if proc not in dl:
                    continue
                entries = []
                for k, (_, nm, off) in enumerate(names):
                    # (a C name the readable form renamed, a keyword there: `self` as `self_`)
                    cs = {nm, nm[:-1]} if nm.endswith("_") else {nm}
                    for (dn, fb, lo, hi) in dl[proc]:
                        if dn in cs and not (dn != nm and any(d == nm for (d, _, _, _) in dl[proc])):
                            entries.append((k, (fb + off + 8) % P64, lo, hi))
                if not entries:
                    continue
                t = "empty"
                for (k, key, lo, hi) in reversed(entries):
                    t = "pair(pair(%d, pair(%d, pair(%d, %d))), %s)" % (k, key, lo, hi, t)
                out.append("def loc.%s.%s() := %s" % (prefix, proc, t))
    path = os.path.join(ROOT, "build", "locmap_O0.core")
    open(path, "w").write("\n".join(out) + "\n")
    print("wrote", path, len(out) - 2, "maps")


if __name__ == "__main__":
    main()
