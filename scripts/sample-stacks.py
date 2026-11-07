# A sampling profiler for slc, by gdb (no perf here; ptrace_scope 1 lets
# gdb trace only its own children, so gdb starts the program):
#
#   SAMPLE_OUT=FILE [SAMPLE_INTERVAL=2] [SAMPLE_DELAY=20] \
#     gdb -q -batch -x scripts/sample-stacks.py --args PROG ARGS..
#
# or for the chain, through check.sh's wrapper:
#
#   SAMPLE_OUT=FILE SLC_WRAP="gdb -q -batch -x scripts/sample-stacks.py --args" \
#     scripts/check.sh [FILE]
#
# Every INTERVAL seconds (after DELAY) a SIGUSR1 stops the program and
# each thread's stack but the main thread's is written to FILE (the work
# runs in a thread of its own), until the program ends. scripts/
# sample-report.py summarizes FILE.
import gdb, os, subprocess

INTERVAL = float(os.environ.get("SAMPLE_INTERVAL", "2"))
DELAY = float(os.environ.get("SAMPLE_DELAY", "20"))
OUT = os.environ["SAMPLE_OUT"]
out = open(OUT, "w")
me = os.getpid()


def record():
    for th in gdb.selected_inferior().threads():
        if th.num == 1:
            continue
        th.switch()
        f = gdb.newest_frame()
        i = 0
        out.write("=== sample\n")
        while f is not None and i < 120:
            n = f.name() or "?"
            sal = f.find_sal()
            loc = "%s:%d" % (os.path.basename(sal.symtab.filename), sal.line) if sal.symtab else ""
            out.write("%s %s\n" % (n, loc))
            f = f.older()
            i += 1
    out.flush()


gdb.execute("set pagination off")
gdb.execute("set confirm off")
# (`noprint` would imply `nostop`)
gdb.execute("handle SIGUSR1 stop print nopass")
# (a separate process sends the signals -- gdb holds Python's lock while
# the program runs, so a thread here would not run -- to gdb's children
# but itself)
subprocess.Popen(
    ["sh", "-c", "sleep %s; while kill -0 %d 2>/dev/null; do for c in $(pgrep -P %d); do [ $c != $$ ] && kill -USR1 $c; done; sleep %s; done" % (DELAY, me, me, INTERVAL)],
    stdout=subprocess.DEVNULL,
    stderr=subprocess.DEVNULL,
)
gdb.execute("run", to_string=True)
while gdb.selected_inferior().pid != 0:
    try:
        record()
    except Exception as e:
        out.write("err %s\n" % e)
    try:
        gdb.execute("continue", to_string=True)
    except gdb.error:
        break
out.close()
