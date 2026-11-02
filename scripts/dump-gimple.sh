#!/bin/sh
# Dumps GCC's GIMPLE for musl source files, compiled exactly as musl's build
# compiled them (the command is taken from build/musl-make.log), into
# build/gimple/:
#   <file>.gimple     the first GIMPLE (after gimplification, before SSA
#                     and any optimization)
#   <file>.optimized  the last GIMPLE (after all tree-level optimizations;
#                     what is expanded to RTL and then machine code)
#   <file>.o          the object compiled with -g in addition (the same
#                     machine code): its DWARF gives struct layouts
#
# With BUILD=-O0 (the build of scripts/build-musl.sh -O0): the commands of
# that build, into build/gimple-O0/.
#
# usage: [BUILD=-O0] scripts/dump-gimple.sh src/malloc/mallocng/malloc.c ...
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
b=${BUILD:+-${BUILD#-}}
musl=$(sed -n 's/^srcdir = //p' "$root/build/musl$b-obj/config.mak")
log=$root/build/musl$b-make.log
out=$root/build/gimple$b
mkdir -p "$out"
for f in "$@"; do
    base=$(echo "$f" | tr / _)
    tmp=$(mktemp -d)
    case "$f" in
      tests/*)
        # (the test program: compiled as scripts/build-musl.sh links it)
        cc="$root/build/musl$b/bin/musl-gcc -static ${BUILD:--O2} -fomit-frame-pointer -c $root/$f"
        eval "$cc -o $tmp/$base.o -fdump-tree-gimple -fdump-tree-optimized -dumpdir $tmp/"
        cp "$tmp"/*.gimple "$out/$base.gimple"
        cp "$tmp"/*.optimized "$out/$base.optimized"
        eval "$cc -o $out/$base.o -g"
        rm -rf "$tmp"
        echo "$out/$base.{gimple,optimized}"
        continue ;;
    esac
    cmd=$(grep -- " $musl/$f\$" "$log" | head -1)
    [ -n "$cmd" ] || { echo "no compile command for $f in $log" >&2; exit 1; }
    # same command; object and dumps into a temporary directory
    cmd=$(echo "$cmd" | sed "s| -o [^ ]*| -o $tmp/$base.o|")
    (cd "$root/build/musl$b-obj" && eval "$cmd -fdump-tree-gimple -fdump-tree-optimized -dumpdir $tmp/")
    cp "$tmp"/*.gimple "$out/$base.gimple"
    cp "$tmp"/*.optimized "$out/$base.optimized"
    (cd "$root/build/musl$b-obj" && eval "$(echo "$cmd" | sed "s| -o [^ ]*| -o $out/$base.o|") -g")
    rm -rf "$tmp"
    echo "$out/$base.{gimple,optimized}"
done
