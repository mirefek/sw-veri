#!/bin/sh
# Builds musl (static) with the given optimization level, links the test
# program against it, and states the malloc claim for the result:
#
#   build/musl<SUFFIX>-obj/     object directory (musl's out-of-tree build)
#   build/musl<SUFFIX>/         installed musl (musl-gcc wrapper)
#   build/test_malloc<SUFFIX>   the binary the claim is about
#   build/musl_malloc<SUFFIX>.core, .summary.txt   the claim
#
# SUFFIX is empty for -O2 (the original build) and _O0 / -O0 otherwise.
#
# usage: scripts/build-musl.sh [-O2|-O0|...]   (default -O2)
set -e
opt=${1:--O2}
root=$(cd "$(dirname "$0")/.." && pwd)
src=/home/mirek/basic-sw/musl-1.2.6
case "$opt" in
    -O2) sfx=""; dsfx="" ;;
    *) sfx="_${opt#-}"; dsfx="-${opt#-}" ;;
esac
obj=$root/build/musl$dsfx-obj
prefix=$root/build/musl$dsfx
mkdir -p "$obj"
cd "$obj"
"$src/configure" --prefix="$prefix" --disable-shared CFLAGS="$opt" > "$root/build/musl$dsfx-configure.log" 2>&1
make -j8 > "$root/build/musl$dsfx-make.log" 2>&1
make install > "$root/build/musl$dsfx-install.log" 2>&1
"$prefix/bin/musl-gcc" -static "$opt" "$root/tests/test_malloc.c" -o "$root/build/test_malloc$sfx"
"$root/slc/target/release/slc" claim malloc --elf "$root/build/test_malloc$sfx" -o "$root/build/musl_malloc$sfx.core"
echo "built build/test_malloc$sfx, claim build/musl_malloc$sfx.core"
