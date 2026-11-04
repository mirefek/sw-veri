#!/bin/sh
# Everything the proof chain needs, from a fresh checkout: the checker,
# musl 1.2.6 built at -O0 with the test program, GCC's GIMPLE dumps of
# the translation units the proofs read, the generated files and the
# locals' location map. Then `scripts/check.sh` checks the chain.
#
# The proofs are about one binary's bytes: built by GCC 16.2.1, as here.
#
# usage: MUSL_SRC=/path/to/musl-1.2.6 scripts/setup.sh
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
cargo build --release --manifest-path slc/Cargo.toml
# (a fresh musl build: its make log has the compile commands the dumps reuse)
rm -rf build/musl-O0-obj build/musl-O0
scripts/build-musl.sh -O0
BUILD=-O0 scripts/dump-gimple.sh \
  src/malloc/mallocng/malloc.c src/malloc/mallocng/free.c src/malloc/free.c src/malloc/lite_malloc.c \
  src/errno/__errno_location.c src/internal/syscall_ret.c src/mman/mmap.c src/mman/mprotect.c src/mman/munmap.c \
  src/thread/__lock.c crt/crt1.c src/env/__libc_start_main.c src/env/__stack_chk_fail.c src/env/__init_tls.c \
  src/exit/exit.c src/exit/_Exit.c tests/test_malloc.c
mkdir -p build/gimple-O0/sl
scripts/check.sh gen
python3 scripts/locmap.py
echo "set up; now: scripts/check.sh"
