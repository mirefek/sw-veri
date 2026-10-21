#!/bin/sh
# The proof chain (proofs/chain; the test `c1_cfg_engine_checks`,
# slc/cli/tests/steps.rs), checked with the caches (build/kernel-cache: a
# file unchanged, after the same statements, not checked again; in a
# changed one, a proof unchanged in the same context neither) -- for
# checking while editing.
#
#   scripts/check.sh gen        make the generated files (build/chain/:
#                               decode facts, program text, readable CFG),
#                               after a change to the binaries or the spec
#   scripts/check.sh [FILE]     elaborate the layers, check the chain (up
#                               to FILE, e.g. proofs/mallocng/fun/try_avail.core)
#
# The test itself checks everything without the caches (--no-cache).
# Needs the musl build (scripts/build-musl.sh -O0) and slc built
# (cargo build --release --manifest-path slc/Cargo.toml).
R=$(cd "$(dirname "$0")/.." && pwd)
B=$R/build/chain
S=$R/slc/target/release/slc
cd "$R" || exit 1
ulimit -v 6000000
# (the leaves' sources: dump name (build/gimple-O0, from scripts/dump-gimple.sh),
# readable name, source file name)
LEAVES="src_errno___errno_location:c_errno_location:__errno_location.c src_internal_syscall_ret:c_syscall_ret:syscall_ret.c
  src_mman_mprotect:c_mman_mprotect:mprotect.c src_mman_mmap:c_mman_mmap:mmap.c"
if [ "$1" = gen ]; then
  mkdir -p "$B"
  $S steps build/test_malloc_O0 build/musl_malloc_O0.core a_ctz_32 is_bouncing=403842 get_slot_index=4030dd get_stride=403350 step_seq=40370a upgradelock resetlock decay_bounces a_clz_32 dequeue=402f49 dequeue_head a_crash=402c6e queue=402e8c free_meta=403014 size_to_class set_size enframe account_bounce get_meta=4030f5 activate_group=40304f __malloc_allzerop alloc_slot try_avail alloc_group=403ee6 a_cas=402c47 size_overflows __malloc_alloc_meta get_random_secret __syscall1=402cf9 __mmap __mprotect __errno_location __get_tp=40569a __syscall3=404bde __syscall6=404a8c __syscall_ret dummy=404ada -o "$B/steps.core" --text "$B/text.core" || exit 1
  $S gimple --readable --cfg --elf build/test_malloc_O0 --obj build/gimple-O0/src_malloc_mallocng_malloc.c.o --source malloc.c build/gimple-O0/src_malloc_mallocng_malloc.c.optimized -o "$B/cfg.sl" || exit 1
  # the leaves' sources (musl's errno, syscall and mman wrappers): their
  # structured and CFG forms
  for t in $LEAVES; do
    src=${t%%:*}; name=${t#*:}; name=${name%%:*}; base=${t##*:}
    $S gimple --readable --elf build/test_malloc_O0 --obj build/gimple-O0/$src.c.o --source $base build/gimple-O0/$src.c.optimized -o build/gimple-O0/sl/$name.sl || exit 1
    $S gimple --readable --cfg --elf build/test_malloc_O0 --obj build/gimple-O0/$src.c.o --source $base build/gimple-O0/$src.c.optimized -o "$B/cfg_$name.sl" || exit 1
  done
  exit 0
fi
[ -e "$B/steps.core" ] || { echo "no build/chain: run scripts/check.sh gen" >&2; exit 1; }
LEAF_SL=""
for t in $LEAVES; do name=${t#*:}; name=${name%%:*}; LEAF_SL="$LEAF_SL build/gimple-O0/sl/$name.sl $B/cfg_$name.sl"; done
$S elab spec layers build/gimple-O0/sl/c_mallocng_malloc.sl "$B/cfg.sl" $LEAF_SL -o "$B/gimple.core" >/dev/null || exit 1
LOC=""
[ -e build/locmap_O0.core ] && LOC=build/locmap_O0.core
FILES=$(grep -v '^ *#' proofs/chain | grep -v '^ *$' |
  sed -e "s|^@gimple\$|$B/gimple.core|" -e "s|^@steps\$|$B/steps.core|" -e "s|^@text\$|$B/text.core|" -e "s|^@locmap\$|$LOC|")
if [ -n "$1" ]; then
  case " $(echo $FILES) " in
    *" $1 "*) ;;
    *) echo "$1: not in the chain" >&2; exit 1 ;;
  esac
  FILES=$(echo $FILES | sed "s| $1 .*| $1|")
fi
$S kernel-check $FILES 2>&1 | grep -v "^core/\|^proofs/[a-z_0-9/]*.core: .*(cached)\$\|^$B/\|^build/"
