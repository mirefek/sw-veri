#!/bin/sh
# The proof chain (proofs/chain; the test `c1_cfg_engine_checks`,
# slc/cli/tests/steps.rs), checked with the caches (build/kernel-cache: a
# file unchanged, after the same statements, not checked again; in a
# changed one, a proof unchanged in the same context neither) -- for
# checking while editing.
#
#   scripts/check.sh gen        make the generated files (build/chain/:
#                               the decode facts' line -- the facts made in
#                               the checker --, program text, readable CFG),
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
# (the other translation units: dump name (build/gimple-O0, from
# scripts/dump-gimple.sh), readable name, source file name)
LEAVES="src_errno___errno_location:c_errno_location:__errno_location.c src_internal_syscall_ret:c_syscall_ret:syscall_ret.c
  src_mman_mprotect:c_mman_mprotect:mprotect.c src_mman_mmap:c_mman_mmap:mmap.c src_thread___lock:c_lock:__lock.c
  src_mman_munmap:c_mman_munmap:munmap.c src_malloc_lite_malloc:c_lite_malloc:lite_malloc.c
  src_malloc_mallocng_free:c_mallocng_free:free.c src_malloc_free:c_free:free.c
  crt_crt1:c_crt1:crt1.c src_env___libc_start_main:c_libc_start_main:__libc_start_main.c
  src_env___stack_chk_fail:c_stack_chk_fail:__stack_chk_fail.c src_env___init_tls:c_init_tls:__init_tls.c"
# (the startup units: their functions all run before main, `slc gimple --startup`)
STARTUP="crt_crt1 src_env___libc_start_main src_env___stack_chk_fail src_env___init_tls"
if [ "$1" = gen ]; then
  mkdir -p "$B"
  $S steps build/test_malloc_O0 a_ctz_32 is_bouncing=4038c8 get_slot_index=403163 get_stride=4033d6 step_seq=403790 upgradelock resetlock decay_bounces a_clz_32 dequeue=402fcf dequeue_head a_crash=402cf4 queue=402f12 free_meta=40309a size_to_class set_size enframe account_bounce get_meta=40317b activate_group=4030d5 __malloc_allzerop alloc_slot try_avail alloc_group=403f6c a_cas=402ccd size_overflows __malloc_alloc_meta get_random_secret __syscall1=402d7f __mmap __mprotect __errno_location __get_tp=405684 __syscall3=404c64 __syscall6=404b12 __syscall_ret dummy=404b60 memcpy __stack_chk_fail rdlock=402e65 wrlock=402e89 unlock=402ead __unlock=40514e __lock=40501e a_fetch_add=404f09 __wake=404f28 __syscall2=404d13 __munmap __libc_malloc_impl default_malloc=401ed9 fr_a_cas=401ef4 a_or fr_a_crash=401f32 fr_wrlock=401f35 fr_unlock=401f59 fr_queue=401f72 fr_dequeue=40202f fr_free_meta=4020c0 fr_activate_group=4020fb fr_get_slot_index=402189 fr_get_meta=4021a1 get_nominal_size fr_get_stride=4024e4 fr_step_seq=402550 record_seq fr_is_bouncing=4025c9 free_group okay_to_free nontrivial_free __libc_free free _start_c __libc_start_main libc_start_main_stage2 __init_libc __libc_start_init exit _init:3 __init_tls __init_ssp lsm___syscall3=40146c lsm_a_crash=4014a1 lsm___syscall2=40143e memset ssp___get_tp=401915 tls___syscall1=405194 tls___syscall6=4051b8 tls_a_crash=405206 __init_tp __copy_tls static_init_tls __set_thread_area _start:22 register_tm_clones:57 frame_dummy:9 -o "$B/steps.core" --text "$B/text.core" || exit 1
  $S gimple --readable --elf build/test_malloc_O0 --obj build/gimple-O0/src_malloc_mallocng_malloc.c.o --source malloc.c build/gimple-O0/src_malloc_mallocng_malloc.c.optimized -o build/gimple-O0/sl/c_mallocng_malloc.sl || exit 1
  $S gimple --readable --cfg --elf build/test_malloc_O0 --obj build/gimple-O0/src_malloc_mallocng_malloc.c.o --source malloc.c build/gimple-O0/src_malloc_mallocng_malloc.c.optimized -o "$B/cfg.sl" || exit 1
  # the leaves' sources (musl's errno, syscall and mman wrappers): their
  # structured and CFG forms
  for t in $LEAVES; do
    src=${t%%:*}; name=${t#*:}; name=${name%%:*}; base=${t##*:}
    # (the units whose functions all run before main: their calls call0, the startup mode's)
    st=""; case " $STARTUP " in *" $src "*) st=--startup ;; esac
    $S gimple --readable $st --elf build/test_malloc_O0 --obj build/gimple-O0/$src.c.o --source $base build/gimple-O0/$src.c.optimized -o build/gimple-O0/sl/$name.sl || exit 1
    $S gimple --readable --cfg $st --elf build/test_malloc_O0 --obj build/gimple-O0/$src.c.o --source $base build/gimple-O0/$src.c.optimized -o "$B/cfg_$name.sl" || exit 1
  done
  exit 0
fi
[ -e "$B/steps.core" ] || { echo "no build/chain: run scripts/check.sh gen" >&2; exit 1; }
LEAF_SL=""
for t in $LEAVES; do name=${t#*:}; name=${name%%:*}; LEAF_SL="$LEAF_SL build/gimple-O0/sl/$name.sl $B/cfg_$name.sl"; done
# the claim (from the layers and the -O0 binary), then the layers and the
# readable GIMPLE elaborated, what the claim states already left out
$S claim malloc --elf build/test_malloc_O0 --program-exits 0,1 -o "$B/claim.core" >/dev/null || exit 1
$S elab spec layers build/gimple-O0/sl/c_mallocng_malloc.sl "$B/cfg.sl" $LEAF_SL --after "$B/claim.core" -o "$B/gimple.core" >/dev/null || exit 1
LOC=""
[ -e build/locmap_O0.core ] && LOC=build/locmap_O0.core
FILES=$(grep -v '^ *#' proofs/chain | grep -v '^ *$' |
  sed -e "s|^@claim\$|$B/claim.core|" -e "s|^@gimple\$|$B/gimple.core|" -e "s|^@steps\$|$B/steps.core|" -e "s|^@text\$|$B/text.core|" -e "s|^@locmap\$|$LOC|")
if [ -n "$1" ]; then
  case " $(echo $FILES) " in
    *" $1 "*) ;;
    *) echo "$1: not in the chain" >&2; exit 1 ;;
  esac
  FILES=$(echo $FILES | sed "s| $1 .*| $1|")
fi
$S kernel-check $FILES 2>&1 | grep -v "^core/\|^proofs/[a-z_0-9/]*.core: .*(cached)\$\|^$B/\|^build/"
