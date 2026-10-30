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
  src_env___stack_chk_fail:c_stack_chk_fail:__stack_chk_fail.c"
# (the startup units: their functions all run before main, `slc gimple --startup`)
STARTUP="crt_crt1 src_env___libc_start_main src_env___stack_chk_fail"
if [ "$1" = gen ]; then
  mkdir -p "$B"
  $S steps build/test_malloc_O0 a_ctz_32 is_bouncing=403842 get_slot_index=4030dd get_stride=403350 step_seq=40370a upgradelock resetlock decay_bounces a_clz_32 dequeue=402f49 dequeue_head a_crash=402c6e queue=402e8c free_meta=403014 size_to_class set_size enframe account_bounce get_meta=4030f5 activate_group=40304f __malloc_allzerop alloc_slot try_avail alloc_group=403ee6 a_cas=402c47 size_overflows __malloc_alloc_meta get_random_secret __syscall1=402cf9 __mmap __mprotect __errno_location __get_tp=40569a __syscall3=404bde __syscall6=404a8c __syscall_ret dummy=404ada memcpy __stack_chk_fail rdlock=402ddf wrlock=402e03 unlock=402e27 __unlock=4050c8 __lock=404f98 a_fetch_add=404e83 __wake=404ea2 __syscall2=404c8d __munmap __libc_malloc_impl default_malloc=401e53 fr_a_cas=401e6e a_or fr_a_crash=401eac fr_wrlock=401eaf fr_unlock=401ed3 fr_queue=401eec fr_dequeue=401fa9 fr_free_meta=40203a fr_activate_group=402075 fr_get_slot_index=402103 fr_get_meta=40211b get_nominal_size fr_get_stride=40245e fr_step_seq=4024ca record_seq fr_is_bouncing=402543 free_group okay_to_free nontrivial_free __libc_free free _start_c __libc_start_main libc_start_main_stage2 __init_libc __libc_start_init exit _init:3 __init_tls __init_ssp lsm___syscall3=4012cc lsm_a_crash=401301 lsm___syscall2=40129e memset ssp___get_tp=405601 -o "$B/steps.core" --text "$B/text.core" || exit 1
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
$S claim malloc --elf build/test_malloc_O0 -o "$B/claim.core" >/dev/null || exit 1
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
