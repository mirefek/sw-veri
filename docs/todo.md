# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

## 1. Now: meaning-level specs for the functions with memory-level ones

Each function's code refined directly to a spec by its purpose, over the
abstract state (layers/mallocng_purpose.sl, proofs/mallocng_purpose.core;
the pattern of get_slot_index, get_meta, get_stride, `__malloc_allzerop`:
a contract with the ghost part read, the refinement, the callers' rule,
the function value, the machine code). Its memory-level spec
(layers/mallocng_specs.sl), C2 and compositions retired once no caller
uses them; what the code does kept as an effect summary where a proof
needs it (`ms.gm_run`). The invariant composed of more basic definitions,
so a function that breaks it in part still states its exact contract and
keeps the lower-level properties. Bottom-up:

- The list operations dequeue, queue, dequeue_head: on a class's active
  list as a list of groups, relative to the list's well-formedness (they
  run inside try_avail, the invariant not holding there).
- activate_group (with a_cas): the group's inactive slots made available.
- free_meta: a meta returned to the free metas.
- The context's counters and the lock (is_bouncing, decay_bounces,
  account_bounce, step_seq, resetlock, upgradelock): the abstract state
  unchanged, musl's heuristics left free.
- Already specs by purpose, kept: a_ctz_32, a_clz_32, size_to_class,
  size_overflows, a_cas, errno_location, a_crash.
- Then the "purpose" name dropped: these are the specs.

Along the way:
- `tr.div_raises` of loop-free code once, structurally (it diverges only
  where an operation is undefined, and raises there too), instead of per
  function (get_meta's, get_stride's, allzerop's now premises of their
  `*_implements`).
- A variant of `ct.refines_contract` choosing the final ghost part, for
  specs that update A (try_avail, alloc_slot).
- What enframe's callers owe: alloc_slot's postcondition the reserved
  slot's access (`slot_rw`); malloc's the class bound (its n within the
  class), the thread pointer's word apart from the slot (the C world's
  TLS), a stride below 2^31.
- The spec bookkeeping: a contract's body (`letin`, `any_rel`) spelled
  out in each refinement (`mp.ef`, `mp.ss`); a generic lemma per spec shape
  (havoc, then return) would take it.

## 2. Next: alloc_group, loops on the CFG and loops by their purpose

- CFG -> loops: alloc_group has four loops one after another (heads 7, 12,
  16, 54). `g.cut_loops` takes one loop's data (H, bs, ks); several loops
  need them per head, chosen under binders. The loop finder already
  accepts a loop exiting into the next loop's head (uncommitted in
  slc/cli/src/c1/gref/gloop.rs). Later: nested loops, a head reached at
  two structured loops, a callee refined inside a walk with loops of its
  own.
- alloc_group's CFG C1: stops at 404413, a byte store of `dl`
  (`tr.store8_b`'s premise); then the rest of its blocks.
- Specs by purpose of the loop functions (alloc_group, try_avail,
  step_seq, activate_group's caller): the loop's invariant and variant at
  its head stated over the abstract state, the code's loop refined to it.

## 3. Then: the remaining functions

- try_avail, alloc_slot (specs written, `try_avail_purpose`,
  `alloc_slot_purpose`; C1 done), `__malloc_alloc_meta`.
- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`), possibly
  generated.
- `get_nominal_size`, `record_seq`, `okay_to_free`, `free_group`,
  `nontrivial_free`.
- The entry points `__libc_malloc_impl`, `__libc_free`, `calloc` and the
  `lite_malloc` / `free.c` wrappers, against the malloc layer.
- Leaves at machine level: `a_or`, `__syscall*`, `__mmap`, `munmap`,
  `__mprotect`, `memset`, `memcpy`, `__lock` / `__unlock`,
  `___errno_location` (then size_overflows' composition without its
  premise).

## 4. The CFG path's remaining engineering

- The structured form generated and checked in one run (`slc gimple`
  running the refinement); a callee's refinement a theorem of its own, not
  walked again in each caller.
- The loop functions' `refines` lines and compositions in
  proofs/mallocng_cfg.core (step_seq, activate_group, try_avail).
- Switch the `c1` lines and compositions to the CFG path and retire the
  structured walk (`block.rs`, `join.rs`, proofs/translate_block.core);
  its memory (2.4 GB peak against 770 MB).
- User proofs on a CFG (an invariant per label) for functions with no
  structured view.

## 5. The invariant and the laws

- `mallocng.abs_unique` (the abstract state determined by memory): the
  laws rest on it.
- `musl.free_step` (free always has a step), open in
  proofs/musl_malloc.core.
- The C world owning only its statics, heap and stack objects.

## 6. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap.

## 7. Usability

- Generate the function-level C2s and compositions (one instance of
  `g.fun_res` / `g.fun_res_ghost` and `tr.implements_refine` each).
- `ex_intro({..})` inside `taut(..)` misparsed as a binder; the list
  lemmas of proofs/translate_call.core to core/list.core.
- The rules' standard form: the statics' names, `and r8, 2^k - 1`, `[p + 0]`
  as equations of N (docs/overview.md).

## Later

- Multi-threading; traces of infinite runs (I/O specs that run forever).
- Optimized code: the cut-point theorem between two CFGs, an optimization
  layer, DWARF location maps; other compilers (LLVM IR).
- Beyond malloc: signals, varargs, realloc, filesystem, networking, C types
  above raw memory, whole executables (busybox).
- Model: file mappings, recursion, fault ordering across two pages.
