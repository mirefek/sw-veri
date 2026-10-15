# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

## 1. Now: the specs' loose ends

Every function's spec states its purpose (layers/mallocng_specs.sl), its
code refining it directly (proofs/mallocng_refine.core). Left over:
- The ABI-level form of the functions with World specs (set_size,
  dequeue, dequeue_head, queue, free_meta, the leaf specs; proved to
  `tr.implements_at` so far): `tr.div_raises` of the spec by the World
  variant of `ct.contract_div`.
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

- try_avail: its run is proved (`mp.ta_run`); left the refinement with
  the ghost update (`mp.ta`, as `mp.ag`), its machine code implementing
  the spec, its contract at a call (for alloc_slot).
- alloc_slot (spec written, `alloc_slot_spec`; C1 done),
  `__malloc_alloc_meta`.
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
- User proofs on a CFG (an invariant per label) for functions with no
  structured view.

## 5. The invariant and the laws

- `mallocng.abs_unique` (the abstract state determined by memory): the
  laws rest on it.
- `musl.free_step` (free always has a step), open in
  proofs/musl_malloc.core.
- The C world owning only its statics, heap and stack objects.
- `slc heapcheck` on larger heaps: each byte's view membership (`held`)
  searches every group's slots (`in_reserved`), so a check grows with
  groups x bytes (~2 min at 60 groups; the ignored tests take 3.5 min).
  An interval form of the footprint per check would make it linear.

## 6. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap.

## 7. Usability

- Generate the function-level C2s and compositions (one instance of
  `g.fun_res` / `g.fun_res_ghost` and `tr.implements_refine` each).
- A call to a callee by its own contract still needs the trivial fact
  that the callee refines itself (`agself`, `dbself` in `mp.ta_run`): the
  call rule could take it as given.
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
