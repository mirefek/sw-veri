# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

## 1. Now: the specs' loose ends

Every function's spec states its purpose (layers/mallocng_specs.sl), its
code refining it directly (proofs/mallocng/fun/). Left over:
- What enframe's callers owe (malloc's): the class bound (its n within the
  class), the thread pointer's word apart from the slot (the C world's
  TLS), a stride below 2^31; the slot's access is the invariant's
  (`mp.slot_rw_of`).

## 2. Next: alloc_group, loops on the CFG and loops by their purpose

- alloc_meta's leaves at machine level: get_random_secret, __syscall1,
  __mmap, __mprotect, __errno_location (C1 of their code, or their specs
  as the machine's), to discharge `mp.am_implements`' hypotheses -- and
  `mp.as_implements` / `mp.agr_implements`' (`mp.ap_leaves`, the same).
  __syscall1 is done (`mp.sy1_abi`; as `mp.ap_leaves`' G3: `mp.ap_sy1`,
  to be used once the other leaves are); __get_tp, __errno_location,
  __syscall3, __mprotect, __syscall_ret have their C1
  (proofs/mallocng/machine/c1_leaves.core); __errno_location, __syscall_ret,
  size_overflows, __syscall3 and __mprotect their contracts at machine
  level (`elc.composed`, `srtc.composed_el`, `sotc.composed_el`,
  `sy3c.composed`, `mprc.composed`, `vwc.composed`, `sy6c.composed` -- the
  last `tr.implements_at_s`, with a stack argument). __mmap has its C2
  (`ms.mmap_fun_c2`) and its C1 (`mmc.implements`); to link it:
  __syscall6's `{p}.typed` and `tr.callee_io_s` (eff.rs for a CFunS spec,
  `tr.eff_sys_call6` -- mmap's fresh pages keep the program loaded),
  __mmap's own `tr.callee_io` (`tr.eff_call1_s`), then `mmc.linked` /
  `mmc.composed` (proofs/mallocng/machine/cfg_mmap.core). Then memcpy's
  model.
- CFG -> loops, later: nested loops, a head reached at two structured
  loops, an exit of two loops, a callee refined inside a walk with loops
  of its own.
- Specs by purpose of the loop functions (step_seq): the
  loop's invariant and variant at its head stated over the abstract
  state, the code's loop refined to it (as try_avail's span loop).

## 3. Then: the remaining functions

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
- User proofs on a CFG (an invariant per label) for functions with no
  structured view.
- The loops' label claims (`lab_all`) split over every label: each label's
  claim the whole premise instantiated there, ~1.5 s per label in
  alloc_group's 56 though only the heads' and exits' are not vacuous. Split
  on the heads (and exits) alone, the rest vacuous at once.
- Variables and terms owned by what uses them: a variable reference
  counted (its name and arity freed with its last term, identity by
  pointer, not a table index), terms hash-consed (equal terms one node,
  equality a pointer compare, a weak table freeing them). Now a proof's
  variables are dropped only at its end (`Env::begin_locals` ..
  `end_locals`), each proof's still held until then, and equal terms built
  apart are separate nodes.

## 5. The invariant and the laws

- `mallocng.abs_unique` (the abstract state determined by memory): the
  laws rest on it.
- `musl.free_step` (free always has a step), open in
  proofs/mallocng/claim.core.
- The C world owning only its statics, heap and stack objects.
- `slc heapcheck` on larger heaps: each byte's view membership (`held`)
  searches every group's slots (`in_reserved`), so a check grows with
  groups x bytes (~2 min at 60 groups; the ignored tests take 3.5 min).
  An interval form of the footprint per check would make it linear.

## 6. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap. It needs from exec (spec/linux/exec.sl):
the break within the user space (`brk_ok`), the auxiliary vector apart
from the data (`fresh_ok.auxv_ctx`); and the ABI's entry its
`brk_start_ok`.

## 7. Usability

- `rsimp` for the machine's semantics (proofs/linux_sys.core) instead of
  hand lemmas: a dispatch's live case is `rsimp(h, tag)` already; a
  statement's known outcome through the elaborator's sequencing forms
  (the outcomes' parts and their kinds' disequalities registered,
  core/records.core) should be too -- the hand lemmas `lx.top_*`,
  `lx.blk_*`, `lx.ib_*`, `lx.istep_*`, `lx.tlp_*`, `lx.lp_brk` then go.
  The rest of the proofs' `simp` that only rewrites: `rsimp` (simp kept
  for executing program paths).

- `divergence()` takes a contract's body only of the `ct.dv_*` shapes (a
  step, a return after a choice or two); brk's (branches, havocs) by hand
  (`mp.sy1_divw`: never diverging with its requirement met,
  `mp.sy1_nodiv`). A body's divergence by its structure (per statement)
  would cover such specs.
- The proof cache does not key on the checker: after an engine change
  `scripts/check.sh` reports proofs "as checked before"; check the
  engine's changes uncached (the test's `--no-cache`), times per file by
  `SLC_TIMES=1`, slow steps by `STEP_SLOW=secs`.
- alloc_meta's remaining plumbing (am_run ~1120 lines): the context's
  usable words derived per memory stretch (`mp.ctx_usable` per offset,
  `mp.usable_pg` across a page change); the two three-case joins (`ht2`,
  `tm`) still split by hand; each exit's outcome built by `disj` /
  `ex_intro`. A closure deriving usability from the invariant
  (`mp.ctx_usable_w`, tried at every usable premise, its variables bound
  from the `using` facts) made the run several times slower: not that
  way -- a fact the run states once per memory, instantiated by step.

- Generate the function-level C2s and compositions (one instance of
  `g.fun_res` / `g.fun_res_ghost` and `tr.implements_refine` each).
- The bitfield store `ms.stbfw_det` (fun/alloc_group.core) belongs with
  ops.core's store lemmas.
- The trivial facts that a callee refines itself (`agself`, `dbself` in
  `mp.ta_run`, `amself`, `taself`) are no longer needed (`gc.calls_self`):
  to be removed.
- `ex_intro({..})` inside `taut(..)` misparsed as a binder (hit again in
  `mp.ta_q` and `gc.regs_one`: the inner witness needs its own `have`);
  the list lemmas of proofs/translate_call.core (`tr.seq_one_type`,
  `tr.concat_list`) to core/list.core.
- `step`'s names: the continuation first, then the call's facts; a
  wrong guess shows up only as "names not used" or an odd destructuring
  error. The message could print which name got what.
- `defs(..)` unfolds the goal only; a fact needs `expand` first (ctx_free
  in `mp.co_unt`): `defs` could unfold the facts it is given too.
- `arith`: `x in bits(n)` for n above 100 is not arithmetic (bits(128):
  narrowed by hand, `mp.hdr_new`); `ord_lt(0, n)` needs `n in omega` given;
  no `-1` literal (`int_neg(1)`); an inline arith inside `taut` needs its
  goal written out.
- Record updates in another order (`fn_update` with distinct keys): simp
  does not normalize them; `mp.clear_perm` swaps four times by hand.
- A call's registers read back: the inversion lemmas `gc.regs1` ..
  `gc.regs_32_64` per list of widths remain (the existence side is
  general now); `gc.reg_at` reads one register of any list.
- The rules' standard form: the statics' names, `and r8, 2^k - 1`, `[p + 0]`
  as equations of N (docs/overview.md).
- `arith` takes `x in omega` only as its own fact, not as a conjunct of
  one (`x0 in omega && x1 in omega` destructured first).
- The invariant's constant tables (the class table, a_ctz_32's) are
  stated, framed and read each by its own copy of the same lemmas
  (`mp.mf_classes` / `mp.mf_debruijn`, `mp.lf_*`, `mp.*_table`): one
  predicate for a read-only table, framed once, would serve both.
- Lemmas stated twice: `ms.imul_4` / `_16` and the generated contexts'
  effect lemmas (`dqtc.eff_meta_next` .. repeated in each `..tc` of `slc
  steps`): one shared set.
- `search`: by patterns and by the goal; not yet by a premise's shape
  (what a fact in hand can be fed to), nor ranked by how much of the
  pattern a fact's statement is.

## Later

- Multi-threading; traces of infinite runs (I/O specs that run forever).
- Optimized code: the cut-point theorem between two CFGs, an optimization
  layer, DWARF location maps; other compilers (LLVM IR).
- Beyond malloc: signals, varargs, realloc, filesystem, networking, C types
  above raw memory, whole executables (busybox).
- Model: file mappings, recursion, fault ordering across two pages.
