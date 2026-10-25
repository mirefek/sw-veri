# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

## 1. Next: the remaining functions

alloc_meta, alloc_slot and alloc_group are verified at machine level from
the configuration alone (`mp.am_machine`, `mp.as_machine`,
`mp.agr_machine`); the locks and munmap too (`mp.rdl_linked` ..
`mp.unl_linked`, `mp.mun_linked`), and `__libc_malloc_impl`
(`mp.mi_machine`, proofs/mallocng/fun/malloc_machine.core).
Next, malloc (`musl.impl_malloc`, proofs/mallocng/claim.core):
- mallocng's abstract state to the malloc layer's blocks (`rep`): the
  purpose spec giving `malloc.malloc`; the `malloc` symbol's wrapper
  (lite_malloc.c's `default_malloc`) to `__libc_malloc_impl`. malloc(0):
  musl's block has no usable byte (the malloc layer allows it: a block's
  place its `extent`, one byte at least); rep's blocks the same, the
  extent's byte at p the allocator's.

Then free and calloc: `get_nominal_size`, `record_seq`, `okay_to_free`,
`free_group`, `nontrivial_free`, `__libc_free`, `calloc`.
- The string instructions in general (layers/musl_asm.sl): `rep movs` of
  any element size (`x86i.rep_movsq` is for 8: its iteration and facts
  with the size a parameter), `rep stos` (memset's: no overlap question);
  an overlapping forward copy (s < d < s + n: each element read after
  writes reached it -- memmove's) its exact bytes, not undefined: the
  pointwise invariant of `x86.moved` with the source as it is then.
- Leaves at machine level: `a_or`, the other `__syscall*`, `memset`.

## 2. The engine, when a function needs it

- Stack objects: more than one object (`tr.obj1` is one 8-byte object;
  `alloc_objs` of several), objects read before their first store (none
  at -O0 yet).
- CFG -> loops: nested loops, a head reached at two structured loops, an
  exit of two loops, a callee refined inside a walk with loops of its own.

## 3. The CFG path's remaining engineering

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

## 4. The invariant and the laws

- `mallocng.abs_unique` (the abstract state determined by memory): the
  laws rest on it.
- `musl.free_step` (free always has a step), open in
  proofs/mallocng/claim.core.
- The C world owning only its statics, heap and stack objects.
- `slc heapcheck` on larger heaps: each byte's view membership (`held`)
  searches every group's slots (`in_reserved`), so a check grows with
  groups x bytes (~2 min at 60 groups; the ignored tests take 3.5 min).
  An interval form of the footprint per check would make it linear.

## 5. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap. It needs from exec (spec/linux/exec.sl):
the break within the user space (`brk_ok`), the auxiliary vector apart
from the data (`fresh_ok.auxv_ctx`) and not at null (`auxv_nz`); and the ABI's entry its
`brk_start_ok`.

The internal specs' `holds_in` has `shown` (`mallocng.shown_in`: the
allocator's bytes the C world's, its reserve's pages valid); the
claim's `rep` does not (the `frame` law says nothing of the world's
bytes). The top-level proof
(rep to holds_in at each allocator call) establishes it as it does
`tls_apart`: the thread block (the canary at fs + 40) apart from the
allocator's memory -- at the empty heap, from the context, the tables
and the auxiliary vector; after, the allocator maps only fresh pages.

## 6. Usability

- `rsimp` for the machine's semantics (proofs/linux_sys.core) instead of
  hand lemmas: a dispatch's live case is `rsimp(h, tag)` already; a
  statement's known outcome through the elaborator's sequencing forms
  (the outcomes' parts and their kinds' disequalities registered,
  core/records.core) should be too -- the hand lemmas `lx.top_*`,
  `lx.blk_*`, `lx.ib_*`, `lx.istep_*`, `lx.tlp_*`, `lx.lp_brk` then go.
  The rest of the proofs' `simp` that only rewrites: `rsimp` (simp kept
  for executing program paths). eff.rs' last simp: a stack call's
  argument count (`seq_len(list) = n`, `tr.eff_call1_s`) -- the list
  lemmas or rsimp through the proof API.

- `divergence()` takes a contract's body only of the `ct.dv_*` shapes (a
  step, a return after a choice or two); brk's and munmap's (branches,
  havocs) by hand (`mp.sy1_divw`, `mp.sy2_divw`, `mp.mun_divw`: never
  diverging with the requirement met -- a memory for the havoc there is;
  `contract` takes a `THM_divw` proven before it, only for a spec without
  parameters). A body's divergence by its structure (per statement), a
  havoc's choice by a given existence fact, would cover such specs.
- A leaf translation unit's C1 has no `.linked` (`contract` derives
  `THM_linked` from it): munmap's, unlock's linked forms by hand
  (`mp.mun_linked`, `mp.mun_calls_linked`), each callee's C1, typing, io
  and refinement listed.
- alloc_meta's remaining plumbing (am_run ~1120 lines): the context's
  usable words derived per memory stretch (`mp.ctx_usable` per offset,
  `mp.usable_pg` across a page change); the two three-case joins (`ht2`,
  `tm`) still split by hand; each exit's outcome built by `disj` /
  `ex_intro`. A closure deriving usability from the invariant
  (`mp.ctx_usable_w`, tried at every usable premise, its variables bound
  from the `using` facts) made the run several times slower: not that
  way -- a fact the run states once per memory, instantiated by step.

- `contract`: a callee never reached (the locks' `__lock`, `a_fetch_add`,
  `__wake`) linked as a_crash's spec by hand (`mp.rdl_linked` ..): C1's
  `.linked` covers only callees with a C1 of their own.
- `contract` for the rest: get_random_secret and memcpy (their `_fun`
  forms by hand, no procedure-level `refines` theorem); a procedure-level
  refinement's ghost bookkeeping (`mp.ag`'s ~70 lines: the precondition's
  clauses read from the union, the ghost part's update) and `THM_q` (a
  `step` over the run lemma) by the procedure too; linking a function
  whose C1 has no `.linked` (alloc_meta over dequeue_head:
  `mp.am_over_leaves` by hand).
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
