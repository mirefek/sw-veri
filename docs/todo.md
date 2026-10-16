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

- `__malloc_alloc_meta` by its spec (`alloc_meta_spec`: a meta taken, or
  0): the free metas' head (dequeue_head), the area's next meta, a new
  area from brk or from the mmap'd reserve (mprotect'ed); the first call's
  secret (get_random_secret). Needs the World-level specs of `__mmap`,
  `__mprotect`, brk (`__syscall1(12, ..)`) and `___errno_location`; a failed
  mmap of the meta areas' doubling size keeps `meta_alloc_shift <= 34`
  (`TASK_SIZE`).
- CFG -> loops: alloc_group has four loops one after another (heads 7, 12,
  16, 54). `g.cut_loops` takes one loop's data (H, bs, ks); several loops
  need them per head, chosen under binders. The loop finder already
  accepts a loop exiting into the next loop's head (uncommitted in
  slc/cli/src/c1/gref/gloop.rs). Later: nested loops, a head reached at
  two structured loops, a callee refined inside a walk with loops of its
  own.
- alloc_group's CFG C1: stops at 404413, a byte store of `dl`
  (`tr.store8_b`'s premise); then the rest of its blocks.
- Specs by purpose of the loop functions (alloc_group, step_seq): the
  loop's invariant and variant at its head stated over the abstract
  state, the code's loop refined to it (as try_avail's span loop).

## 3. Then: the remaining functions

- alloc_slot's machine-code form (`mp.as_implements`): with alloc_group's
  -- they call each other (`mp.as_call`, `mp.agr_call`), the composition
  by induction on the class (a nested group's class larger) --.
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
holding for the empty heap.

## 7. Usability

- Generate the function-level C2s and compositions (one instance of
  `g.fun_res` / `g.fun_res_ghost` and `tr.implements_refine` each).
- A call to a callee by its own contract still needs the trivial fact
  that the callee refines itself (`agself`, `dbself` in `mp.ta_run`): the
  call rule could take it as given.
- `ex_intro({..})` inside `taut(..)` misparsed as a binder (hit again in
  `mp.ta_q`: the inner witness needs its own `have`); the list lemmas of
  proofs/translate_call.core to core/list.core.
- A function's divergence lemma (`mp.ta_divg`) copies the spec's
  elaborated body verbatim (40 lines, parentheses counted by hand): one
  lemma per spec shape (choices, havoc, return), or the checker deriving
  the body from the spec's definition, would remove it.
- `step`'s names: the continuation first, then the call's facts; a
  wrong guess shows up only as "names not used" or an odd destructuring
  error. The message could print which name got what.
- A shadowed hypothesis name (an inner `obtain .. hx` hiding the theorem's
  `hx`) surfaced as "premise not discharged" far away: warn on shadowing.
- Exploring a walk: `print` and then reading "the obtained x occurs in
  the result" is the way to see a continuation; a `goal` / `show ?`
  command printing the current goal and facts would be direct.
- `defs(..)` unfolds the goal only; a fact needs `expand` first (ctx_free
  in `mp.co_unt`): `defs` could unfold the facts it is given too.
- `arith`: `x in bits(n)` for n above 100 is not arithmetic (bits(128):
  narrowed by hand, `mp.hdr_new`); `ord_lt(0, n)` needs `n in omega` given;
  no `-1` literal (`int_neg(1)`); an inline arith inside `taut` needs its
  goal written out.
- Record updates in another order (`fn_update` with distinct keys): simp
  does not normalize them; `mp.clear_perm` swaps four times by hand.
- A call's registers: the step rule picks a lemma per list of argument
  widths from a fixed table (slc/proof/src/lib.rs, `step_regs_ex`), each a
  hand-written pair `gc.regs*` / `gc.regs*_ex` (`gc.regs_32_64` for
  alloc_group's call); one lemma over any list of widths would end that.
- The rules' standard form: the statics' names, `and r8, 2^k - 1`, `[p + 0]`
  as equations of N (docs/overview.md).
- `rewrite(e, f)` rewrites every occurrence, also inside abbreviations
  that unfold to the term (`rewrite(sym(i0), ..)` turning each `0` of
  `mp.res_abs(A2, GN, 0)` into `i`; `rewrite(p0, ..)` each `pow2(0)` in
  it): a `subst` with its motive written out, or the occurrences selected
  (`rewrite(e, p, {k}..)`, counted in the unfolded term), is the workaround.
  A rewrite keeping abbreviations folded would do.
- The kernel normalizes `pow2(0)` to `1` in a step's output but not in a
  `let` or a lemma's instance; the two forms then fail to match
  (`mp.as_run`'s V3).
- `simp` does not evaluate `seq_one(x)[0]` (`at({..})` does); `arith`
  takes `x in omega` only as its own fact, not as a conjunct of one
  (`x0 in omega && x1 in omega` destructured first).
- The invariant's constant tables (the class table, a_ctz_32's) are
  stated, framed and read each by its own copy of the same lemmas
  (`mp.mf_classes` / `mp.mf_debruijn`, `mp.lf_*`, `mp.*_table`): one
  predicate for a read-only table, framed once, would serve both.
- A World spec's divergence lemma and its ABI form (`mp.X_divw`,
  `mp.X_abi`) are the same 15 lines per function, differing only in the
  spec function's shape (`ct.fun_divg` / `_v` / `_v0`) and the body's
  (`ct.dv_havoc`, `ct.dv_exc_a`, ...): written from one template for eleven
  functions. The checker could derive them from the spec's definition.
- A clause added to a predicate breaks every positional destructuring of
  it (`have _ _ .. c11 _ := expand(cok, ctx_ok)`: 22 sites for ctx_ok's
  new last clause; `rep`'s, `metas_partition`'s): named clauses
  (`{cy = name}`) are immune, so the invariant's predicates could all
  name theirs (ctx_ok does not), or the checker could warn on positional
  use of a predicate with more than a few conjuncts.
- Finding an existing lemma: `mp.qu_q` was written a second time before
  the checker said it was proven; a search by statement shape (or by the
  names it mentions) would help.

## Later

- Multi-threading; traces of infinite runs (I/O specs that run forever).
- Optimized code: the cut-point theorem between two CFGs, an optimization
  layer, DWARF location maps; other compilers (LLVM IR).
- Beyond malloc: signals, varargs, realloc, filesystem, networking, C types
  above raw memory, whole executables (busybox).
- Model: file mappings, recursion, fault ordering across two pages.
