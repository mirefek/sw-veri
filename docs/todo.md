# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

## 1. Next: the remaining functions

alloc_meta, alloc_slot and alloc_group are verified at machine level from
the configuration alone (`mp.am_machine`, `mp.as_machine`,
`mp.agr_machine`); the locks and munmap too (`mp.rdl_linked` ..
`mp.unl_linked`, `mp.mun_linked`), `__libc_malloc_impl`
(`mp.mi_machine`) and the `malloc` symbol (`mp.dm_machine`,
proofs/mallocng/fun/malloc_machine.core), all against malloc's purpose spec.

Next: free's purpose proofs. Its translation unit's C1 is done
(proofs/mallocng/machine/c1_free.core; free.c's copies of malloc.c's
functions against malloc.c's CFG forms, their purpose proofs the same).
- `free_group` and `nontrivial_free` call each other (a nested group's
  slot freed in its container group). Their specs (`freed_back`: the
  freed slot, reserved, given back; what is let go returned) carry no
  depth; the proofs go by induction on the groups in use (free_group at n
  from nontrivial_free at n - 1, that at n from free_group at n), at
  machine level, no recursion in the engine. Done: the model of a slot
  freed with its group kept (proofs/mallocng/model/freeing.core:
  `mp.holds_m_unres`, `mp.qu_step_g` -- the freed bit first, on a memory
  made for it, then the queue); of a group given back
  (proofs/mallocng/model/dropgroup.core: `mp.drop_in_own`,
  `mp.drop_in_nest` -- out of `used`, its meta taken until free_meta, a
  nested one's container slot reserved; the invariant first on the old
  memory, then on the new by `mp.holds_held`,
  proofs/mallocng/model/heldonly.core). Both runs are done:
  `mp.fg_run` (proofs/mallocng/fun/free_group.core, nontrivial_free
  called at one group fewer) and `mp.nf_run`
  (proofs/mallocng/fun/nontrivial_free.core, free_group called at the
  same count), and the induction (`mp.fg_nf`). Open: the refinements to
  the specs.
- `__libc_free` and the `free` symbol are done (`mp.lf`, `mp.fr`; their
  contracts: proofs/mallocng/fun/libc_free.core, free.core); next
  `calloc`. `tls_apart` / `errno_apart` (and
  rep's clauses) put the thread's words in none of the allocator's
  ranges -- so in no live block, no reserved slot: free's steps may unmap
  the block freed; the top level's argument (section 5) covers the whole
  ranges.
- free.c's copies of malloc.c's functions: their contracts by `c1 P`
  (proofs/mallocng/fun/free_copies.core; get_meta's done), their linked
  forms (`P.linked`, as cfg.core's for malloc.c's) where free.c's
  callers need them.

The claim is malloc and free (calloc later: section Later), proven in
the chain (proofs/mallocng/claim.core, the claim of the -O0 binary first
in the chain: `@claim`) from one open lemma: `musl.init` (section 5).
Next that.
- The string instructions in general (layers/musl_asm.sl): `rep movs` /
  `rep stos` of any element size (`x86i.rep_movsq`, `x86i.rep_stosq` are
  for 8: their iterations and facts with the size a parameter); an
  overlapping forward copy (s < d < s + n: each element read after
  writes reached it -- memmove's) its exact bytes, not undefined: the
  pointwise invariant of `x86.moved` with the source as it is then.
- Flags kept across instructions (tr.ptf / tr.lvf, proofs/translate_memset.core):
  `_f` forms exist for the rules memset needs (mov r64, r64; the indexed
  64-bit store; the spec's plain reductions); others as a function needs
  them.
- Leaves at machine level: `a_or`, the other `__syscall*`.

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
- The elaborated layers (gimple.core, generated definitions) kept in
  memory, elaborated in the checker from the .sl files, as the `steps`
  and `text` lines make their facts. The readable GIMPLE (cfg*.sl) stays
  text: it is what a person reads.
- The step theorems take ~70 ms each (1069 encodings, ~80 s of the
  `steps` line's 90 s; only after the binary changes): the decoder's
  `members` and the `exec_insn` unfolding, per encoding.

## 4. The invariant and the laws

- The C world owning only its statics, heap and stack objects.
- `slc heapcheck` on larger heaps: each byte's view membership (`held`)
  searches every group's slots (`in_reserved`), so a check grows with
  groups x bytes (~2 min at 60 groups; the ignored tests take 3.5 min).
  An interval form of the footprint per check would make it linear.

## 5. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap (`musl.init`, the claim's last open lemma).
The binary as linked (gcc's crtbegin included). The steps:
- (a) Readable GIMPLE of the startup units (src/env/__libc_start_main.c,
  __init_tls.c, __stack_chk_fail.c, crt/crt1.c; dumped): `slc gimple`
  lacks string literals, function addresses as values, indirect calls,
  the empty `asm` hiding stage2's pointer, `volatile` pointer types,
  `Phdr`.
- (b) Code without musl C: readable models (as musl_asm.sl's) of
  `_start`, `__set_thread_area`, `memset`, crti/crtn's `_init`, and
  gcc's `frame_dummy` -> `register_tm_clones` (the init_array's one
  constructor: no memory, its branch on `__TMC_END__ - __TMC_END__` = 0,
  so no effect).
- (c) `main` as a callee: an external function whose contract requires
  the invariant at the empty heap; stage2's call through the `main`
  pointer meets it (C2). Refinement of whole runs says nothing of a
  state in between, so the bridge gets a stop form: a function's
  disciplined run stopping at rip = t (`main_at`), the stop an outcome
  "at main" that only `main`'s contract allows (its precondition
  holding). The path to `main` (`_start`, `_start_c`,
  `__libc_start_main`, stage2) in that form; the callees returning
  before it (`__init_libc`, `__init_tls`, the leaves `memset`, `memcpy`,
  `__syscall*`, `a_crash`, `__get_tp`) too -- their runs never at t --,
  each proven once: the normal contract (malloc's and free's use)
  derived from the stop form by one bridge theorem (a run never at t is
  the same run without the stop).
  Done (proofs/translate_stop.core): the stop run, its contract
  (tr.implements_stop), the normal one from it (tr.implements_of_s, the
  spec never raising at main), the contract from the claim at the entry
  (tr.entry_s: breakpoint rip = t, relation tr.at_t), the call split
  (tr.run_split_ks); at_main no undefined behaviour in the bridge.
  proofs/translate_stop_call.core: the call rules for any breakpoints
  with t's (tr.callee_sim_g; the callee's contract with the stop, k, or
  never stopping), the call of main itself (tr.call_main: the claim at
  its entry tr.at_t, the spec tr.raises_main), calls through the code
  map `fptr` (tr.code_ok, tr.callee_ind_g; an undefined entry holds any
  contract), the entry (tr.entry_gk, tr.entry_nk generic; tr.fin_k,
  tr.ub_k). A function never stopping (k false) has the normal contract
  too (tr.implements_ns_at): shared leaves proven once, in that mode.
  The engine's stop mode: `c1 FN SPEC P stop T` / `nostop T`
  (breakpoints `rip = T`, relation `k && tr.at_t`; the entry by
  tr.entry_nk/gk; callees' contracts tr.implements_stop with the
  caller's k, calls by tr.call_st/tr.call1_st). `nostop` gives the
  normal contracts too: a_ctz_32 is proven so.
  Calls through the code map (`call *%reg` against `call(fptr[p], ..)`,
  tr.calli_st/calli1_st, hypothesis tr.code_ok); a stop inside a loop
  (tr.loop_cut, tr.cfg_lvk: the relation `(cut && inv) || (bkp && bka)`,
  bka closed under the same exceptions, tr.exc_closed); the rest after a
  call never returning (tr.q_some_e, tr.raise0_ub). C1 in the stop mode:
  `_start_c`, `__libc_start_main`, `libc_start_main_stage2`,
  `__libc_start_init` (its init_array loop; proofs/mallocng/machine/c1_start.core).
  Left: contract.rs linking the stop contracts (an aligned call's from
  the callee's _u contract; k false's into k true's); the entry variants
  entry_np, entry0p generic like tr.entry_n, tr.entry0.
- (c') The startup mode. Until `__init_tp` there is no thread pointer
  (fs 0) and until `__init_ssp` no canary; `__init_tp` sets fs inside
  calls that must keep it (`__init_tls`, `__init_libc`), `__init_ssp`
  writes the canary in C. The main mode (the ABI as it is: the canary
  hidden, `thread_ok`/`canary_ok` at entries and calls, fs restored)
  holds from `main` on; every function before it runs, whole, in the
  startup mode: nothing hidden (the world's `c_bytes` all bytes -- the
  mode read from Objs), no thread requirement, fs as the world has it.
  - GIMPLE: `call0` (and call1_0, ..): no thread check, fs not
    restored; `slc gimple --startup` emits it for the startup units (all
    their functions run before main). `call` and the C2 proofs unchanged.
  - Bridge: done -- the claims' objects v an Objs value (v.c_bytes the
    run's C bytes: the mode, tr.mainv); the contract in either mode b
    (tr.impl_m, tr.mtv over the claim's V and the entry's world tr.vw(b,
    ..), tr.vok, tr.eok), its entry (tr.entry_nkm, entry0km, entry_gkm,
    fin_km); the call machinery generic in b (callee_ready_m, post_call_m,
    callee_sim_sm/gm, ..; gc.cm: call or call0), the main lemmas its
    b = true instances; the startup rules tr.call0_st, calli0_st,
    call1_0_st, calli1_0_st. Engine: `c1 .. stop T startup`; the startup
    units generated with `--startup`; C1 of `_start_c`, `__libc_start_main`,
    `libc_start_main_stage2`, `__libc_start_init` in the startup mode.
    Left: `call0_objs` (`__init_libc`'s aux array); a body using neither
    mode's rules gives both contracts (memcpy, memset proven once); Init's
    top turns the stop's startup view (tr.at_tm(false, ..)) into main's
    world.
- memset (src/string/x86_64/memset.s; layers/musl_asm.sl, its CFG
  musl_asm_cfg.sl): C1 in the startup mode done (proofs/translate_memset.core:
  stores at computed offsets, `g.mem_defined_s`; the `test` kept to its
  `jne`; `rep stosq` as one store of x86.fillv's words, x86.store_cat).
  Left: its CFG ⊑ structured (refines), its purpose spec (the n bytes at
  d all c's low byte) and C2, the call rule of `call memset` against
  GIMPLE's `st_bytes` (`__init_libc`'s zeroed aux array).
- (d) C1 of the startup functions (~560 instructions), C2 against
  purpose specs: `__init_libc` (auxv into `libc.auxv`, the program name,
  environ; unprivileged: the secure path skipped), `__init_tls` (the
  program headers, builtin TLS, `__init_tp`: arch_prctl,
  set_tid_address), `__init_ssp` (the canary from AT_RANDOM),
  `__libc_start_init` (`_init`, the init_array).
- (e) The top: exec_state to the C world at `_start`; at `main` the
  empty heap's rep (the context zero from .bss, the thread block in
  .bss apart from the allocator's ranges) and `owned` within the
  statics, the thread descriptor and the auxv.

It needs from exec (spec/linux/exec.sl):
the break within the user space (`brk_ok`), the auxiliary vector apart
from the data (`fresh_ok.auxv_ctx`) and not at null (`auxv_nz`); and the ABI's entry its
`brk_start_ok`.

The internal specs' `holds_in` has `shown` (`mallocng.shown_in`: the
allocator's bytes the C world's, its reserve's pages valid); the
claim's `rep` does not (the `frame` law says nothing of the world's
bytes). The top-level proof
(rep to holds_in at each allocator call) establishes it as it does
`tls_apart`: the thread block (the canary at fs + 40) apart from the
allocator's ranges (its bytes, the live blocks) -- at the empty heap, from the context, the tables
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
- calloc (its spec in layers/malloc.sl, not claimed): calloc.c's C1
  (`calloc`, `mal0_clear`'s page loop) and memset (`rep stos`). musl
  returns a block unclear when `__malloc_allzerop` says its group has its
  own mapping: malloc's spec must then promise such a block's bytes zero
  (fresh anonymous pages zero in the model; the group's slot not reused
  after a client wrote it -- to check against free's `MADV_FREE`).
- realloc (no spec yet).
- Beyond malloc: signals, varargs, filesystem, networking, C types above
  raw memory, whole executables (busybox).
- Model: file mappings, recursion, fault ordering across two pages.
