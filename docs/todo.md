# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

## 1. Next: the program's claim (tests/test_malloc.c)

The claim's binary is a client of malloc and free only
(tests/test_malloc.c: blocks filled with patterns, half freed and
allocated again, all checked; exit 1 when malloc returns NULL, 42 when a
pattern changed, else 0). The claim `musl_program` (stated, open:
layers/claim_program.sl, `slc claim --program-exits 0,1`): every run of
the process from an unprivileged exec state that ends exits with 0 or 1,
or dies of a stack overflow as abi.sl's `abi_function` raises it; no
other crash, never exit 42. Runs that never end are allowed (§2).
- (c0) `world_ok` at main's first call: its page clauses and the stack
  in the user space from the bridge (abi.sl's `stack_reserve`, the world
  without the stack's pages), in (c).
- (c) `main` (its spec: layers/test_malloc.sl's `main_spec`, 0 or 1, the
  memory outside the allocator's and errno kept; the helpers done:
  proofs/test/helpers.core). Left:
  - what a block's bytes keep across the other calls (alloc_frame,
    live_apart, owned_private); a world written in a block still world_ok
    (live_apart, code_at unwritable). (The call rules: `tm.malloc_q` /
    `tm.free_q` in proofs/test/malloc_calls.core, over `tm.mcall` /
    `tm.fcall`, which musl's code meets: `mp.top_call`, `mp.free_low_all`.)
  - main's C2: four loops, the invariant over the ghost blocks -- p[k]
    live, its size, its pattern; the memory outside the allocator's at
    main's start kept (main_frame); the array object none of the
    allocator's (step_ok's new owned bytes no stack object); then
    `abi.implements(Heap.ghost, main_at, main_spec)` by
    `tr.implements_abi_l` with main's C1.
- (d) After main: stage2's `exit(main(..))` -- musl's `exit`,
  `__funcs_on_exit`, `__libc_exit_fini` (.fini_array, `_fini`),
  `__stdio_exit`, `_Exit` (exit_group): C1, specs, C2, as the startup's.
- (e) The whole run: startup linked with main as a callee by its
  contract (not a breakpoint), the invariant from `musl.init` at its
  entry, the exit path after; the claim proven.

The malloc claim's `Init` is about the runs that reach `main`, vacuous
if none did; (e) shows nothing more of that (a witness that some exec
state reaches main is a separate statement).

## 2. Termination (planned)

The program claim allows runs that never end. To exclude them: every
call of malloc and free returns (or overflows the stack), and the
startup and exit paths end.
- malloc.sl's specs and mallocng's: no divergence (the layer's specs may
  diverge now -- check each); the loops' variants: alloc_group's, the
  activation and span loops (try_avail), dequeue's, the free path's
  recursion (nontrivial_free <-> free_group: depth-indexed already);
  system calls returning (brk, mmap, munmap, mprotect in the model).
- C1 keeps divergence (a diverging machine run only for a diverging
  GIMPLE one): termination proven at GIMPLE level, carried down.
- The startup's and exit's loops (auxv, the constructors, TLS copy).
- The statement: every run ends -- exit 0/1 or a stack overflow.

## 3. Shared libraries (planned)

The standard setup: the program dynamically linked, musl's libc.so (also
its dynamic linker, /lib/ld-musl-x86_64.so.1) loaded at a random base.
- The exec model (spec/linux/exec.sl, static non-PIE only now):
  PT_INTERP -- the interpreter from the file system mapped at a random
  base, auxv's AT_BASE / AT_PHDR / AT_ENTRY for it; a PIE program at a
  random base.
- The library's claim about libc.so alone: malloc and free correct
  wherever it is loaded -- C1 proofs relative to the load base (code at
  base + offset, RIP-relative data; `implements2_at` / `loaded` take a
  base already, the engine and the generated steps do not).
- Startup is the dynamic linker (ldso/dlstart.c, dynlink.c):
  self-relocation, the program's and libc's relocations (GOT entries for
  malloc and free), TLS, then the program's `_start`; calls through the
  PLT.
- The program's claim then for a program and the library file: proven
  from the library's claim and the program's own proofs.

## 4. The engine, when a function needs it

- Frames with a frame pointer (`push rbp; mov rbp, rsp`, rbp-based
  slots): C1 knows rsp-based frames only (musl's -fomit-frame-pointer);
  the test program is compiled so too (scripts/build-musl.sh).
- Narrow return values (a char returned in al, the rest of eax any):
  C1 wants the register to hold the value's width; the test's helper
  returns an int.

- The entry variants entry_np, entry0p generic like tr.entry_n,
  tr.entry0 (optional).
- Stack objects read before their first store (none at -O0 yet); the
  single object's older path (alloc_at, tr.astore_r: get_random_secret)
  and the several objects' one unified (optional).
- CFG -> loops: nested loops, a head reached at two structured loops, an
  exit of two loops, a callee refined inside a walk with loops of its own.
- The string instructions in general (layers/musl_asm.sl): `rep movs` /
  `rep stos` of any element size (`x86i.rep_movsq`, `x86i.rep_stosq` are
  for 8: their iterations and facts with the size a parameter); an
  overlapping forward copy (s < d < s + n: each element read after
  writes reached it -- memmove's) its exact bytes, not undefined: the
  pointwise invariant of `x86.moved` with the source as it is then.
- Flags kept across instructions (tr.ptf / tr.lvf,
  proofs/translate_memset.core): `_f` forms exist for the rules memset
  needs (mov r64, r64; the indexed 64-bit store; the spec's plain
  reductions); others as a function needs them.
- The x86 instruction lemmas each unfold the instruction's semantics by
  simp for their own addressing form (proofs/x86_insn.core, ~30 s
  uncached; `lock_or32_b` 5.5 s, `cas32_b` 3.6 s, the [rsp + d]
  read-modify-writes ~1.5 s each): one lemma per instruction shape with
  the effective address a parameter, each form by its address equation
  (as tr.rsp_bd_ea), if cold checks need to be faster.

## 5. The CFG path's remaining engineering

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

## 6. The invariant and the laws

- The C world owning only its statics, heap and stack objects.
- `slc heapcheck` on larger heaps: each byte's view membership (`held`)
  searches every group's slots (`in_reserved`), so a check grows with
  groups x bytes (~2 min at 60 groups; the ignored tests take 3.5 min).
  An interval form of the footprint per check would make it linear.


## 7. Usability

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
