# To do

The current plans, in order. When an item is done it is deleted here and
summarized in docs/done.md.

The first milestone is reached: both claims are proven (`musl_malloc`,
`musl_program`), the program's with termination. Next comes the
usability debt that the milestone left (§1). The long-term directions
(§3) come after it, each designed in a principled way before it is
built.

## 1. Next: usability and speed

The aim:
- an efficient, intuitive language that states high-level ideas
  directly, with little plumbing; proofs read as ideas rather than
  bookkeeping;
- a fast checker, cold as well as cached, that never accepts anything
  unsound.

Trusted extensions: a check that an algorithm does quickly, but that is
laborious through the kernel, may be a trusted extension that guarantees
its validity. Each new one, and each moving work from the kernel into an
extension, comes with a switch that turns the trust off: the same check
then goes through the kernel or lower extensions. (Most of the existing
extensions have no such switch.)

Every change is timed: `SLC_TIMES=1 scripts/check.sh --no-cache` for
each file's time and memory, `C1_STATS=1` for each refinement's,
`SLC_RECHECK=PATH` to check one file again with the rest cached,
`SLC_SLOW_BY=MS` for each `by` step taking MS ms or more,
scripts/sample-stacks.py (with check.sh's `SLC_WRAP`) for where the time
goes.

### 1.1 `simp` the default rule, `symex` only for program runs

The goal is usability: one intuitive name that is fast wherever it is
used, not the removal of trusted code. The two simplifiers are now named
by what they do:
- `simp` (formerly `rsimp`, slc/proof/src/rsimp.rs, untrusted): Lean-like
  rewriting with the given facts, definitions and registered `simp`
  rules; as a goal rule a fixed sequence (a conjunction conjunct by
  conjunct, typing for a membership, rewriting, then taut / arith with
  the facts about the normal form's atoms). Fast and predictable.
- `symex` (formerly `simp`, slc/kernel/src/ext/simp.rs, trusted, about
  6,000 lines): the path simplifier, for symbolic execution of program
  runs. It searches, so it is slow where nothing is executed.

`symex` calls in the proofs: 5,777 (were 20,052 before scripts/migrate-
simp.py moved the calls `simp` proves as fast, by the shadow's log,
`SLC_SHADOW=rsimp`, scripts/shadow-report.py). What is left, by the last
shadows (the files but nominal_size.core, whose shadow runs out of
memory):
- runs of programs from facts (`o = ok(..)` from `runs(..)`, keep
  calls): `step`'s, proof by proof;
- goals symex proves with its path reasoning: implications and cases of
  the facts, witnesses of existentials, contradictions among facts
  (`false`), memberships and records under premises;
- evaluation of closed terms (a table's entry): the trusted eval proves
  only about 25 of them;
- the fact form `symex(h)` (a fact simplified), not shadowed yet.

The plan, in order (each step measured: speed comes first):
- The program runs: `step` in place of `symex(.., keep(..))` where a
  proof runs a program, proof by proof.
- The typing procedure's gaps (the shadow's failures): `rec_and` states
  (`m in rec_and(Machine, ..)`), program sets (`pair(s, o) in
  set_select(univ(1), ..)`), terms bounded by a definition's arithmetic
  (`page_of(x) in set_select(omega, ..)`), facts under premises.
- The outcome equations as registered `simp` rules (pair and outcome
  injectivity), and a normal order of updates at distinct keys (`symex`
  does not normalize them either; `mp.clear_perm` swaps four times by
  hand).
- `simp`'s speed: the rules indexed by their left side's head (only
  those that can match a node tried).
- The machine's semantics (proofs/linux_sys.core) by `simp` instead of
  hand lemmas. A dispatch's live case is `simp(h, tag)` already. A
  statement's known outcome through the elaborator's sequencing forms
  (the outcomes' parts and their kinds' disequalities registered,
  core/records.core) should be too. Then the hand lemmas `lx.top_*`,
  `lx.blk_*`, `lx.ib_*`, `lx.istep_*`, `lx.tlp_*` and `lx.lp_brk` go.
- eff.rs' last `symex`: a stack call's argument count (`seq_len(list) =
  n`, `tr.eff_call1_s`), by the list lemmas or `simp` through the proof
  API.

### 1.2 Speed

- Measure first: per-file and per-proof times of an uncached check, so
  that the slowest steps are known rather than guessed.
- Trusted kernel extensions where a derived procedure is slow. Each one
  documents how it reduces to the kernel's rules, as the existing ones in
  `slc/kernel/src/ext/` do, and its pinned symbols. Candidates, from the
  times known now:
  - the x86 instruction lemmas (proofs/x86_insn.core, about 30 s
    uncached: `lock_or32_b` 5.5 s, `cas32_b` 3.6 s, the [rsp + d]
    read-modify-writes about 1.5 s each). Each unfolds the instruction's
    semantics by `symex` for its own addressing form. Instead: one lemma
    per instruction shape with the effective address a parameter, each
    form by its address equation (as `tr.rsp_bd_ea`);
  - the `steps` line (35 s, after each change of the binary; the step
    theorems are x86.step_one's instances now): the interpreter decoding
    each address (`decode_facts`, about 6 s), the per-address `at_`
    theorems (a `symex` of `exec_body` each, about 6 s), the members of
    each encoding's decoding;
  - the loops' label claims (`lab_all`): each label's claim is the whole
    premise instantiated there, about 1.5 s per label in alloc_group's
    56, though only the heads' and exits' are not vacuous. Split on the
    heads (and exits) alone, so that the rest are vacuous at once.
- Variables reference counted (a name and arity freed with its last
  term, identity by pointer, not a table index). Now a proof's variables
  are dropped only at its end (`Env::begin_locals` .. `end_locals`).
- An uncached check is about 220 s (run-to-run noise about 10 s), at
  most 0.45 GB (was 1407 s, 2.3 GB, before hash-consing, the DAG-aware
  walks and memos, the projection chains, the intern table's own-entry
  removal, the cheap symbol lookups, simp's conditional rules under
  binders by head, x86.step_one, arith's facts without the branching ones
  first). Largest: cfg.core 39 s, c1.core 31 s, the `steps` line 35 s. alloc_group's refinement is 28 s: 84,000
  `g.low_rw` rewrites and 50,000 `g.ref_low` compositions, each a lemma
  instance over the whole lower term (`C1_RULES=1` counts them). Profile
  with `SLC_CACHE_AS=any GREF_ONLY=alloc_group_ref C1_KEEP_GOING=1
  C1_PHASES=1 C1_PROF=1 C1_RULES=1 SLC_RECHECK=machine/cfg.core
  scripts/check.sh` (about 40 s).
- Reads through stores by hand (`mp.st_out`, `mp.wr32_out`, `mp.rd_at4`
  ..): about 15 left in fun/ (activate_group.core, alloc_group.core,
  alloc_meta.core, alloc_slot.core, a value just written read back in
  lists.core, nontrivial_free.core, set_size.core, try_avail.core), where
  a stated `.. by mem(..)` reads them.
- The C1 engine's lemma premises by `symex` (`simp0()`, `simp_l()`,
  api.rs; c1.core about 37,000 after the memo): a literal key's `k in
  dom(fn_update(..))` and `fn_update(..)[k] = v` now by the update lemmas
  (no search). Left, by time: the `mkprog(..)` existentials of the call
  rules (about 10 s), `tr.hsub(ite(..))` and its `ite` (about 7 s, 176
  calls each), small closed goals (`int_lt(12, 34)`: about 4 s; the
  evaluator tried first was slower overall -- it also took the large
  closed goals). `types` tried first per call was no faster (its fact
  index built each time).
- The elaborated layers (gimple.core, generated definitions) kept in
  memory, elaborated in the checker from the .sl files, as the `steps`
  and `text` lines make their facts. The readable GIMPLE (cfg*.sl) stays
  text: it is what a person reads.
- The structured form generated and checked in one run (`slc gimple`
  running the refinement); a callee's refinement a theorem of its own,
  not walked again in each caller.
- `slc heapcheck` on larger heaps: each byte's view membership (`held`)
  searches every group's slots (`in_reserved`), so a check grows with
  groups × bytes (about 2 min at 60 groups; the ignored tests take
  3.5 min). An interval form of the footprint per check would make it
  linear.

### 1.3 The proof language

- `arith`:
  - `x in bits(n)` for n above 100 is not arithmetic (bits(128):
    narrowed by hand, `mp.hdr_new`);
  - `ord_lt(0, n)` needs `n in omega` given;
  - no `-1` literal (`int_neg(1)`);
  - an inline `arith` inside `taut` needs its goal written out;
  - `x in omega` is taken only as its own fact, not as a conjunct of one
    (`x0 in omega && x1 in omega` destructured first).
- `step`:
  - outcome construction by witness matching. Each exit's outcome is
    built by `disj` / `ex_intro` now, and the three-case joins (`ht2`,
    `tm` in alloc_meta) are split by hand;
  - its names: the continuation first, then the call's facts. A wrong
    guess shows up only as "names not used" or an odd destructuring
    error. The message could print which name got what.
- `ex_intro({..})` inside `taut(..)` is misparsed as a binder (hit again
  in `mp.ta_q` and `gc.regs_one`: the inner witness needs its own
  `have`).
- `search`: by patterns and by the goal; not yet by a premise's shape
  (what a fact in hand can be fed to), nor ranked by how much of the
  pattern a fact's statement is.
- alloc_meta's remaining plumbing (am_run, about 1120 lines): the
  context's usable words derived per memory stretch (`mp.ctx_usable` per
  offset, `mp.usable_pg` across a page change). A closure deriving
  usability from the invariant (`mp.ctx_usable_w`, tried at every usable
  premise, its variables bound from the `using` facts) made the run
  several times slower: not that way. Instead, a fact the run states once
  per memory, instantiated by `step`.

### 1.4 Bookkeeping the tool should do

- `divergence()` takes a contract's body only of the `ct.dv_*` shapes (a
  step, a return after a choice or two). brk's and munmap's (branches,
  havocs) are by hand (`mp.sy1_divw`, `mp.sy2_divw`, `mp.mun_divw`: never
  diverging with the requirement met, since there is a memory for the
  havoc). `contract` takes a `THM_divw` proven before it, only for a spec
  without parameters. A body's divergence by its structure (per
  statement), a havoc's choice by a given existence fact, would cover
  such specs.
- `.linked` facts:
  - a leaf translation unit's C1 has no `.linked` (`contract` derives
    `THM_linked` from it): munmap's and unlock's linked forms are by hand
    (`mp.mun_linked`, `mp.mun_calls_linked`), each callee's C1, typing,
    io and refinement listed;
  - a callee never reached (the locks' `__lock`, `a_fetch_add`,
    `__wake`) is linked as a_crash's spec by hand (`mp.rdl_linked` ..):
    C1's `.linked` covers only callees with a C1 of their own.
- `contract` for the rest: get_random_secret and memcpy (their `_fun`
  forms by hand, no procedure-level `refines` theorem); a
  procedure-level refinement's ghost bookkeeping (`mp.ag`'s about 70
  lines: the precondition's clauses read from the union, the ghost
  part's update) and `THM_q` (a `step` over the run lemma) by the
  procedure too; linking a function whose C1 has no `.linked`
  (alloc_meta over dequeue_head: `mp.am_over_leaves` by hand).
- User proofs on a CFG (an invariant per label) for functions with no
  structured view.

### 1.5 Cleanups

- The bitfield store `ms.stbfw_det` (fun/alloc_group.core) belongs with
  ops.core's store lemmas.
- The trivial facts that a callee refines itself (`agself`, `dbself` in
  `mp.ta_run`, `amself`, `taself`) are no longer needed
  (`gc.calls_self`): to be removed.
- The list lemmas of proofs/translate_call.core (`tr.seq_one_type`,
  `tr.concat_list`) to core/list.core.
- A call's registers read back: the inversion lemmas `gc.regs1` ..
  `gc.regs_32_64` per list of widths remain (the existence side is
  general now); `gc.reg_at` reads one register of any list.
- The rules' standard form: the statics' names, `and r8, 2^k - 1` and
  `[p + 0]` as equations of N (docs/overview.md).
- The invariant's constant tables (the class table, a_ctz_32's) are
  stated, framed and read each by its own copy of the same lemmas
  (`mp.mf_classes` / `mp.mf_debruijn`, `mp.lf_*`, `mp.*_table`): one
  predicate for a read-only table, framed once, would serve both.
- Lemmas stated twice: `ms.imul_4` / `_16` and the generated contexts'
  effect lemmas (`dqtc.eff_meta_next` .. repeated in each `..tc` of
  `slc steps`): one shared set.
- The entry variants entry_np and entry0p made generic like `tr.entry_n`
  and `tr.entry0` (optional).
- Stack objects: the single object's older path (`alloc_at`,
  `tr.astore_r`: get_random_secret) and the several objects' unified
  (optional).

## 2. Open from the milestone: a reached main

The malloc claim's `Init` is about the runs that reach `main`, and it
would hold vacuously if none did. A witness that some exec state reaches
`main` is a separate statement, not made yet. The program claim says
that every run exits with 0 or 1 or overflows the stack, but it does not
state that an exec state exists either.

## 3. Long-term directions

Each is designed in a principled way before it is built: which level it
belongs to, what it adds to the layers, and how the existing claims
compose with it (docs/overview.md's levels).

### 3.1 Shared libraries

The standard setup: the program dynamically linked, musl's libc.so (also
its dynamic linker, /lib/ld-musl-x86_64.so.1) loaded at a random base.
- The exec model (spec/linux/exec.sl, static non-PIE only now):
  PT_INTERP, the interpreter from the file system mapped at a random
  base, auxv's AT_BASE / AT_PHDR / AT_ENTRY for it; a PIE program at a
  random base.
- The library's claim about libc.so alone: malloc and free correct
  wherever it is loaded. C1 proofs relative to the load base (code at
  base + offset, RIP-relative data); `implements2_at` and `loaded` take a
  base already, the engine and the generated steps do not.
- Startup is the dynamic linker (ldso/dlstart.c, dynlink.c):
  self-relocation, the program's and libc's relocations (GOT entries for
  malloc and free), TLS, then the program's `_start`; calls through the
  PLT.
- The program's claim then for a program and the library file, proven
  from the library's claim and the program's own proofs.

### 3.2 Optimized code

- The cut-point theorem between two CFGs as an optimization layer:
  GIMPLE ⊑ GIMPLE, from the -O2 GIMPLE to the -O0 one's structure.
- DWARF location maps for optimized frames; other compilers (LLVM IR).
- Engine features optimized code needs:
  - frames with a frame pointer (`push rbp; mov rbp, rsp`, rbp-based
    slots): C1 knows rsp-based frames only (musl's
    -fomit-frame-pointer; the test program is compiled so too,
    scripts/build-musl.sh);
  - narrow return values (a char returned in al, the rest of eax any):
    C1 wants the register to hold the value's width;
  - CFG -> loops: nested loops, a head reached at two structured loops,
    an exit of two loops, a callee refined inside a walk with loops of
    its own;
  - flags kept across instructions (`tr.ptf` / `tr.lvf`,
    proofs/translate_memset.core): `_f` forms exist for the rules memset
    needs; others as a function needs them;
  - stack objects read before their first store (none at -O0 yet).

### 3.3 Multi-threading

The per-thread simulation meeting a memory model at the primitives
(`cas32` and the other atomic steps of layers/gimple.sl); musl's locks
then taken for real. Traces of infinite runs (I/O specs that run
forever).

### 3.4 More of the library and the model

- calloc (its spec in layers/malloc.sl, not claimed): calloc.c's C1
  (`calloc`, `mal0_clear`'s page loop) and memset (`rep stos`). musl
  returns a block uncleared when `__malloc_allzerop` says its group has
  its own mapping: malloc's spec must then promise such a block's bytes
  zero (fresh anonymous pages are zero in the model; the group's slot is
  not reused after a client wrote it -- to check against free's
  `MADV_FREE`).
- realloc (no spec yet).
- The string instructions in general (layers/musl_asm.sl): `rep movs` /
  `rep stos` of any element size (`x86i.rep_movsq`, `x86i.rep_stosq` are
  for 8: their iterations and facts with the size a parameter); an
  overlapping forward copy (s < d < s + n: each element read after
  writes reached it, as in memmove) by its exact bytes, not undefined:
  the pointwise invariant of `x86.moved` with the source as it is then.
- The C world owning only its statics, heap and stack objects.
- Beyond malloc: signals, varargs, the file system, networking, C types
  above raw memory, whole executables (busybox).
- The model: file mappings, recursion, fault ordering across two pages.
