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
scripts/sample-stacks.py (with check.sh's `SLC_WRAP`) for where the time
goes.

### 1.1 `rsimp` as the default, `simp` retired

`simp` is still called about 20,000 times in the proofs, `rsimp` about
730 times. `simp` is a trusted extension of about 6,000 lines
(slc/kernel/src/ext/simp.rs) with search inside; `rsimp` is untrusted
(each step a kernel rule). Retiring simp shrinks the trusted base and
makes each step readable; it is not for speed -- simp is cheap.

What simp does now (`SLC_SHADOW=1`, the first 6,085 goal calls, up to
proofs/mallocng/code/lists.core):
- 29 s of simp in all, 27 s of it in the 738 calls with loop hints,
  `keep` or `lets` -- executing program paths (`step`'s job);
- of the other 5,347: rsimp proves 1,622 alone, 1,254 more with taut or
  arith after it, eval 324; 2,147 neither. Those are typing and
  membership facts (963: `x in bits(64)`, `fn_update(..) in univ(1)`,
  `M in x86_64_linux.Vm`), equations of records and outcomes (585:
  `o = ok(fn_update(..))`, fields read through updates), `k in dom(w)`
  and contradictions of literals (389), orders (114);
- rsimp was about 60 times slower per call than simp where both prove:
  mostly its registered rules rebuilt at every call (now built once,
  `Env::ext_cache`; mallocng/init.core 65 s -> 52 s).

The typing procedure (`types`, slc/proof/src/types.rs; rsimp's premises
and closing use it, and distinct literals by their bytes or numerals)
proves 7,055 of the 8,047 membership goals simp proves in the chain
(`SLC_SHADOW=types`), at about 0.1 ms each. `rsimp` as a goal rule is now
a fixed sequence (typing for a membership, rewriting, then taut / arith
with the facts about the normal form's terms). By the shadow
(`SLC_SHADOW=rsimp`, scripts/shadow-report.py) scripts/migrate-simp.py
moved 9,030 steps from simp to rsimp: simp calls 20,052 -> 9,653. The
shadow covered the first 138 files (the rest: its own memory, rerun from
there). The plan, in order:
- The shadow and the migration over the remaining files (a recheck from
  a file on), then the calls it does not prove: by kind, as before.
- The typing procedure's gaps (the shadow's failures): `rec_and` states
  (`m in rec_and(Machine, ..)`), program sets (`pair(s, o) in
  set_select(univ(1), ..)`), terms bounded by a definition's arithmetic
  (`page_of(x) in set_select(omega, ..)`), facts under premises.
- The outcome equations as registered rsimp rules (pair and outcome
  injectivity), and a normal order of updates at distinct keys.
- rsimp's speed: the rules indexed by their left side's head (only those
  that can match a node tried).
- Then simp's call sites moved, file by file, by the shadow's data (a
  call rsimp proves, as fast: renamed); simp's program-path calls to
  `step`; the shadow given a per-call time limit so it covers the chain.
- The machine's semantics (proofs/linux_sys.core) by `rsimp` instead of
  hand lemmas. A dispatch's live case is `rsimp(h, tag)` already. A
  statement's known outcome through the elaborator's sequencing forms
  (the outcomes' parts and their kinds' disequalities registered,
  core/records.core) should be too. Then the hand lemmas `lx.top_*`,
  `lx.blk_*`, `lx.ib_*`, `lx.istep_*`, `lx.tlp_*` and `lx.lp_brk` go.
- eff.rs' last `simp`: a stack call's argument count (`seq_len(list) =
  n`, `tr.eff_call1_s`), by the list lemmas or `rsimp` through the proof
  API.
- Record updates in another order (`fn_update` with distinct keys): simp
  does not normalize them; `mp.clear_perm` swaps four times by hand.
- Then the files with the most calls (translate.core, alloc_meta.core,
  alloc_group.core, translate_store_loop.core, malloc.core: 450 to 900
  each), and `simp` removed from the proof language.

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
    semantics by `simp` for its own addressing form. Instead: one lemma
    per instruction shape with the effective address a parameter, each
    form by its address equation (as `tr.rsp_bd_ea`);
  - the step theorems (about 70 ms each, 1069 encodings: about 80 s of
    the `steps` line's 90 s, after each change of the binary): the
    decoder's `members` and the `exec_insn` unfolding, per encoding;
  - the loops' label claims (`lab_all`): each label's claim is the whole
    premise instantiated there, about 1.5 s per label in alloc_group's
    56, though only the heads' and exits' are not vacuous. Split on the
    heads (and exits) alone, so that the rest are vacuous at once.
- Variables reference counted (a name and arity freed with its last
  term, identity by pointer, not a table index). Now a proof's variables
  are dropped only at its end (`Env::begin_locals` .. `end_locals`).
- An uncached check is 576 s, at most 0.9 GB (was 1407 s, 2.3 GB, before
  hash-consing and the DAG-aware walks). The refinements
  (proofs/mallocng/machine/cfg.core, 160 s) are still the largest part:
  alloc_group's alone 110 s, then
  __libc_malloc_impl's, __malloc_alloc_meta's and try_avail's. Their
  remaining time is in the walk's lemma instances (`ev inst`) and
  goal-directed steps (`evp`): profile again (scripts/sample-stacks.py,
  scripts/sample-report.py) after the label claims below.
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
- `defs(..)` unfolds the goal only; a fact needs `expand` first (ctx_free
  in `mp.co_unt`): `defs` could unfold the facts it is given too.
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
