# Done

What the verification of musl's allocator has reached, by area. Each
item is a short summary of finished work; details are in the files named.

## The model and the claim

- **x86-64 and Linux in SL** (`spec/`). The instruction table and
  decoders cover all 2426 instructions reachable from malloc, free, calloc
  and the startup code, and all reachable at -O0. The model also has:
  - the Linux memory model: pages with kinds, faults as in `siginfo`,
    stack growth;
  - the syscalls the allocator and startup need;
  - exec of a static ELF.
- **Differential testing** (`slc cputest`): random encodings per table
  row, compared with the real CPU including faults and syscalls. Every
  difference it found is fixed. The remaining gaps are listed in
  `tests/cputest-limits.txt`.
- **The claim** (`slc claim malloc`): a closed statement over the
  binary's bytes, with a summary of its trusted base.
- **The malloc layer** (`layers/malloc.sl`): client contract and specs.
  The frame law forced the client contract to leave block mappings and
  the break alone; the claim was false before that.

## Logic and proof language

- **The kernel and trusted extensions:**
  - propositional and quantifier rules, equality and rewriting under
    binders;
  - linear arithmetic over integers and words, with symbolic widths,
    products as monomials, Euclidean division by a symbolic divisor and
    nonnegative products, equals for equals (congruence closure of the
    facts' equations), its cases searched by splits with unit propagation,
    pruned by infeasibility, with no limit on the atoms;
  - lists;
  - memory reads through writes (`mem_read`: apart / the same / inside,
    each decided by arith; writes on bytes of any form; a read of any
    size past apart writes; the facts for each check widened to those
    connected to its terms when the nearest do not do);
  - the path simplifier `simp` and the rewriting simplifier `rsimp`.
- **The proof language** (docs/language.md). It has implicit unfolding at
  mismatches, destructuring by position or label, `apply` with
  higher-order matching, `flip` and `unfold`, and cases of a disjunction
  taken from the fact (`have c: case k of P proof`), and `step`: a run of
  readable GIMPLE inverted step by step (binds by one-outcome facts or
  lemmas, branches by conditions, the choices named), and the memory
  rules (`mem`, `mem_read`; views, frames and closures registered per
  layer, proofs/mallocng/code/ops.core): with them queue's and dequeue's runs
  went from about 300 to 110 lines. `step` takes its `with` facts in any
  order (an operation's lemma for every operation it matches), decides a
  branch also on its simplified condition or by arith from the facts, and
  steps on into nested `if`s and through the accessors' bodies (no lemma per
  accessor: the operations' generic ones); a loop by `let B(l, o) := loop_body(h)` and
  `g.loop` (invariant, variant: the exit). `bitwise` decides bits by registered
  bit rules and one arith call; `cases` takes a literal range case by
  case. Goal rules prove
  `mp` / `apply` premises in place; `arith` reads powers of numerals as
  constants; `rsimp` reduces program outcomes' parts; a `show` must end
  its block. Error messages show the
  first difference, with the proof's abbreviations folded back.
- **Lets** (terms that share instead of copying): `fn_modify(f, k, y. g)`
  with its lemmas (core/records.core); simp keeps a let whose value is
  large and used twice or more, looks through it only where a rule needs
  the value (once more with every let reduced if that fails); the kernel's
  `conv_lets` (ext/lets.rs) matches a fact with a goal up to lets,
  reducing a let only where the two differ, used implicitly wherever a
  fact meets its goal; `zeta` / `fold_let` (rules and steps) expand or fold
  a named let at chosen occurrences; `simp(.., lets(keep(..),
  expand(..)))`; binder names kept on any binder argument and shown in
  messages.
- **Libraries** (`core/`): logic, sets, naturals and words (a word is
  determined by its bits), records, lists, and loops. `core/bits.core`:
  division by powers of 2, a word's bits under `/`, `mod` and `*` by 2^k,
  shifts, `and` / `or` / `xor` / `not` bit by bit, the complement, `x - 1`
  and `-x` around the lowest set bit, bit extensionality. For loops, `while_inv`, `while_var` and
  `while_exists` are proven by induction, with no open lemmas.
- **Speed of the kernel and the C1 engine** (try_avail's C1 from 433 s to
  26 s): terms cache their hash and which variables occur in them; the
  kernel checks a term's well-formedness once and instantiates (`all`
  elimination, a variable's substitution) past the parts without the
  parameters, by loose depths computed once per term; the engine
  memoizes expansions, canonical forms and the searches of a spec's rest,
  and abstracts each subterm once. `C1_PROF=1` prints the engine's and the
  kernel's time per part.
- **Codebase review**: the extensions' soundness holes closed
  (arith overflow and widths, simp's matching and literal substitution,
  names read by meaning: pinned prelude, definitions and loop lemmas),
  each with a regression test; the elaborator rejects what would change a
  program's meaning; the cache keyed by source and checker hashes; unused
  lemmas deleted.
- **The checker**: a per-file cache. The main chain checks in about 5 s
  uncached and 0.2 s cached. An entry rests on the parts of the checker it
  uses (hashes of their sources, slc/cli/build.rs): the kernel with the
  cache's format and the proof scripts' automation always, the C1 engine
  for files with `c1` lines -- other changes keep it.

## The levels

- **L1, the C world without the stack** (`layers/abi.sl`):
  - a partial byte map plus stack objects;
  - the stack reserve as the ABI's stack condition;
  - stack overflow as the only C-visible effect of the stack, at the
    fault of any frame size.
- **L2, readable GIMPLE** (`layers/gimple.sl`, `slc gimple --readable`).
  All allocator functions translate except inline assembly with
  operands.

## Top of the claim and the invariant

- `proofs/mallocng/claim.core`: `musl_malloc` is proven from
  `mallocng.abs_unique`, `musl.init`, and `Impl` of malloc, free and
  calloc.
- `layers/mallocng.sl`: mallocng's invariant, a first draft.
  - The four laws are proven for any configuration
    (`proofs/mallocng/laws.core`).
  - `slc heapcheck` evaluates the invariant on real heaps under ptrace,
    with a self-test that corrupts heaps eight ways.
- `proofs/malloc_client.core`: client facts derived from the specs alone.
  These files and the laws are checked by the tests (`claim_proofs_check`).

## Functions

- **C1 by the checker's engine** (`c1` lines, `proofs/mallocng_c1.core`;
  no proof text: rule instances applied through the kernel, untrusted) for
  a_ctz_32, a_clz_32, get_slot_index, is_bouncing, get_stride, step_seq
  (a loop, by invariant and variant at its head), upgradelock, resetlock,
  decay_bounces, dequeue (malloc.c's copy), dequeue_head, queue,
  free_meta, size_to_class, set_size, enframe, account_bounce, get_meta,
  __malloc_allzerop, a_cas, activate_group and try_avail (loops without a
  counter), alloc_slot (an array's 8-byte element, `tr.elem8_sx_*`; a
  call's argument, a return value the spec computes otherwise: equal by
  arith), size_overflows (`movabs`, a 4-byte store through errno's
  pointer) and __malloc_alloc_meta (no arguments; 64-bit stores, loads
  and compares of statics and homes, `neg`, `and`, `imul`, `shl r64, cl`,
  `add rax, imm32`; an `if` decided by a branch condition on a value
  the code computed otherwise -- `x + x` for `x * 2` -- equal by arith;
  a branch whose condition is a false literal comparison closed; a
  32-bit result widened to the 64-bit return).
  The rules cover:
  - frames of any size;
  - a generic entry with register arguments;
  - the prologue as instructions;
  - 8- to 64-bit loads and stores, 32- and 64-bit arithmetic on registers
    and homes;
  - compares and conditional jumps by the flags
    (`proofs/translate_flags.core`): a compare's or test's step sets them
    as x86 does (`x86i.subf`, `x86i.logf`; a rule per operand shape,
    `tr.fs_*`, a register read at its low bits), a lemma per condition
    code reads them (`tr.ccs_*`, `tr.ccl_*`), one jump rule branches
    (`tr.jcc`, 8- or 32-bit displacements) -- shapes and conditions
    combined, not multiplied;
  - stores through a register's pointer, a register holding fewer bytes
    used as a wider one, the stored low byte of 32-bit arithmetic (by the
    words' arithmetic modulo 2^8);
  - an aggregate's zero-initialization (`pxor` and SSE stores against
    GIMPLE's `st_bytes`, `proofs/translate_zero.core`);
  - 16-bit fields and compares, shifts by `cl` (the spec's count below the
    width), signed products, rip-relative loads of statics, a value in the
    spec's form where both are possible (a low bitfield's mask, a load at
    offset 0, a commuted operation, a shifted literal);
  - the atomic primitive `cas32` (`layers/gimple.sl`): inline assembly GCC
    keeps opaque (`asm volatile`, a memory clobber) given a meaning at
    GIMPLE level -- the readable translation maps x86_64's `a_cas` template
    to it -- and `lock cmpxchg` shown to implement it
    (`tr.cas32_b`, its store and register write in one step:
    `tr.store_reg_step`), at -O0 inside the function `a_cas`, inlined
    alike once optimized.
- **The claim with breakpoints** (`tr.sim`, proofs/translate.core): about
  the run from a point -- a step, then on -- to the first state where the
  function has returned (rsp at or above the entry's sp: set by rsp alone,
  a deeper activation never stops it) or that is a breakpoint (a loop's
  head, a (rip, rsp) of this activation), with an arrival condition there
  (the return's: the spec returns as the machine; a breakpoint's: its
  relation). Every rule takes the breakpoints as binders; a stepping rule
  goes from the claim reaching its successors (`tr.pt`: the arrival
  condition at a breakpoint, else the claim leaving it) to the claim
  leaving its point (`tr.lv`); a rule with an intermediate state, the
  zero-store step and the call have the premise that it (the callee's
  states) are no breakpoint. The contract stays the ABI's run to the
  return (`tr.entry_d`, `tr.run_d_k`); a call splits the caller's run at
  the callee's return (`tr.run_split_k`).
- **Loops without a counter in C1** (`tr.loop_lv`,
  proofs/translate_loop.core): the claim at a loop's head from the claim
  for one iteration, walked once by the engine for every world and locals
  -- the head a breakpoint of this activation (at its frame: a callee's
  states are none, `tr.nobp_hd`), the back edge arriving there with the
  iteration's next locals marked (`tr.pt_head`; with more of the frame
  than at the head, `tr.pt_fd`), the exit into the function's rest in its
  own wrapper (`tr.lv_exit`, `tr.lcont`). The locals carry an invariant
  (a local a home holds: a word of its width), assumed in the iteration and
  owed at the head; a loop is met at the first point of a cycle of the
  code the walk reaches (try_avail's, entered at its test).
- **Joins by the spec's structure** (`slc/cli/src/c1/join.rs`): where a
  block of the spec ends at a point paths meet, the claim for the rest is
  made from the spec, not from the paths: for every world and locals (the
  block's outcome `ok(pair(w, y), E)`), the homes holding locals as those
  locals (`link_homes`, shared with the loop rule), the function's own
  frame (`tr.lv_fd`), no registers, the facts every path arriving has
  (`shared_facts`: none of a path's own values, nor of values the claim
  does not mention); where an enclosing block ends at the same point, the
  outer one's. A loop's rule (`tr.loop_lv`) is proven once per loop and
  context for every locals and world (`loop_claims`). This replaced the
  anti-unification of two paths' states: the points walked by the C1 of
  mallocng's 23 functions went from 18076 to about 4700 (try_avail 8038
  to 1612, get_meta 6209 to 672, enframe 1363 to 556), its check from
  60 s to about 20 s.
- **Location maps for C1** (`scripts/locmap.py`, `build/locmap_O0.core`):
  each readable-GIMPLE local's home in the -O0 frame and the addresses
  where it lives, from DWARF (the sources compiled once more with `-g`,
  the code the same). The engine links a home to its local by the map --
  a literal local too (a loop's counter starting at 0, a flag) -- and
  leaves a home whose locals' scopes have ended out of a join's claim.
  Untrusted guidance: the kernel checks every step.
- **Worlds as lets in C1**: the world after a store is the kernel term
  `letin(W, x. body)`, the world before bound once (copied into the new
  world and the stored value that read it, it grew about 4-fold per
  store: 3e8 tree nodes for a DAG of 146 in `__malloc_alloc_meta`, and
  definitional unfolding walks the tree). The store lemmas' facts are
  moved to that form by `letin_eq` and `eq_subst`. The world's tree now
  stays at ~3e3 nodes, the slowest step under 0.4 s.
- **Bitfield stores** (GIMPLE's `stbf(p, off, n, pos, k, v)`, a
  read-modify-write of n = 1, 2, 4 or 8 bytes, the field at any bit pos):
  a field's bytes are the smallest aligned unit holding it, as GCC
  accesses it (within the field's C memory location, the run of adjacent
  bitfields: `maplen` the word at 32, bits 12..; the translator once took
  the bytes the field spans, which the machine's access exceeded). The
  machine reads the bytes (a pending store's write-definedness lets it,
  `tr.reads_wr`, loads of 1, 2 and 8 bytes), clears, merges, stores
  (`tr.store8_bd`, `tr.store16_bd`, `tr.store64_bd_eq`); the merged word
  is GIMPLE's value (proofs/translate_bitfield.core): bit by bit
  (`bitwise`) the old bytes with the field replaced, `(H * 2^k + F) *
  2^pos + L` (nested `bit_addmul`; `bit_slice`), that form GIMPLE's
  (`tr.bf_val`, by `tr.bf_clear`), the field compared modulo 2^k by
  arith.
- **Readable GIMPLE keeps GCC's blocks** (`slc gimple --readable`): the
  join of a branch whose way runs through a loop found (post-dominators on
  the whole graph: a loop's latch is not an end of its own), and
  short-circuit conditions written as `&&` / `||` when their second part is
  defined whatever it computes (no load, division, pointer or signed
  arithmetic) -- no block copied into both ways: alloc_group's readable
  GIMPLE from 769 lines to 300 (the `sc & 3` cascade an `else if` chain,
  as in C), try_avail's from 266 to 207. The engine decides `&&`, `||`, `!`
  part by part, as the machine branches (each part by a fact, a literal
  computation, or an operand computed otherwise), a shift's count bound
  likewise, and a stored value written otherwise (literals only) by
  evaluation (`tr.store32_bd_eq`).
- **C1 joins and resources**: a block end's claim gives locals of the
  same value one variable (the equation kept: `needed = req` where both
  sides of GIMPLE's `||` set it); `jns` after a compare with 0 as GIMPLE
  writes the condition (`tr.ccs32_ns0`). A resource guard stops a walk
  past `C1_MAX_MB` (default 3000) with the addresses walked most often --
  where paths do not join -- instead of running the machine out of
  memory. `bitwise` reads an odd numeral as its low ones plus the rest
  (masks like `0xf03f`) and words' products by 2^k (`bit_bits_mul`);
  indexed 8-byte stores (`tr.store64_bi`, the address by an equation),
  `or r32, imm8`, a stored value up to a commutative operation's order.
- **Division in C1**: GIMPLE's unsigned 64-bit `cdiv`, as the machine
  computes it (`tr.cdiv64u_ok` / `_ub`: the quotient of the dividend's
  value, a literal's number, its cast dropped -- both sides the same term,
  no search at the conditions on it; undefined for 0) against the machine's `div qword [rsp + d]`
  with rdx 0 (`x86i.div64_rsp`: no divide error -- the divisor not 0, the
  quotient at most rax; `tr.div64_home`, rax and rdx written in one step,
  `tr.reg_step2`); the quotient's low half (`tr.sub32_imm_w`), `cmp r32,
  [rsp + d]` and `jns` after a compare (`tr.ccs32_ns`). The checker runs
  on a 1 GiB stack: a path's proof nests step in step (alloc_group's over
  a thousand frames deep).
- **The rules' standard form** (docs/overview.md): one normalizer N
  (`slc/cli/src/c1/nf.rs`; its equations `proofs/translate_nf.core`, each
  step a kernel rewrite). The 60 instruction rules writing an expression
  to a register or home restated with the result a variable and `r = E`
  (their proofs rewrite the claim back: one line each), the indexed loads'
  and stores' addresses likewise, `tr.qs_op` with `r = e`; both sides name
  every value in normal form, so they meet as one name. Stores compare
  values and conditions compare operands after N; `guard_arith` (and the
  operand-order and literal special cases) removed: the 214 C1 theorems
  from 120 s to 113 s. Hints (`using`) are N's extra equations. N includes
  the ring of words modulo 2^n for any width (from integer congruences,
  `mod_add_mod` / `mod_mul_mod` in core/bits.core): the machine's `(i +
  58) * 8 + ctx` and GIMPLE's `(ctx + 464) + i * 8` one normal form, like
  terms combined (`3·x` against `x + 2·x`), so addresses computed
  otherwise match without `arith`. Paths meeting at a block's end are
  joined or the check fails there with why -- never walked on one by one
  (alloc_group: from 3 GB at the memory guard to a stop at 403faf in 76
  s).
- **Per-block simulation** (`proofs/translate_block.core`,
  `slc/cli/src/c1/block.rs`): a claim up to an extra breakpoint and the
  claim from each state arriving there compose (`tr.bk_seq`); a block's
  own program (`tr.bone`: the `if`, then a marked return of its locals)
  with its lemma to its end J and the rest's claim from J give the claim
  at the jump (`tr.block_lv`). The engine makes a block at each
  conditional jump on the spec's `if` (its end the post-dominator, or with
  `return`s the branches' meeting point outside the epilogue), a failed
  one falling back to the join claims, reported. All 214 C1 theorems: 45
  blocks, 104 s, 1.2 GB.
- **C1 on GIMPLE's control-flow graph** (`slc gimple --readable --cfg`,
  `slc/cli/src/c1/cfg.rs`, `proofs/translate_cfg.core`): the loop rule
  over a set of cut points (`tr.loop_cut`, the one-head `tr.loop` its
  instance), the claim at every block's entry from each block's claim
  (`tr.cfg_lv`, by labels `tr.cfg_lvk`); the cut points from the code,
  the labels' addresses found as walks arrive, each label walked once,
  its homes its live locals' (the generator's liveness, the location
  map's innermost scope). All 214 C1 theorems on the CFG (111 s); the
  spec's projections of constructed tuples reduced in one step
  (`tr.q_same`: the structured walk's 214 from 1.2 GB to 770 MB).
- **The CFG form refines the structured form** (`refines NAME LOW HIGH`,
  `slc/cli/src/c1/gref.rs`, `proofs/gimple_cfg.core`,
  `proofs/mallocng/machine/cfg.core`): per point (a label and its structured
  remainder) the CFG's block walked beside the remainder by congruence
  (`g.ref_op` / `g.ref_if` / `g.ref_ifn` / `g.ref_any`), each side's own
  steps by determined lemmas, the CFG-layer callees by the structured
  layer's (`g.low_op`), the loop by `g.cfg_ref` with a rank. 20 loop-free
  functions (get_meta: 28 points, ~40 s); get_stride, a_ctz_32, dequeue,
  set_size, get_slot_index, is_bouncing, decay_bounces, upgradelock and
  resetlock composed machine ⊑ CFG ⊑ structured ⊑ spec
  (`tr.implements_refine` twice); the callers too (a_clz_32,
  dequeue_head, queue, free_meta, size_to_class, enframe): the CFG C1
  linked with the callees' CFG functions, each function's chain `cc.F`
  (its refinement at those callees, its C2 generic in the callee with the
  callees' chains) -- 15 functions on the CFG path alone, all with a C2
  but step_seq (a loop).
- **... through the blocks' procedures**: the generator writes each CFG
  block as a procedure (`F__bN`, a jump its tail call) and `F__entry`;
  (A) the CFG's loop against them, a point per block, nothing found by
  search (a jump by `g.ref_jump_tail`, the callee's outcomes' kinds from
  its body, `g.proc_post`); (B) `F__entry` against the structured
  procedure, each tail call a jump (`g.low_goto*`, void ones by the
  callee's empty value) and each join walked once for every world and
  locals' tuple. All 22 loop-free functions (`__malloc_alloc_meta`
  included), the term caches emptied per point (peak ~600 MB).
- **... by cut points, the structuring's** (`g.cut_acyclic`,
  `proofs/gimple_cut.core`; the blocks' procedures and the old points
  retired, with their 26 lemmas): one routine structures the
  CFG (`slc/cli/src/gimple/structure.rs`) -- the generator's, and the
  checker's on the label graph it finds in the CFG term, its joins and
  the entry the cut points. Between cut points the CFG unrolled
  (`g.seg_step`, `g.seg_cut`); a join's template from the structured
  side's tuple (its assigned locals free, whatever each way assigned), an
  inner join carried on to the enclosing one (one cut point per join);
  each cut point and each label's block walked once (inv, the label set
  and the rank free relations meanwhile, `Seq::inst` then the
  hypotheses discharged). All 22 in ~75 s (`__malloc_alloc_meta` 45 s,
  from 652 s at first). The generator reads its CFG form back and
  structures it the same (`SLC_STRUCT_CHECK=1`).
- **... with loops, the infinite runs' traces matched** (`g.cut_loops`,
  `proofs/gimple_loop.core`; `slc/cli/src/c1/gref/gloop.rs`): a loop a
  node of the structured form. The loop heads and exits cut points (no
  cut point inside a loop but its head); a rank falling at every step but
  a back edge; each trip from a head walked against the structured loop's
  body (the stop's outcome: the head again, a break, or the rest's); each
  exit's claim the loop's rest after a break. An infinite run is the
  structured loop's infinite run with the same trace: the records
  (`os.events`) grow along it (`g.tr_le`, `g.limit_up`) -- each step by
  the body's effect, `tr.seff` from the C1 bookkeeping's lemmas, callees
  by their `tr.callee_io` (premises of the `refines` theorem) -- or a step
  is undefined, and undefined behaviour diverges with any trace
  (`tr.undef`: every exception and divergence, in `tr.eff`, `tr.seff`,
  `tr.may_raise`), so the run is a finite one (`g.inf_fin`). States in
  univ(1) by their parts (the operations' runs, words' widths).
  step_seq, activate_group (a call in its loop) and try_avail refined
  (< 1 s, 1 s, 110 s).
- **Divergence in C1**: the claim (`tr.sim`) matches a machine run that
  never ends by a divergence of the spec (`tr.div`, its trace not compared
  yet), through steps, spec reductions and calls (a callee's divergence is
  its caller's); a crash's I/O by the spec's overflow or (trace-free) its
  divergence (`tr.ovf`, `tr.crashes_t`); the ABI's contract from the
  bridge's for a spec that diverges only where it raises
  (`tr.div_raises`, e.g. a_crash's: `tr.crashes_abi`).
- **Calls in C1** (`tr.call`, `tr.call1` in `proofs/translate_call.core`):
  - any frame of at most 64 KiB, 0 to 6 register arguments, the result in
    rax:rdx (or rax);
  - entries with the stack unaligned (GCC calls `a_crash` so):
    `tr.implements_at_u`;
  - the push's fault is a stack overflow by the guard gap;
  - the homes and the whole frame survive the callee.

  All contracts assume one loaded program text (`text.code`, generated by
  `slc steps --text`, from the executable segment's start, so its base
  does not move with the set of functions), so linking needs no widening. A caller's
  `tr.callee_io` (its returns keep the world valid for GIMPLE) is
  generated from its callees' (`tr.eff_call`). `a_crash` (`hlt`) has the
  undefined contract (`proofs/mallocng/machine/a_crash.core`); callers' specs exclude it by
  their preconditions. `proofs/mallocng_link.core` links a_clz_32 with
  a_ctz_32, dequeue_head with dequeue, queue with a_crash, free_meta with
  queue, and size_to_class with a_clz_32.
- **C2**, against contracts in `layers/mallocng_specs.sl`:
  - dequeue (`ms.dequeue_c2`);
  - dequeue_head from dequeue's contract only (`ms.dequeue_head_c2`),
    and with musl's dequeue (`ms.dequeue_head_c2_dq`); as a C function
    value (`ms.dequeue_head_fun_c2`);
  - queue, for any a_crash (`ms.queue_c2`), and as a C function value
    (`ms.queue_fun_c2`);
  - free_meta from queue's contract (`ms.free_meta_c2`), with musl's queue,
    and as a C function value (`ms.free_meta_fun_c2`); the malloc
    context's address a parameter of the spec;
  - size_to_class from a_clz_32's contract (`ms.size_to_class_c2`, the
    least class covering n, checked case by case of the leading-zero
    count), and as a C function value; read-only tables are a
    precondition on the world's bytes (`table_ok`);
  - a_ctz_32 (`ms.a_ctz_32_c2`: x & -x, the de Bruijn index, the table
    entry tz(x)) and a_clz_32 from a_ctz_32's contract (`ms.a_clz_32_c2`:
    smearing to 2^p, p x's top bit), proofs/mallocng/code/classes.core; with them
    size_to_class with musl's a_clz_32 and a_ctz_32
    (`ms.size_to_class_c2_linked`);
  - set_size (`ms.set_size_c2`, and as a C function value): the reserved
    count in the slot's header byte, its word at the slot's end, case by
    case of the count (0, below 5, 5 and more), proofs/mallocng/code/slots.core;
  - get_stride (`ms.get_stride_c2`, and as a C function value): a group's
    slot size from struct meta's bitfield word, which GIMPLE reads in parts
    (`g.bytes_split`, `g.bytes_bound`, `g.ldbf_det` in
    proofs/gimple_inv.core; `ms.gs_word`), and the size classes' table;
  - enframe from get_stride's and set_size's contracts (`ms.enframe_c2`,
    and as a C function value), its spec in property form: any p 16-byte
    aligned in the slot with room for n bytes (`enframe_at`), as the code's
    offset (cycled, a byte) is reduced below the slack by the smeared mask
    (`ms.ef_mask`); the header writes, then set_size on the memory they
    leave (the meta's mem word and the thread pointer's word apart from the
    slot, in the precondition);
  - get_slot_index; get_meta (its checks the precondition, a_crash never
    reached, for any a_crash; the offset 16- or 32-bit as one value, then
    the class and mapping cases: eight paths, each one `step`;
    `gmtc.composed`); __malloc_allzerop (no class, or a stride below the
    class's; get_meta's checks its precondition, get_stride's following
    from them; `aztc.composed`) (proofs/mallocng/code/slots.core); is_bouncing and
    decay_bounces (a size class's bounce counter in the malloc context),
    step_seq (its sequence byte; at 255 the first C2 of a loop, by
    `while_var`: invariant the first i unmap sequence bytes zeroed, variant
    32 - i), resetlock and upgradelock, account_bounce (a counter whose
    class was unmapped lately up by 1 below 99, else 150; composed through
    the CFG, `acbtc.composed`), a_cas (the word read and written back, x
    if it held t: `ms.cas32_det`; `acstc.composed`), size_overflows (errno,
    musl's cell at the thread pointer + 0x34, set to ENOMEM through
    ___errno_location's contract: `ms.size_overflows_c2` for any callee
    meeting it; `sotc.composed` given such a callee's code), activate_group
    (act, the active index's low bits, moved from the freed mask to the
    available one; its CAS loop by `g.loop` with an invariant under which
    the body only breaks -- a_cas returns the word just read, one thread --
    or overflows; now its effect summary `ms.ag_run`)
    (proofs/mallocng/code/ctx.core).

  The generic call lemmas (monotonicity, inversion under a contract, and
  `gc.contract_call` / `gc.contract_call1`: a call under a callee's
  contract in one step, its outcomes folded into an overflow or the
  contract's return) and the operations' one-outcome lemmas are in
  `proofs/gimple_inv.core`.
- **Composition**: machine code implements the spec, from C1 and C2 by one
  lemma (`tr.implements_refine`; every case of matching is of the spec's
  runs, `tr.matches_t_mono`), for a_ctz_32, a_clz_32, size_to_class,
  dequeue, dequeue_head, queue, free_meta, set_size, get_stride, enframe,
  get_slot_index, is_bouncing, decay_bounces, step_seq, resetlock and
  upgradelock -- every function with a C1 (`proofs/mallocng_compose.core`,
  a caller's with its linked C1 and its callees' C2). A function-level C2
  (the register wrappers) from the procedure's by one lemma per wrapper
  shape (`g.fun_void`, `g.fun_void0`, `g.fun_res`,
  proofs/translate_effects.core), the specs' wrappers returning a word as
  the code's do (`result[64]`).
- **Specs with ghost state**: machine code implements a spec over the C
  world extended by ghost fields (`abi.implements2_at(G, ..)`) from its
  C1 and a refinement of its ghost-free GIMPLE function to the spec
  (`refines_ghost`): `tr.implements_abi_g`, the bridge's four cases
  (raising, return, divergence, crash) for any ghost part
  (proofs/abi_ghost.core); the ghost-free case its instance. The malloc
  layers' state for it: `MallocAbs`, the abstract state a ghost beside
  malloc's blocks (layers/mallocng_specs.sl).
- **get_slot_index by its purpose**: its machine code implements
  `get_slot_index_spec` -- the index of the slot where p's block or
  nested group starts, in the abstract state (`mp.gsi_implements`,
  proofs/mallocng/fun/). The user's part: the byte read is the
  slot's header, the allocator's, its low bits the index (`mp.slot_hdr`;
  the footprint's ranges as lists, `mp.group_fp`). The invariant gained
  what this needed: a slot's in-band header no client's (`hdr_free`), the
  groups' pages not the stack's. The ghost part's bookkeeping moved to
  the language: simp reads and updates a joined record in its part
  (`dom(h) = D` known: `dom_lacks`, `fn_update_union_l/_r`,
  `app_union2_lacks`) and computes `with_ghost` on outcomes; generic
  `g.bind_ghost`, `g.fun_res_ghost`, `ct.contract_ovf/_ret`
  (proofs/gimple_ghost.core); named conjuncts split to the leaves when
  the names count them (`obtain k, hk hl he` of `ex k: nat. P && Q`).
  Library: `nat_lt_mem`, `int_sum_nat`, `at_type`, `build_list`,
  `ex_at_concat_l/_r`, `app_space`, `rec_univ`, `union2_fun`,
  `some_val` (core/), `x86.le_at_nat`.
- **Meaning-level specs refined by the code directly** (no hand-written
  memory-level spec between): `ct.refines_contract` -- under the
  precondition at the joined state, the code overflows or returns as the
  spec allows (proofs/gimple_ghost.core); get_slot_index (`mp.gsi`) and
  get_stride (`mp.gst`: the meta word read packs the group's fields, so
  its stride is the group's). Reusable reads of the allocator's memory:
  `mp.view_read` / `mp.view_usable` (GIMPLE's reads of the allocator's
  bytes are the invariant's view), `mp.meta_mem` / `mp.meta_word` (a used
  meta's bytes and word), `mp.classes_table`, the footprint's pieces
  (`mp.fp_intro`, `mp.area_fp`, `mp.sct_fp`, `mp.group_fp`). The
  invariant: the class table (`Cfg.sct`) readable and as the source has
  it, the meta areas and the table no client's, the areas not stack
  pages. Library: `int_sum_ext`, `dom_union2`.
- **get_meta at the meaning level** (`mp.gm`, `mp.gm_implements`): the
  meta of p's group. Each function's primary theorem a contract with the
  ghost part read (`mp.gsi_run`, `mp.gm_run`: the code's outcome under the
  precondition, the world state exact), the refinement and the callers'
  rule (`mp.gsi_q`) from it -- so a caller uses its callee's meaning-level
  contract with the world-level call rule (`gc.contract_call1`). The
  code's run as an effect summary with the callee's contract a premise
  (`ms.gm_run`, `ms.gm_eff`), shared by the memory-level C2 and the
  meaning-level proof. The invariant read (proofs/mallocng/model/):
  `mp.gm_pre` -- under it every one of get_meta's checks passes; a
  group's start unit-aligned and positive, the offset within the class's
  slot, the context no client's (invariant additions). get_meta's
  precondition narrowed to the header bytes the code reads.
- **`__malloc_allzerop` at the meaning level** (`mp.az`,
  `mp.az_implements`): whether p's group is one slot mapped on its own
  (`own_mapping`: no class, or a stride below its class's). Its callees
  used by their meaning-level callers' rules (`mp.gm_q`, `mp.gst_q`, the
  result typed: `g.fun_q`); its run an effect summary (`ms.az_run`, also
  the memory-level C2's); musl's test the group's by the meta word's
  fields (`mp.gs_pre`). The memory-level specs of get_slot_index,
  get_meta and allzerop then retired, with their C2s, callers' rules and
  compositions (`gsitc/gmtc/aztc/gsit.composed`); their effect
  summaries (`ms.gm_run`, `ms.az_run`) and get_stride's spec (enframe's
  C2 calls it) stay.
- **set_size at the meaning level** (`mp.ss`, `mp.ss_implements`): the
  slack after the n bytes recorded in the invariant's own encoding
  (`size_ok`, now a part of `frame_ok`), the slot index bits kept, no
  other byte written. Its effect read as the encoding (`mp.ss_post`);
  reading memory after stores (`mp.st_out`, `mp.st_at`, `mp.rd_out`,
  `mp.rd_at1`, `mp.rd_at4`, `mp.wr8_out` ...); a contract ending without a
  value (`ct.contract_done`).
- **The invariant with a slot reserved**: a reserved slot's interior
  (`in_slot`, `in_reserved`) is no longer the allocator's -- out of the
  footprint and of the permissions conjunct -- so whoever reserved it
  writes it without touching the invariant; its access a fact of its own
  (`slot_rw`). New structural facts: the groups apart from the fixed
  regions (`groups_apart`, `fixed_ranges`), the byte after a group's last
  slot 0. Reading lemmas: `mp.slot_in_group`, `mp.fixed_unres`
  (the context, areas and class table in no reserved slot), `mp.nores`;
  get_slot_index, get_meta and allzerop require `no_reserved` (their
  callers' context). `holds`' and `group_ok`'s conjuncts labelled; the
  proofs take them by label (`have {uo = used, po = perms} := ..`).
- **enframe at the meaning level** (`mp.ef`, `mp.ef_implements`): slot idx
  of g, the one reserved, framed for a block of n bytes at some p
  (`framed`: `frame_ok`, only the slot's interior written), p's offset a
  byte. Its run an effect summary with its callees as parameters
  (`ms.ef_run`: set_size's contract any relation Q, here `size_set`); the
  invariant read as its memory-level conditions (`mp.ef_pre`: the meta
  word apart from the slot because the slot's interior is not the
  allocator's); the effect read as the frame (`mp.ef_hdr`, `mp.ef_frame`).
  Invariant facts musl keeps, added: each slot's check byte no client's
  (`chk_own`), a multi-slot group's offsets within 16 bits (`offs`).
  set_size's contract named (`size_set`, the header byte and the slack
  its only writes), its callers' rule `mp.ss_q`. Generic: a call whose
  callee gives its memory by a property (`gc.contract_callV`), a
  contract's run inverted (`ct.contract_inv`). The memory-level specs,
  C2s and compositions of set_size, get_stride and enframe retired.
- **dequeue and dequeue_head at the meaning level** (`mp.dq`, `mp.dqh`,
  `mp.dq_implements`, `mp.dqh_implements`): a list at a head word
  (`list_at`: cyclic through the links, its elements' words accessible,
  aligned, apart); dequeue takes m out of any such list holding it, the
  others' order kept (`rm_at`), m's links cleared, no byte but the head
  word and the links written (`dequeued`, `links_only`); dequeue_head
  takes the first (0 for an empty list, nothing written). The list read
  and built word by word (`mp.list_rd`, `mp.list_mk`); its index
  arithmetic after a removal (`mp.rm_next`, `mp.rm_prev`); dequeue's
  precondition from the list (`mp.dq_pre`), its effect on it
  (`mp.dq_list1`, `mp.dq_list2`, `mp.dq_done`); dequeue's run an effect
  summary (`ms.dq_run`); its callers' rule `mp.dq_q`. Core:
  `nat_mem_lt`. The memory-level specs, C2s and compositions of dequeue
  and dequeue_head retired.
- **queue and free_meta at the meaning level** (`mp.qu`, `mp.fm`,
  `mp.qu_implements`, `mp.fm_implements`): queue appends m, its links 0
  and its words apart from the list's (`joinable`), to any list at the
  head word (`queued`: `l ++ [m]`, only the links and the head word
  written); free_meta clears m's meta and appends m to the free metas'
  list at ctx + 16 (`meta_freed`: its links the list's, its other bytes
  0, nothing else written; the thread pointer's word not m's). The
  appended list's elements (`mp.snoc`, `mp.snoc_ok`), queue's
  precondition and effect on it (`mp.qu_pre`, `mp.qu_list0`,
  `mp.qu_list1`, `mp.qu_done`); the zeroed meta (`mp.zero_b`,
  `mp.zero_w`), a list kept by writes apart from it (`mp.list_keep`),
  free_meta's effect (`mp.fm_pre`, `mp.fm_done`); queue's callers' rule
  `mp.qu_q`. The memory-level specs, C2s and compositions of queue and
  free_meta retired; `queue_pre`/`queue_vm` and `zero_meta` kept as
  effect summaries (`ms.qu_run`).
- **activate_group at the meaning level** (`mp.ag`, `mp.ag_implements`):
  the first spec updating A -- m's freed slots up to its active index made
  available, the rest still freed (`activated`; `masks_only`: A changed in
  the masks only), the invariant kept, nothing outside the allocator
  touched. Its precondition from the invariant (`mp.ag_pre`); the code's
  masks as the freed bits split at the index (`mp.ag_bits`); the new state
  built and activated (`mp.act_state`; records updated: `mp.abs_upd`,
  `mp.meta_upd`); its masks sound (`mp.act_masks`); the invariant kept by
  a used meta's mask words written (`mp.holds_masks` per conjunct on the
  views, `mp.holds_in_act` on the memory). `holds_in` states the
  footprint mapped, as `rep` does: no address wraps (`mp.fp_low`). The
  contract rule choosing the final ghost part (`ct.refines_contract_g`),
  the ghost record updated (`mp.g_upd`). activate_group's memory-level
  spec, C2 and compositions retired; `activate_group_pre`/`_vm` kept as
  its effect summary (`ms.ag_run`).
- **Divergence on the spec's side**: the bridge with a ghost part asks a
  spec that diverges only where it raises (`tr.div_raises_g`), not the
  code: the code's divergence (C1 compares no trace) is the spec's by the
  refinement, and a contract diverges only where it is undefined
  (`ct.contract_div`; the wrapper `ct.fun_div`, `ct.fun_divg`; bodies by
  `ct.dv_ret`, `ct.dv_ret2`). The code's loops play no part.
  `tr.crashes_abi_d`, `tr.matches_t_abi_d`, `tr.implements_matches_d`
  keep the divergence instead of a premise. get_slot_index, get_meta,
  get_stride, allzerop, enframe and activate_group's `*_implements`
  without premises (`mp.*_divg`).
- **The structured form's C1 chain retired** (proofs/mallocng_c1.core,
  mallocng_link.core, mallocng_compose.core; the test
  `c1_engine_checks`): the CFG chain has C1 for the same functions, their
  links and compositions; the shared files' counts checked by
  `c1_cfg_engine_checks`. With it the engine's structured walk: per-block
  simulation (block.rs, proofs/translate_block.core), statement joins
  (most of join.rs), counted loops (tr.qs_loop, tr.wf2, tr.count_*); a
  function of a `return` alone (no CFG) is walked straight.
- **A proof cache** (`slc kernel-check`, `syntax::ProofCache`): within a
  changed file, a proof unchanged in the same context is not checked
  again; `scripts/check.sh` checks the chain with the caches.
- **The context's free bytes** (`ctx_free`: musl's counters and
  heuristics -- mmap_counter, meta_alloc_shift, usage_by_class to the
  sequence bytes): in the footprint (owned), out of the invariant's view
  (`held`: the footprint but those), their access stated on the
  footprint's view (`free_rw`, in `rep` and `holds_in`; `perms_ok` leaves
  them out). A function writing only those keeps the invariant by the
  view alone (`mp.held_*`, `mp.mo_held`, `mp.free_rw_pages`).
- **The context's counters by their purpose**: step_seq, decay_bounces
  and account_bounce refine one spec (`counters_spec`: the invariant
  required, only the context's free bytes changed -- `ctx_only`; the
  invariant kept by it, `mp.co_holds`), is_bouncing one answering any
  word (`is_bouncing_spec`); their machine code implements them
  (`mp.sq_implements`, ...). Their preconditions from the invariant (the
  free bytes accessible: `mp.free_usable`), their writes free bytes
  (`mp.co_store`, `mp.sq_only`, ...); one refinement for the three
  (`mp.counters_ref`). Generic rules for functions without a result: the
  wrapper with a ghost part (`g.fun_void_ghost`, `g.fun_void0_ghost`), the
  contract rule for a body ending without a value
  (`ct.refines_contract_ge`), divergence (`ct.fun_divg_v`,
  `ct.fun_divg_v0`). Their memory-level specs, C2s and compositions
  retired; their runs kept as effect summaries (`ms.sq_run`, `ms.ib_run`,
  `ms.db_run`, `ms.ab_run`; account_bounce's effect `account_vm`).
- **The lists by the invariant**: a cyclic list at a context word the
  invariant reads, of meta slots, is as the list functions need it
  (`mp.ctx_list`: `list_at`); so the active lists (`mp.active_at`) and the
  free metas (`mp.free_metas_at`). A meta slot's bytes accessible
  (`mp.slot_mem`, `mp.slot_meta`), a context byte not free so
  (`mp.ctx_acc`); words from read-write bytes (`mp.rw_usable`,
  `mp.word_rw`). The list functions' callers' rules complete:
  dequeue_head's (`mp.dqh_q`) and free_meta's (`mp.fm_q`).
- **One specs layer**: every function's spec states its purpose, so the
  purpose specs joined the leaf specs and the code's effect summaries in
  layers/mallocng_specs.sl (`X_spec`); their refinements in
  proofs/mallocng/fun/.
- **The invariant kept by list operations** (for try_avail; queue's and
  free's later):
  - the same geometry (`mp.geom`: the lists, the groups' links and masks
    may differ), the masks frame's lemmas derived from it (`mp.mo_geom_of`,
    `mp.group_tr_g`);
  - the links frame (`mp.lframe`, `mp.holds_links`): only the lists' head
    words and the metas' links written, the invariant kept given the new
    lists, links and partition;
  - an active list reorganised (`mp.relist`: class sc's list l2, its
    groups' links the memory's) after dequeue or a rotation
    (`mp.holds_relist`: from `links_only` and `list_at`).
- **Groups nest** (derived from the invariant, no new conjunct): every
  group in use lies in one mapped on its own (`mp.root`); two groups'
  bytes meeting, the later lies in a nested slot of the earlier
  (`mp.laminar`); so a group's header byte in another group's bytes is in
  a nested slot of it (`mp.hdr_nested`). Both by strong induction on where
  a group starts.
- **A group's active index raised** (`mp.holds_hdr`, `mp.holds_in_hdr`):
  the masks frame's byte premise leaves the groups' bytes free
  (`mp.ingrp`; what reads no group byte is apart from them by the regions'
  separation, `mp.reg_nogrp`, `mp.grp_noarea`); the groups transferred one
  by one (`mp.group_tr_g`), the groups nesting the header byte excluding
  their nested slots.
- **A slot reserved** (try_avail; `mp.holds_in_res`, the state
  `mp.res_abs`): in two steps -- the reservation on the old view
  (`mp.holds_reserve`: the masks frame on A with the mask changed, then
  the slots replaced, `mp.sl_same`, `mp.blocks_res`, `mp.normal_sl`,
  `mp.perms_sl`, `mp.masks_res`; the group transfer `mp.group_tr_s` over
  `mp.geoms`, slots allowed from unused to reserved), then the view
  restricted (`mp.holds_restrict`: the invariant reads no reserved slot's
  interior, `mp.res_nested`). The masks frame's page premise leaves
  reserved bytes free (an image page in none: `mp.page_nores`).
  `bit_clear` (core/bits.core): x - 2^k, bit k set.
- **Induction from omega's definition**: induction by membership
  (`omega_mem_ind`, the ordinals' induction on omega) in core/sets.core;
  the induction on naturals (`nat_ind`) and strong induction
  (`nat_strong_ind`) derived from it in core/nat.core.
- **The malloc proofs organised** (proofs/mallocng/): `machine/`, `code/`,
  `model/` (the invariant's theory, by topic), `fun/` (one file per
  function or family, everything about it at the GIMPLE level and its
  machine code implementing it); the chain's order in one manifest
  (`proofs/chain`), read by the test and `scripts/check.sh`; the test
  requires every proof file free of axioms and open lemmas.
- **Partially active groups** (`partial_ok` in `holds`): on a class's
  list at most one group with slots never activated, and such a group's
  slots reach past its first page (alloc_group activates those within
  it). Kept by `mp.partial_kept` (the lists, header bytes and geometry as
  before). Checked on real heaps by `slc heapcheck`.
- **try_avail's run by its purpose** (`mp.ta_run`,
  proofs/mallocng/fun/try_avail.core): a slot of the head taken (`take_slot`);
  else the head dequeued or rotated past, its two ways meeting in one
  state (`mp.ta_jst`); the head skipped if fully free and freeable
  (`mp.jst_rot`); the next head's freed slots among its active ones
  (`mp.ta_act`) -- as it is, the list rotated to a group not partially
  active (`mp.act_rot`, `partial_ok`), or its index raised (`mp.act_raise`)
  after the span loop: the span leaves its first page only landing on a
  page's start exactly, twice would make the stride divide 16
  (`mp.span_next`, `mp.mul_16`), so `g.loop` with the room left as the
  variant; then activate_group (`mp.ag_q`, the ghost part's A the joined
  state), `assert(mask)` unreachable, decay_bounces (`mp.db_q`, context
  bytes only: `mp.co_unt`), the lowest available slot reserved. The step
  rule for calls binds the contract's callee from the call (a contract of
  activate_group_fun(g0, g1) itself).
- **try_avail by its purpose, end to end** (`mp.ta`, `mp.ta_fun`,
  `mp.ta_divg`, `mp.ta_implements`; its C1 linked, `tatc.linked`). A
  callee with a ghost-level spec is a parameter of its caller, given by its
  contract at a call (`mp.ag_call`, `mp.db_call`, `mp.ta_call`: what a
  caller relies on of a callee called as it); the code has it
  (`mp.ag_q`, ...), and a callee refining one that has it has it too
  (`mp.ag_call_ref`, ...: the CFG forms at the machine level).
  `try_avail_spec` requires the list's head word at or past `active[0]`
  (no class below 0); `ct.dv_ret3` (three choices before a return).
- **alloc_slot by its purpose** (`mp.as_run`, `mp.as`, `mp.as_fun`,
  `mp.as_divg`, `mp.as_call` / `mp.as_q`; proofs/mallocng/fun/alloc_slot.core):
  try_avail's slot found -- its index by a_ctz_32, the only one reserved
  (`mp.res_only`), room in it by `reuse_ok` (a group on a list with an
  unused slot is not mapped on its own) --; else alloc_group (a parameter,
  by its contract at a call `mp.agr_call`): -1, or its new group's first
  slot reserved (`mp.put_slot`, take_slot's general part) and the group
  queued. The memory composed over the calls: untouched but errno, grown
  only into unmapped memory (`mp.unt_grow`, `mp.grown_trans`). The
  invariant gained a_ctz_32's table (`debruijn_ok`, `Cfg.dbj`, a fixed
  range); try_avail's empty-list return keeps the slots; alloc_group's new
  group is unlinked (prev 0 too).
- **The list frame for a list that grows** (`mp.relink`; `relist` and
  `enlist` its two uses): the links of the groups on K rewritten -- the old
  list's when it shrinks or turns, the new one's when a group joins --;
  `mp.rlpre` with K, `mp.holds_relink` given the active groups' conditions
  (`mp.relink_partial`, `mp.relink_reuse`: as before, the joining groups'
  by premises); `mp.holds_links_pr`. A group queued on an empty list
  (`mp.qu_step`, `mp.join_new`).
- **The groups' bytes accessible** (`grp_rw` in `holds_in` and `rep`):
  every byte of a group in use -- the allocator's, a live block's, a
  reserved slot's -- readable, writable, not the stack; so a reserved
  slot's access (`slot_rw`, enframe's premise) is the invariant's
  (`mp.slot_rw_of`). Kept on the pages as before (`mp.grp_rw_pages`, from
  the clause's every-byte form `mp.grp_all`), by the frame law (the
  allocator's and the live pages unchanged). Checked by `slc heapcheck`.
