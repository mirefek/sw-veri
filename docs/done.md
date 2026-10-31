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
  cache's format and the proof scripts' automation always, and each engine
  a file's lines run, each by its own hash: the C1 engine (`c1`), gref
  with the structuring's cut points (`refines`), contract.rs (`contract`)
  -- other changes keep it (a contract.rs change rechecks the 11 files
  with `contract` lines, 1.5 min, not the chain's C1 and refinements).
- **A function's wrapper theorems by the checker** (`contract FN SPEC by
  THM [call ABBR] [using L, ..]`, slc/cli/src/c1/contract.rs, through the
  proof API, no proof text): from THM, the refinement of FN's procedure
  (with or without the ghost part), `THM_fun` (the `g.fun_*` lemma of the
  wrapper's shape; THM's premises on the arguments by simp / arith from L
  and the configuration's premises), `THM_divg` / `_divw`,
  `THM_implements` (callees by their C1 and THM premises; `_abi` too
  without the ghost part), `THM_linked` (the callees C1's `.linked` has,
  their premises by a theorem of that statement, a `_ref` or a callee's
  `_call_linked`; a callee's own callees fixed by unification),
  `THM_calls_linked` (the linked CFG form refining SPEC), with ABBR
  `THM_call_ref` and `THM_call_linked` (from `THM_q`). SPEC's parameters
  may be fixed by THM (free_meta at the allocator's context). Every C
  function with a procedure-level refinement uses it (get_stride ..
  alloc_meta, 18 lines); callers take the generated `_calls_linked` /
  `_call_linked` facts; about 820 lines of hand-written wrappers gone, each
  line checked in milliseconds.

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

- `proofs/mallocng/claim.core`, last in the chain: `musl_malloc` (malloc
  and free) is proven from `musl.init`; `Impl` of malloc and free from
  `mp.top_malloc` / `mp.top_free`.
- The law free_step (`mallocng.law_free_step`,
  proofs/mallocng/free_step.core): a live block's slot (blocks_ok)
  unframed, then given back as free does. A group not mapped on its
  own: its freed bit (`wr32` of the meta's freed word). A group mapped
  on its own (one slot): the whole group given back -- off its class's
  list (`dequeue_vm`), its meta freed (`queue_vm` of the zeroed meta);
  its mapping only let go, not unmapped (a big group cannot keep a
  freed slot: `big_ok`). The step's frame from `untouched` in a world
  whose every byte is an object's (no stack byte free).
- `mallocng.abs_unique` (proofs/mallocng/model/unique.core): two abstract
  states that hold of the same memory are equal. Both views agree where
  both states' ranges are (nothing reserved or taken); the context's
  fields and lists read from memory (cyclic lists, the areas' chain, the
  auxiliary vector up to AT_NULL), the used metas the meta slots neither
  free nor available (ascending lists of the same members), their fields
  from their bytes, their slots from the in-band headers (a block's or
  nested group's start, its size code).
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
- **... several loops** (alloc_group's four, one after another): H, bs, ks
  a case on the head (`ite(h = k, ..)`); each claim proven at its loop's
  own parts, the cases taken by `g.ite_y` / `g.ite_n` under binders
  (`rewrite_under`, memoized over shared nodes when every instance is
  rewritten -- a DAG not unfolded), a claim at a variable head by cases
  (`g.cases`, the claim whole, not a truth table). The trips walked at the
  free INV as the points; an exit reached before as a cut point (its
  program folded at the break) by `g.ex_mono` (the conversion alone
  evaluated); a parameter in a loop's state in univ(1) by a premise of the
  procedures' refinement, discharged at the wrapper's words. Unsigned
  64-bit division's effect (`tr.eff_cdiv64u`). The label claims' terms
  dropped from the caches per label (62 MB a label kept before).
  alloc_group refined in ~330 s, 2.6 GB (the chain uncached 720 s).
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
  generated from its callees' (`tr.eff_call`), by structure alone, no
  simp (slc/cli/src/c1/eff.rs, proofs/translate_struct.core):
  requirements, choices, statements keeping the world (the rest from it),
  a return to a changed world valid by the change's lemma (`tr.valid_vm`),
  the layer's procedures inlined, a procedure's parameter types (the
  elaborator's `{proc}.dom`) premises of its lemma where its proof uses
  them -- so __syscall6's through sys_call6 and os_mmap, and __mmap
  linked (`mmc.composed`). `a_crash` (`hlt`) has the
  undefined contract (`proofs/mallocng/machine/a_crash.core`); callers' specs exclude it by
  their preconditions. `proofs/mallocng_link.core` links a_clz_32 with
  a_ctz_32, dequeue_head with dequeue, queue with a_crash, free_meta with
  queue, and size_to_class with a_clz_32.
- **Stack objects and the stack protector in C1** (get_random_secret,
  `grsc.implements_abi`; proofs/translate_objs.core):
  - `alloc_objs` at the machine's first store to the object
    (`tr.astore_r`): its bytes the stored word, aligned and outside the
    world's domain by the machine's state (`tr.aslot`, `tr.nodom`); the
    claims' objects from there `tr.obj1(v, A)`, the homes apart from it
    by their ranges (`tr.vone`);
  - the spec's own store of the word after it keeps the world
    (`tr.run_kept`);
  - the CFG entered within its first block (`tr.cfg_lvk_st`);
  - loads of the object as the world's (`tr.load64_obj`); `call_objs` as
    the call (`tr.qs_callobjs`);
  - GCC's canary check: the bridge's alone (see below). The C1 starts
    on the `_fun` wrapper itself (`tr.entry0p`, `Spec::Plain`, rerooted
    at the procedure's call); the return comes with the objects released
    (`tr.ret_insn_w`).
- **Byte-wise validity; the stack protector's word out of the C world**
  (layers/abi.sl, layers/gimple.sl): the world's bytes are `Objs { live,
  c_bytes }` -- `c_bytes` the C world's bytes, stored byte by byte (all
  but the ABI's: `objs_at`, the canary `abi.canary(fs)` not among them),
  `live` the stack objects. An access uses a byte of `c_bytes` on a
  mapped page as the page's protection allows (`usable`, `in_domain`); a
  valid page is a mapped one all of whose bytes are the C world's
  (`page_valid`). The kernel's calls touch only valid pages
  (`sys_pages_ok`), and its fresh pages are the C world's
  (`fresh_pages`, the bridge's: they were free, the ABI's pages are
  mapped). `world_matches` keeps the ABI's bytes and their pages and has
  `c_bytes` all others; a call drops the callee's objects, not
  `c_bytes` (`objs := objs with { live: .. }`). `thread_ptr()` is
  the ABI's fs_base under `thread_ok` (its machine load the bridge's,
  `tr.load64_tp`). The entry requires the canary's word readable and
  writable off the stack (`abi.canary_ok`); the epilogue's `sub r,
  fs:0x28; je` is proven in the bridge (`tr.load64_can`, `tr.fsub64_can`:
  the entry's word, `__stack_chk_fail` never reached).
  - mallocng's invariant in the C world: `holds_in = holds_m &&
    shown_in` -- the memory's (the model's lemmas, page-wise, unchanged)
    and the allocator's bytes the C world's, its reserve's pages valid
    ones (`shown_in`, kept by the steps of the same geometry,
    re-established for fresh pages by `fresh_pages`: `mp.shown_refill`,
    `mp.shown_ngrp`). brk's and mmap's specs return the kernel's refusal
    when no fresh memory is to be had.
  - A callee's dead frame and objects: a call may change the stack's free
    bytes (`abi.stack_free`: on a stack page, no live object's) -- the
    specs' frames say so (`untouched` keeps every other byte outside the
    allocator, `random_secret_spec` every other byte); the allocator's own
    steps keep all (`kept_outside`, `mp.kept_unt`, chained by
    `mp.unt_seq`). The allocator's memory is off the stack's pages
    (`fp_mapped`), so a callee's scratch leaves the invariant
    (`mp.free_holds`) and the thread's word (`mp.tls_unt`).
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
- **The World-spec functions at the ABI level** (`mp.X_abi`:
  `abi.implements2_at` by `tr.implements_abi`): dequeue, dequeue_head,
  queue, free_meta, set_size and the leaves (a_ctz_32, a_clz_32, a_cas,
  upgradelock, resetlock, a_crash; proofs/mallocng/fun/leaves.core). Their
  specs diverge nowhere they do not raise (`mp.X_divw`): the ghost lemmas
  with the empty ghost part (`ct.div_of_g`, `ct.w_single`), the body's
  premise of `ct.contract_div` (`ct.contract_div0` without a precondition)
  inferred and proved by a lemma per body shape (`ct.dv_havoc`, ...), no
  spec body copied.
- **No spec body copied** (the bookkeeping of contracts): a goal-directed
  `show by apply(ct.contract_done, ..)` (`_ret`, `_ovf`) takes the
  contract's precondition and body from the unfolded spec, its body premise
  proved by a rule with that goal (`defs(taut(ex), letin, any_rel)`);
  `ct.contract_inv` takes the run first, so it infers them too; the ghost
  divergence lemmas' body premises by `ct.dv_ret_a` / `_ret2_a` / `_ret3_a`
  (mp.ss, dq, dqh, qu, fm; mp.ag/as/az/db/ef/gm/gsi/ta divergence).
- **Taken metas** (`Abs.taken`, `in_taken`): a meta handed out by
  alloc_meta whose group is not yet made -- out of the footprint and of its
  area's accessible bytes, a fourth case of the metas' partition (a meta
  slot, not used, not free, not available, once); none between the
  allocator's calls (`rep`: `len(A.taken) = 0`). The groundwork for
  alloc_meta's and alloc_group's specs. The footprint lemmas take the byte
  untaken (`mp.untaken_of`, `mp.grp_untaken`, `mp.untaken_meta`,
  `mp.untaken_hdr`); a meta's area read by its header only (`mp.meta_area`).
- **alloc_meta's spec** (`alloc_meta_spec`): a meta taken (`A.taken`
  grown by it, `meta_ready`: accessible, its links 0) or 0; the groups as
  before (`groups_kept`), memory taken only where unmapped, errno. alloc_slot
  and alloc_group keep the taken metas (`A.taken = A0.taken`; `mp.as_out`,
  `mp.as_call`, `mp.agr_call`). The invariant bounds `meta_alloc_shift`
  (`<= 34`, ctx_ok's last clause; no longer a free counter): alloc_meta's
  `2 << shift` is undefined from 64 on.
- **Usability before alloc_meta**: a call's registers for any argument
  widths (`gc.regs_one`, `gc.regs_cat`, `gc.regs_get` composed by `step`
  along the arguments; `gc.reg_at` to read one back); `goal [N]` printing
  the goal, variables and named facts; ctx_ok's, rep's and fresh_ok's
  clauses named; `divergence([GU, GS])` deriving a spec function's
  divergence lemma (`runs_univ()`, `div_body(GS)`; 21 hand-written ones
  replaced); a failing step naming a fact that hides an enclosing block's
  says so; simp evaluates `seq_one(x)[0]`; a fact and a goal differing in
  `pow2(k)` against its value fitted (`conv_pow2`).
- **Lemma search** (`search P1, ..`: the facts with subterms matching the
  patterns, `_` any term, a bare name any application; `search` alone:
  the facts whose conclusion matches the goal) and a note for a theorem
  stating what one before it states (12 such pairs found by hand-written
  proofs, listed in todo §6).
- **alloc_meta's transitions**, each keeping the invariant in memory
  (proofs/mallocng/model/): a meta taken in general (`mp.tk_holds_in`) --
  the free list's head (`mp.tfr_holds_in`) or the last area's next one
  (`mp.tav_holds_in`); a meta area added from the reserve
  (newarea.core, `mp.na_holds_in`: the reserve's region split,
  `mp.sep_split`); the reserve refilled from fresh pages, or the break
  alone set (refill.core, `mp.rf_holds_in`: the owned bytes all mapped,
  `mp.owned_mapped`, so the fresh range apart from every region,
  `mp.sep_replace`); the first call's initialization (first.core,
  `mp.fs_holds_in`). The invariant gained: the reserve 0 just when empty,
  its pages not the stack's, no client's bytes in it; the read-only
  segments' pages stated at their own bytes.
- **Names, lists, rewriting**: `[l] P(args)` states P's clause labelled l
  and `clauses(p..)` assembles a predicate from its clauses' proofs in any
  order; `rewrite(e, p)` with its result stated rewrites only where the
  result differs; `at` and `arith`'s lengths take a known concatenation
  whole when its own pieces are not all known.
- **alloc_meta by its purpose, end to end** (`mp.am_run`, `mp.am`,
  `mp.am_fun`, `mp.am_divg`, `mp.am_implements`, `mp.am_call` /
  `mp.am_call_ref` / `mp.am_q`; proofs/mallocng/fun/alloc_meta.core): each
  path's GIMPLE walk (the first call's initialization, the free metas' head,
  the area's next meta, a new area from the reserve, the reserve refilled by
  brk or mmap) to `alloc_meta_spec`'s outcome. Its machine code is composed
  over dequeue_head's (linked) and, as hypotheses, the leaves not yet at
  machine level (get_random_secret, __syscall1, __mmap, __mprotect,
  __errno_location: each implemented at its address, meeting its spec).
  For no-argument procedures `g.fun_res_ghost0`, `ct.fun_div0` /
  `ct.fun_divg0` (in `divergence`).
- **Brevity and speed of the C2 proofs** (alloc_meta's run 1358 -> ~1120
  lines; the uncached chain 377 s -> 262 s): `arith` reads closed terms by
  their values (named constants, `sval`, word operations on literals);
  `step`'s facts take their aliases (`c.ctx = __malloc_context`), a
  conjunctive premise part by part, a call by its callee's contract or a
  fact for that call, a join (`overflow || return` of an outcome) as a
  call's result, the overflow closed against the goal up to lets and the
  locals' witnesses, a decided branch's condition dropped; a premise
  simplified once per block, arith before mem, mem failures remembered.
- **A group made, in the abstract state** (proofs/mallocng/model/newgroup.core):
  the meta taken last put among the groups in use at its place
  (`mp.ngrp`; `mp.ins_at` keeps them ascending), its record set, its
  slots unused; or in a reserved slot of a larger class's group
  (`mp.ngn`, the slot holding it). The invariant for the new state from
  the old one's clauses (`mp.ng_holds_c`; `mp.ng_holds` mapped on its
  own, `mp.ngn_holds` nested): the old groups by the frame
  (`mp.ng_group`, `mp.nt_group`, the parent `mp.nt_parent`, slot uses by
  `mp.slot_tr`), the new one's clauses from its memory (`mp.ng_self`, its
  masks from the active index `mp.ng_masks`), the regions re-indexed
  (`mp.sep_inject`), the lists, blocks, reserved slots, perms, areas.
- **step through nested ifs and calls**: an `if`'s unnamed outcome opened
  when its condition is decided (a loop body's nested ifs in one step); a
  contract on the callee itself (a parameter) needs no refinement fact
  (`gc.calls_self`); a step's conjunctions by `and_intro` when too large
  for a truth table. The meta alloc_meta hands out: its
  bytes the allocator's at the entry or unmapped then (alloc_meta_spec,
  `mp.am_mfp`) -- what giving it back (`mp.agr_back`) needs.
- **alloc_group by its purpose** (`mp.agr_run`, `mp.agp`, `mp.agp_fun`,
  `mp.agp_divg`, `mp.agr_q`; proofs/mallocng/fun/alloc_group.core, model
  groupmap.core / groupnest.core): every path's GIMPLE walk -- no meta, the
  mmap refused, a group mapped on its own (`mp.gx_holds_in`), a group nested
  in the reserved slot of a larger class's group (size_to_class, alloc_slot,
  free_meta when no slot, enframe, the header byte, the check-byte loop by an
  invariant and variant at its head; `mp.gn_holds_in`, the old invariant on
  a view mixing the held bytes and the slot's) -- to `alloc_group_spec`'s
  outcome. Model and specs grown for it: group_ok's `span` (a class's
  stride under two of its slots); alloc_slot keeps the smaller classes'
  lists and its slot was the allocator's or unmapped (`mp.below`,
  `mp.rgrown`); alloc_group keeps its class's and the smaller ones'
  (`mp.upto`). Engine: arith's congruence classes in a fixed order; a read
  of bytes with no write on them left as it is (bytes after a loop).
- **alloc_group's C1 on its CFG** (`c1 alloc_group .. agrc`,
  machine/c1.core; 48 s): a byte store's value -- the register's low 8
  bits against the spec's -- compared in normal form (`tr.low8_lo`, then
  N), N's names of bitwise operations seen through for that comparison
  only (`eq_nf_bits`); N's new rules: a word's low k bits of a word that
  fits it, of a bitwise operation the operation's on the operands' low k
  bits (`nf.lo_fit`, `nf.lo_and` / `lo_or` / `lo_xor`). The machine's
  `or eax, -64` of a byte and GIMPLE's 8-bit `| -64` one value.
- **alloc_slot and alloc_group at machine level** (`mp.as_over_leaves`,
  `mp.agr_over_leaves`; proofs/mallocng/fun/alloc_pair.core): they call
  each other, a nested group's slot of a larger class (`j > sc`: the
  group's slots, at least one of sc's size, fit in a slot of j), so by
  induction on the class down from 48 -- alloc_slot's code known from k on
  (implemented, typed, io, called as alloc_slot from class k on:
  `mp.as_call_ge`), at 48 a_crash's spec (no class), at k alloc_slot over
  alloc_group's code over the one from k + 1 (`mp.agr_q`, `mp.as_q` at the
  classes from k on). Their callees linked (try_avail, queue, alloc_meta
  with dequeue_head, free_meta, size_to_class, enframe, is_bouncing,
  account_bounce, step_seq); alloc_meta's leaves (`mp.ap_leaves`) their
  machine code linked (`mp.ap_leaves_ok`: get_random_secret with memcpy,
  __syscall1, __mmap, __mprotect, __errno_location), so alloc_meta,
  alloc_slot and alloc_group implement their contracts from the
  configuration alone (`mp.am_machine`, `mp.as_machine`,
  `mp.agr_machine`; `mp.ap_cfg` with `c.libc` libc's struct).
- **A proof's variables dropped after it** (kernel: `Env::begin_locals` /
  `end_locals` around each `prove`, `c1`, `refines`): its variables local,
  numbered from a base above the global ones, the base moved past them at
  its end -- no id given twice, a dropped one unknown to every rule (each
  reads the arity, refuses an unknown variable); a result's local
  variables renamed to fresh global ones by `inst` (`Seq::globalize`), any
  other entry keeping one refused (`Env::locals_kept`); the term caches
  emptied between files. The uncached chain no longer keeps every proof's
  variables (23.7 M by alloc_slot, ~2 GB live): 3.3 GB -> 1.7 GB peak, the
  whole chain with alloc_group within the 6 GB limit (403 s).
- **... 8 bytes each, freed memory given back**: a variable stored as its
  interned name's index and its arity (`VarSlot`; names once, in
  `Env::var_names`; the accessors give `VarInfo { name: &str, arity }`) --
  alloc_group's largest proof makes 35 M (its table's doubling to 2 GB hit
  ulimit -v). After each file the allocator's free memory is returned
  (`malloc_trim`): c1.core's 2.8 GB peak otherwise stayed as free heap
  under the next files' peaks. `SLC_TIMES` shows each file's resident
  memory, its peaks (resident, virtual) and its largest proof's variables.
  The uncached chain 935 s -> 630 s, its virtual peak 5.9 GB -> 4.4 GB
  (alloc_group's; c1.core's resident 2.8 GB the largest).
- **The program loaded, through memory given back** (`abi.loaded`,
  layers/abi.sl): its statics off the stack's space (no longer "mapped and
  not on the stack" -- whether a static is mapped is the C world's to
  check, as for any access), so munmap / brk shrinking / mmap / mprotect
  keep every loaded program (`tr.keeps_code`, `tr.returns_valid`) where
  they keep the stack's space and do not touch executable pages -- what
  `sys_pages_ok` requires of each call changing pages (brk's shrinking
  too). Re-proven by `tr.statics_same` (the same stack top and limit).
- **Linux's memory calls in closed form** (proofs/linux_sys.core):
  `lx.sys_brk_ok`, `lx.sys_mprotect_ok` (the loop to the first unmapped
  page, `lx.prot_loop`), `lx.sys_mmap_ok`, by their loops' invariants
  (`lx.pages_loop`, `lx.bytes_loop`); the syscall instruction with rax 12
  (`x86i.brk_insn`). The readable op by the arguments passed:
  `sys_call1` (brk), `sys_call3` (mprotect), `sys_call6` (mmap); the
  world's brk relational (`gimple.brk_post`, the break returned).
- **C1's rule for `syscall` with brk** (`tr.sys_call1`,
  proofs/translate_sys.core): undefined unless brk with its requirement,
  so the spec raises; else Linux's brk on the machine, the world's memory
  changed alike (`tr.brk_world`: the world's call allows it,
  `g.sys_call1_ok`), the coupling after it by a change on a page range
  off the stack's space, its pages not executable (`tr.vm_chg`;
  `tr.mem_chg`, `tr.inv_chg`, `tr.homes_chg`, `tr.rsv_chg`), the result
  in rax, the frame rsp's page (8 bytes). The engine applies it at a
  `syscall` like a call (`Red::Sys`, `sys_at`); the call's effect
  (`tr.eff_sys_call1`) gives callers' `tr.callee_io`. `c1 __syscall1`.
- **__syscall1 to its contract** (`mp.sy1_abi`): the spec in the code's
  shape (`syscall1_spec(n, new)`, layers/mallocng_specs.sl, requiring brk
  and the op's requirement on shrinking); C2 `ms.syscall1_c2` (brk's
  outcome, one there is -- `ms.brk_post_ex` --, the spec's:
  `ms.brk_post_spec`), composed `sy1c.composed`. alloc_meta's call
  discharges the requirement (`mp.jg_req`: the break grown, or wrapped to
  0 below its start).
- **The thread pointer in C1** (proofs/translate_tp.core): `mov r64,
  fs:[0]` (`tr.load64_tp`: the word there the world's, the thread
  sound -- `tr.tp_def`), readable GIMPLE's `thread_ptr()` (`tr.tp_ok`,
  `tr.tp_ub`, `tr.eff_thread_ptr`);
  calls from a function without a frame (`tr.cfr` with fr = 0: the
  callee's contract for any entry, `tr.implements_at_u`). C1 of __get_tp
  and __errno_location (proofs/mallocng/machine/c1_leaves.core).
- **C1's rule for `syscall` with mprotect** (`tr.sys_call3`,
  proofs/translate_sys3.core): the machine's mprotect (`x86i.mprot_insn`,
  `lx.mprot_post`; `lx.prot_loop` keeps the page map typed), the world's
  alike (`tr.mprot_world`: the pages from addr's to the first unmapped one
  reprotected on both sides, the world's pages the machine's there; the
  world's `os_mprotect` relational, `gimple.mprot_post` / `mprot_ret`);
  its effect `tr.eff_sys_call3`. The engine's `Red::Sys` takes one or three
  arguments. C1 of __syscall3 and __mprotect.
- **Callee-saved registers restored, not kept** (proofs/translate_cs.core):
  the bridge's register map carries rbx, rbp, r12-r15 at their entry
  values from the entry (`tr.entry_n`, `tr.entry0`), the return requires
  them back (`tr.cs_rs`; `tr.inv` no longer has them fixed throughout).
  `push r64` saves one in a home at the frame's new bottom
  (`tr.push64`), `pop r64` restores it (`tr.pop64`); in between the
  register is the function's (`tr.scratch_reg` all but rsp). Calls and
  system calls keep the callee-saved part of the map (`tr.cs_sub`), labels
  and loop heads those at their entry values not saved in a home
  (`tr.pt_rs_cs`). The prologue's pushes count in the frame's depth and
  the body's start, the epilogue's pops in the epilogue. `neg r32` of a
  64-bit word (`tr.neg32_w`). C1 of __syscall_ret.
- **__syscall_ret to its contract** (`srtc.composed`): the spec by purpose
  (`syscall_ret_spec(r)`, layers/mallocng_specs.sl: an error code's number
  -r to errno, -1; else r), C2 `ms.syscall_ret_c2` for any
  ___errno_location meeting errno_location's spec (as size_overflows'),
  the CFG refining the structured form (`__syscall_ret_ref`).
- **___errno_location to its contract** (`elc.composed`): the spec requires
  a sound thread (`thread_ok`) and errno's cell not wrapping (what its
  callers' `errno_ok` has already); the ABI's `thread_ok` says the thread
  pointer is not null (the descriptor an object). C2
  `ms.errno_location_c2` from __get_tp's readable form (`ms.tp_det`:
  `thread_ptr()` the thread pointer, `ms.gtp_q` at a call); `g.fun_res0`
  for functions of no arguments. Linked with __get_tp's C1, it closes
  size_overflows' and __syscall_ret's contracts (`sotc.composed_el`,
  `srtc.composed_el`).
- **mprotect's pages the kernel's to reprotect**: `mprotect_spec` requires
  GIMPLE's `sys_pages_ok` (the kernel model's: off the stack's space, not
  executable); the invariant's `holds_in` says the reserve's pages are
  such (`rsv`: mapped, not executable, off the stack's space -- as the
  mmap without a hint and the brk growth made them, `mp.rsv_fresh`), kept
  by the frames (`mp.rsv_keep`, `mp.rsv_vm`, `mp.rsv_drop` for a new
  area), so alloc_meta's mprotect of the reserve's first page has it
  (`mp.rsv_first`). The frames' preconditions carry the stack's bounds
  (unchanged by the C world).
- **C1 for any entry alignment**: `tr.inv` has the entry's rsp 8-byte
  aligned (enough for the return slot's page, `tr.page_ret`; `tr.kept` the
  return slot's pages), the ABI's 16-byte alignment (`tr.sal16`) a premise
  only where it is used: an aligned call (`tr.call`, `tr.call1`: frame 8
  mod 16), a system call (`tr.sys_call1`, `tr.sys_call3`: the 8-byte frame
  after it, `tr.frame8`). The entry rules (`tr.entry_n`, `tr.entry0`,
  `tr.entry_g`) take the entry's condition E: the ABI's, or
  `tr.entry_ok_u` (now with rsp 8-aligned and the break's start). The
  engine assumes the ABI's entry at the first aligned call or system call;
  else the function's contract is for any entry (`{p}.implements_u`, e.g.
  `gtpc.implements_u`, __get_tp called from the frameless
  __errno_location).
- **__syscall3 and __mprotect to their contracts** (`sy3c.composed`,
  `mprc.composed`, with __syscall_ret linked: `srtc.linked`). `syscall3_spec`
  is the kernel's mprotect (`ms.syscall3_c2`, by `ms.ret_run`: a run of p
  is one of "require q; overflow or return p"). `mprotect_spec` now also
  requires `tls_off` -- the range misses the thread pointer's and errno's
  pages, else the errno write after it could fault -- and len + PAGE <=
  2^63 (musl's addr + len + PAGE - 1, a defined pointer sum). C2
  `ms.mprotect_c2` by the callees' outcomes at a call (`ms.sy3_q`,
  `ms.sr_q`), errno kept sound across the reprotection (`ms.eok_reprot`),
  the kernel's memory after always existing (`ms.mprot_post_ex`), the
  spec's two returns built (`ms.mpr_all`, `ms.mpr_err`: the first unmapped
  page as the spec's choice, `ms.any_i`). Malloc's side: the reserve's
  bytes are the allocator's (`mp.rsv_fp`), the thread pointer's and errno's
  not (`tls_apart`, `errno_apart`), so its page misses them (`mp.am_tls`).
- **Stack arguments, __syscall6 and __mmap's C2.** The ABI layer's
  `CFunS` (more than six arguments, the rest on the stack above the return
  address, `stack_args`); with them fixed a register-argument spec
  (`with_stack`) whose contract is `abi_function`'s (the callee keeps
  them). GIMPLE's `call_s` / `call1_s`, emitted by the readable generator
  for such callees; `gc.contract_call1VR_s` (the contract lemmas' core
  takes the callee's runs, `_m`). The kernel model's os_mmap returns
  ENOMEM without a free place (it was unconstrained). `mmap_spec` requires
  what sys_call6 does (a fixed mapping's pages `sys_pages_ok`, else addr
  0) and, fixed, `tls_off` (__mmap calls on after it); alloc_meta's guard
  page at the old break meets both (`mp.fresh_spo`, `mp.am_tls_unm`). C2:
  `ms.syscall6_c2`, `ms.sy6_q` (its outcomes at a call), `ms.mmap_c2` (musl's
  checks, the vm_wait, the kernel's outcomes through __syscall_ret: errno
  or the place; the spec's returns built, `ms.mmap_ok`, `ms.mmap_errno`;
  the thread pointer sound after fresh pages, `ms.th_fresh`).
- **__syscall6's C1 and contract (a callee with a stack argument).** The
  bridge (proofs/translate_sargs.core): `tr.implements_at_s` (the contract
  for any stack arguments stk the entry has, `abi.stack_args`, off the
  callers' objects, `tr.sargs_off`), the entry `tr.entry_ns` (six in
  registers, the spec's arguments `seq_concat(args, stk)`), the load
  `tr.load64_sarg` (the entry's [rsp + 8 + 8 j], kept as the frames clause
  keeps bytes above rsp), `tr.implements_s_intro`, `tr.implements_refine_s`.
  The engine: an argument count beyond six, stk's facts at the entry, a
  home load above the return slot as a stack argument. mmap's `syscall`
  (proofs/translate_sys6.core): the machine's Linux mmap
  (`x86i.mmap_insn`, `lx.mmap_post`), the world's os_mmap outcomes by
  case (`g.mmap_inval` .. `g.mmap_free`), fresh pages on both sides keeping
  the coupling (`tr.fresh_chg`, `tr.mmap_world`), the rule `tr.sys_call6`.
  The Linux model's sys_mmap returns ENOMEM without a free place (it was
  undefined; Linux's get_unmapped_area fails so) -- trusted spec,
  `lx.sys_mmap_ok` restated. `refines` for a CFunS without the six-argument
  bound; `sy6c.composed` (proofs/mallocng/machine/cfg_mmap.core).
- **__mmap's C1 (a caller of a stack-argument callee).** The bridge
  (proofs/translate_scall.core): `push [rsp + d]` (`x86i.push_m`,
  `tr.push_m64`; before a call from any frame, its fault the call's
  overflow, the slot's page by the stack's gap: `tr.push_m64_c`,
  `tr.push_hacc`); GIMPLE's seven-argument call as the six-register call of
  `with_stack(G, [x])` (`g.callee_ws`, `g.call_ws`); the home at the frame's
  bottom the stack argument at the callee's entry (`tr.sargs_at_call`);
  `tr.callee_sim_c` / `tr.call_c` (tr.callee_sim / tr.call with the
  callee's contract at its entry state, generated copies), `tr.call_s`,
  `tr.call1_s`, `tr.call1_sc`; `and eax, imm32` of a 64-bit word. The
  engine: call1_s, a callee's CFunS premises (`tr.implements_at_s`, typed
  on lists, `tr.callee_io_s`), the cut points' no-stop from a deeper frame
  (`tr.nobp_cut_le`). Effects for callers of a stack-argument callee:
  `tr.eff_call_s` / `tr.eff_call1_s` (generated copy of tr.eff_call),
  `tr.callee_io_s_fun`, eff.rs's `tr.callee_io_s` hypotheses (`mmc.io`);
  `tr.mmap_valid` (fresh pages on no executable page keep the world valid).
  The kernel model's os_mmap: its havocs `else { ENOMEM }` (a memory with
  fresh pages always exists for a world's; defined for every state), the
  free place by `any .. else`.
- **memcpy (musl's assembly) to its contract** (`mcpc.composed`). A
  hand-written readable model (layers/musl_asm.sl, structured;
  layers/musl_asm_cfg.sl, the CFG as the code's blocks, the registers its
  locals: `F_cfg_regs`), the string instructions as primitives: `move(d,
  s, n)` (movs: read, then written; undefined unless usable, n < 2^64),
  `move_words(d, s, c)` (rep movsq: one move of the 8c bytes; a word read
  after a write reached it -- s < d < s + 8c -- not modelled, undefined).
  - C1 (`mcpc.implements`): the CFG rules' registers a function of the
    locals (`tr.cfg_lv` .. `y. rc(y)`, a label's among the point's by
    `tr.rsub`); a hand-written CFG's first block walked from the entry
    (`tr.cfg_lvk_st`); rep movsq on the machine by `while_var` on its
    `while` over rcx (`x86i.rep_movsq`, `x86i.rep_movsq_out`: the bytes
    after j words `x86.moved`, one more word `x86.moved_stepn`, all of them
    one store `x86.moved_store`; byte k of a read `g.bytes_digit`); the
    rules `tr.move_step` (a move the world's: its bytes by `tr.mem`),
    `tr.movsb`, `tr.rep_movsq`, `test r32, imm32`, `and r32, imm8` and `dec
    r32` before a jump (`tr.jcc_w` of any width; `x86i.zff`, dec's zero flag
    alone), `dec r64` (proofs/translate_string.core, translate_asm.core).
  - The CFG refining the structured form (`memcpy_ref`): gref's folding
    of blocks passing their outcome on (`red_t`'s one-point rule;
    `g.ex_pass`, an exit inside nested `if`s), the parameters' universe
    facts past a loop function's ways, the moves' effects
    (`tr.eff_musl_asm_move`, found by eff.rs by name; `move` writes at
    `bits[64](d)`, a word for a loop's untyped locals).
  - C2 (`mp.memcpy_c2`, proofs/mallocng/fun/memcpy.core): the bytes up to
    d's word boundary, the words, the bytes left -- each a move of what is
    at s still (`mp.mvw`), the loops by `g.loop`; `memcpy_spec_fun` by the
    GIMPLE wrapper's convention (`result`).
- **malloc(0) in the malloc layer**: a block may have no usable byte (C's
  malloc(0); musl's frames 0 bytes, free checking the byte at p); blocks
  live at once still distinct and apart by their place, `extent` (the
  usable bytes, at least one), and a new block not a live one
  (`fresh_block`). Laws, claim and client facts unchanged.
- **errno ENOMEM on failure** (what malloc's failure owes its caller):
  mmap's errno by `mmap_err` (EINVAL only for no length or a fixed address
  off a page's start; `ms.sy6_q` keeps when the kernel's EINVAL comes);
  alloc_meta, alloc_group and alloc_slot failing leave `errno_is(vm, fs,
  ENOMEM)` -- the area's or group's mmap refused (a length, no fixed
  address), carried through free_meta's step (`mp.errno_kept`: errno not
  the allocator's; agr_back's `keep`) and the nested alloc_slot's failure.
- **munmap at machine level** (munmap.c: `__vm_wait`, `__syscall2`,
  `__syscall_ret`): readable GIMPLE's `sys_call2` (layers/gimple.sl:
  `os_munmap`, Linux's sys_munmap -- EINVAL, else the pages gone), its C1
  rule (proofs/translate_sys2.core: `tr.sys_call2`, the machine's and the
  world's pages gone alike, `tr.munmap_world`), eff.rs's validity of a
  return with pages gone (`tr.valid_gone`: a field's lemmas tried in
  turn); the specs `syscall2_spec`, `munmap_spec` (errno EINVAL, -1; or
  the pages gone, 0 -- tls_off: __syscall_ret after), C2
  (proofs/mallocng/fun/munmap.core: `mp.sy2`, `mp.mun` through its three
  calls' contracts), divergence by hand (`contract` takes a `THM_divw`
  proven before it), linked (`mp.mun_linked`).
- **The locks, single-threaded** (proofs/mallocng/fun/locks.core): malloc's
  rdlock, wrlock, unlock and __lock.c's __unlock (a new leaf translation
  unit) by their purpose -- nothing done, libc's need_locks 0 and the lock
  word 0 (`lock_spec`, `unlock_spec`; unlock a call, so the thread sound);
  C1 (a test's `jns`: `tr.ccl32_ns`), `refines`, `contract`; linked
  (`mp.rdl_linked` .. `mp.unl_linked`) with the callees never reached
  (__lock, a_fetch_add, __wake) as a_crash's spec.
- **get_random_secret to its purpose** (`grsc.composed`, linked with
  memcpy's code; proofs/mallocng/fun/random_secret.core).
  - Spec and model fixes it needed (GIMPLE level): `stack_free` is a byte
    on none of the world's pages (the world has none of the stack's) and
    no live object's -- before, on a stack page, never in a world, so
    `random_secret_spec` kept every byte, its own object's too;
    `alloc_objs` places its objects at such bytes (`objs_fit`), not null,
    within the address space, and raises a stack overflow when there is
    no such place (before: any outcome); `auxv_ok` has the vector not at
    null and below 2^63 (an index a pointer's signed offset), so mallocng's
    invariant has `auxv_nz` (fresh_ok); `random_secret_spec` requires the
    thread sound (its copy a call).
  - The bridge: the object not null from the stack's reserve (`tr.aslot`:
    rsp at the entry at least the guard gap up, the frame within
    tr.FMAX); `tr.alloc1_run` through the overflow's guard.
  - CFG refining the structured form (`get_random_secret_ref`): a `call_objs`
    callee in a loop (eff.rs `called_in`), a wrapper reading the world
    first (`g.wrap_ref_let`); the CFG's return inside a loop, the
    structured one's after it: a trip's `break` then the loop's rest
    (`g.loop_head`, `g.cut_loops`: the break case `o = pair(5, ..) ||
    ks(..)`; gref's `or_side` takes the exit, else the rest).
  - C2 (`mp.grs_run`): the allocation (`mp.alloc1_inv`), the auxv walk by
    `g.loop` -- k pairs passed, the memory the entry's but the stack's free
    bytes (`mp.rs_vm`, reads by `mp.rs_read`) --, AT_RANDOM's bytes copied
    by memcpy's contract at a call (`mp.mc_q`), the object's word read; the
    function (`mp.grs_fun`), its CFG form linked (`grsc.calls`).
  - Its `tr.callee_io` and typing from C1 (`grsc.io`, `grsc.typed`):
    alloc_objs' effect (`tr.eff_alloc_objs`: the memory's pages the same,
    bytes changed only off the program's -- `tr.valid_keep`), the
    wrapper's return from the world with the objects released (eff.rs: a
    bind from a changed world valid from the current one, `tr.eff_from`,
    `tr.valid_objs`).
- **A stack overflow keeps only the I/O** (layers/abi.sl `overflow()`:
  the memory and the objects any, as a divergence's state; the machine's
  contract reads an overflow's records only, `tr.ovf`): a function with
  stack objects raises with them still live, its spec's overflow too. The
  outcome `abi.ovf_out(t, o)` (proofs/gimple_inv.core) in every contract;
  `ct.objs_ne`, `ct.objs_univ`; the call lemmas (`gc.contract_call*`) with
  the objects a witness; `step` carries an overflow of several witnesses.
- **`__libc_malloc_impl`** (proofs/mallocng/fun/malloc.core): its purpose
  spec (`malloc_impl_spec`: p a new live block of n bytes -- the ghost
  blocks by `set_block` -- or 0 with ENOMEM; malloc(0) allowed none), its
  run (`mp.mi_run`), refinement (`mp.mi`) and contract over any callees.
  - The big path: a group of its own mapped (`mp.mm_fresh_n`,
    `mp.bg_holds_m`), alloc_meta's failure unmapping it (`mp.gone_off`).
  - The class path: the coarse class (sc or its odd neighbour, `mp.low_bit`;
    the if's outcome proved once and the continuation rewritten by it);
    the head group's free slot taken (`mp.take_slot`, a_ctz_32) or
    upgradelock and alloc_slot; both by `mp.mi_efpre` (enframe's premises:
    the class bound `mp.cls_bound` from the invariant's `span`, the stride
    from `reuse_ok`) and `mp.mi_fin` (the slot framed: the new block).
  - The layer: `untouched` / `kept_outside` keep the stack's bounds too
    (`bounds_kept`), munmap's precondition after alloc_meta.
  - C1: `or [rsp + d], imm8` (`tr.or32_home_i`), `or r16, imm16`
    (`tr.or16_imm`); the ghost part's blocks replaced (`mp.g_updb`).
  - At machine level from the configuration alone (`mp.mi_machine`,
    proofs/mallocng/fun/malloc_machine.core): its 13 callees' CFG forms
    linked (the locks' `__lock` never reached: any code), alloc_slot's from
    alloc_pair's induction.
  - The `malloc` symbol (lite_malloc.c's default_malloc, a leaf unit):
    C1, its contract (`mp.dm` by `mp.mi_ref`, any program of malloc's
    outcome), `__libc_malloc_impl` called as such (`mp.mi_call`, its two
    returns as one), `mp.dm_machine`.
- **free's translation unit at machine level (C1)**: its readable and CFG
  forms (scripts/check.sh's units), its code's step facts (free.c's copies
  of malloc.c's static functions as `fr_*`, checked against malloc.c's CFG
  forms: the same GIMPLE). Readable GIMPLE holds a small struct whose
  address is never taken (`struct mapinfo`) as a variable per field
  (`mi_base`, `mi_len`; locmap.py their homes from the struct's), no stack
  object. Engine: `lock or` (`gimple.or32`, a_or), shr r8, setcc after a
  compare (`tr.setcc`, then movzx of the byte, `tr.movzx8_set`), cmp r32,
  r32, or r32, [rsp + d], xor r64, r64, mov word [b + d], imm16, two-word
  call results and returns (`tr.ret_pair`), a narrow register's value
  stored to a home as itself, N on `bits_shr`'s width, pairs' parts,
  `b1` and `ite(!p, ..)`; a guarded spec with any program after the guard
  (`tr.entry_np`); a `nop; jmp` no cut point.
- **The malloc layer's world and rep** (towards the claim's top):
  malloc.sl's `world_ok` (the ABI's view at a call: no stack page, the
  canonical C domain; the thread, the break's start, the program loaded --
  `prog_base` / `prog_code` / `prog_statics`, fixed by `slc claim` from
  the executable segment) required by malloc, free and calloc; the frame
  law keeps `fs_base` and the stack's place. mallocng's `rep` is
  `holds_m` (the reserve clause too), `live_rw`, and the thread's
  descriptor apart (its word, errno, the canary). laws.core in the chain
  (`mallocng.abs_univ`; the frame law's reserve pages by `mp.res_rng`);
  the client facts take `world_ok`.
- **free's leaves by their purpose (C2)**: `get_nominal_size` (a client
  block's size from its slot's size encoding, its checks passing:
  `mp.blk_tail`, `mp.gns_run`), `record_seq` (a counter, `mp.rq`) and
  `okay_to_free` (some answer, its reads accessible, get_stride and
  is_bouncing at their contracts: `mp.otf`; its spec requires
  `thread_ok`), each with its contract. step names why a call's contract
  matching the call did not apply.

## Init (startup to main)

- **Readable GIMPLE of the startup units** (crt1.c, __libc_start_main.c,
  __init_tls.c, __stack_chk_fail.c): string literals, function addresses
  as values, indirect calls, stage2's hidden pointer, `volatile` and
  `Phdr` in `slc gimple`.
- **The stop mode** (proofs/translate_stop.core, translate_stop_call.core):
  a run stopping at rip = t (main's entry), "at main" an outcome only
  main's contract allows; the stop contract, the normal one derived from
  it, calls with any breakpoints (direct, through the code map, main
  itself), a stop inside a loop. Engine: `c1 FN SPEC P stop T` / `nostop
  T`.
- **The startup mode** (no thread pointer until `__init_tp`, no canary
  until `__init_ssp`): GIMPLE's `call0` family (`slc gimple --startup`),
  the contract in either mode (tr.impl_m), the startup call rules
  (tr.call0_st, calli0_st, call1_0_st, calli1_0_st). C1 of `_start_c`,
  `__libc_start_main`, `libc_start_main_stage2`, `__libc_start_init`
  (proofs/mallocng/machine/c1_start.core).
- **memset** (musl's assembly, layers/musl_asm.sl): C1 in the startup
  mode, C2 against `memset_spec`, its startup contract `mset.composed`;
  a call against GIMPLE's zero `st_bytes` (tr.call0_stb, mset.stz_incl;
  the breakpoints' relation kept by the runs in its world, tr.bka_ovs:
  the stop's, a CFG's cut points').
- **Frames with several stack objects of any sizes** (`alloc_objs`;
  proofs/translate_objsn.core, engine objsn.rs): allocated together where
  the machine makes no step (tr.alloc_lv), the homes apart from them, the
  frame reaching them; their addresses through N; element stores and
  loads at [rsp + i*k + d], immediate stores, zero-initialization by
  movaps / movq, calls passing them.
- **`__init_libc`'s C1** (proofs/mallocng/machine/c1_init_libc.core, in
  the startup mode, never at main): its two objects, memset against the
  aux array's zero store, the auxv loop, the program name, the secure
  path's poll and open("/dev/null"). New for it: 2-byte loads (field
  `ld16`, `movzwl` at [rsp + i*k + d]), `cwde`, `jns` after a 64-bit
  test, a load through a register holding a static's address, a void
  return releasing the frame's objects (tr.ret_void_w), the entry of a
  guarded spec in the stop modes (tr.entry_nkpm, tr.entry_gkpm).
- **`__init_ssp`'s C1** (proofs/mallocng/machine/c1_ssp.core; the unit
  __stack_chk_fail.c a startup unit in scripts/check.sh, its own
  `__get_tp` as `ssp___get_tp`): memcpy called before main by its
  startup contract (`mcpz.composed`: a second C1 of memcpy in the startup
  mode, composed with its refinement and C2 as memset's).
- **Calls with a stack argument in either mode** (proofs/
  translate_scall.core; GIMPLE's `call0_s` / `call1_0_s`, emitted by
  `slc gimple --startup`): the callee's contract `tr.impl_m_s` (for
  either alignment `tr.ccs_ms`), its claim at the call's entry
  (`tr.chc`, which the register calls' `tr.call_stmc` now takes per
  entry); the caller's rules `tr.call_s_stm` / `tr.call1_s_stm`, the
  startup's `tr.call1_0_sc` and the push `tr.push_m64_c0` (from
  `tr.push_m64_cm`); the callee's entry `tr.entry_nskm` and contract
  `tr.impl_m_s_intro`. C1 of __init_tls.c's `__syscall6` (the unit in
  check.sh, its location map in scripts/locmap.py).
- **`__copy_tls`, `static_init_tls`'s C1** (c1_init_tls.core; new rules
  among their siblings, translate*.core): `sub rax, imm32`, `sub qword
  [rsp + d], imm8`, `and r64, imm8`, a compare's `cmova` as GIMPLE's
  `umin` (tr.cmov64, engine `cmov_after`), a 32-bit store at a static
  of a wider register (tr.store32_rip_w), `push imm8` before a call
  (tr.push_i8_cm / _c0), a CFG's cut points against a deeper frame
  (tr.tbp_cut_le); a static's load sharing the spec's name for it. GCC
  calls the static leaf `__syscall6` misaligned (frame 0x48 plus the
  pushed word): its startup contract for any alignment (tr.eok_e_s with
  u), the 7-argument call so (ccs_ms's second case); the syscall's
  8-byte frame after it without the ABI's alignment, from a home within
  4 KiB below rsp (tr.home8, tr.frame8_h; tr.sys_call6 takes either).
- **`__init_tp` and the thread pointer** (c1_init_tls.core, c1_asm.core):
  GIMPLE's `sys_call1` with set_tid_address (218; layers/gimple.sl,
  `os_set_tid_address`, as Linux's: a tid in (0, 2^22)) -- machine
  x86i.syscall_tid / tid_insn, the rule's third case (tr.sys_call1,
  tr.sys1_tid, tr.same_chg), its effect; arch_prctl(ARCH_SET_FS) as an op
  of its own, `sys_set_fs` (a generic wrapper's arch_prctl could not keep
  the main mode's thread pointer) -- machine x86i.syscall_aprctl /
  aprctl_insn, the rule tr.sys_set_fs in the startup mode (both thread
  pointers set: tr.inv_chg_fs, tr.mem_fs, tr.cball_nmain);
  `__set_thread_area`'s readable model (layers/musl_asm.sl, _cfg) and
  C1; a `[b + d]` store at the spec's p + off written otherwise
  (tr.store64_bd_a). C1 of the unit's `__syscall1` copy and `__init_tp`.
- **The startup units' leaf copies**: C1 of `__libc_start_main.c`'s
  `__syscall2` / `__syscall3` (lsm_*, c1_init_libc.core); the `a_crash`
  copies (tls_a_crash, lsm_a_crash: hlt) by a contract in either mode at
  any address (acr.impl_m, a_crash_m.core: its spec raises everywhere).
- **The startup code without musl C** (layers/musl_asm.sl, _cfg;
  proofs/mallocng/machine/c1_start_asm.core): crti/crtn's `_init` (`push
  rax; pop rax; ret` -- a scratch register the code pushes held at its
  entry value, its push a prologue's: Gen::entry_held); gcc's
  `register_tm_clones` (its constants' arithmetic, `__TMC_END__` a
  static; `sar r64` by an immediate, and by 1 before a jump on its zero
  flag: tr.sar64_imm, tr.fs_sar64_1); `frame_dummy` (`endbr64; jmp
  register_tm_clones`) by register_tm_clones's contract through the jump
  (tr.impl_m_jmp: a step of one outcome skipped, tr.run_s_det; the
  entry's rip read by neither the run nor the match, tr.run_s_rip,
  tr.mtv_rip).
- **The startup rules in place**: the rules first proven late for short
  checks (`__init_tls.c`'s, the startup code's) moved beside their
  siblings (x86_insn.core, translate.core, translate_frame.core,
  translate_flags.core, translate_memset.core, translate_store_loop.core,
  translate_scall.core, translate_asm.core, translate_stop.core); a
  return to the world with its thread pointer set valid (tr.valid_fs,
  eff.rs's VALID): `__set_thread_area`'s `tr.callee_io` derived.
- **The startup path linked** (step (b)): the startup calls' effects
  (proofs/translate_effects_startup.core: `tr.eff_call0`, `call1_0`, the
  `_objs` and `_s` forms; an `undefined` statement, `true`, and an `if`
  whose other branch it is; a loaded word's type in hand) and eff.rs's
  callees as tables (`fptr[T]`: `all T. T in bits(64) -> tr.callee_io(..)`,
  a parameter typed `fn_space(bits(64), ..)` by its procedure), a
  procedure's lemma from its own facts only; `tr.raises_main` over a
  call's argument lists (abi.ARGS -- a typed spec could not meet it);
  the conversions tr.impl_m_u / tr.impl_m_k (an aligned call's contract
  from one for any alignment, one allowed to stop from one never
  stopping). proofs/mallocng/machine/link_start.core: each caller's C1
  with its callees', bottom up to `stl.linked` (`_start_c`); the code
  maps a concrete table (`lnk.FP1`: main at t, raising at main only --
  `lnk.main()` --, one callee, a_crash's undefined contract elsewhere;
  their `tr.code_okm` by lnk.code_ok1); frame_dummy's entry
  register_tm_clones's CFG form through the jump.
