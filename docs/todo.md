# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.0 Now: GIMPLE as a CFG, C1 per basic block

GIMPLE -> CPU program translation verification moves from the spec's
nesting (blocks of `if`s, loops, joins) to GCC's control-flow graph: a
claim at each basic block's entry (a cut point), for every world and
locals, each block's code walked once up to the cut point it goes on at.
Any control flow (loops in branches, nested loops, gotos, shared tails)
is blocks and jumps; the check is linear by construction, with no joins.

In place (C1 on the CFG: all 214 C1 theorems, 111 s, 2.4 GB; the test
`c1_cfg_engine_checks`):
- The readable CFG (`slc gimple --readable --cfg`; `var bb` first among
  the locals). Blocks with no code of their own written in place: a lone
  jump's (forwarder) by its target, a returning tail (copies, casts, then
  `return`) at each jump to it. Per function the guide `F_cfg_live` (each
  block's live locals) and `F_cfg_widths`.
- The theorems (`proofs/translate_cfg.core`): `tr.cfg_lvk`, the claim at
  every label's address `ad(c)` from each label's claim up to any cut
  point; `tr.pt_cut` the arrival, `tr.nobp_cut` a callee's states.
- The engine (`slc/cli/src/c1/cfg.rs`): the cut points are the code's
  blocks' first instructions (not the epilogue, not a lone `jmp`); each
  label's address found as the walks arrive (`app(AD, c) = a` assumed,
  AD the table found at the end); each label walked once; its homes the
  live locals' (a local of several homes -- nested scopes' variables of
  one name -- the innermost scope's at the address); labels no walk
  reaches (a constant condition the compiler decided) left out.

Next, in order:
1. `alloc_group` on the CFG: its control flow walks (10 labels); next the
   per-instruction gaps -- 404413, a byte store of `dl` (`tr.store8_b`'s
   premise); then the rest of its blocks.
2. Cut-point couplings beyond homes: a value in a register at a block's
   entry (none in mallocng now, the returning tails written in place);
   the claim with registers per label (tr.lv's `rs`).
3. Now: the CFG ⊑ the structured form, per function (proving the chain
   machine ⊑ CFG ⊑ structured ⊑ spec; the composition by
   tr.implements_refine twice). In place (`proofs/mallocng_cfg.core`, the
   test `c1_cfg_engine_checks`, 237 s): 20 loop-free functions refine
   (get_meta the largest, 28 points, ~40 s; the rest 0-2 s each), five
   composed with their C2 (get_stride, a_ctz_32, dequeue, set_size,
   get_slot_index). The checker (`slc/cli/src/c1/gref.rs`, rules in
   `proofs/gimple_cfg.core`): per point (a label and its structured
   remainder) a walk of the CFG's block beside the remainder -- the same
   op, choice, `if` on both by congruence (also the ways swapped,
   `g.ref_ifn`); the CFG side's own steps (the label's dispatch decided
   first, then projections only where a value is used; lets in N and
   named as the reducer names; decided or refuted disjuncts, the
   iteration's end), the structured side's by the spec reducer (its lets
   run before a jump); a callee of the CFG layer by the structured
   layer's, its procedures walked once (`g.low_op`); points found in a
   first pass, the rank the longest path. Next:
   - enframe, __malloc_alloc_meta (proving GIMPLE spec level, the CFG ⊑
     structured check): a value the CFG keeps in a local against the
     structured side's computation of it, the two in different normal
     forms (N's operand order follows the names, the two sides name in
     their own order) -- the point's template matches by syntax. Relate
     a point's local to a value by N (`eq_nf_seq`) instead; also
     __malloc_alloc_meta's memory (over 6 GB);
   - the callers composed: the CFG C1 linked with its callees'
     contracts (as proofs/mallocng_link.core); a callee's refinement as
     a theorem of its own (now walked again in each caller's check);
   - the divergence theorem for nested loops (an infinite run of the CFG
     a diverging run of the structured loops, the same trace), then the
     functions with loops;
   - functions the generator does not structure: C2 on the CFG (item 5).
4. Switch the `c1` lines to the CFG form (then the C2 proofs by 3), and
   retire what only the structured walk needs (`block.rs`, `join.rs`, the
   loop and block points, `proofs/translate_block.core`). Memory: the CFG
   form's 2.4 GB peak (a function walked twice when a label is not
   reached) against the structured 770 MB -- the walks' terms carry the
   label table; make the homes' and invariant's tables smaller (by label,
   not an `ite` chain over all).
5. User proofs on a CFG (proving GIMPLE spec): an invariant per label, one
   obligation per block (Floyd style), as a lemma over the `loop` of the
   readable CFG; for functions with no structured view (gotos).
6. Later, for optimized code (proving optimization steps): the same
   cut-point theorem between two CFGs, with a mapping of cut points (not
   1:1: unrolling, duplication, tail merging), stuttering with a measure
   (divergence kept), and couplings beyond the location map (registers,
   SSA names).

### 1.1 The rest of the rules' standard form (docs/overview.md)

In place: N with the ring modulo 2^n, every value named in normal form,
conditions, stores and addresses matched after N, no form-matching
`arith`. What still recognizes a form of its own (GIMPLE -> CPU program
translation verification, the engine):
- the statics' names (`lea [rip + d]`: the literal address named by a
  spec value or static of that value), `and r8, 2^k - 1` as the spec's
  field, `[p + 0]` as `[p]`: each an equation of N or gone;
- a subtraction stays one.

### 1.2 Then: the remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- Specs and C2 (C1 done): `account_bounce` (spec written), `get_meta`,
  `__malloc_allzerop`, `a_cas`, `activate_group`, `try_avail`,
  `alloc_slot`, `size_overflows`, `__malloc_alloc_meta`.
- `alloc_group` (C1 by 1.0 item 1).
- `get_nominal_size`, `record_seq`,
  `okay_to_free`, `free_group`, `nontrivial_free`.
- The entry points: `__libc_malloc_impl`, `__libc_free`, `calloc`, and
  the `lite_malloc` / `free.c` wrappers.
- Leaves at machine level (inline assembly with operands, syscalls):
  `a_or`, `__syscall*` (a `syscall` primitive, as `cas32`), `__mmap`,
  `munmap`, `__mprotect`, `memset`, `memcpy`, `__lock` / `__unlock`,
  `___errno_location`.

## 2. The invariant and the laws

- Specs of the internal functions in terms of `layers/mallocng.sl`'s
  abstract state; the entry points' C2 against the malloc layer.
- `mallocng.abs_unique` (the abstract state is determined by memory): the
  laws rest on it.
- `musl.free_step` (free always has a step), open in
  proofs/musl_malloc.core.
- The C world: let it own only its statics, its heap and its stack objects
  (TLS and errno included; hinted mmap and `MAP_FIXED` at C level).

## 3. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap, owning only static data, the thread
descriptor and the auxiliary vector.

## 4. Usability and speed: the proof language and the pipeline

Frictions met while writing the proofs, and the features they ask for,
from the proof writer's side. Taken up in batches between functions.

- The function-level C2s and the compositions: each now a few lines, one
  instance of `g.fun_void` / `g.fun_void0` / `g.fun_res` and of
  `tr.implements_refine`; they could be generated with the C1
  certificates (the wrapper's shape and arguments are known there).
- SL: design a syntax for properties; add qualified names and ambiguity
  errors to name resolution; choose the language's name.
- Code: name the C1 engine's instruction rows instead of numbering them,
  and derive its `simp(L, ..)` counts; make the kernel `Env`'s fields
  private; make the interpreter check literal widths as the elaborator
  does.
- Checker speed, if it becomes a problem: generate step theorems, memoise
  normal forms in `taut` / `simp`, check files in parallel.

## Later

With malloc still as the test bed:

- Multi-threading: threads in the model, TLS, malloc's locking.
- Traces of infinite runs: C1 matches a machine's divergence by one of the
  spec's (`tr.div`) without comparing their traces; the ABI's contract
  needs the same trace, so it is now had only for specs that diverge only
  where they raise (`tr.div_raises`, the contracts). Transferring traces
  needs the machine's events growing along every run (a theorem over the
  whole machine step: only `sys_write` / `sys_read` emit, and an
  undecodable instruction is undefined), callees' contracts keeping it
  during the call, and the per-step and loop arguments carrying the
  limit; then specs that run forever doing I/O (and a waiting malloc under
  threads) can be verified with their traces.
- Optimized code and an updated compiler: an optimization layer (GIMPLE ⊑
  GIMPLE), DWARF location maps in the bridge.
- Other compilers' layers: LLVM IR from clang, alongside GIMPLE.

Beyond malloc:

- Signal catching (handlers, `sigaltstack`, `rt_sigreturn`), varargs,
  stack-passed and floating-point arguments, realloc.
- Filesystem, process communication, networking.
- Higher-level understanding of types: C types and objects above raw
  memory.
- Whole executables: busybox.

Smaller items:

- Model: file mappings, recursion (general fixpoints), fault ordering
  across two pages, instruction fetch across into an unmapped page, other
  external kills in `overflow_ok`.
