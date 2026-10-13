# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.0 Now: the CFG path, machine ⊑ CFG ⊑ structured ⊑ spec

C1 on GCC's control-flow graph, the CFG form refining the structured
form, the structured form's C2: composed per function.

1. The CFG ⊑ structured check by cut points (all 22 loop-free functions,
   ~75 s; `__malloc_alloc_meta` 45 s). Next:
   - the structured form generated and checked in one run (`slc gimple`
     running the refinement), and `refines` again in the checked chain;
   - the loop functions (step_seq, activate_group, try_avail refined,
     `g.cut_loops`): their `refines` lines and compositions in
     proofs/mallocng_cfg.core (activate_group's with a_cas's
     `tr.callee_io`); try_avail's 110 s (its labels' and points' walks);
     several loops in one function (H, bs, ks per head), nested loops, a
     head reached at two structured loops, a callee refined inside a walk
     with callees of its own in loops -- for alloc_group;
   - the cut labels on the label graph differ from the generator's where
     returning tails share a block (lite_malloc's `traverses_stack_p`: an
     extra cut point, harmless); the shared tails visible to the checker
     would make them equal;
   - functions the generator does not structure: C2 on the CFG (item 6).
2. A callee's refinement a theorem of its own: now walked again inside
   each caller's `refines` (the CFG layer's callee against the structured
   layer's, `g.low_op`).
3. `alloc_group` on the CFG: its control flow walks (10 labels); next the
   per-instruction gaps -- 404413, a byte store of `dl` (`tr.store8_b`'s
   premise); then the rest of its blocks.
4. Cut-point couplings beyond homes: a value in a register at a block's
   entry (none in mallocng now); the claim with registers per label
   (tr.lv's `rs`).
5. Switch the `c1` lines and compositions to the CFG path, and retire what
   only the structured walk needs (`block.rs`, `join.rs`, the loop and
   block points, `proofs/translate_block.core`). Memory: the CFG C1's
   2.4 GB peak against the structured 770 MB (a function walked twice
   when a label is not reached; the homes' and invariant's tables an
   `ite` chain over all labels -- by label instead).
6. User proofs on a CFG (proving GIMPLE spec): an invariant per label, one
   obligation per block (Floyd style), as a lemma over the `loop` of the
   readable CFG; for functions with no structured view (gotos).
7. Later, for optimized code (proving optimization steps): the same
   cut-point theorem between two CFGs, with a mapping of cut points (not
   1:1: unrolling, duplication, tail merging), stuttering with a measure
   (divergence kept), and couplings beyond the location map (registers,
   SSA names).

### 1.1 The rest of the rules' standard form (docs/overview.md)

What still recognizes a form of its own (GIMPLE -> CPU program
translation verification, the engine):
- the statics' names (`lea [rip + d]`: the literal address named by a
  spec value or static of that value), `and r8, 2^k - 1` as the spec's
  field, `[p + 0]` as `[p]`: each an equation of N or gone;
- a subtraction stays one.

### 1.2 Then: the remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- Specs and C2 (C1 done):
  `__malloc_allzerop`, `activate_group`, `try_avail`,
  `alloc_slot`, `__malloc_alloc_meta`.
- `alloc_group` (C1 by 1.0 item 1).
- `get_nominal_size`, `record_seq`,
  `okay_to_free`, `free_group`, `nontrivial_free`.
- The entry points: `__libc_malloc_impl`, `__libc_free`, `calloc`, and
  the `lite_malloc` / `free.c` wrappers.
- Leaves at machine level (inline assembly with operands, syscalls):
  `a_or`, `__syscall*` (a `syscall` primitive, as `cas32`), `__mmap`,
  `munmap`, `__mprotect`, `memset`, `memcpy`, `__lock` / `__unlock`,
  `___errno_location` (meeting `errno_location_spec`: size_overflows'
  composition, `sotc.composed`, then without its premise).

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
