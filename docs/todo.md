# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.0 Now: the rest of the rules' standard form (docs/overview.md)

In place: N with the ring modulo 2^n, every value named in normal form,
conditions, stores and addresses matched after N, no form-matching
`arith`. What still recognizes a form of its own (GIMPLE -> CPU program
translation verification, the engine):
- the statics' names (`lea [rip + d]`: the literal address named by a
  spec value or static of that value), `and r8, 2^k - 1` as the spec's
  field, `[p + 0]` as `[p]`: each an equation of N or gone;
- a subtraction stays one.

### 1.1 Then: the remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- Specs and C2 (C1 done): `account_bounce` (spec written), `get_meta`,
  `__malloc_allzerop`, `a_cas`, `activate_group`, `try_avail`,
  `alloc_slot`, `size_overflows`, `__malloc_alloc_meta`.
- GIMPLE -> CPU program translation verification of `alloc_group`: it
  stops at 403faf (87 s, 345 MB), the exit of `while (i<2 && ..)` inside
  `if (sc<9)`. The spec reads `small_cnt_tab` (read-only) on its own and
  so is at its block's end there, while the machine has yet to load it
  and store `cnt`: the join there is at the wrong point. The block's end
  is 404036, but `if (sc<9)` can not be a block: a loop inside one is not
  supported. Needed, in the translation theory (`proofs/translate_loop.core`):
  - `tr.loop` / `tr.loop_fin` / `tr.loop_div` with the outer breakpoints'
    arrival (`tr.lg` has none: after a loop's exit the walk runs to the
    function's end, any outer breakpoint unreachable);
  - a block's marked return distinct from a loop iteration's (both
    `ok(w, pair(2^64, y))` now), so a block's end after a loop's exit is
    not read as the loop going on. Nested loops need the same.
- Per-block simulation's other limits (all C1 theorems: 45 blocks, 7 by
  the join claims instead): a block's end where a value lives in a
  register, not a home (`__malloc_allzerop`'s `a || b` in eax); a tail
  the compiler shares between branches (`dequeue`); blocks whose rest
  needs facts proven in the block (`try_avail` 403c9f); `try_avail`
  403d18, 403e41 (homes' subset in the lemma). A block whose `return`s
  and end are the same code (a void function's `if` with `return` as its
  last statement) is no block; the block theory with outcomes other than
  normal arriving at J would cover it.
- C1's joins elsewhere: a code point with two predecessors where the
  spec is not at a block's end is still walked once per path (no claim
  there); the check should join or fail there too. The readable GIMPLE still copies one
  small block (`cnt = 1; needed = req`: an `||` whose second part has a
  signed product, not evaluated outside its guard).
- `get_nominal_size`, `record_seq`,
  `okay_to_free`, `free_group`, `nontrivial_free`.
- The entry points: `__libc_malloc_impl`, `__libc_free`, `calloc`, and
  the `lite_malloc` / `free.c` wrappers.
- Leaves at machine level (inline assembly with operands, syscalls):
  `a_or`, `__syscall*` (a `syscall` primitive, as `cas32`), `__mmap`,
  `munmap`, `__mprotect`, `memset`, `memcpy`, `__lock` / `__unlock`,
  `___errno_location`.
- C1 of nested loops (the inner loop's iterations arriving at the outer
  head).

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
- C1 joins (`slc/cli/src/c1/join.rs`): the claims at a block's end and a
  loop's rule are shared; what is still walked once per path:
  - the function's end, where an early return's path (spec
    `exc(.., "ret")`) and the normal one (`ok(..)`) meet: a claim whose
    spec covers both outcomes, and that carries rax;
  - a block's end where a local without a home in the location map (a
    GIMPLE temporary) holds a literal that differs between paths: a claim
    keeps it literal, so each value has its own.

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
