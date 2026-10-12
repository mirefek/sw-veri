# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.1 Now: the remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- Specs and C2 (C1 done): `account_bounce` (spec written), `get_meta`,
  `__malloc_allzerop`, `a_cas`, `activate_group`, `try_avail`,
  `alloc_slot`, `size_overflows`, `__malloc_alloc_meta`.
- GIMPLE -> CPU program translation verification of `alloc_group`: on the
  readable GIMPLE that now keeps GCC's blocks it walks about 4900 points
  (84 s, 1.7 GB) and stops at an `arith` step that names no place --
  next: that step, then the remaining non-reused block-end claims (a claim
  with two locals sharing a variable does not fit a path where they
  differ). The readable GIMPLE still copies one small block (`cnt = 1;
  needed = req`: an `||` whose second part has a signed product, not
  evaluated outside its guard).
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
