# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.1 Now: the remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- `activate_group`, `get_meta`, `get_nominal_size`,
  `account_bounce`, `record_seq`,
  `okay_to_free`, `free_group`, `alloc_group`, `try_avail`, `alloc_slot`,
  `__malloc_alloc_meta`, `nontrivial_free`.
- The entry points: `__libc_malloc_impl`, `__libc_free`, `calloc`,
  `__malloc_allzerop`, and the `lite_malloc` / `free.c` wrappers.
- Leaves at machine level (inline assembly with operands, syscalls):
  `a_cas`, `a_or`, `__syscall*`, `__mmap`, `munmap`, `__mprotect`,
  `memset`, `memcpy`, `__lock` / `__unlock`, `___errno_location`.
- C1 bookkeeping: a program-level `while`.

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
- C1 joins (`slc/cli/src/c1/join.rs`): cut the repeated walks. Each
  instruction of enframe is now walked 1-4 times (~3.4k steps, ~27 s),
  because the first path at a join walks on concretely and a claim is
  generalized again (walking on each time) as paths from other contexts
  differ in a home or the world. Widening every home's value to a
  variable does not work (a home holds the code's form of a value, the
  spec its own), so this needs another way to generalize.

## Later

With malloc still as the test bed:

- Multi-threading: threads in the model, TLS, malloc's locking.
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
