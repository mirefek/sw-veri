# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.1 queue (current)

1. `a_crash` (inline assembly `hlt`, called by most functions): C1 by
   showing GIMPLE's run of the instruction raises (the model's decode and
   execute through `inline_asm`, `run_code`); its contract.
2. Calls with no arguments (`a_crash()`).
3. `queue`'s C1, its spec (linking a meta into a list; the `a_crash`
   paths excluded by its precondition), C2.

### 1.2 The remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- `queue`, `free_meta`, `activate_group`, `get_meta`, `get_nominal_size`,
  `set_size`, `enframe`, `size_to_class`, `account_bounce`, `record_seq`,
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
- The C world: let it own only its statics, its heap and its stack objects
  (TLS and errno included; hinted mmap and `MAP_FIXED` at C level).

## 3. Init: startup to main

musl's `_start` … `__libc_start_main` reaches `main` with the invariant
holding for the empty heap, owning only static data, the thread
descriptor and the auxiliary vector.

## 4. Proof language and the code base

Ongoing: how could the languages make progress more efficient?

- Review the code base (slc, proofs, layers) for bad code practices.
- A memory normalizer: `rd64` / `wr64` rules for rsimp, apartness by
  arith. Plan it before building it.
- One lemma per contract call that folds the call's outcome shapes
  (overflow before, the callee's outcomes, overflow after).
- Inversion lemmas for the remaining GIMPLE operations (8-, 16-, 32-bit
  loads and stores, arithmetic).
- Possibly rename `rsimp` to `simp` once the old `simp` is not needed.
- `conj` building to the goal's grouping; one way of instantiating
  (`name[x := t]` instead of positional `all_elim`).

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
- SL: syntax of properties, qualified names and ambiguity errors in name
  resolution, the language's name.
- Checker speed, if needed: generated step theorems, memoised normal forms
  in `taut` / `simp`, parallel checking.
