# To do

The big steps first. Only the current one is expanded. When an item is
done it is deleted here and summarized in docs/done.md.

## 1. Every allocator function at -O0: C1 and C2

The functions reachable from malloc, free and calloc, bottom-up over the
call graph.

### 1.1 set_size (current)

A leaf: a slot's size recorded in its header (byte stores, one 32-bit
store, a byte load).

1. C1: whatever the generator lacks (stores at computed offsets).
2. Its spec on the slot's header bytes, C2.

### 1.2 The remaining functions

- The accessors (`meta_*`, `malloc_context_*`, `set_*`, `group_*`): C1 and
  C2, possibly generated.
- a_ctz_32's and a_clz_32's C2 (their specs are contracts already; they
  need the bit library, section 4).
- `activate_group`, `get_meta`, `get_nominal_size`,
  `enframe`, `account_bounce`, `record_seq`,
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
- A bit library (a_ctz_32's `x & -x = 2^tz(x)`, a_clz_32's bit smearing,
  the mask-heavy functions): `arith` reading products of non-literals in a
  polynomial normal form (a trusted extension: the ring facts it already
  relies on), then lemmas -- bit extensionality, `bits_and` / `or` / `not`
  bit by bit, bits under shifts and powers of 2, two's complement. Plan
  it before building it.
- A memory normalizer: `rd64` / `wr64` rules for rsimp, apartness by
  arith. Plan it before building it.
- Inversion lemmas for the remaining GIMPLE operations (8-bit and 32-bit
  loads and stores, more arithmetic), on demand.
- Possibly rename `rsimp` to `simp` once the old `simp` is not needed.
- `conj` building to the goal's grouping; one way of instantiating
  (`name[x := t]` instead of positional `all_elim`).
- Smaller frictions: `defs` unfolds in the goal only; `arith` ignores an
  equation whose sides are not known integers (`pow2(..) = ..`) silently.

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
