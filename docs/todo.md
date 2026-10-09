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

- **A bit library (next).** What the allocator does with bits (GIMPLE
  of malloc.c / free.c):
  - masks and shifts by literals (`& 31`, `& -4096`, `>> 4`, `sc | 1`):
    `x mod 2^k`, `x - x mod 2^k`, `x div 2^k` -- arithmetic;
  - bit sets (avail / freed masks): `2 << k`, `mask & ~act`, `(m >> i) &
    1`;
  - the lowest set bit `x & -x` (try_avail, alloc_slot, malloc);
  - smearing `x | x >> 1 | ..` (a_clz_32, enframe);
  - de Bruijn: `(2^k * 0x077CB531) >> 27` into a table, k < 32.

  The plan, bits as math lemmas (no bit-blasting of words; core/bits.core
  has the bits of each operation and extensionality):
  1. A goal rule `bitwise(p..)`: a word equation by extensionality, `bit`
     pushed through the operations by those lemmas (registered: `bit_rule
     NAME`), then closed by taut / arith over the index with the facts.
     Masks by literals rewritten to div / mod for `arith` the same way.
  2. Lemmas on top: `x & -x = 2^tz(x)` (x != 0); smearing (x in [2^k,
     2^(k+1)): after the five steps 2^(k+1) - 1); `(2 << k) - 1` the mask
     of bits 0..k.
  3. `cases({k}, a, b, R)`: a goal for a literal range of k, each case by
     R (`eval` for the de Bruijn table).
  4. a_ctz_32's and a_clz_32's C2 (their specs are contracts already).
- `arith` diagnostics: when it fails, list the equations it could not
  read (sides not known integers).
- Review the code base (slc, proofs, layers) for bad code practices, a
  bounded pass (e.g. `translate.rs`).

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
