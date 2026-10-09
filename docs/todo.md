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

- **A memory normalizer (current)** -- what remains of a C2 proof after
  `step`: per load or store, the world kept a world, each word's
  usability kept (nested `ms.word_wr`), a read after writes (chains of
  `ms.rd_wr_far` / `ms.rd_wr_same` with apartness facts), nested
  `fn_update(s, "vm", ..)`, and each operation's lemma instantiated by
  hand (queue's linked case: ~45 of its 55 lines).
  A procedure of its own, not rsimp: the decision is which write a read
  hits, made by a fixed algorithm.
  1. Two canonical primitives on byte maps, `store_le(B, a, n, v)` and
     `le(B, a, n)`; what specs and GIMPLE use are views of them,
     registered with the lemma that connects them (the extension point):
     `mem write mallocng_specs.wr64 ms.wr64_store`, `mem read
     mallocng_specs.mnext ms.mnext_rd`, `mem frame mallocng_specs.word_ok
     ms.word_ok_bytes` (a predicate the bytes do not matter to), ..
  2. A read of m bytes at b in w_k(..w_1(M0)..), the writes from the
     outermost in, each of n bytes at a, in this order: apart (`a + n <= b
     || b + m <= a`): past it; the same (a = b, n = m): its value;
     contained: its bytes from that offset (zero_meta's zeros); else stop,
     naming the write undecided. Each test one arith call on the integer
     facts given (bounds, `al8` -- a literal modulus --, `m != P`); each
     decision one canonical lemma: a checked proof, no search, nothing
     trusted. A frame predicate of M: of M0, a step per write.
  3. Interfaces: `mem(f..)` a goal rule (`read = v`, `word_ok(V3, ..)`);
     `mem_read({t}, f..)` the equation `t = value`, the value computed;
     `step .. with ms.setnext_det, .. using f..`: operations' lemmas
     matched with the operations, their premises (world, words'
     usability) by `mem`, each value read resolved by `mem_read`.
  4. Measure on queue's linked case (~55 lines to ~10 expected) and
     `ms.dq_linked`; set_size written with it.
  The user gives the aliasing facts a precondition provides (`m != P`,
  alignment, bounds); a failure names the write and the cases unproven.

- A bit library (a_ctz_32's `x & -x = 2^tz(x)`, a_clz_32's bit smearing,
  the mask-heavy functions): `arith` reading products of non-literals in a
  polynomial normal form (a trusted extension: the ring facts it already
  relies on), then lemmas -- bit extensionality, `bits_and` / `or` / `not`
  bit by bit, bits under shifts and powers of 2, two's complement -- and a
  case split over a literal range (`cases j in 0..32`, for the de Bruijn
  table). Plan it before building it.
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
