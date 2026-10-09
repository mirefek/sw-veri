# Done

What the verification of musl's allocator has reached, by area. Each
item is a short summary of finished work; details are in the files named.

## The model and the claim

- **x86-64 and Linux in SL** (`spec/`). The instruction table and
  decoders cover all 2426 instructions reachable from malloc, free, calloc
  and the startup code. The model also has:
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
  - linear arithmetic over integers and words, with symbolic widths;
  - lists;
  - the path simplifier `simp` and the rewriting simplifier `rsimp`.
- **The proof language** (docs/language.md). It has implicit unfolding at
  mismatches, destructuring by position or label, `apply` with
  higher-order matching, `flip` and `unfold`. Error messages show the
  first difference, with the proof's abbreviations folded back.
- **Libraries** (`core/`): logic, sets, naturals and words, records,
  lists, and loops. For loops, `while_inv`, `while_var` and
  `while_exists` are proven by induction, with no open lemmas.
- **The checker**: a per-file cache. The main chain checks in about 5 s
  uncached and 0.2 s cached.

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

- `proofs/musl_malloc.core`: `musl_malloc` is proven from
  `mallocng.abs_unique`, `musl.init`, and `Impl` of malloc, free and
  calloc.
- `layers/mallocng.sl`: mallocng's invariant, a first draft.
  - The four laws are proven for any configuration
    (`proofs/mallocng.core`).
  - `slc heapcheck` evaluates the invariant on real heaps under ptrace,
    with a self-test that corrupts heaps eight ways.
- `proofs/malloc_client.core`: client facts derived from the specs alone.

## Functions

- **C1 by translation**, generated certificates (`proofs/*_tr.core`) for
  a_ctz_32, a_clz_32, get_slot_index, is_bouncing, get_stride, step_seq
  (a loop, by invariant and variant at its head), upgradelock, resetlock,
  decay_bounces, dequeue (malloc.c's copy) and dequeue_head. The rules
  cover:
  - frames of any size;
  - a generic entry with register arguments;
  - the prologue as instructions;
  - 8- to 64-bit loads and stores;
  - branches.
- **Calls in C1** (`tr.call`, `tr.call1` in `proofs/translate_call.core`):
  - any frame of at most 64 KiB, 1 to 6 register arguments, the result in
    rax:rdx (or rax);
  - the push's fault is a stack overflow by the guard gap;
  - the homes and the whole frame survive the callee.

  A caller's `tr.callee_io` (its returns keep the world valid for GIMPLE)
  is generated from its callees' (`tr.eff_call`).
  `proofs/mallocng_link.core` links a_clz_32 with a_ctz_32 and
  dequeue_head with dequeue.
- **C2**, against contracts in `layers/mallocng_specs.sl`:
  - dequeue (`ms.dequeue_c2`);
  - dequeue_head from dequeue's contract only (`ms.dequeue_head_c2`),
    and with musl's dequeue (`ms.dequeue_head_c2_dq`); as a C function
    value (`ms.dequeue_head_fun_c2`).

  The generic call lemmas (monotonicity, inversion under a contract) are
  in `proofs/gimple_inv.core`.
