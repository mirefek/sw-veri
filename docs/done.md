# Done

What the verification of musl's allocator has reached, by area. Each
item is a short summary of finished work; details are in the files named.

## The model and the claim

- **x86-64 and Linux in SL** (`spec/`). The instruction table and
  decoders cover all 2426 instructions reachable from malloc, free, calloc
  and the startup code, and all reachable at -O0. The model also has:
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
  - linear arithmetic over integers and words, with symbolic widths,
    products as monomials, Euclidean division by a symbolic divisor and
    nonnegative products, equals for equals (congruence closure of the
    facts' equations), its cases searched by splits with unit propagation,
    pruned by infeasibility, with no limit on the atoms;
  - lists;
  - memory reads through writes (`mem_read`: apart / the same / inside,
    each decided by arith);
  - the path simplifier `simp` and the rewriting simplifier `rsimp`.
- **The proof language** (docs/language.md). It has implicit unfolding at
  mismatches, destructuring by position or label, `apply` with
  higher-order matching, `flip` and `unfold`, and cases of a disjunction
  taken from the fact (`have c: case k of P proof`), and `step`: a run of
  readable GIMPLE inverted step by step (binds by one-outcome facts or
  lemmas, branches by conditions, the choices named), and the memory
  rules (`mem`, `mem_read`; views, frames and closures registered per
  layer, proofs/mallocng_mem.core): with them queue's and dequeue's runs
  went from about 300 to 110 lines. `bitwise` decides bits by registered
  bit rules and one arith call; `cases` takes a literal range case by
  case. Goal rules prove
  `mp` / `apply` premises in place; `arith` reads powers of numerals as
  constants; `rsimp` reduces program outcomes' parts; a `show` must end
  its block. Error messages show the
  first difference, with the proof's abbreviations folded back.
- **Libraries** (`core/`): logic, sets, naturals and words (a word is
  determined by its bits), records, lists, and loops. `core/bits.core`:
  division by powers of 2, a word's bits under `/`, `mod` and `*` by 2^k,
  shifts, `and` / `or` / `xor` / `not` bit by bit, the complement, `x - 1`
  and `-x` around the lowest set bit, bit extensionality. For loops, `while_inv`, `while_var` and
  `while_exists` are proven by induction, with no open lemmas.
- **Codebase review**: the extensions' soundness holes closed
  (arith overflow and widths, simp's matching and literal substitution,
  names read by meaning: pinned prelude, definitions and loop lemmas),
  each with a regression test; the elaborator rejects what would change a
  program's meaning; the cache keyed by source and checker hashes; unused
  lemmas deleted.
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
  These files and the laws are checked by the tests (`claim_proofs_check`).

## Functions

- **C1 by the checker's engine** (`c1` lines, `proofs/mallocng_c1.core`;
  no proof text: rule instances applied through the kernel, untrusted) for
  a_ctz_32, a_clz_32, get_slot_index, is_bouncing, get_stride, step_seq
  (a loop, by invariant and variant at its head), upgradelock, resetlock,
  decay_bounces, dequeue (malloc.c's copy), dequeue_head, queue,
  free_meta, size_to_class, set_size and enframe. The rules cover:
  - frames of any size;
  - a generic entry with register arguments;
  - the prologue as instructions;
  - 8- to 64-bit loads and stores, 32- and 64-bit arithmetic on registers
    and homes;
  - signed and unsigned branches;
  - stores through a register's pointer, a register holding fewer bytes
    used as a wider one, the stored low byte of 32-bit arithmetic (by the
    words' arithmetic modulo 2^8);
  - an aggregate's zero-initialization (`pxor` and SSE stores against
    GIMPLE's `st_bytes`, `proofs/translate_zero.core`).
- **Calls in C1** (`tr.call`, `tr.call1` in `proofs/translate_call.core`):
  - any frame of at most 64 KiB, 0 to 6 register arguments, the result in
    rax:rdx (or rax);
  - entries with the stack unaligned (GCC calls `a_crash` so):
    `tr.implements_at_u`;
  - the push's fault is a stack overflow by the guard gap;
  - the homes and the whole frame survive the callee.

  All contracts assume one loaded program text (`text.code`, generated by
  `slc steps --text`), so linking needs no widening. A caller's
  `tr.callee_io` (its returns keep the world valid for GIMPLE) is
  generated from its callees' (`tr.eff_call`). `a_crash` (`hlt`) has the
  undefined contract (`proofs/a_crash.core`); callers' specs exclude it by
  their preconditions. `proofs/mallocng_link.core` links a_clz_32 with
  a_ctz_32, dequeue_head with dequeue, queue with a_crash, free_meta with
  queue, and size_to_class with a_clz_32.
- **C2**, against contracts in `layers/mallocng_specs.sl`:
  - dequeue (`ms.dequeue_c2`);
  - dequeue_head from dequeue's contract only (`ms.dequeue_head_c2`),
    and with musl's dequeue (`ms.dequeue_head_c2_dq`); as a C function
    value (`ms.dequeue_head_fun_c2`);
  - queue, for any a_crash (`ms.queue_c2`), and as a C function value
    (`ms.queue_fun_c2`);
  - free_meta from queue's contract (`ms.free_meta_c2`), with musl's queue,
    and as a C function value (`ms.free_meta_fun_c2`); the malloc
    context's address a parameter of the spec;
  - size_to_class from a_clz_32's contract (`ms.size_to_class_c2`, the
    least class covering n, checked case by case of the leading-zero
    count), and as a C function value; read-only tables are a
    precondition on the world's bytes (`table_ok`);
  - a_ctz_32 (`ms.a_ctz_32_c2`: x & -x, the de Bruijn index, the table
    entry tz(x)) and a_clz_32 from a_ctz_32's contract (`ms.a_clz_32_c2`:
    smearing to 2^p, p x's top bit), proofs/mallocng_bits.core; with them
    size_to_class with musl's a_clz_32 and a_ctz_32
    (`ms.size_to_class_c2_linked`);
  - set_size (`ms.set_size_c2`, and as a C function value): the reserved
    count in the slot's header byte, its word at the slot's end, case by
    case of the count (0, below 5, 5 and more), proofs/mallocng_slots.core;
  - get_stride (`ms.get_stride_c2`, and as a C function value): a group's
    slot size from struct meta's bitfield word, which GIMPLE reads in parts
    (`g.bytes_split`, `g.bytes_bound`, `g.ldbf_det` in
    proofs/gimple_inv.core; `ms.gs_word`), and the size classes' table;
  - enframe from get_stride's and set_size's contracts (`ms.enframe_c2`,
    and as a C function value), its spec in property form: any p 16-byte
    aligned in the slot with room for n bytes (`enframe_at`), as the code's
    offset (cycled, a byte) is reduced below the slack by the smeared mask
    (`ms.ef_mask`); the header writes, then set_size on the memory they
    leave (the meta's mem word and the thread pointer's word apart from the
    slot, in the precondition).

  The generic call lemmas (monotonicity, inversion under a contract, and
  `gc.contract_call` / `gc.contract_call1`: a call under a callee's
  contract in one step, its outcomes folded into an overflow or the
  contract's return) and the operations' one-outcome lemmas are in
  `proofs/gimple_inv.core`.
- **Composition**: machine code implements the spec, from C1 and C2 by one
  lemma (`tr.implements_refine`; every case of matching is of the spec's
  runs, `tr.matches_t_mono`), for a_ctz_32, a_clz_32, size_to_class,
  dequeue, dequeue_head, queue, free_meta, set_size, get_stride and
  enframe (`proofs/mallocng_compose.core`, a caller's with its linked C1
  and its callees' C2).
