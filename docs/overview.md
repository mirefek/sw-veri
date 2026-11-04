# Overview

The project verifies basic software down to machine code (goal.md). The
first target is musl's allocator (mallocng `malloc` and `free`; `calloc`
and `realloc` later). The statement to prove is that, as machine code in
a static binary, these functions implement the malloc layer's specs, and
that the allocator's invariant holds when `main` starts. A second
statement is about a whole test program using them.

This file explains the approach. Its first part is an introduction:
- the big picture;
- one small function followed from its C source to the claim;
- a glossary at the end, for the project's terms.

The sections after the introduction are the reference: what is trusted,
each level, how a function is proven, and the repository.

The other documents:
- docs/language.md: the specification language SL and the proof language;
- docs/done.md: what is done, by area;
- docs/todo.md: what comes next.

## The big picture

```
  layers/claim_malloc.sl, claim_program.sl   the claims: closed statements
        ^                                    over the binary's bytes
        | proofs/mallocng/top*.core, claim.core, proofs/test/
  layers/malloc.sl                           what a client may rely on
        ^
        | proofs/mallocng/top.core (from mallocng's invariant)
  layers/mallocng.sl, mallocng_specs.sl      mallocng's invariant; each
        ^                                    function's purpose
        | C2: hand-written proofs, proofs/mallocng/fun/
  readable GIMPLE (generated)                GCC's GIMPLE as SL procedures
        ^
        | C1: automatic, the checker's engine (`c1` lines)
  machine code, in the binary                the bytes the claim contains
        |
        | its meaning
  spec/x86_64, spec/linux                    the model of the CPU and OS
```

Each arrow is a theorem checked by the kernel. The model at the bottom
and the claims at the top are what a reader has to trust and read. The
layers between are definitions, and the proofs connect them.

C1 is a compiler-correctness check: it knows nothing about the
allocator. C2 is about what the code means: there the invariant and the
purposes are proven. They meet at readable GIMPLE, the last compiler
stage that is still close to the C source.

## One function, from C to the claim

`get_slot_index` (musl's src/malloc/mallocng/meta.h) is a good first
example. It reads the 5-bit index of a slot from the slot's header byte:

```c
static inline int get_slot_index(const unsigned char *p)
{
	return p[-3] & 31;
}
```

**1. The machine code.** The binary (`build/test_malloc_O0`, built by
`scripts/setup.sh`) has two copies, one per translation unit. malloc.c's
is at 0x40318e:

```
mov  QWORD PTR [rsp-0x8], rdi
mov  rax, QWORD PTR [rsp-0x8]
sub  rax, 0x3
movzx eax, BYTE PTR [rax]
movzx eax, al
and  eax, 0x1f
ret
```

What each instruction does is the model's (`spec/x86_64`). The checker
decodes these bytes itself (the `steps` line, build/chain/steps.core).

**2. Readable GIMPLE.** `slc gimple --readable` turns GCC's dump into an
SL procedure (build/gimple-O0/sl/c_mallocng_malloc.sl after setup):

```
proc[World] get_slot_index(p: bits[64]) -> bits[32] {
  var t6: bits[32] = any bits[32]
  let t1 = padd(p, -3)
  let t2 = ld8(t1, 0)
  let t3 = zext[32](t2)
  t6 := t3 & 31
  return t6
}
```

Its operations (`padd`, `ld8`, ...) are defined in layers/gimple.sl. A
load outside the memory the function may see is undefined there, so
whatever the machine does then is allowed.

**3. C1: the machine code ⊑ the GIMPLE.** One line in
proofs/mallocng/machine/c1.core does it:

```
c1 get_slot_index c_src_malloc_mallocng_malloc_cfg.get_slot_index_fun gsitc
```

The engine walks the instructions and the GIMPLE side by side. Each
step is an instance of a proven rule (proofs/translate*.core), so no
proof text is written. The result is the theorem `gsitc.implements`: the
code at its address implements the GIMPLE as an ABI function. The ABI
covers arguments in registers, the stack frame, the return address and
the stack overflowing. The walk is on GIMPLE's control-flow graph form
(`_cfg`). One more line, in proofs/mallocng/machine/cfg.core, relates
that form to the structured form above (`refines get_slot_index_ref
...`).

**4. The purpose.** layers/mallocng_specs.sl says what the function is
for, on mallocng's abstract state (`A`, a ghost of the allocator's
memory):

```
proc[MallocAbs] get_slot_index_spec(c: Cfg, p: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)) && clear_below(A, g, uint(p)))
  either { overflow() } or {
    return any i: bits[32] where ex g: nat. starts_at(A, g, uint(i), uint(p))
  }
}
```

Read: if the invariant holds and `p` starts a block in slot `i` of
group `g`, the result is `i`. A call may also overflow the stack.

**5. C2: the GIMPLE ⊑ the purpose.** This one is a hand-written proof,
proofs/mallocng/fun/get_slot_index.core:
- `mp.gsi_run` runs the GIMPLE (`step`) and shows that the byte it reads
  is the slot header, whose low 5 bits are the index (`mp.slot_hdr`, a
  fact about the invariant);
- `mp.gsi` is the refinement;
- `mp.gsi_implements` composes it with C1 (`tr.implements_refine`,
  `tr.implements_abi_g`): the machine code at 0x40318e implements the
  purpose spec.

**6. Up to the claim.** Callers use `get_slot_index` only through that
theorem: get_meta's proof takes the contract and never looks at the
code. The functions are composed in this way up the call graph, to
`malloc` and `free`. Then:
- proofs/mallocng/top.core and top_free.core show that the purpose specs
  of `malloc` and `free` give layers/malloc.sl's client specs, under
  mallocng's invariant (layers/mallocng.sl);
- proofs/mallocng/init.core and the startup functions' proofs show that
  the invariant holds when `main` starts;
- proofs/mallocng/claim.core supplies the invariant as the witness and
  proves `musl_malloc`;
- proofs/test/ proves `musl_program`. It uses `malloc` and `free` only
  through their client specs, plus the proofs of the startup code and of
  the test program's own functions.

Larger functions look the same. They have more code, loops (an
invariant at the loop's head) and calls (the callee's contract). For
example, proofs/mallocng/fun/alloc_slot.core or try_avail.core.

## What is trusted

- The kernel (`slc/kernel`): a small second-order logic with conservative
  definitions and the 38 axioms of `core/prelude.core`.
- Its trusted extensions (`slc/kernel/src/ext/`): derived rules and
  decision procedures such as natural deduction, tautologies, linear
  arithmetic, lists, memory reads through writes and the simplifiers. Each one documents how it reduces
  to the kernel's rules. The symbols they read by name are pinned
  (`ext/pinned.rs`): the canonical prelude's (its text embedded in the
  kernel), a few layer definitions with fixed bodies (`store_le`, `le`,
  `bytes_at`, `x86.apart`), and the loop theorems simp relies on with fixed
  statements.
- The model (`spec/`): x86-64 and Linux, written in SL, assumed to describe
  the real machine.

Everything above the model is definitions (`layers/`) and theorems.
Front ends (the elaborator, the proof language, the generators) are not
trusted: a mistake there makes a proof fail, never a false theorem.

The claim, `slc claim malloc --elf BINARY`, is a closed statement. The
binary's bytes are a literal in it, and it comes with a summary of what it
rests on:

```
ex inv owned. Laws(inv, owned) && Init(inv, owned)
              && Impl(malloc) && Impl(free)
```

The chain checks the claim of the -O0 binary (`@claim`, first after the
libraries; the elaborated layers after it leave out what it defines) and
proves it in proofs/mallocng/claim.core, from no open lemma.

The program claim, `slc claim --program-exits 0,1` (`musl_program`,
layers/claim_program.sl), is about a whole client, tests/test_malloc.c:
every run of its process from an unprivileged exec state ends, and it
exits with 0 or 1 or dies of a stack overflow; no other crash, never the
exit 42 its pattern check would give. The chain proves it in
proofs/test/whole_top.core.

`Init` (`init_at_main` in layers/claim_malloc.sl) is about the runs that
reach `main`:
- of unprivileged processes only;
- the allocator may own, at `main`, its `static` bytes (all non-writable
  loaded segments -- the client's code and read-only data included -- and
  musl's data symbols), the thread descriptor up to errno (`fs_base ..
  +0x34`), and the auxiliary vector and AT_RANDOM bytes.
If the model could not reach `main` at all, `Init` would hold vacuously;
that some run does is still to show (docs/todo.md §1).

## The levels

Each level sees the state as its own world. A program at a level is a
nondeterministic relation from a state to an outcome: `ok(state, value)`,
`exc(state, e)`, or `diverge(trace)`. Undefined behaviour allows every
outcome.

- **L0, the machine** (`spec/x86_64`, `spec/linux`): exact.
  - Memory is pages, each with a kind (anon, heap or stack), plus bytes.
  - Faults are what Linux reports in `siginfo`.
  - The stack grows as `expand_downwards` does.
  - Placement of hint-less `mmap` and of `brk` is nondeterministic but stays
    out of the stack's space.
  - Checked against the real CPU by differential testing (`slc cputest`).
- **L1, the C world and the ABI** (`layers/abi.sl`). A C function sees:
  - its memory: a partial byte map, the C world's bytes (`c_bytes`,
    stored byte by byte: all but the ABI's, e.g. the stack protector's
    word) on the mapped pages that are not stack pages, plus the bytes
    of its live stack objects (`objs`); a valid page is a mapped one all
    of whose bytes are the C world's (the kernel's calls touch only
    those, and give only those);
  - the I/O, the thread pointer and the CPU features;
  - nothing of the stack, the registers, or where values live.

  An access outside the domain is undefined. The machine's stack (frames,
  spills, return addresses, growth) is the ABI's business. Its only
  C-visible effect is `stack_overflow`.
  - `abi_function` relates a machine run to a spec on the world. A function
    contract has the shape "pre ⇒ overflow ∨ post".
  - `stack_reserve` is the ABI's stack condition: the stack's space and its
    guard gap hold no other mapping. It is what lets any frame size be
    handled.
- **L2, readable GIMPLE** (`layers/gimple.sl`, generated by `slc gimple
  --readable`). This is GCC's final GIMPLE as SL procedures over the L1
  world, with C variables and callees by name. It is the abstraction that
  compiler optimizations preserve:
  - locals are values, not memory;
  - undefined behaviour is as GCC assumes it;
  - nondeterminism covers what C leaves unspecified;
  - a call may overflow the stack before and after the callee;
  - inline assembly GCC keeps opaque (`asm volatile` with a memory
    clobber) is a primitive with its own meaning (`cas32`: one atomic
    step), its instructions shown to implement it in C1 wherever they are
    (an out-of-line function or inlined). Under threads later, the
    primitives are where the per-thread simulation meets the memory model.

  musl's assembly functions (memcpy) have no GIMPLE: their readable
  models are written by hand at this level (layers/musl_asm.sl,
  musl_asm_cfg.sl), their registers the locals, an instruction GIMPLE has
  no operation for a primitive of its own (`move`, `move_words`: the
  string instructions); C1 checks them against the code like the
  generated ones.

  It comes in two forms of the same blocks:
  - structured (`--readable`): nested `if`s and loops, close to C -- what
    the C2 proofs are about;
  - the control-flow graph (`--readable --cfg`): GCC's basic blocks as
    they are, `bb` the block to run, a `loop` running it; each block ends
    with `bb := next` or a `return`. Every C control flow (gotos, any
    loop nesting) has it. C1 on it (`slc/cli/src/c1/cfg.rs`,
    `proofs/translate_cfg.core`): a claim at each block's entry (a cut
    point: the code's blocks' first instructions, known from the code),
    for every world and the block's live locals in their homes, each
    block walked once to the cut point it goes on at, gathered by one
    theorem (`tr.cfg_lvk`, from the loop rule over a set of cut points).
    The labels' addresses are found as the walks arrive. C1 uses this
    form; the C2 proofs are about the structured form.

  The two meet by a GIMPLE-level refinement, the CFG form ⊑ the
  structured form per function (`refines NAME LOW HIGH`,
  `slc/cli/src/c1/gref.rs`, rules in `proofs/gimple_cfg.core`): a
  simulation of the CFG's states by structured remainders, one per point
  (a label and its remainder), each point's block walked beside its
  remainder by congruence (the same terms, no operation's meaning), with a
  rank for the loop's termination. The structuring is untrusted: a
  function it fails on keeps C2 on the CFG. A function's spec then comes
  from its CFG C1, this refinement and its structured C2, by
  `tr.implements_refine` twice (`proofs/mallocng/machine/cfg.core`).

  The -O0 build is the first target. Optimized code can later be added as
  a GIMPLE ⊑ GIMPLE layer: the same cut-point theorem between two CFGs.
- **The malloc layer** (`layers/malloc.sl`): the abstract heap (live blocks
  as ghost state) and the specs of `malloc`, `free` and `calloc` (calloc's
  not yet claimed).
  - The allocator's invariant and owned memory are parameters, constrained
    by laws.
  - The frame law: client writes outside owned memory keep the invariant.
- **mallocng** (`layers/mallocng.sl`, `layers/mallocng_specs.sl`):
  - mallocng's invariant, over an abstract state determined by memory;
  - the specs of its internal functions, as contracts stating each one's
    purpose: on the abstract state (a ghost of the C world, `MallocAbs`),
    or on memory for the list and leaf functions.

## How a function is proven

For a function F, two halves:

- **C1, machine code ⊑ readable GIMPLE.** This is compilation correctness:
  no function-specific assumptions, and anything is allowed where GIMPLE is
  undefined.
  - A `c1 F SPEC PREFIX` line (`proofs/mallocng/machine/c1.core`) has the
    checker's C1 engine (`slc/cli/src/c1/`) walk F's code (its decode facts)
    and its readable GIMPLE side by side. Each step applies a rule instance
    through the kernel; no proof text is written. The engine is untrusted:
    the kernel records only the theorems its rules made, without
    hypotheses.
  - The decode facts come from a `steps` line (build/chain/steps.core,
    written by `slc steps`: the binary by its path and sha256, the
    functions). The checker (`slc/cli/src/steps.rs`) decodes each
    distinct encoding (`members`: no other row of the decoder matches) and
    proves `x86.step_*` (a step there runs that instruction) and, per
    instruction, `F.at_*` (from F's code `F.code` loaded, its fetch
    succeeds), through the kernel, no proof text. The instruction
    boundaries come from the untrusted interpreter. A `text` line
    (build/chain/text.core) the same way: the program text `text.code`
    (the functions' code in address order, the bytes between them) and
    `F.in_text` (F's code a piece of it, where a contract assumes the
    text loaded).
  - C1 is against the readable CFG (`slc gimple --readable --cfg`;
    `slc/cli/src/c1/cfg.rs`, `proofs/translate_cfg.core`): each block is
    walked once from its cut point, its claim proven for every world and
    locals, so a function's proof grows with its code, not its paths. A
    function of a `return` alone has no CFG and is walked straight.
  - The rules are proven once (`proofs/translate*.core`), per statement or
    instruction form.
  - **The rules' standard form**: every comparison of the two sides is a
    match; `arith` only for facts (bounds, definedness), never for
    recognizing a value written otherwise.
    - One normal form of values, by one normalizer N
      (`slc/cli/src/c1/nf.rs`): a fixed list of proven, oriented equations
      (`proofs/translate_nf.core`), applied innermost first, each step a
      kernel rewrite by an instance of one equation. Closed literal terms
      are numerals (evaluated: GIMPLE's `bits[64](-16)` and the machine's
      sign-extended immediate the same numeral), a cast of a word of its
      width (or narrower) is the word, a shift by a constant is a product
      by 2^k, sums and products by literals are in the ring's normal form
      modulo 2^n (sums nested to the left, terms ordered, literals gathered
      last, products by literals distributed; seen through the names of
      sums and products), commutative operands are in one order (by the
      kernel terms, literals last). The ring's equations rest on two
      integer congruences in `core/bits.core` (`mod_add_mod`,
      `mod_mul_mod`), so they hold for any width.
    - A rule producing a value has it as a variable r with a premise `r =
      E` (E the instruction's own expression): the register- and
      home-writing instruction rules, the loads (an indexed one's address
      too, `ad = iv + bv`), and the spec's operations (`tr.qs_op`: `r =
      e`, e the operation's lemma's value). The engine takes r := N(E), the
      premise by N's rewrites; a let's value is rewritten to its normal
      form first (`tr.qe_eq`). Every value is named in normal form (the
      check `C1_NF_CHECK=1` reports one that is not).
    - A rule consuming a value (a store) takes the machine's value u and
      the spec's x with a premise `u = x`, by N (equal normal forms: a
      match); a load's or store's address computed otherwise likewise.
    - A condition is decided by a fact in scope: the same, or one of the
      same comparison of operands with the same normal forms, rewritten to
      the condition's operands by N's proofs; lemmas the engine matches
      against state their terms in the normal form (`tr.bits_field0_n`).
    - Hints extend N: `c1 F SPEC PREFIX using L, ..` names proven equations
      (`all xs. H.. -> l = r`, H closed facts, by evaluation), applied
      after N's own at each node. An equation undoing another's (a hint
      against N's order) fails with the term, not loops.
  - Programs and states are related by a coupling at each point:
    - a location map says where each GIMPLE value lives (the engine is
      guided by the -O0 build's DWARF, `scripts/locmap.py`);
    - the memories agree on the world's domain;
    - the ABI's frame facts hold.
  - Calls use the call rule (`proofs/translate_call.core`).
- **C2, readable GIMPLE ⊑ F's spec.** Hand proofs run the GIMPLE backwards
  by inversion lemmas (`proofs/gimple_inv.core`; `proofs/mallocng/fun/`,
  the leaf functions' in `proofs/mallocng/code/`).
  - A callee is used only through its contract: the call's outcomes follow
    from any contract the callee refines.
  - A caller proves the callee's precondition at the call.

Transitivity gives machine code ⊑ spec: one lemma composes a function's
two halves (`tr.implements_refine`, `proofs/mallocng/machine/cfg.core`,
`proofs/mallocng/fun/`). The
functions are composed bottom-up over the call graph. A callee is a parameter of its caller's
GIMPLE, so each function is checked against its callees' specs.

## Repository

| path | contents |
|---|---|
| `spec/` | the trusted model (x86-64 encoding and semantics, Linux processes and exec) |
| `layers/` | ABI, GIMPLE, malloc, mallocng, the claim |
| `core/` | prelude (axioms) and the logic library (sets, naturals, records, lists, loops) |
| `proofs/` | machine and ABI lemmas, the bridge rules, GIMPLE's lemmas; the chain's order (`proofs/chain`) |
| `proofs/mallocng/` | mallocng: `machine/` (its C1 lines, CFG compositions), `code/` (GIMPLE's operations, the functions' runs), `model/` (the invariant read and kept), `fun/` (one file per function or family: its purpose refined, its machine code implementing it), the laws and the top of the claim |
| `slc/` | the toolchain: kernel, syntax, elaborator, interpreter, proof language, CLI |
| `scripts/` | building musl (`build-musl.sh -O0`), dumping GIMPLE, checking the chain while editing (`check.sh`) |
| `tests/` | C test programs, cputest limits |

Main commands (`slc/target/release/slc`):

```
slc check [PATH..]                          parse, type-check, elaborate SL
slc elab PATH.. -o OUT.core                 elaborate to core definitions
slc kernel-check [--no-cache] FILE.core..   check core files and their proofs
slc claim malloc --elf ELF -o OUT.core      state the claim
slc gimple --readable [--cfg] ...           GIMPLE dump to readable GIMPLE
slc steps ELF F.. -o OUT.core [--text T]    the `steps` line (decode facts of F's instructions) and the `text` line (the program text), both made in the checker
slc decode / coverage / cputest / heapcheck model and invariant testing
```

While editing proofs, `scripts/check.sh [FILE]` checks the proof chain
(up to FILE) with the caches of `kernel-check` (build/kernel-cache): a
file unchanged after the same statements is not checked again, nor, in a
changed file, a proof unchanged in the same context (the file up to it,
earlier proofs cut out) -- an edited proof is checked alone, in about a
second. `scripts/check.sh gen` first makes its generated files
(build/chain). The tests check without the caches.

`cargo test --release --manifest-path slc/Cargo.toml` runs everything,
including the C1 engine on every function. The tests that need
the musl build (`scripts/build-musl.sh -O0`) skip without it; with
`SLC_REQUIRE_BUILD=1` they fail instead.

## Glossary

- **SL**: the specification language of `*.sl` files (models, layers,
  specs), elaborated into definitions of the logic (docs/language.md
  Part I).
- **core file**: a `*.core` file, with declarations and theorems of the
  logic and proofs in the proof language (docs/language.md Part II).
- **slc**: the tool (`slc/`): kernel, elaborator, proof checker,
  generators and the C1 engine.
- **the kernel**: the small trusted checker every theorem goes through
  (`slc/kernel`).
- **the chain**: all core files in checking order (`proofs/chain`),
  checked by `scripts/check.sh`. Its last theorems are the claims.
- **claim**: a closed statement about the binary, made by `slc claim`
  (build/chain/claim.core, explained in build/chain/claim.summary.txt).
- **level / layer**: a view of the state and of programs, defined in
  `layers/` on top of the one below it.
- **world**: the state as one level sees it. GIMPLE's world (`World`,
  layers/abi.sl) is the C world: memory without the stack, the thread
  pointer, the I/O.
- **readable GIMPLE**: GCC's GIMPLE (its intermediate language) printed
  as SL procedures over the C world (`slc gimple --readable`). It comes in
  a structured form and a control-flow graph form (`_cfg`).
- **C1**: machine code ⊑ readable GIMPLE, per function, checked
  automatically by the engine from a `c1` line.
- **C2**: readable GIMPLE ⊑ a spec, per function, by a hand-written
  proof.
- **⊑ (refines)**: every outcome of the lower program is allowed by the
  higher one, where the higher one's precondition holds.
- **outcome**: `ok(state, value)`, `exc(state, e)` (an exception, such as
  an exit or a fault) or `diverge(trace)` (a run that never ends).
- **undefined**: every outcome allowed. It is used where C or the model
  leaves behaviour open, so that a spec over-approximates.
- **contract**: a function's spec in the shape "pre ⇒ overflow ∨ post".
  A caller is proven against its callees' contracts, not their code.
- **purpose spec**: a mallocng function's contract, stating what it is
  for on the abstract state (layers/mallocng_specs.sl).
- **abstract state (`A`, `MallocAbs`)**: mallocng's state as data: the
  groups, slots, metas and lists. It is a ghost: never in memory, but
  determined by it (`mallocng.abs_unique`).
- **invariant**: `alloc_inv`, a parameter of layers/malloc.sl. mallocng's
  (`mallocng.inv`) is the witness in the claim.
- **owned memory**: `alloc_owned`, the bytes the allocator may use and
  a client must leave alone.
- **laws**: what any invariant and owned memory must satisfy for a client
  to rely on them, such as the frame law (layers/malloc.sl).
- **overflow**: a stack overflow, the one machine-level failure a C
  function may show (`overflow()`, layers/abi.sl).
- **decode facts / `steps` line**: the theorems that the binary's bytes
  at an address are a given instruction, proven by the checker
  (build/chain/steps.core).
- **cut point**: the first instruction of a basic block. The C1 claim
  is stated there and each block is walked once.
- **location map**: where each GIMPLE local lives in the -O0 frame (from
  DWARF, build/locmap_O0.core). It guides the engine and is not trusted.
- **normal form (N)**: the one form values are written in during C1
  (`slc/cli/src/c1/nf.rs`), so that comparing two values is a match.
- **`step`, `mem`, `rsimp`, `arith`**: proof-language tactics: run a
  program, read memory through stores, rewrite, linear arithmetic
  (docs/language.md §13).
