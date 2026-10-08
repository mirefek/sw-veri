# Proving the musl allocator claim

This is the plan for proving `musl_malloc`, the statement produced by
`slc claim malloc` (see `docs/spec-language.md`, sections 11–12): musl's
mallocng `malloc`, `free` and `calloc`, as machine code in a static binary,
implement the malloc layer's specs, and the allocator's invariant holds when
`main` starts.

The claim is a closed statement of the core logic: the binary's bytes are a
literal, the x86-64 + Linux model and the layers are kernel definitions, and
the only axioms are the 38 of `core/prelude.core`. What is trusted is the
kernel, those axioms, and that the model's definitions describe the real
machine. Nothing above the model may be trusted on evidence: every level
from there up is reached by proof.

## 1. Principles

**Top-down.** The reasoning system is built from the user's side: proofs
are written with high-level steps, and those steps are checked by trusted
extensions of the kernel (below), not compiled to primitive steps. The
extensions are sound by design and each documents how it reduces to the
primitive rules, so the reduction stays possible in principle and can be
done later, extension by extension, when the system has proven itself on
real work.

**A minimal kernel defines the logic.** `slc/kernel/src/env.rs`: modus
ponens, second-order instantiation, conservative definitions, literal
arithmetic, bytes literals, and the prelude's axioms. It does not grow;
everything else is an extension.

**Trusted extensions** (`slc/kernel/src/ext/`) add derived rules: natural
deduction with hypotheses, quantifier and equality rules, propositional
tautologies, later computation (evaluating closed terms) and decision
procedures (linear arithmetic, bit vectors). They are part of the trusted
base, kept small and separate from the kernel, and listed in every claim
summary.

**Untrusted front ends.** The proof language (`slc/proof`), and later the
symbolic executor and proof automation, only call the kernel's and the
extensions' rules. A mistake there makes a proof fail, never a false
theorem.

**No external solvers.** Arithmetic and bit-vector reasoning are done by
our own procedures, as extensions that know the logic's encodings (`nat`,
`bits`, maps).

## 2. The logical DAG

```
musl_malloc = ∃ inv owned. Laws(inv, owned) ∧ Init(inv, owned)
                           ∧ Impl(malloc) ∧ Impl(free) ∧ Impl(calloc)
│
├─ ∃-introduction with INV, OWNED: mallocng's invariant and owned memory, defined
│   on typed views of its data (ctx, meta areas, struct meta / group, bitmaps)
│
├─ Laws(INV, OWNED)
│   ├─ inv_wf, owned_private, owned_mapped           from INV's definition
│   └─ frame                                         INV depends only on owned bytes
│
├─ Init: from exec_state (unprivileged), the run reaching main ends in a state where
│   INV(empty heap) holds and owned ⊆ static ∪ thread descriptor ∪ auxv
│   ├─ startup (musl's _start … __libc_start_main) reaches main in state S_main
│   └─ S_main ⊨ INV, the allocator not yet initialized (init_done = 0)
│
└─ Impl(f), f ∈ {malloc, free, calloc}  ←  the function lemma of f
     function lemma of F:
       (C1) the callees implement their specs
              ⇒ implements2(F_addr, gimple_fun(F_gimple, callee specs))
       (C2) gimple_fun(F_gimple, callee specs) refines spec_F
       ⇒ implements2(F_addr, spec_F)            (transitivity, monotonicity)

     bottom-up over the call graph (no recursion):
       leaves     __mmap, munmap, __mprotect, memset, memcpy, __lock, __unlock,
                  ___errno_location                 (assembly or tiny: machine-level lemmas)
       then       get_meta, __malloc_alloc_meta, alloc_slot, nontrivial_free,
                  __malloc_allzerop
       then       __libc_malloc_impl, __libc_free, calloc, default_malloc, free
```

Below all of this, general lemmas proven once:

- logic: connectives, quantifiers, equality, choice;
- programs: rules for the prelude's program combinators (`bind_rel`,
  `while_rel`, `any_rel`, `refines`), i.e. sequencing, `if`, `while` with an
  invariant, calls, `havoc`, `any`, `require`, views;
- refinement: transitivity, `implements` monotone in the spec, the call rule;
- memory: reading a byte map after writes, framing (unchanged outside a
  region), page permissions;
- arithmetic: naturals, integers, `bits[n]` (wrap-around, masks, shifts,
  `ctz`, two's complement).

The new definitions the DAG needs: `INV` and `OWNED`, and one spec
`spec_F` per internal function (in terms of typed views of mallocng's
structures). Those are the design work of the proof; the rest is proof.

### 2.1 Worlds and their validity, by level (2026-10-08)

Each level sees the state as its own world, and assumes it valid in its
own sense; a valid world of a lower level corresponds to a world of the
level above.

| level | world | valid when | where |
|---|---|---|---|
| machine code | the x86 machine | the program (code, statics) loaded, the stack as the ABI has it at an entry | `abi.loaded`, `abi.entry_ok` |
| readable GIMPLE | the ABI's view (`abi.view`): memory, os, fs | -- (any world; the machine's validity makes it one) | |
| malloc | the abstract heap (`Abs`) | the invariant, `mallocng.holds` | layers/mallocng.sl |

- **C1** (machine code ⊑ readable GIMPLE) is compilation correctness: it
  holds for every world and every argument, with no function-specific
  assumptions. Where the C code has undefined behaviour, GIMPLE allows
  anything, so the machine matches trivially. Its assumptions are the
  machine-level validity above. A call needs one more piece of
  bookkeeping: after the callee returns, the world is valid again
  (`tr.returns_valid`: the input as it was, the events grown, the program
  loaded), unless the callee's spec is undefined there, in which case the
  caller's call is undefined too (`tr.callee_io`). This is a property of
  GIMPLE as a language (every operation keeps validity or is undefined),
  proven per function from its spec's structure
  (proofs/translate_effects.core), not a precondition a caller proves.
- **C2** (readable GIMPLE ⊑ the function's spec) holds the function
  contracts: "if the world is malloc-valid (the invariant) and the
  arguments satisfy P, then the function does X". Each function's
  assumptions are stated once there, as named definitions, and composed
  by proving the callee's precondition at each call from the caller's.
  Local functions may assume a weaker invariant (they break it
  temporarily); structuring these assumptions (no repetition, each
  function assuming what it needs) is part of C2's design.

### 2.2 Architecture: what each layer sees (2026-10-08)

Each layer's world holds only what its programs can legitimately observe;
the machine's details are absorbed once, where the ABI relates the machine
to the C world, not in every function's proof.

**L0 -- the machine** (x86-64 + Linux): exact. Memory is pages (with a
kind: anonymous, heap, stack) and bytes.

**L1 -- the C world and the ABI.** The world's memory is a *partial byte
map*: the machine's memory restricted to its domain -- the mapped pages
that are not stack pages, with their permissions, and the bytes of the
live stack objects (address-taken locals: `objs`). Objects (allocations,
lifetimes) may come in later layers; at malloc's level memory is raw.
- An access outside the domain is undefined: this one rule covers null
  pointers, unmapped memory, wrong permissions and dangling pointers into
  the stack.
- The machine's stack -- frames, spilled values, return addresses, its
  growth into free pages -- is not in the world. It is the machine's
  private business, constrained only by the ABI: callee-saved registers,
  the return address, and a callee not writing the stack above its stack
  pointer (no C object of a caller is there that it may reach).
- A function's world is its caller's world: the caller's frame is not in
  it, so a callee cannot touch it by construction.
- Running out of stack is the stack's only C-visible effect:
  `stack_overflow` may happen at every call (at a function's entry, before
  it does anything). On the machine, every fault caused by a stack access
  (a push, a `call`, an rsp-relative access; SIGSEGV, or SIGBUS for a
  non-canonical address) is a stack overflow. One lemma, at this level,
  shows that such a fault happens with the I/O of the last call boundary
  (frames are allocated in the prologue; a call's push maps everything
  above it), so it is matched by an overflow at that call -- for any frame
  size and any optimization level.

**L2 -- readable GIMPLE** (`slc gimple --readable`): GCC's final GIMPLE as
SL procedures over the L1 world, with the C function's variables and
callees by name. The one GIMPLE layer, for now of the -O0 build. Its
semantics is the abstraction the compiler preserves, so that GCC's
optimizations are refinements of it:
- *Observable*: the world's memory on its domain, the I/O (os), the
  results, termination, and `stack_overflow` at calls -- nothing of the
  stack, of registers, or of where values live.
- *Undefined behaviour* as GCC assumes it: signed overflow, null and
  out-of-domain accesses, misaligned accesses, `.CTZ (0)`, ...; no
  type-based aliasing (`-fno-strict-aliasing`). An undefined execution
  allows every outcome.
- *Nondeterminism* where C leaves things unspecified: uninitialised
  locals, the placement of stack objects, the contents of fresh memory.
- Locals are values, not memory: GCC may keep them anywhere, merge,
  remove or reorder them.
So an optimized program refines the unoptimized one when, for every world,
each of its observable behaviours is one of the original's (or the
original is undefined there); an optimization layer can be added as
GIMPLE ⊑ GIMPLE on this semantics.

**C1 -- machine code ⊑ readable GIMPLE**, per function, generated: a
simulation in which, at each program point, a *location map* says where
each GIMPLE value lives (a register, a frame slot, a constant) -- read off
the homes at -O0, off DWARF location lists and the register allocation
when optimized. Frame slots appear only in the location map, never in the
memory coupling, which is just "the machine's memory is the world's on
the world's domain". Instruction rules are per instruction class and
parametric in locations; the bookkeeping of calls (`tr.callee_io`) is
generated from the spec's structure.

**C2 -- readable GIMPLE ⊑ the function's spec**: hand proofs, with
explicit named preconditions (§2.1); the invariant and the laws.

Migration, each step keeping the chain checking:
1. L1: the world's domain (non-stack pages and `objs`; no `sp`), the ABI
   correspondence without the stack, the stack-fault lemma; the ABI glue
   re-proven.
2. L2: the stack mechanics out of layers/gimple.sl (`frame_at_call`, the
   private frame, `sp`); `alloc_objs` adds its objects to `objs`.
3. The bridge: location maps and the domain coupling; the instruction
   rules and the generator ported; the certificates regenerated.
4. The remaining -O0 functions (frames of any size, several homes, any
   number of arguments need nothing special any more).
5. Later: optimized code, through DWARF location maps.

Decisions made while porting the bridge (step 3):
- *The C world's memory at a call* is a view: `abi_function` takes the
  stack objects `objs` (above `sp`, on writable stack pages) and a memory
  `mem` with the machine's pages that agrees with the machine on the
  domain (`abi.view_ok`); the contract is stated on
  `world(sp, objs, mem)`. A raise is a world in `rec_and(World, {})`.
- *GIMPLE `usable`*: on a mapped non-stack page the page's permission;
  elsewhere the byte must be one of `objs` (and below 2^64). The frames
  clause of `world_matches` speaks of stack pages, not of mapped ones.
- *Calls in GIMPLE* (revised 2026-10-09): `either overflow; callee;
  either overflow` -- the callee on the caller's world, the caller's
  `objs` restored after it; undefined only if the thread pointer is
  broken. The world has no stack pages: at the entry its page map is the
  machine's without the stack's (`world_pages`). (An earlier port had put
  the stack's pages, `grow_stack` and the guard-gap check into GIMPLE's
  call to ease the bridge; that made every caller's C2 impossible -- a
  growth into a gap made any call undefined -- and was undone.)
- *The stack's reserve* (`abi.stack_reserve`, the ABI's stack condition at
  every entry): the stack's pages lie in its space (`stack_floor` ..
  `stack_top`, one run ending at `stack_top`), no other mapping lies in
  the space or in the guard gap below it, the gap fits above 0. Linux
  keeps it: it places hint-less mmaps and the brk heap below `mmap_base`,
  under the space and the gap (spec/linux/process.sl now says so), and
  growth stays within the limit (`x86.grow_rsv`). It implies
  `stack_gap_free`, so a push or frame access below the stack lands on a
  stack page, an unmapped page (growth or a fault) or faults -- never in
  other memory, for frames of any size. Linux's per-growth check alone
  (only the nearest mapping, only if accessible) would not exclude
  stack clash past a PROT_NONE page. Not covered: unlimited RLIMIT_STACK
  and MAP_FIXED or hinted mappings into the reserve.
- *The ABI's promise* (`world_matches`) also says: the world has no stack
  pages, the stack pages from the callee's return slot up are kept, the
  reserve is kept. The bridge carries the reserve in the coupling
  (`tr.mem`) and the entry's in `tr.inv` (`srsv`); `x86.stk_ext` (the
  stack's growth) keeps it.
- *Machine faults*: SIGSEGV codes 0, 1 and 3 (with `pkuerr`) are crashes
  of the ABI; `stack_gap_free` also says every stack page lies above
  `STACK_GUARD_GAP`. `thread_ok`: the thread pointer's 8 bytes are
  readable, not on stack pages, and point at themselves.
- *Coupling* (`tr.mem`): the world's `objs` are the entry objects, the
  memories match on the domain, and every object is an accessible byte on
  a stack page above `sp`; writes are allowed exactly where `tr.wbl` says
  (accessible, or an object not on a non-stack mapped page).

## 3. The systems that build the theorems

| | system | produces | status |
|---|---|---|---|
| E0 | kernel | primitive steps | exists |
| E1 | proof language and fact store | theorems in core files (`theorem … proof … qed`), checked on load | **first step** |
| E1x | extensions: natural deduction, quantifiers, equality, tautologies | high-level steps | **first step** |
| E2 | computation | `t = value` for closed terms: unfolding definitions, literal arithmetic, bytes of the binary, decoding instructions | next |
| E3 | symbolic execution | refinement theorems for SL programs (the x86 `step`, GIMPLE `run_fun`) on symbolic states, from the program rules | after E2 |
| E4 | decision procedures | linear arithmetic over nat/int, bit-vector facts | with E3 |
| E5 | SL-level proofs | proofs attached to SL `theorem`s, in SL syntax | later |

Where the parts of the DAG come from: machine-level function lemmas and
(C1) mostly from E3 + E2 + E4 guided by the compiler's structure (CFG and
DWARF variable locations give the cut points and the `coupled` relation
of `layers/gimple.sl`); (C2), the invariant and the laws from E5 proofs
written by hand; Init from E3 over the startup code.

## 4. The fact store

A fact is a theorem with its statement (a core term), its dependencies
(facts, definitions, axioms — by name and hash), and how it was obtained
(kernel steps only, or extensions used). Facts live in core files next to
the definitions they are about, and are re-checked when loaded; a changed
definition invalidates what depends on it. `slc facts status musl_malloc`
(to come) prints the DAG: proven, open, and which extensions each proof
relies on.

## 5. Milestones

1. **Proof language, extensions, logic library** (first version done):
   - the kernel accepts `theorem NAME(params): φ proof … qed` in core files
     (`syntax::load_with`); the proof text goes to a proof checker, which
     is not trusted: the kernel accepts only a `Thm` whose statement is
     exactly φ, and a `Thm` can only come from the kernel's rules or the
     extensions. `slc kernel-check` checks proofs;
   - trusted extensions (`slc/kernel/src/ext/`): `prop.rs` — which terms are
     syntactically propositions, and classical tautologies (over any
     atoms: `true -> a` is a proposition interderivable with `a`); `seq.rs` — sequents with hypotheses,
     modus ponens, instantiation, assumption and discharge, ∀-introduction
     and elimination, ∃-introduction, the choice witness, equality (refl,
     sym, trans, substitution, rewriting), definitions' equations,
     is_prop, literal arithmetic. Each documents its derivation from the
     kernel's rules;
   - the proof language (`slc/proof`):
     ```
     theorem subset_refl(s): subset(s, s)
     proof
       fix x
       have h: x in s -> x in s by taut()
       have g := gen(h, x)
       have d := unfold(subset)[a := s, b := s]
       show rewrite(sym(d), g)
     qed
     ```
     steps `assume`, `fix`, `have … := …`, `have … by …`, `show`; proof
     expressions are facts (`h`, theorems, axioms), instantiations
     (`eq_subst[p := x. x = a]`) and rules (`mp`, `discharge`, `defs`, `expand`, `refl`, `sym`, `trans`,
     `subst`, `rewrite`, `unfold`, `gen`, `all_elim`, `ex_intro`,
     `witness`, `prop`, `lit`, `taut`);
   - `core/logic.core`: 14 theorems — `imp_refl`, `eq_sym`, `eq_trans`,
     `true_i` and `dne_any` (`!!a -> a` for any term, ji-trust's
     `not_not_impl`) from the axioms alone; propositional, quantifier and
     definition examples with the extensions. Tests check that unsound
     steps are rejected (generalizing over a variable in a hypothesis,
     discharging a non-assumption, wrong witnesses, non-tautologies, proofs
     of other statements).

   Still to do in this milestone: theorems attached to SL files; hashes
   of the definitions a fact depends on (to invalidate proofs when a
   definition changes, across runs). Across runs, per file so far:
   `slc kernel-check` keeps each checked file's statements (its proofs
   replaced by `cached`, `slc/kernel/src/ext/cache.rs`) in
   build/kernel-cache, and takes a file from there when it is not newer
   than its entry and the statements before it are the same (their
   hash); `--no-cache` checks everything (the tests do).
2. **The top of the DAG** (done): `proofs/musl_malloc.core` proves
   `musl_malloc` from 8 open lemmas — the four laws, `init`, and
   `implements` for malloc, free and calloc — with `musl.inv` and
   `musl.owned` as placeholder definitions the proof does not look into:
   ```
   slc kernel-check core/prelude.core core/logic.core build/musl_malloc.core proofs/musl_malloc.core
     claim musl_malloc: proven from 8 open lemmas: musl.inv_wf, …, musl.impl_calloc
   ```
   What it added:
   - open lemmas (`lemma NAME(params): φ`) and conditional theorems
     (`slc/kernel/src/ext/facts.rs`): a sequent records the open lemmas
     it rests on and never becomes a `Thm` while any is left; a proof
     that uses one is recorded as conditional; `theorem NAME proof … qed`
     (no statement) proves a lemma or claim declared earlier; cycles are
     rejected; `slc kernel-check` prints what each claim and lemma still
     rests on (transitively). This is the first part of the fact store;
   - `slc claim malloc` names the binary's data (`musl_malloc.file`,
     `.main_at`, `.malloc_at`, `.free_at`, `.calloc_at`, `.static`,
     `.errno_offset`), so proofs refer to them by name;
   - the extension rule `Seq::conv`: a fact proves a goal that is the
     same after unfolding named definitions (also under binders, by the
     prelude's extensionality axioms);
   - proof language: `show by R` against the current goal (the statement
     with the `assume`d and `fix`ed parts taken off); goal-directed rules
     nest: `ex_intro({w1}, {w2}, p)` for `ex x1 x2. φ`, `defs(p, D…)`
     (`p` proves the goal with `D…` unfolded), `expand(p, D…)`.

   (The placeholders are since replaced by the real invariant: milestone 6.)
3. **Computation (E2)**: evaluate closed terms; first use: every instruction
   of the allocator decoded from the binary by proof.
4. **Program rules and symbolic execution (E3), arithmetic (E4)**; the
   function lemmas of the leaves (`__mmap`, `munmap`, …, `memset`).
   First part done — induction and arithmetic:
   - trusted extension `ext/arith.rs`: `arith(p…)` proves a goal from
     premises by propositional logic plus linear arithmetic over the
     integers (`+`, `-`, literals, `*`/`/`/`%` by constants, word
     operations mod 2^n, `<`, `<=`, `=`; Fourier–Motzkin with integer
     tightening, no external solver). Arithmetic is total: any term stands
     for its value (`int_val`), so the laws of the integers hold for any
     sets; an equation between sets, or membership in `omega` / `bits(k)`,
     is read only for terms known to be integers. It rests on standard
     theorems about the prelude's integers, listed in the module. Also
     `rec`: the recursion equations of `nat_rec` (the recursion theorem);
   - `core/nat.core`: `nat_ind` proven from `omega_ind`; examples
     (`dbl(n) = 2 n` by induction);
   - proof language: goal-directed `arith(…)` and `induct(base, step)`
     (the base and step goals are computed), `rec({t}[, h])`, and
     sub-proofs `have NAME: φ proof … qed` / `show [φ] proof … qed`, with
     their own `assume`/`fix`/`obtain` scope, closed at their `qed`.
   Tests check that `arith` rejects false or unjustified goals (`a < a`,
   commutativity of unknown terms, `-` below zero, wrong remainders,
   nonlinear facts).

   Lists (functions on a natural number, as in ji-trust): a literal
   `[a, b, c]` now elaborates to `seq_one(a) ++ seq_one(b) ++ seq_one(c)`
   (`seq_one` added to the prelude), so every list expression is a
   concatenation of pieces. Trusted extension `ext/list.rs`, over pieces
   flattened by associativity of `++` (opaque pieces must be known lists,
   `l in list_type(T)`):
   - `lists(p…)`: `A = B` when both have the same pieces;
   - `arith` reads `seq_len` of a list expression (singletons plus the
     lengths of its lists);
   - `at({L[i]}, p…)`: the element at i, found in the piece whose bounds
     `arith` shows from the premises;
   - `list_ext(…)`: extensionality.
   Examples in `core/list.core`; tests check that `++` is not treated as
   commutative, unknown terms are not lists, and out-of-range or
   undetermined indices are refused. Structural list induction is not yet
   there (index induction is `nat_ind`).

   Programs — symbolic execution (`ext/simp.rs`, trusted): a simplifier
   whose rules are theorems of the prelude (β for `letin`, projections of
   pairs and outcomes, record reads through `fn_update`, literal and
   constructor (in)equalities, connectives with true/false, the one-point
   rule, the definitions of `bind_rel`/`any_rel`/`is_ok`) plus one
   one-way step used only in positive positions of facts,
   `runs(mkprog(s o. R), S, O) -> R(S, O)`; then a path normal form
   (&& distributed over ||, existentials pulled out, `x = t` solved per
   path, two equations `x = a`, `x = b` giving `a = b`, contradictory
   paths dropped as they arise — also those refuted by an instance of a
   `all xs. !(ex ys. B)` literal). `simp(h)` turns
   `runs(P, s, o)` into P's paths; goal-directed `simp(p…)` proves a goal
   path by path (taut or arith), choosing witnesses for the goal's
   existentials by matching its equations with the path's. A goal
   `runs(P, s, o)` (the spec side of a refinement) is unfolded too, with
   the typing `pair(s, o) in univ(1)` that membership in `mkprog` needs
   (shown by the closure of universes; `app`, `fst`, `snd` are `empty`
   when undefined, so they stay in universes); its existentials are
   witnessed by a search over matches with the path's literals (e.g. the
   outcome of a sub-program from a lemma about it, `keep` folded), by the
   goal's own equations once those are bound, and by splitting an outcome
   seen only through its projections (`ex x. P(fst x, snd x)` is
   `ex a b. P(a, b)`). `print P`
   shows a fact while writing a proof. `proofs/malloc_client.core`: from
   the spec alone, `free(NULL)` changes nothing, `free(p)` of a live
   block returns with p freed (using the law `free_step`: a step always
   exists), and malloc returns NULL when no place for a block exists.
   The spec's fallbacks are explicit: `let x = any? T where P else S`
   (malloc may always fail, must when no block is possible) and
   `havoc … where P else S`, so no case is undefined by accident.
   Leftover paths: when `simp` cannot close some paths, it reports each
   (up to 3, with the count) as a fact ready to paste, `all x0 .. xk. L1
   -> .. -> Ln -> goal`. Prove it — keeping only the hypotheses it needs
   — and pass it to `simp`: facts of the form `all xs. A1 -> .. -> An ->
   C` are rules, used on every path whose literals match the Ai (the
   others are shown by taut/arith once all xs are bound); C is added. An
   equation C needs no hypotheses: its left side is matched against the
   goal's and the path's terms, and the goal is rewritten left to right.
   Example: `malloc.result_live` (a non-null result is aligned and live)
   with the rule `malloc.set_block_at`.
   Loops: `simp(…, {l0 l. I}, {l. m})` gives an invariant (over the
   loop's first state l0 and its current state l; for `for` loops, l is
   the program state paired with the counter) and optionally a variant.
   On each path `simp` shows, from the path, I at the start, I kept by an
   iteration of the body (an `ok` outcome), and for the variant: a
   natural number that decreases. Then the loop's literal becomes its
   outcome: it stopped in a state with I, by its condition or by an exit
   of the body (`break`/`return` are exceptions of the body), or — without
   a variant — it diverged. The kernel theorems `while_inv`/`while_var`
   (`core/loop.core`, proven by induction) are this step. Example:
   `malloc.terminates` (malloc's spec never diverges on a well-typed
   heap state), using `malloc.idle_step` (the allocator can always keep
   memory as it is), which rests on a small library of functions and
   records (`core/records.core`: `union2`, `rec_and` states,
   `fn_update(f, k, app(f, k)) = f`, fields through ghost extensions).
5. **(C1) for all functions** — machine code ⊑ GIMPLE.
   First target: the `-O0` build (`scripts/build-musl.sh -O0`,
   `build/test_malloc_O0`, its claim `build/musl_malloc_O0.core`); an
   optimization layer (optimized ⊑ unoptimized GIMPLE) can be inserted
   later. At `-O0` GCC's final GIMPLE is the unoptimized one, nothing is
   inlined (62 functions reachable from malloc/free/calloc), and every
   local has its stack slot.
   The intermediate is **readable GIMPLE** (`slc gimple --readable`, see
   `layers/gimple.sl`): each function as an SL proc close to the C source
   — C variables by name, structured `if`/`loop` with early returns,
   struct fields through accessors from DWARF, callees as parameters — and
   the human proofs (C2) are about it. It is not trusted and needs no
   separate check against GIMPLE's semantics: machine code ⊑ R and R ⊑
   spec give machine code ⊑ spec for any R. (The deep form, `Function`
   data run by `run_fun`, stays for reference.) All of mallocng, calloc
   and free translate, except inline assembly with operands (`a_cas`,
   `a_or`, `__syscall1`): leaves, specified and checked at the machine
   level directly.
   The machine side of a function: `slc steps ELF CLAIM F -o OUT` proves,
   per instruction encoding, what `step` runs (the decoding), and per
   instruction of F where a step from it goes (`F.at_A`) and its outcome
   when its memory accesses succeed (`F.ok_A`: the successor state, with
   the accesses as hypotheses; computed by the simplifier, proven in the
   file). A run of F (`proofs/get_slot_index_run.core`) chains these
   outcomes, one path per instruction (get_slot_index: 0.2 s; expanding
   every instruction's semantics with its fault cases took 1.2 s and 456
   paths). The faults are separate cases, for the ABI's crash branch and
   the spec's undefined behavior.
   General facts the trusted `simp` relies on are tracked like any open
   lemma: unrolling a loop is the lemma `while_unroll` (core/loop.core,
   open for now), so a proof that unrolls one is a conditional theorem
   resting on it, and so is every claim built on it, until it is proven.
   The ABI glue (C1 for a function, `implements2_at`) is proven once, in
   machine terms (proofs/abi_glue.core): `abi.implements_intro` (the
   contract from the runs that start at the function with entry_ok),
   `abi.ub_case` (the spec raises on the view of memory the ABI gives:
   anything), `abi.ret_case` (a normal return: the final state a Machine,
   callee-saved registers, rsp, rip and df as the ABI says, rax:rdx and
   memory what the spec's run on the view gives). A function's C1 then
   connects its run lemma and its spec lemmas: get_slot_index
   (`gsi.implements`, proofs/get_slot_index_abi.core, 100 lines, 0.8 s)
   chooses the view showing the stack slot as the machine writes it (it
   is scratch space: `abi.slot_view`) and splits on whether p[-3] is
   defined. Typing obligations (a state after updates is a Machine, ..)
   are simp's: record types are checked field by field. It rests only on
   the open loop lemmas. The same glue gives C1 for upgradelock and
   resetlock (a store to a global: `loaded` keeps static data off the
   stack pages, so the return address stays) and a_ctz_32
   (`ac.implements`, proofs/a_ctz_32.core: a 4-byte slot, the de Bruijn
   table read on the view; the machine's `neg`/`and`/signed `imul`
   connected to the source's `0 - x`/`&`/`*` by `ac.hash`). A leaf
   function's red-zone slot (n bytes at rsp - k, n <= k <= 8) is covered
   once, in proofs/abi_stack.core (`abi.slot_access`, `abi.ret_access`,
   `abi.slot_view`). Found on the way: a call with fewer arguments than
   the function's parameters left the spec computing on `args[i] =
   empty` while the machine read whatever the register held; the
   generated `_fun` wrappers now `require len(args) >= n` (C: undefined).
   Functions with branches (is_bouncing, get_stride:
   proofs/is_bouncing.core, proofs/get_stride.core) state their run lemma
   as a summary, `ex m1. o = ok(m1, empty) && abi.returns(s, m1, vm, r)`
   (flags and scratch registers left out), and a spec that leaves the
   world as it is closes with `abi.ret_view`. get_stride reads the meta's
   bit fields; the machine reads the same word as 1, 2 or 8 bytes, and
   small bridge lemmas (`gb.*`) connect the two, the arithmetic by simp's
   word normalizations and arith. step_seq is still open: its loop stores
   the counter to the stack slot between byte stores to the context, which
   needs separation of the slot from static data inside a loop, an
   unrolled spec loop, and a world-changing ret_case.
   (Retired 2026-10-06: these per-function proofs -- get_slot_index_run,
   get_slot_index_abi, a_ctz_32, is_bouncing, get_stride, upgradelock,
   resetlock, step_seq -- and the lemmas only they used (`abi.ret_view`,
   `abi.returns`, `abi.run_cut`, `abi.frame_apart`, `g.usable_bytes`) are
   removed. C1 for all seven functions is now by the generated certificates
   proofs/FN_tr.core (docs/bridge-pattern-design.md); the text above records
   how the first proofs were built.)
6. **The invariant; (C2) per function; the laws.** First part done:
   - `layers/mallocng.sl`: mallocng's invariant for a given binary
     (`Cfg`: the file, the addresses of ctx, the lock, `__libc`). An
     abstract state `Abs` (ctx fields, meta areas, free metas, the metas in
     use with their fields, active lists, what each slot holds) determines
     the `footprint`; `holds` says that memory *seen only through
     `mview(vm, footprint)`* agrees with it and that it satisfies
     mallocng's structural invariants: the area list and secret, the meta
     partition, the group headers and masks, the in-band slot headers
     (`enframe`/`set_size`), nested groups, the active lists (only the head
     has available slots — `activate_group` and `queue` assert it), the
     code and constant tables intact, single-threaded with the lock free,
     `ctx.brk`, permissions, and separate regions.
   - The four laws are proven for any `Cfg` (`proofs/mallocng.core`), with
     a library of set facts (`core/sets.core`: `ite`, `upair`, pair
     injectivity, `app(fn_build(..), a)`, extensionality). `frame` holds
     because the invariant reads memory only through the view, and rests
     on `mallocng.abs_unique` (the abstract state is determined by the
     memory: open).
   - The malloc layer had to change — the claim was false before:
     `heap_wf` required live blocks to stay mapped read-write, but the
     frame law let a client `mprotect` or `munmap` pages of its own
     multi-page block, so `inv_wf` and `frame` contradicted each other.
     The client contract is now: blocks are under the allocator's control
     — the client writes their bytes, but leaves their mappings, the
     allocator's own memory and the program break alone (the frame law
     assumes the pages of live blocks and `vm.brk` unchanged; mallocng's
     `brk` calls would otherwise unmap client memory). Live blocks are
     read-write as part of the invariant, so malloc's result is.
     STATIC now contains all read-only segments (`size_classes` is in
     `.rodata`).
   - Proof language: `obtain x, h from P` (∃-elimination), `unsel(h)` /
     `sel(p)` (set-builder membership), multi-line steps.

   - Sanity check on real heaps (evidence, not proof): `slc heapcheck ELF
     [ARGS]` runs a program under ptrace, tracks its blocks through
     breakpoints on malloc/calloc/free, and after each call builds `Abs`
     from memory (the abstraction function: the blueprint of
     `abs_unique`) and evaluates every conjunct of `rep` with the SL
     interpreter. `--selftest` corrupts a good state eight ways (secret,
     slot use, a header byte, a forgotten block, a wrong size, a page
     protection, a code byte, an area's check word) and requires each to
     be reported. `tests/stress_malloc.c` mixes all size ranges; slow
     tests: `cargo test --release -- --ignored`. For this the invariant
     is worded with bounded quantifiers only (the footprint as a list of
     ranges, `used` as a sorted list, slots as lists) — equivalent, and
     the form induction proofs want.

   Status: `musl_malloc` proven from `mallocng.abs_unique`, `musl.init`,
   `musl.impl_malloc`, `musl.impl_free`, `musl.impl_calloc`. The invariant
   is a first draft: the function proofs will show what is missing (and
   `init` whether it holds at `main`).
7. **Init** — startup to `main`.
8. **Hardening**: reduce extensions to kernel steps where it matters.

## 6. Structured automation for (C1) (plan, 2026-10)

(Superseded, 2026-10-06: C1 is by translation -- `slc translate`'s
certificates checked against proofs/translate.core and
proofs/translate_store_loop.core, docs/bridge-pattern-design.md. The tools
6.1-6.3 describe -- `symex`, `spec_run`, `bridge` -- and their open lemma
`abi.loop_sim` are removed; this section records how they worked.)

The six leaf functions done so far (get_slot_index, upgradelock,
resetlock, a_ctz_32, is_bouncing, get_stride) were proven with one tool
doing everything: `simp` executed the machine code (unrolling
`run_to_return`), unfolded the GIMPLE procs and searched for the spec's
outcome, typed records, and normalized word arithmetic, all over a flat
list of path literals. That stops scaling:

- cost: every machine step adds ~5 literals and rule matching rescans the
  path, so a run is quadratic in its length; step_seq's loop (32 x 6
  steps) did not finish in 15 minutes;
- the spec side unfolds a whole proc into one formula and searches for a
  witness of its outcome (get_stride: past the 4096-path limit until the
  eager outcome heuristic);
- normal forms depend on what a path knows, so facts and goals stop
  matching in ways that are hard to see (`bits_add(64, x, 0)` vs `x`);
- a failure is "1 path left" with a large formula; the proof structure
  (which block, which statement) is lost;
- every function needed hand-written bridges between the machine's view
  of its values and the GIMPLE's.

The structure the proofs need is the compiler's: at -O0 each GIMPLE
statement becomes a short instruction sequence, every local lives in its
stack slot, and loops stay loops. The plan uses it in three parts, each
usable on its own. Trusted extensions remain fine where they make the
interface simpler; the aim is proofs that are short, steerable and fast,
with failures that point at a block and a statement.

### 6.1 Symbolic execution of machine code (`symex`)

A proof-language step, backed by an extension, that runs the machine from
a state at an address to a set of stop points and returns what it found:

```
have r := symex(h, stop: return)            // h: runs(abi.run_to_return(), m, o)
// r: ex m1. o = ok(m1, empty) && <path condition> && <final state>, per path
```

- State: kept structured, not as literals: registers, flags, rip, and
  memory as the entry memory plus a list of stores, each tagged with its
  region (frame, a static object, the object a pointer argument points
  to). Only the current state is kept; a step costs the same at step 10
  and step 1000.
- Steps: the `F.ok_A` lemmas from `slc steps` (one per instruction), each
  applied by instantiation, not found by rule matching. A conditional
  jump splits the state on its condition (`x86.cond_eval`), giving one
  path per side; a path whose condition is contradictory is dropped.
- Memory: reads resolve through the store list by region (two regions
  are disjoint by an `x86.apart` fact or by being distinct objects);
  stores to the same address replace older ones. This is what simp does
  now with `apart` literals, as a data structure.
- Hypotheses the steps need (accesses allowed, the frame apart from static
  data) are collected and returned as the run lemma's premises, stated
  per region (`reads(frame, 16)`, `writes(__malloc_context + 848, 32)`),
  so the user sees what the run assumes.
- Stop points: the return (the loop of `run_to_return` leaves), a loop
  head (6.3), a call (later: callees' contracts).
- Output for a function: its run lemma, as today's summaries
  (`abi.returns(s, m1, vm, r)`, one result term with `ite` for branches).
  It rests on `while_unroll` as now (or on a lemma for `run_to_return`
  cut at a point, open like the other loop lemmas).

Validation: regenerate the run lemmas of the six functions (their C1
proofs must stay green), then step_seq's, unrolled: linear time should
make 200 steps cheap.

Status (first version, `slc/kernel/src/ext/simp/symex.rs`): `symex(h,
facts..)` returns `O = ok(S1, empty) || ..` with each path's conditions
and its open values (flags) existential; values overwritten later are
dropped. The state is a term normalized by simp's term rules (memory by
the `x86.apart` facts), the path keeps only its branch conditions and the
code fact, premises of a step are shown from the facts (literal, instance
of a `∀` fact, `A -> h` with A decided, typing, taut / arith), and a
premise that cannot be shown is reported with the instruction's address.
The six run lemmas are now `have r := symex(..)` and `simp(r, ..)` for
the stated form (the leaf chain: 27 s before, 16.5 s now); step_seq's
whole run (two paths, 32 loop iterations, ~200 steps) takes under a
second, where simp had not finished in 15 minutes. Not yet: premises
collected and returned instead of required; stop points other than the
return.

### 6.2 Forward execution of the spec (`spec_run`)

The same for the readable GIMPLE: run a proc statement by statement on a
symbolic world, with the operation lemmas of `proofs/gimple.core`
(`g.ld8_ok`, `g.ldbf_ok`, `g.elem_ok`, `g.st32_ok`, …, each with its `_ub`
twin), and return

```
have sp := spec_run(gs.spec, w, args)
// sp: defined(w, args) -> runs(app(gs.spec, args), w, ok(w', pair(r, y)))
//     !defined(w, args) -> runs(app(gs.spec, args), w, exc(w, e))
```

- the outcome is constructed, not searched for: each statement's lemma
  gives the next world and value, so there is no witness search and no
  path explosion from the program's ok/exc/diverge alternatives;
- `defined` is collected from the operations' side conditions along the
  way (each load's `mem_defined`, each signed operation's range), split
  by the branches taken; it is what the hand-written `gs.defined`,
  `ib.defined`, … were;
- accessor procs (`meta_maplen`, …) are executed by their definitions, or
  by lemmas given to `spec_run`;
- a `loop` with a constant trip count can be run through (step_seq's 32);
  otherwise it needs 6.3.

This replaces the per-function `proc_ok`/`proc_raises`/`fun_ok`/
`fun_raises` lemmas (about 150 lines per function now).

Status (first version, `slc/kernel/src/ext/simp/spec.rs`):
`spec_run({P}, {W}, facts.., op-lemmas..)` returns the conjunction of
`all ps. C.. -> runs(P, W, O)`, one per branch (the program's undecided
`if`s, the operations' lemmas: `_ok` and `_ub` give two branches). The
conditions are stated in word form (`gimple.wrap`/`sval`/`fits` of
literal types as `bits_add`/`sint`/true, a sign extension's signed value,
non-wrapping address sums as integer sums), and the range tests the facts
decide are gone: for is_bouncing four branches (out of range; the
counter usable, above 99 or not; not usable). A `_fun` wrapper runs as its
proc, so the proc lemmas serve as operation lemmas for it. is_bouncing's
four spec lemmas are now `spec_run` + `simp` (72 lines fewer, `ib.in_range`
gone), and so are get_stride's (nine branches; 180 lines fewer, its five
accessor lemmas gone). The undefined-behaviour branches come as one
statement `all e. e in univ(1) -> !D -> runs(P, W, exc(S, e))`, D the
conjunction of the branches' `C1 -> .. -> !Cn`, so a `raises` lemma is
`simp(r, hn, he)`: its hand-written `defined` implies D propositionally.
`defined` is still written by hand in the statement.

Loops (2026-10): undefined behaviour raises from any world (the `_ub`
lemmas give `exc(s2, e)` for any s2, e), so a failure after earlier stores
needs no other ABI rule. A loop is reasoned about as a loop, its trip
count as if a variable, on both sides:
- spec: `spec_run({P}, {W}, {l. I}, {l. m}, ..)` runs the body once from a
  state with the invariant I; the obligations of `while_exists`
  (core/loop.core; invariant kept with a smaller variant, the branches
  covering the case) are decided or stated as hypotheses, and the result
  is `pre -> obligations -> (ex lv. D1 && runs(P, W, O1)) || ..` over the
  loop's exits. step_seq: the coverage obligations decided; entry and
  preservation are `ss.entry`, `ss.step` (proofs/step_seq.core, the bytes
  zeroed so far `ss.zs(b, i)` by `nat_rec`);
- machine: `abi.run_from(m0, s, o)` (the run continued at s) and
  `abi.run_cut` (proofs/abi_loop.core: an invariant at the loop's head and
  a variant; induction, no open lemma); `symex(h, .., {H})` stops at the
  head H with `run_from`, and starts from one. step_seq: entry to the head
  0x4024f5 runs.

The general theorems about loops (core/loop.core): `while_cases` -- every
run stops, leaves through its body (an exception), or diverges
(`diverge(t)`); `while_inv` / `while_var` -- the same with an invariant,
divergence ruled out by a variant; `while_exists` -- a run that exists
(spec side). For step_seq's loop, its post-state `ss.exit` (i = 32,
unmap_seq zeroed), with `ss.entry`, `ss.step` the lemmas spec_run proves
its obligations by; the spec is then `ss.fun_ok` (defined: the world
`ss.res(w)`) and `ss.fun_raises` (not defined: a raise), each a few
simp calls over spec_run's statement, its parameters chosen (`part(r,
{k})`, `all_elim`).

Open for step_seq's C1: the machine invariant at the head (rip, rsp, the
memory `store_le(zm(b, i), slot, 4, i)` with the machine's zeroed bytes
`zm` likewise by `nat_rec`), symex around the loop with `abi.run_cut`,
and the ABI glue (`abi.ret_case`). (Superseded: step_seq's C1 is
proofs/step_seq_tr.core, by translation, its loop by an invariant and a
variant at the head (`tr.wf2`); proofs/step_seq.core and `abi.run_cut`
are removed.)

### 6.3 The bridge: readable GIMPLE to machine code (simulation)

Revision (2026-10-05): the per-function co-execution described below searches
(bridge-search-inventory.md). The proposed replacement is in
bridge-pattern-design.md: statement patterns proven once, and a function's
proof as a syntactic matching of its code against the readable GIMPLE.

Principle (2026-10): a function's behaviour is reasoned about only on the
readable GIMPLE (spec_run, simp, loop invariants: C2 and the convenient
specs). The machine code appears only in the bridge, which proves (C1)
without any behavioural reasoning: it checks that the compiled code does
what the GIMPLE does, piece by piece, and a theorem proven once makes that
a refinement of the whole function. GCC is not verified; each compiled
function is validated (translation validation), the method being general.

- cut points: the entry, each loop's head, the return (later: calls). A
  GIMPLE `loop` (a `while_rel` over iterations) corresponds to the
  machine loop it was compiled to: its head the first address a machine
  path visits twice (the natural loop's header at -O0, where the loop
  condition is tested, as the GIMPLE iteration starts with it);
- the coupling at a cut point (`coupled` of `layers/gimple.sl`, for the
  readable form): memory agrees outside the frame, the GIMPLE locals are
  in their homes (at -O0 the C variables in their stack slots, from DWARF
  `DW_OP_fbreg`; step_seq's `i` at rsp - 4), rsp, the return address and
  the callee-saved registers as at entry, the thread's state (os, fs_base,
  cpu) the same;
- a segment (from a cut point to the next ones): the GIMPLE run by
  spec_run's machinery, the machine by symex, from coupled states; each
  machine path matched with a GIMPLE branch: its conditions implying the
  branch's, the end states coupled at the same next cut point, or both
  returned with the same results and world, or the GIMPLE's undefined
  behaviour (anything allowed). No behavioural reasoning: the conditions
  compared are each side's own tests and memory effects;
- a loop: at its head both states generalized, related by the coupling
  only (the coupling is the loop's invariant, nothing about what the loop
  computes); one iteration checked as a segment; the library's loop rule
  makes it the whole loop, the correspondence full: a terminating machine
  run passes the head finitely often (induction on the passes), a
  diverging one infinitely often -- segments have no backward jumps, so
  are finite -- and an infinite GIMPLE run follows (each pass's matching
  iteration chosen, by recursion), with the same trace (the coupling keeps
  the OS state, so the event logs, equal at the heads; a run's trace is
  the limit of an increasing chain, a cofinal part of it has the same
  limit);
- the result, per function: `abi.matches(spec, args, s, o)` -- every
  machine outcome o from the entry s is the spec's raising (undefined
  behaviour), or a return matching the spec's ok outcome (world, rax:rdx),
  or a divergence with the spec's same trace -- and one theorem, proven
  once from `abi.ub_case`, `abi.ret_case` and a divergence case, makes it
  `abi.implements2_at`;
- the lemmas: a proof passes the run's facts and its function's own
  lemmas (the instructions' step lemmas, a spec's table); the generic ones
  the bridge takes from the library itself (`BRIDGE_LEMMAS`, the result
  resting on them as on premises): the frame's accesses, the memories'
  agreement, the stores, the flags -- and of the GIMPLE operations' lemmas
  those for the operations the spec uses (the most specific family
  covering their outcomes: `elem(p, i, 1)` by g.elem1_ok), the arguments'
  only for a spec with arguments.

Milestones: (1) the glue: `abi.matches` and its theorem (with the
divergence case); (2) the bridge for loop-free code (an extension
co-running both sides per segment), checked on is_bouncing, a_ctz_32,
get_stride; (3) loops: generalized heads and the loop rule; (4) step_seq's
C1 by it, then the six existing functions again. Later, per statement
pattern of -O0 code, lemmas proven once could replace the per-occurrence
checks.

What the user writes for a function, the target:

```
theorem ss.implements: all statics. ctx.in_statics(statics) -> abi.implements2_at(..., step_seq.code(), statics)
proof
  simulate(step_seq, ss.spec)
qed
```

with failures reported per obligation: "loop body 4024df..4024fa against
`st8(..); i := sadd(i, 1)`: at the head, slot i = bits_add(32, i, 1)
expected, found ..". The six existing proofs become a few lines each; the
bridge lemmas (`gb.*`, `ac.hash`) turn into obligations of single blocks,
where the arithmetic is small.

Loops with symbolic trip counts (most of mallocng's loops: over slots,
over pages) need 6.3; 6.1 + 6.2 alone can unroll constant loops only.

### 6.4 Word arithmetic as library lemmas

The facts behind the bit-field bridges are ordinary arithmetic: a shift
right is division by a power of two, `and` with a low mask is a
remainder, a little-endian word is its first byte plus 256 times the
rest. They go into a library (`core/words.core`) as lemmas that 6.1–6.3
and simp use, instead of more special cases inside simp; the word rules
added to simp during get_stride move there where they can.

### Order

1. 6.1 `symex`: the six run lemmas regenerated; step_seq's run, unrolled.
2. 6.2 `spec_run`: is_bouncing and get_stride without hand-written spec
   lemmas; step_seq's spec (unrolled loop, 33 stores).
3. step_seq's C1 with 6.1 + 6.2 and the ABI glue (`abi.ret_case`: the
   frame store is scratch, `abi.slot_view`'s matching half).
4. 6.3 `simulate` on step_seq (no unrolling), then the others; then the
   first function with a loop over a symbolic bound.
5. 6.4 alongside, as lemmas are needed.

## 7. dequeue end to end: what the layers and the proof language made easy and hard (2026-10-08)

dequeue (mallocng's list unlinking: two arguments, a red-zone frame,
64-bit loads and stores through pointers, branches on 64-bit equality, an
early return) is the first function with both halves:

- **C1** (machine code ⊑ readable GIMPLE): generated,
  proofs/dequeue_tr.core (1218 lines, 10 theorems, with its
  `tr.callee_io`). It needed new rules (64-bit field loads/stores, cmp of a
  home with je/jne), and before that the frame generalization
  (proofs/translate_frame.core: frames of any size, homes kept by a
  determined `tr.hkeep` chain, the generic entry `tr.entry_n`).
- **C2** (readable GIMPLE ⊑ spec): by hand.
  - layers/mallocng_specs.sl (57 lines): `dequeue_spec` is a named
    precondition (the words involved usable, aligned, apart) and its
    effect as a function of the memory.
  - proofs/gimple_inv.core (310 lines, reusable): inverting GIMPLE.
  - proofs/mallocng_c2.core (480 lines): the word lemmas, the accessors,
    and the two cases of dequeue; the main case is 167 lines. Result:
    `ms.dequeue_c2: refines(dequeue, dequeue_spec, World)`.

### What worked

- **The layers.** The C world (memory a partial byte map, `usable` its
  domain, `objs`) makes the spec short. C2 never mentions the stack,
  registers or frames, and C1 never mentions the list.
- **`apply` with higher-order inference.** `g.bind_inv` (a step's
  continuation, given the step's one outcome) infers its continuation
  lambda from the hypothesis. Peeling a GIMPLE statement is one line
  (`apply(g.letin_e, apply(g.bind_inv, h, det))`), with no restated terms.
  Premises given as `simp()` get their goal from `apply`.
- **simp for small inversions.** `padd`'s determinism follows directly from
  its unfolded hypothesis.
- **Loops by invariant and variant** (`while_var`, `while_exists`):
  `write_bytes` is proven for every n, both directions, in about 60 lines
  each, with no unrolling.

### What was hard (with proposals)

1. **Goals behind a definition.** `fix` and `assume` do not see through
   `g.det(..)`. Every such lemma restates the unfolded goal as
   `have g: … proof … qed; show by defs(g, D)`.
   Proposal: an `unfold D` step on the goal, or `fix`/`assume` looking
   through definitions.
2. **`taut` and simp as arguments need a goal.** So `taut(h)` cannot
   extract a conjunct inline. Destructuring (`have a b c := h`) must name
   exactly the flattened conjuncts.
   Proposal: `_` for the rest of a conjunction, and goal-less `taut`/simp
   where `apply` supplies the premise (it does for simp already).
3. **Equations have no direction.** `taut` does not use symmetry
   (`!(m = N)` versus `!(N = m)` needed a three-line proof each time).
   simp may use a fact `l = r` right to left: here it blew a word read back
   from memory into the whole written memory.
   Proposal: oriented rewriting for given facts (`simp(→e, ..)`), and
   tautologies modulo symmetric equality.
4. **No structure-preserving normalization of a hypothesis.** The
   goal-less `simp(p)` normalizes everything, including the `bind_rel`
   shapes the next step needs. Selecting a branch took small lemmas
   (`g.pick`, `g.pick2`, `g.pick0`) and `out_state(ok(a, b)) = a`.
   Proposal: goal-less simp honouring `keep(..)`.
5. **SL functions with a block body** elaborate to a `choose` over a
   program run, which is unusable in proofs; I rewrote the spec with
   expression-only functions.
   Proposal: elaborate `let`-only blocks to nested `letin`.
6. **Two forms of an address.** GIMPLE's `mem` yields `int_add(p, off)`,
   while SL's `Addr` arithmetic yields `bits_add(64, p, off)`, so every
   step converted (`ms.addr`).
   Proposal: one form (GIMPLE's `mem` returning the `bits_add` form when
   defined).
7. **Reading after writing** is a chain of `ms.rd_wr_far` with one
   apartness fact per pair of words: mechanical, but a third of the main
   case.
   Proposal: a memory normalizer for `rd64`/`wr64` from apartness facts
   (as `symex` had for the machine).
8. **Error messages print expanded `let`s.** A failing step shows terms of
   thousands of characters where the proof text says `V2`.
   Proposal: the printer folds the proof's abbreviations back.
9. **GIMPLE inversion is new for C2** (C1 only ever ran specs forwards).
   `gimple_inv.core` covers what dequeue uses. The other operations (8-,
   16- and 32-bit loads and stores, arithmetic, calls) follow the same
   pattern; then a C2 proof is a chain of `bind_inv` steps that a tool
   could emit, as the C1 generator does, leaving only the memory facts by
   hand.

### Status (2026-10-08)

1. Done: `unfold [D..] [in h]`, implicit unfolding at a mismatch (also
   `fix`/`assume` through a defined goal, `mp`/`apply` premises,
   destructuring), `irreducible NAME`.
2. Done: `have a b .. := h` / `r..`; goal rules inline in `apply`/`mp`
   (already so).
3. Done: `flip`; `taut` takes `a = b` as `b = a` (and `!=` as `!(=)`);
   `rsimp` rewrites left to right only.
4. Done: `rsimp(h, only, ..)` simplifies a fact with exactly the rules
   given.
5. Done: a `fn` block body is the term of its value (`letin`, `ite`); no
   `choose`; nondeterministic statements rejected.
6. Done: arith reads symbolic widths; `bits_add_nowrap` and friends
   (core/nat.core) are simp rules, their bounds shown by arith.
7. Open: a memory normalizer (rd/wr rules for rsimp with apartness by
   arith) -- to be planned.
8. Done: messages fold abbreviations (a proof's `let`s) back.
9. Open: inversion lemmas for the remaining GIMPLE operations; calls (the
   caller's C2 from the callee's C2 only).
