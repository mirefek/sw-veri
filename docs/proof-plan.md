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
   definition changes, across runs).
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
     naturals (`+`, `succ`, literals, `*`/`/`/`%` by constants, `-` where
     defined, `<`, `<=`, `=`; Fourier–Motzkin with integer tightening, no
     external solver). A term counts as a number only if a premise says so
     (`t in omega`, `t in bits(k)`, or `t` equated to a number). It rests
     on standard theorems about the prelude's naturals, listed in the
     module. Also `rec`: the recursion equations of `nat_rec` (the
     recursion theorem);
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
   path, contradictory paths dropped). `simp(h)` turns
   `runs(P, s, o)` into P's paths; goal-directed `simp(p…)` proves a goal
   path by path (taut or arith), choosing witnesses for the goal's
   existentials by matching its equations with the path's. `print P`
   shows a fact while writing a proof. `proofs/malloc_client.core`: from
   the spec alone, `free(NULL)` changes nothing, and `free(p)` of a live
   block returns with p freed — or no allocator step was possible, since
   `havoc … where P` with no solution is undefined (see open question).
   Loops (`while_rel`) stay opaque in `simp`: an invariant rule is next.
5. **(C1) for all functions** — machine code ⊑ GIMPLE.
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
