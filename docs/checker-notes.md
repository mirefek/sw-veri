# Proof checker: notes from use (2026-10-08)

Observations from developing proofs/translate_call.core and the a_clz_32
certificate, with the improvements they suggest. Worked through one by one.

## 1. Caching

`slc kernel-check` rechecked the whole chain from core/prelude.core on
every run. Measured (one run, timings vary with load):

| part of the chain | time |
|---|---|
| libraries, x86 model, steps, ABI/GIMPLE proofs | ~7 s |
| proofs/translate.core | ~1.8 s |
| proofs/translate_store_loop.core | ~0.2 s |
| proofs/translate_call.core | ~30-45 s |
| a generated certificate | ~1 s |

Almost all of a 40-55 s check went into files not being changed.

**Implemented.** Per checked file, build/kernel-cache holds its statements:
the file with each `proof ... qed` replaced by `cached` (a conditional
theorem: `cached rests(lemmas)`). A file is taken from its entry when

- the file is not newer than the entry (the entry is dated as the file
  when it was read, so a change during the check counts as newer),
- the statements of the files before it are the same (a hash chain over
  their statement texts: editing only a proof upstream keeps later
  entries; changing a statement rechecks everything after it),
- the entry was written by the same checker (its executable's date), and
  in the same position (first file: axioms allowed).

Otherwise the file is checked and its entry written (only on success).
`cached` is accepted only when loading an entry
(`syntax::load_cached`), never in a source file; the trusted entry is
`slc/kernel/src/ext/cache.rs`. `slc kernel-check --no-cache` neither reads
nor writes the cache; the tests use it.

Measured on the full chain (25 files): 36 s uncached, 0.27 s all cached,
2.2 s after touching proofs/translate.core (only it rechecked).

## 2. Language annoyances

- **Mismatch errors are huge and point nowhere.** A `modus ponens ... does
  not apply` error printed thousands of characters; the cause was one
  subterm (`4205681` vs `bits_add(64, a2, bits_sext(...))`). Report the
  first differing subterm and its path instead.

  **Implemented** (`Printer::mismatch`, `Printer::short`): modus ponens,
  `apply`, `ex_intro`, `trans`, `defs` (after unfolding), a block's or
  `show`'s goal, and a theorem's statement now report

  ```
  modus ponens: the fact does not match the premise `tr.implements_at(bits_add(64, ...), G0, ...)`
    first difference at: tr.implements_at, argument 1
      expected: bits_add(64, 4205803, bits_sext(32, 64, 4294967174))
      given:    4205681
  ```

  The path goes through implications by premise number ("after premise k"
  when one side has fewer), conjunctions by conjunct (however nested),
  and other symbols by argument, noting the other differing parts on the
  way. Terms in messages are cut to 400 characters; `SLC_FULL_ERRORS=1`
  prints them whole. The `tr.call1` error went from several thousand
  characters to 277.
- **Restating formulas.** `assume` repeats the goal's hypothesis verbatim
  (`u2` in translate_call.core: a six-line formula twice); extracting a
  conjunct restates it (`have slt: int_lt(S, ...) by taut(ic)`). Wanted:
  `assume eo` taking its formula from the goal; positional conjunct access
  (`ic.3`); `obtain x o1, h from e` for several witnesses.

  **Implemented** (slc/proof/src/lib.rs): `assume h1 h2` (the goal's next
  premises), `fix x y`, `h.k` / `R(args).k` (by `and_left`/`and_right`,
  core/logic.core: modus ponens, no search), `have h1 h2 .. := P` (any
  `have` form, its conjuncts as written, `_` skips), `obtain x y, h1 h2
  from P`, a line starting with `:=` continuing the step. All hand-written
  proofs use them now: the conjunct extractions in translate_call.core,
  abi_bridge.core and translate.core by hand; the redundant assume
  formulas (3,360) and runs of `fix`/`assume` lines by
  scripts/tidy_proofs.py (the checker reports the assumes whose formula
  is the goal's premise: `SLC_TIDY=1`). core/ and proofs/: about 6,200
  lines shorter.

  **Judgement.**
  - Speed: the big win. Extracting a conjunct with `taut` (or
    `simp(i, keep(..))`) from a large conjunction searched over all its
    atoms, ~0.5 s per use on the 20-conjunct `tr.inv_call`; a projection
    is a few `mp`s. translate_call.core 30 s -> 0.25 s, abi_bridge.core
    7.5 s -> 0.65 s, translate.core 3 s -> 0.9 s; the whole chain
    uncached 36-55 s -> 6.6 s.
  - Reading: `assume hi hr hh hrs hmm` under a statement right above reads
    well; `obtain m1 a k, oe kk m1M .. from expand(h, abi.crashes_at)`
    replaced chains of obtain + taut. A block-local `let OKC(vv, o) := ..`
    named a 5-line formula used four times -- worth doing more.
  - Weak spot: positions in long conjunctions. `have _ _ _ _ rspm fo _ ..
    sM _ _ _ hlt _ := expand(hi, tr.inv)` (26 positions) is hard to read
    and easy to miscount; `i.21` is opaque. **Next idea: labelled
    conjuncts in definitions** (`def tr.inv(..) := mM: m in Machine && ..`),
    so proofs say `i.sM` or `have {sM, hlt} := i`.

    **Implemented** as term metadata (slc/kernel/src/term.rs): a term may
    carry a label, which equality and hashing ignore and no rule reads;
    rebuilding a node keeps it, and where a variable is substituted the
    variable's label (the outer one) wins. So a labelled conjunct inside a
    definition or a theorem's statement -- under binders, in a premise, in
    an `ex` body -- keeps its label through instantiation and unfolding.
    Written `name: φ` as an operand of `&&` (printed so; in parentheses
    where an operand cannot stand). In proofs: `hi.sM` (unfolding
    `tr.inv` at the head), `have {rspm, fro, sM, slt} := hi`,
    `have {xM = cM} := gt` (renamed), `obtain m2 a0 k0, {oe} from ..`.
    Labelled now: `tr.inv`, `tr.inv_call`, `tr.matches_t`,
    `abi.crashes_at`, `x86.grown_typed`; the positional destructurings of
    them are gone (`tr.inv_call`'s own proof: 15 lines -> 4). Not yet:
    SL predicates (`abi.world_matches`, `abi.overflow_ok`), which would
    need the elaborator to carry labels.
  - Still `taut`: rebuilding a conjunction from parts (`tr.ok_abi` drops a
    conjunct, `tr.sim_red` replaces one). A cheap builder (`conj(p1, ..)`
    by `and_intro`) would cover it.
- **`rewrite` / `expand` act on every occurrence**, under binders too. To
  rewrite only a value (not the program containing the same subterm) an
  auxiliary equation was needed (`vq` in `tr.ssub32_ok_lit`). Wanted:
  occurrence selection or a restricted position.
- **Small inconsistencies.** `taut` / `defs` need a named goal
  (`show by taut(hk, defs(...))` fails); four ways to instantiate a lemma
  (`name[p := ...]`, `all_elim(name, {x})`, positional `mp(name, {x}, ...)`,
  `apply`); `simp` does not chain equations stated after the facts
  (`rewrite(trans(...))` instead).

## 3. Speed

In translate_call.core a few big blocks of `tr.call1` take 3-8 s each, one
`apply(tr.post_call, ...)` 2.7 s, and each `taut(ic)` projecting a conjunct
of the large invariant ~0.5 s (435 `taut(` uses in the file). The time is
overhead (re-normalising the same hypotheses, large terms), not missing
decision power, so no new trusted decision procedure is proposed.

Ideas, least added trust first:

1. Conjunct projection without `taut` (`ic.k` as a chain of and-elimination
   steps): no new trust.
2. Memoised normal forms of hypotheses inside `taut` / `simp`: the same
   trusted code, cached.
3. Theorems checked in parallel (statements first, proofs independent):
   concurrency in the checker.
4. Prefix / file caching (item 1 above): trust in the cache, or development
   only with a full check in CI.
