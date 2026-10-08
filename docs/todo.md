# To do: ideas for later

Long-term ideas not scheduled yet, by area. Open design questions of the
spec language: docs/spec-language.md §14; the proof's milestones:
docs/proof-plan.md §5.

## Proof checker: speed

Not needed at the current times (docs/proof-checker.md §5); in order of
expected gain:

- **Step theorem generation.** The generated step theorems are now most
  of an uncached check (build/leaf_steps.core 3.5 s, the a_ctz/a_clz
  steps 1.4 s, proofs/x86_insn.core 1.0 s). Look there first if a full
  uncached check (CI) gets slow.
- **Memoised normal forms** of hypotheses inside `taut` / `simp`: the same
  hypothesis is re-normalised in every call.
- **Parallel checking**: statements first, then the proofs independently.

## C1 certificates

- **`tr.callee_io` for the remaining constructs** (generated per function
  by slc/cli/src/effects.rs): stores (`tr.eff_st8`/`st32`: a defined
  store's target is writable, the code is not, so the program stays
  loaded -- a forward lemma on `write_bytes`), calls (by the callee's own
  `FN.io`), loops (`while_rel`: validity as the invariant).

## Proof language

- **Grouped conjunctions with `conj`.** `conj(p1, .., pn)` builds the flat
  left-nested conjunction; a differently grouped goal still uses `taut`
  (`tr.push_ok`'s conclusion in translate_call.core; `tr.ok_abi` dropping
  a conjunct, `tr.sim_red` replacing one). Building to the goal's shape
  would cover them.
- **One way to instantiate.** `name[x := t]` covers parameters and leading
  `all`s by name; positional `all_elim(p, {t})` and `mp(p, {t}, ..)` are
  still used (~550 `all_elim` in proofs/). Migrate where it reads better.
- **More labels** in the large definitions and SL predicates the proofs
  take apart, as the need shows up.
