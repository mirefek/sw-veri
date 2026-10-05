# The bridge's searches: inventory (2026-10-05)

Goal: the bridge translates a function directly. Each obligation has a known
shape and is discharged by a determined lemma instance or by comparing normal
forms, not by a general search. This lists where it still searches.

Measured with `INVENTORY=1` (`slc/kernel/src/ext/inventory.rs`). The recorder
reports every outermost simp / arith / tautology call with the extension
frames that made it. Functions measured: a_ctz_32, is_bouncing, step_seq.
Search time in the bridge: 0.6 s, 2.4 s and 5.5 s; that is nearly all of each
function's bridge time. Normalization (`sp.prop`, the `Words` forms) is
rewriting, not search, and is not counted.

| | obligation | where | time | calls (ok) | of it in failed calls |
|---|---|---|---|---|---|
| A | machine branch decisions | symex.rs:443, via `symex_decide` | 1.94 s | 210 (7) | 0.08 s |
| B | D's implications resolved, as context for C | symex.rs:749, via `symex_decide` | 0.27 s | 162 (6) | 0.27 s |
| C | access premises (`can_access`) | symex.rs:719/797/800/802 | 2.89 s | 145 (30) | 2.56 s |
| D | return matching (matches_at's conjuncts) | bridge.rs:514/530/535 | 0.87 s | 32 (25) | 0.50 s |
| E | hypotheses of applied lemmas (agree_st1b) | bridge.rs:871, `bridge_apply` | 1.64 s | 8 (6) | 1.55 s |
| F | prologue: scratch view, world match | bridge.rs:196 | 0.15 s | 15 (15) | 0 |
| G | arguments: arity, reg = arg, S' = S | bridge.rs:662-690 | 0.20 s | 18 (8) | 0.13 s |
| H | coverage, the view in univ(1) | bridge.rs:554/571 | 0.06 s | 6 (6) | 0 |
| I | loop: coupling, exits, returns | bridge_loop.rs:246/361/364/446 | 0.28 s | 43 (41) | 0.04 s |
| J | dead machine path | symex.rs:384 | 0.00 s | 1 (1) | 0 |
| K | spec side: spec_run's branch decisions, invariant step | spec.rs (several) | 0.20 s | 5084 (230) | 0.16 s |

The common cause: an obligation compares a machine-side term (address,
condition, value) with a spec-side one. The two are equal only after
normalization. Where the normal forms are applied as a *retry* after a failed
search, or don't coincide, the bridge searches. 2.56 s of C and 1.55 s of E
are attempts that fail before the word-form retry succeeds.

## Per category: what it proves, the direct way

**A. Machine branch decisions.** A `jcc`'s condition on the flags, after a
`cmp`/`test`. Example: `bits_add(8, bytes[4228240], 1) != 0`. It is decided by
tautology and arith over the path's facts. It succeeds because the spec's
branch condition (`seq != 255`) is among them. Direct: the machine's
condition, in normal form, *is* the spec's branch condition or its negation.
Each segment's GIMPLE branch fixes which one. So the decision is a lookup:
normal form equal to the condition, or to its negation. Anything else is an
error naming both conditions.

**B. Implications resolved.** Context building for C's simp fallback: D's
implications whose antecedents the path decides. This disappears with C.

**C. Access premises.** For each instruction's memory access,
`all x0 < n. can_access(vm, addr + x0, k)`. Today the chain is
`shows_access`, then tautology/arith, then focused simp, then full simp,
then all of it again in word form. The address has one of a few shapes, and
each has its lemma:
- a frame slot `rsp0 + c` (c a negative literal): `abi.slot_at`;
- the return address `rsp0 + 0..8`: `abi.ret_at`;
- an address the spec accesses at the same point, through GIMPLE `usable`
  (a static such as `4228240`, a table entry `4219040 + i`, `4228176 + i`):
  `g.read_off` / `g.write_off`, with the `usable` fact taken from the branch's
  conditions;
- the machine state at a loop head (`?M`): the same, through the coupling's
  `pages` equation (`symex.rs:687`).

The direct way is to classify the address's normal form and apply that one
lemma instance (as `shows_access` does now for the last two). Most of the time
goes where the address's normal form doesn't match the spec's. Example:
`bits_sext(32, 64, le(bytes, rsp-4, 4)) + 4228240` against
`int_add(4228176, i)` with `i` in its home slot. The comparison needs the
homes' values substituted first.

**D. Return matching.** The conjuncts of `abi.matches_at`'s return case:
- `!df`: an entry fact carried through the run; direct by the fact;
- `world_matches`: by the agreement layers (E) and `abi.agree_wm2`, then
  fields equal;
- the final state's fields and register typing: equalities of normal forms;
- values equal (rax against the spec's result): normal forms.

Today it's a lean simp, then a full simp, then a word-form retry.

**E. Lemma hypotheses.** `bridge_apply` already applies the right lemma
(`agree_st1b`, `agree_slot`) at a determined instance. But it shows the
hypotheses by simp. The costly one is the stored values' equality
(`bits_add(8, bytes_at(vm, 4228240, 1), 1)` against the machine's
`bits_add(8, bits_add(32, le(bytes, 4228240, 1), 1), 0)`): 1.47 s failed,
then the word form. Direct: compare the normal forms. The remaining hypotheses
(page, alignment, bounds) are entry facts or literal arithmetic.

**F. Prologue / view.** `scratch_view` and `world_matches` at the
prologue's stores: instances of `abi.sv_base`, `abi.slot_sv`, `abi.wm_base`
and `abi.slot_wm`, by the store chain's shape (as the agreement layers do).

**G. Arguments.** The arity guard: a literal fact of the spec's branch, or
its absence. `reg = arg`: an instance of `abi.arg_passed`. `S' = S`: the
equalities just shown. All direct.

**H. Coverage.** The spec's branches cover D. That is the disjunction of
spec_run's own branch conditions, a propositional fact about how spec_run
built them. It could be stated by spec_run, not searched.

**I. Loop checks.** The coupling at the head, field by field (facts or
normal-form equalities), and matching the exits (as D). Mostly cheap already;
direct in the same way as D–F.

**J. Dead paths.** A machine path the spec's branch rules out. With A
decided by lookup, a dead path is one whose condition is the negation of the
branch's. No search.

**K. Spec side.** spec_run deciding GIMPLE branch conditions and checking the
loop invariant's step. This is GIMPLE-level reasoning, not the bridge's
comparison. Cheap (0.2 s for 5084 calls).

## The order

C, A and E are 6.5 s of the 8.5 s, and they share a need: one canonical
normal form for machine and spec terms. That includes homes substituted,
words as integers, and byte reads as `bytes_at`. With that, C becomes
classify-and-apply, A a lookup, E a comparison. D, F, G and I follow with the
same comparison. B and J disappear. Each step is measured before and after
with `INVENTORY=1`.
