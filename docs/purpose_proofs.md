# Proofs of purpose-level specs: an outline (temporary)

The specs: `try_avail_purpose` and `alloc_slot_purpose` at the end of
`layers/mallocng_purpose.sl`. This note is about how their proofs could read, what
the system could do itself, and what the person would write.

## What writing the specs taught

Stating the purpose exposed three things the invariant (`holds`) did not
say, and that the code relies on. They are now in `group_ok` / `rep`:

- **reserved slots.** Between `alloc_slot` and `malloc`'s `enframe` a slot
  is neither free (in a mask) nor a block. `Use` has a fourth case,
  `reserved`; `holds` allows it, `rep` (the invariant between calls)
  excludes it (`no_reserved`).
- **inactive slots are freed.** `alloc_group` puts every slot above the
  active index into the freed mask. Without this, `try_avail`'s growth
  could activate slots and still find none free (its `assert(mask)`).
- **16-byte groups are fully active.** For them the page-crossing loop
  never ends. musl only creates them nested and fully active, so the
  growth branch never meets them; the invariant must say so.

So the purpose-level spec is also how missing invariant facts surface:
each is one line, with a reason.

## Three parts of a proof

**(a) What the code does to memory: computed.** Running the function
symbolically, as `step` already does piece by piece, gives per path:
the conditions taken, the writes (as a chain over the initial memory), the
result, the callees' contracts applied at their calls, and the definedness
of each access as an obligation. This is deterministic: no search, no
person. The one exception is a loop, whose invariant (what holds at its
head) is an idea the person states.

**(b) Memory read as the abstract state: computed.** The invariant's
definitions say where each abstract field lives:
`meta_in_memory(m, g, v)` puts `v.avail` at `g + 24`, `cyclic` puts
`active[sc]`'s links at `+0`/`+8`, `ctx_ok` the list heads in the context.
That gives a table, read off the definitions once: a read at `g + 24` of a
used meta `g` becomes `A.metas[g].avail`. Rewriting the path summaries
with it is again determined -- the only side fact is that `g` is used, which
comes from where `g` came from (`ctx.active[sc]`'s head is used by
`active_ok`). The definedness obligations go the same way: `perms_ok` says
which ranges are readable and writable.

After (a) and (b), each path reads in abstract terms, e.g. try_avail's
first path: "`h = A.active[sc][0]`, `A.metas[h].avail != 0`; writes
`A.metas[h].avail := avail - lowbit(avail)`; returns `lowbit(avail)`."

**(c) Why the step keeps the invariant: the person's part.** The person
names the new abstract state and says why `holds` holds again. Most of
`holds` is not touched by a step: a conjunct whose reads miss the step's
writes is kept. That is the frame argument, and it is mechanical given the
invariant's separation facts (metas are distinct 40-byte cells, the
context is apart from the areas, a group's header is in no slot). Those
facts are lemmas about the invariant, proved once and reused by every
function. What remains are the conjuncts the step really changes, and for
each the reason, usually a small lemma about one data structure, also
proved once:

- a bit moved out of the available mask, its slot reserved: `group_ok`
  kept (the unused-iff-in-a-mask correspondence);
- a cyclic list rotated, or its head removed: `cyclic` kept;
- slots activated: the freed bits now inside the active range (by the
  inactive-slots-freed fact), so `activate_group`'s mask is not 0.

## How try_avail's proof could read

```
proof try_avail_purpose by paths of try_avail, abstract via holds_in(c, A, vm, blocks)
  let h := A.active[sc][0]
  case A.active[sc] = []:                     // returns 0
    A2 := A
  case avail(h) != 0:                         // the head has an available slot
    let i := ctz(avail(h))
    A2 := A with { metas[h].avail: avail(h) - 2^i, slots[h][i]: reserved }
    holds by frame except group_ok(h) by mask_reserve(i)
  case avail(h) = 0, freed(h) = 0:            // the head is full: dequeued
    A2 := A with { active[sc]: tail(A.active[sc]), metas[h].prev: 0, metas[h].next: 0 }
    holds by frame except cyclic(active[sc]) by cyclic_drop_head, group_ok(h) by unlinked
    then as below, from A2's head
  case avail(h) = 0, freed(h) != 0:           // rotated to the next group
    ...
  case grow:                                  // the head alone, no free active slot
    loop invariant: cnt counts slots whose span stays in one page, cnt <= c
    holds by frame except group_ok(h) by activate_more(c)
```

Every line is an idea: which state comes next, and which lemma explains
the one or two conjuncts that change. The paths, their conditions, the
writes, the reads as abstract fields, the frame for the rest of `holds`,
and the callees' contracts are the system's.

## What this needs from the language and the checker

- **`paths of f`**: the function's path summaries (a), named by their
  conditions, so a proof can take them case by case without restating
  them. The C2 machinery has most of this; it now stops at each `if`
  instead of producing the paths.
- **`abstract via P`**: the read table (b) derived from `P`'s definitions,
  applied to the summaries.
- **`A with { metas[h].avail: v, slots[h][i]: u }`**: updates of nested
  fields and of list/function points (SL has `with` for records only).
- **`holds by frame except Q1 by l1, ...`**: the conjuncts of a definition
  (instances of its quantified ones too) checked by frame, the listed ones
  by the given lemmas. This generalizes the memory procedure's
  `mem_frame` from single predicates to a definition's conjuncts, with
  read and write sets computed from the terms -- set disjointness by
  arithmetic, no search.
- **Lemmas per data structure**, stated once: masks and slots, cyclic
  lists, the context. They are the reusable ideas.
- **A loop invariant at the loop** (as now), for the growth loop.

What still needs choices: the new abstract state `A2`. It is mostly read
off the writes (a write at `g + 24` sets `A2.metas[g].avail`), so it could
be proposed automatically too. What remains is the purely abstract change,
like a slot becoming `reserved` or a list losing its head, which the
person states.

## A possible order

1. Separation lemmas for `holds` and the frame check over a definition's
   conjuncts (`holds by frame except ...`).
2. Path summaries from the C2 machinery (`paths of f`) and the read table
   (`abstract via`).
3. try_avail's proof as the pilot; alloc_slot after `alloc_group`'s
   purpose (it calls it, and through it alloc_slot again, nested).
