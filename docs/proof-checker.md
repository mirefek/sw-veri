# The proof checker (`slc kernel-check`)

How core files are checked, what is trusted, and the tools for writing
and speeding up proofs. The proof language itself is documented where it
is implemented: the module doc of slc/proof/src/lib.rs (steps, proof
expressions, rules); the trusted rules in slc/kernel/src/ext/mod.rs and
the files it lists. Ideas not yet done: docs/todo.md.

## 1. Running

```
slc kernel-check [--no-cache] core/prelude.core FILE.core ...
```

Files are loaded in order, each seeing the declarations of the ones
before; only the first may have axioms. Each `theorem NAME(params): φ
proof ... qed` is checked by the proof language (slc/proof), which builds
the theorem through the kernel and its extensions; the kernel checks that
the result is the stated φ. The final status lists the claims and the
open lemmas the conditional theorems rest on.

**File cache.** build/kernel-cache holds, per checked file, its
statements: the file with each `proof ... qed` replaced by `cached`
(`cached rests(a, b)` for a conditional theorem). An entry is used when

- the file is not newer than the entry (the entry is dated as the file
  when it was read, so a change during the check counts as newer),
- the statements of the files before it are the same (a hash chain over
  their statement texts: editing only a proof keeps the later entries;
  changing a statement rechecks everything after it),
- it was written by the same checker (its executable's date), in the same
  position (the first file: axioms allowed).

Otherwise the file is checked and, on success, its entry written. The
cache is trusted (slc/kernel/src/ext/cache.rs: `cached` is accepted only
from an entry, never in a source file); `--no-cache` neither reads nor
writes it, and the tests use it.

## 2. Writing proofs: notes on the language

The reference is the module doc of slc/proof/src/lib.rs; the points
below are the design decisions behind it.

- **Premises and variables from the goal.** `assume h1 h2` and `fix x y`
  take their formulas from the goal; a formula is written only where it
  says something new (`SLC_TIDY=1` reports the assumes that restate the
  goal, scripts/tidy_proofs.py removes them).
- **Conjuncts by position or label, without search.** `h.k`, `h.label`,
  `have {a, x = b} := P`, `obtain v, {a} from P` project by
  `and_left`/`and_right`; `conj(p1, .., pn)` builds by `and_intro`
  (core/logic.core). Projecting with `taut` searched over every atom of a
  large conjunction (~0.5 s each on the 20-conjunct `tr.inv_call`); this
  was most of the checker's time before.
- **Labels are term metadata** (slc/kernel/src/term.rs): equality and
  hashing ignore them and no rule reads them. Rebuilding a node keeps its
  label; where a variable is substituted, the variable's (outer) label
  wins. So a labelled conjunct in a definition or a statement keeps its
  label through instantiation and unfolding. Written `name: φ` as an
  operand of `&&`, in core files and in SL predicates (the elaborator
  attaches the label, e.g. `abi.world_matches`: top limit brk0 brk bytes
  pages). Binder names are metadata too: `l[x := t]` instantiates a
  theorem's leading `all`s by name.
- **Rewriting.** `rewrite(e, h)` / `expand(h, c)` / `defs(R, c)` act on
  every occurrence or the chosen ones (`{k}`: from 1, outer before inner,
  left to right). An equation under `all`s rewrites its instances also
  under binders (the trusted `Seq::rewrite_under`, by extensionality of
  the primitive binders): a pattern variable may take a term with
  variables bound around the instance, never one bound inside the
  matched left side (`all p. (ex x. p) = p` rewrites `all y. ex x. y = 1`,
  not `ex x. x = 1`).
- **Goal rules inline.** A rule that needs its goal (`taut`, `simp`,
  `defs`, `ex_intro`, ..) is a proof expression as `(φ by R(args))`.
- **Bridge proofs without search**: each obligation by a determined
  lemma or normal form, not by `simp` exploring; check time is not traded
  for convenience.

## 3. Error messages

A mismatch (modus ponens, `apply`, `ex_intro`, `trans`, `defs` after
unfolding, a block's or `show`'s goal, a theorem's statement) names the
first differing subterm and its path:

```
modus ponens: the fact does not match the premise `tr.implements_at(bits_add(64, ...), G0, ...)`
  first difference at: tr.implements_at, argument 1
    expected: bits_add(64, 4205803, bits_sext(32, 64, 4294967174))
    given:    4205681
```

The path goes through implications by premise number, conjunctions by
conjunct (however nested), other symbols by argument, noting the other
differing parts on the way. Terms are cut to 400 characters;
`SLC_FULL_ERRORS=1` prints them whole. Lines are exact: the failing
step's line in the file, also inside nested blocks.

## 4. Diagnostics

| variable | effect |
|---|---|
| `SLC_TIMES=1` | each file's check time |
| `STEP_SLOW=secs` | proof steps taking longer (with their lines) |
| `SLC_TIDY=1` | assumes restating the goal's premise (`tidy-file` / `tidy-assume <line>`, read by scripts/tidy_proofs.py) |
| `SLC_FULL_ERRORS=1` | error messages uncut |
| `SIMP_SLOW=secs`, `SIMP_TIME=1` | slow `simp` calls; `simp`'s time per phase |

## 5. Speed (2026-10-08)

The main chain (libraries, x86 model, step theorems, ABI/GIMPLE proofs,
translate*, the a_clz_32 certificate; 25 files):

| | time |
|---|---|
| uncached | 4.6 s (was 36-55 s) |
| all cached | 0.18 s |
| one proof file changed | 0.3 s |

Per file, uncached: generated step theorems 1.4 s (a_ctz/a_clz) and 3.5 s
(build/leaf_steps.core), proofs/x86_insn.core 1.0 s, translate.core
0.67 s, abi_bridge.core 0.5 s, translate_call.core 0.11 s (was 30-45 s),
a generated certificate 0.00-0.15 s. What made the difference: conjunct
projection and construction without `taut`, then the cache.
