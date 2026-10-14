# The languages

Two languages are used together:

- **SL** (`*.sl`) writes models, layers and specs. `slc` elaborates it into
  definitions of the core logic.
- **Core files** (`*.core`) hold the logic's declarations and theorems. A
  proof is written in the proof language and checked by `slc
  kernel-check`.

Part I is SL; Part II is core files and proofs.

# Part I: SL

## 1. Principles

1. **Reads like the Intel manual and like C.** An instruction body is a
   few lines of imperative code.
2. **Every construct has a fixed translation** into the second-order
   background logic. The translation is the semantics; the elaborator is
   not trusted, because the kernel re-reads its output.
3. **Nondeterminism and undefined behaviour are explicit**: `any`,
   `either`, `havoc`, `undefined`. Whatever a spec does not cover is
   `undefined`, which keeps a model an over-approximation of the machine.
4. **Mathematics and programs are separate.**
   - `fn` and `pred` are pure and may use binders.
   - `proc` is stateful. A `fn` never calls a `proc`.
   - A `proc` binds variables only in constructs with a fixed evaluation
     order (`let`, `for`, `while`).
5. **Low noise.** Braces, newline-terminated statements, no header files,
   no proofs in SL files.

## 2. Declarations

| declaration | meaning |
|---|---|
| `type T = ...` | alias, refinement `{x: T \| P}`, or sum type `a(..) \| b(..)` |
| `enum E : bits[k] { a, b = 5, ... }` | finite enumeration with an encoding |
| `record R { f: T, ... }` | product type with named fields |
| `const c: T = e` | named constant |
| `fn f(x: T) -> U { ... }` / `fn f(x: T) -> U = e` | total function; a block body is a term (`let`, `var`, assignments, `if`, `match`, `return`) |
| `pred p(x: T) = e` | `fn p(x: T) -> bool` |
| `state S { f: T, ... }` | the mutable state; fields are lvalues |
| `state S extends T { ghost f: U }` | a state with extra (ghost) fields |
| `exception e(x: T)` | a way to end abnormally |
| `view v(x: T) : U { get ...; set(v) {...} }` | a named getter/setter pair (an lvalue) |
| `proc p(x: T) -> U { ... }`, `proc[S] p(..)` | nondeterministic stateful program, over the module's state or `S` |
| `decoder`, `table`, `notations` | binary decoding (section 8) |
| `spec M uses ...` / `layer M uses ...` | file header: trusted model or defined abstraction (section 9) |
| `param`, `law`, `instance` | hypotheses of a layer and their discharge |
| `theorem name(x): P` | a claim, proven in core files |

Generic parameters are written in brackets and inferred at call sites:
`proc set_flags[w: Width](r: bits[w])`.

## 3. Types

- `bool`, `nat`, `int`: mathematical, never overflowing.
- `bits[n]`: an n-bit word, `n` any `nat` expression (`bits[w]`,
  `bits[8*n]`).
- Compound types:
  - `A -> B` (total maps), tuples `(A, B)`;
  - `List[T]`, `Set[T]`, `Option[T]` (`none` / `some(x)`);
  - records, enums, sum types.
- `Seq[T]` is a finite or infinite sequence with `len : natinf`. `a <= b`
  is the prefix order, and every increasing chain has a limit.
- Refinements `{w: nat | w in {8, 16, 32, 64}}`: membership is a proof
  obligation.
- `proc[S](A) -> R` is the type of procs. Procs are values.

In the logic:
- `bits[n]` is the set of integers `0 .. 2^n - 1`;
- records are functions from field names;
- sums are tagged pairs.

## 4. Integers

The type decides the arithmetic; nothing converts implicitly.

- `+ - *` wrap on `bits[n]` and are exact on `int` / `nat`. `nat`
  subtraction needs a non-negative result; otherwise use `int`.
- Both operands have the same type. Shifts take `k: nat`, and so does the
  bit test `x[i]`.
- Literals take the type from context. Negative literals in `bits[n]` are
  two's complement.
- Signedness belongs to the operation:
  - `<` `<=` `/` `%` `>>` are unsigned;
  - `<s` `<=s` `>>s` are signed (signed division: on `sint` values, as
    spec/x86_64's `idiv` does).
- Conversions are explicit:
  - `uint(x)`, `sint(x)`;
  - `bits[n](e)` (wraps; the width is always written);
  - `zext[n](x)`, `sext[n](x)`;
  - slices `x[hi:lo]`, the bit `x[i]`.

Example: the carry of an addition is `uint(a) + uint(b) >= 2^w`.

## 5. Programs

A `proc` denotes a relation between an input state and an **outcome**:

```
ok(S, V)            normal return
exc(S, Exception)   raise; the state at the raise is kept
diverge(Trace[S])   infinite run, with the limit of its trace fields
```

**Traces.**
- A field `trace f: Seq[E]` only grows: `emit f e` appends, and `havoc`
  chooses an extension.
- A diverging run has no final state, but its traces converge.
  - A program printing forever diverges with an infinite trace.
  - A silent loop keeps the finite trace it had.

| statement | meaning |
|---|---|
| `let x = e`, `let (a, b) = e` | immutable local |
| `var x = e`, `x := e` | mutable local, assignment |
| `lv := e` | state update: a field path, map entry `gpr[r]`, slice `x[15:8]`, or view `reg(r, 32)` |
| `if c { } else { }`, `match e { p => ... }` | also expressions |
| `while c { }`, `for i in a..b { }`, `loop { ... break ... }` | loops |
| `return e`, `raise e(...)` | leave normally / abnormally |
| `try { } catch e(x) { }` | handle an exception |
| `let x = any T where P(x)` | nondeterministic choice; **undefined if no x exists** |
| `let x = any T where P(x) else { S }` | `S` runs if no x exists |
| `let x = any? T where P(x) else { S }` | `S` may run anyway (an operation that may always fail) |
| `either { } or { }` | choice between blocks |
| `havoc lv`, `havoc lv where P else { S }`, `havoc?` | arbitrary value (with a condition, as for `any`) |
| `emit f e` | append to a trace |
| `require P` | `undefined` unless `P` |
| `undefined` | every outcome possible |

**Expressions.**
- Inside a `proc`, expressions may call procs and views (innermost first,
  left to right).
- Binders:
  - `all`, `ex`, `{x: T | P}`, `min S`, `max S`, `sum i in a..b. e`;
  - lambdas `(x: T) => e`, comprehensions `[e for i in a..b]`.
- Sugar:
  - list slices `l[a..b]`, concatenation `++`;
  - record update `r with { f: e }`;
  - `o.value` for an `Option` known to be `some`.

**Views** give getters and setters to derived locations (`eax`, `rflags`,
"a register or memory"). Their accessors are procedures, so they may
fault.

**Contracts.** A function spec is a contract:

```
require pre
either { overflow() } or { vm := post(vm); return r }
```

## 6. Meaning

Each `proc` becomes a program `mkprog(s o. R(s, o))`: the set of pairs of
a state and a possible outcome.

- Sequencing passes non-`ok` outcomes through; `bind_rel` composes.
- `let x = any T where P; K` means `(ex x. P && K) || !(ex x. P)`.
  - With `else S`, the second disjunct is `!(ex x. P) && S`.
  - `any?` adds `|| S`.

  There is deliberately no construct with no outcome.
- `undefined` is `true`. `require P` is `!P || ...`.
- Loops: `ok` and `exc` outcomes are the least fixpoint, and `diverge(t)`
  is the greatest (coinductive big-step semantics). The trace of an
  infinite run is the limit along it.
- `fn`s become definitions, and a block body becomes a term (`letin`,
  `ite`). No recursion yet.

Encodings:
- numbers are integers with total arithmetic (`int_add`, ...);
- word operations are integer operations mod 2^n
  (`bits_add(n, a, b) = int_mod(a + b, 2^n)`);
- types are sets;
- a `param` becomes an extra argument of the definitions that use it;
- a `law` becomes a definition;
- a `theorem` becomes a `claim`.

## 7. Lexical conventions and grammar

**Tokens.**
- Names are `[A-Za-z_][A-Za-z0-9_]*`.
- Numbers: `123`, `0x1F`, `0b101`, with `_` separators.
- Strings `"..."`, comments `//`.
- In table rows, hex bytes are written `0x83`.
- All operators are ASCII.

**Newlines.** A newline ends a statement when two things hold:
- the innermost open bracket is `{` (or there is none);
- the line's last token can end a statement: a name, a literal, `)`, `]`
  or `}`.

`else`, `or` and `catch` may start the next line.

**Dots.** A field access `x.f` has no space after the dot; a binder's dot
does (`ex q: nat. q.f = 0`).

**Signed operators** (`<s`, `/s`, ...) are single tokens when the `s` is
not followed by a name character.

**Precedence**, lowest first:
1. binders (extend to the right);
2. `<->`;
3. `->` (right);
4. `||`;
5. `&&`;
6. comparisons `= != < <= > >= <s <=s >s >=s in notin is refines`;
7. `..`;
8. `|`;
9. `xor`;
10. `&`;
11. `<< >> >>s`;
12. `+ - ++`;
13. `* / %`;
14. unary `! - ~`;
15. `^` (right);
16. postfix: calls, indexing, slices, fields, `x.{f, g}`, `with`.

**Braces.**
- In expression position `{` starts a set.
- `Name { f: e }` is a record literal, except in the condition of `if`,
  `while`, `match` and `for`.
- Blocks are values only in these places:
  - `if` / `match` arms;
  - lambda bodies;
  - `do[S] { ... }` (a program as a value);
  - `with view(args) { ... }`.

**Keywords:** `let var if else match while for in loop break return raise
try catch either havoc where require guard undefined emit ghost fn pred
proc view type enum record state const exception decoder notations table
using with param law theorem uses extends all ex sum any true false self
is notin refines do`.

**Contextual keywords:** `spec layer or xor trace get set context before
after`.

```
file     := ('spec' | 'layer') NAME ('uses' NAME (',' NAME)*)? decl*
decl     := 'type' NAME generics? '=' (type | variant ('|' variant)*)
          | 'enum' NAME (':' type)? '{' (NAME ('=' expr)?),* '}'
          | 'record' NAME fields | 'state' NAME ('extends' type)? fields
          | 'const' NAME (':' type)? '=' expr | 'exception' NAME params?
          | ('fn' | 'pred' | 'decoder') NAME generics? params ('->' type)? body
          | 'decoder' 'context' type
          | 'proc' ('[' type ']')? NAME generics? params ('->' type)? body
          | 'view' ('[' type ']')? NAME params? ':' type '{' get set '}'
          | 'notations' NAME '{' (pattern '~>' tokens)* '}'
          | 'table' NAME ('using' NAME,*)? '{' entry* '}'
          | 'param' 'pred' NAME params | 'param' 'fn' NAME params '->' type
          | 'law' NAME params? ':' expr | 'theorem' NAME generics? params? ':' expr
fields   := '{' (('ghost' | 'trace')? NAME,+ ':' type),* '}'
generics := '[' (NAME (':' type)?),+ ']'
body     := '=' expr | block
type     := NAME ('[' (type | expr),+ ']')? | type '->' type | '(' type,* ')'
          | '{' NAME ':' type '|' expr '}' | 'proc' ('[' type ']')? '(' type,* ')' ('->' type)?
          | type '&' type
stmt     := 'let' pat (':' type)? '=' expr | 'var' NAME (':' type)? '=' expr
          | 'ghost'? expr ':=' expr | 'emit' expr expr
          | 'if' expr block ('else' (block | if))? | 'match' expr '{' arm* '}'
          | 'while' expr block | 'for' NAME 'in' expr block | 'loop' block | 'break'
          | 'return' expr? | 'raise' expr | 'try' block ('catch' pat block)+
          | 'either' block ('or' block)+
          | 'havoc' '?'? expr,+ ('where' expr ('else' block)?)?
          | 'require' expr | 'guard' expr | 'undefined' | expr | block
arm      := pat,+ '=>' (block | stmt)
pat      := '_' | NUM | 'true' | 'false' | NAME | NAME '(' pat,* ')' | '(' pat,* ')'
```

## 8. Decoders, tables and notations

These are generic features for binary formats. All x86 specifics are
defined with them in `spec/x86_64/encoding.sl`.

**Decoders** run over a byte stream and a mutable context `ctx`, and
cannot touch the machine state:

```
decoder context Ctx
decoder imm(n: nat) -> bits[8*n] {
  var v: bits[8*n] = 0
  for i in 0..n { v[8*i+7 : 8*i] := next() }
  return v
}
```

- `next()` consumes a byte; `peek()` reads one without consuming it.
- `guard c`: the decoder does not match unless `c` (not `undefined`).
- `ctx.f := e` updates the context.

A decoder denotes `d(x, bytes, pos, ctx) -> Option[(T, pos', ctx')]`.

**Tables:**

```
table x86 using intel {
  context START
  before  prefixes()
  after   finish()
  0x83 /op:AluOp ib  => alu(op, rm, sext[w](ib))
  with w = opsize() { rows }
  for op in AluOp except cmp { rows }
}
```

A row's items:
- a byte (`0x83`, `{expr}`);
- a decoder call, optionally bound: `x = d(args)`;
- a guard `if expr`;
- a notation.

The table elaborates to three things:
- a sum type with one constructor per row;
- `decode(b) -> Set[(nat, Insn)]`, all matching rows;
- `execute(i)`.

Overlapping rows are nondeterministic. The x86 `step` makes a
non-matching instruction `undefined`.

**Notations** are textual shorthand for items, deliberately unhygienic
(their bound names become visible in the row):

```
notations intel {
  ib                     ~> ib = imm(1)
  /r                     ~> (r, rm, rm8, reg8) = modrm_r()
  /(d: nat)              ~> (rm, rm8) = modrm_ext(d)
  (b: byte)+r            ~> r = plus_reg(b)
}
```

Hole categories are `nat`, `byte`, `ident`, `type` and `expr`. The
longest match wins, and a literal token beats a hole.

## 9. Modules and layers

- **`spec`** modules form the trusted model (`spec/`), assumed to describe
  the real machine.
- **`layer`** modules (`layers/`) hold only definitions, parameters with
  laws, and theorems. A wrong layer is useless, never unsound.

| feature | meaning |
|---|---|
| `S & G`, `state H extends S { ghost f: T }` | a state with ghost fields; a proc over `S` runs on `S & G` leaving `G` alone; ghosts change only by `ghost` statements |
| `self` | the whole current state |
| `with v(args) { body }` | run `body` through the view `v` (read by `get`, written back by `set`, also on exceptions) |
| `outcome(s, p(args), o)` | `p(args)` from `s` may produce `o` (allowed in `pred`) |
| `low refines high` | every outcome of `low` is one of `high` (with ghosts: for each initial ghost, some final ghost) |
| `param pred p(x)`, `param fn f(x) -> T` | an unknown of the layer |
| `law name(x): P` | an assumption on the params, discharged by an `instance` |

**Specs with ghost state.** A spec may run on the C world extended by
ghost fields (`state MallocAbs extends Heap { ghost A: Abs }`,
layers/mallocng_purpose.sl): it reads the memory where that is its purpose, the
ghosts where that is, and updates the ghosts by `ghost f := e`. The code
has no ghosts, so nothing is erased: the refinement says that for every
initial ghost some final one matches (`refines_ghost(code, spec, abi.World,
G)`, after any ghost-free refinements: `g.refines_then_ghost`), and the
machine code then implements the spec, `abi.implements2_at(G, ..)`, from
its C1 by `tr.implements_abi_g` (proofs/abi_ghost.core; for every G whose
fields are none of the machine's or the world's, `abi.ghost_ok`).

In such a refinement the ghost part rides along without bookkeeping:
`simp` reads a field of `union2(s, h)` in the part that has it and pushes
an update into it (a part lacks a field by its construction or by a known
`dom(h) = D`), and computes `with_ghost(ok(s, v), h) = ok(union2(s, h), v)`
(likewise `exc`; a divergence is itself). Binding commutes with a ghost
extension (`g.bind_ghost`), so a C function value's wrapper refines when
its procedure does (`g.fun_res_ghost`, as `g.fun_res`), and a contract's
runs are introduced by its two cases (`ct.contract_ovf`,
`ct.contract_ret`; proofs/gimple_ghost.core). The user's proof is then the
spec's idea: get_slot_index's (proofs/mallocng_purpose.core) is that the
byte it reads is the slot's header, the allocator's, its low bits the
slot's index (`mp.slot_hdr`, from the invariant).

## 10. Static semantics

- **Names.** A module sees its own declarations and those of the modules
  it uses, transitively; its own shadow the used ones. A bare name inside
  a procedure resolves in this order:
  1. a local;
  2. a value generic;
  3. a field of the current state;
  4. a global.

  Shared constructor names are resolved by the expected type.
- **State.** A `proc` / `view` has the state type `proc[S]`, or the
  module's first `state`. States are open records. Calling a procedure
  over another base state needs `with`.
- **Effects.** In `fn` / `pred`, a procedure call denotes the program and
  never runs it. `any`, `havoc` and `next()` occur only in procedures and
  decoders.
- **Types.**
  - `nat` and `int` mix; `bits` goes only with `bits` and enums.
  - Widths are compared in a linear normal form. Different literal widths
    are an error; widths that cannot be shown equal are a warning.
  - Generic parameters are inferred, also `n` in `bits[8*n]`.
- **No recursion** yet.

# Part II: core files and proofs

## 11. Core files

```
const c                        (prelude only)
axiom name(params): φ          (prelude only)
def f(params) := t             conservative definition
abbrev f(params) := t          read as its expansion
claim name: φ                  a closed statement to prove
lemma name(params): φ          an open lemma: theorems using it are conditional
theorem name(params): φ proof ... qed
theorem name proof ... qed     proves an earlier claim or lemma
irreducible name               implicit unfolding keeps `name` folded
simp name                      registers an equation for rsimp
mem_view name                  registers a memory view (below, "Memory")
mem_frame name                 registers a memory frame
mem_closure name               registers a memory closure
bit_rule name                  registers a bit rule (below, "Bits")
```

Terms:
- the operators are fixed: `-> <-> || && ! = != in`;
- binders are `all x. P`, `ex x. P`, and `x y. t` as an argument of a
  binder constant (`set_select(s, x. p)`).

A labelled conjunct `name: φ` is term metadata: no rule reads it, but
labels survive instantiation and unfolding. SL predicates may label
their conjuncts the same way.

## 12. Running the checker

```
slc kernel-check [--no-cache] core/prelude.core FILE.core ...
```

Files load in order, each seeing the ones before; only the first may have
axioms. The result lists the claims and the open lemmas that conditional
theorems rest on.

**Cache.** `build/kernel-cache` keeps each checked file's statements,
with its proofs replaced by `cached`. An entry is used when all of these
hold:
- the file is not newer than the entry;
- the statements before it are the same (a hash chain, so editing only a
  proof keeps later entries);
- it was written by the same checker, at the same position.

`--no-cache` neither reads nor writes the cache; the tests use it.

## 13. Proofs

A proof is a sequence of steps, one per line. A line continues while
brackets are open; a line starting with `by` or `:=` continues the step
before.

```
assume h: φ               hypothesis (discharged at the end)
assume h1 h2              the goal's next premises, named
fix x y                   the goal's next `all`s (generalized at the end)
have h: φ := P            a fact from a proof expression (φ checked if given)
have h: φ by R(args)      a fact by a goal rule (below)
have a b c := P           P's conjuncts, named (`_` skips one, `..` ignores the rest, `r..` names it;
                          as many names as the leaves of its tree of `&&`s: every leaf)
have {sM, x = mM} := P    the conjuncts labelled sM, mM
obtain x y, h1 h2 from P  witnesses of `ex x y. ...`, the body's conjuncts named (as `have`: `ex k: nat.
                          P && Q`'s body `k in omega && (P && Q)` takes 2 or 3 names)
step x.., h.. from P with f.. [using u..]   a run of readable GIMPLE inverted step by step (below)
show P / show φ by R(..)  the result (else the last `have`); the block's last step
show [φ] proof ... qed    a sub-proof with its own scope (also `have h: φ proof ... qed`)
have c: case k of P proof ... qed   a sub-proof of P's k-th disjunct (as written) -> the goal
let N := t / let N(a) := t   an abbreviation to the end of the block (`:= loop_body(h)`: h's loop's body)
unfold [D..] [in h]       unfold definitions in the goal (or fact h)
zeta x [, {k}..] [in h]   the let x's variable its value (all or the k-th occurrences)
fold_let x [, {t}] [, {k}..] [in h]   the let x's value back to x, or a new let x of t
flip [in h]               turn the equation / disequation around
rsimp e1, .. [in h]       simplify the goal (or h) with rsimp
print P                   show what P proves, then (on their own lines) its hypotheses and the goal
```

`assume` and `fix` take formulas from the goal, so write a formula only
where it says something new. They see through a defined goal's head.

**Conjuncts** are counted as written: `a && b && c` has three. `h.k` is
the k-th (from 1) and `h.label` the labelled one. Both are projections,
not search.

**Proof expressions:**
- a fact: `h`, a theorem, an axiom;
- an instantiation `name[x := t, p := y. φ]`: its parameters, or its
  leading `all`s by binder name;
- a rule `name(args)`;
- an inline goal rule `(φ by R(args))`.

Arguments are proof expressions, terms `{t}`, occurrence selections
`{1, 3}` (numbered from 1, outer before inner, left to right), or symbols.

**Lets.** `letin(a, x. f)` keeps the name written at its binder (term
metadata, like labels): messages print it, and `zeta` / `fold_let` /
`simp(.., lets(..))` select a let by it. A let without a written name is
selected by the name it is printed with (`x3`); the first let so named
counts (outer before inner, left to right). A new let made by `fold_let`
goes around the whole statement, so its value must be closed. A fact proves a goal
that is the same up to lets: the two are compared node by node, a let
reduced only where they differ (`Seq::conv_lets`; a long chain of lets
is never unfolded as a whole). This holds wherever a fact meets its goal:
`show`, a premise of `mp` / `apply`, the steps above.

**step** (C2 proofs; needs proofs/gimple_inv.core). From P -- a run
`runs(prog, s, o)`, or a fact on a program's outcome, first simplified by
step's own rules (`fst(pair(s, ..))` to s: a loop body at a state) -- it
goes, in order:
- through the program's definition and relation (`g.runs_elim`) and
  `letin`s (`g.letin_e`);
- through `bind_rel(p, s, ..)` by a `with` fact `g.det(p, s, ok(s1,
  v1))`, an operation's one outcome (`g.bind_inv`). The `with` item may
  instead be a lemma `all xs. H1 -> .. -> g.det(P, S, O)`: its variables
  come from matching P and S with the operation and the state, and its
  premises are discharged from the `using` facts (see "Memory"). A call of
  a defined procedure no `with` fact covers (an accessor such as
  `meta_mem_(g)`, `ld64(g, 16)`) is stepped through: its body with the
  same facts, to its one outcome (`g.det`, derived on the spot). Then the
  value read is resolved, if it resolves -- to a value written, or to the
  same read before the writes (`mnext(wr64(V0, ..), m)` to `mnext(V0, m)`)
  --, and the state's record fields are simplified;
- through a local's choice of a word (`any_rel`), and an `if`'s outcome
  (`ex x. ((c && T) || (!c && E)) && K(x)`), each named by the next name;
- into the `if`'s branch that is decided: by a `with` fact implying c or
  its negation propositionally (c as written, simplified by step's own
  rules: `snd(pair(a, b))` to b .., or both with the memory views unfolded:
  `mnext(vm, m)` as `rd64(vm, m + 8)`), else by arith from a `with` fact and
  the `using` facts, else from the `using` facts alone; through the
  branch's `letin`s and binds; a branch ending in `x = V` is substituted
  into K, and K's dispatch on V (an `ok`: on with the rest; a return: the
  outcome) simplified; a branch with more steps (a nested `if`, a choice)
  is stepped on, K waiting for its outcome;
- into L of `L && R` (while there are names or `with` items left), R
  waiting for L's outcome `x = V`; an L that is already `x = V` (an `if`
  step's rules decided) substituted into R;
- and it stops at anything else -- a call, a loop, a bind or branch with
  no `with` fact for it, a choice with no name -- naming the fact there
  `h` (or its conjuncts `h..`). Unused names or `with` facts are an error
  (for an operation's lemma that matched but did not apply, why).
  `using` facts that are conjunctions are split.

The `with` facts are used wherever they fit, in any order; an operation's
lemma applies to every operation it matches (`g.padd_det` once for all
the pointer additions). Give an instance instead to keep `step` from
going on past a point.

**Loops.** `step` stops at a loop, `while_rel(l0, l. true, l o. B(l, o),
.., r) && K(r)`. `let B(l, o) := loop_body(h)` names its body (from the
fact h, as it is); `g.loop` (proofs/gimple_inv.core) takes an invariant p
with p(l0), a variant m with p(l) -> m(l) in omega, and the step
`all l l2. p(l) -> B(l, ok(l2, empty)) -> p(l2) && m(l2) < m(l)` to the
loop's exit: `ex l. p(l) && B(l, r) && !is_ok(r)` -- a break, a return or
a failure from a state with the invariant (ms.step_seq_c2):

```
let BODY(l, o) := loop_body(wl)
have wv := apply(g.loop[b := l o. BODY(l, o), p := l. P(l), m := l. M(l)], p0, pm, nx, wl)
```

```
step a3 a5 a7 a9 x13, oe from hr with hq     // oe: o = ok(s, bits_of_int(32, Q))
step x17, hx17 hk17 from hk2 with sd, md, ad, rd1, ld1
step c9 from conj(hc3, hrest3) with nn, d2, ms.setnext_det, ms.prev_det, ms.setprev_det, .. using F
```

**Memory.** A procedure of its own, not rewriting search: which write a
read hits is decided by a fixed algorithm.
- Views (`mem_view`): equations giving a spec's or GIMPLE's reads and
  writes in two canonical forms -- a write `fn_update(M, "bytes",
  store_le(app(M, "bytes"), a, n, v))`, a read `gimple.bytes_at(M, b, m)`
  (`ms.v_wr64`, `ms.v_rd64`, `ms.v_mnext` in proofs/mallocng_mem.core).
- A read through writes: the kernel's `mem_read` walks the writes from the
  outermost in -- also a chain of writes on bytes of any form,
  `fn_update(M, "bytes", store_le(store_le(B, ..), ..))`, ending at bytes
  B it does not know (the read is then of `fn_update(M, "bytes", B)`).
  For each it tests, by `arith` on the facts given: apart (past it), the
  same place and size (its value), the read inside it (its digits); else
  it stops, naming the write. A read of a size not a numeral passes apart
  writes only. A word's value is then cleaned back from its digits.
- In a `mem` goal a read that does not resolve (inside a value written,
  or of bytes not known) is left as it is: the goal may not need it (a
  fact about it may), else the failure lists such reads and why.
- Frames (`mem_frame`): predicates the bytes do not matter to,
  `P(fn_update(vm, "bytes", X), ..) = P(vm, ..)` (`word_ok`).
- Closures (`mem_closure`): lemmas `H.. -> C1 && ..`, used backward for a
  premise matching a conjunct (`ms.world_wr`, `ms.sw`: a world written is
  a world).
- A `step` lemma's premise is discharged by a `using` fact, its record
  fields simplified, a closure, `mem`, or `arith` on the facts.

The facts are what a precondition provides: bounds, alignment (`al8`
expanded to `x % 8 = 0`), disequalities, either-or placements (a slot
before or after a word). Each `arith` check gets the facts mentioning its
terms, and through the equations among them, the facts on their other
sides' terms (an address `e + sval(d)` given as `sval(d) = -r`, then r's
bounds); if that does not do, the facts connected to its terms by any
chain of shared terms (a membership's type not counted), those with cases
(disjunctions, disequalities) only when about its own terms -- so a
bound like `p + n + 4 <= e + w` brings in n's and w's facts.

### Rules without a goal

| rule | result |
|---|---|
| `mp(ab, a1, ..)` | modus ponens; a term `{t}` instantiates the leading `all` |
| `apply(f, a1, ..)` | f instantiated by matching its premises with the proofs, then applied; terms `{t}` fill `all`s in order |
| `all_elim(p, {t}, ..)` | instantiate `all`s |
| `conj(p1, .., pn)` | `p1 && .. && pn` |
| `refl({t})`, `sym(e)`, `trans(e1, e2)` | equality |
| `flip(p)` | `a = b` as `b = a`, `a != b` as `b != a` |
| `subst({x. φ}, e, p)` | substitution |
| `rewrite(e, p [, {k}..])` | rewrite e's left side in p (all occurrences or the selected); e may be `all x.. l = r`, also under binders |
| `expand(p, D.. [, {k}..])` | unfold D in p once |
| `unfold(D)` | D's defining equation |
| `zeta(p, x [, {k}..])` | the let x's variable its value at the k-th occurrences in the let's body (none given: all, the let dropped) |
| `fold_let(p, x [, {k}..])`, `fold_let(p, x, {t} [, {k}..])` | the let x's value back to x (at the k-th occurrences); with no let x, p as `letin(t, x. ..)` of t's (k-th) occurrences |
| `discharge(p, h)`, `gen(p, x)` | `h -> p`; `all x. p` |
| `witness(p)` | the choice witness of `ex x. φ` |
| `part(p, {k})`, `unsel(h)` | a conjunct; `z in S && P(z)` from `z in set_select(S, x. P)` |
| `prop({t})`, `lit({t})` | `t` is a proposition; a literal fact |
| `rec({t}[, h])` | the recursion equations of `nat_rec` |
| `at({L[i]}, p..)` | the element at i of a list expression (or of a defined list constant's) |
| `list_ext(ha, hb, hl, he)` | list extensionality |
| `members({S}, h..)` | the members of S on concrete data |
| `rsimp(h, e.., [only])` | h simplified |
| `mem_read({t}, p..)` | `t = r`: t's reads resolved through their memories' writes (facts p..) |
| `mem_bytes({bytes_at(M, b, m)}, p..)` | the kernel's `mem_read`: one read through M's writes |
| `simp(h, ..)` | h's paths (symbolic execution) |

A higher-order parameter applied to distinct bound variables (`k(s1, v)`)
matches any term over them. Other parameters are given explicitly.

### Goal rules

These prove the current goal. Write them as `show by R(..)`, `have h: φ by
R(..)`, or inline as `(φ by R(..))`. In `mp` / `apply` they prove the
premise they stand for.

| rule | proves the goal by |
|---|---|
| `taut(p..)` | a propositional tautology from the premises; `a = b` is also `b = a`, and `a != b` is `!(a = b)` |
| `arith(p..)` | propositional logic plus linear arithmetic over integers: words mod 2^n with symbolic widths, `*`, `/`, `%` by constants (numerals, or powers of numerals: `pow2(64)`, `int_pow(2, 32)`); products of non-constants as monomials (`a * (b + c)` is `a b + a c`), a product of nonnegatives nonnegative, `x = m q + r` for `/`, `%` by a symbolic m > 0, `pow2(k + 1)` as `2 pow2(k)` |
| `rsimp(e.., D.., [only])` | left-to-right rewriting to `true` with the facts, definitions and registered `simp` rules |
| `simp(p.., keep(P..), {l0 l. I}, {l. m})` | the path simplifier, below |
| `defs(p, D..)` | p proves the goal with D unfolded |
| `ex_intro({w}.., p)` | witnesses for `ex` |
| `sel(p)` | `z in set_select(S, x. P)` from `z in S && P(z)` |
| `lists(p..)` | equal list expressions (same pieces) |
| `induct(base, step)` | `all n. n in omega -> P(n)` |
| `eval(p..)` | evaluation on concrete data |
| `bitwise([{n},] p..)` | bits: a word equation of n-bit words bit by bit (extensionality), or a proposition about bits; see "Bits" |
| `cases({k}, {a}, {b}, R, p..)` | the goal for each value c of the variable k, a <= k < b (numerals; the bounds from p.. by arith), each by R with k read as c in R's terms |
| `mem(p..)` | memory: an equation of reads (both sides resolved, then equal or by arith), or a predicate of a written memory (views and frames, then a fact) |

In `arith`, the facts' equations substitute equals for equals: each term
is read with its subterms replaced by their class's representative (the
smallest; from `q = Q`, `m q = m Q`), and the equations count as given
too. An equation assumed in one case of the search (not a fact) is used
arithmetically only. The cases are split on the atoms the goal still
depends on, with unit propagation; there is no limit on the atoms. A
sign fact comes with each product in the facts or the goal, so a product
term given as a hint (`refl({int_mul(m, int_sub(q, 1))})`) brings `m >= 0
&& q - 1 >= 0 -> m (q - 1) >= 0` in (core/bits.core's `div_unique`).

**Bits** (core/bits.core). `bitwise` reduces a word equation `L = R` to
`bit(L, i) <-> bit(R, i)` at a fresh i < n (`bits_ext`), the width n from
the words' operations or given. Each `bit(W, I)` met is explained by the
first registered rule (`bit_rule NAME`: `H.. -> (bit(P, j) <-> φ)`) whose P
matches W -- a numeral read as `pow2(k)` or `pow2(k) - 1`, a product
either way round --, its premises shown from the facts (a fact, arith),
else kept as hypotheses for the case they hold in; the bits of φ in turn.
One `arith` call then decides the goal from the facts, the explanations,
the facts' `all`s at the indices met, `bit_cong` (equal indices) and
`bit_high` (none at or above a word's width). No rewriting, no search.
The rules: `and` / `or` / `xor` / `not`, shifts, `bits_of_int`, `/`, `mod`,
`*` by 2^k, masks 2^k - 1, 2^k, 1, 0. The idioms: `lowest_bit` (`x & -x`),
`smear_step` / `smear_done` (`x | x >> m`), `shl_two` (`2 << k`).

**Implicit unfolding.** A fact proves a goal that differs from it only by
definitions. The checker unfolds at the mismatches, newer definitions
first. This applies to:
- a step against its goal;
- the premises of `mp` / `apply`;
- a stated `assume`;
- destructuring and `all_elim`.

**rsimp** is Lean-like: it rewrites left to right only, with the given
equations and definitions and the registered `simp` rules (`only`
excludes the registered ones).
- A conditional rule's premises are discharged by:
  1. known facts;
  2. nested rsimp;
  3. arith on the relevant facts.
- Ground arithmetic and literal (in)equalities are evaluated.
- A program outcome's parts are registered rules (`out_state` / `out_value`
  of `ok` and `exc`, `fst` of `ok` / `exc` / `diverge`; core/records.core).
- `RSIMP_TRACE=1` prints every rewrite.

**simp** is the path simplifier, used for symbolic execution of programs.
- It turns `runs(P, s, o)` into P's paths, with the existentials pulled
  out and equations solved.
- It closes each path by taut / arith. It finds witnesses for the goal's
  existentials by matching.
- `keep(P)` keeps runs of P folded.
- `lets(keep(x, ..), expand(y, ..))` overrides the let strategy below for
  the lets named so: x kept (not substituted, also used once; not looked
  through for a decision), y reduced at once.
- `fn_modify(f, k, y. g(y))` (core/prelude.core: f's value at k changed
  by g of the old one; lemmas in core/records.core) is simplified as
  `fn_update` of f bound by a let, so f is not copied into the new value.
- A `let` is reduced lazily. A small value (32 nodes at most, as a tree)
  goes into the body. Otherwise the body is simplified with the variable
  a local constant bound to the value, looked through only where it
  helps: a node with the constant as an argument (a projection, `app` at
  a key, ..), or an atom mentioning it, is tried with the value there and
  kept so if a rule fires. Then the let stays if the variable is still
  used twice or more (a large value used many times is not copied), is
  substituted if once, dropped if not. An atom with a let kept in it is
  tried once more with its lets reduced, kept so if that decides it (an
  equation between a let-bound world and its substituted form). A goal
  that attempt leaves open is
  tried again with every let reduced (`SIMP_LET_TRACE=1` reports when
  that was needed: once in the whole chain, a let inside an arithmetic
  term that only the closing arithmetic needs).
- Loops take an invariant `{l0 l. I}` and optionally a variant `{l. m}`.
- Leftover paths are reported as facts ready to prove and pass back.

### Messages and diagnostics

A mismatch names the first differing subterm and its path, with the
proof's `let`s folded back:

```
modus ponens: the fact does not match the premise `tr.implements_at(...)`
  first difference at: tr.implements_at, argument 1
    expected: bits_add(64, 4205803, ...)
    given:    4205681
```

A failed `arith` shows a consistent case, one atom per line, as it read
them (equals substituted). An atom it did not read arithmetically -- a
mere proposition to it -- is marked with why:

```
arith: not shown; a consistent case:
  int_le(k, 3) = true
  int_le(3, k) = true
  k = 3 = false    [an equation, not arithmetic: `k` not known to be an integer (give `k in omega` / ...)]
```

| variable | effect |
|---|---|
| `SLC_FULL_ERRORS=1` | terms uncut (default: 400 characters) |
| `SLC_TIMES=1` | each file's check time |
| `STEP_SLOW=secs` | slow proof steps, with lines |
| `SLC_TIDY=1` | `assume`s restating the goal (`scripts/tidy_proofs.py` removes them) |
| `SIMP_SLOW=secs`, `SIMP_TIME=1` | slow `simp` calls; time per phase |
| `RSIMP_TRACE=1` | rsimp's rewrites and premise attempts |

### Conventions

- Bridge proofs (C1 rules) use determined lemmas and normal forms, not
  search.
- Loops are proven with an invariant and a variant at the head, never by
  unrolling.
