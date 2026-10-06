# A specification language for machine code (draft 0)

Working name: **SL** (files `*.sl`). Everything here is a proposal; open
questions are collected at the end.

Example specification written in SL:

* `spec/x86_64/state.sl` – registers, flags, operands, views
* `spec/x86_64/memory.sl` – Linux page mapping, faults, stack growth
* `spec/x86_64/instructions.sl` – instruction semantics
* `spec/x86_64/encoding.sl` – prefixes, REX, ModRM/SIB decoders, Intel notations, the instruction table
* `spec/linux/process.sl` – syscalls, the process run loop
* `spec/linux/exec.sl` – process start: loading a static ELF, the initial stack
* `layers/abi.sl` – calling convention: what a C function is, `implements`
* `layers/malloc.sl` – abstract heap, malloc / free / calloc specifications
* `layers/claim_malloc.sl` – what is claimed about a libc binary's allocator
* `core/prelude.core` – the background logic (axioms and basic definitions)
* `slc/` – the toolchain (kernel, parser, elaborator, interpreter, CLI); section 13

## 1. Principles

1. **Reads like the Intel manual / like C.** An instruction body is a few lines
   of imperative code, not a chain of `funModify(...)`.
2. **Every construct has a fixed translation** into the second-order background
   logic (ji-trust `logic.lg`). The translation is the semantics; the tool
   is an elaborator, the kernel stays small.
3. **Nondeterminism and undefined behavior are explicit** (`any`, `either`,
   `havoc`, `undefined`), never implicit gaps. Anything the spec does not cover
   is `undefined` – this keeps the spec sound (an over‑approximation of the CPU).
4. **Mathematics and programs are separate layers.** `fn`/`pred` are pure and
   may use binders (quantifiers, set-builder); `proc` is stateful. A `fn` can
   never call a `proc`. A `proc` may call `fn`s, and may bind variables only in
   constructs with a fixed evaluation order (`for`, `while`, `let`).
5. **Low noise, easy parsing.** Braces, newline‑terminated statements
   (Go-style semicolon insertion), no header files, no proof terms in the spec.

## 2. Top-level declarations

| declaration | meaning |
|---|---|
| `type T = ...` | type alias, refinement `{x: T \| P}`, or sum type `a(..) \| b(..)` |
| `enum E : bits[k] { a, b = 5, ... }` | finite enumeration with a numeric encoding |
| `record R { f: T, ... }` | product type with named fields |
| `const c: T = e` | named constant |
| `fn f(x: T) -> U { ... }` / `fn f(x: T) -> U = e` | total mathematical function |
| `pred p(x: T) = e` | shorthand for `fn p(x: T) -> bool` |
| `state S { f: T, ... }` | the global (mutable) state; fields are global lvalues |
| `exception e(x: T)` | a way a program can end abnormally |
| `view v(x: T) : U { get ...; set(v) {...} }` | a named getter/setter pair (an lvalue) |
| `proc p(x: T) -> U { ... }` | nondeterministic stateful program |
| `decoder`, `table`, `notations` | binary decoding, pattern tables, user notations (section 8) |
| `spec M uses ...` / `layer M uses ...` | file header: trusted model vs. defined abstraction (section 9). A module sees its own declarations and those of the modules it uses; its own shadow the used ones. |
| `state S extends T { ghost f: U }` | a state with extra (ghost) fields |
| `param`, `law`, `instance` | hypotheses of a layer, and their discharge (section 9) |
| `theorem name(x): P` | a claim to be proven (proofs: core files for now, see docs/proof-plan.md) |

Generic parameters are written in brackets and inferred at call sites:
`proc set_flags[w: Width](r: bits[w])`.

## 3. Types

* `bool`, `nat`, `int` – mathematical; `nat`/`int` never overflow.
* `bits[n]` – an n-bit word, `n` any `nat` expression (may be a parameter:
  `bits[w]`, `bits[8*n]`).
* `A -> B` (total maps), `(A, B)` tuples, `List[T]`, `Set[T]`, `Option[T]`
  (`none` / `some(x)`), records, enums, sum types.
* `Seq[T]`: finite **or infinite** sequences, with `len : nat∞`
  (`nat∞ = nat ∪ {∞}`). `a <= b` on sequences is the prefix order. Every
  increasing chain has a limit (its least upper bound). `List[T]` is the
  finite subset.
* Refinements `{w: nat | w in {8, 16, 32, 64}}` – membership is a proof
  obligation, discharged automatically when obvious (constants, case splits).

In the logic, `bits[n]` is the set `{0 .. 2^n - 1}`, records are finite
functions from field names, sum types are tagged pairs – the same encodings
ji-trust already uses, but generated rather than written by hand.

## 4. Integers

The type decides the arithmetic; nothing converts implicitly.

* `+ - *` on `bits[n]` wrap modulo 2^n; on `int`/`nat` they are exact
  (`nat` subtraction is a type error unless provably non-negative; use `int`).
* Both operands must have the same type. Exceptions are operators whose
  signature is heterogeneous by definition: shifts `x << k`, `x >> k`,
  `x >>s k` take `k: nat`; bit test `x[i]` takes `i: nat`.
* Literals take the type from context and must fit; negative literals into
  `bits[n]` mean two's complement (`-1 : bits[64]` is all ones).
* Signed vs unsigned is a property of the **operation** on `bits`:
  `<` `<=` `/` `%` `>>` are unsigned, `<s` `<=s` `/s` `%s` `>>s` are signed.
* Conversions, all explicit:
  * `uint(x): nat`, `sint(x): int` – read a word as a number;
  * `bits[n](e)` – wrap any integer or word into n bits. The width is always
    written, never inferred: a conversion may lose information, and even
    when it does not, the width is worth seeing;
  * `zext[n](x)`, `sext[n](x)` – zero/sign extension to n bits, the target
    width always written;
  * slices `x[hi:lo] : bits[hi-lo+1]`, single bit `x[i] : bool`;
  * `b ? 1 : 0` style is written `if b { 1 } else { 0 }`.

Example: carry of an addition is `uint(a) + uint(b) >= 2^w` – computed in
`nat`, no overflow possible, the result is a `bool`.

## 5. Programs (`proc`)

A procedure denotes a relation between an input state and an **outcome**:

```
Outcome[S, V] = ok(S, V)           // normal return with a value
              | exc(S, Exception)  // raise; the state at the raise is kept, so
                                   // properties can inspect it (e.g. where a fault was)
              | diverge(Trace[S])  // infinite computation, with the limit of its traces
```

**Traces.** A state field declared `trace f: Seq[E]` records external
interaction. It can only be extended: `emit f e` appends one event, and an
assignment or `havoc` involving `f` must leave a value that extends the old
one (for `havoc`, only such values are chosen; for an assignment it is a
proof obligation). So along any run the trace grows in the prefix order. A diverging run has no final
state, but the values of its trace fields still converge. `Trace[S]` is the
record of those limits, which may be infinite sequences. A program that loops
printing forever ends in `diverge(t)` with an infinite `t.os.events`. A silent
infinite loop keeps the finite trace it had.

Statements:

| statement | meaning |
|---|---|
| `let x = e` / `let (a, b) = e` | immutable local |
| `var x = e`, `x := e` | mutable local, assignment |
| `lv := e` | state update; `lv` is a field path, map entry `gpr[r]`, slice `x[15:8]`, or a view call `reg(r, 32)` |
| `if c { } else { }`, `match e { p => ... }` | as usual; `if` and `match` are also expressions |
| `while c { }`, `for i in a..b { }`, `loop { … break … }` | loops, fixed evaluation order |
| `return e`, `raise e(...)` | leave normally / abnormally |
| `try { } catch e(x) { }` | handle an exception |
| `let x = any T where P(x)` | nondeterministic choice (`x` is bound in `P`); **if no such x exists the behavior is `undefined`** (never vacuous). General form in expressions: `any y: T where P(y)` |
| `let x = any T where P(x) else { S }` | as above, but if no such x exists, run `S` (which must end with `return` or `raise`) |
| `let x = any? T where P(x) else { S }` | may run `S` even when some x exists; must when none does (typical: `else { return fail() }` for an operation that may always fail) |
| `either { } or { }` | nondeterministic choice between blocks |
| `havoc lv`, `havoc flags.{af, pf}` | assign an arbitrary value (trace fields: any extension) |
| `havoc lv where P else { S }`, `havoc? lv where P else { S }` | as for `any`: `S` runs if (`?`: or whenever) no value makes `P` hold; `S` need not leave |
| `emit f e` | append event `e` to trace field `f` |
| `require P` | precondition: `undefined` if `P` is false |
| `undefined` | every outcome is possible |

Inside a `proc`, expressions may contain calls of procs and views; they are
evaluated innermost-first, left to right. `fn` bodies may use `let`, local
`var`s, `if`, `for` and `return` – these are sugar for pure expressions.
Binders in math expressions: `all`, `ex`, `{x: T | P}`, `min S`, `max S`,
`sum i in a..b. e`, lambdas `(x: T) => e`, list comprehensions
`[e for i in a..b]`. Other expression sugar: list slices `l[a..b]`, `l[a..]`,
concatenation `++`, record update `r with { f: e }`, `o.value` for an `Option`
known to be `some` (a proof obligation).

Views (`view`) give getters/setters to derived locations (`eax`,
the `rflags` word, an operand that is "a register or memory"). A view's
getter and setter are procedures, so they may fault (memory operands).

**Frames.** For each `proc` the tool infers the set of state lvalues it may
modify (through views as well). A `modifies` clause can be written and is then
checked. Each proc elaborates to a frame lemma "the outcome state agrees with
the input state outside the modified set", which is what later verification
uses most.

## 6. Elaboration into the logic

Each `proc p(x) -> V` becomes a predicate `p(x, s, o)` ("from state `s`, `p`
may produce outcome `o`"). Rules, with `⟦·⟧` the translation:

* `⟦A; B⟧(s, o)` = `⟦A⟧(s, o)` for non-`ok` `o`, or `∃ s1. ⟦A⟧(s, ok(s1)) ∧ ⟦B⟧(s1, o)`.
* `⟦let x = any T where P⟧; K` = `(∃x:T. P ∧ ⟦K⟧) ∨ ¬(∃x:T. P)`
  (the second disjunct: no witness ⇒ anything). With `else S`:
  `(∃x:T. P ∧ ⟦K⟧) ∨ (¬(∃x:T. P) ∧ ⟦S⟧)`; `any?` adds `∨ ⟦S⟧`, i.e. it is
  `either { S } or { let x = any T where P else S; K }`. There is
  deliberately no construct with *no* outcome: a model (the machine, the
  OS) without an outcome in some state would claim that state never
  continues.
* `⟦undefined⟧(s, o)` = `true`; `⟦require P⟧` = `P → skip`, i.e. `¬P ∨ ...`.
* `while` / recursive procs: finite and infinite runs are defined separately,
  as in coinductive big-step semantics (Leroy & Grall, 2009):
  * `ok` and `exc` outcomes: the **least** fixpoint (inductive). An outcome is
    possible if some finite number of iterations or calls produces it.
  * `diverge(t)`: the **greatest** fixpoint (coinductive). It is possible if
    there is an infinite sequence of iterations (or an infinite descent of
    calls), each starting in the state the previous one ended in. `t` is the
    limit of the trace fields along that sequence.

  This agrees with the fixpoint idea of `goal.md` (start from "everything
  diverges", refine monotonically) on terminating behavior, and adds the
  trace of infinite runs precisely. In particular, a program that prints `a`
  *n* times for a nondeterministically chosen *n* and then loops silently
  diverges with `a^n` for each n, but never with an infinite `a^ω`, because
  no single infinite run produces it. Monotonicity is checked syntactically
  for the built-in constructs; user-defined recursion must be structurally
  built from them.
* `fn`s become `def`s; recursive `fn`s need a decreasing measure.

Programs cannot occur under a quantifier because `fn`/`pred` bodies are
type-checked to be pure (they cannot call `proc`s or read state).

## 7. Lexical conventions and grammar (v0.1)

This is what `slc` parses (`slc/syntax`).

**Tokens.** Names `[A-Za-z_][A-Za-z0-9_]*`; numbers `123`, `0x1F`, `0b101`,
with `_` separators; strings `"..."`; comments `//`. Hex *bytes* in table
rows are written `0x83`: a bare `83` is decimal and a bare `FF` is a name.
All operators are ASCII (`natinf` instead of `nat∞`).

**Newlines.** A newline ends a statement when (1) the innermost open bracket
is `{` (or none), and (2) the line's last token can end a statement: a name,
a literal, `)`, `]` or `}`. So a line ending in an operator or `,`
continues, and newlines inside `(...)` and `[...]` never end anything.
`else`, `or` (after `either`) and `catch` may start the next line.

**Dots.** A `.` for field access or a qualified name (`x86.decode`) is written
without a space after it; the `.` of a binder is followed by a space:
`ex q: nat. q.f = 0`.

**Signed operators** `<s <=s >s >=s /s %s >>s` are single tokens when the `s`
is not followed by a name character: write `a /s b` (but `a / s`).

**Precedence**, lowest first: binders (`all x: T. P`, `ex`, `sum i in a..b. e`,
`any x: T where P` extend to the right) · `<->` · `->` (right) · `||` ·
`&&` · comparisons `= != < <= > >= <s <=s >s >=s in notin is refines`
(non-associative) · `..` · `|` · `xor` · `&` · `<< >> >>s` · `+ - ++` ·
`* / % /s %s` · unary `! - ~` · `^` (power, right) · postfix `f(..)`, `x[..]`,
`x[hi:lo]`, `x[a..]`, `x.f`, `x.{f, g}`, `r with { f: e }`.

**Braces.** In expression position `{` starts a set (`{}`, `{a, b}`,
`{x: T | P}`), never a block. `Name { f: e, g }` is a record literal, except
in the condition of `if` / `while` / `match` / `for`, where `{` starts the
body. Blocks as values occur only as `if` / `match` branches, lambda bodies,
`do[S] { ... }` (a program as a value) and `with view(args) { ... }`.

**Keywords** (not usable as names): `let var if else match while for in loop
break return raise try catch either havoc where require guard undefined emit
ghost fn pred proc view type enum record state const exception decoder
notations table using with param law theorem uses extends all ex sum any
true false self is notin refines do`. Contextual (usable as names): `spec`,
`layer`, `or`, `xor`, `trace`, `get`, `set`, `context`, `before`, `after`.

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
generics := '[' (NAME (':' type)?),+ ']'       // type param, value param, `enum bits[k]` kind
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
          | 'havoc' '?'? expr,+ ('where' expr ('else' block)?)?   // '?' needs 'else'
          | 'require' expr | 'guard' expr | 'undefined' | expr | block
arm      := pat,+ '=>' (block | stmt)
pat      := '_' | NUM | 'true' | 'false' | NAME | NAME '(' pat,* ')' | '(' pat,* ')'
```

## 8. Decoders, tables and notations

Binary formats (here: instruction encodings) are described with three
generic features. The language knows nothing about x86; the x86 prefixes,
REX, ModRM and the Intel-manual shorthand are all defined in
`spec/x86_64/encoding.sl` using these features.

### 8.1 Decoders

```
decoder context Ctx                 // the context type for the decoders below
decoder imm(n: nat) -> bits[8*n] {  // like a proc, but over a byte stream
  var v: bits[8*n] = 0
  for i in 0..n { v[8*i+7 : 8*i] := next() }
  return v
}
```

A decoder runs over a byte stream and a mutable context `ctx` (of the declared
context type). It cannot touch the machine state. Besides ordinary statements
it may use:

| | |
|---|---|
| `next()` | consume and return the next byte |
| `peek()` | return the next byte without consuming it |
| `guard c` | if `c` is false, the decoder **does not match** (this is not `undefined`) |
| `ctx.f := e` | update the context |
| `loop { … break … }` | loop with an explicit exit (also usable in procs) |

Meaning: `decoder d(x) -> T` denotes a pure function
`d(x, bytes, pos, ctx) -> Option[(T, pos', ctx')]`, where `none` means "does
not match".

### 8.2 Tables

```
table x86 using intel {
  context START          // initial context value
  before  prefixes()     // run before every row
  after   finish()       // run after every row
  0x83 /op:AluOp ib  => alu(op, rm, sext[w](ib))
  with w = opsize() { rows }     // prepend an item to each row in the block
  for op in AluOp { rows }       // generate rows, one per value
  for op in AluOp except cmp { rows }   // ... leaving out some values
}
```

A row is `items => statement`. It matches if `before`, its items (left to
right) and `after` all succeed. The kinds of items are:

| item | meaning |
|---|---|
| `0x83`, or any byte-valued `{expr}` | the next byte must equal it |
| `x = d(args)`, `(x, y) = d(args)` | run decoder `d`, bind the result |
| `d(args)` | run decoder `d`, ignore the result |
| `if expr` | guard on already bound values (`if rm is ref(m)`) |
| a notation | expands to items (8.3) |

The bound names are in scope in the row's statement, together with
`ctx`. The table elaborates to:

* a sum type `x86.Insn` with one constructor per row, carrying the row's
  bindings;
* `fn x86.decode(b: Bytes) -> Set[(nat, x86.Insn)]`: all matching rows with
  the number of bytes consumed;
* `proc x86.execute(i: x86.Insn)`: runs the row's statement.

If several rows match, all are possible (nondeterminism), and the tool reports
the overlap as a warning, since instruction bytes are bounded in length and
this can be checked by enumeration. What happens when no row matches is up to
the user of `decode`. The x86 `step` makes it `undefined`, so unmodelled
instructions keep the spec sound.

### 8.3 Notations

Notations are user-defined shorthand for table items, declared before they
are used:

```
notations intel {
  ib                     ~> ib = imm(1)
  /r                     ~> (r, rm, rm8, reg8) = modrm_r()
  /(d: nat)              ~> (rm, rm8) = modrm_ext(d)
  /(x: ident):(E: type)  ~> (x, rm, rm8) = modrm_enum[E]()
  (b: byte)+r            ~> r = plus_reg(b)
}
```

* A pattern is a sequence of ordinary tokens and typed holes. The hole
  categories are syntactic: `nat` and `byte` (numeric literals), `ident`,
  `type`, `expr`.
* In a row, the parser tries the notations of the table's `using` sets,
  longest match first, before the generic item forms. A literal token beats
  a hole: `/r` is the notation `/r`, not `/(x: ident)`.
* Expansion is textual substitution of the holes. It is **not hygienic on
  purpose**: names bound by the expansion (`r`, `rm`, …) become visible in the
  row. This is the only way a notation can introduce names, and the notation
  declaration shows exactly which names they are.
* Notations only produce items, so their meaning is always given by decoders
  written in SL. The parser needs no knowledge of the Intel manual. It needs
  the notation declarations, which precede their use.

## 9. Layers

There are two kinds of module:

* **`spec`**, e.g. `spec x86_64_linux`: the trusted model. Its definitions are
  *assumed* to describe the real machine and kernel. It should be small.
* **`layer`**, e.g. `layer abi uses x86_64_linux`: an abstraction built on top.
  It contains only definitions, parameters with laws, and theorems. A layer
  cannot make the trusted base claim more. A wrong layer is merely useless,
  because its theorems won't be provable, or they won't say what we want.

Final results are theorems whose statements unfold, through the layers'
definitions, to statements about the trusted spec.

### 9.1 Language features for layers

| feature | meaning |
|---|---|
| `proc[S] p(...)` | a proc over state type `S`. By default a module's procs run over its declared `state`, so the prefix is only needed when mixing. |
| `S & G`, `state H extends S { ghost f: T }` | a state extended with extra fields. **Ghost** fields exist only in the specification. Machine-level code never reads them, and they are changed only by `ghost` statements. A proc over `S` also runs on `S & G`, leaving `G` unchanged. |
| `self` | the whole current state, as a value |
| `havoc x where P` | give `x` any value such that `P` holds *afterwards*. If there is none, `undefined`; with `else { S }`, run `S` instead (`havoc?`: `S` may also run when there is one). |
| `with v(args) { body }` | run `body`, a proc over the view's type, through the view `v`. It reads via `get`, and writes the result back via `set`, also on exceptional outcomes. |
| `proc[S](A) -> R` | the type of procs. Procs are values, so a spec can take a spec as an argument. |
| `outcome(s, p(args), o)` | predicate: running `p(args)` from `s` may produce `o`. It talks about the relation without running anything, so it is allowed in `pred`. |
| `low refines high` | from every state of `low`'s state type (e.g. a well-formed `Machine`), every outcome of `low` is an outcome of `high`. If `high` has extra ghost fields: for every initial ghost value, and each outcome of `low`, *some* final ghost value makes it an outcome of `high` (forward simulation). |
| `param pred p(x)`, `param fn f(x) -> T` | an unknown of the layer. Everything in the layer holds for any value of it. |
| `law name(x): P` | an assumption about the params. It is not an axiom: it is discharged by an `instance`. |
| `instance M { p := ..., f := ... }` | gives the params concrete definitions, and turns each law into a proof obligation |

Preconditions are `require`, so violating a layer's rules (e.g. corrupting
the heap) is `undefined` at that layer, which is exactly how C describes
it.

### 9.2 The ABI layer (`layers/abi.sl`)

* `World`: what a C function sees, i.e. memory, OS state and the TLS pointer,
  but no registers. The view `world(sp)` maps the machine to it. The
  callee's scratch space is the stack below the caller's stack pointer plus
  the free space right below it into which the stack can grow (bounded by
  the next mapping, not by `RLIMIT_STACK`, so an unlimited stack does not
  swallow the heap). When reading, the view shows its contents as arbitrary
  (a function cannot rely on what lies below its caller's stack pointer;
  a proof chooses what the machine has there), but keeps its pages visible
  (stack pages are not free memory for an allocator); when writing back it
  leaves the contents arbitrary and lets the stack grow into free pages.
* A C function spec is a `CFun[S] = proc[S](Args) -> bits[64]` over `World`,
  or over an extension of it with ghost state.
* `abi_function(f, spec, args)` is what the ABI promises from function entry
  to return:
  - the entry conditions are `require`s: rsp on a writable stack page (the
    `call` has just written the return address there), with no other
    mapping within the guard gap below the stack (Linux keeps this gap for
    all but `MAP_FIXED` mappings; without it a push could overwrite other
    memory instead of faulting), alignment, direction flag clear, arguments
    in registers, and the thread pointer pointing to itself (the x86-64 TLS
    ABI; code reaches TLS and errno through `fs:0`);
  - the function behaves like `spec` on the world;
  - rbx, rbp, r12–r15 and rsp are restored, the result is in rax, and all
    other registers and the flags are clobbered;
  - **or** it runs out of stack: a fault (`maperr` or `accerr`) at an address
    of its scratch space, which is always possible. Memory and registers are
    then arbitrary, since
    the process dies. The I/O done so far (output written, input consumed)
    must be the beginning of some complete behavior the spec allows. This is
    sound because the crashed run is the same run as with a larger stack
    limit, cut short;
  - if the spec may raise from the entry world (`spec_raises`), anything.
    A C function's spec raises only through undefined behavior
    (`undefined` allows every outcome, exceptions included) or a deliberate
    crash, and C promises nothing then. (A spec's `undefined` alone would
    not suffice: it allows any outcome of the spec, but `abi_function` then
    still sets the registers and returns.) The program's top-level spec
    never raises, so this case never applies to a whole program.
* `implements(f, spec)`: `run_to_return()` (the actual machine, stepping until
  it returns to the return address) `refines` `abi_function(f, spec, args)`.
* `call_rule`: at a `call f` site the machine can be reasoned about as the
  spec. It is proven once, and then used at every call.
* Functions inside a program: `implements2_at(f, spec, base, code, statics)`
  is `implements2` provided the program is loaded (`loaded`): its
  executable segment `code` at `base` (`code_at`: its bytes in memory,
  executable, not writable), and its static data (the addresses `statics`)
  not on stack pages -- else a store to a global could overwrite a return
  address. Every function of the program assumes the same, so a caller and
  its callees share the precondition; `call_rule_at` uses it at a call
  site. To go on after a call, the caller needs the callee's spec to keep
  the program loaded (`keeps_code`, a frame property proven for each
  function at the C level). The program's entry points (malloc, free, calloc) keep
  the plain `implements2`: their specs give the code loaded (`image_ok`).

### 9.3 The malloc layer (`layers/malloc.sl`)

* Ghost state `blocks: Addr -> Option[nat]` holds the live blocks and their
  usable sizes. `heap_wf` states what every valid heap satisfies: blocks are
  non-null, 16-byte aligned, readable and writable, and pairwise disjoint.
* The allocator's internals (glibc's arenas, chunks, bins) are **params**:
  `alloc_inv` (the internals are intact and describe `blocks`) and
  `alloc_owned` (the bytes the allocator owns). Laws: the invariant implies
  `heap_wf`; owned memory is disjoint from live blocks and mapped; and the
  **frame law**: the invariant depends only on owned memory, so clients
  writing elsewhere cannot break it.
* `malloc` / `free` / `calloc` are nondeterministic procs:
  - `malloc` may always return 0. Otherwise it returns a fresh 16-aligned
    block taken from allocator memory or from new mappings, with arbitrary
    contents.
  - `free` requires a live block; an invalid or double free is `undefined`.
  - Apart from their own memory and mappings, the allocator functions change
    nothing.
* Heap corruption needs no special notion. A client write into
  allocator-owned memory is allowed by the machine, but may break
  `alloc_inv`, and the next `malloc` / `free` then fails its `require`, so its
  behavior is `undefined`.
* `allocator_correct(malloc_at, free_at, calloc_at)` is what a libc binary
  must satisfy. Its proof provides an `instance` of the params. Client proofs
  never see that instance.

### 9.4 The GIMPLE layer (`layers/gimple.sl`)

An implementation level between machine code and C function specs: GCC's
optimized GIMPLE (the last tree-level form, which is what gets compiled to
machine code; `scripts/dump-gimple.sh` dumps it with musl's exact flags).

* **Syntax as data**, in a normalized form a translator produces from GCC's
  dumps: `Function` (typed parameters, the types of names, stack objects,
  blocks, entry), `Block` (phis, statements, a jump), statements (`assign`,
  `load`, `store`, `store_bytes`, `call`, `asm`), right-hand sides (unary,
  binary, conversions, GCC internal functions such as `.CTZ`,
  `.MUL_OVERFLOW`, `.REDUC_IOR`), memory accesses as base + offset + size
  (+ bit position for bitfields). Names are numbers, fields are offsets,
  globals are addresses.
* **Meaning**: `gimple_fun(f, callees) : CFun2[World]` – a GIMPLE function is
  a C function spec. The relation to machine code is therefore the ABI's
  `implements2(address, gimple_fun(f, callees))`, and a proof that the
  GIMPLE refines e.g. `malloc_fun()` carries over. Callees are given by
  their specs (modular: each function is checked against its callees'
  specs).
* **State of a running function**: the `World` plus a `Frame` – values of
  names (integers with a type: precision and signedness), addresses of stack
  objects (placed in the scratch space below `World.sp`, growing the stack
  as needed; running out of stack is the ABI's crash case), the current and
  previous block (for phis).
* **Calls** run the callee's spec on a nested world view whose stack pointer
  `sp2` lies below the caller's stack objects. The caller's private frame
  `[sp2, sp)` (below the lowest object, with objects) holds none of its C
  objects: before the call its bytes are arbitrary, and the stack may have
  grown down to the return address's slot (`frame_at_call`); a callee that
  changes them is undefined -- C gives a callee no access there. (Machine
  code keeps spilled values in that frame; the bridge chooses the arbitrary
  bytes as the machine's.) **Inline assembly** is given its
  meaning by the machine model itself: the operands go into registers, the
  instruction bytes run through `x86.decode` / `x86.execute` on a machine
  built from the world.
* **Undefined** (chosen so that GCC's optimizations are valid): signed
  overflow, division by zero and overflowing division, shifts by at least
  the precision, pointer arithmetic that wraps around, misaligned accesses
  and accesses without the needed permission (C objects are never
  write-only), accesses through a null base pointer (even if page 0 were
  mapped: GCC deletes null tests after a dereference), `.CTZ (0)` without a
  value for zero. No type-based aliasing
  rules: musl is compiled with `-fno-strict-aliasing`.
* **Coupling for proofs**: `coupled(f, pt, sp, ret, entry, fr, w, m)`
  relates the running GIMPLE function (frame `fr`, world `w`) to the machine
  `m` at a program point `pt`: the machine address where a block begins,
  rsp relative to its value at entry, where each name's value is (`Home`: a
  register, a stack slot, a known constant, dead), where the stack objects
  are, and where the caller's callee-saved registers are kept. Memory, OS
  state and thread pointer agree except for scratch contents that are not
  GIMPLE objects (spills, callees' frames), and the machine's stack may be
  deeper. Proving `implements2` for a compiled function means showing that
  such couplings are preserved from block to block (with DWARF and the
  control-flow graph telling which points correspond).

Nothing in this layer is trusted: a mistake in it (or in the translator)
makes a proof fail, never makes a false claim provable.

**The translator** (`slc gimple`, in `slc/cli/src/gimple/`) turns a dump into
an SL layer with one `Function` per GIMPLE function
(`scripts/dump-gimple.sh` produces the inputs: the dump, and the object
compiled again with `-g`, which gives the same machine code):

* `dump.rs` parses the dump: declarations, blocks, phis, statements and
  expressions (`MEM[…]`, `->`, `.`, `[…]`, `BIT_FIELD_REF`, casts,
  `MIN_EXPR`…, internal functions, constructors, inline assembly; volatile
  accesses `={v}` as plain ones, `{CLOBBER}` and labels dropped);
* `dwarf.rs` reads struct layouts (member offsets, bitfields), arrays,
  typedefs and declared types from the object's DWARF (`readelf`);
* `lower.rs` numbers the names and types them; memory references become
  base + offset + size (bitfields: bit position and width), dynamic array
  indices explicit address arithmetic; locals used without an SSA version
  become stack objects; globals become addresses from the binary's symbol
  table (statics from the source file's own group); structs returned in
  rax:rdx become two values; inline assembly becomes its operands in
  registers and the instruction bytes, assembled by `as` from the template
  with those registers substituted. It checks that every name used is
  defined, and reports what it cannot translate instead of guessing.

All 14 functions of the allocator (mallocng's `malloc.c` and `free.c`,
`calloc.c`, `free.c`, `lite_malloc.c`) translate and elaborate.

The ABI layer's `World` includes the CPU features (`cpu`, inline assembly
may depend on them) and the caller's stack pointer (`sp`: a function's
stack objects go below it), and function specs may return two registers
(`CFun2`, rax:rdx, for small structs); `implements(f, spec)` for a
single-result spec is `implements2(f, wide(spec))`.

## 10. Static semantics (as checked by `slc`)

* **Names.** A module sees its own declarations and those of the modules it
  `uses`, transitively. Inside a procedure, a bare name is (in this order) a
  local, a value generic, a field of the current state, or a global. Enum
  values and constructors that share a name (`read` is both an `Access` value
  and an `IoEvent` constructor) are resolved by the expected type.
* **State.** Every `proc` / `view` has a state type: `proc[S]`, or the first
  `state` declared in its module. States are open records: a procedure over
  `Machine` also runs on `Machine & G` and leaves the extra fields alone.
  A call from a procedure over one base state to one over another needs
  `with view(..) { .. }`.
* **Effects.** `fn` / `pred` are pure: a procedure call there denotes the
  program (a value, e.g. for `refines` or `outcome`), never executes it.
  `any`, `havoc` and `next()` are only in procedures / decoders.
* **Types.** Arguments and assigned values must have compatible types:
  `nat` and `int` mix (nat is a subset of int); `bits` goes only with `bits`
  or enum values; literals take the expected type. Bit widths are compared
  in a linear normal form (`(8*i+7) + 1 - 8*i` is `8`): different literal
  widths are an error, widths that cannot be shown equal a warning. Generic
  parameters are inferred from argument types, including `n` in
  `bits[8*n]`. Operand sizes are counted in bytes (`Size`), so memory
  accesses need no division by 8.
* **Ghost / trace.** A ghost field is written only by `ghost` statements; a
  trace field only grows (`emit`, or `havoc` choosing an extension).
* **No recursion** yet: a definition may not depend on itself (loops are
  `while` / `loop` / `for`). Recursive procedures need the fixpoint
  machinery of section 6, which the prelude does not define yet.

## 11. The core logic and the claim

`core/prelude.core` is the background theory (section 6), in the kernel's own
syntax: `const` / `axiom` (only in the prelude), `def` (conservative
definitions) and `claim` (closed statements, no proofs yet). Operators are
fixed (`-> <-> || && ! = != in`), binders are `all x. P`, `ex x. P`, or an
argument `x y. t` of a binder constant (`set_select(s, x. p)`).

The elaborator turns each SL declaration into definitions: types into sets
(`bits[n]` = the integers 0 .. 2^n - 1, `nat` = the integers >= 0,
records = functions from field names, sums = `tag(i, payload)`); numbers
are integers, with total arithmetic (`int_add`, ...; a set that is not an
integer counts as 0), and word operations are integer operations mod 2^n
(`bits_add(n, a, b) = int_mod(a + b, 2^n)`); `fn` / `pred` into terms, procedures into programs
`mkprog(s o. F)` — sets of (state, outcome) pairs — and tables into a
`decode` set and an `execute` program. Layer parameters (`param`) become
extra arguments of every definition that depends on them; `law`s become
definitions; `theorem`s become `claim`s. The kernel re-reads the printed
output, so the elaborator is not trusted.

`slc claim malloc --elf BINARY` states, for a static musl binary:

```
ex alloc_inv, alloc_owned.
  laws(alloc_inv, alloc_owned)                   // malloc.sl
  && init_at_main(FILE, main, STATIC)            // claim_malloc.sl: when main starts, the
                                                 // invariant holds with no blocks, and the
                                                 // allocator owns only STATIC
  && implements(malloc) && implements(free) && implements(calloc)
```

with the file's bytes as a literal and `errno` at thread pointer + 0x34.
Besides STATIC, the allocator may own the thread descriptor up to errno and
libc's data on the initial stack: the auxiliary vector and the AT_RANDOM
bytes, which musl's allocator reads at its first allocation. The malloc
specs also require errno to be readable and writable (musl saves, restores
and sets it). It
writes the core file and a summary of everything the claim rests on
(kernel, prelude axioms, the `spec` files with hashes, the binary's hash).

## 12. Machine & process model decisions

* **State**: 16 GPRs, `rip`, flags `cf pf af zf sf df of` as `bool`s,
  `fs_base`/`gs_base`, virtual memory, and the OS part: the whole stdin
  content (fixed, possibly infinite) and the trace of I/O events
  (`read(bytes)`, `write(fd, bytes)`). What was consumed and what was output
  are derived from the trace, and so is the interleaving of reads and
  writes.
* **Memory** is a page map `PageNo -> Option[Page]` (protection + kind:
  `anon | heap | stack`) plus a byte map. VMAs are the maximal runs of equal
  pages, so `munmap`/`mprotect` splitting needs no bookkeeping.
* **Faults** raise `segv(addr, code)` carrying exactly what Linux puts in
  `siginfo`: the address and `SEGV_MAPERR` / `SEGV_ACCERR` / `SI_KERNEL`
  (the last for #GP, e.g. non-canonical addresses, with address 0) /
  `SEGV_PKUERR` (execute-only memory under protection keys). A
  non-canonical address through rsp/rbp (the stack segment) raises #SS,
  which Linux reports as SIGBUS: `stack_fault`. Page permissions follow the
  hardware: any accessible page is readable, except execute-only pages when
  Linux protects them with a protection key (`cpu.pku`).
* **Stack growth** follows Linux `expand_downwards`: an access to an unmapped
  page just below the stack extends it, if the new size stays within
  `RLIMIT_STACK`, the new start keeps `stack_guard_gap` (256 pages) from the
  previous accessible mapping, and the kernel does not (nondeterministically)
  run out of memory. Otherwise `segv(addr, maperr)`, like any unmapped access.
  The page kind `stack` makes "this page has become stack" observable.
* **Stack overflow is not a separate exception**: the kernel does not
  distinguish it either. Instead the spec provides predicates over the state
  at the fault, which a program can also compute (initial `rsp`,
  `getrlimit`): `stack_space(vm, a)` – addresses the main stack may ever
  occupy, `[stack_top − limit, stack_top)`; `below_stack_space(vm, a)` – the
  guard gap below that, where running out of stack faults. A contract can
  then say e.g. `raises segv(a, _) only if below_stack_space(vm, a)`.
  This is also how real runtimes (Rust) classify a SIGSEGV. Thread stacks
  (later) are ordinary mmap'd memory with a guard page and do not grow.
* **Faults terminate the process** (no signal handlers yet), so partial
  effects of a faulting instruction are irrelevant.
* **mmap/munmap/mprotect/brk** are specified with Linux semantics for anonymous
  private mappings; placement is nondeterministic (any free range respecting
  the stack guard gap); `-ENOMEM` is always a possible answer.
* **Page 0** is never handed out by the kernel on its own: a non-fixed
  `mmap` never returns it (POSIX: "it never places a mapping at address
  0"), the initial state has nothing there unless the image covers it
  (assuming no `MMAP_PAGE_ZERO` personality), and the break starts above
  it. The stack starts above the image, and grows only into the unmapped
  gap directly below it, so it cannot reach page 0 while the program's code
  stays mapped. Only an explicit `MAP_FIXED` at 0 maps it, which the model allows
  (Linux refuses it below `vm.mmap_min_addr` unless privileged). This is
  what lets C-level semantics treat a null pointer as pointing to nothing.
* Unknown syscalls, file mappings, signals, threads: `undefined` for now.

### 12.1 What the musl allocator needs (and how it is modelled)

`slc coverage build/test_malloc malloc free calloc` and the same from `_start`
(through `libc_start_main_stage2` to `main`) report no unmodelled
instructions; all 2426 reachable instructions decode with the same lengths
as objdump. Decisions made for them:

* **XMM registers** are part of the machine state (`xmm: Reg -> bits[128]`),
  zero at exec, clobbered by calls (all are caller-saved). Only integer SSE
  is modelled (`pxor`, `por`, `pand`, `movdqa`/`movdqu`, `movaps`/`movups`,
  `psrldq`/`pslldq`, `movd`/`movq`); instructions requiring alignment fault
  (#GP, `segv(0, kernel)`) on a misaligned memory operand.
* **`lock`** is accepted only where the manual allows it (a memory
  destination of add/or/adc/sbb/and/sub/xor, `xadd`, `cmpxchg`); with a single
  thread a locked instruction behaves like the unlocked one.
* **CPU features** are part of the machine state (`cpu: Cpu`), fixed for
  the whole run and not specified at process start, so a claim must hold
  for every CPU. `tzcnt` (`F3 0F BC`) executes as `tzcnt` if `cpu.bmi1`,
  otherwise as `bsf` (the two differ only for a zero source); `cpu.pku`
  decides whether execute-only memory can be read. Choosing per
  run rather than per instruction matches real hardware; `undefined` is
  kept for behavior that is really unknown.
* **`cmpxchg`** writes the destination back even when the comparison fails
  (so it needs write permission); register destinations are not modelled.
* **`bt`** only with a register operand or an immediate offset (the memory
  form with a register offset addresses outside the operand).
* **System calls:** `futex` for one thread (WAKE finds no waiters, WAIT
  either fails with EAGAIN or blocks forever), `set_tid_address` (returns
  some thread id).
* **Credentials:** the process state records the real / effective user and
  group ids and the secure-execution flag, as the kernel reports them in
  the auxiliary vector (`AT_UID`, ..., `AT_SECURE`). The trusted spec makes
  no assumption about them. The musl claim assumes an unprivileged start
  (`claim_malloc.unprivileged`), because musl's secure startup path uses
  `poll` and `open`, which are not modelled yet.

## 13. Tools (`slc/`)

```
cargo build --release  (in slc/)
slc parse  [PATH...]                      parse (default: spec/ and layers/)
slc check  [PATH...]                      parse, resolve, type-check, elaborate
slc elab   [PATH...] -o OUT.core          write the elaborated definitions
slc kernel-check core/prelude.core X.core re-check a core file with the kernel
slc decode ELF SYMBOL                     disassemble with the spec's own table
slc coverage ELF SYMBOL...                reachable instructions / syscalls not modelled
slc claim malloc --elf ELF -o OUT.core    state the claim (+ OUT.summary.txt)
slc cputest [--n N] [--rows K,..] [--seed S] [--verbose] [--limits FILE [--update-limits]]
slc gimple --elf ELF --obj F.o --source F.c DUMP.optimized -o OUT.sl
                                          translate a GIMPLE dump to the GIMPLE layer
                                          differential test against this CPU
```

Crates: `sl-kernel` (trusted; no dependencies), `sl-syntax`, `sl-elab`,
`sl-interp` (evaluates the decoding fragment directly on the AST, for
`decode` / `coverage` / `cputest`), `slc`.

**Differential testing (`slc cputest`, also `cargo test --test cputest`).**
Nothing in the test is written per instruction: for every row of the `x86`
table it samples random instruction bytes (with random 66/F3/F0/REX
prefixes) and keeps those the spec's decoder assigns to that row; it samples
register, flag and memory contents, runs the spec interpreter's `step()` on
that machine state, runs the same bytes on the real CPU, and requires the
CPU's behaviour to be one the spec allows.

* Every case ends with a signal: the instruction sits at the end of an
  executable page, after `int3` bytes and before an inaccessible guard page.
  Falling through faults at the guard page, a branch faults at (or traps
  just after) its target, and an instruction that raises an exception stops
  on itself. A handler on an alternate stack records the registers, so
  jumps, calls, `ret`, `ud2`, `hlt` and faulting instructions are all
  compared: normal outcomes on registers, flags, XMM registers, fs base,
  scratch memory and the next rip; exceptions on the signal (SIGSEGV with
  its address and code, SIGBUS for #SS, SIGFPE, SIGILL).
* Encodings are built from the row's items: required prefixes (`P66`,
  `REP`, `LOCK`, `REX.W`), opcode bytes (including `+r` / `+cc`), the ModRM
  reg field of `/digit`, register or memory form from guards like
  `rm is gp(_)`; random bytes fill the rest, and the spec's decoder must
  assign the result to the row and to no other.
* Memory operands usually point into scratch pages, sometimes (15%) to a
  read-only, write-only, execute-only, guard or unmapped page, a
  non-canonical or a kernel address. Every addressing form is aimed: base
  and index registers are set; fs/gs operands get a segment base for the
  case (set in the trampoline, restored by the handler); rip-relative and
  absolute operands get their displacement patched in the instruction
  (re-decoded to check). `ret` and indirect branches get interesting
  targets, stack instructions sometimes a faulting `rsp`; a sample whose
  branch would enter the instruction itself or the harness's code is
  redrawn.
* System calls run in a forked child with stdin/stdout/stderr on pipes and
  a prepared arena of pages; beyond registers and memory they are compared
  on the bytes written and consumed, the memory map (every page the spec
  knows, against `/proc/self/maps`), `brk`, and the exit status. Choices
  the interpreter cannot enumerate (`any` addresses, byte counts) are tried
  from hints (the kernel's result) and the ends of their ranges; a hint is
  only used if it satisfies the spec's condition.
* Quantifiers and set-builders over large ranges (e.g. `next_mapped` in the
  page-fault path) are evaluated at breakpoints: the numbers and map keys in
  scope and their neighbours; every gap between them is sampled at both
  ends and the middle, and if the samples differ the case is reported as
  unsupported instead of guessed.
* The spec is nondeterministic (`havoc`, `any`, undefined flags): a case
  passes if some spec outcome matches. Each row runs in its own process.

The manual parts are the case generators (`setup_hints`, `aim_memory`,
`aim_target` in `cputest.rs`, `sys::generate`) and the test's limits:
`tests/cputest-limits.txt` lists rows never compared and rows with samples
the interpreter could not evaluate ("partly skipped"; currently none).
Samples where the spec is `undefined` are a deliberate gap in the spec, not
in the test: they are only counted in the summary. Every full run prints them; with `--limits
FILE` (as in `cargo test`) a difference from the file fails the run, naming
the new gaps, until it is accepted with `--update-limits`.

What it found, all fixed: `xadd` recomputing its memory address after
writing its source register (`resolve`: addresses are computed once);
shifts by 0 still accessing the operand and zero-extending a 32-bit
register; non-canonical addresses through rsp/rbp raising #SS, which Linux
reports as SIGBUS (`stack_fault`); write-only pages being readable and
execute-only pages unreadable only with protection keys (`cpu.pku`,
`pkuerr`); `futex` checking alignment and address first and refusing
read-only pages for shared futexes, and a misparsed `sum` in its value
check (now an elaboration error); `mmap` rejecting unaligned offsets;
`arch_prctl` rejecting non-canonical fs bases; `read` into a buffer that
faults part-way writing a prefix before returning `EFAULT`; `read`/`write`
checking that the buffer lies in user space even for 0 bytes
(`access_ok`); `resolve` (used by `xadd`) losing the stack-segment check of
an `rsp`/`rbp` operand; and interpreter bugs (`cdq` producing 64-bit `-1`,
set-builders over large ranges silently truncated).

## 14. Open questions

1. Syntax of contracts / properties (`raises ... only if ...` above is a
   placeholder).
2. Signal handlers (`sigaction`, `sigaltstack`, delivery, `rt_sigreturn`):
   needed eventually for busybox; for now a `segv` ends the process.
3. Fault ordering for accesses spanning two pages – currently lowest address
   first; could be nondeterministic.
4. Instruction fetch from bytes of unmapped memory (instruction crossing into
   an unmapped page) currently decodes against the byte map and then faults –
   imprecise only in exotic cases (may give `undefined` instead of `segv`).
5. Name of the language.
6. The stack-overflow "prefix of an allowed behavior" policy should later
   cover other external kills too (the OOM killer, signals).
7. `realloc`, threads (malloc arenas, TLS), stack-passed and floating-point
   arguments.
8. Coverage beyond the musl allocator and startup: after `main`, `exit` may
   use `pause` (34); floating point, AVX, signals and threads are not
   modelled.
9. Recursion (general fixpoints) and a proof language.
10. Name resolution: a module's own declarations shadow the used modules'
    ones, but there is no way yet to name a shadowed declaration
    (`x86_64_linux.Operand`), and two used modules declaring the same name
    silently resolve to the first; qualified names and an ambiguity error
    would fix both.
