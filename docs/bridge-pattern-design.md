# The bridge by statement patterns (design, 2026-10-05)

C1 says that the machine code refines the readable GIMPLE under the ABI:
`abi.implements2_at(…, f.code(), spec, …)`. This document proposes how a
function's C1 proof should look: a **syntactic matching** of the machine code
against the readable GIMPLE, statement by statement. All semantics is in
lemmas proven once. It replaces the current bridge's per-function symbolic
co-execution (section 6.3 of proof-plan.md; measured in
bridge-search-inventory.md).

## 1. Why

The current bridge runs both semantics per function:
- spec_run on the GIMPLE;
- symex on the machine code, one step lemma per instruction address;
- then it compares paths, conditions and states.

Every fact it needs is an instance of a few general ones:
- a frame access is allowed by the ABI's stack guarantees;
- an access to GIMPLE memory is allowed where the GIMPLE's own access is
  (otherwise the spec has undefined behaviour);
- a `cmp`/`jcc` decides the GIMPLE `if`;
- a stored value is the GIMPLE's value.

It re-derives each of them at every occurrence, by search. On three small
functions that is 8.5 s of search (bridge-search-inventory.md), and the time
depends on which lemmas are in reach.

GCC at -O0 translates each GIMPLE statement by a fixed scheme. The facts
above therefore belong to the *scheme*, so each is proven once in a lemma
about a statement form and its instruction form. A function's proof then only
checks that its code is an instance of the scheme. It never mentions a memory
access, a flag or an arithmetic fact.

## 2. What GCC -O0 emits (the seven functions)

Leaf functions keep source variables in **homes** in the red zone: rsp-relative
slots, no frame pointer. Examples are `p`, `g` at rsp-8 and `x`, `sc`, `i` at
rsp-4. Parameters are stored to their homes first:

```
402c71  mov %edi,-0x4(%rsp)          ; x's home  (a_ctz_32)
40245e  mov %rdi,-0x8(%rsp)          ; g's home  (get_stride)
```

**Compiler temporaries** (`let tN`, and `var tN` from `iftmp`/`D.NNNN`) have
no homes. They live in registers from the statement that computes them to the
one that uses them:

```
_1 = -x;          402c75  mov -0x4(%rsp),%eax ; x
                  402c79  neg %eax            ; _1 in eax
_2 = x & _1;      402c7b  and -0x4(%rsp),%eax ; _2 in eax (x read again from its home)
_3 = _2 * K;      402c7f  imul $0x76be629,%eax,%eax
_4 = _3 >> 27;    402c85  shr $0x1b,%eax
_5 = debruijn32[_4];  402c88 mov %eax,%edx ; lea debruijn32(%rip),%rax ; movzbl (%rdx,%rax,1),%eax
D = (int) _5;     402c95  movsbl %al,%eax
return D;         402c98  ret
```

Most statements are 1–3 instructions, reading variables from their homes and
temporaries from registers. The scheme differs from a literal reading of the
statement in a few systematic ways. Each is a fixed rule of GCC's instruction
selection:

- **operand folding:** a variable used once is a memory operand
  (`and -0x4(%rsp),%eax`, `cmpl $0x1f,-0x4(%rsp)`), and `i = i + 1` on a home
  is one `addl $1,-0x4(%rsp)`;
- **arithmetic canonicalisation:**
  - `t6 * 4096` → `shl $0xc`, `t11 * 16` → `shl $0x4`, and `t + -16` →
    `sub $0x10` (get_stride);
  - `sc + 4294967289` (32-bit) → `sub $0x7` (is_bouncing);
- **condition canonicalisation:** the jump goes to the else branch on the
  negated condition, signedness picks the code, and a comparison with 0
  becomes `test`:
  - `if (_2 <= 31)` unsigned → `cmp $0x1f,%eax; ja else` (is_bouncing);
  - `if (_1 == 255)` → `cmp $0xff,%al; jne else`;
  - `if (i <= 31)` signed → `cmpl $0x1f,home; jle body`;
  - `if (_2 == 0)` → `test %al,%al; jne` (get_stride);
- **conversions:**
  - widening is `movzbl`/`movsbl`/`movzwl`/`cltq`/`mov %eax,%edx`, and
    redundant ones stay (`movzbl (%rax),%eax; movzbl %al,%eax`);
  - narrowing is free (using `%al` of `%eax`, `mov %al,X(%rip)`);
- **addresses:**
  - a global is `X(%rip)` or `lea X(%rip),%r`;
  - an array element is `base + index*size`, in an addressing mode
    (`(%rdx,%rax,1)`) or by `lea (%rax,%rax,1)` for size 2;
  - a struct field or bitfield is a displacement (`0x20(%rax)`);
- **bitfields:**
  - `g->maplen` (52 bits) → `mov 0x20(%rax),%rax; shr $0xc`;
  - `g->sizeclass` (6 bits) → `movzwl 0x20(%rax),%eax; shr $6,%ax; and $0x3f,%eax`;
- **control-flow edits:**
  - the return block is duplicated into each branch (is_bouncing:
    `iftmp = 1; D = iftmp; return D` → `mov $1,%eax; ret`, twice);
  - jumps are threaded to their final target (`jbe 0x402571`);
  - the GIMPLE loop `loop { if 31 <s i break; body }` is compiled with its
    test at the bottom (`jmp test; body: …; test: cmpl; jle body`).

## 3. The design

### 3.1 Program points and the coupling

A **point** pairs a position in the readable GIMPLE (before a statement)
with a machine address. At a point the two states are related by the
**coupling** `R(g, m)`. This is the relation `bridge_loop` already uses at
loop heads, extended with temporaries:

- each source variable in scope is in its home: `le(bytes(m), rsp0 + c, n) = x`;
- each live temporary is in its register (the low n bits): `reg(m, r) = t mod 2^n`;
- the memory outside the frame agrees with the GIMPLE world's (`abi.agree`),
  and the vm's other fields are equal;
- the ABI frame invariants hold:
  - rsp = rsp0;
  - the return address is at rsp0;
  - the callee-saved registers, os, fs_base, cpu and df are as at entry;
  - the code is loaded.

The homes and temporary registers at each point come from the matching (3.5);
DWARF can confirm the homes. R carries **no** facts about what the function
computes. It is the same shape for every function, and it is what the
statement lemmas preserve.

### 3.2 Three layers

1. **Decoding, per address (generated, mechanical).** `x86.decodes(vm, a, I, len)`:
   the bytes at `a` decode to the instruction `I`, an AST such as
   `mov_load(32, eax, mem(rsp, -4))` or `jcc(ja, 0x402571)`. The model's step
   is already decode-then-execute (`x86_64_linux.step` lets
   `x86.decode(bytes at rip)`), so these facts are concrete evaluations of
   the decoder. They replace today's per-address step lemmas, which fuse
   decoding with execution and carry each instruction's access premises.
2. **Instruction semantics, once per instruction form.** The execution of `I`
   with its fields symbolic (`neg(32, r)`, `mov_load(w, r, mem(base, disp))`,
   …): its effect, and when it can fault. This is proven from the model once
   per form, not per address.
3. **Statement lemmas, once per pattern.** For a statement form S and an
   instruction-sequence form P:

   ```
   all <holes>. decodes(.. P's instructions at a, a+l1, ..) ->
     sim(R_pre, a, S, R_post, b)
   ```

   `sim` says that from any coupled pair at `a`, one of these holds:
   - the GIMPLE statement raises (undefined behaviour: nothing is required);
   - or the machine runs from `a` to `b` without faulting and the GIMPLE
     statement completes, coupled again by `R_post` (`R_pre` updated by S's
     effect: a home, a temporary's register, the memory).

   A branch statement has two exits.

   **The access checks live here, once:**
   - a home access is allowed because R places homes in the frame and the
     ABI's entry conditions make the frame accessible (`abi.slot_at`);
   - a memory access is allowed because the GIMPLE statement's own access
     (`ld8`, `st8`, `elem`, `ldbf` …) succeeded, which requires `usable`,
     and the machine address equals the GIMPLE address (`g.read_off`).

   The flag reasoning (`cmp` + `ja` ⇔ `!(t <= 31)`) and the arithmetic
   canonicalisations (`x * 4096 = shl(x, 12)` on the word, the bitfield
   extractions) are proven in these lemmas, as math lemmas.

### 3.3 Values

A temporary's value is an expression of the statement's operands. The pattern
fixes which instruction computes which operation:
- `neg` ↔ `-`, `imul $k` ↔ `* k`, `shr $k` ↔ `>> k`;
- `shl $k` ↔ `* 2^k` (canonicalisation);
- `sub $k` ↔ `+ (2^n - k)`.

The correspondence is in the pattern's statement, so matching a block against
a statement compares the operation and the constants syntactically. Nothing
is normalised at match time beyond literal arithmetic on the constants, such
as checking `4294967289 = 2^32 - 7`.

### 3.4 Composition and adequacy

The readable GIMPLE is structured: statement sequences, `if`, `loop` with
`break`, `return`. The composition rules follow that structure:

- **sequence:** `sim(R1, a, S1, R2, b)` and `sim(R2, b, S2, R3, c)` give
  `sim(R1, a, S1; S2, R3, c)`;
- **if:** the branch statement's lemma gives each exit's coupling, and the
  two arms are composed separately. A duplicated machine tail is just two
  matchings of the same GIMPLE suffix;
- **loop:** the coupling at the head is the invariant. No user invariant is
  needed: R says nothing about values, and the loop is related step for step.
  A terminating machine run passes the head finitely often; a diverging one
  passes it infinitely often, and the GIMPLE diverges with the same trace.
  This is `abi.loop_sim`'s argument, stated for R. The `{l. int_le(snd(l),
  32)}` that step_seq passes today was needed only because symex re-derived
  the array access's bounds. Under the patterns, the access is justified by
  the GIMPLE `st8` succeeding.
- **return:** `return t` with t in rax, `ret` with rsp at the return address
  and the ABI invariants of R gives the ok case of `abi.matches_at`.

An **adequacy theorem**, proven once, turns a complete matching of the
function body from the entry point to all returns into `abi.matches(spec, args,
s, o)`. It uses the prologue (the parameter registers stored to their homes:
the argument coupling, `abi.arg_passed`), and through the existing
`abi.bridge_implements` it gives `abi.implements2_at`.

### 3.5 The per-function proof

A **matching certificate** lists, for each statement in the readable GIMPLE:
- its machine address range;
- the pattern;
- the hole values (homes, registers, constants, symbols);
- the temporary registers at its boundaries;
- the branch targets.

Checking it is syntactic:
- each block's decode facts are instances of the pattern's instructions;
- the statement is an instance of the pattern's statement form;
- the couplings at consecutive points agree;
- the jump targets are the addresses of the right points.

There is no search, no arithmetic beyond constants, and no lemma selection.
Each pattern lemma is applied at an instance read off the certificate.

The certificate is found by a **matcher**: a deterministic left-to-right walk
over the GIMPLE and the code that tries the patterns for the statement at
hand. The matcher sits outside the trusted base, because its output is
checked. A failure names the statement and the block: "4024df..4024ec does
not implement `st8(elem(padd(__malloc_context, 848), sext[64](i), 1), 0, 0)`:
expected an indexed byte store".

A function's C1 proof becomes:

```
theorem ss.implements: all statics. ss.statics(statics) ->
  abi.implements2_at(single(empty), 4203722, ss.spec, 4203722, step_seq.code(), statics)
proof
  fix statics
  assume hs: ss.statics(statics)
  show := translate(step_seq, ss.spec, hs)
qed
```

## 4. The patterns the seven functions need

Rows are statement forms; w is a width, h a home, r a register, k a constant.

| statement form (readable GIMPLE) | instruction form | in |
|---|---|---|
| prologue: param → home | `mov %rdi,h` / `mov %edi,h` | gsi, a_ctz, is_b, gs |
| `let t = x` (x in a home) | `mov h,%r` (w = 32, 64) | all with params |
| `x := k` (home) | `movl $k,h` | step_seq |
| `x := x + 1` (home, signed) | `addl $1,h` | step_seq |
| `let t = u op k`: `+ k`, `- k`, `& k`, `* k`, `>> k` | `add`/`sub`/`and`/`imul`/`shr`/`shl $k,%r` | all but locks |
| `let t = -u` | `neg %r` | a_ctz |
| `let t = x & u` (x in a home) | `and h,%r` | a_ctz |
| `let t = zext/sext/trunc(u)` | `movzbl %al,%eax`, `movsbl`, `movzwl`, `cltq`, `mov %eax,%edx`, nothing | most |
| `let t = ld8(padd(p, k), 0)` / `*(p + k)` | `sub $k,%rax; movzbl (%rax),%eax` | gsi |
| `let t = ldN(elem(G, sext(u), s), 0)` (global array) | `cltq; lea G(%rip),%rd; movzbl/movzwl (%rax,%rd,1)`, with `lea (%rax,%rax,1)` for s = 2 | a_ctz, is_b, gs |
| `st8(elem(G, sext(x), 1), 0, k)` | `mov h,%eax; cltq; lea G(%rip),%rdx; movb $k,(%rax,%rdx,1)` | step_seq |
| `let t = G.field` / `set_G.field(k or t)` | `movzbl G+o(%rip),%eax` / `movb $k,…` / `mov %al,…` / `movl $k,…` | step_seq, resetlock |
| `let t = ldbf(p, o, n, s, w)`, `meta_maplen(p)`, `meta_sizeclass(p)` | `movzbl/mov/movzwl o(%rax),%r` + `shr`/`and` | gs |
| `if t cmp k` (unsigned, signed, = 0, = k) | `cmp $k,%r` / `cmpl $k,h` / `test %r,%r` + `ja`/`jbe`/`jne`/`je`/`jle` | is_b, gs, step_seq |
| `loop { if c break; body }` | `jmp test; body; test: cmp; jcc body` | step_seq |
| `return k` / `return t` / `return` | `mov $k,%eax; ret` / `ret` / `nop; ret` | all |

That is about 20 patterns, each with a few width/sign variants. The six
functions after these will add their own forms: calls, 64-bit compares,
struct stores.

## 5. What stays, what goes

- **Stays:**
  - the x86 model;
  - `abi.matches`, `abi.bridge_implements`, `abi.implements2_at`;
  - the frame and agreement lemmas (`abi.slot_at`, `abi.agree_*`,
    `g.read_off` …), which are now used inside pattern proofs;
  - the readable GIMPLE and its operation semantics;
  - the loop argument (`abi.loop_sim`, restated for R; still to be proven).
- **Changes role:** symex and spec_run become tools for **proving the pattern
  lemmas** (once each), not for function proofs. The current bridge
  extension and its per-function obligations are retired once the pattern
  route covers the seven functions.
- **Goes:**
  - the per-address step lemmas with access premises (replaced by decode
    facts);
  - the bridge's lemma selection;
  - the loop invariant argument;
  - the word-form retries and their searches.

## 6. Decisions needed

1. **Where the matcher lives:** an untrusted tool emitting the certificate
   (proposed; the kernel only checks), or inside a kernel extension.
2. **The pattern lemmas' form:** one lemma per pattern with all its variants
   as holes (fewer lemmas, more general proofs), or one per variant (simpler
   proofs, more lemmas).
3. **Instruction semantics (layer 2):** the model's executor must allow
   proofs with symbolic operand fields. That holds if `x86.decode` yields an
   AST that the executor dispatches on. I still have to confirm it in the
   model, and it's the first technical risk.

## 7. Plan

1. Confirm layer 2 on two forms (`mov_load`, `neg`): decode facts, and the
   generic execution lemma.
2. Define `R`, `sim` and the sequence rule; prove the patterns a_ctz_32 needs
   (it is loop-free and memory-light). Match it, and check its C1 by the new
   route.
3. Branches (is_bouncing: canonicalised conditions, the duplicated return),
   then memory and bitfields (get_slot_index, get_stride).
4. The loop rule and step_seq, without an invariant.
5. Retire the per-function bridge; redo the remaining functions.
