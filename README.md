# sw-veri

**An AI-maintained project for software verification in a set-theory-based
mathematical system.** The code, the specifications and the proofs are
written and maintained by an AI (Claude), directed by a human. The goal is
to investigate:

- what a good language for stating and proving properties of real code
  looks like, from the CPU's specification up;
- how to separate the levels of a verification into layers, and how to
  compose them well.

The prototype is the verification of a real memory allocator: musl's
mallocng `malloc` and `free`, as machine code in a static x86-64 binary.

## What is proven

The chain (`proofs/chain`) checks two closed statements about one binary:
musl 1.2.6 built with `-O0`, statically linked with the test program
`tests/test_malloc.c`.

- **`musl_malloc`, the allocator.** There is an invariant on the heap and
  a set of bytes the allocator owns such that:
  - every call of `malloc` and `free` in the binary, as machine code,
    implements the specs in `layers/malloc.sl`, keeping the invariant;
  - the invariant holds when `main` starts, in every run from an
    unprivileged exec state that reaches `main`;
  - laws a client can rely on hold, such as owned memory being private and
    mapped, and the frame of a call.
- **`musl_program`, a whole client.** Every run of the process from an
  unprivileged exec state ends, and it ends in one of two ways:
  - an exit with status 0 or 1;
  - a stack overflow.

  There is no other crash and no run that never ends. The program's
  pattern check, which would exit with 42, never fails.

Both are proven down to the binary's bytes, from the model of the CPU and
the OS. No lemma is left open.

The background logic (`core/prelude.core`) is classical second-order logic
with Hilbert choice and set theory with a hierarchy of Grothendieck
universes. Everything after its axioms is a conservative definition.

### What is trusted

- The kernel (`slc/kernel`) and its documented extensions: tautologies,
  linear arithmetic, memory reads through writes, the simplifiers.
- The model of the machine and the OS (`spec/`): x86-64 and Linux written
  in SL, assumed to describe the real machine. It is differentially tested
  against the real CPU (`slc cputest`, gaps in `tests/cputest-limits.txt`).
- The statements: `layers/claim_malloc.sl`, `layers/claim_program.sl` and
  the layers they use (`layers/malloc.sl`, `layers/abi.sl`) say what is
  claimed, so a reader has to check that they mean what is wanted.

The front ends are not trusted: the elaborator, the proof language, the C1
engine and the generators of GIMPLE and decode facts. A mistake there
makes a proof fail, never a false theorem. See `docs/overview.md` for the
details.

## Start here

1. **This README**: what is proven and how to check it.
2. **[docs/overview.md](docs/overview.md)**: the approach. It starts with
   the big picture and follows one small function (`get_slot_index`) from
   its C source through machine code, GIMPLE, its spec and its proofs up
   to the claim. It ends with a glossary of the project's terms.
3. **The statements**, in SL, a language close to C:
   - `layers/claim_malloc.sl` and `layers/claim_program.sl`: the two
     claims;
   - `layers/malloc.sl`: what `malloc` and `free` promise a client.
4. **Then any of the following**, depending on interest:
   - [docs/language.md](docs/language.md): the specification language SL
     and the proof language, as a reference;
   - [docs/done.md](docs/done.md): a detailed record of what is done, by
     area;
   - [docs/todo.md](docs/todo.md): what comes next;
   - [goal.md](goal.md): the project's original brief.

### Where to find things

| question | where |
| --- | --- |
| What exactly is claimed? | `layers/claim_malloc.sl`, `layers/claim_program.sl`; after setup, `build/chain/claim.summary.txt` lists the binary's addresses and the trusted base |
| What may a client of `malloc` and `free` rely on? | `layers/malloc.sl` (specs and laws), `proofs/malloc_client.core` (consequences) |
| How are the CPU and Linux modelled? | `spec/x86_64/`, `spec/linux/` |
| What does a C function see, and what is the ABI? | `layers/abi.sl` |
| What is readable GIMPLE? | `layers/gimple.sl`; the generated code in `build/gimple-O0/sl/` after setup |
| What is mallocng's invariant? | `layers/mallocng.sl` (its design is in the comment at the top) |
| What is each mallocng function for? | `layers/mallocng_specs.sl` |
| Where is the proof for function F? | C2: `proofs/mallocng/fun/`, one file per function or family (`get_slot_index.core`, `lists.core` for queue and dequeue); the test program's in `proofs/test/`. C1: F's `c1` line in `proofs/mallocng/machine/` |
| How do the pieces join into the claims? | `proofs/mallocng/top.core`, `top_free.core`, `init.core`, `claim.core`; `proofs/test/whole_top.core` |
| How are machine code and GIMPLE related? | the rules in `proofs/translate*.core`, the engine in `slc/cli/src/c1/` |
| What does the proof language look like? | `docs/language.md` §13; any file in `proofs/mallocng/fun/` |

## The layers

From the bottom up:

| level | where | what |
| --- | --- | --- |
| machine | `spec/x86_64`, `spec/linux` | instructions, memory with pages and stack growth, syscalls, exec |
| ABI | `layers/abi.sl` | the C world as a C function sees it; contracts of functions |
| GIMPLE | `layers/gimple.sl` | GCC's GIMPLE as readable code, generated from the compiler's dumps |
| allocator | `layers/mallocng.sl`, `layers/mallocng_specs.sl` | mallocng's abstract state, its invariant, its functions' specs |
| client | `layers/malloc.sl` | what a client of malloc and free may rely on |
| claims | `layers/claim_malloc.sl`, `layers/claim_program.sl` | the statements proven |

Machine code is related to GIMPLE automatically: the C1 engine in `slc/cli`
checks each function's code against its GIMPLE. GIMPLE is related to the
specs by hand-written proofs (C2, `proofs/`).

## Size

- About 100 functions' machine code is checked against their GIMPLE: the
  allocator, musl's startup and exit code, and the test program.
- The model (`spec/`) is about 1,500 lines of SL, and the layers about
  5,000.
- The proofs are about 170,000 lines.
- The tool (`slc/`) is about 61,000 lines of Rust, of which the kernel
  with its trusted extensions is about 13,500.

## Layout

- `core/`: the background theory and its libraries.
- `spec/`: the machine and OS model.
- `layers/`: the specification layers.
- `proofs/`: the proofs. `proofs/chain` lists them in checking order.
- `slc/`: the tool, in Rust: kernel, parser, elaborator, proof language,
  interpreter, CLI (claims, GIMPLE and C1 generators, the checker).
- `scripts/`: building musl, generating files, checking the chain.
- `tests/`: the test programs and the CPU test's known limits.
- `docs/`: the documentation (see "Start here").
- `goal.md`: the project's original goal.

## Checking it

The claim contains the binary's bytes, and the proofs refer to its
addresses. They check only for the same binary: musl 1.2.6 built by
GCC 16.2.1, the compiler used here. Another compiler version gives other
bytes.

Requirements: Rust (cargo), GCC 16.2.1, Python 3, binutils (objdump),
and the musl 1.2.6 source tree.

```sh
MUSL_SRC=/path/to/musl-1.2.6 scripts/setup.sh   # build slc and musl, dump GIMPLE, generate files
scripts/check.sh                                # check the whole chain
```

`scripts/setup.sh` builds the checker and musl at `-O0` with the test
program, dumps GCC's GIMPLE of the translation units the proofs read, and
generates the decode facts, readable GIMPLE and the locals' location map.
`scripts/check.sh` keeps caches in `build/`. A check without them takes
about 25 minutes and about 2.5 GB of memory; the script limits memory to
6 GB. It ends with:

```
status:
  claim musl_malloc: proven
  claim musl_program: proven
ok: all declarations well-formed, definitions conservative, proofs checked, claims closed
```

`scripts/check.sh FILE` checks the chain up to FILE. With the caches, an
edited proof is checked again on its own, in about a second.

## Status

Both claims are proven. Next steps are in `docs/todo.md`:
- a witness that some run reaches `main`;
- shared libraries and the dynamic linker;
- usability of the proof language.

## License

MIT, see `LICENSE`.
