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

The background logic (`core/prelude.core`) is classical second-order logic
with Hilbert choice and set theory with a hierarchy of Grothendieck
universes. Everything after its axioms is a conservative definition.

### What is trusted

- The kernel (`slc/kernel`) and its documented extensions: tautologies,
  linear arithmetic, memory reads through writes, the simplifiers.
- The model of the machine and the OS (`spec/`): x86-64 and Linux written
  in SL, assumed to describe the real machine. It is differentially tested
  against the real CPU (`slc cputest`, gaps in `tests/cputest-limits.txt`).

The front ends are not trusted: the elaborator, the proof language and the
generators of GIMPLE and decode facts. A mistake there makes a proof fail,
never a false theorem. See `docs/overview.md` for the details.

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

## Layout

- `core/`: the background theory and its libraries.
- `spec/`: the machine and OS model.
- `layers/`: the specification layers.
- `proofs/`: the proofs. `proofs/chain` lists them in checking order.
- `slc/`: the tool, in Rust: kernel, parser, elaborator, proof language,
  interpreter, CLI (claims, GIMPLE and C1 generators, the checker).
- `scripts/`: building musl, generating files, checking the chain.
- `tests/`: the test programs and the CPU test's known limits.
- `docs/`:
  - `overview.md`: the approach and what is trusted;
  - `language.md`: the languages;
  - `done.md`: what is done;
  - `todo.md`: what comes next.
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
6 GB.

## Status

Both claims are proven, with no open lemma. Next steps are in
`docs/todo.md`: a witness that some run reaches `main`, shared libraries
and the dynamic linker, and usability of the proof language.

## License

MIT, see `LICENSE`.
