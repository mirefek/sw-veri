# Software verification

The long-term goal of this project is to software-verify basic software up to machine code level. Starting with tools such as libc ([musl](https://git.musl-libc.org/cgit/musl) 1.2.6), and [busybox](https://git.busybox.net/busybox) (0.60.3).

For that, we first need a convenient formal language for stating properties about code, starting from CPU specification, and building abstraction layers above.

## Ideas

As of theoretical foundations, base the background logical theory on a second-order system, such as logic.c of [ji-trust](https://git.olsak.net/mirek/Vibe-ITP).

A program would be a "stateful non-deterministic function", so something that gets a state, and an input, and returns either an exception, or a possibly modified state, with an output.
* Except standard exception, also "infinite calculation" is logically an "exception"
* "Undefined behavior" means that the output of the program can be arbitrary (arbitrary exception, arbitrary output state ...)
* The state often has many "getters" & "setters" for particular fields / calculated attributes, or parts of the field of a state.
* Most of programs do not change most of the fields / attributes (calculated fields), so we are tracking which fields / subfields could be changed by which programs (in harder cases, a manual proof must come)
* Distinguish mathematical functions, and programs. programs can in principle call mathematical functions, but if a mathematical function introduces a binder (e.g. a quantifier), it should not be able to have a program inside. A program can take introduce a binder too with programs inside (such as for loop, list map) but then it knows exactly in which order the subprograms are called.

The programmatic syntax should have relatively standard (and possibly rich) type support, which gets translated into a proposition in the background logic.

There should be also further logical (and convenient) language for describing program's properties. These should include keeping the invariants, as well as standard software specification attributed to the standard functions.

An abstraction layer is a mathematical mapping from low-level states satisfying certain properties to a more high-level states which properties are some attributes of the low-level states. Also, not every high-level state encodes for a low-level state.

Mathematically, (possibly mutually) recursive function is a fixpoint of the program constructors which starts with assigning all programs the "infinite loop" exception. For the fixpoint to work, we should expect each program recurrence description to be "monotone" in a way that it allows all the outputs it allowed before (only possible exception infinite loop), and if it didn't allow infinite loop on certain input, then it still should not allow infinite loops.

## x86_64 spec

We aim at a language that can precisely, and confortably describe the important parts of x86_64 spec (for start at least those that are covered by mmc of [Metamath Zero](https://github.com/digama0/mm0), and [ji-trust](https://git.olsak.net/mirek/Vibe-ITP)). The language should probably mostly resemble imperative code but with undeterminism where the behavior is not fully specified.
The state should store how the system allocates memory for the code, so mmap / munmap / mprotect can be implemented accordingly.
As an exception, distinguish crashing on stack overflow, and crashing on segfault. Note that the stack can dynamically grow, be precise in that (exceptionally, a code could detect if a memory which was not stack became stack).
