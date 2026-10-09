//! Trusted extensions of the kernel.
//!
//! The kernel (`env.rs`) defines the logic: its rules and the prelude's
//! axioms say what is provable. The extensions here add derived rules so
//! that proofs can take larger steps without being compiled down to kernel
//! steps. Each rule documents how it follows from the kernel's rules; they
//! are part of the trusted base (and listed as such), kept separate from
//! the kernel so that it stays minimal, and can later be replaced rule by
//! rule by proofs in the kernel.
//!
//! - `prop`: which terms are propositions; propositional tautologies.
//! - `seq`: natural deduction with hypotheses, quantifiers, equality,
//!   definitions; rewriting with an equation under `all`s at its instances
//!   under binders (`rewrite_under`, by the binders' extensionality).
//! - `arith`: linear arithmetic over the naturals; `nat_rec`'s recursion
//!   equations.
//! - `list`: lists up to associativity of `++`, their lengths (for
//!   `arith`), indexing, extensionality.
//! - `simp`: a simplifier for elaborated programs (symbolic execution of
//!   `runs(P, s, o)`) and propositions.
//! - `facts`: open lemmas and conditional theorems (bookkeeping, not a rule:
//!   nothing resting on an open lemma becomes a `Thm`).
//! - `cache`: theorems from `slc kernel-check`'s file cache, recorded
//!   without their proofs (trusting the cache; `--no-cache` avoids it).
//! - `mem`: a memory read through its writes (`gimple.bytes_at` of
//!   `store_le`s), the writes' places decided by `arith`.

pub mod arith;
pub mod cache;
pub mod facts;
pub(crate) mod inventory;
pub mod list;
pub mod mem;
pub mod prop;
pub mod simp;
pub mod seq;

pub use prop::Logic;
pub use seq::Seq;
