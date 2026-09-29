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
//!   definitions.
//! - `facts`: open lemmas and conditional theorems (bookkeeping, not a rule:
//!   nothing resting on an open lemma becomes a `Thm`).

pub mod facts;
pub mod prop;
pub mod seq;

pub use prop::Logic;
pub use seq::Seq;
