//! Cached statements: `slc kernel-check`'s file cache (a trusted entry, not
//! a rule of the logic).
//!
//! After checking a core file, the checker may write its *statements*: the
//! file with each `proof ... qed` replaced by `cached` (and the open lemmas
//! a conditional theorem rests on, `cached rests(a, b)`). Loaded in cache
//! mode (`syntax::load_cached`, never for a source file), such a theorem is
//! recorded without its proof by `admit`. What is trusted: that the cache
//! holds what the checker wrote for an unchanged file after the same
//! statements of the files before it, by the same checker -- the CLI's
//! conditions for reading it. `slc kernel-check --no-cache` checks every
//! proof again.
//!
//! The proof cache (`syntax::ProofCache`, for a file not in the file
//! cache) admits single theorems the same way: a proof whose text, and the
//! text it is checked in (the file up to it, earlier proofs cut out), the
//! checker had checked before after the same statements of the files
//! before. Trusted alike: that its entries hold what the checker wrote.

use super::facts;
use super::seq::Seq;
use crate::env::{Env, KResult, Thm};
use crate::term::Term;

/// Records the cached theorem `name: prop` (resting on the open lemmas
/// `open`, if any) as the checker had proven it.
pub(crate) fn admit(env: &mut Env, name: &str, prop: Term, open: Vec<String>) -> KResult<()> {
    env.check_wf(&prop, 0)?;
    if open.is_empty() {
        if env.open.conditional.iter().any(|(n, _)| n == name) {
            return Err(crate::env::KernelError(format!("`{}` is already proven", name)));
        }
        return env.add_theorem(name, Thm::by_extension(prop));
    }
    facts::record(env, name, Seq::cached(prop, open))
}
