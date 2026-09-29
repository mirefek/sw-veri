//! Open lemmas and conditional theorems: how a proof is broken into parts
//! that are proven separately (in any order, in later files).
//!
//! Not a rule of the logic. An open lemma is a statement without a proof
//! (`lemma NAME(params): φ`); it is not an axiom and never yields a `Thm`.
//! A proof that uses open lemmas gives a *conditional theorem*: a sequent
//! resting on them (`Seq::open`), recorded here and usable by later proofs,
//! but never turned into a `Thm`. When every open lemma it rests on is
//! proven (`remaining` is empty), the conditional theorem holds: chaining
//! the proofs (cut) gives a kernel proof. Cycles are rejected.
//!
//! A proof of an open lemma schema with parameters proves every instance,
//! so a conditional theorem's use of any instance is covered.

use super::seq::Seq;
use crate::env::{Env, KResult, KernelError};
use crate::term::Term;

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

#[derive(Default)]
pub struct OpenFacts {
    /// open lemmas: statements to be proven
    pub lemmas: Vec<(String, Term)>,
    /// theorems proven from open lemmas
    pub conditional: Vec<(String, Seq)>,
}

/// Declares an open lemma.
pub fn add_lemma(env: &mut Env, name: &str, prop: Term) -> KResult<()> {
    env.check_wf(&prop, 0)?;
    check_new(env, name)?;
    env.open.lemmas.push((name.to_string(), prop));
    Ok(())
}

/// `name` is not yet a claim, lemma or fact (a claim or lemma must come
/// before its proof, which is checked against its statement).
pub fn check_new(env: &Env, name: &str) -> KResult<()> {
    if statement_of(env, name).is_some() || seq_of(env, name).is_some() {
        return err(format!("`{}` already exists", name));
    }
    Ok(())
}

/// The statement of an open lemma or a claim (what a `theorem` of that name
/// has to prove).
pub fn statement_of(env: &Env, name: &str) -> Option<Term> {
    env.open.lemmas.iter().chain(env.claims.iter()).find(|(n, _)| n == name).map(|(_, t)| t.clone())
}

/// A fact for proofs: a theorem, an axiom, a conditional theorem, or an
/// open lemma.
pub fn seq_of(env: &Env, name: &str) -> Option<Seq> {
    if let Some(t) = env.fact(name) {
        return Some(Seq::of_thm(t));
    }
    if let Some((_, s)) = env.open.conditional.iter().find(|(n, _)| n == name) {
        return Some(s.clone());
    }
    Seq::open_lemma(env, name).ok()
}

/// Records a proof of `name`: a theorem, or a conditional theorem if it
/// rests on open lemmas.
pub fn record(env: &mut Env, name: &str, s: Seq) -> KResult<()> {
    if env.fact(name).is_some() || env.open.conditional.iter().any(|(n, _)| n == name) {
        return err(format!("`{}` is already proven", name));
    }
    if s.open().is_empty() {
        let thm = s.into_thm(env)?;
        return env.add_theorem(name, thm);
    }
    if !s.hyps().is_empty() {
        return err(format!("hypotheses left: {}", s.show(env)));
    }
    let mut path = vec![name.to_string()];
    for d in s.open() {
        if d == name {
            return err(format!("circular: the proof of `{}` rests on `{}` itself", name, name));
        }
        remaining_from(env, d, &mut path, &mut Vec::new())?;
    }
    env.open.conditional.push((name.to_string(), s));
    Ok(())
}

/// The open lemmas `name` still rests on, transitively (empty: proven).
pub fn remaining(env: &Env, name: &str) -> KResult<Vec<String>> {
    let mut out = Vec::new();
    remaining_from(env, name, &mut Vec::new(), &mut out)?;
    Ok(out)
}

fn remaining_from(env: &Env, name: &str, path: &mut Vec<String>, out: &mut Vec<String>) -> KResult<()> {
    if path.iter().any(|p| p == name) {
        return err(format!("circular proofs: {} -> {}", path.join(" -> "), name));
    }
    if env.fact(name).is_some() {
        return Ok(());
    }
    if let Some((_, s)) = env.open.conditional.iter().find(|(n, _)| n == name) {
        path.push(name.to_string());
        for d in s.open() {
            remaining_from(env, d, path, out)?;
        }
        path.pop();
        return Ok(());
    }
    if !out.iter().any(|o| o == name) {
        out.push(name.to_string());
    }
    Ok(())
}
