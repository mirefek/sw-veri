//! Pinned meanings: the symbols and theorems the trusted extensions rely
//! on by name.
//!
//! Trusted. An extension that reads a symbol by its name (`int_add`,
//! `pair`, `x86_64_linux.store_le`, ..) applies that symbol's intended
//! meaning, so the name must denote it:
//!
//! * the prelude's symbols, only from the canonical prelude: the first
//!   file with axioms counts as the prelude only when its text is
//!   core/prelude.core's (embedded here), and `Env::ksym` resolves a name
//!   to a prelude symbol only then;
//! * a few layer definitions (`PINNED_DEFS`): such a definition is
//!   accepted only with exactly the body here (`check_def`, at `define`),
//!   and only then `Env::ksym` resolves it;
//! * the library theorems simp relies on (`PINNED_THMS`): their statements
//!   (as printed) must be these (`thm_ok`).

use crate::env::{Env, KResult, KernelError};
use crate::term::{Term, VarId};

/// core/prelude.core, the canonical prelude
pub(crate) const PRELUDE: &str = include_str!("../../../../core/prelude.core");

/// (name, parameter names, body): the definitions the extensions read
pub(crate) const PINNED_DEFS: &[(&str, &[&str], &str)] = &[
    (
        "x86_64_linux.store_le",
        &["b", "a", "n", "v"],
        "fn_build(bits(64), x0. ite(int_lt(bits_sub(64, x0, a), n), bits_of_int(8, int_div(v, int_pow(256, bits_sub(64, x0, a)))), app(b, x0)))",
    ),
    (
        "x86_64_linux.le",
        &["b", "a", "n"],
        "bits_of_int(int_mul(8, n), int_sum(0, n, x0. int_mul(app(b, bits_add(64, a, bits_of_int(64, x0))), int_pow(256, x0))))",
    ),
    (
        "gimple.bytes_at",
        &["vm", "a", "n"],
        "int_sum(0, n, x0. int_mul(app(app(vm, \"bytes\"), bits_add(64, a, bits_of_int(64, x0))), int_pow(256, x0)))",
    ),
    (
        "x86.apart",
        &["a", "n", "b", "m"],
        "all i j. i in omega -> int_lt(i, n) -> j in omega -> int_lt(j, m) -> !(bits_add(64, a, bits_of_int(64, i)) = bits_add(64, b, bits_of_int(64, j)))",
    ),
];

/// (name, statement as printed): the theorems simp relies on
pub(crate) const PINNED_THMS: &[(&str, &str)] = &[
    (
        "while_unroll",
        "while_rel(l0, x0. c(x0), x0 x1. b(x0, x1), x0. tr(x0), r) -> ((!c(l0) && r = ok(l0, empty)) || ((c(l0) && b(l0, r)) && !is_ok(r))) || (c(l0) && (ex x0. b(l0, ok(x0, empty)) && (ex x1. (while_rel(x0, x2. c(x2), x2 x3. b(x2, x3), x2. tr(x2), x1) && fst(x1) = fst(r)) && (!(fst(r) = 2) -> x1 = r))))",
    ),
    ("while_stop", "!c(l0) -> while_rel(l0, x0. c(x0), x0 x1. b(x0, x1), x0. tr(x0), ok(l0, empty))"),
    ("while_leave", "c(l0) -> b(l0, r) -> !is_ok(r) -> while_rel(l0, x0. c(x0), x0 x1. b(x0, x1), x0. tr(x0), r)"),
    (
        "while_step",
        "c(l0) -> b(l0, ok(l1, empty)) -> while_rel(l1, x0. c(x0), x0 x1. b(x0, x1), x0. tr(x0), r) -> !(fst(r) = 2) -> while_rel(l0, x0. c(x0), x0 x1. b(x0, x1), x0. tr(x0), r)",
    ),
];

/// A definition of a pinned name: only with its pinned body (checked
/// before it is added). Ok(true): pinned; Ok(false): not a pinned name, or
/// no canonical prelude (the extensions then never read it).
pub(crate) fn check_def(env: &mut Env, name: &str, params: &[VarId], body: &Term) -> KResult<bool> {
    let Some((_, names, text)) = PINNED_DEFS.iter().find(|(n, _, _)| *n == name) else { return Ok(false) };
    if env.prelude_end.is_none() {
        return Ok(false);
    }
    if names.len() != params.len() {
        return Err(KernelError(format!("`{}`: the extensions rely on its definition with {} parameters", name, names.len())));
    }
    let scope: Vec<(String, VarId)> = names.iter().map(|n| n.to_string()).zip(params.iter().copied()).collect();
    let reference = crate::syntax::parse_term(env, text, &scope)?;
    if &reference != body {
        return Err(KernelError(format!("`{}`: the extensions rely on its definition `{}`; this one differs", name, text)));
    }
    Ok(true)
}

/// The theorem or open lemma `name` states its pinned statement (or is no
/// pinned name).
pub(crate) fn thm_ok(env: &Env, name: &str) -> bool {
    let Some((_, want)) = PINNED_THMS.iter().find(|(n, _)| *n == name) else { return true };
    let stmt = env.theorems.iter().find(|(n, _)| n == name).map(|(_, t)| t.prop().clone()).or_else(|| env.open.lemmas.iter().find(|(n, _)| n == name).map(|(_, t)| t.clone()));
    stmt.is_some_and(|s| crate::syntax::Printer::new(env).term(&s) == *want)
}
