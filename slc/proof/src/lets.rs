//! Lets in proofs: `zeta` (a let's variable replaced by its value at the
//! chosen occurrences, the let dropped when none is left) and `fold_let`
//! (the value back to the variable, or a new let around a statement).
//!
//! Not trusted: the new statement is computed here, the step is
//! `Seq::conv_lets` (the two the same up to lets).
//!
//! A let is named by the name written at it (`letin(a, x. ..)`), else by
//! the one it is printed with (`x3`: `x` and the number of variables bound
//! around it); the first let so named, outer before inner, left to right.

use std::collections::{HashMap, HashSet};

use sl_kernel::ext::lets::{beta, letin_sym};
use sl_kernel::{Env, KResult, KernelError, Node, Term};

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

/// whether the let `t` (at `depth` bound variables) is named `name`
fn named(t: &Term, depth: u32, name: &str) -> bool {
    let written = t.binder_name().and_then(|n| n.split(' ').next()).filter(|n| !n.is_empty());
    written == Some(name) || name == format!("x{}", depth)
}

/// `t` with the first let named `name` replaced by `f(let, depth)`; None
/// if there is none
fn at_let(env: &Env, l: sl_kernel::SymId, t: &Term, name: &str, depth: u32, none: &mut HashSet<(usize, u32)>, f: &mut dyn FnMut(&Term, u32) -> KResult<Term>) -> KResult<Option<Term>> {
    let Node::App(s, a) = t.node() else {
        if let Node::Var(_, a) = t.node() {
            for (i, x) in a.iter().enumerate() {
                if let Some(y) = at_let(env, l, x, name, depth, none, f)? {
                    let mut b = a.to_vec();
                    b[i] = y;
                    return Ok(Some(t.with_args(b)));
                }
            }
        }
        return Ok(None);
    };
    if *s == l && a.len() == 2 && named(t, depth, name) {
        return f(t, depth).map(Some);
    }
    if a.is_empty() || none.contains(&(t.ptr_id(), depth)) {
        return Ok(None);
    }
    let bs = env.syms[*s as usize].binders.clone();
    for (i, x) in a.iter().enumerate() {
        if let Some(y) = at_let(env, l, x, name, depth + bs[i], none, f)? {
            let mut b = a.to_vec();
            b[i] = y;
            return Ok(Some(t.with_args(b)));
        }
    }
    none.insert((t.ptr_id(), depth));
    Ok(None)
}

/// `t` with the occurrences of the bound variable `BVar(e)` (e the depth
/// inside the let's body, counted in `n` from 1) replaced, where `occ`
/// chooses them (all if empty), by `val(e)`
fn subst_occ(env: &Env, t: &Term, e: u32, occ: &[usize], n: &mut usize, val: &mut dyn FnMut(u32) -> Term) -> Term {
    if env.loose_depth_m(t) <= e {
        return t.clone();
    }
    match t.node() {
        Node::BVar(j) if *j == e => {
            *n += 1;
            if occ.is_empty() || occ.contains(n) {
                val(e)
            } else {
                t.clone()
            }
        }
        Node::Var(_, a) => t.with_args(a.iter().map(|x| subst_occ(env, x, e, occ, n, val)).collect()),
        Node::App(s, a) => {
            let bs = env.syms[*s as usize].binders.clone();
            t.with_args(a.iter().enumerate().map(|(i, x)| subst_occ(env, x, e + bs[i], occ, n, val)).collect())
        }
        _ => t.clone(),
    }
}

/// `t` with the occurrences of `pat(e)` (at depth e, counted in `n`)
/// chosen by `occ` (all if empty) replaced by `BVar(e)`
fn abstract_occ(env: &Env, t: &Term, e: u32, occ: &[usize], n: &mut usize, pat: &mut dyn FnMut(u32) -> Term) -> Term {
    if *t == pat(e) {
        *n += 1;
        return if occ.is_empty() || occ.contains(n) { Term::bvar(e) } else { t.clone() };
    }
    match t.node() {
        Node::Var(_, a) => t.with_args(a.iter().map(|x| abstract_occ(env, x, e, occ, n, pat)).collect()),
        Node::App(s, a) => {
            let bs = env.syms[*s as usize].binders.clone();
            t.with_args(a.iter().enumerate().map(|(i, x)| abstract_occ(env, x, e + bs[i], occ, n, pat)).collect())
        }
        _ => t.clone(),
    }
}

/// `v` (a let's value, at the let) moved under `k` binders
fn shifted(env: &Env, v: &Term, k: u32, memo: &mut HashMap<u32, Term>) -> Term {
    if env.loose_depth_m(v) == 0 {
        return v.clone();
    }
    memo.entry(k).or_insert_with(|| v.shift(k, 0, &env.binders_fn())).clone()
}

fn check_occ(occ: &[usize], n: usize, what: &str) -> KResult<()> {
    match occ.iter().find(|k| **k == 0 || **k > n) {
        Some(k) => err(format!("no occurrence {} of {} ({} in all)", k, what, n)),
        None => Ok(()),
    }
}

fn letin(env: &Env) -> KResult<sl_kernel::SymId> {
    letin_sym(env).ok_or_else(|| KernelError("`letin` is not the prelude's `letin(a, x. f) := f(a)`".into()))
}

/// `t` with the let `name`'s variable replaced by its value at the
/// occurrences `occ` (numbered from 1 in its body; all if empty), the let
/// dropped when none is left
pub fn zeta(env: &Env, t: &Term, name: &str, occ: &[usize]) -> KResult<Term> {
    let l = letin(env)?;
    let mut f = |lt: &Term, _d: u32| -> KResult<Term> {
        let Node::App(_, a) = lt.node() else { unreachable!() };
        let (v, b) = (&a[0], &a[1]);
        let mut memo = HashMap::new();
        let mut n = 0;
        // (inside the body, at depth e: under the let's binder and e more)
        let b2 = subst_occ(env, b, 0, occ, &mut n, &mut |e| shifted(env, v, e + 1, &mut memo));
        check_occ(occ, n, &format!("the let `{}`'s variable", name))?;
        // (none left: the let reduced)
        let left = n - if occ.is_empty() { n } else { occ.len() };
        Ok(if left == 0 { beta(env, b, v) } else { lt.with_args(vec![v.clone(), b2]) })
    };
    at_let(env, l, t, name, 0, &mut HashSet::new(), &mut f)?.ok_or_else(|| KernelError(format!("zeta: no let `{}`", name)))
}

/// `t` with the let `name`'s value back to its variable at the occurrences
/// `occ` of the value in its body (all if empty); or, if there is no let
/// so named and `val` is given, `t` as the let `letin(val, name. t')`, the
/// occurrences of val in t its variable
pub fn fold_let(env: &Env, t: &Term, name: &str, val: Option<&Term>, occ: &[usize]) -> KResult<Term> {
    let l = letin(env)?;
    let mut f = |lt: &Term, _d: u32| -> KResult<Term> {
        let Node::App(_, a) = lt.node() else { unreachable!() };
        let (v, b) = (&a[0], &a[1]);
        let mut memo = HashMap::new();
        let mut n = 0;
        let b2 = abstract_occ(env, b, 0, occ, &mut n, &mut |e| shifted(env, v, e + 1, &mut memo));
        check_occ(occ, n, &format!("the let `{}`'s value", name))?;
        if n == 0 {
            return err(format!("fold_let: the let `{}`'s value does not occur in its body", name));
        }
        Ok(lt.with_args(vec![v.clone(), b2]))
    };
    if let Some(r) = at_let(env, l, t, name, 0, &mut HashSet::new(), &mut f)? {
        if val.is_some() {
            return err(format!("fold_let: a let `{}` is there already (its value is folded; no value to give)", name));
        }
        return Ok(r);
    }
    let Some(val) = val else { return err(format!("fold_let: no let `{}` (give a value `{{t}}` for a new one)", name)) };
    if env.loose_depth_m(val) > 0 || env.loose_depth_m(t) > 0 {
        return err("fold_let: the value and the statement must be closed");
    }
    let mut n = 0;
    let body = abstract_occ(env, t, 0, occ, &mut n, &mut |_| val.clone());
    check_occ(occ, n, "the value")?;
    if n == 0 {
        return err(format!("fold_let: `{}` does not occur", sl_kernel::syntax::Printer::new(env).short(val)));
    }
    Ok(Term::app(l, vec![val.clone(), body]).with_binder_name(Some(name.into())))
}

/// whether `t` has a let (its shared parts looked at once)
pub fn mentions_let(env: &Env, t: &Term) -> bool {
    fn go(t: &Term, l: sl_kernel::SymId, seen: &mut HashSet<usize>) -> bool {
        match t.node() {
            Node::App(s, _) if *s == l => true,
            Node::App(_, a) | Node::Var(_, a) => !a.is_empty() && seen.insert(t.ptr_id()) && a.iter().any(|x| go(x, l, seen)),
            _ => false,
        }
    }
    letin_sym(env).is_some_and(|l| go(t, l, &mut HashSet::new()))
}

/// whether `t` has a let named `name`
pub fn has_let(env: &Env, t: &Term, name: &str) -> bool {
    let Some(l) = letin_sym(env) else { return false };
    matches!(at_let(env, l, t, name, 0, &mut HashSet::new(), &mut |lt, _| Ok(lt.clone())), Ok(Some(_)))
}

/// `s` as a proof of `goal`, the two the same up to lets (a let reduced
/// only where they differ), if they are and one has a let
pub fn conv_try(env: &Env, s: &sl_kernel::ext::Seq, goal: &Term) -> Option<sl_kernel::ext::Seq> {
    if !mentions_let(env, s.concl()) && !mentions_let(env, goal) {
        return None;
    }
    sl_kernel::ext::Seq::conv_lets(env, s, goal).ok()
}
