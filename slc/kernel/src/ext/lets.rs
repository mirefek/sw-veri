//! Equality up to lets: two terms that are the same once their lets
//! (`letin(a, x. f) := f(a)`, the prelude's) are reduced, compared node by
//! node and a let reduced only where the two differ -- the local expansion
//! a matching needs, not every let's (a let-bound value used many times
//! would be copied into each use: a run of lets doubles the term per let).
//!
//! Soundness: `let_eq(a, b)` implies `unfold_all(a, [letin]) ==
//! unfold_all(b, [letin])`, what `Seq::conv` with `letin` accepts: equal
//! arguments under the same head stay equal unfolded, and a reduced let is
//! its unfolding at that node (its body with its variable the value, the
//! body's other bound variables lowered past it), the rest unfolded after.

use std::collections::HashMap;

use crate::env::{Env, SymKind};
use crate::term::{Node, SymId, Term};

/// The prelude's `letin(a, x. f) := f(a)`, if `letin` is defined so.
pub fn letin_sym(env: &Env) -> Option<SymId> {
    let s = *env.sym_by_name.get("letin")?;
    let info = &env.syms[s as usize];
    if info.binders != [0, 1] {
        return None;
    }
    match &info.kind {
        SymKind::Defined { params, body } if params.len() == 2 => match body.node() {
            Node::Var(f, a) if *f == params[1] && a.len() == 1 && matches!(a[0].node(), Node::Var(x, b) if *x == params[0] && b.is_empty()) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

/// `body` (a let's, its variable `BVar(0)`) with its variable the value `v`
/// (in the let's context) and its other bound variables lowered by one:
/// the let reduced. Parts without the variable are kept as they are.
pub fn beta(env: &Env, body: &Term, v: &Term) -> Term {
    // (v's bound variables of the context, from `cut` on, moved under d
    // binders; its closed parts kept)
    fn shift(env: &Env, t: &Term, d: u32, cut: u32, memo: &mut HashMap<(usize, u32, u32), Term>) -> Term {
        if d == 0 || env.loose_depth_m(t) <= cut {
            return t.clone();
        }
        let key = (t.ptr_id(), d, cut);
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let r = match t.node() {
            Node::BVar(j) => Term::bvar(j + d).with_label(t.label().map(Into::into)),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| shift(env, x, d, cut, memo)).collect()),
            Node::App(s, a) => {
                let bs = &env.syms[*s as usize].binders;
                t.with_args(a.iter().enumerate().map(|(i, x)| shift(env, x, d, cut + bs[i], memo)).collect())
            }
            _ => t.clone(),
        };
        memo.insert(key, r.clone());
        r
    }
    fn go(env: &Env, t: &Term, v: &Term, dep: u32, memo: &mut HashMap<(usize, u32), Term>, sm: &mut HashMap<(usize, u32, u32), Term>) -> Term {
        if env.loose_depth_m(t) <= dep {
            return t.clone();
        }
        let key = (t.ptr_id(), dep);
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let r = match t.node() {
            Node::BVar(j) if *j == dep => shift(env, v, dep, 0, sm),
            Node::BVar(j) if *j > dep => Term::bvar(j - 1),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| go(env, x, v, dep, memo, sm)).collect()),
            Node::App(s, a) => {
                let bs = &env.syms[*s as usize].binders;
                t.with_args(a.iter().enumerate().map(|(i, x)| go(env, x, v, dep + bs[i], memo, sm)).collect())
            }
            _ => t.clone(),
        };
        memo.insert(key, r.clone());
        r
    }
    go(env, body, v, 0, &mut HashMap::new(), &mut HashMap::new())
}

/// Equality up to lets (see the module docs).
pub struct LetEq<'a> {
    env: &'a Env,
    letin: SymId,
    memo: HashMap<(Term, Term), bool>,
}

impl<'a> LetEq<'a> {
    pub fn new(env: &'a Env, letin: SymId) -> Self {
        LetEq { env, letin, memo: HashMap::new() }
    }

    /// a and b the same up to lets
    pub fn eq(&mut self, a: &Term, b: &Term) -> bool {
        if a == b {
            return true;
        }
        let key = (a.clone(), b.clone());
        if let Some(r) = self.memo.get(&key) {
            return *r;
        }
        let r = self.eq_(a, b);
        self.memo.insert(key, r);
        r
    }

    fn eq_(&mut self, a: &Term, b: &Term) -> bool {
        // (the same head: the arguments, each up to lets)
        match (a.node(), b.node()) {
            (Node::App(s, x), Node::App(t, y)) if s == t && x.len() == y.len() => {
                if x.iter().zip(y.iter()).all(|(p, q)| self.eq(p, q)) {
                    return true;
                }
            }
            (Node::Var(s, x), Node::Var(t, y)) if s == t && x.len() == y.len() => {
                return x.iter().zip(y.iter()).all(|(p, q)| self.eq(p, q));
            }
            _ => {}
        }
        // (else a let at either side reduced there)
        if let Some(r) = self.reduce(a) {
            return self.eq(&r, b);
        }
        if let Some(r) = self.reduce(b) {
            return self.eq(a, &r);
        }
        false
    }

    fn reduce(&self, t: &Term) -> Option<Term> {
        match t.node() {
            Node::App(s, x) if *s == self.letin && x.len() == 2 => Some(beta(self.env, &x[1], &x[0])),
            _ => None,
        }
    }
}
