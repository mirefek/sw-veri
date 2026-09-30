//! A simplifier for elaborated programs and propositions: symbolic
//! execution of `runs(P, s, o)`.
//!
//! Trusted extension. It rewrites with a fixed set of rules, each a theorem
//! of the prelude:
//!
//! Equations (used anywhere):
//! * `letin(a, x. f(x)) = f(a)` (definition);
//! * `fst(pair(a, b)) = a`, `snd(pair(a, b)) = b` (pair injectivity), and
//!   for the outcome constructors `ok(s, v) = pair(0, pair(s, v))`,
//!   `exc(s, e) = pair(1, pair(s, e))`, `diverge(t) = pair(2, t)`: their
//!   `fst`, `snd`, `out_state`, `out_value`;
//! * `app(fn_update(f, k, v), k) = v`; `app(fn_update(f, k, v), k2) =
//!   app(f, k2)` for distinct literals k, k2 (`fn_update` keeps the other
//!   pairs);
//! * `ite(c, a, b)` is `a` if c simplifies to `true`, `b` if to `false`.
//!
//! Equivalences (used in proposition positions: under connectives,
//! quantifier bodies, `ite` conditions):
//! * the connectives with `true`/`false` operands (classical logic, any
//!   operands: `true -> a` is interderivable with a);
//! * `a = a` is true; distinct numeric or string literals are unequal
//!   (numerals by `lit_*`, strings by `bytes_len`/`bytes_at`);
//! * `pair(a, b) = pair(c, d) <-> a = c && b = d`, likewise for `ok`,
//!   `exc`, `diverge`; outcomes built with different constructors differ;
//! * `ex x. .. && x = t && ..` <-> the rest with `t` for x (x not in t),
//!   `all x. x = t -> P(x)` <-> `P(t)`; `ex x. P` <-> P when x does not
//!   occur (the universe is not empty);
//! * the definitions of `bind_rel`, `any_rel`, `is_ok`, `ne`.
//!
//! One implication, used only where weakening is sound (positive positions
//! of a fact being simplified, never in a goal):
//! * `runs(mkprog(s o. R), S, O) -> R(S, O)` (membership in `mkprog`; the
//!   converse also needs `pair(S, O) in univ(1)`).

use super::prop::Logic;
use crate::env::{Env, SymKind};
use crate::term::{Node, SymId, Term};

#[derive(Clone, Copy, PartialEq)]
enum Pol {
    /// a positive position of a fact: weakening allowed
    Pos,
    /// negative, or both (a goal, an `iff`): equivalences only
    Other,
}

impl Pol {
    fn flip(self) -> Pol {
        Pol::Other
    }
}

struct Syms {
    eq: SymId,
    imp: SymId,
    false_: SymId,
    true_: Option<SymId>,
    not: Option<SymId>,
    and: Option<SymId>,
    or: Option<SymId>,
    ne: Option<SymId>,
    ex: SymId,
    all: SymId,
    unfold: Vec<SymId>,
    letin: Option<SymId>,
    pair: Option<SymId>,
    fst: Option<SymId>,
    snd: Option<SymId>,
    ok: Option<SymId>,
    exc: Option<SymId>,
    diverge: Option<SymId>,
    out_state: Option<SymId>,
    out_value: Option<SymId>,
    app: Option<SymId>,
    fn_update: Option<SymId>,
    ite: Option<SymId>,
    runs: Option<SymId>,
    mkprog: Option<SymId>,
}

fn is(s: SymId, o: Option<SymId>) -> bool {
    o == Some(s)
}

struct Simp<'a> {
    env: &'a Env,
    s: Syms,
}

impl<'a> Simp<'a> {
    fn new(env: &'a Env, lg: &Logic) -> Simp<'a> {
        let g = |n: &str| env.sym_by_name.get(n).copied();
        let unfold = ["bind_rel", "any_rel", "is_ok"].iter().filter_map(|n| g(n)).collect();
        Simp {
            env,
            s: Syms {
                eq: env.builtins.eq,
                imp: env.builtins.imp,
                false_: lg.false_,
                true_: g("true"),
                not: g("not"),
                and: g("and"),
                or: g("or"),
                ne: g("ne"),
                ex: lg.ex,
                all: lg.all,
                unfold,
                letin: g("letin"),
                pair: g("pair"),
                fst: g("fst"),
                snd: g("snd"),
                ok: g("ok"),
                exc: g("exc"),
                diverge: g("diverge"),
                out_state: g("out_state"),
                out_value: g("out_value"),
                app: g("app"),
                fn_update: g("fn_update"),
                ite: g("ite"),
                runs: g("runs"),
                mkprog: g("mkprog"),
            },
        }
    }

    fn tt(&self) -> Term {
        Term::app(self.s.true_.expect("true"), vec![])
    }
    fn ff(&self) -> Term {
        Term::app(self.s.false_, vec![])
    }
    fn is_true(&self, t: &Term) -> bool {
        matches!(t.node(), Node::App(f, a) if a.is_empty() && is(*f, self.s.true_))
    }
    fn is_false(&self, t: &Term) -> bool {
        matches!(t.node(), Node::App(f, a) if a.is_empty() && *f == self.s.false_)
    }
    fn app2(&self, f: Option<SymId>, a: Term, b: Term) -> Term {
        Term::app(f.expect("prelude symbol"), vec![a, b])
    }

    /// Unfolds a defined symbol once (its parameters substituted).
    fn unfold(&self, s: SymId, args: &[Term]) -> Option<Term> {
        let SymKind::Defined { params, body } = &self.env.syms[s as usize].kind else { return None };
        let mut t = body.clone();
        for (p, a) in params.iter().zip(args) {
            let k = self.env.vars[*p as usize].arity;
            t = subst_var_ctx(self.env, &t, *p, a, k);
        }
        Some(t)
    }

    // ------------------------------------------------------------------
    //  Terms (equations only)

    fn term(&self, t: &Term) -> Term {
        let s = &self.s;
        let Node::App(f, a) = t.node() else { return t.clone() };
        let f = *f;
        // `letin(a, x. body)`: β
        if is(f, s.letin) {
            let v = self.term(&a[0]);
            return self.term(&inst_k(self.env, &a[1], &[v]));
        }
        if is(f, s.ite) {
            let c = self.prop(&a[0], Pol::Other);
            if self.is_true(&c) {
                return self.term(&a[1]);
            }
            if self.is_false(&c) {
                return self.term(&a[2]);
            }
            return Term::app(f, vec![c, self.term(&a[1]), self.term(&a[2])]);
        }
        let args: Vec<Term> = a.iter().map(|x| self.term(x)).collect();
        let head = |x: &Term| match x.node() {
            Node::App(g, b) => Some((*g, b.clone())),
            _ => None,
        };
        let nat = |n: u64| Term::nat(crate::nat::Nat::from_u64(n));
        if is(f, s.fst) || is(f, s.snd) || is(f, s.out_state) || is(f, s.out_value) {
            if let Some((g, b)) = head(&args[0]) {
                let fst = is(f, s.fst);
                let snd = is(f, s.snd);
                if is(g, s.pair) {
                    if fst {
                        return b[0].clone();
                    }
                    if snd {
                        return b[1].clone();
                    }
                }
                let tag = if is(g, s.ok) { Some(0) } else if is(g, s.exc) { Some(1) } else if is(g, s.diverge) { Some(2) } else { None };
                if let Some(k) = tag {
                    if fst {
                        return nat(k);
                    }
                    if snd {
                        return if k == 2 { b[0].clone() } else { self.app2(s.pair, b[0].clone(), b[1].clone()) };
                    }
                    if k < 2 {
                        return if is(f, s.out_state) { b[0].clone() } else { b[1].clone() };
                    }
                }
            }
        }
        if is(f, s.app) {
            let mut m = args[0].clone();
            loop {
                match head(&m) {
                    Some((g, b)) if is(g, s.fn_update) => {
                        if b[1] == args[1] {
                            return b[2].clone();
                        }
                        if distinct_literals(&b[1], &args[1]) {
                            m = b[0].clone();
                            continue;
                        }
                    }
                    _ => {}
                }
                break;
            }
            return Term::app(f, vec![m, args[1].clone()]);
        }
        Term::app(f, args)
    }

    // ------------------------------------------------------------------
    //  Propositions (equivalences; runs-elimination in positive positions)

    fn and(&self, a: Term, b: Term) -> Term {
        if self.is_false(&a) || self.is_false(&b) {
            return self.ff();
        }
        if self.is_true(&a) {
            return b;
        }
        if self.is_true(&b) {
            return a;
        }
        self.app2(self.s.and, a, b)
    }
    fn or(&self, a: Term, b: Term) -> Term {
        if self.is_true(&a) || self.is_true(&b) {
            return self.tt();
        }
        if self.is_false(&a) {
            return b;
        }
        if self.is_false(&b) {
            return a;
        }
        self.app2(self.s.or, a, b)
    }
    fn not(&self, a: Term) -> Term {
        if self.is_true(&a) {
            return self.ff();
        }
        if self.is_false(&a) {
            return self.tt();
        }
        if let Node::App(n, b) = a.node() {
            if is(*n, self.s.not) {
                return b[0].clone();
            }
        }
        Term::app(self.s.not.expect("not"), vec![a])
    }

    fn prop(&self, t: &Term, pol: Pol) -> Term {
        let s = &self.s;
        let Node::App(f, a) = t.node() else { return t.clone() };
        let f = *f;
        if f == s.imp {
            let x = self.prop(&a[0], pol.flip());
            let y = self.prop(&a[1], pol);
            if self.is_false(&x) || self.is_true(&y) {
                return self.tt();
            }
            if self.is_true(&x) {
                return y;
            }
            if self.is_false(&y) {
                return self.not(x);
            }
            return Term::app(f, vec![x, y]);
        }
        if is(f, s.not) {
            return self.not(self.prop(&a[0], pol.flip()));
        }
        if is(f, s.and) {
            return self.and(self.prop(&a[0], pol), self.prop(&a[1], pol));
        }
        if is(f, s.or) {
            return self.or(self.prop(&a[0], pol), self.prop(&a[1], pol));
        }
        if is(f, s.ne) {
            return self.not(self.eq(&a[0], &a[1]));
        }
        if f == s.eq {
            return self.eq(&a[0], &a[1]);
        }
        if f == s.ex {
            return self.ex(&self.prop(&a[0], pol));
        }
        if f == s.all {
            return self.all(&self.prop(&a[0], pol));
        }
        if is(f, s.letin) {
            let v = self.term(&a[0]);
            return self.prop(&inst_k(self.env, &a[1], &[v]), pol);
        }
        if s.unfold.contains(&f) {
            if let Some(u) = self.unfold(f, a) {
                return self.prop(&u, pol);
            }
        }
        if is(f, s.runs) && pol == Pol::Pos {
            let mut p = self.term(&a[0]);
            // a procedure: its definition is a `mkprog`
            if let Node::App(g, ga) = p.node() {
                if !is(*g, s.mkprog) {
                    if let Some(u) = self.unfold(*g, ga) {
                        if matches!(u.node(), Node::App(m, _) if is(*m, s.mkprog)) {
                            p = u;
                        }
                    }
                }
            }
            if let Node::App(m, r) = p.node() {
                if is(*m, s.mkprog) {
                    let (st, o) = (self.term(&a[1]), self.term(&a[2]));
                    return self.prop(&inst_k(self.env, &r[0], &[st, o]), pol);
                }
            }
            return Term::app(f, vec![p, self.term(&a[1]), self.term(&a[2])]);
        }
        // an atom: its arguments as terms
        self.term(t)
    }

    fn eq(&self, a: &Term, b: &Term) -> Term {
        let s = &self.s;
        let (x, y) = (self.term(a), self.term(b));
        if x == y {
            return self.tt();
        }
        if distinct_literals(&x, &y) {
            return self.ff();
        }
        // constructors: injective and distinct
        let ctor = |t: &Term| -> Option<(u8, Vec<Term>)> {
            match t.node() {
                Node::App(g, b) if is(*g, s.pair) => Some((10, b.to_vec())),
                Node::App(g, b) if is(*g, s.ok) => Some((0, b.to_vec())),
                Node::App(g, b) if is(*g, s.exc) => Some((1, b.to_vec())),
                Node::App(g, b) if is(*g, s.diverge) => Some((2, b.to_vec())),
                _ => None,
            }
        };
        if let (Some((k1, a1)), Some((k2, a2))) = (ctor(&x), ctor(&y)) {
            if k1 < 10 && k2 < 10 && k1 != k2 {
                return self.ff();
            }
            if k1 == k2 && a1.len() == a2.len() {
                let mut r = self.tt();
                for (p, q) in a1.iter().zip(&a2) {
                    r = self.and(r, self.eq(p, q));
                }
                return r;
            }
        }
        Term::app(s.eq, vec![x, y])
    }

    /// `ex x. body` (body under one binder)
    fn ex(&self, body: &Term) -> Term {
        if self.is_false(body) {
            return self.ff();
        }
        if !has_bvar(self.env, body, 0) {
            return lower(self.env, body, 0);
        }
        // one-point: a conjunct `x = t` or `t = x`
        let mut cs = Vec::new();
        self.conjuncts(body, &mut cs);
        for (i, c) in cs.iter().enumerate() {
            if let Node::App(e, ab) = c.node() {
                if *e == self.s.eq {
                    for (v, t) in [(&ab[0], &ab[1]), (&ab[1], &ab[0])] {
                        if matches!(v.node(), Node::BVar(0)) && !has_bvar(self.env, t, 0) {
                            let mut rest = self.tt();
                            for (j, d) in cs.iter().enumerate() {
                                if j != i {
                                    rest = self.and(rest, d.clone());
                                }
                            }
                            let tl = lower(self.env, t, 0);
                            let r = inst_k(self.env, &rest, &[tl]);
                            return self.prop(&r, Pol::Other);
                        }
                    }
                }
            }
        }
        // distribute over a disjunction, so each branch can use one-point
        if let Node::App(o, ab) = body.node() {
            if is(*o, self.s.or) {
                return self.or(self.ex(&ab[0]), self.ex(&ab[1]));
            }
        }
        Term::app(self.s.ex, vec![body.clone()])
    }

    /// `all x. body`
    fn all(&self, body: &Term) -> Term {
        if self.is_true(body) {
            return self.tt();
        }
        if !has_bvar(self.env, body, 0) {
            return lower(self.env, body, 0);
        }
        if let Node::App(i, ab) = body.node() {
            if *i == self.s.imp {
                if let Node::App(e, xy) = ab[0].node() {
                    if *e == self.s.eq {
                        for (v, t) in [(&xy[0], &xy[1]), (&xy[1], &xy[0])] {
                            if matches!(v.node(), Node::BVar(0)) && !has_bvar(self.env, t, 0) {
                                let tl = lower(self.env, t, 0);
                                let r = inst_k(self.env, &ab[1], &[tl]);
                                return self.prop(&r, Pol::Other);
                            }
                        }
                    }
                }
            }
        }
        Term::app(self.s.all, vec![body.clone()])
    }

    fn conjuncts(&self, t: &Term, out: &mut Vec<Term>) {
        if let Node::App(a, b) = t.node() {
            if is(*a, self.s.and) {
                self.conjuncts(&b[0], out);
                self.conjuncts(&b[1], out);
                return;
            }
        }
        out.push(t.clone());
    }
}

/// `body` with its k parameters (`BVar(k-1-i)` = parameter i at the top)
/// replaced by `args`, where body may also refer to enclosing binders
/// (`BVar(>= k)`) and args live in that enclosing context.
fn inst_k(env: &Env, body: &Term, args: &[Term]) -> Term {
    fn go(env: &Env, t: &Term, args: &[Term], dep: u32) -> Term {
        let k = args.len() as u32;
        match t.node() {
            Node::BVar(j) if *j < dep => t.clone(),
            Node::BVar(j) if j - dep < k => args[(k - 1 - (j - dep)) as usize].shift(dep, 0, &env.binders_fn()),
            Node::BVar(j) => Term::bvar(j - k),
            Node::Nat(_) | Node::Bytes(_) => t.clone(),
            Node::Var(v, a) => Term::var(*v, a.iter().map(|x| go(env, x, args, dep)).collect()),
            Node::App(s, a) => Term::app(*s, a.iter().enumerate().map(|(i, x)| go(env, x, args, dep + env.binders_fn()(*s, i))).collect()),
        }
    }
    go(env, body, args, 0)
}

/// `t` (closed but for schematic variables, like a definition's body) with
/// variable v of arity k replaced by `value` (k parameters, possibly
/// referring to enclosing binders of the site).
fn subst_var_ctx(env: &Env, t: &Term, v: crate::term::VarId, value: &Term, k: u32) -> Term {
    fn go(env: &Env, t: &Term, v: crate::term::VarId, value: &Term, k: u32, dep: u32) -> Term {
        match t.node() {
            Node::Var(w, a) => {
                let a: Vec<Term> = a.iter().map(|x| go(env, x, v, value, k, dep)).collect();
                if *w == v {
                    // the value's references to the enclosing context move
                    // under the `dep` binders passed on the way
                    let val = value.shift(dep, k, &env.binders_fn());
                    inst_k(env, &val, &a)
                } else {
                    Term::var(*w, a)
                }
            }
            Node::App(s, a) => Term::app(*s, a.iter().enumerate().map(|(i, x)| go(env, x, v, value, k, dep + env.binders_fn()(*s, i))).collect()),
            _ => t.clone(),
        }
    }
    go(env, t, v, value, k, 0)
}

/// Two literals that denote different sets (numerals, or byte strings).
fn distinct_literals(a: &Term, b: &Term) -> bool {
    match (a.node(), b.node()) {
        (Node::Nat(x), Node::Nat(y)) => x != y,
        (Node::Bytes(x), Node::Bytes(y)) => x != y,
        _ => false,
    }
}

/// Does bound variable `i` (relative to the top) occur in t?
fn has_bvar(env: &Env, t: &Term, i: u32) -> bool {
    match t.node() {
        Node::BVar(j) => *j == i,
        Node::Nat(_) | Node::Bytes(_) => false,
        Node::Var(_, a) => a.iter().any(|x| has_bvar(env, x, i)),
        Node::App(s, a) => a.iter().enumerate().any(|(k, x)| has_bvar(env, x, i + env.binders_fn()(*s, k))),
    }
}

/// t without bound variable `i` (which must not occur): the variables
/// above it move down by one.
fn lower(env: &Env, t: &Term, i: u32) -> Term {
    match t.node() {
        Node::BVar(j) if *j > i => Term::bvar(j - 1),
        Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
        Node::Var(v, a) => Term::var(*v, a.iter().map(|x| lower(env, x, i)).collect()),
        Node::App(s, a) => Term::app(*s, a.iter().enumerate().map(|(k, x)| lower(env, x, i + env.binders_fn()(*s, k))).collect()),
    }
}

// ----------------------------------------------------------------------
//  Path normal form: `P1 || P2 || ..`, each `ex xs. l1 && l2 && ..`
//  (distribution of && over ||, existentials pulled out, `x = t` solved;
//  equivalences)

/// One path: its existential variables (fresh schematic variables standing
/// for the bound ones) and its literals.
#[derive(Clone)]
struct Path {
    vars: Vec<crate::term::VarId>,
    lits: Vec<Term>,
}

const MAX_PATHS: usize = 512;

impl Simp<'_> {
    fn paths(&self, t: &Term, fresh: &mut u32) -> Option<Vec<Path>> {
        let s = &self.s;
        if self.is_true(t) {
            return Some(vec![Path { vars: vec![], lits: vec![] }]);
        }
        if self.is_false(t) {
            return Some(vec![]);
        }
        if let Node::App(f, a) = t.node() {
            if is(*f, s.or) {
                let mut x = self.paths(&a[0], fresh)?;
                x.extend(self.paths(&a[1], fresh)?);
                return (x.len() <= MAX_PATHS).then_some(x);
            }
            if is(*f, s.and) {
                let (x, y) = (self.paths(&a[0], fresh)?, self.paths(&a[1], fresh)?);
                if x.len() * y.len() > MAX_PATHS {
                    return None;
                }
                let mut out = Vec::new();
                for p in &x {
                    for q in &y {
                        let mut r = p.clone();
                        r.vars.extend(q.vars.iter().copied());
                        r.lits.extend(q.lits.iter().cloned());
                        out.push(r);
                    }
                }
                return Some(out);
            }
            if *f == s.ex {
                let v = *fresh;
                *fresh += 1;
                let body = inst_k(self.env, &a[0], &[Term::var(v, vec![])]);
                let mut ps = self.paths(&body, fresh)?;
                for p in ps.iter_mut() {
                    p.vars.push(v);
                }
                return Some(ps);
            }
        }
        Some(vec![Path { vars: vec![], lits: vec![t.clone()] }])
    }

    /// Solves `x = t` literals of a path, simplifies its literals; `None`
    /// if the path is contradictory.
    fn settle(&self, mut p: Path) -> Option<Path> {
        'again: loop {
            let mut lits = Vec::new();
            for l in &p.lits {
                let l = self.prop(l, Pol::Other);
                if self.is_false(&l) {
                    return None;
                }
                if !self.is_true(&l) {
                    let mut cs = Vec::new();
                    self.conjuncts(&l, &mut cs);
                    lits.extend(cs);
                }
            }
            p.lits = lits;
            // a literal `x = t` (or `t = x`) for a path variable x not in t
            let found = p.lits.iter().enumerate().find_map(|(i, l)| {
                let Node::App(e, ab) = l.node() else { return None };
                if *e != self.s.eq {
                    return None;
                }
                [(&ab[0], &ab[1]), (&ab[1], &ab[0])].into_iter().find_map(|(v, t)| match v.node() {
                    Node::Var(x, xa) if xa.is_empty() && p.vars.contains(x) && !has_var(t, *x) => Some((i, *x, t.clone())),
                    _ => None,
                })
            });
            if let Some((i, x, t)) = found {
                let bf = self.env.binders_fn();
                p.lits = p.lits.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, l)| l.subst_var(x, &t, &bf)).collect();
                p.vars.retain(|y| *y != x);
                continue 'again;
            }
            return Some(p);
        }
    }

    /// The path normal form of a proposition (equivalent to it).
    fn pathify(&self, t: &Term) -> Term {
        let mut fresh = self.env.vars.len() as u32 + 1_000_000;
        let Some(ps) = self.paths(t, &mut fresh) else { return t.clone() };
        let mut out = self.ff();
        for p in ps {
            let Some(p) = self.settle(p) else { continue };
            let mut body = self.tt();
            for l in &p.lits {
                body = self.and(body, l.clone());
            }
            // close the remaining variables (innermost last)
            for v in p.vars.iter().rev() {
                if has_var(&body, *v) {
                    let b = abstract_var(self.env, &body, *v, 0);
                    body = Term::app(self.s.ex, vec![b]);
                }
            }
            out = self.or(out, body);
        }
        out
    }
}

impl Simp<'_> {
    /// Some disjunct of the goal, its existentials instantiated by matching
    /// its equations against the path's literals, follows from the path.
    fn witnessed(&self, lits: &[Term], goal: &Term, fresh: &mut u32, lg: &Logic) -> bool {
        let mut ds = Vec::new();
        self.disjuncts(goal, &mut ds);
        for d in ds {
            let Some(gps) = self.paths(&d, fresh) else { continue };
            for gp in gps {
                if gp.vars.is_empty() {
                    continue;
                }
                let mut binds: Vec<(crate::term::VarId, Term)> = Vec::new();
                for gl in &gp.lits {
                    for pl in lits {
                        let mut b = binds.clone();
                        if pmatch(gl, pl, &gp.vars, &mut b) {
                            binds = b;
                        }
                    }
                }
                if !gp.vars.iter().all(|v| binds.iter().any(|(w, _)| w == v)) {
                    continue;
                }
                let bf = self.env.binders_fn();
                let inst: Vec<Term> = gp
                    .lits
                    .iter()
                    .map(|l| {
                        let mut l = l.clone();
                        for (v, t) in &binds {
                            l = l.subst_var(*v, t, &bf);
                        }
                        self.prop(&l, Pol::Other)
                    })
                    .collect();
                let mut want = self.tt();
                for l in inst {
                    want = self.and(want, l);
                }
                if lg.tautology(self.env, lits, &want).is_ok() || lg.arith(self.env, lits, &want).is_ok() {
                    return true;
                }
            }
        }
        false
    }

    fn disjuncts(&self, t: &Term, out: &mut Vec<Term>) {
        if let Node::App(o, ab) = t.node() {
            if is(*o, self.s.or) {
                self.disjuncts(&ab[0], out);
                self.disjuncts(&ab[1], out);
                return;
            }
        }
        out.push(t.clone());
    }
}

/// Matches `pat` (whose variables `pvars` are pattern variables) against
/// `t`, extending `binds`.
fn pmatch(pat: &Term, t: &Term, pvars: &[crate::term::VarId], binds: &mut Vec<(crate::term::VarId, Term)>) -> bool {
    match (pat.node(), t.node()) {
        (Node::Var(v, a), _) if a.is_empty() && pvars.contains(v) => match binds.iter().find(|(w, _)| w == v) {
            Some((_, b)) => b == t,
            None => {
                binds.push((*v, t.clone()));
                true
            }
        },
        (Node::App(f, a), Node::App(g, b)) => f == g && a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| pmatch(x, y, pvars, binds)),
        (Node::Var(v, a), Node::Var(w, b)) => v == w && a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| pmatch(x, y, pvars, binds)),
        _ => pat == t,
    }
}

fn has_var(t: &Term, v: crate::term::VarId) -> bool {
    let mut vs = Vec::new();
    t.vars(&mut vs);
    vs.contains(&v)
}

/// t with the variable v made the bound variable of a new binder around it.
fn abstract_var(env: &Env, t: &Term, v: crate::term::VarId, dep: u32) -> Term {
    match t.node() {
        Node::Var(w, a) if *w == v && a.is_empty() => Term::bvar(dep),
        Node::BVar(j) if *j >= dep => Term::bvar(j + 1),
        Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
        Node::Var(w, a) => Term::var(*w, a.iter().map(|x| abstract_var(env, x, v, dep)).collect()),
        Node::App(s, a) => Term::app(*s, a.iter().enumerate().map(|(i, x)| abstract_var(env, x, v, dep + env.binders_fn()(*s, i))).collect()),
    }
}

impl Logic {
    /// A consequence of the fact `t` (simplified; `runs` of a program
    /// replaced by its relation in positive positions; then in path normal
    /// form).
    pub fn simp_fact(&self, env: &Env, t: &Term) -> Term {
        let sp = Simp::new(env, self);
        let mut t = t.clone();
        for _ in 0..8 {
            let u = sp.pathify(&sp.prop(&t, Pol::Pos));
            if u == t {
                break;
            }
            t = u;
        }
        t
    }

    /// `premises -> goal`, path by path: the premises are simplified (as
    /// facts) and split into paths (each path's variables are arbitrary:
    /// ∃-elimination); the goal is simplified (equivalently), and each path
    /// must imply it by propositional logic or linear arithmetic, after
    /// choosing witnesses for the goal's existentials by matching its
    /// equations with the path's (∃-introduction).
    pub fn simp_prove(&self, env: &Env, premises: &[Term], goal: &Term) -> crate::env::KResult<()> {
        let sp = Simp::new(env, self);
        let mut prem = sp.tt();
        for p in premises {
            prem = sp.and(prem, self.simp_fact(env, p));
        }
        let g = self.simp_eqv(env, goal);
        let mut fresh = env.vars.len() as u32 + 2_000_000;
        let paths = sp.paths(&prem, &mut fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
        for p in paths {
            let Some(p) = sp.settle(p) else { continue };
            if self.tautology(env, &p.lits, &g).is_ok() || self.arith(env, &p.lits, &g).is_ok() {
                continue;
            }
            if sp.witnessed(&p.lits, &g, &mut fresh, self) {
                continue;
            }
            // report the path (its variables closed again)
            let mut body = sp.tt();
            for l in &p.lits {
                body = sp.and(body, l.clone());
            }
            for v in p.vars.iter().rev() {
                if has_var(&body, *v) {
                    body = Term::app(sp.s.ex, vec![abstract_var(env, &body, *v, 0)]);
                }
            }
            let pr = crate::syntax::Printer::new(env);
            return Err(crate::env::KernelError(format!("simp: left to show: {}\n  on the path: {}", pr.term(&g), pr.term(&body))));
        }
        Ok(())
    }

    /// A proposition equivalent to `t`.
    pub fn simp_eqv(&self, env: &Env, t: &Term) -> Term {
        let sp = Simp::new(env, self);
        let mut t = t.clone();
        for _ in 0..8 {
            let u = sp.prop(&t, Pol::Other);
            if u == t {
                break;
            }
            t = u;
        }
        t
    }
}
