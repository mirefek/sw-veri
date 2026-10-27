//! Evaluation on concrete data (part of the trusted `simp` extension):
//! the outcomes of a program run from a concrete state, and the members of
//! a set given by a comprehension, computed exactly.
//!
//! A proposition is *solved* for its unknowns (the outcome, intermediate
//! outcomes, bound variables): conjunctions left to right (or right to left
//! when the left needs the right), disjunctions by cases, `x = t` binds an
//! unknown (or matches a constructor pattern against a value), `runs(P, s,
//! o)` evaluates P from the concrete state s, a loop is iterated from its
//! concrete state, `x in set_select(D, y. p)` solves p. Closed propositions
//! are decided by `simp`'s rules (numerals, constructors, definitions).
//! Every step is an equivalence (definitions, the prelude's facts about
//! pairs and outcomes, the loop's finite runs); a loop whose every run from
//! its state ends has no infinite run (its runs form a finitely branching
//! tree without an infinite path). Anything else -- an unknown constrained
//! only by an atom that is not an equation, `any` over an unbounded or
//! empty set (undefined behaviour), a loop exceeding the fuel -- makes the
//! evaluation fail, never return a wrong set.

use super::*;
use crate::term::VarId;
use std::collections::HashMap;

type Assign = Vec<(VarId, Term)>;

const UNSOLVED: &str = "unsolved: ";
/// iterations of all loops, per evaluation
const FUEL: usize = 100_000;
/// the largest numeral whose elements a membership is solved by (a
/// binary's bytes, each)
const ENUM_MAX: u64 = 1 << 16;

pub(super) struct Ev<'s, 'a> {
    sp: &'s Simp<'a>,
    fresh: u32,
    fuel: usize,
    memo: HashMap<(Term, Term), Vec<Term>>,
    /// normal forms of terms met before
    norm_memo: HashMap<Term, Term>,
    /// terms with known values (premises `lhs = value`), and which were used
    known: Vec<(Term, Term)>,
    used: std::cell::RefCell<Vec<bool>>,
    /// counters (printed with EVAL_STATS=1): subst, norm, truth, structural,
    /// outcomes, size of truth's input
    stats: std::cell::RefCell<[u64; 6]>,
}

fn size(t: &Term) -> u64 {
    match t.node() {
        Node::App(_, a) | Node::Var(_, a) => 1 + a.iter().map(size).sum::<u64>(),
        _ => 1,
    }
}

fn err<T>(m: impl Into<String>) -> Result<T, String> {
    Err(m.into())
}

impl<'s, 'a> Ev<'s, 'a> {
    pub(super) fn new(sp: &'s Simp<'a>, fresh: u32) -> Self {
        Ev { sp, fresh, fuel: FUEL, memo: HashMap::new(), norm_memo: HashMap::new(), known: Vec::new(), used: Default::default(), stats: Default::default() }
    }

    /// Premises `lhs = value` (value closed) to use while evaluating.
    pub(super) fn with_known(mut self, eqs: &[Term]) -> Self {
        for e in eqs {
            if let Node::App(q, ab) = e.node() {
                if *q == self.sp.s.eq {
                    let (l, v) = (self.sp.term(&ab[0]), self.sp.term(&ab[1]));
                    self.known.push((l, v));
                    continue;
                }
            }
            // not an equation: kept (unused) so that indices match the premises
            self.known.push((e.clone(), e.clone()));
        }
        self.used = std::cell::RefCell::new(vec![false; eqs.len()]);
        self
    }

    fn var(&mut self) -> (VarId, Term) {
        self.fresh += 1;
        (self.fresh - 1, Term::var(self.fresh - 1, vec![]))
    }

    fn subst(&self, t: &Term, a: &Assign) -> Term {
        self.stats.borrow_mut()[0] += 1;
        let bf = self.sp.env.binders_fn();
        let mut t = t.clone();
        for (v, x) in a {
            if has_var(&t, *v) {
                t = t.subst_var(*v, x, &bf);
            }
        }
        t
    }

    /// an unknown not yet assigned occurs in t
    fn open(&self, t: &Term, us: &[VarId], a: &Assign) -> bool {
        us.iter().any(|u| has_var(t, *u) && !a.iter().any(|(v, _)| v == u))
    }

    fn defined(&self, f: SymId) -> bool {
        matches!(self.sp.env.syms[f as usize].kind, SymKind::Defined { .. })
    }

    fn name(&self, f: SymId) -> &str {
        self.sp.env.kname(f)
    }

    /// A closed term in normal form: `simp`'s term rules, and definitions
    /// of values unfolded where that exposes a constructor, a numeral or a
    /// record (not programs, not definitions by choice or recursion).
    pub(super) fn norm(&mut self, t: &Term) -> Term {
        if let Some(r) = self.norm_memo.get(t) {
            return r.clone();
        }
        let mut r = self.norm1(t);
        // a term with a known value (a premise `lhs = value`)
        if let Some(i) = self.known.iter().position(|(l, _)| *l == r) {
            self.used.borrow_mut()[i] = true;
            r = self.known[i].1.clone();
        }
        self.norm_memo.insert(t.clone(), r.clone());
        r
    }

    fn norm1(&mut self, t: &Term) -> Term {
        self.stats.borrow_mut()[1] += 1;
        let mut t = self.sp.term(t);
        for _ in 0..16 {
            let Node::App(f, a) = t.node() else { return t };
            let (f, a) = (*f, a.clone());
            // arguments first
            let a2: Vec<Term> = a.iter().enumerate().map(|(i, x)| if self.sp.env.binders_fn()(f, i) == 0 { self.norm(x) } else { x.clone() }).collect();
            let t2 = self.sp.term(&Term::app(f, a2.clone()));
            if t2 != t {
                t = t2;
                continue;
            }
            // `ite(c, a, b)` with a condition `simp` alone does not decide
            if is(f, self.sp.s.ite) {
                match self.truth(&a2[0]) {
                    Ok(c) => {
                        t = if c { a2[1].clone() } else { a2[2].clone() };
                        t = self.norm(&t);
                        return t;
                    }
                    Err(_) => return t,
                }
            }
            // `bits_build(n, i. p)`: the word whose bit i is p(i)
            if self.name(f) == "bits_build" {
                if let Some(v) = self.bits_build(&a2) {
                    return v;
                }
                return t;
            }
            if !self.defined(f) || self.opaque(f) {
                return t;
            }
            match self.sp.unfold(f, &a2) {
                Some(u) => {
                    let u = self.sp.term(&u);
                    if self.stuck(&u) {
                        return t;
                    }
                    t = u;
                }
                None => return t,
            }
        }
        t
    }

    fn bits_build(&mut self, a: &[Term]) -> Option<Term> {
        let Node::Nat(n) = a[0].node() else { return None };
        let n = n.to_u64().filter(|&n| n <= 128)?;
        let mut v: u128 = 0;
        for i in 0..n {
            let p = inst_k(self.sp.env, &a[1], &[Term::nat(crate::nat::Nat::from_u64(i))]);
            if self.truth(&p).ok()? {
                v |= 1u128 << i;
            }
        }
        Some(Term::nat(crate::nat::Nat::from_u128(v)))
    }

    /// definitions not unfolded as values (arithmetic: computed on numerals,
    /// kept otherwise)
    fn opaque(&self, f: SymId) -> bool {
        if self.sp.arith.contains_key(&f) {
            return true;
        }
        let n = self.name(f);
        [
            "mkprog", "runs", "bind_rel", "any_rel", "while_rel", "set_select", "set_image", "choose", "nat_rec", "fn_build", "fn_update", "pair", "tag",
            "ok", "exc", "diverge", "some", "none", "empty", "omega", "univ", "cart", "powerset", "union", "upair", "single", "union2", "insert",
            // (computed by the simplifier's rules on constructed data)
            "app", "fst", "snd",
        ]
        .contains(&n)
            || matches!(&self.sp.env.syms[f as usize].kind, SymKind::Defined { body, .. } if matches!(body.node(), Node::App(g, _) if self.name(*g) == "mkprog"))
    }

    /// a term that did not become a value by unfolding
    fn stuck(&self, t: &Term) -> bool {
        match t.node() {
            Node::App(f, _) => ["choose", "nat_rec", "set_select"].contains(&self.name(*f)),
            _ => false,
        }
    }

    // ------------------------------------------------------------------
    //  Deciding closed propositions

    fn truth(&mut self, p: &Term) -> Result<bool, String> {
        {
            let mut st = self.stats.borrow_mut();
            st[2] += 1;
            st[5] += size(p);
        }
        let sp = self.sp;
        let s = &sp.s;
        let p = sp.prop(p, Pol::Other);
        if sp.is_true(&p) {
            return Ok(true);
        }
        if sp.is_false(&p) {
            return Ok(false);
        }
        let Node::App(f, a) = p.node() else { return err(format!("undecided: {}", self.show(&p))) };
        let f = *f;
        if is(f, s.and) {
            return Ok(self.truth(&a[0])? && self.truth(&a[1])?);
        }
        if is(f, s.or) {
            return Ok(self.truth(&a[0])? || self.truth(&a[1])?);
        }
        if is(f, s.not) {
            return Ok(!self.truth(&a[0])?);
        }
        if f == s.imp {
            return Ok(!self.truth(&a[0])? || self.truth(&a[1])?);
        }
        if f == s.eq {
            let (x, y) = (self.norm(&a[0]), self.norm(&a[1]));
            let e = sp.eq(&x, &y);
            if sp.is_true(&e) {
                return Ok(true);
            }
            if sp.is_false(&e) {
                return Ok(false);
            }
            if e != p {
                return self.truth(&e);
            }
            return err(format!("undecided: {}", self.show(&p)));
        }
        if is(f, s.in_) {
            let x = self.norm(&a[0]);
            let set = self.norm(&a[1]);
            if let Some(b) = self.member(&x, &set)? {
                return Ok(b);
            }
        }
        if self.defined(f) && !self.opaque(f) {
            if let Some(u) = sp.unfold(f, a) {
                return self.truth(&u);
            }
        }
        // `ex`, `runs`, ...: by solving
        Ok(!self.structural(&p, &[], Vec::new())?.is_empty())
    }

    /// Membership of a value in a set built from constructors; None: not
    /// decided here.
    fn member(&mut self, x: &Term, set: &Term) -> Result<Option<bool>, String> {
        let Node::App(g, b) = set.node() else { return Ok(None) };
        let n = self.name(*g).to_string();
        Ok(match n.as_str() {
            "empty" => Some(false),
            "omega" => match x.node() {
                Node::Nat(_) => Some(true),
                _ => None,
            },
            // the values of finite data (numerals, strings, pairs, records)
            // are in every universe (closure under pairs and finite sets)
            "univ" if self.finite_data(x) => Some(true),
            "cart" => match x.node() {
                Node::App(p, xy) if is(*p, self.sp.s.pair) || is(*p, self.sp.s.tag) => {
                    let (a0, a1) = (xy[0].clone(), xy[1].clone());
                    let (s0, s1) = (b[0].clone(), b[1].clone());
                    Some(self.truth(&Term::app(self.sp.s.in_.unwrap(), vec![a0, s0]))? && self.truth(&Term::app(self.sp.s.in_.unwrap(), vec![a1, s1]))?)
                }
                _ => None,
            },
            "set_select" => {
                let d = Term::app(self.sp.s.in_.unwrap(), vec![x.clone(), b[0].clone()]);
                Some(self.truth(&d)? && self.truth(&inst_k(self.sp.env, &b[1], &[x.clone()]))?)
            }
            // finite sets: `union(upair(a, b))`, `upair`, `single`, `insert`, `union2`
            "union" | "upair" | "single" | "insert" | "union2" => {
                let in_ = self.sp.s.in_.unwrap();
                let alts: Vec<Term> = match n.as_str() {
                    "union" => match b[0].node() {
                        Node::App(u, ab) if self.name(*u) == "upair" => {
                            vec![Term::app(in_, vec![x.clone(), ab[0].clone()]), Term::app(in_, vec![x.clone(), ab[1].clone()])]
                        }
                        _ => return Ok(None),
                    },
                    "upair" => vec![Term::app(self.sp.s.eq, vec![x.clone(), b[0].clone()]), Term::app(self.sp.s.eq, vec![x.clone(), b[1].clone()])],
                    "single" => vec![Term::app(self.sp.s.eq, vec![x.clone(), b[0].clone()])],
                    "insert" => vec![Term::app(self.sp.s.eq, vec![x.clone(), b[0].clone()]), Term::app(in_, vec![x.clone(), b[1].clone()])],
                    _ => vec![Term::app(in_, vec![x.clone(), b[0].clone()]), Term::app(in_, vec![x.clone(), b[1].clone()])],
                };
                for alt in alts {
                    if self.truth(&alt)? {
                        return Ok(Some(true));
                    }
                }
                Some(false)
            }
            // a defined set (`nat_range`, ...): its definition
            _ if self.defined(*g) && !self.opaque(*g) => match self.sp.unfold(*g, b) {
                Some(u) => {
                    let u = self.sp.term(&u);
                    self.member(x, &u)?
                }
                None => None,
            },
            _ => None,
        })
    }

    fn finite_data(&self, x: &Term) -> bool {
        match x.node() {
            Node::Nat(_) | Node::Bytes(_) => true,
            Node::App(f, a) => {
                let s = &self.sp.s;
                let ctor = is(*f, s.pair) || is(*f, s.tag) || is(*f, s.ok) || is(*f, s.exc) || is(*f, s.some) || is(*f, s.none) || is(*f, s.empty) || is(*f, s.fn_update);
                let n = self.name(*f);
                (ctor || n == "true" || n == "false") && a.iter().all(|y| self.finite_data(y))
            }
            _ => false,
        }
    }

    fn show(&self, t: &Term) -> String {
        crate::syntax::Printer::new(self.sp.env).term(t)
    }

    // ------------------------------------------------------------------
    //  Solving

    /// The assignments to the unknowns `us` (extending `a`) that make `p`
    /// true: all of them, or an error.
    fn solve(&mut self, p: &Term, us: &[VarId], a: Assign) -> Result<Vec<Assign>, String> {
        let p = self.subst(p, &a);
        if !self.open(&p, us, &a) {
            return Ok(if self.truth(&p)? { vec![a] } else { vec![] });
        }
        self.structural(&p, us, a)
    }

    /// `solve` by the proposition's form (also for closed propositions that
    /// `truth` does not decide by itself: `ex`, `runs`, loops, members)
    fn structural(&mut self, p: &Term, us: &[VarId], a: Assign) -> Result<Vec<Assign>, String> {
        self.stats.borrow_mut()[3] += 1;
        let p = p.clone();
        let sp = self.sp;
        let s = &sp.s;
        let Node::App(f, x) = p.node() else { return err(format!("{}{}", UNSOLVED, self.show(&p))) };
        let f = *f;
        if is(f, s.and) {
            return match self.solve(&x[0], us, a.clone()) {
                Ok(es) => {
                    let mut out = Vec::new();
                    for e in es {
                        out.extend(self.solve(&x[1], us, e)?);
                    }
                    Ok(out)
                }
                Err(m) if m.starts_with(UNSOLVED) => {
                    // the right first (reporting the left's problem if that fails too)
                    let mut out = Vec::new();
                    for e in self.solve(&x[1], us, a).map_err(|_| m.clone())? {
                        out.extend(self.solve(&x[0], us, e).map_err(|_| m.clone())?);
                    }
                    Ok(out)
                }
                Err(m) => Err(m),
            };
        }
        if is(f, s.or) {
            let mut out = self.solve(&x[0], us, a.clone())?;
            for e in self.solve(&x[1], us, a)? {
                if !out.contains(&e) {
                    out.push(e);
                }
            }
            return Ok(out);
        }
        if f == s.imp {
            let (n, _) = (sp.not(x[0].clone()), ());
            return self.solve(&sp.or(n, x[1].clone()), us, a);
        }
        if f == s.ex {
            let (v, vt) = self.var();
            let body = inst_k(sp.env, &x[0], &[vt]);
            let mut us2 = us.to_vec();
            us2.push(v);
            let mut out: Vec<Assign> = Vec::new();
            for mut e in self.solve(&body, &us2, a)? {
                e.retain(|(w, _)| *w != v);
                if !out.contains(&e) {
                    out.push(e);
                }
            }
            return Ok(out);
        }
        if f == s.eq {
            let (l, r) = (&x[0], &x[1]);
            for (pat, val) in [(l, r), (r, l)] {
                if !self.open(val, us, &a) {
                    let v = self.norm(val);
                    let mut e = a.clone();
                    return match self.unify(pat, &v, us, &mut e)? {
                        Some(true) => Ok(vec![e]),
                        Some(false) => Ok(vec![]),
                        None => err(format!("{}{}", UNSOLVED, self.show(&p))),
                    };
                }
            }
            return err(format!("{}{}", UNSOLVED, self.show(&p)));
        }
        if is(f, s.runs) {
            if self.open(&x[0], us, &a) || self.open(&x[1], us, &a) {
                return err(format!("{}{}", UNSOLVED, self.show(&p)));
            }
            let outs = self.outcomes(&x[0], &x[1])?;
            let mut res = Vec::new();
            for o in outs {
                let mut e = a.clone();
                match self.unify(&x[2], &o, us, &mut e)? {
                    Some(true) => res.push(e),
                    Some(false) => {}
                    None => return err(format!("{}{}", UNSOLVED, self.show(&p))),
                }
            }
            return Ok(res);
        }
        if is(f, s.in_) && !self.open(&x[1], us, &a) {
            let set = self.norm(&x[1]);
            return self.solve_member(&x[0], &set, us, a);
        }
        if self.name(f) == "while_rel" {
            return self.solve_loop(x, us, a);
        }
        if is(f, s.not) {
            // a negation inward (classical equivalences): !(a -> b) is
            // a && !b, !(a && b) is !a || !b, !(a || b) is !a && !b, !!a is a
            // -- so that an `all` is refuted by solving its counterexample
            if let Node::App(g, y) = x[0].node() {
                let g = *g;
                if g == s.imp {
                    return self.solve(&sp.and(y[0].clone(), sp.not(y[1].clone())), us, a);
                }
                if is(g, s.and) {
                    return self.solve(&sp.or(sp.not(y[0].clone()), sp.not(y[1].clone())), us, a);
                }
                if is(g, s.or) {
                    return self.solve(&sp.and(sp.not(y[0].clone()), sp.not(y[1].clone())), us, a);
                }
                if is(g, s.not) {
                    return self.solve(&y[0], us, a);
                }
            }
            return err(format!("{}{}", UNSOLVED, self.show(&p)));
        }
        if self.defined(f) && self.name(f) != "mkprog" {
            if let Some(u) = sp.unfold(f, x) {
                return self.solve(&u, us, a);
            }
        }
        // letin, ite, ...: `simp`'s equivalences, then again
        let q = sp.prop(&p, Pol::Other);
        if q != p {
            return self.solve(&q, us, a);
        }
        err(format!("{}{}", UNSOLVED, self.show(&p)))
    }

    /// Match the pattern (with unknowns) against a closed value: Some(true)
    /// with the assignments extended, Some(false) if it cannot match, None
    /// if undecided.
    fn unify(&mut self, pat: &Term, v: &Term, us: &[VarId], a: &mut Assign) -> Result<Option<bool>, String> {
        let pat = self.subst(pat, a);
        if !self.open(&pat, us, a) {
            let e = Term::app(self.sp.s.eq, vec![pat, v.clone()]);
            return Ok(Some(self.truth(&e)?));
        }
        if let Node::Var(w, args) = pat.node() {
            if args.is_empty() && us.contains(w) {
                a.push((*w, v.clone()));
                return Ok(Some(true));
            }
        }
        // constructors, each read as the pair it is (`tag(k, v)` is `pair(k,
        // v)`, `ok(s, v)` is `pair(0, pair(s, v))`, `exc` tag 1, `diverge`
        // tag 2): argument by argument
        let s = &self.sp.s;
        let ctor = |t: &Term| -> Option<Vec<Term>> {
            let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
            match t.node() {
                Node::App(g, b) if (is(*g, s.pair) || is(*g, s.tag)) && b.len() == 2 => Some(b.to_vec()),
                Node::App(g, b) if is(*g, s.ok) && b.len() == 2 => Some(vec![nat(0), Term::app(s.pair?, b.to_vec())]),
                Node::App(g, b) if is(*g, s.exc) && b.len() == 2 => Some(vec![nat(1), Term::app(s.pair?, b.to_vec())]),
                Node::App(g, b) if is(*g, s.diverge) && b.len() == 1 => Some(vec![nat(2), b[0].clone()]),
                _ => None,
            }
        };
        let (Some(ap), Some(av)) = (ctor(&pat), ctor(v)) else { return Ok(None) };
        for (x, y) in ap.iter().zip(&av) {
            match self.unify(x, y, us, a)? {
                Some(true) => {}
                r => return Ok(r),
            }
        }
        Ok(Some(true))
    }

    fn solve_member(&mut self, x: &Term, set: &Term, us: &[VarId], a: Assign) -> Result<Vec<Assign>, String> {
        // a numeral n (von Neumann: {0, .., n-1}), not too large: each element
        if let Node::Nat(n) = set.node() {
            if let Some(n) = n.to_u64().filter(|&n| n <= ENUM_MAX) {
                let mut out = Vec::new();
                for v in 0..n {
                    let e = Term::app(self.sp.s.eq, vec![x.clone(), Term::nat(crate::nat::Nat::from_u64(v))]);
                    out.extend(self.solve(&e, us, a.clone())?);
                }
                return Ok(out);
            }
        }
        let Node::App(g, b) = set.node() else { return err(format!("{}membership in {}", UNSOLVED, self.show(set))) };
        match self.name(*g) {
            "set_select" => {
                let (d, pb) = (b[0].clone(), b[1].clone());
                let mut out = Vec::new();
                // naturals below (or up to) a numeral: each of them
                if matches!(d.node(), Node::App(o, oa) if oa.is_empty() && is(*o, self.sp.s.omega)) {
                    let body = inst_k(self.sp.env, &pb, &[x.clone()]);
                    if let Node::App(r, ra) = body.node() {
                        let rel = self.name(*r).to_string();
                        if (rel == "int_lt" || rel == "int_le") && ra[0] == *x {
                            if let Some(n) = match self.norm(&ra[1]).node() {
                                Node::Nat(n) => n.to_u64().filter(|&n| n <= ENUM_MAX),
                                _ => None,
                            } {
                                let top = if rel == "int_lt" { n } else { n + 1 };
                                for v in 0..top {
                                    let e = Term::app(self.sp.s.eq, vec![x.clone(), Term::nat(crate::nat::Nat::from_u64(v))]);
                                    out.extend(self.solve(&e, us, a.clone())?);
                                }
                                return Ok(out);
                            }
                        }
                    }
                }
                for e in self.solve(&inst_k(self.sp.env, &pb, &[x.clone()]), us, a)? {
                    let xv = self.norm(&self.subst(x, &e));
                    if self.open(&xv, us, &e) {
                        return err(format!("{}membership of {} (not determined)", UNSOLVED, self.show(x)));
                    }
                    if self.truth(&Term::app(self.sp.s.in_.unwrap(), vec![xv, d.clone()]))? {
                        out.push(e);
                    }
                }
                Ok(out)
            }
            "empty" => Ok(vec![]),
            _ => {
                if let Some(u) = self.sp.unfold(*g, b) {
                    let u = self.norm(&u);
                    if &u != set {
                        return self.solve_member(x, &u, us, a);
                    }
                }
                err(format!("{}{} in {}", UNSOLVED, self.show(&self.subst(x, &a)), self.show(set)))
            }
        }
    }

    /// `while_rel(l0, l. c, l o. b, l. tr, r)` from a concrete l0: every run
    /// iterated; r matched against each final outcome.
    fn solve_loop(&mut self, x: &[Term], us: &[VarId], a: Assign) -> Result<Vec<Assign>, String> {
        if self.open(&x[0], us, &a) || self.open(&x[1], us, &a) || self.open(&x[2], us, &a) {
            return err(format!("{}a loop from an open state", UNSOLVED));
        }
        let env = self.sp.env;
        let mut finals: Vec<Term> = Vec::new();
        let mut work = vec![self.norm(&x[0])];
        while let Some(l) = work.pop() {
            if self.fuel == 0 {
                return err("a loop did not end within the fuel");
            }
            self.fuel -= 1;
            if !self.truth(&inst_k(env, &x[1], &[l.clone()]))? {
                let empty = Term::app(self.sp.s.empty.unwrap(), vec![]);
                finals.push(Term::app(self.sp.s.ok.unwrap(), vec![l, empty]));
                continue;
            }
            let (ov, ot) = self.var();
            for e in self.solve(&inst_k(env, &x[2], &[l.clone(), ot]), &[ov], Vec::new())? {
                let Some((_, o)) = e.iter().find(|(w, _)| *w == ov) else { return err("an iteration's outcome is not determined (undefined behaviour)") };
                let o = self.norm(o);
                match o.node() {
                    Node::App(k, ob) if is(*k, self.sp.s.ok) => work.push(ob[0].clone()),
                    _ => finals.push(o),
                }
            }
        }
        let mut res = Vec::new();
        for f in finals {
            let mut e = a.clone();
            match self.unify(&x[4], &f, us, &mut e)? {
                Some(true) => res.push(e),
                Some(false) => {}
                None => return err(format!("{}the outcome of a loop", UNSOLVED)),
            }
        }
        Ok(res)
    }

    /// The outcomes of program p run from the concrete state st.
    fn outcomes(&mut self, p: &Term, st: &Term) -> Result<Vec<Term>, String> {
        self.stats.borrow_mut()[4] += 1;
        let p = self.norm(p);
        let st = self.norm(st);
        if let Some(r) = self.memo.get(&(p.clone(), st.clone())) {
            return Ok(r.clone());
        }
        let mut q = p.clone();
        for _ in 0..8 {
            match q.node() {
                Node::App(m, _) if is(*m, self.sp.s.mkprog) => break,
                Node::App(g, b) if self.defined(*g) => match self.sp.unfold(*g, b) {
                    Some(u) => q = self.sp.term(&u),
                    None => return err(format!("not a program: {}", self.show(&q))),
                },
                _ => return err(format!("not a program: {}", self.show(&q))),
            }
        }
        let Node::App(m, r) = q.node() else { return err("not a program") };
        if !is(*m, self.sp.s.mkprog) {
            return err(format!("not a program: {}", self.show(&q)));
        }
        let (ov, ot) = self.var();
        let rel = inst_k(self.sp.env, &r[0], &[st.clone(), ot]);
        let mut outs = Vec::new();
        for e in self.solve(&rel, &[ov], Vec::new())? {
            let Some((_, o)) = e.iter().find(|(w, _)| *w == ov) else {
                return err(format!("an outcome of {} is not determined (undefined behaviour)", self.show(&p)));
            };
            let o = self.norm(o);
            if !outs.contains(&o) {
                outs.push(o);
            }
        }
        self.memo.insert((p, st), outs.clone());
        Ok(outs)
    }

    /// The members of a set: `x in set` solved for x.
    pub(super) fn members(&mut self, set: &Term) -> Result<Vec<Term>, String> {
        let (xv, xt) = self.var();
        let set = self.norm(set);
        let mut out = Vec::new();
        for e in self.solve_member(&xt, &set, &[xv], Vec::new())? {
            let Some((_, v)) = e.iter().find(|(w, _)| *w == xv) else { return err("a member is not determined") };
            let v = self.norm(v);
            if !out.contains(&v) {
                out.push(v);
            }
        }
        Ok(out)
    }
}

impl Logic {
    /// `p` is true, evaluated on concrete data with the premises `lhs =
    /// value` as known values; which premises were used.
    pub fn eval_truth(&self, env: &Env, p: &Term, known: &[Term]) -> crate::env::KResult<Vec<usize>> {
        let sp = Simp::new(env, self);
        let fresh = known.iter().chain([p]).map(|t| max_var(t) + 1).fold(env.var_bound() + 5_000_000, u32::max);
        let mut ev = Ev::new(&sp, fresh).with_known(known);
        match ev.truth(p) {
            Ok(true) => Ok(ev.used.borrow().iter().enumerate().filter(|(_, u)| **u).map(|(i, _)| i).collect()),
            Ok(false) => Err(crate::env::KernelError(format!("eval: false: {}", ev.show(p)))),
            Err(e) => Err(crate::env::KernelError(format!("eval: {}", e))),
        }
    }

    /// The members of `set` (a comprehension, evaluated on concrete data,
    /// with the premises `lhs = value` as known values): `all x. x in set
    /// <-> x = c1 || .. || x = cn`, and which premises were used.
    pub fn eval_members(&self, env: &Env, set: &Term, known: &[Term]) -> crate::env::KResult<(Term, Vec<usize>)> {
        let sp = Simp::new(env, self);
        let fresh = known.iter().chain([set]).map(|t| max_var(t) + 1).fold(env.var_bound() + 5_000_000, u32::max);
        let mut ev = Ev::new(&sp, fresh).with_known(known);
        let ms = ev.members(set).map_err(|e| crate::env::KernelError(format!("eval: {}", e)))?;
        if std::env::var("EVAL_STATS").is_ok() {
            eprintln!("eval stats [subst, norm, truth, structural, outcomes, truth input size]: {:?}", ev.stats.borrow());
        }
        let iff = env.ksym("iff").ok_or_else(|| crate::env::KernelError("no iff".into()))?;
        let mut rhs = sp.ff();
        for m in &ms {
            rhs = sp.or(rhs, Term::app(sp.s.eq, vec![Term::bvar(0), m.shift(1, 0, &env.binders_fn())]));
        }
        let body = Term::app(iff, vec![Term::app(sp.s.in_.unwrap(), vec![Term::bvar(0), set.shift(1, 0, &env.binders_fn())]), rhs]);
        let used: Vec<usize> = ev.used.borrow().iter().enumerate().filter(|(_, u)| **u).map(|(i, _)| i).collect();
        Ok((Term::app(sp.s.all, vec![body]), used))
    }
}
