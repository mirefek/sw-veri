//! Natural-number arithmetic: linear arithmetic (with propositional
//! structure), and the recursion equations of `nat_rec`.
//!
//! Trusted extension. The prelude's naturals are von Neumann ordinals in
//! `omega`, with `nat_lt` = membership and `+ * - / %` defined by recursion
//! (`nat_rec`) and choice. What this module relies on are the standard facts
//! about them, all theorems of the prelude (via the recursion theorem for
//! `nat_rec` and induction, `omega_ind`):
//!
//! * `nat_rec(z, k v. s, 0) = z`, and for `n in omega`:
//!   `nat_rec(z, k v. s, n + 1) = s(n, nat_rec(z, k v. s, n))`;
//! * `(omega, 0, succ, nat_add, nat_mul, nat_lt)` is the standard model of
//!   the naturals: `succ(n) = n + 1`, `0 = empty` (`lit_zero`), literals
//!   are their values (`lit_succ`, `lit_nat`), `+` and `*` are commutative
//!   semiring operations, `<` (= `in`) is the strict order with `a < b`
//!   iff `a + 1 <= b`, and `<=` (`nat_le`) is `<` or `=`;
//! * `b <= a -> nat_sub(a, b) in omega && b + nat_sub(a, b) = a`
//!   (nothing is used about `nat_sub(a, b)` when `a < b`);
//! * for `k > 0`: `a = k * nat_div(a, k) + nat_mod(a, k)` with
//!   `nat_mod(a, k) < k` (Euclidean division).
//!
//! `arith(premises, goal)` checks that `premises -> goal` holds whenever
//! each atom is read as true or false and the arithmetic atoms are
//! consistent: for every assignment falsifying it, the arithmetic literals
//! are infeasible over the integers (Fourier-Motzkin elimination with
//! integer tightening: sound, not complete). A term is read as a number
//! only if it is known to be one: a literal, a term `t` with a premise
//! `t in omega` or `t in bits(k)`, a term equated to a number by a premise,
//! the length of a list expression over known lists (`ext::list`), or
//! built from those with `succ`, `+`, `*` by a constant, `-`, and `/`, `%`
//! by a positive constant. Other atoms stay propositional. A goal
//! `t in omega` where t has differences `nat_sub(a, b)` is shown from
//! `b <= a` for each of them (then `nat_sub(a, b) in omega`, as above).

use super::prop::Logic;
use crate::env::{Env, KResult, KernelError};
use crate::term::{Node, SymId, Term};
use std::collections::BTreeMap;

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

/// `sum coeffs[v] * x_v + c`, a linear form over integer variables.
#[derive(Clone, Debug, PartialEq)]
struct Lin {
    coeffs: BTreeMap<usize, i128>,
    c: i128,
}

impl Lin {
    fn konst(c: i128) -> Lin {
        Lin { coeffs: BTreeMap::new(), c }
    }
    fn var(v: usize) -> Lin {
        Lin { coeffs: BTreeMap::from([(v, 1)]), c: 0 }
    }
    fn add(&self, o: &Lin, k: i128) -> Option<Lin> {
        let mut r = self.clone();
        for (v, a) in &o.coeffs {
            let e = r.coeffs.entry(*v).or_insert(0);
            *e = e.checked_add(a.checked_mul(k)?)?;
            if *e == 0 {
                r.coeffs.remove(v);
            }
        }
        r.c = r.c.checked_add(o.c.checked_mul(k)?)?;
        Some(r)
    }
    fn scale(&self, k: i128) -> Option<Lin> {
        Lin::konst(0).add(self, k)
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Rel {
    Lt,
    Le,
    Eq,
}

/// An arithmetic atom `lhs rel rhs`, or a membership `t in omega` that
/// holds because t is a number.
#[derive(Clone, Debug)]
enum Atom {
    Cmp(Lin, Rel, Lin),
    True,
}

/// `nat_sub(a, b)` stands for variable `v`: `b <= a -> v = a - b`.
#[derive(Clone, Debug)]
struct SubVar {
    v: usize,
    a: Lin,
    b: Lin,
}

struct Reader {
    s: Syms,
    ls: super::list::LSyms,
    /// terms known to be lists (their lengths are naturals)
    lists: Vec<Term>,
    /// terms known to be naturals
    nats: Vec<Term>,
    /// variables: the term each stands for
    vars: Vec<Term>,
    /// side conditions (each `lin >= 0`) for division variables
    side: Vec<Lin>,
    subs: Vec<SubVar>,
}

#[derive(Clone, Copy)]
struct Syms {
    eq: SymId,
    in_: SymId,
    lit_lt: SymId,
    lit_add: SymId,
    nat_lt: Option<SymId>,
    nat_le: Option<SymId>,
    nat_add: Option<SymId>,
    nat_sub: Option<SymId>,
    nat_mul: Option<SymId>,
    nat_div: Option<SymId>,
    nat_mod: Option<SymId>,
    succ: Option<SymId>,
    empty: Option<SymId>,
    omega: Option<SymId>,
    bits: Option<SymId>,
}

impl Syms {
    fn new(env: &Env) -> Syms {
        let s = |n: &str| env.sym_by_name.get(n).copied();
        Syms {
            eq: env.builtins.eq,
            in_: s("in").unwrap_or(u32::MAX),
            lit_lt: env.builtins.lit_lt,
            lit_add: env.builtins.lit_add,
            nat_lt: s("nat_lt"),
            nat_le: s("nat_le"),
            nat_add: s("nat_add"),
            nat_sub: s("nat_sub"),
            nat_mul: s("nat_mul"),
            nat_div: s("nat_div"),
            nat_mod: s("nat_mod"),
            succ: s("succ"),
            empty: s("empty"),
            omega: s("omega"),
            bits: s("bits"),
        }
    }
}

/// The subterms of `t` headed by `f` (not under binders).
fn collect_app(t: &Term, f: SymId, out: &mut Vec<Term>) {
    if let Node::App(g, a) = t.node() {
        if *g == f && !out.contains(t) {
            out.push(t.clone());
        }
        a.iter().for_each(|x| collect_app(x, f, out));
    }
}

fn is(s: SymId, o: Option<SymId>) -> bool {
    o == Some(s)
}

impl Reader {
    fn var_of(&mut self, t: &Term) -> usize {
        match self.vars.iter().position(|x| x == t) {
            Some(i) => i,
            None => {
                self.vars.push(t.clone());
                self.vars.len() - 1
            }
        }
    }

    /// `t in omega` or `t in bits(k)`: the t
    fn membership(&self, t: &Term) -> Option<Term> {
        if let Node::App(i, a) = t.node() {
            if *i == self.s.in_ {
                match a[1].node() {
                    Node::App(o, _) if is(*o, self.s.omega) => return Some(a[0].clone()),
                    Node::App(b, _) if is(*b, self.s.bits) => return Some(a[0].clone()),
                    _ => {}
                }
            }
        }
        None
    }

    /// The linear form of a natural-number term, if it is one.
    fn lin(&mut self, t: &Term) -> Option<Lin> {
        let s = self.s;
        match t.node() {
            Node::Nat(n) => return n.to_u64().map(|v| Lin::konst(v as i128)),
            Node::App(e, a) if a.is_empty() && is(*e, s.empty) => return Some(Lin::konst(0)),
            Node::App(f, a) if is(*f, s.succ) => return self.lin(&a[0])?.add(&Lin::konst(1), 1),
            // the length of a list expression: its singletons plus the
            // lengths of the lists in it
            Node::App(f, a) if is(*f, self.ls.len) => {
                if let Some(pieces) = super::list::flatten(&self.ls, &a[0], &self.lists) {
                    let mut l = Lin::konst(0);
                    for p in pieces {
                        l = match p {
                            super::list::Piece::One(_) => l.add(&Lin::konst(1), 1)?,
                            super::list::Piece::List(m) => {
                                let v = self.var_of(&Term::app(*f, vec![m]));
                                l.add(&Lin::var(v), 1)?
                            }
                        };
                    }
                    return Some(l);
                }
            }
            Node::App(f, a) if is(*f, s.nat_add) => {
                let (x, y) = (self.lin(&a[0])?, self.lin(&a[1])?);
                return x.add(&y, 1);
            }
            Node::App(f, a) if *f == s.lit_add && matches!(a[0].node(), Node::Nat(_)) && matches!(a[1].node(), Node::Nat(_)) => {
                let (x, y) = (self.lin(&a[0])?, self.lin(&a[1])?);
                return x.add(&y, 1);
            }
            Node::App(f, a) if is(*f, s.nat_mul) => {
                // linear only if one factor is a constant
                if let Some(x) = self.lin_opt_const(&a[0]) {
                    let y = self.lin(&a[1])?;
                    return y.scale(x);
                }
                if let Some(y) = self.lin_opt_const(&a[1]) {
                    let x = self.lin(&a[0])?;
                    return x.scale(y);
                }
            }
            Node::App(f, a) if is(*f, s.nat_sub) => {
                let (x, y) = (self.lin(&a[0])?, self.lin(&a[1])?);
                if let Some(sv) = self.subs.iter().find(|sv| self.vars[sv.v] == *t) {
                    return Some(Lin::var(sv.v));
                }
                let v = self.var_of(t);
                self.subs.push(SubVar { v, a: x, b: y });
                return Some(Lin::var(v));
            }
            Node::App(f, a) if is(*f, s.nat_div) || is(*f, s.nat_mod) => {
                if let Some(k) = self.lin_opt_const(&a[1]).filter(|k| *k > 0) {
                    let x = self.lin(&a[0])?;
                    // q = a / k, r = a % k: a = k q + r, 0 <= r < k
                    let (qt, rt) = (
                        Term::app(s.nat_div.unwrap(), vec![a[0].clone(), a[1].clone()]),
                        Term::app(s.nat_mod.unwrap(), vec![a[0].clone(), a[1].clone()]),
                    );
                    let fresh = !self.vars.contains(&qt);
                    let (q, r) = (self.var_of(&qt), self.var_of(&rt));
                    if fresh {
                        // a - k q - r = 0, r >= 0, k - 1 - r >= 0, q >= 0
                        let d = x.add(&Lin::var(q), -k)?.add(&Lin::var(r), -1)?;
                        self.side.push(d.clone());
                        self.side.push(d.scale(-1)?);
                        self.side.push(Lin::konst(k - 1).add(&Lin::var(r), -1)?);
                    }
                    return Some(Lin::var(if is(*f, s.nat_div) { q } else { r }));
                }
            }
            _ => {}
        }
        if self.nats.contains(t) {
            let v = self.var_of(t);
            return Some(Lin::var(v));
        }
        None
    }

    fn lin_opt_const(&mut self, t: &Term) -> Option<i128> {
        match t.node() {
            Node::Nat(n) => n.to_u64().map(|v| v as i128),
            _ => None,
        }
    }

    /// Reads an atom of the propositional structure.
    fn atom(&mut self, t: &Term) -> Option<Atom> {
        let s = self.s;
        let Node::App(f, a) = t.node() else { return None };
        if a.len() != 2 {
            return None;
        }
        let rel = if *f == s.eq {
            Rel::Eq
        } else if is(*f, s.nat_lt) || *f == s.lit_lt {
            Rel::Lt
        } else if is(*f, s.nat_le) {
            Rel::Le
        } else if *f == s.in_ {
            if let Node::App(o, _) = a[1].node() {
                if is(*o, s.omega) {
                    // a number built from numbers is a number (no `-`: it
                    // may leave omega; unless the difference is known to
                    // be a number)
                    let n = self.subs.len();
                    let r = self.lin(&a[0]).map(|_| Atom::True);
                    if self.subs[n..].iter().any(|sv| !self.nats.contains(&self.vars[sv.v])) {
                        self.subs.truncate(n);
                        return None;
                    }
                    return r;
                }
            }
            Rel::Lt
        } else {
            return None;
        };
        let (x, y) = (self.lin(&a[0])?, self.lin(&a[1])?);
        Some(Atom::Cmp(x, rel, y))
    }
}

/// Fourier-Motzkin: is `{ l >= 0 : l in cs }` infeasible over the integers?
/// (Unknown is reported as feasible.)
fn infeasible(mut cs: Vec<Lin>) -> bool {
    fn gcd(a: i128, b: i128) -> i128 {
        if b == 0 { a.abs() } else { gcd(b, a % b) }
    }
    // integer tightening: divide by the gcd of the coefficients, rounding
    // the constant down
    let norm = |l: &mut Lin| {
        let g = l.coeffs.values().fold(0, |g, c| gcd(g, *c));
        if g > 1 {
            for c in l.coeffs.values_mut() {
                *c /= g;
            }
            l.c = l.c.div_euclid(g);
        }
    };
    for l in cs.iter_mut() {
        norm(l);
    }
    loop {
        if cs.iter().any(|l| l.coeffs.is_empty() && l.c < 0) {
            return true;
        }
        cs.retain(|l| !l.coeffs.is_empty());
        cs.dedup();
        // the variable with the fewest new constraints
        let mut best: Option<(usize, usize)> = None;
        let mut vars: Vec<usize> = cs.iter().flat_map(|l| l.coeffs.keys().copied()).collect();
        vars.sort();
        vars.dedup();
        if vars.is_empty() {
            return false;
        }
        for &v in &vars {
            let p = cs.iter().filter(|l| l.coeffs.get(&v).is_some_and(|c| *c > 0)).count();
            let n = cs.iter().filter(|l| l.coeffs.get(&v).is_some_and(|c| *c < 0)).count();
            let cost = p * n;
            if best.is_none_or(|b| cost < b.1) {
                best = Some((v, cost));
            }
        }
        let v = best.unwrap().0;
        let (with, mut rest): (Vec<Lin>, Vec<Lin>) = cs.into_iter().partition(|l| l.coeffs.contains_key(&v));
        let pos: Vec<&Lin> = with.iter().filter(|l| l.coeffs[&v] > 0).collect();
        let neg: Vec<&Lin> = with.iter().filter(|l| l.coeffs[&v] < 0).collect();
        for p in &pos {
            for n in &neg {
                let (a, b) = (p.coeffs[&v], -n.coeffs[&v]);
                let Some(mut l) = p.scale(b).and_then(|x| x.add(n, a)) else { return false };
                l.coeffs.remove(&v);
                norm(&mut l);
                rest.push(l);
            }
        }
        if rest.len() > 20_000 {
            return false;
        }
        cs = rest;
    }
}

/// The literals of one assignment (with `!=` split into cases) are
/// infeasible.
fn refuted(lits: &[(Lin, Rel, Lin, bool)], base: &[Lin], subs: &[SubVar], k: usize) -> bool {
    if k == lits.len() {
        // `nat_sub` variables: either b <= a and v = a - b (v >= 0), or
        // a < b and nothing is known (constraints using v are dropped)
        return refute_subs(base.to_vec(), subs, 0);
    }
    let (x, rel, y, val) = &lits[k];
    let add = |extra: Vec<Lin>| {
        let mut b = base.to_vec();
        b.extend(extra);
        refuted(lits, &b, subs, k + 1)
    };
    let d = y.add(x, -1).unwrap_or(Lin::konst(0)); // y - x
    let dn = x.add(y, -1).unwrap_or(Lin::konst(0)); // x - y
    match (rel, val) {
        (Rel::Lt, true) => add(vec![d.add(&Lin::konst(1), -1).unwrap_or(d.clone())]),
        (Rel::Lt, false) => add(vec![dn]),
        (Rel::Le, true) => add(vec![d]),
        (Rel::Le, false) => add(vec![dn.add(&Lin::konst(1), -1).unwrap_or(dn.clone())]),
        (Rel::Eq, true) => add(vec![d, dn]),
        (Rel::Eq, false) => {
            add(vec![d.add(&Lin::konst(1), -1).unwrap_or(d.clone())])
                && add(vec![dn.add(&Lin::konst(1), -1).unwrap_or(dn.clone())])
        }
    }
}

fn refute_subs(base: Vec<Lin>, subs: &[SubVar], k: usize) -> bool {
    if k == subs.len() {
        return infeasible(base);
    }
    let sv = &subs[k];
    // case b <= a: a - b >= 0, v = a - b
    let mut c1 = base.clone();
    let amb = sv.a.add(&sv.b, -1).unwrap_or(Lin::konst(0));
    c1.push(amb.clone());
    let e = amb.add(&Lin::var(sv.v), -1).unwrap_or(Lin::konst(0));
    c1.push(e.clone());
    c1.push(e.scale(-1).unwrap_or(Lin::konst(0)));
    // case a < b: b - a - 1 >= 0, and nothing about v
    let mut c2: Vec<Lin> = base.into_iter().filter(|l| !l.coeffs.contains_key(&sv.v)).collect();
    c2.push(sv.b.add(&sv.a, -1).and_then(|x| x.add(&Lin::konst(1), -1)).unwrap_or(Lin::konst(0)));
    refute_subs(c1, subs, k + 1) && refute_subs(c2, subs, k + 1)
}

impl Logic {
    /// `premises -> goal` holds by propositional logic and linear arithmetic
    /// over the naturals (see the module docs).
    pub fn arith(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        // a goal `t in omega` with differences `nat_sub(a, b)` in t: from
        // `b <= a` for each (then `nat_sub(a, b) in omega`)
        let s = Syms::new(env);
        if let (Node::App(i, g), Some(nat_sub), Some(nat_le)) = (goal.node(), s.nat_sub, s.nat_le) {
            if *i == s.in_ && matches!(g[1].node(), Node::App(o, _) if is(*o, s.omega)) {
                let mut subs = Vec::new();
                collect_app(&g[0], nat_sub, &mut subs);
                if !subs.is_empty() && self.arith_core(env, premises, goal).is_err() {
                    let mut ps = premises.to_vec();
                    for t in &subs {
                        let Node::App(_, ab) = t.node() else { unreachable!() };
                        self.arith(env, premises, &Term::app(nat_le, vec![ab[1].clone(), ab[0].clone()]))?;
                        ps.push(Term::app(s.in_, vec![t.clone(), g[1].clone()]));
                    }
                    return self.arith_core(env, &ps, goal);
                }
            }
        }
        self.arith_core(env, premises, goal)
    }

    fn arith_core(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        let s = Syms::new(env);
        let mut r = Reader { s, ls: super::list::LSyms::new(env), lists: super::list::known_lists(env, premises), nats: Vec::new(), vars: Vec::new(), side: Vec::new(), subs: Vec::new() };
        // numbers: memberships among the premises, then terms equated to
        // numbers (repeat until nothing changes)
        for p in premises {
            if let Some(t) = r.membership(p) {
                r.nats.push(t);
            }
        }
        loop {
            let before = r.nats.len();
            for p in premises {
                if let Node::App(e, a) = p.node() {
                    if *e == s.eq && a.len() == 2 {
                        for (x, y) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                            // (not through `-`: it may leave omega)
                            let n = r.subs.len();
                            let num = r.lin(y).is_some() && r.subs.len() == n;
                            r.subs.truncate(n);
                            if num && !r.nats.contains(x) {
                                r.nats.push(x.clone());
                            }
                        }
                    }
                }
            }
            if r.nats.len() == before {
                break;
            }
        }
        r.vars.clear();
        r.side.clear();
        r.subs.clear();
        let mut f = goal.clone();
        for p in premises.iter().rev() {
            f = Term::app(self.imp, vec![p.clone(), f]);
        }
        let mut atoms: Vec<Term> = Vec::new();
        let tree = self.prop_tree(env, &f, &mut atoms, 0)?;
        if atoms.len() > 20 {
            return err("arith: too many atoms");
        }
        let read: Vec<Option<Atom>> = atoms.iter().map(|a| r.atom(a)).collect();
        // every variable is a natural
        let mut base: Vec<Lin> = (0..r.vars.len()).filter(|v| !r.subs.iter().any(|s| s.v == *v)).map(Lin::var).collect();
        base.extend(r.side.iter().cloned());
        for row in 0u64..(1 << atoms.len()) {
            if tree.eval(row) {
                continue;
            }
            let mut lits = Vec::new();
            let mut contradiction = false;
            for (i, a) in read.iter().enumerate() {
                let val = row >> i & 1 == 1;
                match a {
                    Some(Atom::Cmp(x, rel, y)) => lits.push((x.clone(), *rel, y.clone(), val)),
                    Some(Atom::True) if !val => contradiction = true,
                    _ => {}
                }
            }
            if contradiction {
                continue;
            }
            if !refuted(&lits, &base, &r.subs, 0) {
                let atoms_s: Vec<String> = atoms
                    .iter()
                    .enumerate()
                    .map(|(i, a)| format!("{}={}", crate::syntax::Printer::new(env).term(a), row >> i & 1))
                    .collect();
                return err(format!("arith: not shown (a consistent case: {})", atoms_s.join(", ")));
            }
        }
        Ok(())
    }

    /// The recursion equations of `nat_rec` for `t = nat_rec(z, k v. s, n)`:
    /// `t = z` if n is 0; `t = s(m, nat_rec(z, k v. s, m))` if n is
    /// `m + 1` or `succ(m)`, given `m in omega` (`m_nat`).
    pub fn nat_rec_eq(&self, env: &Env, t: &Term, m_nat: Option<&Term>) -> KResult<Term> {
        let rec = env.sym_by_name.get("nat_rec").copied();
        let s = Syms::new(env);
        let Node::App(f, a) = t.node() else { return err("rec: not nat_rec(...)") };
        if Some(*f) != rec || a.len() != 3 {
            return err("rec: not nat_rec(...)");
        }
        let (z, step, n) = (&a[0], &a[1], &a[2]);
        let zero = matches!(n.node(), Node::Nat(k) if k.is_zero()) || matches!(n.node(), Node::App(e, x) if x.is_empty() && is(*e, s.empty));
        if zero {
            return Ok(env.mk_eq(t.clone(), z.clone()));
        }
        let m = match n.node() {
            Node::App(g, x) if is(*g, s.succ) => x[0].clone(),
            Node::App(g, x) if is(*g, s.nat_add) && matches!(x[1].node(), Node::Nat(k) if k.to_u64() == Some(1)) => x[0].clone(),
            _ => return err("rec: the argument is neither 0 nor m + 1"),
        };
        let omega = s.omega.ok_or_else(|| KernelError("no omega".into()))?;
        let want = Term::app(s.in_, vec![m.clone(), Term::app(omega, vec![])]);
        if m_nat != Some(&want) {
            return err("rec: needs a proof of `m in omega`");
        }
        let prev = Term::app(*f, vec![z.clone(), step.clone(), m.clone()]);
        let body = step.instantiate_params(&[m, prev], &env.binders_fn());
        Ok(env.mk_eq(t.clone(), body))
    }
}
