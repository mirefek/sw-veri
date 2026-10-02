//! Integer arithmetic: linear arithmetic (with propositional structure),
//! and the recursion equations of `nat_rec`.
//!
//! Trusted extension. The prelude's integers are the von Neumann naturals
//! (`omega`) and `pair(1, n)` for -n; arithmetic is total: every operation
//! reads its arguments through `int_val` (a set that is not an integer
//! counts as 0) and yields an integer. What this module relies on are the
//! standard facts about them, all theorems of the prelude (via the
//! recursion theorem for `nat_rec` and induction, `omega_ind`):
//!
//! * `nat_rec(z, k v. s, 0) = z`, and for `n in omega`:
//!   `nat_rec(z, k v. s, n + 1) = s(n, nat_rec(z, k v. s, n))`;
//! * `(int, 0, int_add, int_neg, int_mul, int_lt)` is the ordered ring of the
//!   integers on the values `int_val(x)` of its arguments, with `int_sub(a,
//!   b) = a + (-b)`, `int_succ(a) = a + 1`, `int_pred(a) = a - 1`, `int_le`
//!   is `<` or `=` of the values, `0 = empty` (`lit_zero`) and literals are
//!   naturals with their values (`lit_*`);
//! * for `k > 0`: `int_val(a) = k * int_div(a, k) + int_mod(a, k)` with
//!   `0 <= int_mod(a, k) < k` (Euclidean division);
//! * `omega` is the integers `>= 0`; `bits(n)` those in `0 .. 2^n - 1`;
//!   `bits_add(n, a, b) = int_mod(a + b, 2^n)` (and `bits_sub`, `bits_neg`,
//!   `bits_of_int` likewise); the length of a list is in omega.
//!
//! `arith(premises, goal)` checks that `premises -> goal` holds whenever
//! each atom is read as true or false and the arithmetic atoms are
//! consistent: for every assignment falsifying it, the arithmetic literals
//! are infeasible over the integers (Fourier-Motzkin elimination with
//! integer tightening: sound, not complete). Every term in an arithmetic
//! position stands for its value `int_val(t)`: arithmetic terms exactly,
//! other terms as integer variables. Comparisons `int_lt`, `int_le` are
//! comparisons of values. An equation `a = b`, and membership in `omega`
//! or `bits(k)`, are read arithmetically only when a and b are integers
//! (arithmetic terms, numerals, or with a premise `t in int`, `t in omega`
//! or `t in bits(k)`): for other sets, equal values do not make equal sets.

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

/// An arithmetic atom `lhs rel rhs`, a range `lo <= x <= hi` (membership in
/// `omega` or `bits(k)` of an integer), or an atom that holds (a term of
/// arithmetic is an integer).
#[derive(Clone, Debug)]
enum Atom {
    Cmp(Lin, Rel, Lin),
    Range(Lin, i128, Option<i128>),
    True,
}

struct Reader {
    s: Syms,
    ls: super::list::LSyms,
    /// terms known to be lists (their lengths are naturals)
    lists: Vec<Term>,
    /// terms known to be integers (premises `t in int / omega / bits(k)`)
    ints: Vec<Term>,
    /// ... and naturals (premises `t in omega / bits(k)`): succ(t) is t + 1
    nats: Vec<Term>,
    /// variables: the term each stands for (its value)
    vars: Vec<Term>,
    /// side conditions (each `lin >= 0`): divisions, list lengths
    side: Vec<Lin>,
}

#[derive(Clone, Copy)]
struct Syms {
    eq: SymId,
    in_: SymId,
    lit_lt: SymId,
    lit_add: SymId,
    int_lt: Option<SymId>,
    int_le: Option<SymId>,
    int_add: Option<SymId>,
    int_sub: Option<SymId>,
    int_neg: Option<SymId>,
    int_mul: Option<SymId>,
    int_div: Option<SymId>,
    int_mod: Option<SymId>,
    int_succ: Option<SymId>,
    int_pred: Option<SymId>,
    succ: Option<SymId>,
    empty: Option<SymId>,
    omega: Option<SymId>,
    int: Option<SymId>,
    bits: Option<SymId>,
    bits_add: Option<SymId>,
    bits_sub: Option<SymId>,
    bits_neg: Option<SymId>,
    bits_of_int: Option<SymId>,
    pair: Option<SymId>,
}

impl Syms {
    fn new(env: &Env) -> Syms {
        let s = |n: &str| env.sym_by_name.get(n).copied();
        Syms {
            eq: env.builtins.eq,
            in_: s("in").unwrap_or(u32::MAX),
            lit_lt: env.builtins.lit_lt,
            lit_add: env.builtins.lit_add,
            int_lt: s("int_lt"),
            int_le: s("int_le"),
            int_add: s("int_add"),
            int_sub: s("int_sub"),
            int_neg: s("int_neg"),
            int_mul: s("int_mul"),
            int_div: s("int_div"),
            int_mod: s("int_mod"),
            int_succ: s("int_succ"),
            int_pred: s("int_pred"),
            succ: s("succ"),
            empty: s("empty"),
            omega: s("omega"),
            int: s("int"),
            bits: s("bits"),
            bits_add: s("bits_add"),
            bits_sub: s("bits_sub"),
            bits_neg: s("bits_neg"),
            bits_of_int: s("bits_of_int"),
            pair: s("pair"),
        }
    }
}

fn is(s: SymId, o: Option<SymId>) -> bool {
    o == Some(s)
}

/// numerals up to 2^100 (coefficients are i128; room for sums and products
/// by small constants, which `Lin` checks)
fn small(t: &Term) -> Option<i128> {
    match t.node() {
        Node::Nat(n) => n.to_u128().filter(|&v| v <= 1u128 << 100).map(|v| v as i128),
        _ => None,
    }
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

    /// `t in int`, `t in omega` or `t in bits(k)`: the t
    fn membership(&self, t: &Term) -> Option<Term> {
        if let Node::App(i, a) = t.node() {
            if *i == self.s.in_ {
                if let Node::App(o, _) = a[1].node() {
                    if is(*o, self.s.omega) || is(*o, self.s.bits) || is(*o, self.s.int) {
                        return Some(a[0].clone());
                    }
                }
            }
        }
        None
    }

    /// `t` is an integer: a numeral, a term of arithmetic, or known to be one.
    fn is_int(&self, t: &Term) -> bool {
        let s = self.s;
        match t.node() {
            Node::Nat(_) => true,
            Node::App(e, a) if a.is_empty() && is(*e, s.empty) => true,
            // a negative literal: pair(1, m) is -m
            Node::App(p, a) if is(*p, s.pair) && a.len() == 2 && small(&a[0]) == Some(1) && small(&a[1]).is_some_and(|m| m > 0) => true,
            Node::App(f, a) if is(*f, s.succ) => small(&a[0]).is_some() || self.nats.contains(&a[0]),
            // the length of a list expression (a natural)
            Node::App(f, a) if is(*f, self.ls.len) && super::list::flatten(&self.ls, &a[0], &self.lists).is_some() => true,
            Node::App(f, _) => {
                [s.int_add, s.int_sub, s.int_neg, s.int_mul, s.int_div, s.int_mod, s.int_succ, s.int_pred].iter().any(|g| is(*f, *g))
                    || self.bits_op(t).is_some()
                    || self.ints.contains(t)
            }
            _ => self.ints.contains(t),
        }
    }

    /// `t` is known to be a natural: a numeral, or with a premise `t in
    /// omega` / `t in bits(k)`.
    fn natural(&self, t: &Term) -> bool {
        small(t).is_some() || self.nats.contains(t)
    }

    /// `bits_add(n, a, b)` etc. with a numeral width: (2^n, the argument of
    /// the reduction mod 2^n)
    fn bits_op(&self, t: &Term) -> Option<(i128, Vec<(Term, i128)>)> {
        let Node::App(f, a) = t.node() else { return None };
        let s = self.s;
        let n = small(a.first()?)?;
        if !(0..=64).contains(&n) {
            return None;
        }
        let m = 1i128 << n;
        let parts = if is(*f, s.bits_add) && a.len() == 3 {
            vec![(a[1].clone(), 1), (a[2].clone(), 1)]
        } else if is(*f, s.bits_sub) && a.len() == 3 {
            vec![(a[1].clone(), 1), (a[2].clone(), -1)]
        } else if is(*f, s.bits_neg) && a.len() == 2 {
            vec![(a[1].clone(), -1)]
        } else if is(*f, s.bits_of_int) && a.len() == 2 {
            vec![(a[1].clone(), 1)]
        } else {
            return None;
        };
        Some((m, parts))
    }

    /// `x mod k` (k > 0) of the value x: a fresh variable r, with
    /// x = k q + r, 0 <= r <= k - 1 (q another fresh variable)
    fn modulo(&mut self, t: &Term, x: Lin, k: i128) -> Option<(usize, usize)> {
        let (qt, rt) = (Term::app(u32::MAX, vec![t.clone()]), t.clone());
        let fresh = !self.vars.contains(&rt);
        let (q, r) = (self.var_of(&qt), self.var_of(&rt));
        if fresh {
            // x - k q - r = 0, r >= 0, k - 1 - r >= 0
            let d = x.add(&Lin::var(q), -k)?.add(&Lin::var(r), -1)?;
            self.side.push(d.clone());
            self.side.push(d.scale(-1)?);
            self.side.push(Lin::var(r));
            self.side.push(Lin::konst(k - 1).add(&Lin::var(r), -1)?);
        }
        Some((q, r))
    }

    /// The linear form of the value of `t`.
    fn lin(&mut self, t: &Term) -> Option<Lin> {
        let s = self.s;
        match t.node() {
            Node::Nat(_) => return small(t).map(Lin::konst),
            // pair(1, m): the integer -m (the prelude's negative literals)
            Node::App(p, a) if is(*p, s.pair) && a.len() == 2 && small(&a[0]) == Some(1) && small(&a[1]).is_some_and(|m| m > 0) => {
                return small(&a[1]).map(|m| Lin::konst(-m));
            }
            Node::App(e, a) if a.is_empty() && is(*e, s.empty) => return Some(Lin::konst(0)),
            // succ of a natural is its + 1 (of other sets: a set)
            Node::App(f, a) if is(*f, s.succ) && (small(&a[0]).is_some() || self.nats.contains(&a[0])) => return self.lin(&a[0])?.add(&Lin::konst(1), 1),
            Node::App(f, a) if is(*f, s.int_succ) => return self.lin(&a[0])?.add(&Lin::konst(1), 1),
            Node::App(f, a) if is(*f, s.int_pred) => return self.lin(&a[0])?.add(&Lin::konst(1), -1),
            // the length of a list expression: its singletons plus the
            // lengths of the lists in it (each >= 0)
            Node::App(f, a) if is(*f, self.ls.len) => {
                if let Some(pieces) = super::list::flatten(&self.ls, &a[0], &self.lists) {
                    let mut l = Lin::konst(0);
                    for p in pieces {
                        l = match p {
                            super::list::Piece::One(_) => l.add(&Lin::konst(1), 1)?,
                            super::list::Piece::List(m) => {
                                let v = self.var_of(&Term::app(*f, vec![m]));
                                self.side.push(Lin::var(v));
                                l.add(&Lin::var(v), 1)?
                            }
                        };
                    }
                    return Some(l);
                }
            }
            Node::App(f, a) if is(*f, s.int_add) => return self.lin(&a[0])?.add(&self.lin(&a[1])?, 1),
            Node::App(f, a) if is(*f, s.int_sub) => return self.lin(&a[0])?.add(&self.lin(&a[1])?, -1),
            Node::App(f, a) if is(*f, s.int_neg) => return self.lin(&a[0])?.scale(-1),
            Node::App(f, a) if *f == s.lit_add && small(&a[0]).is_some() && small(&a[1]).is_some() => {
                return self.lin(&a[0])?.add(&self.lin(&a[1])?, 1);
            }
            Node::App(f, a) if is(*f, s.int_mul) => {
                // linear only if one factor is a numeral
                if let Some(k) = small(&a[0]) {
                    return self.lin(&a[1])?.scale(k);
                }
                if let Some(k) = small(&a[1]) {
                    return self.lin(&a[0])?.scale(k);
                }
            }
            Node::App(f, a) if is(*f, s.int_div) || is(*f, s.int_mod) => {
                if let Some(k) = small(&a[1]).filter(|k| *k > 0) {
                    let x = self.lin(&a[0])?;
                    let m = Term::app(s.int_mod.unwrap(), vec![a[0].clone(), a[1].clone()]);
                    let (q, r) = self.modulo(&m, x, k)?;
                    return Some(Lin::var(if is(*f, s.int_div) { q } else { r }));
                }
            }
            _ => {
                if let Some((m, parts)) = self.bits_op(t) {
                    let mut x = Lin::konst(0);
                    for (p, k) in parts {
                        x = x.add(&self.lin(&p)?, k)?;
                    }
                    let (_, r) = self.modulo(t, x, m)?;
                    return Some(Lin::var(r));
                }
            }
        }
        // any other term: its value, an integer variable
        let v = self.var_of(t);
        Some(Lin::var(v))
    }

    /// Reads an atom of the propositional structure.
    fn atom(&mut self, t: &Term) -> Option<Atom> {
        let s = self.s;
        let Node::App(f, a) = t.node() else { return None };
        if a.len() != 2 {
            return None;
        }
        let rel = if *f == s.eq {
            // (sets with equal values need not be equal)
            if !self.is_int(&a[0]) || !self.is_int(&a[1]) {
                return None;
            }
            Rel::Eq
        } else if is(*f, s.int_lt) {
            Rel::Lt
        } else if is(*f, s.int_le) {
            Rel::Le
        } else if *f == s.lit_lt {
            // (on numerals: their order)
            small(&a[0])?;
            small(&a[1])?;
            Rel::Lt
        } else if *f == s.in_ && self.natural(&a[0]) && self.natural(&a[1]) {
            // naturals (von Neumann): membership is the order
            Rel::Lt
        } else if *f == s.in_ {
            let Node::App(o, ob) = a[1].node() else { return None };
            if is(*o, s.int) {
                return self.is_int(&a[0]).then_some(Atom::True);
            }
            if !self.is_int(&a[0]) {
                return None;
            }
            // an integer x: x in omega iff x >= 0; x in bits(k) iff 0 <= x < 2^k
            if is(*o, s.omega) {
                let x = self.lin(&a[0])?;
                return Some(Atom::Range(x, 0, None));
            }
            if is(*o, s.bits) {
                let k = small(&ob[0]).filter(|&k| (0..=100).contains(&k))?;
                let x = self.lin(&a[0])?;
                return Some(Atom::Range(x, 0, Some((1i128 << k) - 1)));
            }
            return None;
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
    // equalities (l >= 0 and -l >= 0): solved for a variable with
    // coefficient ±1 and substituted (exact over the integers, unlike the
    // elimination below)
    'eqs: loop {
        for i in 0..cs.len() {
            let neg = match cs[i].scale(-1) {
                Some(n) => n,
                None => continue,
            };
            let Some(j) = cs.iter().position(|m| *m == neg) else { continue };
            let Some((&v, &cv)) = cs[i].coeffs.iter().find(|(_, c)| c.abs() == 1) else { continue };
            // v = -(l - cv v) / cv: substitute l's solution for v
            let l = cs[i].clone();
            let mut out = Vec::new();
            for (k, m) in cs.iter().enumerate() {
                if k == i || k == j {
                    continue;
                }
                match m.coeffs.get(&v) {
                    // m + (-(m_v / cv)) l removes v
                    Some(&mv) => match m.add(&l, -mv * cv) {
                        Some(mut r) => {
                            r.coeffs.remove(&v);
                            norm(&mut r);
                            out.push(r);
                        }
                        None => return false,
                    },
                    None => out.push(m.clone()),
                }
            }
            cs = out;
            continue 'eqs;
        }
        break;
    }
    loop {
        if cs.iter().any(|l| l.coeffs.is_empty() && l.c < 0) {
            return true;
        }
        cs.retain(|l| !l.coeffs.is_empty());
        cs.dedup();
        // the variable with the fewest new constraints, preferring one whose
        // elimination is exact over the integers (coefficient 1 on one
        // side: with larger ones on both, the real shadow can lose integer
        // infeasibility, e.g. of a quotient `x = 4096 q + r`)
        let mut best: Option<(usize, (bool, usize))> = None;
        let mut vars: Vec<usize> = cs.iter().flat_map(|l| l.coeffs.keys().copied()).collect();
        vars.sort();
        vars.dedup();
        if vars.is_empty() {
            return false;
        }
        for &v in &vars {
            let p = cs.iter().filter(|l| l.coeffs.get(&v).is_some_and(|c| *c > 0)).count();
            let n = cs.iter().filter(|l| l.coeffs.get(&v).is_some_and(|c| *c < 0)).count();
            let exact = cs.iter().all(|l| l.coeffs.get(&v).is_none_or(|c| *c <= 1))
                || cs.iter().all(|l| l.coeffs.get(&v).is_none_or(|c| *c >= -1));
            let cost = (!exact, p * n);
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
                // scaled to the lcm of the two coefficients (not their
                // product: coefficients like 2^64 would overflow)
                let (a, b) = (p.coeffs[&v], -n.coeffs[&v]);
                let g = gcd(a, b);
                let (a, b) = (a / g, b / g);
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

/// The literals of one assignment (with `!=` and ranges split into cases)
/// are infeasible.
fn refuted(lits: &[(Atom, bool)], base: &[Lin], k: usize) -> bool {
    if k == lits.len() {
        return infeasible(base.to_vec());
    }
    let add = |extra: Vec<Lin>| {
        let mut b = base.to_vec();
        b.extend(extra);
        refuted(lits, &b, k + 1)
    };
    let minus1 = |l: &Lin| l.add(&Lin::konst(1), -1).unwrap_or(l.clone());
    match &lits[k] {
        (Atom::Cmp(x, rel, y), val) => {
            let d = y.add(x, -1).unwrap_or(Lin::konst(0)); // y - x
            let dn = x.add(y, -1).unwrap_or(Lin::konst(0)); // x - y
            match (rel, val) {
                (Rel::Lt, true) => add(vec![minus1(&d)]),
                (Rel::Lt, false) => add(vec![dn]),
                (Rel::Le, true) => add(vec![d]),
                (Rel::Le, false) => add(vec![minus1(&dn)]),
                (Rel::Eq, true) => add(vec![d, dn]),
                (Rel::Eq, false) => add(vec![minus1(&d)]) && add(vec![minus1(&dn)]),
            }
        }
        (Atom::Range(x, lo, hi), val) => {
            let above = x.add(&Lin::konst(*lo), -1).unwrap_or(Lin::konst(0)); // x - lo
            let below = hi.map(|h| Lin::konst(h).add(x, -1).unwrap_or(Lin::konst(0))); // hi - x
            if *val {
                add([Some(above), below].into_iter().flatten().collect())
            } else {
                // x < lo, or x > hi
                add(vec![minus1(&above.scale(-1).unwrap_or(Lin::konst(0)))]) && below.is_none_or(|b| add(vec![minus1(&b.scale(-1).unwrap_or(Lin::konst(0)))]))
            }
        }
        (Atom::True, _) => refuted(lits, base, k + 1),
    }
}

impl Logic {
    /// `premises -> goal` holds by propositional logic and linear arithmetic
    /// over the integers (see the module docs).
    pub fn arith(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        let s = Syms::new(env);
        let mut r = Reader {
            s,
            ls: super::list::LSyms::new(env),
            lists: super::list::known_lists(env, premises),
            ints: Vec::new(),
            nats: Vec::new(),
            vars: Vec::new(),
            side: Vec::new(),
        };
        // integers: memberships among the premises, then terms equated to
        // integers (repeat until nothing changes)
        for p in premises {
            if let Some(t) = r.membership(p) {
                if let Node::App(_, a) = p.node() {
                    if matches!(a[1].node(), Node::App(o, _) if is(*o, s.omega) || is(*o, s.bits)) {
                        r.nats.push(t.clone());
                    }
                }
                r.ints.push(t);
            }
        }
        loop {
            let before = r.ints.len();
            for p in premises {
                if let Node::App(e, a) = p.node() {
                    if *e == s.eq && a.len() == 2 {
                        for (x, y) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                            if r.is_int(y) && !r.ints.contains(x) {
                                r.ints.push(x.clone());
                            }
                        }
                    }
                }
            }
            if r.ints.len() == before {
                break;
            }
        }
        let mut f = goal.clone();
        for p in premises.iter().rev() {
            f = Term::app(self.imp, vec![p.clone(), f]);
        }
        let mut atoms: Vec<Term> = Vec::new();
        let tree = self.prop_tree(env, &f, &mut atoms, 0)?;
        let Some(rows) = tree.falsifying_rows(atoms.len(), 20) else {
            return err("arith: too many atoms");
        };
        let read: Vec<Option<Atom>> = atoms.iter().map(|a| r.atom(a)).collect();
        let base: Vec<Lin> = r.side.clone();
        for row in rows {
            let mut lits = Vec::new();
            let mut contradiction = false;
            for (i, a) in read.iter().enumerate() {
                let val = row >> i & 1 == 1;
                match a {
                    Some(Atom::True) if !val => contradiction = true,
                    Some(a) => lits.push((a.clone(), val)),
                    None => {}
                }
            }
            if contradiction {
                continue;
            }
            if !refuted(&lits, &base, 0) {
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
    /// `m + 1`, `int_succ(m)` or `succ(m)`, given `m in omega` (`m_nat`).
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
            Node::App(g, x) if is(*g, s.succ) || is(*g, s.int_succ) => x[0].clone(),
            Node::App(g, x) if is(*g, s.int_add) && matches!(x[1].node(), Node::Nat(k) if k.to_u64() == Some(1)) => x[0].clone(),
            _ => return err("rec: the argument is neither 0 nor m + 1"),
        };
        let omega = s.omega.ok_or_else(|| KernelError("no omega".into()))?;
        let want = Term::app(s.in_, vec![m.clone(), Term::app(omega, vec![])]);
        if m_nat != Some(&want) {
            return err("rec: needs a proof of `m in omega`");
        }
        // (the step's argument: the successor, as the definition has it)
        let prev = Term::app(*f, vec![z.clone(), step.clone(), m.clone()]);
        let body = step.instantiate_params(&[m, prev], &env.binders_fn());
        Ok(env.mk_eq(t.clone(), body))
    }
}
