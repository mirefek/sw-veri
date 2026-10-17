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
//!   `bits_of_int` likewise); the length of a list is in omega; a power
//!   (`int_pow`, `pow2`) is an integer (its definition: a product, or 0).
//!
//! Products of non-constants are read as monomials: the products of their
//! factors' values (sorted), a polynomial normal form (the commutative ring
//! laws). Facts of symbolic divisors and powers are added as premises (see
//! `symbolic_facts`); `pow2(k + c)` (c a numeral, k a known natural) is
//! read as `2^c * pow2(k)` (`int_pow`'s recursion).
//!
//! Equals for equals: the premises' equations between closed terms are
//! merged into classes (congruence closure), and every term is read with
//! each subterm replaced by its class's representative (`eq_subst`); the
//! equations are kept as given too (their arithmetic).
//!
//! `arith(premises, goal)` checks that `premises -> goal` holds whenever
//! each atom is read as true or false and the arithmetic atoms are
//! consistent: for every assignment falsifying it, the arithmetic literals
//! are infeasible over the integers (Fourier-Motzkin elimination with
//! integer tightening: sound, not complete). The assignments are searched
//! by case splits on the atoms the formula still depends on, the values its
//! falsity forces propagated (unit propagation); a branch closes when the
//! formula is true there, a forced value conflicts, or its literals so far
//! are infeasible (every falsifying assignment extends a branch searched,
//! or one closed). Every term in an arithmetic
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
        // (i128::MIN excluded: every form can be negated without overflow)
        if r.c == i128::MIN || r.coeffs.values().any(|c| *c == i128::MIN) {
            return None;
        }
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
    pow2: Option<SymId>,
    int_pow: Option<SymId>,
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
    /// the other word operations, each n-bit (`int_mod(.., 2^n)`, a
    /// `bits_build(n, ..)`, a `bits_of_int(n, ..)`): (symbol, the position of
    /// n among its arguments, its arity)
    words: [Option<(SymId, usize, usize)>; 8],
    bits_shr: Option<SymId>,
    sint: Option<SymId>,
    bit: Option<SymId>,
}

impl Syms {
    fn new(env: &Env) -> Syms {
        let s = |n: &str| env.ksym(n);
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
            pow2: s("pow2"),
            int_pow: s("int_pow"),
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
            words: [("bits_mul", 0, 3), ("bits_shl", 0, 3), ("bits_sar", 0, 3), ("bits_and", 0, 3), ("bits_or", 0, 3), ("bits_xor", 0, 3), ("bits_not", 0, 2), ("bits_sext", 1, 3)]
                .map(|(n, i, k)| s(n).map(|f| (f, i, k))),
            bits_shr: s("bits_shr"),
            sint: s("sint"),
            bit: s("bit"),
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

/// the key of a monomial's variable: its factors (variables), sorted
const MONO: SymId = u32::MAX - 1;

impl Reader {
    /// the factors of variable v (v itself, or a monomial's)
    fn factors(&mut self, v: usize) -> Vec<usize> {
        match self.vars[v].node() {
            Node::App(f, a) if *f == MONO => a.to_vec().iter().map(|t| self.var_of(t)).collect(),
            _ => vec![v],
        }
    }

    /// x * y, a polynomial (each product of variables a monomial's
    /// variable); None if too large (degree above 4, many terms)
    fn mul(&mut self, x: &Lin, y: &Lin) -> Option<Lin> {
        if x.coeffs.len() * y.coeffs.len() > 64 {
            return None;
        }
        let mut r = Lin::konst(x.c.checked_mul(y.c)?);
        r = r.add(&Lin { coeffs: y.coeffs.clone(), c: 0 }, x.c)?;
        r = r.add(&Lin { coeffs: x.coeffs.clone(), c: 0 }, y.c)?;
        for (v, a) in x.coeffs.clone() {
            for (w, b) in y.coeffs.clone() {
                let mut fs = self.factors(v);
                fs.extend(self.factors(w));
                if fs.len() > 4 {
                    return None;
                }
                fs.sort();
                let key = Term::app(MONO, fs.iter().map(|i| self.vars[*i].clone()).collect());
                let m = self.var_of(&key);
                r = r.add(&Lin::var(m), a.checked_mul(b)?)?;
            }
        }
        Some(r)
    }

    /// a numeral's value, or a power of numerals' (`pow2(64)`, `int_pow(2, 32)`)
    fn konst(&self, t: &Term) -> Option<i128> {
        let s = self.s;
        match t.node() {
            Node::App(f, a) if is(*f, s.pow2) && a.len() == 1 => small(&a[0]).filter(|k| (0..=120).contains(k)).map(|k| 1i128 << k),
            Node::App(f, a) if is(*f, s.int_pow) && a.len() == 2 => {
                let (b, k) = (small(&a[0])?, small(&a[1]).filter(|k| (0..=120).contains(k))?);
                b.checked_pow(k as u32)
            }
            _ => small(t),
        }
    }

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
            Node::App(f, a)
                if is(*f, self.ls.len)
                    && (super::list::flatten(&self.ls, &a[0], &self.lists).is_some() || super::list::flatten_known(&self.ls, &a[0], &self.lists).is_some()) =>
            {
                true
            }
            Node::App(f, a) => {
                [s.int_add, s.int_sub, s.int_neg, s.int_mul, s.int_div, s.int_mod, s.int_succ, s.int_pred, s.pow2, s.int_pow].iter().any(|g| is(*f, *g))
                    || self.bits_op(t).is_some()
                    // (a signed value, the other word operations: integers --
                    // a `bits_build(n, ..)` (and, or, xor, not) only of a
                    // natural width n: of bits(n) empty, a choice of nothing)
                    || is(*f, s.sint)
                    || is(*f, s.bits_shr)
                    || s.words.iter().enumerate().any(|(k, w)| {
                        w.is_some_and(|(g, i, _)| g == *f && (!(3..=6).contains(&k) || a.get(i).is_some_and(|n| self.natural(n))))
                    })
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
            // powers of numerals: their values (`pow2(64)`, `int_pow(2, 64)`)
            Node::App(f, a) if is(*f, s.pow2) && small(&a[0]).is_some_and(|k| (0..=120).contains(&k)) => return Some(Lin::konst(1i128 << small(&a[0])?)),
            Node::App(f, a) if is(*f, s.int_pow) && small(&a[0]).is_some() && small(&a[1]).is_some_and(|k| (0..=120).contains(&k)) => {
                let (b, k) = (small(&a[0])?, small(&a[1])? as u32);
                return b.checked_pow(k).map(Lin::konst);
            }
            // pow2(k + c), k a natural: 2^c pow2(k)
            Node::App(f, a) if is(*f, s.pow2) && matches!(a[0].node(), Node::App(p, b) if is(*p, s.int_add) && b.len() == 2
                && small(&b[1]).is_some_and(|c| (0..=64).contains(&c)) && self.natural(&b[0])) =>
            {
                let Node::App(_, b) = a[0].node() else { unreachable!() };
                let p = Term::app(*f, vec![b[0].clone()]);
                return self.lin(&p)?.scale(1i128 << small(&b[1])?);
            }
            Node::App(f, a) if is(*f, s.int_pred) => return self.lin(&a[0])?.add(&Lin::konst(1), -1),
            // the length of a list expression: its singletons plus the
            // lengths of the lists in it (each >= 0)
            Node::App(f, a) if is(*f, self.ls.len) => {
                // (a known concatenation whole when its pieces are not all known)
                if let Some(pieces) = super::list::flatten(&self.ls, &a[0], &self.lists).or_else(|| super::list::flatten_known(&self.ls, &a[0], &self.lists)) {
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
            // the signed value of n bits (`sint(n, a)`, a numeral n): x - 2^n *
            // (x div 2^(n-1)), x = a mod 2^n -- its definition, x below 2^n
            Node::App(f, a) if is(*f, s.sint) && a.len() == 2 && small(&a[0]).is_some_and(|n| (1..=64).contains(&n)) => {
                let n = small(&a[0])?;
                let x = self.lin(&a[1])?;
                let bx = Term::app(s.bits_of_int?, vec![a[0].clone(), a[1].clone()]);
                // (an n-bit operation's value already below 2^n: itself)
                let r = match (self.bits_op(&a[1]), x.coeffs.len(), x.c) {
                    (Some((m, _)), 1, 0) if m == 1i128 << n && x.coeffs.values().all(|c| *c == 1) => *x.coeffs.keys().next().unwrap(),
                    _ => self.modulo(&bx, x, 1i128 << n)?.1,
                };
                // (x mod 2^(n-1), keyed as that term: its quotient is x's top bit)
                let key = Term::app(s.int_mod?, vec![bx.clone(), Term::nat(crate::nat::Nat::from_u128(1u128 << (n - 1)))]);
                let (q, _) = self.modulo(&key, Lin::var(r), 1i128 << (n - 1))?;
                return Lin::var(r).add(&Lin::var(q), -(1i128 << n));
            }
            Node::App(f, a) if *f == s.lit_add && small(&a[0]).is_some() && small(&a[1]).is_some() => {
                return self.lin(&a[0])?.add(&self.lin(&a[1])?, 1);
            }
            Node::App(f, a) if is(*f, s.int_mul) => {
                // linear only if one factor is a numeral (or a power of numerals)
                if let Some(k) = self.konst(&a[0]) {
                    return self.lin(&a[1])?.scale(k);
                }
                if let Some(k) = self.konst(&a[1]) {
                    return self.lin(&a[0])?.scale(k);
                }
                // (else a polynomial: monomials)
                let (x, y) = (self.lin(&a[0])?, self.lin(&a[1])?);
                if let Some(p) = self.mul(&x, &y) {
                    return Some(p);
                }
            }
            Node::App(f, a) if is(*f, s.int_div) || is(*f, s.int_mod) => {
                if let Some(k) = self.konst(&a[1]).filter(|k| *k > 0) {
                    let x = self.lin(&a[0])?;
                    // (keyed by the divisor's value: `pow2(32)` is 4294967296)
                    let m = Term::app(s.int_mod.unwrap(), vec![a[0].clone(), Term::nat(crate::nat::Nat::from_u128(k as u128))]);
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
        // any other term: its value, an integer variable -- of an n-bit word
        // operation, in 0 .. 2^n - 1 (`bits_shr(n, a, k)`, a numeral k: the
        // n-bit a divided)
        let fresh = !self.vars.contains(t);
        let v = self.var_of(t);
        if fresh {
            if let Node::App(f, a) = t.node() {
                let width = s.words.iter().flatten().find(|(g, _, k)| g == f && a.len() == *k).and_then(|(_, i, _)| small(&a[*i]));
                let width = width.or_else(|| (is(*f, s.bits_shr) && a.len() == 3 && small(&a[2]).is_some()).then(|| small(&a[0])).flatten());
                if let Some(n) = width.filter(|n| (0..=100).contains(n)) {
                    self.side.push(Lin::var(v));
                    self.side.push(Lin::konst((1i128 << n) - 1).add(&Lin::var(v), -1)?);
                }
            }
        }
        Some(Lin::var(v))
    }

    /// Reads an atom of the propositional structure.
    fn atom(&mut self, t: &Term) -> Option<Atom> {
        let s = self.s;
        let Node::App(f, a) = t.node() else { return None };
        if a.len() != 2 {
            return None;
        }
        // bit k of a value (`bit(x, k)`, a numeral k): (x div 2^k) mod 2 = 1,
        // its definition
        if is(*f, s.bit) {
            let k = small(&a[1]).filter(|k| (0..=100).contains(k))?;
            let d = Term::app(s.int_div?, vec![a[0].clone(), Term::nat(crate::nat::Nat::from_u128(1u128 << k))]);
            let m = Term::app(s.int_mod?, vec![d, Term::nat(crate::nat::Nat::from_u64(2))]);
            let x = self.lin(&m)?;
            return Some(Atom::Cmp(x, Rel::Eq, Lin::konst(1)));
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

    /// (diagnostics) why `atom` did not read t arithmetically: t is then a
    /// mere proposition to the check
    fn unread_reason(&self, env: &Env, t: &Term) -> String {
        let s = self.s;
        let pr = crate::syntax::Printer::new(env);
        let not_int = |x: &Term| format!("`{}` not known to be an integer (give `{} in omega` / `in bits(n)` / `in int`, or an equation with an integer)", pr.short(x), pr.short(x));
        let Node::App(f, a) = t.node() else { return "not arithmetic: a variable proposition".into() };
        if a.len() != 2 {
            return "not arithmetic: a proposition".into();
        }
        if is(*f, s.bit) {
            return match small(&a[1]) {
                Some(_) => "not arithmetic: a bit beyond 2^100".into(),
                None => "not arithmetic: a bit at a symbolic index (core/bits.core's lemmas, `bitwise`)".into(),
            };
        }
        if *f == s.eq {
            return match (self.is_int(&a[0]), self.is_int(&a[1])) {
                (false, _) => format!("an equation, not arithmetic: {}", not_int(&a[0])),
                (_, false) => format!("an equation, not arithmetic: {}", not_int(&a[1])),
                _ => "an equation of integers whose terms arith cannot read (a coefficient too large?)".into(),
            };
        }
        if *f == s.lit_lt {
            return "not arithmetic: `lit_lt` of non-numerals".into();
        }
        if *f == s.in_ {
            let Node::App(o, ob) = a[1].node() else { return "not arithmetic: membership in a variable set".into() };
            if !(is(*o, s.omega) || is(*o, s.bits) || is(*o, s.int)) {
                return "not arithmetic: membership in a set other than omega, int, bits(k)".into();
            }
            if !self.is_int(&a[0]) {
                return format!("a membership, not arithmetic: {}", not_int(&a[0]));
            }
            if is(*o, s.bits) && small(&ob[0]).is_none_or(|k| !(0..=100).contains(&k)) {
                return "a membership in bits(n), n not a numeral up to 100: read only through `x in bits(n) <-> x in omega && x < pow2(n)`".into();
            }
        }
        if is(*f, s.int_lt) || is(*f, s.int_le) || *f == s.in_ {
            return "a comparison whose terms arith cannot read (a coefficient too large?)".into();
        }
        "not arithmetic: a proposition".into()
    }
}

/// Fourier-Motzkin: is `{ l >= 0 : l in cs }` infeasible over the integers?
/// (Unknown is reported as feasible.)
fn infeasible(mut cs: Vec<Lin>, limit: usize) -> bool {
    // (coefficients are never i128::MIN: `Lin::add`)
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
                    Some(&mv) => match mv.checked_neg().and_then(|n| n.checked_mul(cv)).and_then(|f| m.add(&l, f)) {
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
        if rest.len() > limit {
            return false;
        }
        cs = rest;
    }
}

/// The literals of one assignment (with `!=` and ranges split into cases)
/// are infeasible.
fn refuted(lits: &[(Atom, bool)], base: &[Lin], k: usize, limit: usize) -> bool {
    if k == lits.len() {
        return infeasible(base.to_vec(), limit);
    }
    let add = |extra: Vec<Lin>| {
        let mut b = base.to_vec();
        b.extend(extra);
        refuted(lits, &b, k + 1, limit)
    };
    // (a constraint whose form overflows: none -- weaker, never wrong)
    let minus1 = |l: Option<Lin>| l.and_then(|l| l.add(&Lin::konst(1), -1));
    let some = |ls: Vec<Option<Lin>>| ls.into_iter().flatten().collect::<Vec<Lin>>();
    match &lits[k] {
        (Atom::Cmp(x, rel, y), val) => {
            let d = || y.add(x, -1); // y - x
            let dn = || x.add(y, -1); // x - y
            match (rel, val) {
                (Rel::Lt, true) => add(some(vec![minus1(d())])),
                (Rel::Lt, false) => add(some(vec![dn()])),
                (Rel::Le, true) => add(some(vec![d()])),
                (Rel::Le, false) => add(some(vec![minus1(dn())])),
                (Rel::Eq, true) => add(some(vec![d(), dn()])),
                (Rel::Eq, false) => add(some(vec![minus1(d())])) && add(some(vec![minus1(dn())])),
            }
        }
        (Atom::Range(x, lo, hi), val) => {
            let above = || x.add(&Lin::konst(*lo), -1); // x - lo
            let below = |h: i128| Lin::konst(h).add(x, -1); // hi - x
            if *val {
                add(some(vec![above(), hi.and_then(below)]))
            } else {
                // x < lo, or x > hi
                add(some(vec![minus1(above().and_then(|a| a.scale(-1)))])) && hi.is_none_or(|h| add(some(vec![minus1(below(h).and_then(|b| b.scale(-1)))])))
            }
        }
        (Atom::True, _) => refuted(lits, base, k + 1, limit),
    }
}

/// No assignment extending `asg` falsifies the tree with feasible
/// arithmetic literals; else such a (partial) assignment, or None when the
/// budget of cases runs out. `newly`: the atoms assigned since the last
/// arithmetic check.
fn falsify(tree: &super::prop::PTree, read: &[Option<Atom>], base: &[Lin], mut asg: Vec<Option<bool>>, newly: &[usize], connected: bool, budget: &mut usize) -> Result<(), Option<Vec<Option<bool>>>> {
    if *budget == 0 {
        return Err(None);
    }
    *budget -= 1;
    // the values the tree's falsity forces
    let mut new = newly.to_vec();
    if !tree.propagate(&mut asg, &mut new) {
        return Ok(());
    }
    if tree.eval3(&asg) == Some(true) {
        return Ok(());
    }
    // the literals so far: infeasible closes the branch (checked again when
    // an arithmetic atom was assigned; before a leaf, within a small budget)
    let new_lit = new.iter().any(|&i| read[i].is_some());
    let pick = if connected { tree.pick_connected(&asg) } else { tree.pick(&asg) };
    let mut lits = Vec::new();
    for (i, a) in read.iter().enumerate() {
        let Some(v) = asg[i] else { continue };
        match a {
            Some(Atom::True) if !v => return Ok(()),
            Some(a) => lits.push((a.clone(), v)),
            None => {}
        }
    }
    let limit = if pick.is_some() { 200 } else { 20_000 };
    if (new_lit || pick.is_none()) && refuted(&lits, base, 0, limit) {
        return Ok(());
    }
    let Some(i) = pick else {
        return Err(Some(asg));
    };
    for b in [true, false] {
        let mut a2 = asg.clone();
        a2[i] = Some(b);
        falsify(tree, read, base, a2, &[i], connected, budget)?;
    }
    Ok(())
}

/// Facts about word operations of a symbolic width n (arith reads only
/// literal widths and moduli), for the closed terms occurring in
/// `premises` and `goal` -- standard facts of the prelude's arithmetic:
/// * `bits_add(n, a, b) = int_mod(int_add(a, b), pow2(n))` (likewise
///   `bits_sub`, `bits_of_int`: their definitions);
/// * `n in omega -> int_lt(0, pow2(n))`;
/// * for r = `int_mod(x, m)`, m not a numeral: `int_lt(0, m) -> int_le(0, r)
///   && int_lt(r, m)`, and `int_le(0, x) && int_lt(x, m) -> int_le(r, x) &&
///   int_le(x, r)` (Euclidean division; the remainder of a value in 0 .. m
///   - 1 is that value -- compared as values: x need not be an integer);
/// * for q = `int_div(x, m)`, m not a numeral: `int_le(0, x) && int_lt(x, m)
///   -> q = 0`, `int_lt(0, m) && int_le(m, x) && int_lt(x, 2 * m) -> q = 1`
///   (Euclidean division: x = m * 0 + x, x = m * 1 + (x - m));
/// * for q = `int_div(x, m)`, r = `int_mod(x, m)`, m not a constant:
///   `int_lt(0, m) -> x = m * q + r` (Euclidean division);
/// * for a product `int_mul(a, b)` of non-constants: `int_le(0, a) &&
///   int_le(0, b) -> int_le(0, int_mul(a, b))` (the ordered ring);
/// * `k in omega -> pow2(k + 1) = 2 * pow2(k)` (`int_pow`'s recursion);
/// * `x in bits(n) <-> x in omega && int_lt(x, pow2(n))` (`bits`'s definition).
fn symbolic_facts(env: &Env, premises: &[Term], goal: &Term) -> Vec<Term> {
    let g = |n: &str| env.ksym(n);
    let (Some(imod), Some(lt), Some(le), Some(pow2), Some(and), Some(iff), Some(inn), Some(omega), Some(bits), Some(iadd), Some(isub)) =
        (g("int_mod"), g("int_lt"), g("int_le"), g("pow2"), g("and"), g("iff"), g("in"), g("omega"), g("bits"), g("int_add"), g("int_sub"))
    else {
        return Vec::new();
    };
    let (badd, bsub, boi, idiv, imul) = (g("bits_add"), g("bits_sub"), g("bits_of_int"), g("int_div"), g("int_mul"));
    let bf = env.binders_fn();
    // (a numeral, or a power of numerals: what arith reads as a constant)
    let ipow = g("int_pow");
    let constant = |t: &Term| match t.node() {
        Node::Nat(_) => true,
        Node::App(f, a) if (*f == pow2 || Some(*f) == ipow) && a.iter().all(|x| small(x).is_some()) => small(a.last().unwrap()).is_some_and(|k| k <= 120),
        _ => false,
    };
    // (the closed subterms with these heads, each once)
    let heads: Vec<SymId> = [Some(imod), Some(pow2), Some(inn), badd, bsub, boi, idiv, imul].into_iter().flatten().collect();
    let mut seen = std::collections::HashSet::new();
    let mut terms: Vec<Term> = Vec::new();
    fn collect(t: &Term, heads: &[SymId], bf: &dyn Fn(SymId, usize) -> u32, seen: &mut std::collections::HashSet<Term>, out: &mut Vec<Term>) {
        if let Node::App(f, a) = t.node() {
            if heads.contains(f) && t.loose_depth(bf) == 0 && seen.insert(t.clone()) {
                out.push(t.clone());
            }
            a.iter().for_each(|x| collect(x, heads, bf, seen, out));
        }
    }
    for p in premises.iter().chain([goal]) {
        collect(p, &heads, &bf, &mut seen, &mut terms);
    }
    let zero = Term::nat(crate::nat::Nat::zero());
    let app = |s: SymId, a: Vec<Term>| Term::app(s, a);
    let imp = |a: Term, b: Term| Term::app(env.builtins.imp, vec![a, b]);
    let eq = |a: Term, b: Term| Term::app(env.builtins.eq, vec![a, b]);
    let mut out = Vec::new();
    let mut mods = Vec::new();
    for t in &terms {
        let Node::App(f, a) = t.node() else { continue };
        let wide = |w: &Term| small(w).is_none();
        if Some(*f) == badd && a.len() == 3 && wide(&a[0]) {
            let m = app(imod, vec![app(iadd, vec![a[1].clone(), a[2].clone()]), app(pow2, vec![a[0].clone()])]);
            out.push(eq(t.clone(), m.clone()));
            mods.push(m);
        } else if Some(*f) == bsub && a.len() == 3 && wide(&a[0]) {
            let m = app(imod, vec![app(isub, vec![a[1].clone(), a[2].clone()]), app(pow2, vec![a[0].clone()])]);
            out.push(eq(t.clone(), m.clone()));
            mods.push(m);
        } else if Some(*f) == boi && a.len() == 2 && wide(&a[0]) {
            let m = app(imod, vec![a[1].clone(), app(pow2, vec![a[0].clone()])]);
            out.push(eq(t.clone(), m.clone()));
            mods.push(m);
        } else if *f == pow2 && a.len() == 1 && wide(&a[0]) {
            out.push(imp(app(inn, vec![a[0].clone(), app(omega, vec![])]), app(lt, vec![zero.clone(), t.clone()])));
            // (pow2(k + 1): twice pow2(k))
            if let (Node::App(p, s), Some(mul)) = (a[0].node(), imul) {
                if *p == iadd && s.len() == 2 && small(&s[1]) == Some(1) {
                    let k = s[0].clone();
                    let two = Term::nat(crate::nat::Nat::from_u64(2));
                    // (as two comparisons: values, pow2(..) not read as an integer in an equation)
                    let d = app(mul, vec![two, app(pow2, vec![k.clone()])]);
                    let both = app(and, vec![app(le, vec![t.clone(), d.clone()]), app(le, vec![d, t.clone()])]);
                    out.push(imp(app(inn, vec![k, app(omega, vec![])]), both));
                }
            }
        } else if Some(*f) == imul && a.len() == 2 && !constant(&a[0]) && !constant(&a[1]) {
            let both = app(and, vec![app(le, vec![zero.clone(), a[0].clone()]), app(le, vec![zero.clone(), a[1].clone()])]);
            out.push(imp(both, app(le, vec![zero.clone(), t.clone()])));
        } else if Some(*f) == idiv && a.len() == 2 && small(&a[1]).is_none() {
            let (x, m) = (a[0].clone(), a[1].clone());
            if !constant(&m) {
                mods.push(app(imod, vec![x.clone(), m.clone()]));
            }
            let one = Term::nat(crate::nat::Nat::from_u64(1));
            let two = Term::nat(crate::nat::Nat::from_u64(2));
            let below = app(and, vec![app(le, vec![zero.clone(), x.clone()]), app(lt, vec![x.clone(), m.clone()])]);
            out.push(imp(below, eq(t.clone(), zero.clone())));
            if let Some(mul) = imul {
                let once = app(and, vec![app(lt, vec![zero.clone(), m.clone()]), app(and, vec![app(le, vec![m.clone(), x.clone()]), app(lt, vec![x.clone(), app(mul, vec![two, m.clone()])])])]);
                out.push(imp(once, eq(t.clone(), one)));
            }
        } else if *f == imod && a.len() == 2 && small(&a[1]).is_none() {
            mods.push(t.clone());
        } else if *f == inn && a.len() == 2 {
            if let Node::App(b, w) = a[1].node() {
                if *b == bits && w.len() == 1 && wide(&w[0]) {
                    let p2 = app(pow2, vec![w[0].clone()]);
                    let rhs = app(and, vec![app(inn, vec![a[0].clone(), app(omega, vec![])]), app(lt, vec![a[0].clone(), p2.clone()])]);
                    out.push(app(iff, vec![t.clone(), rhs]));
                    if seen.insert(p2.clone()) {
                        out.push(imp(app(inn, vec![w[0].clone(), app(omega, vec![])]), app(lt, vec![zero.clone(), p2])));
                    }
                }
            }
        }
    }
    let mut done = std::collections::HashSet::new();
    for r in mods {
        if !done.insert(r.clone()) {
            continue;
        }
        let Node::App(_, a) = r.node() else { continue };
        let (x, m) = (a[0].clone(), a[1].clone());
        // (x = m q + r, as two comparisons of values)
        if let (Some(mul), false) = (imul, constant(&m)) {
            let e = app(iadd, vec![app(mul, vec![m.clone(), app(idiv.unwrap(), vec![x.clone(), m.clone()])]), r.clone()]);
            let both = app(and, vec![app(le, vec![x.clone(), e.clone()]), app(le, vec![e, x.clone()])]);
            out.push(imp(app(lt, vec![zero.clone(), m.clone()]), both));
        }
        if let Node::App(p, w) = m.node() {
            if *p == pow2 && wide(&w[0]) {
                out.push(imp(app(inn, vec![w[0].clone(), app(omega, vec![])]), app(lt, vec![zero.clone(), m.clone()])));
            }
        }
        let range = app(and, vec![app(le, vec![zero.clone(), r.clone()]), app(lt, vec![r.clone(), m.clone()])]);
        out.push(imp(app(lt, vec![zero.clone(), m.clone()]), range));
        // (on values: x need not be an integer, the remainder is its value)
        let small_x = app(and, vec![app(le, vec![zero.clone(), x.clone()]), app(lt, vec![x.clone(), m.clone()])]);
        let same = app(and, vec![app(le, vec![r.clone(), x.clone()]), app(le, vec![x, r.clone()])]);
        out.push(imp(small_x, same));
    }
    out
}

/// `l = r` between closed terms: (l, r)
fn equation(env: &Env, t: &Term) -> Option<(Term, Term)> {
    match t.node() {
        Node::App(e, a) if *e == env.builtins.eq && a.len() == 2 => {
            let bf = env.binders_fn();
            (a[0].loose_depth(&bf) == 0 && a[1].loose_depth(&bf) == 0).then(|| (a[0].clone(), a[1].clone()))
        }
        _ => None,
    }
}

/// Equal terms: classes of the premises' equations between closed terms,
/// each with a representative (the smallest, a numeral first); a term read
/// with each subterm replaced by its class's representative (bottom up, so
/// that f(a) and f(b) are one class when a and b are).
struct Congruence {
    rep: std::collections::HashMap<Term, Term>,
    /// the heads of the classes' members (only terms with one are looked up)
    heads: std::collections::HashSet<(bool, u32)>,
    /// canon's results by node identity (the terms read share subterms)
    memo: std::cell::RefCell<std::collections::HashMap<usize, (Term, Term)>>,
}

impl Congruence {
    fn of(env: &Env, premises: &[Term]) -> Congruence {
        let eqs: Vec<(Term, Term)> = premises.iter().filter_map(|p| equation(env, p)).collect();
        let mut cc = Congruence { rep: Default::default(), heads: Default::default(), memo: Default::default() };
        for _ in 0..20 {
            cc.memo.borrow_mut().clear();
            let mut changed = false;
            for (l, r) in &eqs {
                let (a, b) = (cc.canon(l), cc.canon(r));
                if a != b {
                    let (big, small) = if size(&a) < size(&b) { (b, a) } else { (a, b) };
                    cc.heads.insert(head_key(&big));
                    cc.rep.insert(big, small);
                    cc.memo.borrow_mut().clear();
                    changed = true;
                }
            }
            // (an entry whose arguments' classes changed: also under its
            // arguments' representatives -- f(a), f(b) one class)
            let entries: Vec<(Term, Term)> = cc.rep.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
            for (k, v) in entries {
                let k2 = match k.node() {
                    Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => k.with_args(a.iter().map(|x| cc.canon(x)).collect()),
                    _ => continue,
                };
                let v2 = cc.canon(&v);
                if k2 != k && k2 != v2 && !cc.rep.contains_key(&k2) {
                    cc.heads.insert(head_key(&k2));
                    cc.rep.insert(k2, v2);
                    cc.memo.borrow_mut().clear();
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        cc
    }

    fn find(&self, t: &Term) -> Term {
        let mut t = t.clone();
        for _ in 0..1000 {
            match self.rep.get(&t) {
                Some(r) => t = r.clone(),
                None => break,
            }
        }
        t
    }

    fn canon(&self, t: &Term) -> Term {
        if self.rep.is_empty() {
            return t.clone();
        }
        if let Some((k, v)) = self.memo.borrow().get(&t.ptr_id()) {
            // (the same node: its key kept alive, so the address is its)
            if k.ptr_eq(t) {
                return v.clone();
            }
        }
        let t2 = match t.node() {
            Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => t.with_args(a.iter().map(|x| self.canon(x)).collect()),
            _ => t.clone(),
        };
        let r = if self.heads.contains(&head_key(&t2)) { self.find(&t2) } else { t2 };
        self.memo.borrow_mut().insert(t.ptr_id(), (t.clone(), r.clone()));
        r
    }
}

/// a term's head: (a variable?, its symbol or variable); a numeral (0, u32::MAX)
fn head_key(t: &Term) -> (bool, u32) {
    match t.node() {
        Node::App(f, _) => (false, *f),
        Node::Var(v, _) => (true, *v),
        _ => (false, u32::MAX),
    }
}

/// a term's size (a numeral smallest: preferred as a representative)
fn size(t: &Term) -> usize {
    match t.node() {
        Node::Nat(_) => 0,
        Node::App(_, a) | Node::Var(_, a) => 1 + a.iter().map(size).sum::<usize>(),
        _ => 1,
    }
}

fn wide(w: &Term) -> bool {
    small(w).is_none()
}

impl Logic {
    /// `premises -> goal` holds by propositional logic and linear arithmetic
    /// over the integers (see the module docs).
    pub fn arith(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        crate::ext::inventory::measure("arith", env, goal, || self.arith_(env, premises, goal))
    }

    fn arith_(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        // (closed terms by their values: `PAGE` by 4096 in `int_div(a, PAGE)`;
        // a closed equation of distinct literals false: `!("a" = "b")`)
        let gs = self.ground_facts(env, &premises.iter().chain([goal]).cloned().collect::<Vec<_>>());
        let subst: Vec<(Term, Term)> = gs
            .iter()
            .filter_map(|g| match g.node() {
                // (a term arith reads only as an atom -- not its own
                // arithmetic, `pow2(32)` --, with a value it reads: below 2^96)
                Node::App(e, a)
                    if *e == env.builtins.eq
                        && a.len() == 2
                        && !matches!(a[0].node(), Node::App(f, _) if ARITH_NATIVE.contains(&env.kname(*f)))
                        && matches!(a[1].node(), Node::Nat(v) if v.to_u128().is_some_and(|v| v < 1u128 << 96)) =>
                {
                    Some((a[0].clone(), a[1].clone()))
                }
                _ => None,
            })
            .collect();
        let ground: Vec<Term> = gs.iter().filter(|g| !matches!(g.node(), Node::App(e, _) if *e == env.builtins.eq)).cloned().collect();
        let mut given: Vec<Term> = premises.iter().map(|p| replace_ground(p, &subst)).collect();
        given.extend(ground);
        let goal = &replace_ground(goal, &subst);
        let premises = &given[..];
        // (equals for equals: the terms read by their classes' representatives,
        // the equations also as given)
        let cc = Congruence::of(env, premises);
        let mut ps: Vec<Term> = premises.iter().map(|p| cc.canon(p)).collect();
        for p in premises {
            if equation(env, p).is_some() && !ps.contains(p) {
                ps.push(p.clone());
            }
        }
        let goal = &cc.canon(goal);
        // (words of a symbolic width: the standard facts, as premises)
        let sf: Vec<Term> = symbolic_facts(env, &ps, goal).iter().map(|f| cc.canon(f)).collect();
        let mut ext = ps;
        ext.extend(sf);
        let premises = &ext[..];
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
        let read: Vec<Option<Atom>> = atoms.iter().map(|a| r.atom(a)).collect();
        let base: Vec<Lin> = r.side.clone();
        // the assignments falsifying the formula, by case splits on the atoms
        // it depends on: each branch closed when the formula is true there,
        // or when its arithmetic literals are infeasible
        // (splits left to right first; if that takes too many cases, splits
        // connected to the case at hand first)
        let mut budget = 500usize;
        let mut res = falsify(&tree, &read, &base, vec![None; atoms.len()], &[], false, &mut budget);
        if matches!(res, Err(None)) {
            let mut budget = 100_000usize;
            res = falsify(&tree, &read, &base, vec![None; atoms.len()], &[], true, &mut budget);
        }
        match res {
            Ok(()) => Ok(()),
            Err(None) => err("arith: too many cases"),
            Err(Some(asg)) => {
                // (the case's atoms, one per line; those not read
                // arithmetically marked, with why: the usual cause of a
                // surprise)
                let pr = crate::syntax::Printer::new(env);
                let lines: Vec<String> = atoms
                    .iter()
                    .enumerate()
                    .filter_map(|(i, a)| {
                        let v = asg[i]?;
                        // (an equation made trivial by the equals substituted: not shown)
                        if matches!(a.node(), Node::App(e, x) if *e == env.builtins.eq && x.len() == 2 && x[0] == x[1]) {
                            return None;
                        }
                        let why = match read[i] {
                            None => format!("    [{}]", r.unread_reason(env, a)),
                            Some(_) => String::new(),
                        };
                        Some(format!("  {} = {}{}", pr.term(a), if v { "true" } else { "false" }, why))
                    })
                    .collect();
                err(format!("arith: not shown; a consistent case:\n{}", lines.join("\n")))
            }
        }
    }

    /// The recursion equations of `nat_rec` for `t = nat_rec(z, k v. s, n)`:
    /// `t = z` if n is 0; `t = s(m, nat_rec(z, k v. s, m))` if n is
    /// `m + 1`, `int_succ(m)` or `succ(m)`, given `m in omega` (`m_nat`).
    pub fn nat_rec_eq(&self, env: &Env, t: &Term, m_nat: Option<&Term>) -> KResult<Term> {
        let rec = env.ksym("nat_rec");
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

/// t with the closed terms of `subst` replaced by their values (outermost
/// first; closed terms have no bound variables, so no shifting)
fn replace_ground(t: &Term, subst: &[(Term, Term)]) -> Term {
    if subst.is_empty() {
        return t.clone();
    }
    if let Some((_, v)) = subst.iter().find(|(c, _)| c == t) {
        return v.clone();
    }
    match t.node() {
        Node::App(f, a) => {
            let b: Vec<Term> = a.iter().map(|x| replace_ground(x, subst)).collect();
            if b.iter().zip(a.iter()).all(|(x, y)| x == y) {
                t.clone()
            } else {
                Term::app(*f, b)
            }
        }
        _ => t.clone(),
    }
}

/// the operations arith reads itself (their closed terms not replaced by
/// values: the reading is already exact)
const ARITH_NATIVE: &[&str] = &["int_add", "int_sub", "int_neg", "int_mul", "int_div", "int_mod", "int_pow", "pow2", "bits_add", "bits_sub", "bits_of_int", "bits_neg"];
