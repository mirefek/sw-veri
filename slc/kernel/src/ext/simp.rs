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
//! * `n in omega` is true for a numeral n (`lit_nat`);
//! * `a = a` is true; distinct numeric or string literals are unequal
//!   (numerals by `lit_*`, strings by `bytes_len`/`bytes_at`);
//! * `pair(a, b) = pair(c, d) <-> a = c && b = d`, likewise for `ok`,
//!   `exc`, `diverge`; outcomes built with different constructors differ;
//!   `tag(k, v)`, `some(x)`, `none` are the pairs `pair(k, v)`,
//!   `pair(1, x)`, `pair(0, empty)` (definitions);
//! * `ex x. .. && x = t && ..` <-> the rest with `t` for x (x not in t),
//!   `all x. x = t -> P(x)` <-> `P(t)`; `ex x. P` <-> P when x does not
//!   occur (the universe is not empty);
//! * the definitions of `bind_rel`, `any_rel`, `is_ok`, `ne`.
//!
//! One implication, used only where weakening is sound (positive positions
//! of a fact being simplified, never in a goal):
//! * `runs(mkprog(s o. R), S, O) -> R(S, O)` (membership in `mkprog`; the
//!   converse also needs `pair(S, O) in univ(1)`).
//!
//! Rules: a path literal `all xs. A1 -> .. -> An -> C` whose hypotheses
//! match literals of the path (or follow from them by taut/arith), with
//! every x bound, adds its instance of C to the path (∀- and →-elimination);
//! for an equation C (possibly n = 0), xs may also be bound by matching its
//! left side against terms of the path or goal. The goal is rewritten with
//! the path's equations `x = t` / `t = x` (x a variable) and `a = b` (left
//! to right).
//!
//! Loops, with invariants given by the user (`simp_prove_loops`): a literal
//! `while_rel(l0, l. C, l o. B, l. T, r)` on a path is replaced by what the
//! theorems `while_inv` / `while_var` (core/loop.core) conclude, once their
//! premises are shown by `simp` itself, on that path.

use super::prop::Logic;
use crate::env::{Env, SymKind};
use crate::term::{Node, SymId, Term};

mod eval;

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
    set_select: Option<SymId>,
    in_: Option<SymId>,
    omega: Option<SymId>,
    tag: Option<SymId>,
    some: Option<SymId>,
    none: Option<SymId>,
    empty: Option<SymId>,
}

fn is(s: SymId, o: Option<SymId>) -> bool {
    o == Some(s)
}

struct Simp<'a> {
    env: &'a Env,
    s: Syms,
    /// arithmetic definitions computed on numerals
    arith: std::collections::HashMap<SymId, &'static str>,
}

/// The arithmetic and bitwise definitions of the prelude that `simp`
/// computes on numerals (their values follow from the definitions and the
/// `lit_*` axioms; words up to 128 bits).
const ARITH: &[&str] = &[
    "nat_add", "nat_mul", "nat_sub", "nat_div", "nat_mod", "nat_pow", "pow2", "bits_of_nat", "bits_add", "bits_sub", "bits_neg", "bits_mul",
    "bits_not", "bits_and", "bits_or", "bits_xor", "bits_shl", "bits_shr", "bits_slice", "nat_and", "nat_or", "lit_add", "lit_mul",
    "lit_sub", "lit_div", "lit_mod", "succ", "int_mod", "int_div",
];

/// Numerals: arithmetic on literal arguments (None: not all literals, or
/// out of range)
fn compute(op: &str, a: &[Term]) -> Option<Term> {
    use crate::nat::Nat;
    let n = |i: usize| -> Option<Nat> {
        match a.get(i)?.node() {
            Node::Nat(v) => Some(v.clone()),
            _ => None,
        }
    };
    let u = |i: usize| n(i).and_then(|v| v.to_u128());
    let w = |i: usize| u(i).filter(|&v| v <= 128).map(|v| v as u32);
    let mask = |bits: u32| if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
    let t = |v: Nat| Some(Term::nat(v));
    let tu = |v: u128| Some(Term::nat(Nat::from_u128(v)));
    match op {
        "nat_add" | "lit_add" => t(n(0)?.add(&n(1)?)),
        "nat_mul" | "lit_mul" => t(n(0)?.mul(&n(1)?)),
        "nat_sub" | "lit_sub" => t(n(0)?.sub(&n(1)?)?),
        "nat_div" | "lit_div" => t(n(0)?.divmod(&n(1)?)?.0),
        "nat_mod" | "lit_mod" => t(n(0)?.divmod(&n(1)?)?.1),
        "succ" => t(n(0)?.add(&Nat::from_u64(1))),
        "nat_pow" => {
            let (b, e) = (n(0)?, u(1)?);
            if e > 256 {
                return None;
            }
            let mut r = Nat::from_u64(1);
            for _ in 0..e {
                r = r.mul(&b);
            }
            t(r)
        }
        "pow2" => {
            let e = u(0)?;
            if e > 256 {
                return None;
            }
            t(Nat::pow2(e as u64))
        }
        "bits_of_nat" => {
            let k = u(0)?;
            if k > 256 {
                return None;
            }
            t(n(1)?.divmod(&Nat::pow2(k as u64))?.1)
        }
        "bits_add" => tu(u(1)?.wrapping_add(u(2)?) & mask(w(0)?)),
        "bits_sub" => tu(u(1)?.wrapping_sub(u(2)?) & mask(w(0)?)),
        "bits_neg" => tu(0u128.wrapping_sub(u(1)?) & mask(w(0)?)),
        "bits_mul" => tu(u(1)?.wrapping_mul(u(2)?) & mask(w(0)?)),
        "bits_not" => tu(!u(1)? & mask(w(0)?)),
        "bits_and" => tu(u(1)? & u(2)? & mask(w(0)?)),
        "bits_or" => tu((u(1)? | u(2)?) & mask(w(0)?)),
        "bits_xor" => tu((u(1)? ^ u(2)?) & mask(w(0)?)),
        "nat_and" => tu(u(0)? & u(1)?),
        "nat_or" => tu(u(0)? | u(1)?),
        "bits_shl" => {
            let k = u(2)?;
            tu(if k >= 128 { 0 } else { u(1)? << k } & mask(w(0)?))
        }
        "bits_shr" => {
            let k = u(2)?;
            tu(if k >= 128 { 0 } else { u(1)? >> k })
        }
        "bits_slice" => {
            let (x, hi, lo) = (u(0)?, u(1)?, u(2)?);
            if hi < lo || hi >= 128 {
                return None;
            }
            tu((x >> lo) & mask((hi - lo + 1) as u32))
        }
        _ => None,
    }
}

impl<'a> Simp<'a> {
    fn new(env: &'a Env, lg: &Logic) -> Simp<'a> {
        let g = |n: &str| env.sym_by_name.get(n).copied();
        let unfold = ["bind_rel", "any_rel", "is_ok"].iter().filter_map(|n| g(n)).collect();
        let arith = ARITH.iter().filter_map(|n| g(n).map(|s| (s, *n))).collect();
        Simp {
            env,
            arith,
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
                set_select: g("set_select"),
                in_: g("in"),
                omega: g("omega"),
                tag: g("tag"),
                some: g("some"),
                none: g("none"),
                empty: g("empty"),
            },
        }
    }

    /// Euclidean division of integer numerals (`int_div`, `int_mod`: a = b q
    /// + r with 0 <= r < |b|); integers are numerals or `pair(1, m)` for -m.
    fn compute_int(&self, op: &str, a: &[Term]) -> Option<Term> {
        let int = |t: &Term| -> Option<i128> {
            match t.node() {
                Node::Nat(v) => i128::try_from(v.to_u128()?).ok(),
                Node::App(p, b) if is(*p, self.s.pair) => match (b[0].node(), b[1].node()) {
                    (Node::Nat(one), Node::Nat(m)) if one.to_u64() == Some(1) && !m.is_zero() => Some(-i128::try_from(m.to_u128()?).ok()?),
                    _ => None,
                },
                _ => None,
            }
        };
        let of = |v: i128| -> Term {
            if v >= 0 {
                Term::nat(crate::nat::Nat::from_u128(v as u128))
            } else {
                self.app2(self.s.pair, Term::nat(crate::nat::Nat::from_u64(1)), Term::nat(crate::nat::Nat::from_u128(v.unsigned_abs())))
            }
        };
        let (x, y) = (int(a.first()?)?, int(a.get(1)?)?);
        if y == 0 {
            return None;
        }
        let r = x.rem_euclid(y.abs());
        match op {
            "int_mod" => Some(of(r)),
            "int_div" => Some(of((x - r) / y)),
            _ => None,
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
                // (a tag is a pair: `tag(k, v) = pair(k, v)`)
                if is(g, s.pair) || is(g, s.tag) {
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
        if let Some(op) = self.arith.get(&f) {
            if let Some(v) = compute(op, &args) {
                return v;
            }
            if let Some(v) = self.compute_int(op, &args) {
                return v;
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
        // comprehension: `z in set_select(s, x. p)` <-> `z in s && p(z)`
        if is(f, s.in_) {
            if let Node::App(sel, sb) = a[1].node() {
                if is(*sel, s.set_select) {
                    let z = self.term(&a[0]);
                    let mem = Term::app(f, vec![z.clone(), sb[0].clone()]);
                    return self.and(self.prop(&mem, pol), self.prop(&inst_k(self.env, &sb[1], &[z]), pol));
                }
            }
        }
        // an atom: its arguments as terms
        let t = self.term(t);
        if let Some(b) = self.literal_prop(&t) {
            return if b { self.tt() } else { self.ff() };
        }
        t
    }

    /// Propositions about numerals: a numeral is a natural number (`lit_nat`);
    /// order, membership (von Neumann) and bits of numerals.
    fn literal_prop(&self, t: &Term) -> Option<bool> {
        let s = &self.s;
        let Node::App(m, b) = t.node() else { return None };
        let lit = |x: &Term| match x.node() {
            Node::Nat(v) => Some(v.clone()),
            _ => None,
        };
        let name = self.env.syms.get(*m as usize).map(|x| x.name.as_str()).unwrap_or("");
        if is(*m, s.in_) {
            let x = lit(&b[0])?;
            if let Node::App(o, ob) = b[1].node() {
                if is(*o, s.omega) {
                    return Some(true);
                }
                // x in bits(n): x < 2^n
                if self.env.syms.get(*o as usize).is_some_and(|y| y.name == "bits") {
                    let n = lit(&ob[0])?.to_u64()?;
                    return Some(x < crate::nat::Nat::pow2(n));
                }
            }
            return Some(x < lit(&b[1])?);
        }
        match name {
            "nat_lt" | "lit_lt" => Some(lit(&b[0])? < lit(&b[1])?),
            "nat_le" => Some(lit(&b[0])? <= lit(&b[1])?),
            "bit" => {
                let (x, i) = (lit(&b[0])?, lit(&b[1])?.to_u64()?);
                let (q, _) = x.divmod(&crate::nat::Nat::pow2(i))?;
                Some(!q.divmod(&crate::nat::Nat::from_u64(2))?.1.is_zero())
            }
            _ => None,
        }
    }

    fn eq(&self, a: &Term, b: &Term) -> Term {
        let s = &self.s;
        let (mut x, mut y) = (self.term(a), self.term(b));
        if x == y {
            return self.tt();
        }
        // a variable on the left (`t = x` is `x = t`)
        let var = |t: &Term| matches!(t.node(), Node::Var(_, a) if a.is_empty());
        if var(&y) && !var(&x) {
            std::mem::swap(&mut x, &mut y);
        }
        if distinct_literals(&x, &y) {
            return self.ff();
        }
        // `empty` is the numeral 0 (`lit_zero`)
        let is_empty = |t: &Term| matches!(t.node(), Node::App(e, b) if b.is_empty() && is(*e, s.empty));
        for (p, q) in [(&x, &y), (&y, &x)] {
            if let (Node::Nat(v), true) = (p.node(), is_empty(q)) {
                return if v.is_zero() { self.tt() } else { self.ff() };
            }
        }
        // constructors: injective and distinct
        let ctor = |t: &Term| -> Option<(u8, Vec<Term>)> {
            match t.node() {
                Node::App(g, b) if is(*g, s.pair) || is(*g, s.tag) => Some((10, b.to_vec())),
                // some(x) = tag(1, x), none = tag(0, empty)
                Node::App(g, b) if is(*g, s.some) => Some((10, vec![Term::nat(crate::nat::Nat::from_u64(1)), b[0].clone()])),
                Node::App(g, _) if is(*g, s.none) => Some((10, vec![Term::nat(crate::nat::Nat::zero()), Term::app(s.empty?, vec![])])),
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
    /// conclusions of rules already added to the path
    done: Vec<Term>,
}

const MAX_PATHS: usize = 4096;
/// leftover paths printed in full
const MAX_REPORTED: usize = 3;

impl Simp<'_> {
    fn paths(&self, t: &Term, fresh: &mut u32) -> Option<Vec<Path>> {
        let s = &self.s;
        if self.is_true(t) {
            return Some(vec![Path { vars: vec![], lits: vec![], done: vec![] }]);
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
                // contradictory combinations (e.g. `x = ok(..)` with
                // `x = exc(..)` from consecutive statements) are dropped
                // as they arise, so sequences do not multiply out
                let mut out = Vec::new();
                for p in &x {
                    for q in &y {
                        let mut r = p.clone();
                        r.vars.extend(q.vars.iter().copied());
                        r.lits.extend(q.lits.iter().cloned());
                        r.done.extend(q.done.iter().cloned());
                        if x.len() == 1 || y.len() == 1 || self.settle(r.clone()).is_some() {
                            out.push(r);
                        }
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
        Some(vec![Path { vars: vec![], lits: vec![t.clone()], done: vec![] }])
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
            // `x = a` and `x = b` for any variable x, a and b not variables:
            // the second becomes `a = b` (then split by injectivity)
            if let Some((j, e)) = self.same_var_eqs(&p.lits) {
                p.lits[j] = e;
                continue 'again;
            }
            // a literal and its negation
            if p.lits.iter().any(|l| matches!(l.node(), Node::App(n, a) if is(*n, self.s.not) && p.lits.contains(&a[0]))) {
                return None;
            }
            // `!(ex x. B(x))` with every conjunct of some B(t) among the
            // literals: contradictory (∃-introduction)
            if p.lits.iter().any(|l| self.refuted_by(l, &p.lits)) {
                return None;
            }
            return Some(p);
        }
    }

    fn same_var_eqs(&self, lits: &[Term]) -> Option<(usize, Term)> {
        let side = |l: &Term| -> Option<(crate::term::VarId, Term)> {
            let Node::App(e, ab) = l.node() else { return None };
            if *e != self.s.eq {
                return None;
            }
            let var = |t: &Term| matches!(t.node(), Node::Var(_, a) if a.is_empty());
            [(&ab[0], &ab[1]), (&ab[1], &ab[0])].into_iter().find_map(|(v, t)| match v.node() {
                Node::Var(x, xa) if xa.is_empty() && !var(t) && !has_var(t, *x) => Some((*x, t.clone())),
                _ => None,
            })
        };
        let eqs: Vec<_> = lits.iter().enumerate().filter_map(|(i, l)| side(l).map(|(x, t)| (i, x, t))).collect();
        for (k, (_, x, a)) in eqs.iter().enumerate() {
            for (j, y, b) in &eqs[k + 1..] {
                if x == y {
                    return Some((*j, Term::app(self.s.eq, vec![a.clone(), b.clone()])));
                }
            }
        }
        None
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

    /// `l` is `!(ex x. B(x))` and the literals contain every conjunct of
    /// B(t) for a t found by matching.
    fn refuted_by(&self, l: &Term, lits: &[Term]) -> bool {
        // `all xs. !(ex ys. B)` (xs or ys non-empty): they become pattern
        // variables, B instantiated must be among the literals
        let mut vs = Vec::new();
        let mut next = self.env.vars.len() as u32 + 3_000_000;
        let mut open = |t: &Term, vs: &mut Vec<crate::term::VarId>| {
            vs.push(next);
            next += 1;
            inst_k(self.env, t, &[Term::var(next - 1, vec![])])
        };
        let mut t = l.clone();
        while let Node::App(q, a) = t.node() {
            if *q != self.s.all {
                break;
            }
            t = open(&a[0], &mut vs);
        }
        let Node::App(n, a) = t.node() else { return false };
        if !is(*n, self.s.not) {
            return false;
        }
        let mut body = a[0].clone();
        while let Node::App(e, b) = body.node() {
            if *e != self.s.ex {
                break;
            }
            body = open(&b[0], &mut vs);
        }
        if vs.is_empty() {
            return false;
        }
        let mut cs = Vec::new();
        self.conjuncts(&body, &mut cs);
        let mut binds = Vec::new();
        for c in &cs {
            for pl in lits {
                let mut bd = binds.clone();
                if pmatch(c, pl, &vs, &mut bd) {
                    binds = bd;
                    break;
                }
            }
        }
        if !vs.iter().all(|v| binds.iter().any(|(w, _)| w == v)) {
            return false;
        }
        let bf = self.env.binders_fn();
        cs.iter().all(|c| {
            let mut c = c.clone();
            for (v, t) in &binds {
                c = c.subst_var(*v, t, &bf);
            }
            lits.contains(&c)
        })
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

/// A loop invariant for `simp`: `inv` is a body under two binders (the
/// loop's initial state l0, the current state l), `var` under one (l): a
/// natural number that each iteration decreases (the loop terminates).
#[derive(Clone, Debug)]
pub struct LoopHint {
    pub inv: Term,
    pub var: Option<Term>,
    /// no invariant: unroll loops without one, an iteration at a time
    pub unroll: bool,
}

/// The literals sharing a variable with `goal`.
fn relevant(lits: &[Term], goal: &Term) -> Vec<Term> {
    fn vars(t: &Term, out: &mut Vec<crate::term::VarId>) {
        match t.node() {
            Node::Var(v, a) => {
                if !out.contains(v) {
                    out.push(*v);
                }
                a.iter().for_each(|x| vars(x, out));
            }
            Node::App(_, a) => a.iter().for_each(|x| vars(x, out)),
            _ => {}
        }
    }
    let mut gv = Vec::new();
    vars(goal, &mut gv);
    lits.iter()
        .filter(|l| {
            let mut lv = Vec::new();
            vars(l, &mut lv);
            lv.iter().any(|v| gv.contains(v))
        })
        .cloned()
        .collect()
}

/// The largest variable id in `t` (0 if none).
fn max_var(t: &Term) -> u32 {
    match t.node() {
        Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => 0,
        Node::Var(v, a) => a.iter().map(max_var).fold(*v, u32::max),
        Node::App(_, a) => a.iter().map(max_var).fold(0, u32::max),
    }
}

/// Rule instances tried per rule and path.
const MAX_INSTANCES: usize = 64;

/// The bindings of pattern variables `vs` under which each hypothesis
/// `hyps[i..]` matches a literal; a hypothesis matching none is left for
/// checking (its index in the second component).
fn instances(
    hyps: &[Term],
    i: usize,
    lits: &[Term],
    vs: &[crate::term::VarId],
    binds: Vec<(crate::term::VarId, Term)>,
    open: Vec<usize>,
    out: &mut Vec<(Vec<(crate::term::VarId, Term)>, Vec<usize>)>,
) {
    if out.len() >= MAX_INSTANCES {
        return;
    }
    if i == hyps.len() {
        out.push((binds, open));
        return;
    }
    let mut any = false;
    for pl in lits {
        let mut b = binds.clone();
        if pmatch(&hyps[i], pl, vs, &mut b) {
            any = true;
            instances(hyps, i + 1, lits, vs, b, open.clone(), out);
        }
    }
    if !any {
        let mut o = open;
        o.push(i);
        instances(hyps, i + 1, lits, vs, binds, o, out);
    }
}

impl Simp<'_> {
    /// A literal as a rule `all xs. A1 -> .. -> An -> C` (n >= 1, or n = 0
    /// for an equation C): its
    /// variables (fresh pattern variables), the conjuncts of the Ai, and C.
    fn rule(&self, l: &Term, fresh: &mut u32) -> Option<(Vec<crate::term::VarId>, Vec<Term>, Term)> {
        let mut vs = Vec::new();
        let mut t = l.clone();
        while let Node::App(q, a) = t.node() {
            if *q != self.s.all {
                break;
            }
            vs.push(*fresh);
            *fresh += 1;
            t = inst_k(self.env, &a[0], &[Term::var(*fresh - 1, vec![])]);
        }
        let mut hyps = Vec::new();
        while let Node::App(i, a) = t.node() {
            if *i != self.s.imp {
                break;
            }
            self.conjuncts(&a[0], &mut hyps);
            t = a[1].clone();
        }
        // (an equation needs no hypotheses: a rewrite rule)
        let eq = matches!(t.node(), Node::App(e, _) if *e == self.s.eq);
        (!hyps.is_empty() || (eq && !vs.is_empty())).then_some((vs, hyps, t))
    }

    /// A new fact on the path from a rule among its literals: an instance
    /// whose hypotheses are literals of the path, or follow from them (taut
    /// or arith), and whose conclusion is not yet known.
    fn chain(&self, lg: &Logic, p: &Path, goal: &Term, fresh: &mut u32) -> Option<Term> {
        let bf = self.env.binders_fn();
        // the terms an equation's left side may match (not under binders)
        let mut subs = Vec::new();
        for t in p.lits.iter().chain([goal]) {
            self.subterms(t, &mut subs);
        }
        for l in &p.lits {
            let Some((vs, hyps, concl)) = self.rule(l, fresh) else { continue };
            let mut insts = Vec::new();
            instances(&hyps, 0, &p.lits, &vs, Vec::new(), Vec::new(), &mut insts);
            // variables only in the conclusion `lhs = rhs`: from the terms
            let lhs = match concl.node() {
                Node::App(e, ab) if *e == self.s.eq => Some(ab[0].clone()),
                _ => None,
            };
            let mut all_insts = Vec::new();
            for (binds, open) in insts {
                if vs.iter().all(|v| binds.iter().any(|(w, _)| w == v)) {
                    all_insts.push((binds, open));
                } else if let Some(lhs) = &lhs {
                    for u in &subs {
                        let mut b = binds.clone();
                        if pmatch(lhs, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                            all_insts.push((b, open.clone()));
                        }
                    }
                }
                if all_insts.len() >= MAX_INSTANCES {
                    break;
                }
            }
            for (binds, open) in all_insts {
                let inst = |t: &Term| {
                    let mut t = t.clone();
                    for (v, x) in &binds {
                        t = t.subst_var(*v, x, &bf);
                    }
                    self.prop(&t, Pol::Other)
                };
                let shown = |h: &Term| {
                    lg.tautology(self.env, &p.lits, h).is_ok()
                        || lg.arith(self.env, &p.lits, h).is_ok()
                        || lg.arith(self.env, &relevant(&p.lits, h), h).is_ok()
                };
                if !open.iter().all(|&i| shown(&inst(&hyps[i]))) {
                    continue;
                }
                let c = inst(&concl);
                if self.is_true(&c) || p.done.contains(&c) || lg.tautology(self.env, &p.lits, &c).is_ok() {
                    continue;
                }
                return Some(c);
            }
        }
        None
    }

    /// The subterms of `t` (applications, not under binders).
    fn subterms(&self, t: &Term, out: &mut Vec<Term>) {
        if let Node::App(f, a) = t.node() {
            if !out.contains(t) {
                out.push(t.clone());
            }
            let bf = self.env.binders_fn();
            for (i, x) in a.iter().enumerate() {
                if bf(*f, i) == 0 {
                    self.subterms(x, out);
                }
            }
        }
    }

    /// The path with the fact `c` added (split into paths).
    fn extend(&self, lg: &Logic, p: &Path, c: Term, fresh: &mut u32) -> crate::env::KResult<Vec<Path>> {
        let mut t = self.tt();
        for o in &p.lits {
            t = self.and(t, o.clone());
        }
        t = self.and(t, lg.simp_fact(self.env, &c));
        let ps = self.paths(&t, fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
        Ok(ps
            .into_iter()
            .map(|mut q| {
                q.vars.extend(p.vars.iter().copied());
                q.done.extend(p.done.iter().cloned());
                q.done.push(c.clone());
                q
            })
            .collect())
    }

    /// The path with a `while_rel` literal replaced by the loop's outcome,
    /// for the first loop and hint whose premises `simp` shows on the path
    /// (the other literals); why the hints failed goes to `why`.
    fn loop_step(&self, lg: &Logic, p: &Path, hints: &[LoopHint], fresh: &mut u32, why: &mut String) -> crate::env::KResult<Option<Vec<Path>>> {
        let Some(wr) = self.env.sym_by_name.get("while_rel").copied() else { return Ok(None) };
        for (i, l) in p.lits.iter().enumerate() {
            let Node::App(f, a) = l.node() else { continue };
            if *f != wr {
                continue;
            }
            if hints.is_empty() {
                why.push_str("\n  (a loop on the path: `simp` needs its invariant, `{l0 l. I}`)");
                return Ok(None);
            }
            let others: Vec<Term> = p.lits.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, l)| l.clone()).collect();
            let replace = |out: Term, fresh: &mut u32| -> crate::env::KResult<Option<Vec<Path>>> {
                let mut t = self.tt();
                for o in &others {
                    t = self.and(t, o.clone());
                }
                t = self.and(t, lg.simp_fact(self.env, &out));
                let ps = self.paths(&t, fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
                Ok(Some(
                    ps.into_iter()
                        .map(|mut q| {
                            q.vars.extend(p.vars.iter().copied());
                            q.done.extend(p.done.iter().cloned());
                            q
                        })
                        .collect(),
                ))
            };
            for (k, h) in hints.iter().enumerate().filter(|(_, h)| !h.unroll) {
                match self.loop_rule(lg, &others, a, h, hints, fresh) {
                    Ok(out) => return replace(out, fresh),
                    Err(e) => why.push_str(&format!("\n  (invariant {} for a loop on the path: {})", k + 1, e.0.replace('\n', "\n  "))),
                }
            }
            if hints.iter().any(|h| h.unroll) {
                let out = self.unroll(a, fresh)?;
                return replace(out, fresh);
            }
        }
        Ok(None)
    }

    /// One iteration of `while_rel(l0, l. C, l o. B, l. T, r)` (theorem
    /// `while_unroll`, core/loop.core): it stops at l0, the body leaves, or
    /// the body continues to l1 and the loop runs on from there (or
    /// diverges).
    fn unroll(&self, a: &[Term], fresh: &mut u32) -> crate::env::KResult<Term> {
        let env = self.env;
        let wr = env.sym_by_name.get("while_rel").copied().ok_or_else(|| crate::env::KernelError("no while_rel".into()))?;
        let is_ok = env.sym_by_name.get("is_ok").copied().ok_or_else(|| crate::env::KernelError("no is_ok".into()))?;
        let empty = Term::app(env.sym_by_name.get("empty").copied().ok_or_else(|| crate::env::KernelError("no empty".into()))?, vec![]);
        let (l0, r) = (&a[0], &a[4]);
        let cond = |x: &Term| inst_k(env, &a[1], &[x.clone()]);
        let body = |x: &Term, o: &Term| inst_k(env, &a[2], &[x.clone(), o.clone()]);
        let ok = |x: &Term| Term::app(self.s.ok.expect("ok"), vec![x.clone(), empty.clone()]);
        let mut var = || {
            *fresh += 1;
            (*fresh - 1, Term::var(*fresh - 1, vec![]))
        };
        let ((l1v, l1), (tv, t)) = (var(), var());
        let stop = self.and(self.not(cond(l0)), Term::app(self.s.eq, vec![r.clone(), ok(l0)]));
        let leave = self.and(self.and(cond(l0), body(l0, r)), self.not(Term::app(is_ok, vec![r.clone()])));
        let div = Term::app(self.s.eq, vec![r.clone(), Term::app(self.s.diverge.expect("diverge"), vec![t])]);
        let div = Term::app(self.s.ex, vec![abstract_var(env, &div, tv, 0)]);
        let again = Term::app(wr, vec![l1.clone(), a[1].clone(), a[2].clone(), a[3].clone(), r.clone()]);
        let next = self.and(body(l0, &ok(&l1)), self.or(again, div));
        let next = self.and(cond(l0), Term::app(self.s.ex, vec![abstract_var(env, &next, l1v, 0)]));
        Ok(self.or(self.or(stop, leave), next))
    }

    /// The outcome of `while_rel(a..)` given the hint, its premises shown
    /// from `others`: `(ex l. I(l) && ((!C(l) && r = ok(l, empty)) ||
    /// (C(l) && B(l, r) && !is_ok(r))))`, with `|| (ex t. r = diverge(t))`
    /// unless the hint has a variant.
    fn loop_rule(&self, lg: &Logic, others: &[Term], a: &[Term], h: &LoopHint, hints: &[LoopHint], fresh: &mut u32) -> crate::env::KResult<Term> {
        let env = self.env;
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| crate::env::KernelError(format!("loops need `{}`", n)));
        let c0 = |n: &str| sym(n).map(|s| Term::app(s, vec![]));
        let (l0, r) = (&a[0], &a[4]);
        let inv = |x: &Term| inst_k(env, &h.inv, &[l0.clone(), x.clone()]);
        let cond = |x: &Term| inst_k(env, &a[1], &[x.clone()]);
        let body = |x: &Term, o: &Term| inst_k(env, &a[2], &[x.clone(), o.clone()]);
        let empty = c0("empty")?;
        let ok = |x: &Term| Term::app(self.s.ok.expect("ok"), vec![x.clone(), empty.clone()]);
        let mut var = || {
            *fresh += 1;
            Term::var(*fresh - 1, vec![])
        };
        let (x, y, z, t) = (var(), var(), var(), var());
        let with = |extra: Vec<Term>| -> Vec<Term> { others.iter().cloned().chain(extra).collect() };
        let pr = crate::syntax::Printer::new(env);
        let show = |what: &str, prem: &[Term], goal: &Term, fresh: &mut u32| {
            lg.prove_paths(env, prem, goal, hints, fresh)
                .map_err(|e| crate::env::KernelError(format!("{} `{}`: {}", what, pr.term(goal), e.0)))
        };
        show("at the start,", others, &inv(l0), fresh)?;
        let step = with(vec![inv(&x), cond(&x), body(&x, &ok(&y))]);
        show("after an iteration,", &step, &inv(&y), fresh)?;
        if let Some(m) = &h.var {
            let mv = |x: &Term| inst_k(env, m, &[x.clone()]);
            let nat = Term::app(sym("in")?, vec![mv(&x), c0("omega")?]);
            show("the variant is a natural number,", &with(vec![inv(&x)]), &nat, fresh)?;
            let lt = Term::app(sym("nat_lt")?, vec![mv(&y), mv(&x)]);
            show("the variant decreases,", &step, &lt, fresh)?;
        }
        // theorems while_inv / while_var (core/loop.core)
        let is_ok = Term::app(sym("is_ok")?, vec![r.clone()]);
        let stop = self.and(self.not(cond(&z)), Term::app(self.s.eq, vec![r.clone(), ok(&z)]));
        let exit = self.and(self.and(cond(&z), body(&z, r)), self.not(is_ok));
        let Node::Var(zv, _) = z.node() else { unreachable!() };
        let fin = self.and(inv(&z), self.or(stop, exit));
        let mut out = Term::app(self.s.ex, vec![abstract_var(env, &fin, *zv, 0)]);
        if h.var.is_none() {
            let Node::Var(tv, _) = t.node() else { unreachable!() };
            let div = Term::app(self.s.eq, vec![r.clone(), Term::app(self.s.diverge.expect("diverge"), vec![t.clone()])]);
            out = self.or(out, Term::app(self.s.ex, vec![abstract_var(env, &div, *tv, 0)]));
        }
        Ok(out)
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
        self.simp_prove_loops(env, premises, goal, &[])
    }

    /// `simp_prove`, with invariants for the loops on the paths.
    pub fn simp_prove_loops(&self, env: &Env, premises: &[Term], goal: &Term, hints: &[LoopHint]) -> crate::env::KResult<()> {
        // fresh variables above every variable of the input
        let mut fresh = env.vars.len() as u32 + 2_000_000;
        for t in premises.iter().chain([goal]).chain(hints.iter().flat_map(|h| [&h.inv].into_iter().chain(&h.var))) {
            fresh = fresh.max(max_var(t) + 1);
        }
        self.prove_paths(env, premises, goal, hints, &mut fresh)
    }

    fn prove_paths(&self, env: &Env, premises: &[Term], goal: &Term, hints: &[LoopHint], fresh: &mut u32) -> crate::env::KResult<()> {
        let sp = Simp::new(env, self);
        let mut prem = sp.tt();
        for p in premises {
            prem = sp.and(prem, self.simp_fact(env, p));
        }
        let g = self.simp_eqv(env, goal);
        let mut work = sp.paths(&prem, fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
        let (mut steps, mut left, mut report) = (0, 0, String::new());
        while let Some(p) = work.pop() {
            let Some(p) = sp.settle(p) else { continue };
            // the path's equations used in the goal: `x = t` or `t = x` (x a
            // variable) substituted, then `a = b` rewritten left to right
            let bf = env.binders_fn();
            let mut g = g.clone();
            let eqs: Vec<(&Term, &Term)> = p
                .lits
                .iter()
                .filter_map(|l| match l.node() {
                    Node::App(e, ab) if *e == sp.s.eq => Some((&ab[0], &ab[1])),
                    _ => None,
                })
                .collect();
            let var = |t: &Term| match t.node() {
                Node::Var(x, xa) if xa.is_empty() => Some(*x),
                _ => None,
            };
            for &(a, b) in &eqs {
                for (v, t) in [(a, b), (b, a)] {
                    if let Some(x) = var(v) {
                        if !has_var(t, x) && has_var(&g, x) {
                            g = self.simp_eqv(env, &g.subst_var(x, t, &bf));
                            break;
                        }
                    }
                }
            }
            for &(a, b) in &eqs {
                if var(a).is_none() && var(b).is_none() {
                    let body = super::seq::abstract_term(&g, a, 0, &bf);
                    if body != g {
                        g = self.simp_eqv(env, &inst_k(env, &body, &[b.clone()]));
                    }
                }
            }
            if sp.is_true(&g) {
                continue;
            }
            if self.tautology(env, &p.lits, &g).is_ok() || self.arith(env, &p.lits, &g).is_ok() {
                continue;
            }
            if sp.witnessed(&p.lits, &g, fresh, self) {
                continue;
            }
            // long paths: arithmetic from the literals about the goal's variables
            let near = relevant(&p.lits, &g);
            if near.len() < p.lits.len() && (self.tautology(env, &near, &g).is_ok() || self.arith(env, &near, &g).is_ok()) {
                continue;
            }
            // a rule among the facts (`all xs. A -> .. -> C`) whose
            // hypotheses the path has: continue with its conclusion
            if let Some(c) = sp.chain(self, &p, &g, fresh) {
                steps += 1;
                if steps > MAX_PATHS {
                    return Err(crate::env::KernelError("simp: too many paths".into()));
                }
                work.extend(sp.extend(self, &p, c, fresh)?);
                continue;
            }
            // a loop on the path, with an invariant: continue with its outcome
            let mut why = String::new();
            if let Some(ps) = sp.loop_step(self, &p, hints, fresh, &mut why)? {
                steps += 1;
                if steps > MAX_PATHS {
                    return Err(crate::env::KernelError("simp: too many paths".into()));
                }
                work.extend(ps);
                continue;
            }
            // left: reported as a fact to prove (its variables universal)
            left += 1;
            if left <= MAX_REPORTED {
                let mut fact = g.clone();
                for l in p.lits.iter().rev() {
                    fact = Term::app(sp.s.imp, vec![l.clone(), fact]);
                }
                for v in p.vars.iter().rev() {
                    if has_var(&fact, *v) {
                        fact = Term::app(sp.s.all, vec![abstract_var(env, &fact, *v, 0)]);
                    }
                }
                let pr = crate::syntax::Printer::new(env);
                report.push_str(&format!("\n  path {}: {}{}", left, pr.term(&fact), why));
            }
        }
        if left > 0 {
            let more = if left > MAX_REPORTED { format!("\n  ({} more)", left - MAX_REPORTED) } else { String::new() };
            return Err(crate::env::KernelError(format!(
                "simp: {} path{} left (prove each as a fact -- keeping only the hypotheses it needs -- and pass it to simp):{}{}",
                left,
                if left == 1 { "" } else { "s" },
                report,
                more
            )));
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
