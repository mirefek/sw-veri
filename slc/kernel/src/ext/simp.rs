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
//! * the definitions of `bind_rel`, `any_rel`, `is_ok`, `ne`;
//! * `runs(mkprog(s o. R), S, O) <-> pair(S, O) in univ(1) && R(S, O)`
//!   (membership in `mkprog`; in positive positions of the goal);
//! * `pair(a, b) in univ(u) <-> a in univ(u) && b in univ(u)` (likewise
//!   `tag`, outcomes, `some`, `upair`, `single`); integers are in `univ(u)`
//!   for u >= 1 (`omega_univ`), numerals and strings in every universe.
//!
//! * records: `app(restrict(f, d), k)` is `app(f, k)` if k in d, `empty`
//!   if not; `app(ghost_part(f, d), k)` is `empty` if k in d, `app(f, k)`
//!   if not; `app(union2(a, b), k)` (`rec_merge`) is `app(a, k)` when b has
//!   no pair with first element k (`empty`, a ghost part or restriction
//!   without k, updates at other keys of such) -- by `app_ext`, the pairs
//!   at k being the same; `app(empty, k)` is `empty`.
//!
//! Per path, the goal is also simplified with the path's literals (a
//! literal L true, `!L`'s L false). Witnesses for the goal's existentials:
//! matching its literals with the path's, its own equations once bound, and
//! for a variable seen only through projections (`fst(x) = 1`, `m =
//! fst(out_state(x))`) the nested pairs those fix (the rest `empty`);
//! each candidate is then checked (taut / arith).
//!
//! Implications, used only where they are sound:
//! * in positive positions of a fact being simplified (weakening):
//!   `runs(mkprog(s o. R), S, O) -> R(S, O)`;
//! * in positive positions of the goal (strengthening): `fn_update(f, k, v)`,
//!   `insert`, `union2` are in `univ(u)` if their arguments are; `app(f, k)`,
//!   `fst(p)`, `snd(p)` (and `out_state`, `out_value`) if f or p is (they
//!   are `empty` when undefined); `ite(c, a, b)` if a and b are.
//!
//! Rules: a path literal `all xs. A1 -> .. -> An -> C` whose hypotheses
//! match literals of the path (or follow from them by taut/arith), with
//! every x bound, adds its instance of C to the path (∀- and →-elimination);
//! for an equation C (possibly n = 0), xs may also be bound by matching its
//! left side against terms of the path or goal. The goal is rewritten with
//! the path's equations `x = t` / `t = x` (x a variable) and `a = b` (left
//! to right).
//!
//! Delayed case splits (no rule, only the order of the search): a
//! disjunction about the pending outcome r of a loop (`while_rel(.., r)`)
//! or of a folded program (`runs(P, s, r)`) -- e.g. how a run's result
//! becomes the function's outcome -- stays one literal while r is unknown,
//! and is split only when nothing else applies (no rule, no loop step):
//! by then r is usually known and one alternative is left. Meanwhile the
//! closing checks leave it out (fewer premises), and a goal about what it
//! decides waits.
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
    /// a positive position of the goal: equivalences only, but runs of a
    /// program are unfolded (to choose the outcomes of its parts)
    Goal,
    /// negative, or both (an `iff`): equivalences only
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
    fn_build: Option<SymId>,
    ite: Option<SymId>,
    runs: Option<SymId>,
    mkprog: Option<SymId>,
    univ: Option<SymId>,
    bits_add: Option<SymId>,
    bits_of_int: Option<SymId>,
    int_add: Option<SymId>,
    int_sub: Option<SymId>,
    int_div: Option<SymId>,
    int_pow: Option<SymId>,
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

/// What a path knows a term to be: an integer, a natural, an n-bit word.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Ty {
    Int,
    Nat,
    Bits(u64),
}

/// A fast hasher for the simplifier's small integer keys (symbols, node
/// addresses): SipHash's flooding resistance is not needed here.
#[derive(Default, Clone, Copy)]
struct FxHasher(u64);

impl std::hash::Hasher for FxHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.add(*b as u64);
        }
    }
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64)
    }
    fn write_u64(&mut self, i: u64) {
        self.add(i)
    }
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64)
    }
}

impl FxHasher {
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

type FxMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<FxHasher>>;

struct Simp<'a> {
    env: &'a Env,
    s: Syms,
    /// arithmetic definitions computed on numerals
    arith: FxMap<SymId, &'static str>,
    /// split every disjunction (no holding: `pending_outs` is empty)
    no_hold: std::cell::Cell<bool>,
    /// `term` of the nodes seen (by address; the node kept alive), valid
    /// for the current typing context `nats`
    memo: std::cell::RefCell<FxMap<usize, (Term, Term)>>,
    /// programs kept folded (`Logic::simp_keep`)
    keep: Vec<SymId>,
    /// terms the current path knows to be natural numbers (its literals
    /// `t in omega`, `t in bits(k)`)
    nats: std::cell::RefCell<Vec<(Term, Ty)>>,
    /// fields read by definitions of their parameters (`footprint`)
    footprints: std::cell::RefCell<FxMap<(SymId, usize), Option<Vec<Term>>>>,
    /// parameters used only mod 2^n (`word_param`)
    word_params: std::cell::RefCell<FxMap<(SymId, usize), Option<u64>>>,
    /// time in rule chaining (SIMP_TIME): matching, typing / instances,
    /// taut, arith
    prof: std::cell::RefCell<[std::time::Duration; 4]>,
}

/// The arithmetic and bitwise definitions of the prelude that `simp`
/// computes on integer literals (their values follow from the definitions
/// and the `lit_*` axioms; words up to 128 bits).
const ARITH: &[&str] = &[
    "int_add", "int_sub", "int_neg", "int_mul", "int_div", "int_mod", "int_pow", "int_succ", "int_pred", "int_abs", "int_val", "pow2",
    "bits_of_int", "bits_add", "bits_sub", "bits_neg", "bits_mul", "bits_not", "bits_and", "bits_or", "bits_xor", "bits_shl", "bits_shr",
    "bits_slice", "bits_sext", "sint", "int_and", "int_or", "lit_add", "lit_mul", "lit_sub", "lit_div", "lit_mod", "succ",
];

/// An integer literal's value: sign (true: negative) and magnitude. The
/// literals of integers are numerals, and `pair(1, m)` (m > 0) for -m.
#[derive(Clone, PartialEq, Debug)]
struct SInt {
    neg: bool,
    m: crate::nat::Nat,
}

impl SInt {
    fn new(neg: bool, m: crate::nat::Nat) -> SInt {
        SInt { neg: neg && !m.is_zero(), m }
    }
    fn nat(m: crate::nat::Nat) -> SInt {
        SInt::new(false, m)
    }
    fn neg(&self) -> SInt {
        SInt::new(!self.neg, self.m.clone())
    }
    fn add(&self, o: &SInt) -> SInt {
        if self.neg == o.neg {
            return SInt::new(self.neg, self.m.add(&o.m));
        }
        // different signs: the larger magnitude wins
        match self.m.sub(&o.m) {
            Some(d) => SInt::new(self.neg, d),
            None => SInt::new(o.neg, o.m.sub(&self.m).unwrap()),
        }
    }
    fn mul(&self, o: &SInt) -> SInt {
        SInt::new(self.neg != o.neg, self.m.mul(&o.m))
    }
    fn lt(&self, o: &SInt) -> bool {
        match (self.neg, o.neg) {
            (true, false) => true,
            (false, true) => false,
            (false, false) => self.m < o.m,
            (true, true) => o.m < self.m,
        }
    }
    /// Euclidean division (0 <= r < |d|); None for d = 0
    fn divmod(&self, d: &SInt) -> Option<(SInt, SInt)> {
        let (q, r) = self.m.divmod(&d.m)?;
        let one = crate::nat::Nat::from_u64(1);
        if !self.neg || r.is_zero() {
            // a = |d| q + r (a >= 0), or a = -(|d| q) exactly
            let q = SInt::new(self.neg != d.neg, q);
            return Some((q, SInt::nat(r)));
        }
        // a = -m = -(|d| q + r) = |d| (-(q + 1)) + (|d| - r)
        let q = SInt::new(!d.neg, q.add(&one));
        Some((q, SInt::nat(d.m.sub(&r).unwrap())))
    }
    fn to_u128(&self) -> Option<u128> {
        if self.neg { None } else { self.m.to_u128() }
    }
}

impl Simp<'_> {
    /// The value of an integer literal.
    fn int_lit(&self, t: &Term) -> Option<SInt> {
        match t.node() {
            Node::Nat(v) => Some(SInt::nat(v.clone())),
            Node::App(p, b) if is(*p, self.s.pair) && b.len() == 2 => match (b[0].node(), b[1].node()) {
                (Node::Nat(one), Node::Nat(m)) if one.to_u64() == Some(1) && !m.is_zero() => Some(SInt::new(true, m.clone())),
                _ => None,
            },
            Node::App(e, b) if b.is_empty() && is(*e, self.s.empty) => Some(SInt::nat(crate::nat::Nat::zero())),
            _ => None,
        }
    }

    /// The literal of an integer.
    fn of_int(&self, v: SInt) -> Term {
        if v.neg {
            self.app2(self.s.pair, Term::nat(crate::nat::Nat::from_u64(1)), Term::nat(v.m))
        } else {
            Term::nat(v.m)
        }
    }

    /// Arithmetic on literal arguments (None: not all literals, or out of
    /// range).
    fn compute(&self, op: &str, a: &[Term]) -> Option<Term> {
        use crate::nat::Nat;
        let i = |k: usize| self.int_lit(a.get(k)?);
        let n = |k: usize| i(k).filter(|v| !v.neg).map(|v| v.m);
        let u = |k: usize| i(k)?.to_u128();
        let w = |k: usize| u(k).filter(|&v| v <= 128).map(|v| v as u32);
        let mask = |bits: u32| if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
        let t = |v: SInt| Some(self.of_int(v));
        let tu = |v: u128| Some(Term::nat(Nat::from_u128(v)));
        let pow2 = |k: u128| (k <= 256).then(|| SInt::nat(Nat::pow2(k as u64)));
        // x mod 2^n, for a width n
        let wrap = |x: SInt, k: usize| -> Option<Term> { t(x.divmod(&pow2(u(k)?)?)?.1) };
        match op {
            "int_add" => t(i(0)?.add(&i(1)?)),
            "int_sub" => t(i(0)?.add(&i(1)?.neg())),
            "int_neg" => t(i(0)?.neg()),
            "int_mul" => t(i(0)?.mul(&i(1)?)),
            "int_succ" => t(i(0)?.add(&SInt::nat(Nat::from_u64(1)))),
            "int_pred" => t(i(0)?.add(&SInt::new(true, Nat::from_u64(1)))),
            "int_abs" => t(SInt::nat(i(0)?.m)),
            "int_val" => t(i(0)?),
            // (by 0: a / 0 = 0, a % 0 = a)
            "int_div" if i(1)?.m.is_zero() => t(SInt::nat(Nat::zero())),
            "int_mod" if i(1)?.m.is_zero() => t(i(0)?),
            "int_div" => t(i(0)?.divmod(&i(1)?)?.0),
            "int_mod" => t(i(0)?.divmod(&i(1)?)?.1),
            "lit_add" => t(SInt::nat(n(0)?.add(&n(1)?))),
            "lit_mul" => t(SInt::nat(n(0)?.mul(&n(1)?))),
            "lit_sub" => t(SInt::nat(n(0)?.sub(&n(1)?)?)),
            "lit_div" => t(SInt::nat(n(0)?.divmod(&n(1)?)?.0)),
            "lit_mod" => t(SInt::nat(n(0)?.divmod(&n(1)?)?.1)),
            "succ" => t(SInt::nat(n(0)?.add(&Nat::from_u64(1)))),
            "int_pow" => {
                let (b, e) = (i(0)?, i(1)?);
                if e.neg {
                    return t(SInt::nat(Nat::zero()));
                }
                let e = e.m.to_u64().filter(|&e| e <= 256)?;
                let mut r = SInt::nat(Nat::from_u64(1));
                for _ in 0..e {
                    r = r.mul(&b);
                }
                t(r)
            }
            "pow2" => {
                let e = i(0)?;
                if e.neg {
                    return t(SInt::nat(Nat::zero()));
                }
                t(pow2(e.to_u128()?)?)
            }
            "bits_of_int" => wrap(i(1)?, 0),
            "bits_add" => wrap(i(1)?.add(&i(2)?), 0),
            "bits_sub" => wrap(i(1)?.add(&i(2)?.neg()), 0),
            "bits_neg" => wrap(i(1)?.neg(), 0),
            "bits_mul" => wrap(i(1)?.mul(&i(2)?), 0),
            "bits_shl" => {
                let k = u(2)?;
                if k > 256 {
                    return None;
                }
                wrap(i(1)?.mul(&pow2(k)?), 0)
            }
            // on words: the arguments reduced mod 2^n first
            "bits_not" | "bits_and" | "bits_or" | "bits_xor" | "bits_shr" | "bits_slice" | "sint" | "bits_sext" => {
                let red = |k: usize, n: u32| -> Option<u128> { i(k)?.divmod(&pow2(n as u128)?).map(|x| x.1).and_then(|x| x.to_u128()) };
                match op {
                    "bits_not" => tu(!red(1, w(0)?)? & mask(w(0)?)),
                    "bits_and" => tu(red(1, w(0)?)? & red(2, w(0)?)?),
                    "bits_or" => tu(red(1, w(0)?)? | red(2, w(0)?)?),
                    "bits_xor" => tu(red(1, w(0)?)? ^ red(2, w(0)?)?),
                    "bits_shr" => {
                        let k = u(2)?;
                        let x = red(1, w(0)?)?;
                        tu(if k >= 128 { 0 } else { x >> k })
                    }
                    "bits_slice" => {
                        // (x / 2^lo) mod 2^(hi + 1 - lo)
                        let (hi, lo) = (u(1)?, u(2)?);
                        if hi < lo || hi >= 128 {
                            return None;
                        }
                        let x = i(0)?.divmod(&pow2(lo)?)?.0;
                        wrap_n(self, x, (hi - lo + 1) as u64)
                    }
                    "sint" => {
                        let n = w(0)?;
                        if n == 0 {
                            return None;
                        }
                        let x = red(1, n)?;
                        if x >> (n - 1) & 1 == 1 {
                            t(SInt::nat(Nat::from_u128(x)).add(&pow2(n as u128)?.neg()))
                        } else {
                            tu(x)
                        }
                    }
                    // sign extension from m to n bits
                    _ => {
                        let (m, n) = (w(0)?, w(1)?);
                        if m == 0 || m > n {
                            return None;
                        }
                        let x = red(2, m)?;
                        let neg = x >> (m - 1) & 1 == 1;
                        tu(if neg { (x | !mask(m)) & mask(n) } else { x & mask(m) })
                    }
                }
            }
            "int_and" => tu(u(0)? & u(1)?),
            "int_or" => tu(u(0)? | u(1)?),
            _ => None,
        }
    }
}

/// x mod 2^n as a literal
fn wrap_n(sp: &Simp, x: SInt, n: u64) -> Option<Term> {
    if n > 256 {
        return None;
    }
    Some(sp.of_int(x.divmod(&SInt::nat(crate::nat::Nat::pow2(n)))?.1))
}

impl<'a> Simp<'a> {
    fn new(env: &'a Env, lg: &Logic) -> Simp<'a> {
        let g = |n: &str| env.sym_by_name.get(n).copied();
        let unfold = ["bind_rel", "any_rel", "is_ok"].iter().filter_map(|n| g(n)).collect();
        let arith = ARITH.iter().filter_map(|n| g(n).map(|s| (s, *n))).collect();
        Simp {
            env,
            arith,
            keep: lg.simp_keep.borrow().clone(),
            no_hold: Default::default(),
            memo: Default::default(),
            nats: std::cell::RefCell::new(Vec::new()),
            footprints: Default::default(),
            word_params: Default::default(),
            prof: Default::default(),
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
                fn_build: g("fn_build"),
                ite: g("ite"),
                runs: g("runs"),
                mkprog: g("mkprog"),
                univ: g("univ"),
                bits_add: g("bits_add"),
                bits_of_int: g("bits_of_int"),
                int_add: g("int_add"),
                int_sub: g("int_sub"),
                int_div: g("int_div"),
                int_pow: g("int_pow"),
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

    /// An n-bit address as base + offset (mod 2^n): `bits_add` and
    /// `bits_sub` of numerals around at most one other term. The base must
    /// be a natural number (`nat_term`): for other sets the arithmetic is
    /// unspecified; None then.
    fn offset(&self, t: &Term, n: u32) -> Option<(Option<Term>, u128)> {
        let m = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
        let name = |g: SymId| self.env.syms[g as usize].name.as_str();
        match t.node() {
            Node::Nat(v) => {
                // (the low bits directly when it fits: no division)
                if let Some(x) = v.to_u128() {
                    return Some((None, x & m));
                }
                let low = v.divmod(&crate::nat::Nat::pow2(n.min(128) as u64))?.1.to_u128()?;
                Some((None, low & m))
            }
            Node::App(g, a) if (name(*g) == "bits_add" || name(*g) == "bits_sub") && a.len() == 3 && matches!(a[0].node(), Node::Nat(w) if w.to_u64() == Some(n as u64)) => {
                let (b1, c1) = self.offset(&a[1], n)?;
                let (b2, c2) = self.offset(&a[2], n)?;
                Some(if name(*g) == "bits_add" {
                    match (b1, b2) {
                        (b, None) | (None, b) => (b, c1.wrapping_add(c2) & m),
                        _ => (Some(t.clone()), 0),
                    }
                } else {
                    match (b1, b2) {
                        (b, None) => (b, c1.wrapping_sub(c2) & m),
                        (Some(x), Some(y)) if x == y => (None, c1.wrapping_sub(c2) & m),
                        _ => (Some(t.clone()), 0),
                    }
                })
            }
            // integer sums (effective addresses: base + index + disp);
            // x mod 2^n of x
            Node::App(g, a) if (name(*g) == "int_add" || name(*g) == "int_sub") && a.len() == 2 => {
                let (b1, c1) = self.offset(&a[0], n)?;
                let (b2, c2) = self.offset(&a[1], n)?;
                Some(match (b1, b2) {
                    (b, None) if name(*g) == "int_sub" => (b, c1.wrapping_sub(c2) & m),
                    (b, None) | (None, b) if name(*g) == "int_add" => (b, c1.wrapping_add(c2) & m),
                    _ => (Some(t.clone()), 0),
                })
            }
            Node::App(g, a) if name(*g) == "bits_of_int" && a.len() == 2 && matches!(a[0].node(), Node::Nat(w) if w.to_u64() == Some(n as u64)) => {
                self.offset(&a[1], n)
            }
            // a negative literal
            _ if self.int_lit(t).is_some_and(|v| v.neg) => {
                let v = self.int_lit(t)?;
                // (-x mod 2^n is the two's complement of x's low bits)
                if let Some(x) = v.m.to_u128() {
                    return Some((None, x.wrapping_neg() & m));
                }
                let low = v.divmod(&SInt::nat(crate::nat::Nat::pow2(n.min(128) as u64)))?.1.to_u128()?;
                Some((None, low & m))
            }
            // (arithmetic reads any set as its value: no typing needed)
            _ => Some((Some(t.clone()), 0)),
        }
    }

    /// The canonical form of an n-bit address `t` (a `bits_add` / `bits_sub`
    /// of integers): base + c, as `bits_add(n, base, c)`, the base alone
    /// when c = 0 and it is an n-bit word, or the numeral c.
    fn canonical_addr(&self, t: &Term, n: u64) -> Option<Term> {
        let (b, c) = self.offset(t, n as u32)?;
        let nat = |v: u128| Term::nat(crate::nat::Nat::from_u128(v));
        let out = match b {
            None => nat(c),
            Some(b) if b == *t => return None,
            Some(b) if c == 0 && self.bits_term(&b, n) => b,
            Some(b) => Term::app(self.s.bits_add?, vec![nat(n as u128), b, nat(c)]),
        };
        (out != *t).then_some(out)
    }

    /// `x - a` (n bits) as a numeral, when both have the same base.
    fn distance(&self, x: &Term, a: &Term, n: u32) -> Option<u128> {
        let m = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
        let (bx, cx) = self.offset(x, n)?;
        let (ba, ca) = self.offset(a, n)?;
        (bx == ba).then(|| cx.wrapping_sub(ca) & m)
    }

    /// A proposition equivalent to `t` (in the current typing context).
    fn eqv(&self, t: &Term) -> Term {
        let mut t = t.clone();
        for _ in 0..8 {
            let u = self.prop(&t, Pol::Other);
            if u == t {
                break;
            }
            t = u;
        }
        t
    }

    /// The fields that the definition of `f` reads of its (first-order)
    /// parameter i: literal keys k in `app(p, k)`, or those of the defined
    /// symbols p is passed to; None if p is used otherwise.
    fn footprint(&self, f: SymId, i: usize) -> Option<Vec<Term>> {
        if let Some(r) = self.footprints.borrow().get(&(f, i)) {
            return r.clone();
        }
        // (in progress: unknown, which also cuts recursion)
        self.footprints.borrow_mut().insert((f, i), None);
        let r = (|| {
            let SymKind::Defined { params, body } = &self.env.syms[f as usize].kind else { return None };
            let p = *params.get(i)?;
            if self.env.vars[p as usize].arity != 0 {
                return None;
            }
            let mut out = Vec::new();
            self.reads(body, p, &mut out).then_some(out)
        })();
        self.footprints.borrow_mut().insert((f, i), r.clone());
        r
    }

    /// The width n if the definition of `f` uses its (first-order) parameter
    /// i only as an argument of n-bit word operations (`bits_add(n, ..)`,
    /// `bits_sub(n, ..)`, `bits_of_int(n, ..)`), which depend on it only mod
    /// 2^n.
    fn word_param(&self, f: SymId, i: usize) -> Option<u64> {
        if let Some(r) = self.word_params.borrow().get(&(f, i)) {
            return *r;
        }
        let r = self.word_param_of(f, i);
        self.word_params.borrow_mut().insert((f, i), r);
        r
    }

    fn word_param_of(&self, f: SymId, i: usize) -> Option<u64> {
        let SymKind::Defined { params, body } = &self.env.syms[f as usize].kind else { return None };
        let p = *params.get(i)?;
        if self.env.vars[p as usize].arity != 0 {
            return None;
        }
        fn walk(sp: &Simp, t: &Term, p: crate::term::VarId, w: &mut Option<u64>) -> bool {
            let bare = |x: &Term| matches!(x.node(), Node::Var(v, xa) if *v == p && xa.is_empty());
            match t.node() {
                Node::Var(v, xa) => *v != p && xa.iter().all(|x| walk(sp, x, p, w)),
                Node::App(g, xs) => {
                    let name = sp.env.syms[*g as usize].name.as_str();
                    let word = matches!((name, xs.len()), ("bits_add" | "bits_sub", 3) | ("bits_of_int", 2));
                    for (j, x) in xs.iter().enumerate() {
                        if bare(x) {
                            let n = match xs[0].node() {
                                Node::Nat(n) => n.to_u64(),
                                _ => None,
                            };
                            match (word && j >= 1, n) {
                                (true, Some(n)) if w.is_none_or(|m| m == n) => *w = Some(n),
                                _ => return false,
                            }
                        } else if !walk(sp, x, p, w) {
                            return false;
                        }
                    }
                    true
                }
                _ => true,
            }
        }
        let mut w = None;
        (walk(self, body, p, &mut w)).then_some(w).flatten()
    }

    fn reads(&self, t: &Term, p: crate::term::VarId, out: &mut Vec<Term>) -> bool {
        let bare = |x: &Term| matches!(x.node(), Node::Var(v, xa) if *v == p && xa.is_empty());
        match t.node() {
            Node::Var(v, xa) => *v != p && xa.iter().all(|x| self.reads(x, p, out)),
            Node::App(g, xs) => {
                if is(*g, self.s.app) && bare(&xs[0]) && matches!(xs[1].node(), Node::Bytes(_) | Node::Nat(_)) {
                    if !out.contains(&xs[1]) {
                        out.push(xs[1].clone());
                    }
                    return true;
                }
                for (j, x) in xs.iter().enumerate() {
                    if bare(x) {
                        match self.footprint(*g, j) {
                            Some(fs) => {
                                for k in fs {
                                    if !out.contains(&k) {
                                        out.push(k);
                                    }
                                }
                            }
                            None => return false,
                        }
                    } else if !self.reads(x, p, out) {
                        return false;
                    }
                }
                true
            }
            _ => true,
        }
    }

    /// The typing context of a path: the terms its literals say are
    /// integers (`t in int`), naturals (`t in omega`) or words (`t in
    /// bits(k)`).
    fn set_nats(&self, lits: &[Term]) {
        let s = &self.s;
        let mut out = Vec::new();
        for l in lits {
            if let Node::App(i, ab) = l.node() {
                if is(*i, s.in_) {
                    match ab[1].node() {
                        Node::App(o, x) if x.is_empty() && is(*o, s.omega) => out.push((ab[0].clone(), Ty::Nat)),
                        Node::App(o, x) if x.is_empty() && self.env.syms[*o as usize].name == "int" => out.push((ab[0].clone(), Ty::Int)),
                        Node::App(b, x) if self.env.syms[*b as usize].name == "bits" && x.len() == 1 => {
                            if let Node::Nat(k) = x[0].node() {
                                if let Some(k) = k.to_u64() {
                                    out.push((ab[0].clone(), Ty::Bits(k)));
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        // (`term` depends on the typing: its memo only for this one)
        if *self.nats.borrow() != out {
            self.memo.borrow_mut().clear();
            *self.nats.borrow_mut() = out;
        }
    }

    fn known(&self, t: &Term, ok: impl Fn(Ty) -> bool) -> bool {
        self.nats.borrow().iter().any(|(u, k)| u == t && ok(*k))
    }

    /// `t` is an n-bit word (in bits(n)): a numeral below 2^n, known on the
    /// path, or a word operation of width at most n (their results are
    /// always words: arithmetic is total).
    fn bits_term(&self, t: &Term, n: u64) -> bool {
        let width = |x: &Term| match x.node() {
            Node::Nat(v) => v.to_u64(),
            _ => None,
        };
        if let Node::Nat(v) = t.node() {
            return v.to_u128().is_some_and(|x| n >= 128 || x < (1u128 << n));
        }
        if self.known(t, |k| matches!(k, Ty::Bits(j) if j <= n)) {
            return true;
        }
        let Node::App(f, a) = t.node() else { return false };
        match self.env.syms[*f as usize].name.as_str() {
            "bits_add" | "bits_mul" | "bits_sub" | "bits_shl" | "bits_shr" | "bits_and" | "bits_or" | "bits_xor" | "bits_sar" if a.len() == 3 => {
                width(&a[0]).is_some_and(|k| k <= n)
            }
            "bits_neg" | "bits_of_int" | "bits_not" if a.len() == 2 => width(&a[0]).is_some_and(|k| k <= n),
            "bits_sext" if a.len() == 3 => width(&a[1]).is_some_and(|k| k <= n),
            // x / 2^lo mod 2^(hi + 1 - lo)
            "bits_slice" if a.len() == 3 => match (width(&a[1]), width(&a[2])) {
                (Some(hi), Some(lo)) => hi >= lo && hi + 1 - lo <= n,
                _ => false,
            },
            // 0 <= x mod k < k <= 2^n
            "int_mod" if a.len() == 2 => match a[1].node() {
                Node::Nat(k) => !k.is_zero() && (n >= 128 || k.to_u128().is_some_and(|k| k <= 1u128 << n)),
                _ => false,
            },
            // a definition whose body is a word of a computable width (e.g.
            // `le(b, a, n) := bits_of_int(8 * n, ..)`)
            _ => match &self.env.syms[*f as usize].kind {
                SymKind::Defined { params, body } if params.len() == a.len() => match body.node() {
                    Node::App(g, gb) if self.env.syms[*g as usize].name == "bits_of_int" && gb.len() == 2 => {
                        let mut wt = gb[0].clone();
                        for (p, x) in params.iter().zip(a) {
                            if self.env.vars[*p as usize].arity != 0 {
                                return false;
                            }
                            wt = wt.subst_var(*p, x, &self.env.binders_fn());
                        }
                        width(&self.term(&wt)).is_some_and(|k| k <= n)
                    }
                    _ => false,
                },
                _ => false,
            },
        }
    }

    /// `t` is a natural (in omega).
    fn nat_term(&self, t: &Term) -> bool {
        if matches!(t.node(), Node::Nat(_)) || self.known(t, |k| k != Ty::Int) {
            return true;
        }
        if (0..=128).any(|n| n % 8 == 0 && self.bits_term(t, n)) {
            return true;
        }
        let Node::App(f, a) = t.node() else { return false };
        match self.env.syms[*f as usize].name.as_str() {
            "int_abs" => true,
            "int_mod" if a.len() == 2 => matches!(a[1].node(), Node::Nat(k) if !k.is_zero()),
            _ => false,
        }
    }

    /// `t` is an integer (in int): a literal, an operation of arithmetic
    /// (their results are integers), or known on the path.
    fn int_term(&self, t: &Term) -> bool {
        if self.int_lit(t).is_some() || self.known(t, |_| true) {
            return true;
        }
        let Node::App(f, _) = t.node() else { return false };
        const INT_OPS: &[&str] = &[
            "int_val", "int_abs", "int_neg", "int_succ", "int_pred", "int_add", "int_sub", "int_mul", "int_pow", "int_div", "int_mod", "int_sum", "pow2",
            "sint",
        ];
        INT_OPS.contains(&self.env.syms[*f as usize].name.as_str()) || self.nat_term(t)
    }

    /// Reads through a store (`x86_64_linux.store_le(b, a, n, v)`, the
    /// memory b with the n bytes at a replaced by v's, little-endian): a
    /// byte at a known distance from a, and `le` of the same or a disjoint
    /// range (distances from the definitions; addresses are 64-bit).
    fn read_store(&self, f: SymId, args: &[Term]) -> Option<Term> {
        let name = |g: SymId| self.env.syms[g as usize].name.as_str();
        let store = |t: &Term| -> Option<Vec<Term>> {
            match t.node() {
                Node::App(g, b) if name(*g) == "x86_64_linux.store_le" && b.len() == 4 => Some(b.to_vec()),
                _ => None,
            }
        };
        let lit = |t: &Term| match t.node() {
            Node::Nat(v) => v.to_u128(),
            _ => None,
        };
        let nat = |v: u128| Term::nat(crate::nat::Nat::from_u128(v));
        let (bits_of_int, int_div, pow) = (self.s.bits_of_int?, self.s.int_div?, self.s.int_pow?);
        if is(f, self.s.app) {
            // app(store_le(b, a, n, v), x)
            let st = store(&args[0])?;
            let n = lit(&st[2])?;
            let d = self.distance(&args[1], &st[1], 64)?;
            if d < n {
                let byte = Term::app(int_div, vec![st[3].clone(), Term::app(pow, vec![nat(256), nat(d)])]);
                return Some(self.term(&Term::app(bits_of_int, vec![nat(8), byte])));
            }
            return Some(self.term(&Term::app(f, vec![st[0].clone(), args[1].clone()])));
        }
        if name(f) == "x86_64_linux.le" && args.len() == 3 {
            // le(store_le(b, a, n, v), c, m)
            let st = store(&args[0])?;
            let (n, m) = (lit(&st[2])?, lit(&args[2])?);
            let d = self.distance(&args[1], &st[1], 64)?;
            if d == 0 && m == n && n <= 16 {
                return Some(self.term(&Term::app(bits_of_int, vec![nat(8 * n), st[3].clone()])));
            }
            if n <= d && d.checked_add(m).is_some_and(|e| e <= 1u128 << 64) {
                return Some(self.term(&Term::app(f, vec![st[0].clone(), args[1].clone(), args[2].clone()])));
            }
        }
        None
    }

    /// Byte strings: `bytes_len(B)`, `bytes_at(B, i)` (builtins), and a
    /// literal as a list (`bytes_seq(B) = fn_build(bytes_len(B), i.
    /// bytes_at(B, i))`): its length `seq_len` (the domain) and its byte at
    /// a numeral index in range.
    fn bytes(&self, f: SymId, args: &[Term]) -> Option<Term> {
        let name = self.env.syms[f as usize].name.as_str();
        let lit = |t: &Term| -> Option<std::rc::Rc<[u8]>> {
            match t.node() {
                Node::Bytes(b) => Some(b.clone()),
                _ => None,
            }
        };
        let seq = |t: &Term| -> Option<std::rc::Rc<[u8]>> {
            match t.node() {
                Node::App(g, b) if self.env.syms[*g as usize].name == "bytes_seq" && b.len() == 1 => lit(&b[0]),
                _ => None,
            }
        };
        let idx = |t: &Term| match t.node() {
            Node::Nat(v) => v.to_u64(),
            _ => None,
        };
        let nat = |n: u64| Term::nat(crate::nat::Nat::from_u64(n));
        match (name, args.len()) {
            ("bytes_len", 1) => Some(nat(lit(&args[0])?.len() as u64)),
            ("seq_len", 1) => Some(nat(seq(&args[0])?.len() as u64)),
            ("bytes_at", 2) => {
                let (b, i) = (lit(&args[0])?, idx(&args[1])?);
                b.get(i as usize).map(|&x| nat(x as u64))
            }
            ("app", 2) => {
                let (b, i) = (seq(&args[0])?, idx(&args[1])?);
                b.get(i as usize).map(|&x| nat(x as u64))
            }
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
        if !matches!(t.node(), Node::App(..)) {
            return t.clone();
        }
        let key = t.node() as *const Node as usize;
        if let Some((_, r)) = self.memo.borrow().get(&key) {
            return r.clone();
        }
        let r = self.term_uncached(t);
        self.memo.borrow_mut().insert(key, (t.clone(), r.clone()));
        r
    }

    fn term_uncached(&self, t: &Term) -> Term {
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
            return t.with_args(vec![c, self.term(&a[1]), self.term(&a[2])]);
        }
        let mut args: Vec<Term> = a.iter().map(|x| self.term(x)).collect();
        // an argument updated at a field the definition never reads (e.g.
        // `can_access(fn_update(vm, "bytes", b), x, k)`, which reads only
        // the pages): the update dropped
        if matches!(self.env.syms[f as usize].kind, SymKind::Defined { .. }) {
            for i in 0..args.len() {
                while let Node::App(u, ub) = args[i].node() {
                    if !is(*u, s.fn_update) || !matches!(ub[1].node(), Node::Bytes(_) | Node::Nat(_)) {
                        break;
                    }
                    match self.footprint(f, i) {
                        Some(fs) if fs.iter().all(|k| distinct_literals(k, &ub[1])) => {
                            let v = ub[0].clone();
                            args[i] = v;
                        }
                        _ => break,
                    }
                }
            }
        }
        // an argument the definition uses only mod 2^n (in n-bit word
        // operations, e.g. an address): in canonical n-bit form
        if matches!(self.env.syms[f as usize].kind, SymKind::Defined { .. }) {
            for i in 0..args.len() {
                let Some(n) = self.word_param(f, i) else { continue };
                if !matches!(args[i].node(), Node::App(g, _) if matches!(self.env.syms[*g as usize].name.as_str(), "int_add" | "int_sub")) {
                    continue;
                }
                let Some(boi) = self.s.bits_of_int else { continue };
                let w = self.term(&Term::app(boi, vec![Term::nat(crate::nat::Nat::from_u64(n)), args[i].clone()]));
                if matches!(w.node(), Node::Nat(_)) || matches!(w.node(), Node::App(g, _) if self.env.syms[*g as usize].name == "bits_add") {
                    args[i] = w;
                }
            }
        }
        let args = args;
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
                // (`some(x) = tag(1, x)`, `none = tag(0, empty)`)
                if is(g, s.some) && (fst || snd) {
                    return if fst { nat(1) } else { b[0].clone() };
                }
                if is(g, s.none) && b.is_empty() && (fst || snd) {
                    if fst {
                        return nat(0);
                    }
                    if let Some(e) = s.empty {
                        return Term::app(e, vec![]);
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
            if let Some(v) = self.compute(op, &args) {
                return v;
            }
            // x + c1 + c2 = x + (c1 + c2), for any x (arithmetic is on the
            // value of x); x + 0 = x for an integer x
            // 0 + x = x for an integer x
            if *op == "int_add" && args.len() == 2 && self.int_lit(&args[0]).is_some_and(|c| c.m.is_zero()) && self.int_term(&args[1]) {
                return args[1].clone();
            }
            if (*op == "int_add" || *op == "int_sub") && args.len() == 2 {
                if let Some(c) = self.int_lit(&args[1]) {
                    let c = if *op == "int_sub" { c.neg() } else { c };
                    let (x, c) = match args[0].node() {
                        Node::App(g, b) if b.len() == 2 && matches!(self.arith.get(g), Some(&"int_add") | Some(&"int_sub")) => match self.int_lit(&b[1]) {
                            Some(c0) => (b[0].clone(), c.add(&if self.arith.get(g) == Some(&"int_sub") { c0.neg() } else { c0 })),
                            None => (args[0].clone(), c),
                        },
                        _ => (args[0].clone(), c),
                    };
                    if c.m.is_zero() && self.int_term(&x) {
                        return x;
                    }
                    let (name, m) = if c.neg { ("int_sub", SInt::nat(c.m.clone())) } else { ("int_add", c.clone()) };
                    if let Some(g) = if name == "int_sub" { self.s.int_sub } else { self.s.int_add } {
                        let out = Term::app(g, vec![x, self.of_int(m)]);
                        if !matches!(out.node(), Node::App(h, b) if *h == f && b[..] == args[..]) {
                            return self.term(&out);
                        }
                    }
                }
            }
            if *op == "int_val" && self.int_term(&args[0]) {
                return args[0].clone();
            }
            // the operands of an n-bit addition are read mod 2^n: an integer
            // sum among them in canonical n-bit form
            if (*op == "bits_add" || *op == "bits_sub") && args.len() == 3 {
                if let (Node::Nat(w), Some(boi)) = (args[0].node(), self.s.bits_of_int) {
                    let w = Term::nat(w.clone());
                    let mut new = args.clone();
                    let mut changed = false;
                    for x in new.iter_mut().skip(1) {
                        if matches!(x.node(), Node::App(g, _) if matches!(self.arith.get(g), Some(&"int_add") | Some(&"int_sub"))) {
                            let c = self.term(&Term::app(boi, vec![w.clone(), x.clone()]));
                            let sum = |y: &Term| matches!(y.node(), Node::App(g, _) if matches!(self.arith.get(g), Some(&"int_add") | Some(&"int_sub")));
                            if matches!(c.node(), Node::Nat(_)) || matches!(c.node(), Node::App(g, cb) if is(*g, self.s.bits_add) && !cb.iter().any(sum)) {
                                *x = c;
                                changed = true;
                            }
                        }
                    }
                    if changed {
                        return self.term(&t.with_args(new));
                    }
                }
            }
            // addresses in canonical form: base + offset
            if ((*op == "bits_add" || *op == "bits_sub") && args.len() == 3) || (*op == "bits_of_int" && args.len() == 2 && !self.bits_term(&args[1], 64)) {
                if let Node::Nat(w) = args[0].node() {
                    if let Some(n) = w.to_u64().filter(|&n| n <= 128) {
                        if let Some(c) = self.canonical_addr(&t.with_args(args.clone()), n) {
                            return c;
                        }
                    }
                }
            }
            // an n-bit x is its own n-bit value
            if *op == "bits_of_int" && args.len() == 2 {
                if let Node::Nat(w) = args[0].node() {
                    if w.to_u64().is_some_and(|n| n <= 256 && self.bits_term(&args[1], n)) {
                        return args[1].clone();
                    }
                }
            }
            // typed words: all bits of x (`bits_slice(x, n-1, 0)` of an n-bit
            // x); `bits_set_slice(n, x, n-1, 0, v)` of an n-bit v is v
            if *op == "bits_slice" && args.len() == 3 {
                if let (Node::Nat(hi), Node::Nat(lo)) = (args[1].node(), args[2].node()) {
                    if lo.is_zero() && hi.to_u64().is_some_and(|h| h < 256 && self.bits_term(&args[0], h + 1)) {
                        return args[0].clone();
                    }
                }
            }
            // addresses: `bits_sub` of the same base is its offset
            if *op == "bits_sub" {
                if let (Node::Nat(w), 3) = (args[0].node(), args.len()) {
                    if let Some(n) = w.to_u64().filter(|&n| n <= 128) {
                        if let Some(d) = self.distance(&args[1], &args[2], n as u32) {
                            return Term::nat(crate::nat::Nat::from_u128(d));
                        }
                    }
                }
            }
        }
        if let Some(v) = self.read_store(f, &args) {
            return v;
        }
        if let Some(v) = self.bytes(f, &args) {
            return v;
        }
        if self.env.syms[f as usize].name == "bits_set_slice" && args.len() == 5 {
            let num = |x: &Term| match x.node() {
                Node::Nat(v) => v.to_u64(),
                _ => None,
            };
            if let (Some(n), Some(hi), Some(0)) = (num(&args[0]), num(&args[2]), num(&args[3])) {
                if n >= 1 && hi == n - 1 && self.bits_term(&args[4], n) {
                    return args[4].clone();
                }
            }
        }
        // a constant defined as a numeral (`PAGE`)
        if args.is_empty() {
            if let SymKind::Defined { params, body } = &self.env.syms[f as usize].kind {
                if params.is_empty() && matches!(body.node(), Node::Nat(_)) && !self.keep.contains(&f) {
                    return body.clone();
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
                    // `app(fn_build(omega, x. v), n)` = v(n) for a numeral n
                    // (`app_fn_build`: n in omega)
                    Some((g, b)) if is(g, s.fn_build) && matches!(args[1].node(), Node::Nat(_)) && matches!(b[0].node(), Node::App(o, _) if is(*o, s.omega)) => {
                        return self.term(&inst_k(self.env, &b[1], &[args[1].clone()]));
                    }
                    // records through restriction, ghost parts and merges
                    // (`app_ext`: the pairs with first element k are the same)
                    Some((g, b)) => {
                        let name = self.env.syms[g as usize].name.as_str();
                        let k = &args[1];
                        match name {
                            // no pair at all: `empty` (app's default)
                            "empty" if b.is_empty() => return m,
                            "restrict" => match self.key_in(k, &b[1]) {
                                Some(true) => {
                                    m = b[0].clone();
                                    continue;
                                }
                                Some(false) if s.empty.is_some() => return Term::app(s.empty.unwrap(), vec![]),
                                _ => {}
                            },
                            "ghost_part" => match self.key_in(k, &b[1]) {
                                Some(true) if s.empty.is_some() => return Term::app(s.empty.unwrap(), vec![]),
                                Some(false) => {
                                    m = b[0].clone();
                                    continue;
                                }
                                _ => {}
                            },
                            "union2" | "rec_merge" => {
                                if self.lacks(&b[1], k) {
                                    m = b[0].clone();
                                    continue;
                                }
                                if self.lacks(&b[0], k) {
                                    m = b[1].clone();
                                    continue;
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
                break;
            }
            return Term::app(f, vec![m, args[1].clone()]);
        }
        // an update of a field updated before (with only other literal keys
        // in between): the earlier update is overwritten
        if is(f, s.fn_update) {
            let (k, v) = (&args[1], &args[2]);
            let mut inner = Vec::new();
            let mut m = args[0].clone();
            while let Some((g, b)) = head(&m) {
                if !is(g, s.fn_update) {
                    break;
                }
                if b[1] == *k {
                    // drop it, keep the updates above it
                    let mut r = b[0].clone();
                    for (ik, iv) in inner.into_iter().rev() {
                        r = Term::app(f, vec![r, ik, iv]);
                    }
                    return Term::app(f, vec![r, k.clone(), v.clone()]);
                }
                if !distinct_literals(&b[1], k) {
                    break;
                }
                inner.push((b[1].clone(), b[2].clone()));
                m = b[0].clone();
            }
        }
        t.with_args(args)
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
            if self.is_false(&x) {
                return self.tt();
            }
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
            return t.with_args(vec![x, y]);
        }
        // (unchanged operands, none decided: the term itself, not a copy)
        let decided = |x: &Term| self.is_true(x) || self.is_false(x);
        if is(f, s.not) {
            let x = self.prop(&a[0], pol.flip());
            if x.ptr_eq(&a[0]) && !decided(&x) && !matches!(x.node(), Node::App(n, _) if is(*n, s.not)) {
                return t.clone();
            }
            return self.not(x);
        }
        // (short-circuit: a decided left side spares simplifying the right,
        // e.g. the arms of a `match` on a known constructor)
        if is(f, s.and) {
            let x = self.prop(&a[0], pol);
            if self.is_false(&x) {
                return x;
            }
            let y = self.prop(&a[1], pol);
            if x.ptr_eq(&a[0]) && y.ptr_eq(&a[1]) && !decided(&x) && !decided(&y) {
                return t.clone();
            }
            return self.and(x, y);
        }
        if is(f, s.or) {
            let x = self.prop(&a[0], pol);
            if self.is_true(&x) {
                return x;
            }
            let y = self.prop(&a[1], pol);
            if x.ptr_eq(&a[0]) && y.ptr_eq(&a[1]) && !decided(&x) && !decided(&y) {
                return t.clone();
            }
            return self.or(x, y);
        }
        if is(f, s.ne) {
            return self.not(self.eq(&a[0], &a[1]));
        }
        if f == s.eq {
            let r = self.eq(&a[0], &a[1]);
            if matches!(r.node(), Node::App(e, b) if *e == f && b[0].ptr_eq(&a[0]) && b[1].ptr_eq(&a[1])) {
                return t.clone();
            }
            return r;
        }
        if f == s.ex {
            return self.ex(&self.prop(&a[0], pol), pol == Pol::Goal);
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
        if is(f, s.runs) && pol != Pol::Other {
            let mut p = self.term(&a[0]);
            // a procedure: its definition is a `mkprog` (unless kept folded)
            if let Node::App(g, ga) = p.node() {
                if !is(*g, s.mkprog) && !self.keep.contains(g) {
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
                    let body = self.prop(&inst_k(self.env, &r[0], &[st.clone(), o.clone()]), pol);
                    if pol == Pol::Pos {
                        return body;
                    }
                    // (in a goal: also the typing `pair(S, O) in univ(1)`)
                    let (Some(in_), Some(univ), Some(pair)) = (s.in_, s.univ, s.pair) else { return Term::app(f, vec![p, st, o]) };
                    let one = Term::nat(crate::nat::Nat::from_u64(1));
                    let ty = Term::app(in_, vec![Term::app(pair, vec![st, o]), Term::app(univ, vec![one])]);
                    return self.and(self.prop(&ty, pol), body);
                }
            }
            return Term::app(f, vec![p, self.term(&a[1]), self.term(&a[2])]);
        }
        // comprehension: `z in set_select(s, x. p)` <-> `z in s && p(z)`
        if is(f, s.in_) {
            if let Node::App(un, _) = a[1].node() {
                if is(*un, s.univ) {
                    if let Some(r) = self.univ_mem(&self.term(&a[0]), &a[1], pol) {
                        return r;
                    }
                }
            }
            if let Node::App(sel, sb) = a[1].node() {
                if is(*sel, s.set_select) {
                    let z = self.term(&a[0]);
                    let mem = Term::app(f, vec![z.clone(), sb[0].clone()]);
                    return self.and(self.prop(&mem, pol), self.prop(&inst_k(self.env, &sb[1], &[z]), pol));
                }
            }
            // finite sets: `upair`, `single`, `insert`, `union2`, `empty`,
            // and constants defined as one (`bool`)
            let z = self.term(&a[0]);
            let mut set = self.term(&a[1]);
            for _ in 0..2 {
                let Node::App(g, gb) = set.node() else { break };
                let name = self.env.syms.get(*g as usize).map(|y| y.name.as_str()).unwrap_or("");
                let mem = |x: &Term| Term::app(f, vec![z.clone(), x.clone()]);
                match name {
                    "empty" if gb.is_empty() => return self.ff(),
                    "upair" => return self.or(self.eq(&z, &gb[0]), self.eq(&z, &gb[1])),
                    "single" => return self.eq(&z, &gb[0]),
                    "insert" => return self.or(self.eq(&z, &gb[0]), self.prop(&mem(&gb[1]), pol)),
                    "union2" => return self.or(self.prop(&mem(&gb[0]), pol), self.prop(&mem(&gb[1]), pol)),
                    _ if gb.is_empty() => match self.unfold(*g, gb) {
                        Some(u) => set = self.term(&u),
                        None => break,
                    },
                    _ => break,
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

    /// `k in d`, when decided (k a literal, d a finite set of literals).
    fn key_in(&self, k: &Term, d: &Term) -> Option<bool> {
        let r = self.prop(&Term::app(self.s.in_?, vec![k.clone(), d.clone()]), Pol::Other);
        if self.is_true(&r) {
            Some(true)
        } else if self.is_false(&r) {
            Some(false)
        } else {
            None
        }
    }

    /// `x` has no pair with first element k (a record without the field k).
    fn lacks(&self, x: &Term, k: &Term) -> bool {
        let Node::App(g, b) = x.node() else { return false };
        match self.env.syms[*g as usize].name.as_str() {
            "empty" => b.is_empty(),
            "ghost_part" => self.key_in(k, &b[1]) == Some(true),
            "restrict" => self.key_in(k, &b[1]) == Some(false),
            "fn_update" => distinct_literals(&b[1], k) && self.lacks(&b[0], k),
            "union2" | "rec_merge" => self.lacks(&b[0], k) && self.lacks(&b[1], k),
            _ => false,
        }
    }

    /// `x in univ(u)` by the closure of universes: a pair (an outcome, a
    /// tagged value) is in it iff its parts are; in a goal, also the
    /// stronger: a finite set or function update built from members, a
    /// component (`app`, `fst`, `snd`, which are `empty` when undefined) of
    /// a member, either branch of an `ite`; integers (in `univ(1)` and
    /// above, as `omega` is) and finite data always.
    fn univ_mem(&self, x: &Term, set: &Term, pol: Pol) -> Option<Term> {
        let s = &self.s;
        let mem = |y: &Term| self.prop(&Term::app(s.in_.expect("in"), vec![y.clone(), set.clone()]), pol);
        let all = |ys: &[Term]| ys.iter().fold(self.tt(), |acc, y| self.and(acc, mem(y)));
        let above_omega = match set.node() {
            Node::App(_, ub) => matches!(ub[0].node(), Node::Nat(n) if *n != crate::nat::Nat::zero()),
            _ => false,
        };
        if above_omega && self.int_term(x) {
            return Some(self.tt());
        }
        match x.node() {
            Node::Nat(_) | Node::Bytes(_) => Some(self.tt()),
            Node::App(h, args) => {
                let h = *h;
                let name = self.env.syms.get(h as usize).map(|y| y.name.as_str()).unwrap_or("");
                if [s.pair, s.tag, s.ok, s.exc, s.diverge, s.some].iter().any(|c| is(h, *c)) || name == "upair" || name == "single" {
                    return Some(all(args));
                }
                if is(h, s.none) || name == "empty" {
                    return Some(self.tt());
                }
                if pol != Pol::Goal {
                    return None;
                }
                if is(h, s.fn_update) || name == "insert" || name == "union2" || name == "rec_merge" {
                    return Some(all(args));
                }
                if [s.app, s.fst, s.snd, s.out_state, s.out_value].iter().any(|c| is(h, *c)) {
                    return Some(mem(&args[0]));
                }
                if is(h, s.ite) {
                    return Some(all(&args[1..]));
                }
                None
            }
            _ => None,
        }
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
        match name {
            "int_lt" => return Some(self.int_lit(&b[0])?.lt(&self.int_lit(&b[1])?)),
            "int_le" => return Some(!self.int_lit(&b[1])?.lt(&self.int_lit(&b[0])?)),
            _ => {}
        }
        if is(*m, s.in_) {
            // integer literals: integers; the negative ones in no set of naturals
            if let Some(v) = self.int_lit(&b[0]) {
                if let Node::App(o, ob) = b[1].node() {
                    let set = self.env.syms[*o as usize].name.as_str();
                    if set == "int" && ob.is_empty() {
                        return Some(true);
                    }
                    if v.neg && (is(*o, s.omega) || set == "bits") {
                        return Some(false);
                    }
                }
            }
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
                // a set literal of numerals: `insert(a, s)`, `single(a)`, `empty`
                let mut set = b[1].clone();
                loop {
                    let Node::App(g, gb) = set.node() else { break };
                    match self.env.syms.get(*g as usize).map(|y| y.name.as_str()) {
                        Some("empty") => return Some(false),
                        Some("single") => return Some(x == lit(&gb[0])?),
                        Some("insert") => {
                            if x == lit(&gb[0])? {
                                return Some(true);
                            }
                            set = gb[1].clone();
                        }
                        _ => break,
                    }
                }
            }
            return Some(x < lit(&b[1])?);
        }
        match name {
            "ord_lt" | "lit_lt" => Some(lit(&b[0])? < lit(&b[1])?),
            "ord_le" => Some(lit(&b[0])? <= lit(&b[1])?),
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
        // two n-bit words with the same base: equal iff the offsets are
        // (both words: each is its value mod 2^n)
        // (the offsets first: cheaper than the typing)
        for n in [64u64, 32, 16, 8] {
            if let Some(d) = self.distance(&x, &y, n as u32) {
                if self.bits_term(&x, n) && self.bits_term(&y, n) {
                    return if d == 0 { self.tt() } else { self.ff() };
                }
            }
        }
        // the same function updated at the same key: equal iff the values are
        // (the pair (k, a) is in the one exactly if it is in the other)
        if let (Node::App(f1, u), Node::App(f2, w)) = (x.node(), y.node()) {
            if is(*f1, s.fn_update) && is(*f2, s.fn_update) && u[0] == w[0] && u[1] == w[1] {
                return self.eq(&u[2], &w[2]);
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

    /// `ex x. body` (body under one binder); in the goal also the steps
    /// that prepare choosing witnesses (they multiply terms in facts)
    fn ex(&self, body: &Term, goal: bool) -> Term {
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
        if !goal {
            // distribute over a disjunction, so each branch can use one-point
            if let Node::App(o, ab) = body.node() {
                if is(*o, self.s.or) {
                    return self.or(self.ex(&ab[0], goal), self.ex(&ab[1], goal));
                }
            }
            return Term::app(self.s.ex, vec![body.clone()]);
        }
        // one-point through an inner existential (R without x):
        // `ex x. A(x) && (ex y. x = t(y) && R(y))` <-> `ex y. A(t(y)) && R(y)`
        let bf = self.env.binders_fn();
        for (i, c) in cs.iter().enumerate() {
            let Node::App(e2, eb) = c.node() else { continue };
            if *e2 != self.s.ex {
                continue;
            }
            // (inside: BVar(0) is y, BVar(1) is x)
            let mut ds = Vec::new();
            self.conjuncts(&eb[0], &mut ds);
            let pt = ds.iter().enumerate().find_map(|(k, d)| match d.node() {
                Node::App(e, ab) if *e == self.s.eq => [(&ab[0], &ab[1]), (&ab[1], &ab[0])]
                    .into_iter()
                    .find(|(v, t)| matches!(v.node(), Node::BVar(1)) && !has_bvar(self.env, t, 1))
                    .map(|(_, t)| (k, t.clone())),
                _ => None,
            });
            let Some((k, t)) = pt else { continue };
            if ds.iter().enumerate().any(|(j, d)| j != k && has_bvar(self.env, d, 1)) {
                continue;
            }
            let t = lower(self.env, &t, 1);
            let mut a = self.tt();
            for (j, d) in cs.iter().enumerate() {
                if j != i {
                    a = self.and(a, d.clone());
                }
            }
            let mut r = inst_k(self.env, &a.shift(1, 1, &bf), &[t]);
            for (j, d) in ds.iter().enumerate() {
                if j != k {
                    r = self.and(r, lower(self.env, d, 1));
                }
            }
            return self.ex(&self.prop(&r, Pol::Other), goal);
        }
        // an equation for x deeper in a conjunct `ex y. D`: swap,
        // `ex x. A(x) && (ex y. D(x, y))` <-> `ex y. ex x. A(x) && D(x, y)`
        // (until the equation is one level down)
        fn deep_point(sp: &Simp, d: &Term, depth: u32) -> bool {
            let mut ds = Vec::new();
            sp.conjuncts(d, &mut ds);
            ds.iter().any(|c| match c.node() {
                Node::App(e, ab) if *e == sp.s.eq => [(&ab[0], &ab[1]), (&ab[1], &ab[0])]
                    .iter()
                    .any(|(v, t)| matches!(v.node(), Node::BVar(j) if *j == depth) && !has_bvar(sp.env, t, depth)),
                Node::App(e, ab) if *e == sp.s.ex => deep_point(sp, &ab[0], depth + 1),
                _ => false,
            })
        }
        for (i, c) in cs.iter().enumerate() {
            let Node::App(e2, eb) = c.node() else { continue };
            if *e2 != self.s.ex || !deep_point(self, &eb[0], 1) {
                continue;
            }
            let mut a = self.tt();
            for (j, d) in cs.iter().enumerate() {
                if j != i {
                    a = self.and(a, d.clone());
                }
            }
            let nb = self.and(a.shift(1, 1, &bf), swap01(self.env, &eb[0], 0));
            let inner = self.ex(&self.prop(&nb, Pol::Other), goal);
            return self.ex(&inner, goal);
        }
        // a conjunct `A || (B && x = t)` (e.g. `require`'s): distribute, so
        // that branch can use one-point
        let point = |d: &Term| {
            let mut ds = Vec::new();
            self.conjuncts(d, &mut ds);
            ds.iter().any(|c| match c.node() {
                Node::App(e, ab) if *e == self.s.eq => [(&ab[0], &ab[1]), (&ab[1], &ab[0])]
                    .iter()
                    .any(|(v, t)| matches!(v.node(), Node::BVar(0)) && !has_bvar(self.env, t, 0)),
                _ => false,
            })
        };
        // `x = c` with c a constant (no variables): one of finitely many values
        fn ground(t: &Term) -> bool {
            match t.node() {
                Node::Var(..) | Node::BVar(_) => false,
                Node::App(_, a) => a.iter().all(ground),
                _ => true,
            }
        }
        let const_point = |d: &Term| match d.node() {
            Node::App(e, ab) if *e == self.s.eq => [(&ab[0], &ab[1]), (&ab[1], &ab[0])].iter().any(|(v, t)| matches!(v.node(), Node::BVar(0)) && ground(t)),
            _ => false,
        };
        for (i, c) in cs.iter().enumerate() {
            let mut ds = Vec::new();
            self.disjuncts(c, &mut ds);
            // (not a mere choice among values, `x = a || x = b`: that stays,
            // for matching x with a path's variable)
            if ds.len() > 1 && ds.iter().any(|d| point(d)) && !ds.iter().all(|d| const_point(d)) {
                let mut rest = self.tt();
                for (j, d) in cs.iter().enumerate() {
                    if j != i {
                        rest = self.and(rest, d.clone());
                    }
                }
                let mut r = self.ff();
                for d in ds {
                    r = self.or(r, self.ex(&self.and(d, rest.clone()), goal));
                }
                return r;
            }
        }
        // distribute over a disjunction, so each branch can use one-point
        if let Node::App(o, ab) = body.node() {
            if is(*o, self.s.or) {
                return self.or(self.ex(&ab[0], goal), self.ex(&ab[1], goal));
            }
        }
        // x only through its projections: `ex x. P(fst(x), snd(x))` <->
        // `ex a b. P(a, b)` (x = pair(a, b); `x in univ(u)` is `a in univ(u)
        // && b in univ(u)`, as fst and snd stay in universes)
        if let Some(nb) = self.proj_split(body, 0) {
            let inner = self.ex(&self.prop(&nb, Pol::Other), goal);
            return self.ex(&inner, goal);
        }
        // miniscoping: the conjuncts without x out
        let (inner, outer): (Vec<&Term>, Vec<&Term>) = cs.iter().partition(|c| has_bvar(self.env, c, 0));
        if !outer.is_empty() {
            let mut b = self.tt();
            for c in inner {
                b = self.and(b, c.clone());
            }
            let mut r = self.ex(&b, goal);
            for c in outer {
                r = self.and(lower(self.env, c, 0), r);
            }
            return r;
        }
        // `ex x. x in S` for a set with a known member (0)
        if let [c] = cs.as_slice() {
            if let Node::App(m, ab) = c.node() {
                if is(*m, self.s.in_) && matches!(ab[0].node(), Node::BVar(0)) && !has_bvar(self.env, &ab[1], 0) {
                    let s = lower(self.env, &ab[1], 0);
                    let zero = Term::nat(crate::nat::Nat::zero());
                    let mem = self.prop(&Term::app(*m, vec![zero, s]), Pol::Other);
                    if self.is_true(&mem) {
                        return self.tt();
                    }
                }
            }
        }
        Term::app(self.s.ex, vec![body.clone()])
    }

    /// `t` (under d binders below x = BVar(d)) with x replaced by two
    /// binders a (outer), b (inner): `fst(x)` is a, `snd(x)` is b,
    /// `out_state(x)` is `fst(b)`, `out_value(x)` is `snd(b)`; None if x
    /// occurs otherwise (or not at all).
    fn proj_split(&self, t: &Term, d: u32) -> Option<Term> {
        fn go(sp: &Simp, t: &Term, d: u32, used: &mut bool) -> Option<Term> {
            let s = &sp.s;
            let (a, b) = (Term::bvar(d + 1), Term::bvar(d));
            match t.node() {
                Node::BVar(j) if *j == d => None,
                Node::BVar(j) if *j > d => Some(Term::bvar(j + 1)),
                Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => Some(t.clone()),
                Node::Var(v, xs) => Some(Term::var(*v, xs.iter().map(|x| go(sp, x, d, used)).collect::<Option<Vec<_>>>()?)),
                Node::App(f, xs) => {
                    let f = *f;
                    if xs.len() == 1 && matches!(xs[0].node(), Node::BVar(j) if *j == d) {
                        let r = if is(f, s.fst) {
                            a
                        } else if is(f, s.snd) {
                            b
                        } else if is(f, s.out_state) {
                            Term::app(s.fst?, vec![b])
                        } else if is(f, s.out_value) {
                            Term::app(s.snd?, vec![b])
                        } else {
                            return None;
                        };
                        *used = true;
                        return Some(r);
                    }
                    if is(f, s.in_) && matches!(xs[0].node(), Node::BVar(j) if *j == d) {
                        if let Node::App(u, _) = xs[1].node() {
                            if is(*u, s.univ) {
                                // (not a use: x must have a projection)
                                let us = go(sp, &xs[1], d, used)?;
                                return Some(sp.app2(s.and, Term::app(f, vec![a, us.clone()]), Term::app(f, vec![b, us])));
                            }
                        }
                        return None;
                    }
                    let bf = sp.env.binders_fn();
                    let ys = xs.iter().enumerate().map(|(k, x)| go(sp, x, d + bf(f, k), used)).collect::<Option<Vec<_>>>()?;
                    Some(Term::app(f, ys))
                }
            }
        }
        let mut used = false;
        let r = go(self, t, d, &mut used)?;
        used.then_some(r)
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
            Node::Var(_, a) => t.with_args(a.iter().map(|x| go(env, x, args, dep)).collect()),
            Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| go(env, x, args, dep + env.binders_fn()(*s, i))).collect()),
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
                    t.with_args(a)
                }
            }
            Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| go(env, x, v, value, k, dep + env.binders_fn()(*s, i))).collect()),
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
/// `t` with the bound variables i and i + 1 exchanged (two adjacent binders
/// swapped).
fn swap01(env: &Env, t: &Term, i: u32) -> Term {
    match t.node() {
        Node::BVar(j) if *j == i => Term::bvar(i + 1),
        Node::BVar(j) if *j == i + 1 => Term::bvar(i),
        Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
        Node::Var(_, a) => t.with_args(a.iter().map(|x| swap01(env, x, i)).collect()),
        Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(k, x)| swap01(env, x, i + env.binders_fn()(*s, k))).collect()),
    }
}

fn lower(env: &Env, t: &Term, i: u32) -> Term {
    match t.node() {
        Node::BVar(j) if *j > i => Term::bvar(j - 1),
        Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
        Node::Var(_, a) => t.with_args(a.iter().map(|x| lower(env, x, i)).collect()),
        Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(k, x)| lower(env, x, i + env.binders_fn()(*s, k))).collect()),
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
    /// The variables that are the pending outcome of something on the
    /// path: of a loop (`while_rel(.., r)`) or of a program kept folded
    /// (`runs(P, s, r)`).
    fn pending_outs(&self, lits: &[Term]) -> Vec<crate::term::VarId> {
        if self.no_hold.get() {
            return Vec::new();
        }
        let wr = self.env.sym_by_name.get("while_rel").copied();
        let mut out = Vec::new();
        for l in lits {
            let Node::App(f, a) = l.node() else { continue };
            let r = if Some(*f) == wr && a.len() == 5 {
                &a[4]
            } else if is(*f, self.s.runs) && a.len() == 3 {
                &a[2]
            } else {
                continue;
            };
            if let Node::Var(v, va) = r.node() {
                if va.is_empty() {
                    out.push(*v);
                }
            }
        }
        // ... and a variable tied to a pending one by an equation or an
        // implication about just the two (an unrolled loop's outcome r is
        // the rest's r1: `fst(r1) = fst(r)`, `fst(r) != 2 -> r1 = r`)
        if !out.is_empty() {
            loop {
                let n = out.len();
                for l in lits {
                    let Node::App(f, _) = l.node() else { continue };
                    if *f != self.s.eq && *f != self.s.imp {
                        continue;
                    }
                    let mut vs = Vec::new();
                    l.vars(&mut vs);
                    if let [a, b] = vs[..] {
                        if out.contains(&a) && !out.contains(&b) {
                            out.push(b);
                        } else if out.contains(&b) && !out.contains(&a) {
                            out.push(a);
                        }
                    }
                }
                if out.len() == n {
                    break;
                }
            }
        }
        out
    }

    /// `l` is a disjunction whose every alternative is about one of the
    /// pending outcomes `outs` (to be decided once that is known).
    fn held(&self, l: &Term, outs: &[crate::term::VarId]) -> bool {
        if !matches!(l.node(), Node::App(o, _) if is(*o, self.s.or)) {
            return false;
        }
        let mut ds = Vec::new();
        self.disjuncts(l, &mut ds);
        outs.iter().any(|r| ds.iter().all(|d| has_var(d, *r)))
    }

    /// `l` is a disjunction not yet split (held, or decided but not yet
    /// released); not a choice among constants, which stays a literal.
    fn unsplit(&self, l: &Term) -> bool {
        let Node::App(o, _) = l.node() else { return false };
        if !is(*o, self.s.or) {
            return false;
        }
        let mut ds = Vec::new();
        self.disjuncts(l, &mut ds);
        let choice = |d: &Term| -> Option<crate::term::VarId> {
            let Node::App(e, ab) = d.node() else { return None };
            if *e != self.s.eq {
                return None;
            }
            let konst = |c: &Term| self.is_true(c) || self.is_false(c);
            match (ab[0].node(), ab[1].node()) {
                (Node::Var(v, va), _) if va.is_empty() && konst(&ab[1]) => Some(*v),
                (_, Node::Var(v, va)) if va.is_empty() && konst(&ab[0]) => Some(*v),
                _ => None,
            }
        };
        !matches!(ds.first().and_then(choice), Some(v0) if ds.iter().all(|d| choice(d) == Some(v0)))
    }

    /// The paths of a conjunction from those of its parts (contradictory
    /// combinations dropped).
    fn combine(&self, x: Vec<Path>, y: Vec<Path>) -> Option<Vec<Path>> {
        if x.len() * y.len() > MAX_PATHS {
            return None;
        }
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
        Some(out)
    }

    /// A path's literals that are no longer held (their outcome is known,
    /// or the path has no more to do): split into paths again.
    fn release(&self, p: &Path, fresh: &mut u32, all: bool) -> Option<Vec<Path>> {
        let outs = self.pending_outs(&p.lits);
        let splittable = |l: &Term| match l.node() {
            Node::App(o, _) if is(*o, self.s.or) => (all || !self.held(l, &outs)) && self.paths(l, &mut 0).is_some_and(|ps| ps.len() > 1),
            Node::App(e, _) if *e == self.s.ex => true,
            _ => false,
        };
        let i = p.lits.iter().position(|l| splittable(l))?;
        let mut rest = p.clone();
        let l = rest.lits.remove(i);
        if all {
            self.no_hold.set(true);
        }
        let ps = self.paths(&l, fresh);
        self.no_hold.set(false);
        self.combine(vec![rest], ps?)
    }

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
                // a choice of constants for a variable (`x = false || x =
                // true`: an undefined flag) stays one literal: splitting
                // would duplicate everything after it
                let mut ds = Vec::new();
                self.disjuncts(t, &mut ds);
                let choice = |d: &Term| -> Option<crate::term::VarId> {
                    let Node::App(e, ab) = d.node() else { return None };
                    if *e != s.eq {
                        return None;
                    }
                    let konst = |c: &Term| self.is_true(c) || self.is_false(c);
                    match (ab[0].node(), ab[1].node()) {
                        (Node::Var(v, va), _) if va.is_empty() && konst(&ab[1]) => Some(*v),
                        (_, Node::Var(v, va)) if va.is_empty() && konst(&ab[0]) => Some(*v),
                        _ => None,
                    }
                };
                if let Some(v0) = ds.first().and_then(choice) {
                    if ds.iter().all(|d| choice(d) == Some(v0)) {
                        return Some(vec![Path { vars: vec![], lits: vec![t.clone()], done: vec![] }]);
                    }
                }
                let mut x = self.paths(&a[0], fresh)?;
                x.extend(self.paths(&a[1], fresh)?);
                return (x.len() <= MAX_PATHS).then_some(x);
            }
            if is(*f, s.and) {
                // a disjunction about the pending outcome of a loop or a
                // folded program among the conjuncts stays one literal: it
                // is decided once that outcome is known (splitting now would
                // repeat everything until then, once per alternative)
                let mut cs = Vec::new();
                self.conjuncts(t, &mut cs);
                let outs = self.pending_outs(&cs);
                if !outs.is_empty() && cs.iter().any(|c| self.held(c, &outs)) {
                    let mut acc = vec![Path { vars: vec![], lits: vec![], done: vec![] }];
                    for c in &cs {
                        let y = if self.held(c, &outs) { vec![Path { vars: vec![], lits: vec![c.clone()], done: vec![] }] } else { self.paths(c, fresh)? };
                        acc = self.combine(acc, y)?;
                    }
                    return Some(acc);
                }
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
        let mut rounds = 0u32;
        // the literals changed since they were simplified (only those are
        // simplified again, unless the typing changed)
        let mut dirty = vec![true; p.lits.len()];
        'again: loop {
            rounds += 1;
            let before = self.nats.borrow().clone();
            self.set_nats(&p.lits);
            if *self.nats.borrow() != before {
                dirty.iter_mut().for_each(|d| *d = true);
            }
            if rounds == 5000 && std::env::var("SIMP_DEBUG").is_ok() {
                let pr = crate::syntax::Printer::new(self.env);
                for l in &p.lits {
                    eprintln!("simp: settle loops on {}", pr.term(l).chars().take(300).collect::<String>());
                }
            }
            let mut lits = Vec::new();
            for (l, d) in p.lits.iter().zip(&dirty) {
                if !*d {
                    if !lits.contains(l) {
                        lits.push(l.clone());
                    }
                    continue;
                }
                let l = self.prop(l, Pol::Other);
                if self.is_false(&l) {
                    return None;
                }
                if !self.is_true(&l) {
                    let mut cs = Vec::new();
                    self.conjuncts(&l, &mut cs);
                    for c in cs {
                        if !lits.contains(&c) {
                            lits.push(c);
                        }
                    }
                }
            }
            p.lits = lits;
            dirty = vec![false; p.lits.len()];
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
                let (mut lits, mut ds) = (Vec::new(), Vec::new());
                for (j, l) in p.lits.iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    let changed = has_var(l, x);
                    lits.push(if changed { l.subst_var(x, &t, &bf) } else { l.clone() });
                    ds.push(changed);
                }
                p.lits = lits;
                dirty = ds;
                p.vars.retain(|y| *y != x);
                continue 'again;
            }
            // `x = a` and `x = b` for any variable x, a and b not variables:
            // the second becomes `a = b` (then split by injectivity)
            if let Some((j, e)) = self.same_var_eqs(&p.lits) {
                p.lits[j] = e;
                dirty[j] = true;
                continue 'again;
            }
            // `x = t` (x a variable, t compound, not containing x): t is x in
            // the other literals (so rules about x match)
            let bf = self.env.binders_fn();
            let side_of = |_: &Term, _: &Term| false;
            let named = p.lits.iter().enumerate().find_map(|(i, l)| {
                let Node::App(e, ab) = l.node() else { return None };
                if *e != self.s.eq {
                    return None;
                }
                let Node::Var(x, xa) = ab[0].node() else { return None };
                let compound = matches!(ab[1].node(), Node::App(_, b) if !b.is_empty());
                (xa.is_empty() && compound && !has_var(&ab[1], *x)
                    && p.lits.iter().enumerate().any(|(j, m)| j != i && !side_of(m, &ab[1]) && super::seq::abstract_term(m, &ab[1], 0, &bf) != *m))
                    .then(|| (i, ab[0].clone(), ab[1].clone()))
            });
            if let Some((i, x, t)) = named {
                for j in 0..p.lits.len() {
                    if j == i || side_of(&p.lits[j], &t) {
                        continue;
                    }
                    let a = super::seq::abstract_term(&p.lits[j], &t, 0, &bf);
                    if a != p.lits[j] {
                        p.lits[j] = inst_k(self.env, &a, &[x.clone()]);
                        dirty[j] = true;
                    }
                }
                continue 'again;
            }
            // `t = N` (t compound, N a numeral, e.g. a known register): N
            // for t in the other literals (so they compute)
            let known = p.lits.iter().enumerate().find_map(|(i, l)| {
                let Node::App(e, ab) = l.node() else { return None };
                if *e != self.s.eq {
                    return None;
                }
                [(&ab[0], &ab[1]), (&ab[1], &ab[0])].into_iter().find_map(|(t, n)| {
                    (matches!(t.node(), Node::App(_, b) if !b.is_empty())
                        && matches!(n.node(), Node::Nat(_))
                        && p.lits.iter().enumerate().any(|(j, m)| j != i && super::seq::abstract_term(m, t, 0, &bf) != *m))
                        .then(|| (i, t.clone(), n.clone()))
                })
            });
            if let Some((i, t, n)) = known {
                for j in 0..p.lits.len() {
                    if j == i {
                        continue;
                    }
                    let a = super::seq::abstract_term(&p.lits[j], &t, 0, &bf);
                    if a != p.lits[j] {
                        p.lits[j] = inst_k(self.env, &a, &[n.clone()]);
                        dirty[j] = true;
                    }
                }
                continue 'again;
            }
            // a literal and its negation
            if p.lits.iter().any(|l| matches!(l.node(), Node::App(n, a) if is(*n, self.s.not) && p.lits.contains(&a[0]))) {
                return None;
            }
            // ... or the negation of an instance of a literal `all xs. C`
            if p.lits.iter().any(|l| matches!(l.node(), Node::App(n, a) if is(*n, self.s.not) && self.instance_of_all(&p.lits, &a[0]))) {
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
        // (only constructor terms, which then split: `x = t` and `x = u` with
        // t opaque both stay -- `x = t` names t in the other literals)
        let s = &self.s;
        let ctor = |t: &Term| match t.node() {
            Node::Nat(_) | Node::Bytes(_) => true,
            Node::App(h, _) => [s.pair, s.tag, s.ok, s.exc, s.diverge, s.some, s.none].iter().any(|c| is(*h, *c)),
            _ => false,
        };
        for (k, (_, x, a)) in eqs.iter().enumerate() {
            for (j, y, b) in &eqs[k + 1..] {
                if x == y && ctor(a) && ctor(b) {
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
    /// More bindings from the goal path's equations `a = b`: with the
    /// bindings substituted, one side matched against the other once that
    /// has no unbound variables (e.g. `x = ok(y, z)` with x bound).
    fn solve_goal_eqs(&self, glits: &[Term], vars: &[crate::term::VarId], binds: &mut Vec<(crate::term::VarId, Term)>) {
        let bf = self.env.binders_fn();
        let sub = |t: &Term, binds: &[(crate::term::VarId, Term)]| {
            let mut t = t.clone();
            for (v, x) in binds {
                t = t.subst_var(*v, x, &bf);
            }
            t
        };
        let unbound = |t: &Term, binds: &[(crate::term::VarId, Term)]| vars.iter().any(|v| has_var(t, *v) && !binds.iter().any(|(w, _)| w == v));
        loop {
            let n = binds.len();
            for l in glits {
                let Node::App(e, ab) = l.node() else { continue };
                if *e != self.s.eq {
                    continue;
                }
                let (a, b) = (sub(&ab[0], binds), sub(&ab[1], binds));
                for (p, t) in [(&a, &b), (&b, &a)] {
                    if unbound(p, binds) && !unbound(t, binds) {
                        let mut bs = binds.clone();
                        if pmatch(p, &self.term(t), vars, &mut bs) {
                            *binds = bs;
                            break;
                        }
                    }
                }
            }
            // a variable seen only through projections (`fst(x) = 1`,
            // `m = fst(out_state(x))`): built as nested pairs from them
            // (the parts no equation fixes: empty)
            if binds.len() == n {
                for v in vars {
                    if binds.iter().any(|(w, _)| w == v) {
                        continue;
                    }
                    let mut cs: Vec<(Vec<bool>, Term)> = Vec::new();
                    for l in glits {
                        let Node::App(e, ab) = l.node() else { continue };
                        if *e != self.s.eq {
                            continue;
                        }
                        let (a, b) = (sub(&ab[0], binds), sub(&ab[1], binds));
                        for (p, t) in [(&a, &b), (&b, &a)] {
                            if let Some(path) = self.proj_path(p, *v) {
                                if !unbound(t, binds) {
                                    cs.push((path, self.term(t)));
                                }
                            }
                        }
                    }
                    if !cs.is_empty() {
                        if let Some(t) = self.build_from_projs(&cs) {
                            binds.push((*v, t));
                        }
                    }
                }
            }
            if binds.len() == n {
                return;
            }
        }
    }

    /// `t` is projections of the variable v: the steps from v (false: fst,
    /// true: snd), innermost first.
    fn proj_path(&self, t: &Term, v: crate::term::VarId) -> Option<Vec<bool>> {
        let s = &self.s;
        let mut steps = Vec::new();
        let mut t = t;
        loop {
            match t.node() {
                Node::Var(w, a) if *w == v && a.is_empty() => {
                    if steps.is_empty() {
                        return None;
                    }
                    steps.reverse();
                    return Some(steps);
                }
                Node::App(f, a) if a.len() == 1 => {
                    let f = *f;
                    // (outermost first; reversed at the end)
                    if is(f, s.fst) {
                        steps.push(false);
                    } else if is(f, s.snd) {
                        steps.push(true);
                    } else if is(f, s.out_state) {
                        steps.extend([false, true]);
                    } else if is(f, s.out_value) {
                        steps.extend([true, true]);
                    } else {
                        return None;
                    }
                    t = &a[0];
                }
                _ => return None,
            }
        }
    }

    /// The nested pairs with the given parts (paths from the root, false:
    /// fst, true: snd); None if two of them conflict.
    fn build_from_projs(&self, cs: &[(Vec<bool>, Term)]) -> Option<Term> {
        if let Some((_, t)) = cs.iter().find(|(p, _)| p.is_empty()) {
            return cs.iter().all(|(p, u)| !p.is_empty() || u == t).then(|| t.clone());
        }
        let part = |side: bool| -> Option<Term> {
            let sub: Vec<(Vec<bool>, Term)> = cs.iter().filter(|(p, _)| p[0] == side).map(|(p, t)| (p[1..].to_vec(), t.clone())).collect();
            if sub.is_empty() {
                Some(Term::app(self.s.empty?, vec![]))
            } else {
                self.build_from_projs(&sub)
            }
        };
        Some(Term::app(self.s.pair?, vec![part(false)?, part(true)?]))
    }

    /// The goal path's literals, with the bindings, follow from the path's.
    fn witness_ok(&self, lits: &[Term], glits: &[Term], binds: &[(crate::term::VarId, Term)], lg: &Logic) -> bool {
        let bf = self.env.binders_fn();
        let mut want = self.tt();
        for l in glits {
            let mut l = l.clone();
            for (v, t) in binds {
                l = l.subst_var(*v, t, &bf);
            }
            want = self.and(want, self.prop(&l, Pol::Other));
        }
        lg.tautology(self.env, lits, &want).is_ok() || lg.arith(self.env, lits, &want).is_ok()
    }

    fn witnessed(&self, lits: &[Term], goal: &Term, fresh: &mut u32, lg: &Logic) -> bool {
        let mut ds = Vec::new();
        self.disjuncts(goal, &mut ds);
        for d in ds {
            let Some(gps) = self.paths(&d, fresh) else { continue };
            // (the typing of the path, not of the goal's paths)
            self.set_nats(lits);
            for gp in gps {
                if gp.vars.is_empty() {
                    continue;
                }
                // the bindings from matching goal literals with path
                // literals, each goal literal matched or not (a search,
                // matches first; at most WITNESS_TRIES complete ones tried)
                const WITNESS_TRIES: usize = 64;
                let (mut tries, mut nodes) = (0, 0);
                let mut stack: Vec<(usize, Vec<(crate::term::VarId, Term)>)> = vec![(0, Vec::new())];
                while let Some((i, mut binds)) = stack.pop() {
                    nodes += 1;
                    if nodes > 64 * WITNESS_TRIES {
                        break;
                    }
                    self.solve_goal_eqs(&gp.lits, &gp.vars, &mut binds);
                    if gp.vars.iter().all(|v| binds.iter().any(|(w, _)| w == v)) {
                        tries += 1;
                        if tries > WITNESS_TRIES {
                            break;
                        }
                        if self.witness_ok(lits, &gp.lits, &binds, lg) {
                            return true;
                        }
                        continue;
                    }
                    if i == gp.lits.len() {
                        continue;
                    }
                    // (pushed last: tried first)
                    stack.push((i + 1, binds.clone()));
                    for pl in lits.iter().rev() {
                        let mut b = binds.clone();
                        if pmatch(&gp.lits[i], pl, &gp.vars, &mut b) && b.len() > binds.len() {
                            stack.push((i + 1, b));
                        }
                    }
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
        // (hypotheses about runs first: they bind the most, and a more
        // general hypothesis matched first may bind wrongly)
        hyps.sort_by_key(|h| !matches!(h.node(), Node::App(r, _) if is(*r, self.s.runs)));
        // (an equation needs no hypotheses: a rewrite rule)
        let eq = matches!(t.node(), Node::App(e, _) if *e == self.s.eq);
        (!hyps.is_empty() || (eq && !vs.is_empty())).then_some((vs, hyps, t))
    }

    /// Typing: `t in int`, `t in omega` or `t in bits(k)` from the literals
    /// and the definitions of the arithmetic (see `int_term`, `nat_term`,
    /// `bits_term`).
    fn typed(&self, lits: &[Term], g: &Term) -> bool {
        let Node::App(i, ab) = g.node() else { return false };
        if !is(*i, self.s.in_) {
            return false;
        }
        self.set_nats(lits);
        match ab[1].node() {
            Node::App(o, x) if x.is_empty() && is(*o, self.s.omega) => self.nat_term(&ab[0]),
            Node::App(o, x) if x.is_empty() && self.env.syms[*o as usize].name == "int" => self.int_term(&ab[0]),
            Node::App(b, x) if self.env.syms[*b as usize].name == "bits" && x.len() == 1 => match x[0].node() {
                Node::Nat(k) => k.to_u64().is_some_and(|k| self.bits_term(&ab[0], k)),
                _ => false,
            },
            _ => false,
        }
    }

    /// `t` is an instance of a literal `all xs. C` (C not an implication).
    fn instance_of_all(&self, lits: &[Term], t: &Term) -> bool {
        let head = |x: &Term| match x.node() {
            Node::App(g, _) => Some(*g),
            _ => None,
        };
        let th = head(t);
        for l in lits {
            if !matches!(l.node(), Node::App(q, _) if *q == self.s.all) {
                continue;
            }
            // (cheaply first: a body under the binders with t's head)
            let mut b = l;
            let mut fits = false;
            while let Node::App(q, a) = b.node() {
                if *q != self.s.all {
                    break;
                }
                b = &a[0];
                fits |= head(b) == th;
            }
            if !fits || head(b) == Some(self.s.imp) && th != Some(self.s.imp) && th != Some(self.s.all) {
                continue;
            }
            // pattern variables above those of t and l
            let mut fresh = max_var(t).max(max_var(l)) + 1;
            let mut vs = Vec::new();
            let mut b = l.clone();
            while let Node::App(q, a) = b.node() {
                if *q != self.s.all {
                    break;
                }
                vs.push(fresh);
                fresh += 1;
                b = inst_k(self.env, &a[0], &[Term::var(fresh - 1, vec![])]);
                // (t may itself be universal: matched at each depth)
                if !matches!(b.node(), Node::App(i, _) if *i == self.s.imp) && pmatch(&b, t, &vs, &mut Vec::new()) {
                    return true;
                }
            }
        }
        false
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
            for (mut binds, mut open) in insts {
                // an open hypothesis may match once instantiated and
                // simplified (`app(m, "vm")` with m an update of rip)
                if !vs.iter().all(|v| binds.iter().any(|(w, _)| w == v)) {
                    let mut k = 0;
                    while k < open.len() {
                        let mut h = hyps[open[k]].clone();
                        for (v, x) in &binds {
                            h = h.subst_var(*v, x, &bf);
                        }
                        let h = self.prop(&h, Pol::Other);
                        let hit = p.lits.iter().find_map(|l| {
                            let mut b = binds.clone();
                            pmatch(&h, l, &vs, &mut b).then_some(b)
                        });
                        match hit {
                            Some(b) => {
                                binds = b;
                                open.remove(k);
                            }
                            None => k += 1,
                        }
                    }
                }
                if vs.iter().all(|v| binds.iter().any(|(w, _)| w == v)) {
                    all_insts.push((binds, open));
                } else if let Some(lhs) = &lhs {
                    for u in &subs {
                        let mut b = binds.clone();
                        if pmatch(lhs, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                            all_insts.push((b, open.clone()));
                        }
                    }
                } else {
                    // (otherwise from the goal: a conjunct the conclusion matches)
                    let mut gs = Vec::new();
                    self.conjuncts(goal, &mut gs);
                    for u in &gs {
                        let mut b = binds.clone();
                        if pmatch(&concl, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                            all_insts.push((b, open.clone()));
                        }
                    }
                }
                if all_insts.len() >= MAX_INSTANCES {
                    break;
                }
            }
            let outs = self.pending_outs(&p.lits);
            for (binds, open) in all_insts {
                let inst = |t: &Term| {
                    let mut t = t.clone();
                    for (v, x) in &binds {
                        t = t.subst_var(*v, x, &bf);
                    }
                    self.prop(&t, Pol::Other)
                };
                let shown = |h: &Term| {
                    // the path's known values (`t = N`) in h first
                    let mut h = h.clone();
                    for l in &p.lits {
                        if let Node::App(e, ab) = l.node() {
                            if *e == self.s.eq && matches!(ab[1].node(), Node::Nat(_)) && matches!(ab[0].node(), Node::App(_, x) if !x.is_empty()) {
                                let body = super::seq::abstract_term(&h, &ab[0], 0, &bf);
                                if body != h {
                                    h = self.prop(&inst_k(self.env, &body, &[ab[1].clone()]), Pol::Other);
                                }
                            }
                        }
                    }
                    let h = &h;
                    if self.is_false(h) || self.is_true(h) {
                        return self.is_true(h);
                    }
                    // (a program's run holds only as a literal)
                    if matches!(h.node(), Node::App(r, _) if is(*r, self.s.runs)) {
                        return p.lits.contains(h);
                    }
                    // (about a pending outcome: not shown before it is known,
                    // unless it is a literal)
                    if !outs.is_empty() {
                        let mut hv = Vec::new();
                        h.vars(&mut hv);
                        if hv.iter().any(|v| outs.contains(v)) {
                            return p.lits.contains(h);
                        }
                    }
                    let t = std::time::Instant::now();
                    let lap = |i: usize, t: &mut std::time::Instant| {
                        self.prof.borrow_mut()[i] += t.elapsed();
                        *t = std::time::Instant::now();
                    };
                    let mut t = t;
                    if self.typed(&p.lits, h) || self.instance_of_all(&p.lits, h) {
                        lap(1, &mut t);
                        return true;
                    }
                    lap(1, &mut t);
                    if lg.tautology(self.env, &p.lits, h).is_ok() {
                        lap(2, &mut t);
                        return true;
                    }
                    lap(2, &mut t);
                    // (the literals about h first: a much smaller problem)
                    let near = relevant(&p.lits, h);
                    let r = lg.arith(self.env, &near, h).is_ok() || (near.len() < p.lits.len() && lg.arith(self.env, &p.lits, h).is_ok());
                    if !r && std::env::var("SIMP_DEBUG").is_ok() {
                        eprintln!("simp: not shown {}", crate::syntax::Printer::new(self.env).term(h).chars().take(200).collect::<String>());
                    }
                    lap(3, &mut t);
                    r
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
        // (the path's literals are in normal form already: only the new
        // fact is split, each of its paths added to them)
        let ps = self.paths(&lg.simp_fact(self.env, &c), fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
        Ok(ps
            .into_iter()
            .map(|mut q| {
                let mut lits = p.lits.clone();
                lits.append(&mut q.lits);
                q.lits = lits;
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
                let ps = self.paths(&lg.simp_fact(self.env, &out), fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
                Ok(Some(
                    ps.into_iter()
                        .map(|mut q| {
                            let mut lits = others.clone();
                            lits.append(&mut q.lits);
                            q.lits = lits;
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
        let ((l1v, l1), (rv, r1)) = (var(), var());
        let stop = self.and(self.not(cond(l0)), Term::app(self.s.eq, vec![r.clone(), ok(l0)]));
        let leave = self.and(self.and(cond(l0), body(l0, r)), self.not(Term::app(is_ok, vec![r.clone()])));
        // the loop runs on from l1 with an outcome r1 of the same kind: r
        // itself, or both divergences (with other traces). As one path:
        // `fst(r1) = fst(r) && (!(fst(r) = 2) -> r1 = r)` (outcomes are
        // tagged 0, 1, 2), so the rest of the loop is followed once.
        let fst = |x: &Term| Term::app(self.s.fst.expect("fst"), vec![x.clone()]);
        let nat = |n: u64| Term::nat(crate::nat::Nat::from_u64(n));
        let again = Term::app(wr, vec![l1.clone(), a[1].clone(), a[2].clone(), a[3].clone(), r1.clone()]);
        let kind = Term::app(self.s.eq, vec![fst(&r1), fst(r)]);
        let same = Term::app(self.s.imp, vec![self.not(Term::app(self.s.eq, vec![fst(r), nat(2)])), Term::app(self.s.eq, vec![r1.clone(), r.clone()])]);
        let again = self.and(self.and(again, kind), same);
        let again = Term::app(self.s.ex, vec![abstract_var(env, &again, rv, 0)]);
        let next = self.and(body(l0, &ok(&l1)), again);
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
        // (the facts about the loop's outcome r play no part in its
        // iterations: left out of these proofs)
        let others: Vec<Term> = match r.node() {
            Node::Var(rv, ra) if ra.is_empty() => others.iter().filter(|l| !has_var(l, *rv)).cloned().collect(),
            _ => others.to_vec(),
        };
        let others = &others[..];
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
            let lt = Term::app(sym("int_lt")?, vec![mv(&y), mv(&x)]);
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

    /// `t` simplified as a term (the simplifier's equations), for tools.
    pub fn simp_term(&self, env: &Env, t: &Term) -> Term {
        Simp::new(env, self).term(t)
    }

    /// The settled paths of the premises (programs in `keep` folded): each
    /// its existential variables (fresh, not in `env`) and literals. For
    /// tools that propose statements (e.g. an instruction's outcome); it
    /// proves nothing.
    pub fn simp_paths(&self, env: &Env, premises: &[Term], keep: &[SymId]) -> crate::env::KResult<Vec<(Vec<crate::term::VarId>, Vec<Term>)>> {
        let mut fresh = env.vars.len() as u32 + 2_000_000;
        for t in premises {
            fresh = fresh.max(max_var(t) + 1);
        }
        *self.simp_keep.borrow_mut() = keep.to_vec();
        let sp = Simp::new(env, self);
        let mut prem = sp.tt();
        for p in premises {
            prem = sp.and(prem, self.simp_fact(env, p));
        }
        self.simp_keep.borrow_mut().clear();
        let work = sp.paths(&prem, &mut fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
        Ok(work.into_iter().filter_map(|p| sp.settle(p)).map(|p| (p.vars, p.lits)).collect())
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
        let t0 = std::time::Instant::now();
        let mut prem = sp.tt();
        for p in premises {
            prem = sp.and(prem, self.simp_fact(env, p));
        }
        let t1 = std::time::Instant::now();
        let g = self.simp_eqv(env, goal);
        let mut work = sp.paths(&prem, fresh).ok_or_else(|| crate::env::KernelError("simp: too many paths".into()))?;
        if std::env::var("SIMP_TIME").is_ok() {
            eprintln!("simp time [facts, goal+paths]: {:?}, {:?}", t1 - t0, t1.elapsed());
        }
        let (mut steps, mut left, mut report) = (0, 0, String::new());
        // timings (SIMP_TIME=1): settle, goal, taut/arith, witnessed, near, chain, loop; paths
        let timing = std::env::var("SIMP_TIME").is_ok();
        let mut tm = [std::time::Duration::ZERO; 7];
        let mut npaths = 0usize;
        let mut clock = std::time::Instant::now();
        let mut lap = |i: usize, tm: &mut [std::time::Duration; 7]| {
            let now = std::time::Instant::now();
            tm[i] += now - clock;
            clock = now;
        };
        let report_time = |tm: &[std::time::Duration; 7], n: usize| {
            if timing {
                eprintln!("simp time [settle, goal, taut/arith, witnessed, near, chain, loop]: {:?}, {} paths", tm, n);
                eprintln!("simp chain time [-, typed/instance, taut, arith]: {:?}", sp.prof.borrow());
            }
        };
        while let Some(p) = work.pop() {
            npaths += 1;
            if timing && npaths % 50 == 0 {
                eprintln!("simp: {} paths, {} queued, {} literals; {:?}", npaths, work.len(), p.lits.len(), tm);
            }
            lap(6, &mut tm);
            let Some(p) = sp.settle(p) else {
                lap(0, &mut tm);
                continue;
            };
            lap(0, &mut tm);
            // the path's equations used in the goal: `x = t` or `t = x` (x a
            // variable) substituted, then `a = b` rewritten left to right
            let bf = env.binders_fn();
            // (the goal with the path's typing)
            let mut g = sp.eqv(&g);
            let eqs_owned: Vec<(Term, Term)> = p
                .lits
                .iter()
                .filter_map(|l| match l.node() {
                    Node::App(e, ab) if *e == sp.s.eq => Some((ab[0].clone(), ab[1].clone())),
                    _ => None,
                })
                .collect();
            let eqs: Vec<(&Term, &Term)> = eqs_owned.iter().map(|(a, b)| (a, b)).collect();
            let var = |t: &Term| match t.node() {
                Node::Var(x, xa) if xa.is_empty() => Some(*x),
                _ => None,
            };
            let mut substs: Vec<(crate::term::VarId, Term)> = Vec::new();
            // (t built from constructors: x := t, so the goal computes; t
            // opaque: t becomes x in the goal, as in the literals)
            let ctor = |t: &Term| match t.node() {
                Node::Nat(_) | Node::Bytes(_) => true,
                Node::App(h, _) => [sp.s.pair, sp.s.tag, sp.s.ok, sp.s.exc, sp.s.diverge, sp.s.fn_update, sp.s.some, sp.s.none].iter().any(|c| is(*h, *c)),
                _ => false,
            };
            for &(a, b) in &eqs {
                for (v, t) in [(a, b), (b, a)] {
                    if let Some(x) = var(v) {
                        if ctor(t) || var(t).is_some() {
                            if has_var(t, x) {
                                continue;
                            }
                            if has_var(&g, x) {
                                g = sp.eqv(&g.subst_var(x, t, &bf));
                                substs.push((x, t.clone()));
                                break;
                            }
                        } else {
                            let body = super::seq::abstract_term(&g, t, 0, &bf);
                            if body != g {
                                g = sp.eqv(&inst_k(env, &body, &[v.clone()]));
                                break;
                            }
                        }
                    }
                }
            }
            // the same substitutions in the literals (they may name t by x)
            let p = if substs.is_empty() {
                p
            } else {
                let mut q = p.clone();
                q.lits = q
                    .lits
                    .iter()
                    .map(|l| {
                        let mut l = l.clone();
                        for (x, t) in &substs {
                            if has_var(&l, *x) && !matches!(l.node(), Node::App(e, ab) if *e == sp.s.eq && matches!(ab[0].node(), Node::Var(y, _) if y == x)) {
                                l = sp.prop(&l.subst_var(*x, t, &bf), Pol::Other);
                            }
                        }
                        l
                    })
                    .collect();
                q
            };
            for &(a, b) in &eqs {
                if var(a).is_none() && var(b).is_none() {
                    let body = super::seq::abstract_term(&g, a, 0, &bf);
                    if body != g {
                        g = sp.eqv(&inst_k(env, &body, &[b.clone()]));
                    }
                }
            }
            // the path's (non-equation) literals in the goal: true there (a
            // negated one: its atom false), the goal simplified again
            let mut known = false;
            for l in &p.lits {
                let (atom, val) = match l.node() {
                    Node::App(n, a) if is(*n, sp.s.not) => (&a[0], sp.ff()),
                    Node::App(e, _) if *e == sp.s.eq || *e == sp.s.all => continue,
                    _ => (l, sp.tt()),
                };
                if matches!(atom.node(), Node::App(o, _) if is(*o, sp.s.or) || is(*o, sp.s.and) || *o == sp.s.imp) {
                    continue;
                }
                let body = super::seq::abstract_term(&g, atom, 0, &bf);
                if body != g {
                    g = inst_k(env, &body, &[val]);
                    known = true;
                }
            }
            if known {
                g = self.simp_eqv(env, &g);
            }
            lap(1, &mut tm);
            if sp.is_true(&g) {
                continue;
            }
            // the checks below without the held disjunctions (undecided,
            // they cannot close the path; fewer premises is sound); the path
            // goes on with them (`full`)
            let full = p;
            let p = if !full.lits.iter().any(|l| sp.unsplit(l)) {
                full.clone()
            } else {
                Path { vars: full.vars.clone(), lits: full.lits.iter().filter(|l| !sp.unsplit(l)).cloned().collect(), done: full.done.clone() }
            };
            // a goal about what such a disjunction decides (e.g. the run's
            // outcome o) waits until it is decided: the checks would fail
            let waits = p.lits.len() < full.lits.len() && {
                let mut gv = Vec::new();
                g.vars(&mut gv);
                full.lits.iter().any(|l| {
                    let mut lv = Vec::new();
                    l.vars(&mut lv);
                    sp.unsplit(l) && lv.iter().any(|v| gv.contains(v))
                })
            };
            let closes = |g: &Term| !waits && (sp.typed(&p.lits, g) || self.tautology(env, &p.lits, g).is_ok() || self.arith(env, &p.lits, g).is_ok() || sp.instance_of_all(&p.lits, g));
            // a conjunction: each conjunct (arithmetic from the literals about it)
            let closes_part = |c: &Term| closes(c) || (!waits && self.arith(env, &relevant(&p.lits, c), c).is_ok());
            let mut gs = Vec::new();
            sp.conjuncts(&g, &mut gs);
            if closes(&g) || (gs.len() > 1 && gs.iter().all(|c| closes_part(c))) {
                lap(2, &mut tm);
                continue;
            }
            lap(2, &mut tm);
            if !waits && sp.witnessed(&p.lits, &g, fresh, self) {
                lap(3, &mut tm);
                continue;
            }
            // (each conjunct by itself, its existentials witnessed)
            if !waits && gs.len() > 1 && gs.iter().all(|c| closes_part(c) || sp.witnessed(&p.lits, c, fresh, self)) {
                lap(3, &mut tm);
                continue;
            }
            lap(3, &mut tm);
            // long paths: arithmetic from the literals about the goal's variables
            let near = relevant(&p.lits, &g);
            if !waits && near.len() < p.lits.len() && (self.tautology(env, &near, &g).is_ok() || self.arith(env, &near, &g).is_ok()) {
                lap(4, &mut tm);
                continue;
            }
            lap(4, &mut tm);
            // a rule among the facts (`all xs. A -> .. -> C`) whose
            // hypotheses the path has: continue with its conclusion
            let ch = sp.chain(self, &p, &g, fresh);
            lap(5, &mut tm);
            if let Some(c) = ch {
                if std::env::var("SIMP_DEBUG").is_ok() {
                    eprintln!("simp: new fact {}", crate::syntax::Printer::new(env).term(&c).chars().take(300).collect::<String>());
                }
                steps += 1;
                if steps > MAX_PATHS {
                    return Err(crate::env::KernelError("simp: too many paths".into()));
                }
                work.extend(sp.extend(self, &full, c, fresh)?);
                continue;
            }
            // a loop on the path, with an invariant: continue with its outcome
            let mut why = String::new();
            if std::env::var("SIMP_DEBUG").is_ok() && p.lits.len() > 150 {
                let pr = crate::syntax::Printer::new(env);
                for l in &p.lits {
                    eprintln!("simp: literal {}", pr.term(l).chars().take(400).collect::<String>());
                }
                return Err(crate::env::KernelError("simp: stopped (SIMP_DEBUG, long path)".into()));
            }
            if let Some(ps) = sp.loop_step(self, &full, hints, fresh, &mut why)? {
                steps += 1;
                if steps > MAX_PATHS {
                    return Err(crate::env::KernelError("simp: too many paths".into()));
                }
                work.extend(ps);
                continue;
            }
            // nothing else to do: a held disjunction whose outcome is known
            // now is split (late: a rule may still refute the path), else
            // those still held (as without holding), before the path counts
            // as left
            if let Some(ps) = sp.release(&full, fresh, false).or_else(|| sp.release(&full, fresh, true)) {
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
        lap(6, &mut tm);
        report_time(&tm, npaths);
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

    /// A proposition equivalent to the goal `t`.
    pub fn simp_eqv(&self, env: &Env, t: &Term) -> Term {
        let sp = Simp::new(env, self);
        let mut t = t.clone();
        for _ in 0..8 {
            let u = sp.prop(&t, Pol::Goal);
            if u == t {
                break;
            }
            t = u;
        }
        t
    }
}
