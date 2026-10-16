//! A simplifier for elaborated programs and propositions: symbolic
//! execution of `runs(P, s, o)`.
//!
//! Trusted extension. It rewrites with a fixed set of rules, each a theorem
//! of the prelude (or of the pinned definitions of `x86_64_linux.store_le`,
//! `x86_64_linux.le`, `x86.apart`): the symbols are read by name only as
//! `Env::ksym` / `Env::kname` resolve them -- the canonical prelude's, or a
//! definition with its pinned body (`ext::pinned`):
//!
//! Equations (used anywhere):
//! * `letin(a, x. f(x)) = f(a)` (definition) -- lazily: a small value
//!   (`LET_SMALL` nodes at most, as a tree) is copied in; else f is
//!   simplified with x a local constant bound to a, looked through where
//!   it helps -- a node with x as an argument, or a proposition's atom
//!   mentioning x, is tried with a in its place, kept so if a rule fires
//!   there --, then the let is kept if x is still used twice or more (a
//!   large value used many times is not copied: the term stays as small
//!   as it was), substituted if once, dropped if not; a goal that attempt
//!   does not prove, again with every let reduced;
//! * `fst(pair(a, b)) = a`, `snd(pair(a, b)) = b` (pair injectivity), and
//!   for the outcome constructors `ok(s, v) = pair(0, pair(s, v))`,
//!   `exc(s, e) = pair(1, pair(s, e))`, `diverge(t) = pair(2, t)`: their
//!   `fst`, `snd`, `out_state`, `out_value`;
//! * `fn_modify(f, k, y. g(y)) = letin(f, F. fn_update(F, k, g(app(F, k))))`
//!   (definitions: f bound once, a let as above -- not copied);
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
//!   without k, updates at other keys of such, or a term whose `dom(x) =
//!   D` is a literal of the path with k not in D: `dom_lacks`) -- by
//!   `app_ext`, the pairs at k being the same (`app_union2_lacks`);
//!   `fn_update(union2(a, b), k, v)` is `union2(fn_update(a, k, v), b)`
//!   when b lacks k, and symmetrically (`fn_update_union_l`/`_r`: a state
//!   with a ghost part updated in its part); `app(empty, k)` is `empty`;
//!   `with_ghost(ok(s, v), h)` is `ok(union2(s, h), v)`, likewise `exc`,
//!   and a divergence is itself (`with_ghost_ok`, `_exc`, `_diverge`);
//!   `ghost_part(fn_update(f, k, v), d)` is `ghost_part(f, d)` and
//!   `restrict(fn_update(f, k, v), d)` is `fn_update(restrict(f, d), k, v)`
//!   if k in d; both are `empty` of `empty`; `union2(a, empty)` and
//!   `union2(empty, a)` are a (`union2_empty`; `rec_merge` likewise) -- set
//!   equalities, by the definitions.
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
//!   are `empty` when undefined); `ite(c, a, b)` if a and b are;
//!   `restrict(f, d)` and `ghost_part(f, d)` if f is (subsets:
//!   `restrict_univ`, `ghost_part_univ` in core/records.core); updates of
//!   the same base b at different literal keys are equal if they agree at
//!   every key, b is a function and the keys updated on one side only are
//!   in dom(b) (`fn_update_fun`, `fn_update_dom`, `rec_ext`);
//!   updates x of a base b at literal keys are in a record type T
//!   (`set_select(powerset(cart(K, univ(u))), x. is_fun(x) && dom(x) = K
//!   && app(x, "k") in T_k ..)`, or a constant defined as one) if b is (or
//!   b is `empty` and every key is updated), the keys are T's, each value
//!   is of its field's type, and the outermost record w that x is a field
//!   of is in univ(u) (its fields then are: `app_univ`) -- by
//!   `rec_type_intro`, `fn_update_fd`, `dom_update`; and in `fn_space(A,
//!   B)` if b is, the keys are in A and the values in B.
//! * a proposition by its form (an equation, implication, existential,
//!   `false`, or a definition whose body is one) is in `bool` (`eq_prop`,
//!   `imp_prop`, `ex_prop`, `false_is_prop`);
//! * a field `app(r, k)` is of the type of the field k in a record type the
//!   path gives r; the premises' `t in univ(u)` (in the goal: also the
//!   path's) count before the goal's strengthening takes t apart.
//! * `app(fn_build(d, x. v), a)` is v(a) when a in d is known (a premise or
//!   literal, or d = bits(n) and a an n-bit word: `app_fn_build`);
//!   `int_sum(a, b, i. f)` for numerals a <= b (at most 64 apart) is
//!   f(a) + .. + f(b - 1) (its definition, `nat_rec`'s equations); x / 1 =
//!   x * 1 = x for an integer x.
//! * with `unroll`, a loop of the goal whose condition is decided at a known
//!   state is run an iteration at a time: it stops (`while_stop`), the body
//!   leaves (`while_leave`) or goes on (`while_step`) -- theorems of
//!   core/loop.core the step relies on, like `while_unroll` for loops of
//!   facts (the step is refused unless they are loaded).
//! * in facts, `ex x. P(fst(x), snd(x))` is split into the projections when
//!   that decides it (a choice of several values that exists).
//! * a comparison of a literal k with a natural x, or with a word x of a
//!   width n (0 <= x < 2^n), is decided when k lies outside that range
//!   (`int_le(2^63, x)` is false for a 32-bit x); `int_mod(x, k)` of an
//!   n-bit x with 2^n <= k is x.
//! * a goal `all ys. H1 -> .. -> C` holds when C (its variables fixed) is an
//!   instance of a literal `all xs. D` (`all i. i in omega -> P(f(i))` from
//!   `all a. P(a)`).
//! * the path's literal bounds of an integer term (`d <= 31`, `!(k < d)`)
//!   decide comparisons of it with literals -- not the literal they come
//!   from (`int_lt(d, 2^31)` in an `ite` condition).
//! * a goal computing `ite(c, a, b)` whose condition no literal decides is
//!   split on c (or on an undecided atom of a compound c), as `c || !c`.
//! * a premise `all xs. f(xs) = rhs` (f defined, the xs in order, f not in
//!   rhs) unfolds f everywhere, as a definition would (`x86.cond_eval`: a
//!   jump's condition computed from the flags); a bit of a numeral as a
//!   value is its proposition; `p = true` / `p = false` of a proposition p
//!   is p / !p.
//! * a proposition (eq, in, imp, ex, and what unfolds to them) is in
//!   every universe (the prelude's `prop_univ`: in univ(0)).
//! * arith, when the literals alone do not close a path, also gets the
//!   widths simp knows of opaque words (`le(b, a, 1) in bits(8)`).
//! * witnesses: a variable only typed `x in bits(n)` / `x in omega` (an
//!   uninitialized local) takes 0 when nothing else binds it; an equation
//!   binds a variable only through injective constructors; a goal too large
//!   to enumerate is first reduced with the outcomes of the runs the path
//!   knows (`runs(P, s, o)`: the goal's `ex x. runs(P, s, x) && ..` takes
//!   o) and its literals as decided.
//! * separated memory: a path literal `x86.apart(A, N, B, M)` (the regions
//!   [A, A+N) and [B, B+M) disjoint; N, M numerals) lets a read of one
//!   region skip stores to the other (ranges placed in the regions by their
//!   known distance from A, B); and puts stores in an order: a store to A's
//!   region moves out past a store to B's (disjoint stores commute), and a
//!   store of the same n bytes at the same address replaces an earlier one.
//! * words (bit fields): `x mod 2^n` is `bits_add(n, x, 0)`, and that is x
//!   for an n-bit x; mod 2^k of mod 2^n (k <= n) is mod 2^k; `and` with a
//!   low mask 2^k - 1 is mod 2^k, of x with itself is x; a 16-bit write of
//!   a 16-bit value is the value; sign extension of a small value is the
//!   value; x * 1 is x; x + x is 2 * x; widths of products with literals,
//!   of sums, of `and` with a mask, of `bits_set_slice`; an address of the
//!   domain's width is in its domain (`app(f, a)` of f in fn_space);
//!   signed values: `sint(n, x)` of x below 2^(n-1) is x, of a sign
//!   extension `bits_sext(m, n, y)` (m <= n) is `sint(m, y)`; an n-bit
//!   operation (add, sub, `bits_of_int`) reads an operand `sint(m, y)`
//!   (m >= n) as y, and `bits_of_int(n, sint(m, y))` (m < n) is
//!   `bits_sext(m, n, y)`.
//! * a choice of constants (`t = false || t = true`) stays one literal (not
//!   a case split) also for a projection t of a variable (`fst(snd(u))`:
//!   one of several undefined flags).
//!
//! Rules: a path literal `all xs. A1 -> .. -> An -> C` whose hypotheses
//! match literals of the path (or follow from them by taut/arith), with
//! every x bound, adds its instance of C to the path (∀- and →-elimination);
//! for an equation C (possibly n = 0), xs may also be bound by matching its
//! left side against terms of the path or goal, and for a run C by matching
//! C against the goal (`all o. o in univ(1) -> runs(P, s, o)`: an outcome
//! no literal has), its hypotheses then shown -- with the path's
//! definitions of variables (`x = t`) put in, a hypothesis `x in omega`
//! also met by a literal `x in bits(k)`. C is added unless known (a literal,
//! or by taut from the literals other than the rule: a disjunction C is
//! then split into its cases). A goal `all xs. A1 -> .. -> C` that simp
//! does not show as it is, is tried once more opened: the xs fresh, the
//! A's premises, C the goal (introduction). The goal is rewritten with
//! the path's equations `x = t` / `t = x` (x a variable) and `a = b` (left
//! to right), again while it changes (simplified, it may show a rewritten
//! term anew), with the goal-side rule for equations of update chains.
//! (`SIMP_GOAL=1` prints each path's equations and rewritten goal.)
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
    with_ghost: Option<SymId>,
    union2: Option<SymId>,
    app: Option<SymId>,
    fn_update: Option<SymId>,
    fn_modify: Option<SymId>,
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

/// A record type (`Simp::rec_type`): its universe, keys, field types.
struct RecType {
    u: Term,
    keys: Term,
    fields: Vec<(Term, Term)>,
}

/// What a path knows a term to be: an integer, a natural, an n-bit word,
/// a member of `univ(u)`.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Ty {
    Int,
    Nat,
    Bits(u64),
    Univ(u64),
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
    /// lets kept / reduced by name (`Logic::simp_lets`)
    lets: (Vec<String>, Vec<String>),
    /// symbols unfolded by premises `all xs. f(xs) = rhs` (`Logic::simp_rewrites`)
    rewrites: Vec<(SymId, usize, Term)>,
    /// run loops in the goal (`Logic::simp_goal_loops`)
    goal_loops: bool,
    /// library lemmas used (for `Logic::simp_used`)
    used: std::cell::RefCell<Vec<String>>,
    /// terms the current path knows to be natural numbers (its literals
    /// `t in omega`, `t in bits(k)`)
    nats: std::cell::RefCell<Vec<(Term, Ty)>>,
    /// in the goal's first simplification: the premises' literals `t in S`
    /// (the typing rule leaves those as they are)
    known_mems: std::cell::RefCell<Vec<Term>>,
    /// the path's literals `dom(x) = D`: the fields a record x has (a state
    /// type's, as its membership gives them) -- for `lacks`
    known_doms: std::cell::RefCell<Vec<(Term, Term)>>,
    /// literal bounds the path's literals give integers: (x, upper, k, the
    /// literal's atom) for x <= k (upper) or x >= k
    bounds: std::cell::RefCell<Vec<(Term, bool, SInt, Term)>>,
    /// the path's literals `runs(P, s, o)`: a goal's `ex x. runs(P, s, x)
    /// && ..` takes x := o
    runs_facts: std::cell::RefCell<Vec<Term>>,
    /// the path's literals `x86.apart(A, N, B, M)` (N, M numerals): the
    /// regions [A, A+N) and [B, B+M) are disjoint
    aparts: std::cell::RefCell<Vec<(Term, u128, Term, u128)>>,
    /// (only for a goal too large to search a witness in otherwise)
    eager_runs: std::cell::Cell<bool>,
    /// the lets being simplified: their local constants and values (a
    /// constant looked through to its value where a rule needs it)
    let_env: std::cell::RefCell<Vec<(crate::term::VarId, Term)>>,
    let_fresh: std::cell::Cell<u32>,
    /// the path's literals (with `eager_runs`: a goal's atom that is one
    /// holds, its negation fails)
    lit_facts: std::cell::RefCell<Vec<Term>>,
    /// the witness search's goal is the eager step's
    eager_tried: std::cell::Cell<bool>,
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
        let g = |n: &str| env.ksym(n);
        let unfold = ["bind_rel", "any_rel", "is_ok"].iter().filter_map(|n| g(n)).collect();
        let arith = ARITH.iter().filter_map(|n| g(n).map(|s| (s, *n))).collect();
        Simp {
            env,
            arith,
            keep: lg.simp_keep.borrow().clone(),
            lets: lg.simp_lets.borrow().clone(),
            rewrites: lg.simp_rewrites.borrow().clone(),
            goal_loops: lg.simp_goal_loops.get(),
            used: Default::default(),
            no_hold: Default::default(),
            memo: Default::default(),
            let_env: Default::default(),
            let_fresh: std::cell::Cell::new(LET_FRESH0),
            nats: std::cell::RefCell::new(Vec::new()),
            known_mems: std::cell::RefCell::new(Vec::new()),
            known_doms: std::cell::RefCell::new(Vec::new()),
            bounds: std::cell::RefCell::new(Vec::new()),
            runs_facts: std::cell::RefCell::new(Vec::new()),
            aparts: std::cell::RefCell::new(Vec::new()),
            eager_runs: Default::default(),
            lit_facts: std::cell::RefCell::new(Vec::new()),
            eager_tried: Default::default(),
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
                with_ghost: g("with_ghost"),
                union2: g("union2"),
                app: g("app"),
                fn_update: g("fn_update"),
                fn_modify: g("fn_modify"),
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
        let name = |g: SymId| self.env.kname(g);
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
                    let name = sp.env.kname(*g);
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
                        Node::App(o, x) if x.is_empty() && self.env.ksym("int") == Some(*o) => out.push((ab[0].clone(), Ty::Int)),
                        Node::App(b, x) if self.env.ksym("bits") == Some(*b) && x.len() == 1 => {
                            if let Node::Nat(k) = x[0].node() {
                                if let Some(k) = k.to_u64() {
                                    out.push((ab[0].clone(), Ty::Bits(k)));
                                }
                            }
                        }
                        Node::App(b, x) if is(*b, s.univ) && x.len() == 1 => {
                            if let Node::Nat(k) = x[0].node() {
                                if let Some(k) = k.to_u64() {
                                    out.push((ab[0].clone(), Ty::Univ(k)));
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        // the memberships (a function's argument in its domain: `term` applies
        // a built function to it)
        let mems: Vec<Term> = lits.iter().filter(|l| matches!(l.node(), Node::App(i, _) if is(*i, s.in_))).cloned().collect();
        // the records' known fields: `dom(x) = D`
        let dom_s = self.env.ksym("dom");
        let doms: Vec<(Term, Term)> = lits
            .iter()
            .filter_map(|l| match l.node() {
                Node::App(e, ab) if *e == s.eq && ab.len() == 2 => match ab[0].node() {
                    Node::App(d, x) if dom_s == Some(*d) && x.len() == 1 => Some((x[0].clone(), ab[1].clone())),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        // (`term` depends on the typing: its memo only for this one)
        if *self.nats.borrow() != out || *self.known_mems.borrow() != mems || *self.known_doms.borrow() != doms {
            self.memo.borrow_mut().clear();
            *self.nats.borrow_mut() = out;
            *self.known_mems.borrow_mut() = mems;
            *self.known_doms.borrow_mut() = doms;
        }
        // literal bounds of integers: `x <= k`, `k < x`, `!(x < k)`, ..
        let bounds = self.literal_bounds(lits);
        if *self.bounds.borrow() != bounds {
            self.memo.borrow_mut().clear();
            *self.bounds.borrow_mut() = bounds;
        }
        let rf: Vec<Term> = lits.iter().filter(|l| matches!(l.node(), Node::App(r, a) if is(*r, self.s.runs) && a.len() == 3)).cloned().collect();
        if *self.runs_facts.borrow() != rf {
            self.memo.borrow_mut().clear();
            *self.runs_facts.borrow_mut() = rf;
        }
        let ap: Vec<(Term, u128, Term, u128)> = match self.env.ksym("x86.apart").as_ref() {
            Some(apart) => lits
                .iter()
                .filter_map(|l| match l.node() {
                    Node::App(g, a) if g == apart && a.len() == 4 => match (a[1].node(), a[3].node()) {
                        (Node::Nat(n), Node::Nat(m)) => Some((a[0].clone(), n.to_u128()?, a[2].clone(), m.to_u128()?)),
                        _ => None,
                    },
                    _ => None,
                })
                .collect(),
            None => Vec::new(),
        };
        if *self.aparts.borrow() != ap {
            self.memo.borrow_mut().clear();
            *self.aparts.borrow_mut() = ap;
        }
        if *self.lit_facts.borrow() != lits {
            *self.lit_facts.borrow_mut() = lits.to_vec();
        }
    }

    /// The literals with the widths simp knows of their opaque words (`le(b,
    /// a, 1) in bits(8)`), for arithmetic: a value read from memory is a
    /// word, which arith alone does not see.
    fn width_facts(&self, lits: &[Term]) -> Vec<Term> {
        fn walk(sp: &Simp, t: &Term, out: &mut Vec<Term>) {
            let Node::App(f, a) = t.node() else { return };
            if *f == sp.s.all || *f == sp.s.ex {
                return;
            }
            let name = sp.env.kname(*f);
            let opaque = !sp.arith.contains_key(f) && !name.starts_with("bits_") && name != "bit" && matches!(sp.env.syms[*f as usize].kind, SymKind::Defined { .. } | SymKind::Primitive);
            if opaque && !out.contains(t) {
                if let (Some(n), Some(b), Some(i)) = ([8u64, 16, 32, 64].into_iter().find(|&n| sp.bits_term(t, n)), sp.env.ksym("bits").as_ref(), sp.s.in_) {
                    out.push(Term::app(i, vec![t.clone(), Term::app(*b, vec![Term::nat(crate::nat::Nat::from_u64(n))])]));
                }
            }
            for x in a {
                walk(sp, x, out);
            }
        }
        let mut found = Vec::new();
        for l in lits {
            walk(self, l, &mut found);
        }
        let mut out = lits.to_vec();
        out.extend(found);
        out
    }

    /// The bounds `x <= k` / `x >= k` (k a literal, x an integer) the
    /// literals state, each with the comparison it comes from.
    fn literal_bounds(&self, lits: &[Term]) -> Vec<(Term, bool, SInt, Term)> {
        use crate::nat::Nat;
        let one = SInt::nat(Nat::from_u64(1));
        let minus_one = SInt::new(true, Nat::from_u64(1));
        let mut out = Vec::new();
        for l in lits {
            let (neg, atom) = match l.node() {
                Node::App(n, a) if is(*n, self.s.not) && a.len() == 1 => (true, &a[0]),
                _ => (false, l),
            };
            let Node::App(f, b) = atom.node() else { continue };
            if b.len() != 2 {
                continue;
            }
            let strict = match self.env.kname(*f) {
                "int_lt" => true,
                "int_le" => false,
                _ => continue,
            };
            let (x, lit_left, k) = match (self.int_lit(&b[0]), self.int_lit(&b[1])) {
                (Some(k), None) => (&b[1], true, k),
                (None, Some(k)) => (&b[0], false, k),
                _ => continue,
            };
            if !self.int_term(x) {
                continue;
            }
            let (upper, k) = match (lit_left, strict, neg) {
                (false, false, false) => (true, k),             // x <= k
                (false, true, false) => (true, k.add(&minus_one)), // x < k
                (false, false, true) => (false, k.add(&one)),   // !(x <= k)
                (false, true, true) => (false, k),              // !(x < k)
                (true, false, false) => (false, k),             // k <= x
                (true, true, false) => (false, k.add(&one)),    // k < x
                (true, false, true) => (true, k.add(&minus_one)), // !(k <= x)
                (true, true, true) => (true, k),                // !(k < x)
            };
            out.push((x.clone(), upper, k, atom.clone()));
        }
        out
    }

    fn known(&self, t: &Term, ok: impl Fn(Ty) -> bool) -> bool {
        self.nats.borrow().iter().any(|(u, k)| u == t && ok(*k))
    }

    /// `bits_term` by the term's form alone (not the path's typing)
    fn bits_form(&self, t: &Term, n: u64) -> bool {
        let saved = std::mem::take(&mut *self.nats.borrow_mut());
        let r = self.bits_term(t, n);
        *self.nats.borrow_mut() = saved;
        r
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
        match self.env.kname(*f) {
            "bits_add" | "bits_mul" | "bits_sub" | "bits_shl" | "bits_shr" | "bits_and" | "bits_or" | "bits_xor" | "bits_sar" if a.len() == 3 => {
                width(&a[0]).is_some_and(|k| k <= n)
                    // (`and` of a numeral width with a mask below 2^n: a
                    // bits_build of a natural width, its bits the mask's)
                    || (self.env.ksym("bits_and") == Some(*f) && width(&a[0]).is_some() && [&a[1], &a[2]].iter().any(|c| matches!(c.node(), Node::Nat(v) if n >= 128 || v.to_u128().is_some_and(|v| v < (1u128 << n)))))
            }
            "bits_neg" | "bits_of_int" | "bits_not" if a.len() == 2 => width(&a[0]).is_some_and(|k| k <= n),
            "bits_sext" if a.len() == 3 => width(&a[1]).is_some_and(|k| k <= n),
            // a product with a literal c: an m-bit a times c is below
            // 2^(m + bits of c); a sum of two words below 2^(n-1)
            "int_mul" if a.len() == 2 => {
                let lit = |t: &Term| match t.node() {
                    Node::Nat(v) => v.to_u128(),
                    _ => None,
                };
                let bitlen = |c: u128| 128 - c.leading_zeros() as u64;
                [(&a[0], &a[1]), (&a[1], &a[0])].iter().any(|(x, c)| {
                    lit(c).is_some_and(|c| c > 0 && bitlen(c) <= n && self.bits_term(x, n - bitlen(c)))
                })
            }
            "int_add" if a.len() == 2 && n >= 1 => self.bits_term(&a[0], n - 1) && self.bits_term(&a[1], n - 1),
            // (a bits_build of the width: a partial register write)
            "bits_set_slice" | "bits_set_bit" if !a.is_empty() => width(&a[0]).is_some_and(|k| k <= n),
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
                    Node::App(g, gb) if self.env.ksym("bits_of_int") == Some(*g) && gb.len() == 2 => {
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
        if matches!(t.node(), Node::Nat(_)) || self.known(t, |k| matches!(k, Ty::Nat | Ty::Bits(_))) {
            return true;
        }
        if (0..=128).any(|n| n % 8 == 0 && self.bits_term(t, n)) {
            return true;
        }
        let Node::App(f, a) = t.node() else { return false };
        match self.env.kname(*f) {
            "int_abs" => true,
            "int_mod" if a.len() == 2 => matches!(a[1].node(), Node::Nat(k) if !k.is_zero()),
            _ => false,
        }
    }

    /// `t` is an integer (in int): a literal, an operation of arithmetic
    /// (their results are integers), or known on the path.
    fn int_term(&self, t: &Term) -> bool {
        if self.int_lit(t).is_some() || self.known(t, |k| !matches!(k, Ty::Univ(_))) {
            return true;
        }
        let Node::App(f, _) = t.node() else { return false };
        const INT_OPS: &[&str] = &[
            "int_val", "int_abs", "int_neg", "int_succ", "int_pred", "int_add", "int_sub", "int_mul", "int_pow", "int_div", "int_mod", "int_sum", "pow2",
            "sint",
        ];
        if INT_OPS.contains(&self.env.kname(*f)) || self.nat_term(t) {
            return true;
        }
        // a definition whose body is an integer operation (`bytes_at`, a sum)
        match &self.env.syms[*f as usize].kind {
            SymKind::Defined { body, .. } => matches!(body.node(), Node::App(g, _) if INT_OPS.contains(&self.env.kname(*g))),
            _ => false,
        }
    }

    /// Reads through a store (`x86_64_linux.store_le(b, a, n, v)`, the
    /// memory b with the n bytes at a replaced by v's, little-endian): a
    /// byte at a known distance from a, and `le` of the same or a disjoint
    /// range (distances from the definitions; addresses are 64-bit).
    /// The n bytes at x lie in [r, r + len) (x at a known distance from r).
    fn within(&self, x: &Term, n: u128, r: &Term, len: u128) -> bool {
        if self.distance(x, r, 64).is_some_and(|d| d.checked_add(n).is_some_and(|e| e <= len)) {
            return true;
        }
        // (a base c plus an offset t the path bounds, in a region at a
        // literal r: r - c <= t and t + n <= r - c + len -- no wrap, the
        // sum below 2^64)
        let lit = |t: &Term| match t.node() {
            Node::Nat(v) => v.to_u128().filter(|v| *v < 1u128 << 64).map(|v| v as i128),
            _ => None,
        };
        let Some(r) = lit(r) else { return false };
        let parts = match x.node() {
            Node::App(g, a) if self.arith.get(g) == Some(&"int_add") && a.len() == 2 => match (lit(&a[0]), lit(&a[1])) {
                (Some(c), None) => Some((c, a[1].clone())),
                (None, Some(c)) => Some((c, a[0].clone())),
                _ => None,
            },
            Node::App(g, a) if self.arith.get(g) == Some(&"bits_add") && a.len() == 3 && matches!(a[0].node(), Node::Nat(w) if w.to_u64() == Some(64)) => match (lit(&a[1]), lit(&a[2])) {
                (Some(c), None) => Some((c, a[2].clone())),
                (None, Some(c)) => Some((c, a[1].clone())),
                _ => None,
            },
            _ => None,
        };
        let Some((c, t)) = parts else { return false };
        let to_i = |k: &SInt| k.m.to_u128().filter(|v| *v < 1u128 << 100).map(|v| if k.neg { -(v as i128) } else { v as i128 });
        let mut lo: Option<i128> = (self.nat_term(&t) || self.bits_term(&t, 64)).then_some(0);
        let mut hi: Option<i128> = (1..=64u64).find(|&k| self.bits_term(&t, k)).map(|k| (1i128 << k) - 1);
        for (u, upper, k, _) in self.bounds.borrow().iter() {
            if *u != t {
                continue;
            }
            let Some(k) = to_i(k) else { continue };
            if *upper {
                hi = Some(hi.map_or(k, |h| h.min(k)));
            } else {
                lo = Some(lo.map_or(k, |l| l.max(k)));
            }
        }
        let (Some(lo), Some(hi)) = (lo, hi) else { return false };
        lo >= r - c && hi + n as i128 <= r - c + len as i128 && c + hi + (n as i128) <= (1i128 << 64)
    }

    /// Which side of an `apart` fact the n bytes at x lie in, for a fact
    /// that also places the m bytes at y on the other side: (fact index,
    /// x in its first region).
    fn apart_sides(&self, x: &Term, n: u128, y: &Term, m: u128) -> Option<(usize, bool)> {
        self.aparts.borrow().iter().enumerate().find_map(|(i, (a, an, b, bm))| {
            if self.within(x, n, a, *an) && self.within(y, m, b, *bm) {
                Some((i, true))
            } else if self.within(x, n, b, *bm) && self.within(y, m, a, *an) {
                Some((i, false))
            } else {
                None
            }
        })
    }

    /// The n bytes at x and the m bytes at y are disjoint (by an `apart`
    /// fact of the path).
    fn disjoint(&self, x: &Term, n: u128, y: &Term, m: u128) -> bool {
        self.apart_sides(x, n, y, m).is_some()
    }

    /// Stores in a canonical order: a store to the first region of an
    /// `apart` fact moves out past a store to its second region (they
    /// commute: disjoint bytes); a store of the same n bytes at the same
    /// address replaces an earlier one.
    fn store_order(&self, args: &[Term]) -> Option<Term> {
        let store = self.env.ksym("x86_64_linux.store_le")?;
        let Node::App(g, inner) = args[0].node() else { return None };
        if *g != store || inner.len() != 4 {
            return None;
        }
        let lit = |t: &Term| match t.node() {
            Node::Nat(v) => v.to_u128(),
            _ => None,
        };
        let (n1, n2) = (lit(&inner[2])?, lit(&args[2])?);
        // (overwritten)
        if n1 == n2 && self.distance(&args[1], &inner[1], 64) == Some(0) {
            return Some(self.term(&Term::app(store, vec![inner[0].clone(), args[1].clone(), args[2].clone(), args[3].clone()])));
        }
        // (the inner store to the first region: moved out)
        if let Some((_, true)) = self.apart_sides(&inner[1], n1, &args[1], n2) {
            let swapped_in = self.term(&Term::app(store, vec![inner[0].clone(), args[1].clone(), args[2].clone(), args[3].clone()]));
            return Some(self.term(&Term::app(store, vec![swapped_in, inner[1].clone(), inner[2].clone(), inner[3].clone()])));
        }
        None
    }

    fn read_store(&self, f: SymId, args: &[Term]) -> Option<Term> {
        let name = |g: SymId| self.env.kname(g);
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
            // app(store_le(b, a, n, v), x), x an address (store_le is a
            // function on bits(64): elsewhere it is no byte)
            let st = store(&args[0])?;
            if !self.bits_term(&args[1], 64) {
                return None;
            }
            let n = lit(&st[2])?;
            // (x in a region apart from the store's: b's byte)
            if self.disjoint(&args[1], 1, &st[1], n) {
                return Some(self.term(&Term::app(f, vec![st[0].clone(), args[1].clone()])));
            }
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
            if self.disjoint(&args[1], m, &st[1], n) {
                return Some(self.term(&Term::app(f, vec![st[0].clone(), args[1].clone(), args[2].clone()])));
            }
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
        let name = self.env.kname(f);
        let lit = |t: &Term| -> Option<std::rc::Rc<[u8]>> {
            match t.node() {
                Node::Bytes(b) => Some(b.clone()),
                _ => None,
            }
        };
        let seq = |t: &Term| -> Option<std::rc::Rc<[u8]>> {
            match t.node() {
                Node::App(g, b) if self.env.ksym("bytes_seq") == Some(*g) && b.len() == 1 => lit(&b[0]),
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
        let r = self.let_look_term(r);
        self.memo.borrow_mut().insert(key, (t.clone(), r.clone()));
        r
    }

    /// a fresh local constant for a let's variable
    fn let_var(&self) -> crate::term::VarId {
        let v = self.let_fresh.get();
        self.let_fresh.set(v + 1);
        v
    }

    /// a node r with a let's constant as an argument: with the value
    /// there, if a rule then fires (the result not the node so formed)
    fn let_look_term(&self, r: Term) -> Term {
        if self.let_env.borrow().is_empty() {
            return r;
        }
        let Node::App(_, a) = r.node() else { return r };
        let env = self.let_env.borrow().clone();
        let mut args = a.to_vec();
        let mut any = false;
        for x in args.iter_mut() {
            if let Node::Var(v, va) = x.node() {
                if va.is_empty() {
                    if let Some((_, val)) = env.iter().rev().find(|(c, _)| c == v) {
                        *x = val.clone();
                        any = true;
                    }
                }
            }
        }
        if !any {
            return r;
        }
        let formed = r.with_args(args);
        let r2 = self.term_uncached(&formed);
        if r2 != formed {
            r2
        } else {
            r
        }
    }

    /// the let t (its value simplified v) reduced at once: v small, or
    /// open, or the let named in `simp(.., lets(expand(..)))` -- and not
    /// one named in `lets(keep(..))`
    fn let_reduced(&self, t: &Term, v: &Term) -> bool {
        if self.env.loose_depth_m(v) > 0 {
            return true;
        }
        match t.binder_name().and_then(|n| n.split(' ').next()) {
            Some(n) if self.lets.0.iter().any(|k| k == n) => false,
            Some(n) if self.lets.1.iter().any(|k| k == n) => true,
            _ => let_inline(v),
        }
    }

    /// a let's body simplified with its variable a local constant bound to
    /// the value v (`simp` the body's simplifier): the result, with the let
    /// as it ends up (kept, substituted, dropped)
    fn let_body(&self, t: &Term, v: Term, body: &Term, simp: &dyn Fn(&Term) -> Term) -> Term {
        let c = self.let_var();
        let open = inst_k(self.env, body, &[Term::var(c, vec![])]);
        self.let_env.borrow_mut().push((c, v.clone()));
        let b = simp(&open);
        self.let_env.borrow_mut().pop();
        // (a let named in `lets(keep(..))` kept used once too)
        let kept = t.binder_name().and_then(|n| n.split(' ').next()).is_some_and(|n| self.lets.0.iter().any(|k| k == n));
        match var_uses(&b, c, 2) {
            0 => b,
            1 if !kept => simp(&b.subst_var(c, &v, &self.env.binders_fn())),
            _ => t.with_args(vec![v, let_abstract(self.env, &b, c)]),
        }
    }

    fn term_uncached(&self, t: &Term) -> Term {
        let s = &self.s;
        let Node::App(f, a) = t.node() else { return t.clone() };
        let f = *f;
        // `fn_modify(f, k, y. g)`: `fn_update` of f bound by a let (f a local
        // constant while the update is simplified)
        if is(f, s.fn_modify) && a.len() == 3 {
            if let (Some(upd), Some(app)) = (s.fn_update, s.app) {
                let fv = self.term(&a[0]);
                let mk = |x: &Term| {
                    let old = Term::app(app, vec![x.clone(), a[1].clone()]);
                    Term::app(upd, vec![x.clone(), a[1].clone(), inst_k(self.env, &a[2], &[old])])
                };
                if let_inline(&fv) || self.env.loose_depth_m(&fv) > 0 || self.env.loose_depth_m(&a[1]) > 0 {
                    return self.term(&mk(&fv));
                }
                let c = self.let_var();
                self.let_env.borrow_mut().push((c, fv.clone()));
                let b = self.term(&mk(&Term::var(c, vec![])));
                self.let_env.borrow_mut().pop();
                return match var_uses(&b, c, 2) {
                    0 => b,
                    1 => self.term(&b.subst_var(c, &fv, &self.env.binders_fn())),
                    _ => match s.letin {
                        Some(l) => Term::app(l, vec![fv, let_abstract(self.env, &b, c)]),
                        None => self.term(&b.subst_var(c, &fv, &self.env.binders_fn())),
                    },
                };
            }
        }
        // `letin(a, x. body)`: β for a small value, else lazily
        if is(f, s.letin) {
            let v = self.term(&a[0]);
            if self.let_reduced(t, &v) {
                return self.term(&inst_k(self.env, &a[1], &[v]));
            }
            return self.let_body(t, v, &a[1], &|b| self.term(b));
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
        // a symbol a premise unfolds (`all xs. f(xs) = rhs`): rhs instantiated
        if let Some((_, _, rule)) = self.rewrites.iter().find(|(g, n, _)| *g == f && *n == a.len()) {
            let mut r = rule.clone();
            for x in a.iter() {
                let body = match r.node() {
                    Node::App(_, b) => b[0].clone(),
                    _ => break,
                };
                r = inst_k(self.env, &body, &[x.clone()]);
            }
            if let Node::App(e, b) = r.node() {
                if *e == s.eq {
                    return self.term(&b[1]);
                }
            }
        }
        let mut args: Vec<Term> = a.iter().map(|x| self.term(x)).collect();
        // a bit of a numeral, as a value (`c = bit(7, 0)`): the proposition
        if self.env.ksym("bit") == Some(f) && args.len() == 2 {
            if let Some(b) = self.literal_prop(&t.with_args(args.clone())) {
                return if b { self.tt() } else { self.ff() };
            }
        }
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
                if !matches!(args[i].node(), Node::App(g, _) if matches!(self.env.kname(*g), "int_add" | "int_sub")) {
                    continue;
                }
                let Some(boi) = self.s.bits_of_int else { continue };
                let w = self.term(&Term::app(boi, vec![Term::nat(crate::nat::Nat::from_u64(n)), args[i].clone()]));
                if matches!(w.node(), Node::Nat(_)) || matches!(w.node(), Node::App(g, _) if self.env.ksym("bits_add") == Some(*g)) {
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
        // an outcome with a ghost part h: its state joined with h
        // (`with_ghost_ok`, `_exc`, `_diverge`, core/records.core)
        if is(f, s.with_ghost) && args.len() == 2 {
            if let (Some((g, b)), Some(u)) = (head(&args[0]), s.union2) {
                if (is(g, s.ok) || is(g, s.exc)) && b.len() == 2 {
                    let st = self.term(&Term::app(u, vec![b[0].clone(), args[1].clone()]));
                    return Term::app(g, vec![st, b[1].clone()]);
                }
                if is(g, s.diverge) {
                    return args[0].clone();
                }
            }
        }
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
                    // `out_state(o) = fst(snd(o))`, `out_value(o) = snd(snd(o))`
                    if let Some((h, c)) = head(&b[1]) {
                        if is(h, s.pair) || is(h, s.tag) {
                            return if is(f, s.out_state) { c[0].clone() } else { c[1].clone() };
                        }
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
        // a sum over numeral bounds, term by term (`int_sum`'s definition and
        // the recursion equations of `nat_rec`): f(a) + .. + f(b - 1)
        if self.env.ksym("int_sum") == Some(f) && args.len() == 3 {
            if let (Node::Nat(a0), Node::Nat(b0)) = (args[0].node(), args[1].node()) {
                if let (Some(a0), Some(b0)) = (a0.to_u64(), b0.to_u64()) {
                    if a0 <= b0 && b0 - a0 <= 64 {
                        let add = self.env.ksym("int_add");
                        let empty = self.env.ksym("empty");
                        if let (Some(add), Some(empty)) = (add, empty) {
                            let mut r = Term::app(empty, vec![]);
                            for k in a0..b0 {
                                let fk = inst_k(self.env, &args[2], &[Term::nat(crate::nat::Nat::from_u64(k))]);
                                r = Term::app(add, vec![r, fk]);
                            }
                            return self.term(&r);
                        }
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
            // x / 1 = x * 1 = x for an integer x
            if (*op == "int_div" || *op == "int_mul") && args.len() == 2 && self.int_lit(&args[1]).is_some_and(|c| !c.neg && c.m == crate::nat::Nat::from_u64(1)) && self.int_term(&args[0]) {
                return args[0].clone();
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
            // addresses in canonical form: base + offset (`bits_of_int` of
            // a term not a word by its form -- not by the typing, which a
            // premise and the goal need not share: one normal form for both)
            if ((*op == "bits_add" || *op == "bits_sub") && args.len() == 3) || (*op == "bits_of_int" && args.len() == 2 && !self.bits_form(&args[1], 64)) {
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
            // `and` with a low mask 2^k - 1 (k <= n): x mod 2^k; `and` of x
            // with itself: x (as n bits)
            if *op == "bits_and" && args.len() == 3 {
                if let Node::Nat(w) = args[0].node() {
                    if let Some(n) = w.to_u64().filter(|&n| n <= 128) {
                        if args[1] == args[2] {
                            return self.term(&Term::app(self.s.bits_of_int.unwrap(), vec![args[0].clone(), args[1].clone()]));
                        }
                        for (x, c) in [(&args[1], &args[2]), (&args[2], &args[1])] {
                            if let Node::Nat(c) = c.node() {
                                let k = (0..=n).find(|&k| crate::nat::Nat::pow2(k).sub(&crate::nat::Nat::from_u64(1)).as_ref() == Some(c));
                                if let Some(k) = k {
                                    // (as `bits_add(k, x, 0)`, the canonical form of x mod 2^k)
                                    let z = Term::nat(crate::nat::Nat::zero());
                                    return self.term(&Term::app(self.s.bits_add.unwrap(), vec![Term::nat(crate::nat::Nat::from_u64(k)), x.clone(), z]));
                                }
                            }
                        }
                    }
                }
            }
            // x + 0 mod 2^n: x for an n-bit x; mod 2^k of a value mod 2^n
            // (k <= n): mod 2^k of the value
            if *op == "bits_add" && args.len() == 3 && self.int_lit(&args[2]).is_some_and(|c| c.m.is_zero()) {
                if let Node::Nat(k) = args[0].node() {
                    if let Some(k) = k.to_u64().filter(|&k| k <= 128) {
                        if self.bits_term(&args[1], k) {
                            return args[1].clone();
                        }
                        if let Node::App(g, b) = args[1].node() {
                            let inner_n = match b.first().map(|x| x.node()) {
                                Some(Node::Nat(n)) => n.to_u64(),
                                _ => None,
                            };
                            if self.arith.get(g) == Some(&"bits_add") && b.len() == 3 && inner_n.is_some_and(|n| k <= n) && self.int_lit(&b[2]).is_some_and(|c| c.m.is_zero()) {
                                return self.term(&t.with_args(vec![args[0].clone(), b[1].clone(), args[2].clone()]));
                            }
                        }
                    }
                }
            }
            // x + x: 2 * x (an index scaled by `lea (x, x)`)
            if *op == "int_add" && args.len() == 2 && args[0] == args[1] && self.int_term(&args[0]) {
                if let Some(m) = self.env.ksym("int_mul").as_ref() {
                    return self.term(&Term::app(*m, vec![args[0].clone(), Term::nat(crate::nat::Nat::from_u64(2))]));
                }
            }
            // x * 1 (an address's scale): x mod 2^n
            if *op == "bits_mul" && args.len() == 3 {
                let one = |t: &Term| matches!(t.node(), Node::Nat(v) if v.to_u64() == Some(1));
                for (x, c) in [(&args[1], &args[2]), (&args[2], &args[1])] {
                    if one(c) {
                        return self.term(&Term::app(self.s.bits_of_int.unwrap(), vec![args[0].clone(), x.clone()]));
                    }
                }
            }
            // the signed value of a sign extension (m <= n): the signed m-bit
            // value (`sint(n, bits_of_int(n, sint(m, y)))`, in n-bit range)
            if *op == "sint" && args.len() == 2 {
                // (of a non-negative value, below 2^(n-1): the value)
                if let Node::Nat(n) = args[0].node() {
                    if n.to_u64().is_some_and(|n| (2..=129).contains(&n) && self.bits_term(&args[1], n - 1)) {
                        return args[1].clone();
                    }
                }
                if let (Node::Nat(n), Node::App(g, b)) = (args[0].node(), args[1].node()) {
                    if self.arith.get(g) == Some(&"bits_sext") && b.len() == 3 && b[1] == args[0] && matches!(b[0].node(), Node::Nat(m) if m <= n) {
                        return self.term(&t.with_args(vec![b[0].clone(), b[2].clone()]));
                    }
                }
            }
            // an operand of an n-bit operation is read mod 2^n: the signed
            // m-bit value of y (m >= n) as y; as all of it, the signed m-bit
            // value (m < n) is y sign extended
            if ((*op == "bits_add" || *op == "bits_sub") && args.len() == 3) || (*op == "bits_of_int" && args.len() == 2) {
                if let Node::Nat(n) = args[0].node() {
                    let sint_of = |x: &Term| match x.node() {
                        Node::App(g, b) if self.arith.get(g) == Some(&"sint") && b.len() == 2 => match b[0].node() {
                            Node::Nat(m) => Some((m.clone(), b[1].clone())),
                            _ => None,
                        },
                        _ => None,
                    };
                    let mut new = args.clone();
                    let mut changed = false;
                    // (likewise the low k+1 bits of y, k+1 >= n: y -- as a
                    // slice, or y mod 2^(k+1), `bits_add(k+1, y, 0)`)
                    let slice_of = |x: &Term| match x.node() {
                        Node::App(g, b) if self.arith.get(g) == Some(&"bits_slice") && b.len() == 3 => match (b[1].node(), b[2].node()) {
                            (Node::Nat(k), Node::Nat(lo)) if lo.is_zero() => Some((k.clone(), b[0].clone())),
                            _ => None,
                        },
                        Node::App(g, b) if self.arith.get(g) == Some(&"bits_add") && b.len() == 3 && self.int_lit(&b[2]).is_some_and(|c| c.m.is_zero()) => match b[0].node() {
                            Node::Nat(m) if !m.is_zero() => Some((m.sub(&crate::nat::Nat::from_u64(1))?, b[1].clone())),
                            _ => None,
                        },
                        _ => None,
                    };
                    for x in new.iter_mut().skip(1) {
                        if let Some((m, y)) = sint_of(x) {
                            if m >= *n {
                                *x = y;
                                changed = true;
                            }
                        } else if let Some((k, y)) = slice_of(x) {
                            if k.to_u64().zip(n.to_u64()).is_some_and(|(k, n)| k + 1 >= n) {
                                *x = y;
                                changed = true;
                            }
                        }
                    }
                    if changed {
                        return self.term(&t.with_args(new));
                    }
                    let zero = *op == "bits_of_int" || (*op == "bits_add" && self.int_lit(&args[2]).is_some_and(|c| c.m.is_zero()));
                    if let (true, Some((m, y)), Some(sx)) = (zero, sint_of(&args[1]), self.env.ksym("bits_sext").as_ref()) {
                        if m < *n {
                            return self.term(&Term::app(*sx, vec![Term::nat(m), args[0].clone(), y]));
                        }
                    }
                }
            }
            // the sign extension (m <= n) of a non-negative m-bit x (x below
            // 2^(m-1)): x
            if *op == "bits_sext" && args.len() == 3 {
                if let (Node::Nat(m), Node::Nat(n)) = (args[0].node(), args[1].node()) {
                    if m <= n && m.to_u64().is_some_and(|m| (2..=129).contains(&m) && self.bits_term(&args[2], m - 1)) {
                        return args[2].clone();
                    }
                }
            }
            // x mod k of an n-bit x with 2^n <= k: x
            if *op == "int_mod" && args.len() == 2 {
                if let Node::Nat(k) = args[1].node() {
                    if (1..=128u64).any(|n| crate::nat::Nat::pow2(n) <= *k && self.bits_term(&args[0], n)) {
                        return args[0].clone();
                    }
                    // x mod 2^n: as `bits_add(n, x, 0)` (one form for the
                    // value of n bits; for any x: int_mod reads x through
                    // int_val, as x + 0 is)
                    if let Some(n) = (1..=128u64).find(|&n| crate::nat::Nat::pow2(n) == *k) {
                        let z = Term::nat(crate::nat::Nat::zero());
                        return self.term(&Term::app(self.s.bits_add.unwrap(), vec![Term::nat(crate::nat::Nat::from_u64(n)), args[0].clone(), z]));
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
                    // the low k+1 bits: x mod 2^(k+1), in its one form
                    // `bits_add(k+1, x, 0)`
                    if lo.is_zero() && hi.to_u64().is_some_and(|h| h < 256) {
                        let z = Term::nat(crate::nat::Nat::zero());
                        return self.term(&Term::app(self.s.bits_add.unwrap(), vec![Term::nat(hi.add(&crate::nat::Nat::from_u64(1))), args[0].clone(), z]));
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
        if args.len() == 4 && self.env.ksym("x86_64_linux.store_le") == Some(f) {
            if let Some(v) = self.store_order(&args) {
                return v;
            }
        }
        if let Some(v) = self.bytes(f, &args) {
            return v;
        }
        if self.env.ksym("bits_set_slice") == Some(f) && args.len() == 5 {
            let num = |x: &Term| match x.node() {
                Node::Nat(v) => v.to_u64(),
                _ => None,
            };
            if let (Some(n), Some(hi), Some(0)) = (num(&args[0]), num(&args[2]), num(&args[3])) {
                if n >= 1 && hi == n - 1 && self.bits_term(&args[4], n) {
                    return args[4].clone();
                }
                // (all the bits x has, written: x and v of hi + 1 bits, hi <
                // n -- a 16-bit write to a register holding a 16-bit value)
                if hi < 128 && hi < n && self.bits_term(&args[1], hi + 1) && self.bits_term(&args[4], hi + 1) {
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
                    // ... for any a the premises or path give `a in d`
                    // (a C function applied to its arguments)
                    Some((g, b))
                        if is(g, s.fn_build)
                            && (self.known_mems.borrow().iter().any(|l| matches!(l.node(), Node::App(_, ab) if ab[0] == args[1] && ab[1] == b[0]))
                                || matches!(b[0].node(), Node::App(bt, w) if self.env.ksym("bits") == Some(*bt) && w.len() == 1
                                    && matches!(w[0].node(), Node::Nat(k) if k.to_u64().is_some_and(|k| self.bits_term(&args[1], k))))) =>
                    {
                        return self.term(&inst_k(self.env, &b[1], &[args[1].clone()]));
                    }
                    // records through restriction, ghost parts and merges
                    // (`app_ext`: the pairs with first element k are the same)
                    Some((g, b)) => {
                        let name = self.env.kname(g);
                        let k = &args[1];
                        match name {
                            // no pair at all: `empty` (app's default)
                            "empty" if b.is_empty() => return m,
                            // a one-element list's element (`seq_one(x)` is
                            // `single(pair(0, x))`)
                            "seq_one" if b.len() == 1 && matches!(k.node(), Node::Nat(n) if n.is_zero()) => return b[0].clone(),
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
        // record operations through updates: a ghost part drops an update
        // at one of its keys; a restriction keeps it (outside); merging
        // with `empty` changes nothing
        {
            let name = self.env.kname(f);
            let is_empty = |t: &Term| matches!(t.node(), Node::App(e, b) if b.is_empty() && is(*e, s.empty));
            if (name == "ghost_part" || name == "restrict") && args.len() == 2 {
                if is_empty(&args[0]) {
                    return args[0].clone();
                }
                if let Node::App(u, ub) = args[0].node() {
                    if is(*u, s.fn_update) && self.key_in(&ub[1], &args[1]) == Some(true) {
                        if name == "ghost_part" {
                            return self.term(&Term::app(f, vec![ub[0].clone(), args[1].clone()]));
                        }
                        let inner = self.term(&Term::app(f, vec![ub[0].clone(), args[1].clone()]));
                        return Term::app(*u, vec![inner, ub[1].clone(), ub[2].clone()]);
                    }
                }
            }
            if (name == "union2" || name == "rec_merge") && args.len() == 2 {
                if is_empty(&args[1]) {
                    return args[0].clone();
                }
                if is_empty(&args[0]) {
                    return args[1].clone();
                }
            }
        }
        // an update of a joined record: in the part with the field, the
        // other lacking it (`fn_update_union_l`/`_r`, core/records.core)
        if is(f, s.fn_update) {
            if let Some((u, ub)) = head(&args[0]) {
                let un = self.env.kname(u);
                if (un == "union2" || un == "rec_merge") && ub.len() == 2 {
                    if self.lacks(&ub[1], &args[1]) {
                        let inner = self.term(&Term::app(f, vec![ub[0].clone(), args[1].clone(), args[2].clone()]));
                        return Term::app(u, vec![inner, ub[1].clone()]);
                    }
                    if self.lacks(&ub[0], &args[1]) {
                        let inner = self.term(&Term::app(f, vec![ub[1].clone(), args[1].clone(), args[2].clone()]));
                        return Term::app(u, vec![ub[0].clone(), inner]);
                    }
                }
            }
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
        let r = self.prop_(t, pol);
        let s = &self.s;
        let atom = match r.node() {
            Node::App(f, _) => ![s.and, s.or, s.not].iter().any(|g| is(*f, *g)) && *f != s.ex && *f != s.all && *f != self.env.builtins.imp && !is(*f, s.letin),
            _ => false,
        };
        if !atom {
            return r;
        }
        // (an atom with a let kept in it: with its lets reduced, if the atom
        // is then decided -- a local expansion for a decision)
        if s.letin.is_some_and(|l| has_sym(self.env, &r, l)) && !LET_EAGER.with(|e| e.get()) {
            let prev = LET_EAGER.with(|e| e.replace(true));
            let r2 = self.prop_(&r, pol);
            LET_EAGER.with(|e| e.set(prev));
            if self.is_true(&r2) || self.is_false(&r2) {
                return r2;
            }
        }
        if self.let_env.borrow().is_empty() {
            return r;
        }
        // (an atom mentioning a let's constant: with its value, if the atom
        // is then decided or a rule fires)
        let env = self.let_env.borrow().clone();
        let bf = self.env.binders_fn();
        let mut formed = r.clone();
        for (c, v) in env.iter().rev() {
            if formed.may_contain_var(*c) {
                formed = formed.subst_var(*c, v, &bf);
            }
        }
        if formed == r {
            return r;
        }
        let r2 = self.prop_(&formed, pol);
        if r2 != formed {
            r2
        } else {
            r
        }
    }

    fn prop_(&self, t: &Term, pol: Pol) -> Term {
        let s = &self.s;
        let Node::App(f, a) = t.node() else { return t.clone() };
        let f = *f;
        // (eager, in a goal: a path literal holds, its negation fails --
        // equations too, which are decided below before atoms are)
        if self.eager_runs.get() && f == s.eq {
            let lf = self.lit_facts.borrow();
            if lf.contains(t) {
                return self.tt();
            }
            if lf.iter().any(|l| matches!(l.node(), Node::App(n, b) if is(*n, s.not) && b[0] == *t)) {
                return self.ff();
            }
        }
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
            if pol == Pol::Goal {
                if let Some(r) = self.update_chains_goal(&a[0], &a[1]) {
                    return r;
                }
            }
            // a proposition equal to true / false (`(c || z) = bit(7, 0)`, a
            // jump's condition): the proposition / its negation
            for (p, c) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                if self.prop_shaped(p, 4) {
                    let c = self.term(c);
                    if self.is_true(&c) {
                        return self.prop(p, pol);
                    }
                    if self.is_false(&c) {
                        return self.prop(&self.not(p.clone()), pol);
                    }
                }
            }
            let r = self.eq(&a[0], &a[1]);
            if matches!(r.node(), Node::App(e, b) if *e == f && b[0].ptr_eq(&a[0]) && b[1].ptr_eq(&a[1])) {
                return t.clone();
            }
            return r;
        }
        if f == s.ex {
            // (one-point first: a leading conjunct that simplifies to `x =
            // t` instantiates the rest before it is simplified -- a
            // program's block form, whose rest may be all of the program
            // after it, and whose outcome the head decides)
            if let Node::App(c, b) = a[0].node() {
                if is(*c, s.and) {
                    let x = self.prop(&b[0], pol);
                    if let Node::App(e, eb) = x.node() {
                        if *e == s.eq {
                            for (v, t) in [(&eb[0], &eb[1]), (&eb[1], &eb[0])] {
                                if matches!(v.node(), Node::BVar(0)) && !has_bvar(self.env, t, 0) {
                                    let r = inst_k(self.env, &b[1], &[lower(self.env, t, 0)]);
                                    return self.prop(&r, if pol == Pol::Goal && self.eager_runs.get() { Pol::Goal } else { Pol::Other });
                                }
                            }
                        }
                    }
                    // (else as a conjunction, then the binder)
                    let body = if self.is_false(&x) { x } else { self.and(x, self.prop(&b[1], pol)) };
                    return self.ex(&body, pol == Pol::Goal);
                }
            }
            return self.ex(&self.prop(&a[0], pol), pol == Pol::Goal);
        }
        if f == s.all {
            return self.all(&self.prop(&a[0], pol));
        }
        if is(f, s.letin) {
            let v = self.term(&a[0]);
            if self.let_reduced(t, &v) {
                return self.prop(&inst_k(self.env, &a[1], &[v]), pol);
            }
            return self.let_body(t, v, &a[1], &|b| self.prop(b, pol));
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
            if pol == Pol::Goal {
                if let Some(r) = self.typed_goal(&a[0], &a[1], None) {
                    return r;
                }
            }
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
                    // `bool`: a proposition is false or true (`eq_prop`,
                    // `imp_prop`, `ex_prop`, `false_is_prop`)
                    "upair" if self.is_bool_pair(&gb[0], &gb[1]) && self.prop_shaped(&z, 4) => return self.tt(),
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
        // in the goal, with `unroll`: a loop whose condition is decided, an
        // iteration at a time
        if pol == Pol::Goal && self.goal_loops && self.env.ksym("while_rel") == Some(f) && a.len() == 5 {
            if let Some(r) = self.goal_loop(a) {
                return r;
            }
        }
        // an atom: its arguments as terms
        let t0 = t;
        let t = self.term(t);
        // (unfolded by a premise into a proposition: `cond(f, cc)` by
        // x86.cond_eval: simplified as one)
        if t != *t0 {
            if let Node::App(g, _) = t.node() {
                if *g != f && (*g == s.imp || *g == s.eq || *g == s.ex || *g == s.all || is(*g, s.not) || is(*g, s.and) || is(*g, s.or)) {
                    return self.prop(&t, pol);
                }
            }
        }
        if let Some(b) = self.literal_prop(&t).or_else(|| self.bound_prop(&t)) {
            return if b { self.tt() } else { self.ff() };
        }
        // (eager, in a goal: a path literal holds, its negation fails)
        if self.eager_runs.get() {
            let lf = self.lit_facts.borrow();
            if lf.contains(&t) {
                return self.tt();
            }
            if lf.iter().any(|l| matches!(l.node(), Node::App(n, a) if is(*n, self.s.not) && a[0] == t)) {
                return self.ff();
            }
        }
        t
    }

    /// A comparison of a literal k with a term x known to be a natural (x
    /// >= 0) or a word of a width n (0 <= x <= 2^n - 1): decided when k lies
    /// outside that range (`int_le(2^63, x)` is false for a 32-bit x).
    fn bound_prop(&self, t: &Term) -> Option<bool> {
        use crate::nat::Nat;
        let Node::App(m, b) = t.node() else { return None };
        if b.len() != 2 {
            return None;
        }
        let strict = match self.env.syms.get(*m as usize)?.name.as_str() {
            "int_lt" => true,
            "int_le" => false,
            _ => return None,
        };
        let (k, x, lit_left) = match (self.int_lit(&b[0]), self.int_lit(&b[1])) {
            (Some(k), None) => (k, &b[1], true),
            (None, Some(k)) => (k, &b[0], false),
            _ => return None,
        };
        let zero = SInt::nat(Nat::zero());
        let mut lo = self.nat_term(x).then(|| zero.clone());
        let mut hi = (1..=128u64).find(|&n| self.bits_term(x, n)).map(|n| SInt::nat(Nat::pow2(n)).add(&SInt::new(true, Nat::from_u64(1))));
        // the path's literal bounds on x (not one from t itself: a literal
        // does not decide itself)
        for (y, upper, k, src) in self.bounds.borrow().iter() {
            if y != x || src == t {
                continue;
            }
            if *upper {
                if hi.as_ref().is_none_or(|h| k.lt(h)) {
                    hi = Some(k.clone());
                }
            } else if lo.as_ref().is_none_or(|l| l.lt(k)) {
                lo = Some(k.clone());
            }
        }
        // x's range [lo, hi] against k: x < k, x <= k, k < x, k <= x
        let below = |a: &SInt, c: &SInt| a.lt(c);
        let le = |a: &SInt, c: &SInt| !c.lt(a);
        match (lit_left, strict) {
            // k < x: true when k < lo; false when hi <= k
            (true, true) => {
                if lo.as_ref().is_some_and(|l| below(&k, l)) {
                    return Some(true);
                }
                if hi.as_ref().is_some_and(|h| le(h, &k)) {
                    return Some(false);
                }
            }
            // k <= x: true when k <= lo; false when hi < k
            (true, false) => {
                if lo.as_ref().is_some_and(|l| le(&k, l)) {
                    return Some(true);
                }
                if hi.as_ref().is_some_and(|h| below(h, &k)) {
                    return Some(false);
                }
            }
            // x < k: true when hi < k; false when k <= lo
            (false, true) => {
                if hi.as_ref().is_some_and(|h| below(h, &k)) {
                    return Some(true);
                }
                if lo.as_ref().is_some_and(|l| le(&k, l)) {
                    return Some(false);
                }
            }
            // x <= k: true when hi <= k; false when k < lo
            (false, false) => {
                if hi.as_ref().is_some_and(|h| le(h, &k)) {
                    return Some(true);
                }
                if lo.as_ref().is_some_and(|l| below(&k, l)) {
                    return Some(false);
                }
            }
        }
        None
    }

    /// `{a, b}` is `{false, true}`.
    fn is_bool_pair(&self, a: &Term, b: &Term) -> bool {
        let named = |t: &Term, n: &str| matches!(t.node(), Node::App(g, x) if x.is_empty() && self.env.kname(*g) == n);
        let is_true = |t: &Term| named(t, "true") || self.is_true(t);
        let is_false = |t: &Term| named(t, "false") || self.is_false(t);
        (is_false(a) && is_true(b)) || (is_true(a) && is_false(b))
    }

    /// `t` is a proposition by its form: an equation, an implication, an
    /// existential, false, or a definition whose body is one (`not`,
    /// `and`, `or`, `all`, `bit`, ..).
    fn prop_shaped(&self, t: &Term, depth: u32) -> bool {
        let Node::App(g, _) = t.node() else { return false };
        // (`a in b` too: the prelude's `in_prop`)
        if *g == self.s.eq || *g == self.env.builtins.imp || *g == self.s.ex || is(*g, self.s.in_) || self.is_false(t) || self.is_true(t) {
            return true;
        }
        if self.env.ksym("false") == Some(*g) {
            return true;
        }
        if depth == 0 {
            return false;
        }
        match &self.env.syms[*g as usize].kind {
            SymKind::Defined { body, .. } => self.prop_shaped(body, depth - 1),
            _ => false,
        }
    }

    /// `k in d`, when decided (k a literal, d a finite set of literals).
    fn key_in(&self, k: &Term, d: &Term) -> Option<bool> {
        // (a word of the domain's width: an address in bits(64))
        if let Node::App(b, x) = d.node() {
            if self.env.ksym("bits") == Some(*b) && x.len() == 1 {
                if let Node::Nat(n) = x[0].node() {
                    if n.to_u64().is_some_and(|n| self.bits_term(k, n)) {
                        return Some(true);
                    }
                }
            }
        }
        let r = self.prop(&Term::app(self.s.in_?, vec![k.clone(), d.clone()]), Pol::Other);
        if self.is_true(&r) {
            Some(true)
        } else if self.is_false(&r) {
            Some(false)
        } else {
            None
        }
    }

    /// `x` has no pair with first element k (a record without the field k):
    /// by its construction, or by a known `dom(x) = D` without k
    /// (`dom_lacks`, core/records.core).
    fn lacks(&self, x: &Term, k: &Term) -> bool {
        if self.known_doms.borrow().iter().any(|(t, d)| t == x && self.key_in(k, d) == Some(false)) {
            return true;
        }
        let Node::App(g, b) = x.node() else { return false };
        match self.env.kname(*g) {
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
        // a proposition: in univ(0) (the prelude's `prop_univ`) and so in
        // every universe
        let literal_univ = matches!(set.node(), Node::App(_, ub) if matches!(ub.first().map(|n| n.node()), Some(Node::Nat(_))));
        if literal_univ && self.prop_shaped(x, 4) && self.env.axioms.iter().any(|(n, _)| n == "prop_univ") {
            return Some(self.tt());
        }
        // in a goal: a member by the path (before the strengthening below
        // takes it apart)
        if let (Pol::Goal, Node::App(_, ub)) = (pol, set.node()) {
            if let Some(Node::Nat(u)) = ub.first().map(|n| n.node()) {
                if let Some(u) = u.to_u64() {
                    if self.known(x, |k| k == Ty::Univ(u)) {
                        return Some(self.tt());
                    }
                }
            }
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
                // parts of a record: subsets (`restrict_univ`, `ghost_part_univ`)
                if (name == "restrict" || name == "ghost_part") && args.len() == 2 {
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
                    let set = self.env.kname(*o);
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
                if self.env.ksym("bits") == Some(*o) {
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

    /// In the goal (strengthening): updates of the same base `b` at
    /// different sets of literal keys are equal if they agree at every key,
    /// b is a function and each key updated on one side only is in dom(b)
    /// (then both sides are functions on dom(b) and the keys of both sides,
    /// agreeing everywhere: `fn_update_fun`, `fn_update_dom`, `rec_ext`).
    fn update_chains_goal(&self, x: &Term, y: &Term) -> Option<Term> {
        self.update_chains_goal_b(x, y, false)
    }

    /// `update_chains_goal`; with `bare`, also updates of b equal to b
    /// itself (`fn_update_same`).
    fn update_chains_goal_b(&self, x: &Term, y: &Term, bare: bool) -> Option<Term> {
        let s = &self.s;
        let (x, y) = (self.term(x), self.term(y));
        let chain = |t: &Term| -> (Term, Vec<Term>) {
            let mut keys = Vec::new();
            let mut b = t.clone();
            while let Node::App(g, a) = b.node() {
                if !is(*g, s.fn_update) || !matches!(a[1].node(), Node::Bytes(_) | Node::Nat(_)) {
                    break;
                }
                if !keys.contains(&a[1]) {
                    keys.push(a[1].clone());
                }
                b = a[0].clone();
            }
            (b, keys)
        };
        let ((bx, kx), (by, ky)) = (chain(&x), chain(&y));
        // (both sides updates: `m = fn_update(m, k, v)` stays a literal, which
        // the path may have)
        if (kx.is_empty() && ky.is_empty()) || (!bare && (kx.is_empty() || ky.is_empty())) || bx != by {
            return None;
        }
        let only: Vec<&Term> = kx.iter().filter(|k| !ky.contains(k)).chain(ky.iter().filter(|k| !kx.contains(k))).collect();
        if only.is_empty() {
            return None;
        }
        let is_fun = self.env.ksym("is_fun")?;
        let dom = self.env.ksym("dom")?;
        let (appf, in_) = (s.app?, s.in_?);
        let app = |r: &Term, k: &Term| self.term(&Term::app(appf, vec![r.clone(), k.clone()]));
        let mut r = self.prop(&Term::app(is_fun, vec![bx.clone()]), Pol::Goal);
        for k in &only {
            let d = Term::app(dom, vec![bx.clone()]);
            r = self.and(r, self.prop(&Term::app(in_, vec![(*k).clone(), d]), Pol::Goal));
        }
        for k in kx.iter().chain(ky.iter().filter(|k| !kx.contains(k))) {
            r = self.and(r, self.eq(&app(&x, k), &app(&y, k)));
        }
        Some(r)
    }

    /// `update_chains_goal` (also with a bare base) on the equations among
    /// the goal's top-level conjuncts that are not literals of the path.
    fn chain_eqs_goal(&self, g: &Term, lits: &[Term]) -> Term {
        match g.node() {
            Node::App(f, a) if is(*f, self.s.and) => {
                let (x, y) = (self.chain_eqs_goal(&a[0], lits), self.chain_eqs_goal(&a[1], lits));
                if x.ptr_eq(&a[0]) && y.ptr_eq(&a[1]) {
                    return g.clone();
                }
                self.and(x, y)
            }
            Node::App(f, a) if *f == self.s.eq => {
                if lits.iter().any(|l| l == g || matches!(l.node(), Node::App(e, b) if *e == self.s.eq && b[0] == a[1] && b[1] == a[0])) {
                    return g.clone();
                }
                if let Some(r) = self.update_chains_goal_b(&a[0], &a[1], true) {
                    return r;
                }
                // records of a record type the path gives one side: equal if
                // the other is of it too and they agree at every key (`rec_ext`)
                for (x, y) in [(&a[0], &a[1]), (&a[1], &a[0])] {
                    for ty in self.types_of(lits, y, 0) {
                        let Some(rt) = self.rec_type(&ty) else { continue };
                        let Some(keys) = self.key_list(&rt.keys) else { continue };
                        let (appf, in_) = (self.s.app.expect("app"), self.s.in_.expect("in"));
                        let mut r = self.prop(&Term::app(in_, vec![x.clone(), ty.clone()]), Pol::Goal);
                        for k in &keys {
                            let (u, w) = (self.term(&Term::app(appf, vec![x.clone(), k.clone()])), self.term(&Term::app(appf, vec![y.clone(), k.clone()])));
                            r = self.and(r, self.eq(&u, &w));
                        }
                        return r;
                    }
                }
                g.clone()
            }
            _ => g.clone(),
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
        // updates of the same base at the same literal keys (in any order,
        // repeated or not): equal iff they agree at each key (elsewhere both
        // are the base). (Not for different key sets: a key updated on one
        // side only adds a pair the base may lack.)
        let chain = |t: &Term| -> (Term, Vec<Term>) {
            let mut keys = Vec::new();
            let mut b = t.clone();
            while let Node::App(g, a) = b.node() {
                if !is(*g, s.fn_update) || !matches!(a[1].node(), Node::Bytes(_) | Node::Nat(_)) {
                    break;
                }
                keys.push(a[1].clone());
                b = a[0].clone();
            }
            (b, keys)
        };
        let ((bx, kx), (by, ky)) = (chain(&x), chain(&y));
        if !kx.is_empty() && bx == by && kx.iter().all(|k| ky.contains(k)) && ky.iter().all(|k| kx.contains(k)) {
            let mut keys: Vec<Term> = Vec::new();
            for k in kx {
                if !keys.contains(&k) {
                    keys.push(k);
                }
            }
            let app = |r: &Term, k: &Term| self.term(&Term::app(s.app.expect("app"), vec![r.clone(), k.clone()]));
            let mut r = self.tt();
            for k in &keys {
                r = self.and(r, self.eq(&app(&x, k), &app(&y, k)));
            }
            return r;
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
        // a member of a set that has one: `ex x. x in bits(n)` (0; n a
        // natural -- bits of a negative width is empty), omega, int, bool
        // (false)
        if let Node::App(i, ab) = body.node() {
            if is(*i, self.s.in_) && matches!(ab[0].node(), Node::BVar(0)) && !has_bvar(self.env, &ab[1], 0) {
                if let Node::App(set, sa) = ab[1].node() {
                    let name = self.env.kname(*set);
                    if (name == "bits" && sa.len() == 1 && (matches!(sa[0].node(), Node::Nat(_)) || self.nat_term(&sa[0])))
                        || (matches!(name, "omega" | "int" | "bool") && sa.is_empty())
                    {
                        return self.tt();
                    }
                }
            }
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
                            // (eager: still a goal, its runs now closed may take their outcomes)
                            return self.prop(&r, if goal && self.eager_runs.get() { Pol::Goal } else { Pol::Other });
                        }
                    }
                }
            }
        }
        // in a goal, a run the path knows the outcome of: `ex x. runs(P, s,
        // x) && K(x)` with `runs(P, s, o)` a literal: K(o) (a witness; for a
        // goal too large for the witness search)
        if goal && self.eager_runs.get() {
            // (the outcome's pattern: x is BVar(0), outer bound variables
            // wildcards -- their own `ex` binds them in turn)
            fn bind(env: &Env, pat: &Term, val: &Term) -> Option<Option<Term>> {
                match pat.node() {
                    Node::BVar(0) => Some(Some(val.clone())),
                    Node::BVar(_) => Some(None),
                    _ if !has_bvar_any(env, pat, 0) => (lower(env, pat, 0) == *val).then_some(None),
                    Node::App(f, ps) => match val.node() {
                        Node::App(g, vs) if f == g && ps.len() == vs.len() && env.syms[*f as usize].binders.iter().all(|b| *b == 0) => {
                            let mut out = None;
                            for (p, v) in ps.iter().zip(vs) {
                                if let Some(b) = bind(env, p, v)? {
                                    if out.as_ref().is_some_and(|o| *o != b) {
                                        return None;
                                    }
                                    out = Some(b);
                                }
                            }
                            Some(out)
                        }
                        _ => None,
                    },
                    _ => None,
                }
            }
            for c in &cs {
                if let Node::App(r, ab) = c.node() {
                    if is(*r, self.s.runs) && ab.len() == 3 && has_bvar(self.env, &ab[2], 0) && !has_bvar_any(self.env, &ab[0], 0) && !has_bvar_any(self.env, &ab[1], 0) {
                        let (p, st) = (lower(self.env, &ab[0], 0), lower(self.env, &ab[1], 0));
                        let known = self.runs_facts.borrow().iter().find_map(|l| match l.node() {
                            Node::App(_, lb) if lb[0] == p && lb[1] == st => bind(self.env, &ab[2], &lb[2]).flatten(),
                            _ => None,
                        });
                        if std::env::var("WITNESS_DEBUG").is_ok() {
                            let pr = crate::syntax::Printer::new(self.env);
                            eprintln!("witness: eager {} for {} ({} runs facts)", known.is_some(), pr.term(&p).chars().take(80).collect::<String>(), self.runs_facts.borrow().len());
                        }
                        if let Some(o) = known {
                            return self.prop(&inst_k(self.env, body, &[o]), Pol::Goal);
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
            // x only through projections, when that decides it (a choice of
            // several values that exists: `any (bool, bool)`); otherwise
            // kept, so facts do not multiply
            // (the goal's steps: equivalences, kept only when decided)
            // (as a fact: no goal-only strengthening of a run -- `ex x.
            // runs(..x) && K(x)` read as K(o) -- a stronger statement found
            // false says nothing of this one; without a run, none applies)
            if let Some(nb) = self.proj_split(body, 0) {
                let mode = !mentions_sym(&nb, self.s.runs);
                let inner = self.ex(&self.prop(&nb, Pol::Other), mode);
                let r = self.ex(&inner, mode);
                if self.is_true(&r) || self.is_false(&r) {
                    return r;
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
/// a let's value copied into its body: at most this many nodes (as a tree)
const LET_SMALL: usize = 32;

thread_local! {
    /// every let reduced (the second attempt at a goal)
    static LET_EAGER: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// the local constants of the lets simp is in (above any variable of a
/// goal, below the paths' fresh ones)
const LET_FRESH0: u32 = 3_000_000_000;

/// whether the symbol f occurs in t (its shared parts looked at once)
fn has_sym(env: &Env, t: &Term, f: SymId) -> bool {
    fn go(t: &Term, f: SymId, seen: &mut std::collections::HashSet<usize>) -> bool {
        let Node::App(g, a) = t.node() else {
            return matches!(t.node(), Node::Var(_, a) if a.iter().any(|x| go(x, f, seen)));
        };
        if *g == f {
            return true;
        }
        if a.is_empty() || !seen.insert(t.node() as *const Node as usize) {
            return false;
        }
        a.iter().any(|x| go(x, f, seen))
    }
    let _ = env;
    go(t, f, &mut std::collections::HashSet::new())
}

/// the occurrences of the variable c in t, up to cap
fn var_uses(t: &Term, c: crate::term::VarId, cap: usize) -> usize {
    fn go(t: &Term, c: crate::term::VarId, cap: usize, n: &mut usize) {
        if *n >= cap || !t.may_contain_var(c) {
            return;
        }
        match t.node() {
            Node::Var(v, a) => {
                if *v == c {
                    *n += 1;
                }
                a.iter().for_each(|x| go(x, c, cap, n));
            }
            Node::App(_, a) => a.iter().for_each(|x| go(x, c, cap, n)),
            _ => {}
        }
    }
    let mut n = 0;
    go(t, c, cap, &mut n);
    n
}

/// t with the variable c a bound variable (the body of a binder of one)
fn let_abstract(env: &Env, t: &Term, c: crate::term::VarId) -> Term {
    fn go(env: &Env, t: &Term, c: crate::term::VarId, d: u32) -> Term {
        if !t.may_contain_var(c) {
            return t.clone();
        }
        match t.node() {
            Node::Var(v, a) if *v == c && a.is_empty() => Term::bvar(d),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| go(env, x, c, d)).collect()),
            Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| go(env, x, c, d + env.binders_fn()(*s, i))).collect()),
            _ => t.clone(),
        }
    }
    go(env, &t.shift(1, 0, &env.binders_fn()), c, 0)
}

/// whether a let's value v is copied into its body: v small (or every let
/// reduced)
fn let_inline(v: &Term) -> bool {
    fn size(t: &Term, cap: usize, n: &mut usize) {
        *n += 1;
        if *n > cap {
            return;
        }
        if let Node::Var(_, a) | Node::App(_, a) = t.node() {
            for x in a.iter() {
                size(x, cap, n);
                if *n > cap {
                    return;
                }
            }
        }
    }
    if LET_EAGER.with(|e| e.get()) {
        return true;
    }
    let mut n = 0;
    size(v, LET_SMALL, &mut n);
    n <= LET_SMALL
}

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
/// `t` has a loose bound variable (any index >= `depth`).
fn has_bvar_any(env: &Env, t: &Term, depth: u32) -> bool {
    match t.node() {
        Node::BVar(j) => *j >= depth,
        Node::App(f, a) => a.iter().enumerate().any(|(k, x)| has_bvar_any(env, x, depth + env.syms[*f as usize].binders[k])),
        Node::Var(_, a) => a.iter().any(|x| has_bvar_any(env, x, depth)),
        _ => false,
    }
}

/// The condition of an `ite` in `t` that mentions no bound variable (a
/// case split for a goal computing a branch: `ok(w, ite(c, 1, 0))`).
fn open_ite(env: &Env, ite: Option<SymId>, t: &Term) -> Option<Term> {
    let Node::App(f, a) = t.node() else { return None };
    if is(*f, ite) && a.len() == 3 && !has_bvar_any(env, &a[0], 0) {
        return Some(a[0].clone());
    }
    a.iter().enumerate().filter(|(k, _)| env.syms[*f as usize].binders[*k] == 0).find_map(|(_, x)| open_ite(env, ite, x))
}

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
        let wr = self.env.ksym("while_rel");
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
        !self.const_choice(&ds)
    }

    /// The disjuncts `ds` choose among constants for one variable, or one
    /// projection of a variable (`fst(snd(u)) = false || … = true`, a flag
    /// of an open choice): such a disjunction stays one literal.
    fn const_choice(&self, ds: &[Term]) -> bool {
        fn proj_of_var(sp: &Simp, t: &Term) -> bool {
            match t.node() {
                Node::Var(_, va) => va.is_empty(),
                Node::App(g, b) if b.len() == 1 && (is(*g, sp.s.fst) || is(*g, sp.s.snd)) => proj_of_var(sp, &b[0]),
                _ => false,
            }
        }
        let choice = |d: &Term| -> Option<Term> {
            let Node::App(e, ab) = d.node() else { return None };
            if *e != self.s.eq {
                return None;
            }
            let konst = |c: &Term| self.is_true(c) || self.is_false(c);
            if proj_of_var(self, &ab[0]) && konst(&ab[1]) {
                Some(ab[0].clone())
            } else if proj_of_var(self, &ab[1]) && konst(&ab[0]) {
                Some(ab[1].clone())
            } else {
                None
            }
        };
        match ds.first().and_then(choice) {
            Some(v0) => ds.iter().all(|d| choice(d).as_ref() == Some(&v0)),
            None => false,
        }
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
                if self.const_choice(&ds) {
                    return Some(vec![Path { vars: vec![], lits: vec![t.clone()], done: vec![] }]);
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
            let before = (self.nats.borrow().clone(), self.bounds.borrow().clone());
            self.set_nats(&p.lits);
            if *self.nats.borrow() != before.0 || *self.bounds.borrow() != before.1 {
                dirty.iter_mut().for_each(|d| *d = true);
            }
            if rounds == 5000 && std::env::var("SIMP_DEBUG").is_ok() {
                let pr = crate::syntax::Printer::new(self.env);
                for l in &p.lits {
                    eprintln!("simp: settle loops on {}", pr.term(l).chars().take(3000).collect::<String>());
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
        // (an equation determines its variables only through injective
        // constructors: not `x mod 2^5 = c`)
        fn injective(sp: &Simp, p: &Term, vars: &[crate::term::VarId]) -> bool {
            match p.node() {
                Node::Var(..) => true,
                Node::App(f, a) => {
                    if !vars.iter().any(|v| has_var(p, *v)) {
                        return true;
                    }
                    let name = sp.env.kname(*f);
                    let ctor = [sp.s.pair, sp.s.tag, sp.s.ok, sp.s.exc, sp.s.diverge, sp.s.some].iter().any(|c| is(*f, *c)) || name == "fn_update" || name == "insert";
                    ctor && a.iter().all(|x| injective(sp, x, vars))
                }
                _ => true,
            }
        }
        loop {
            let n = binds.len();
            for l in glits {
                let Node::App(e, ab) = l.node() else { continue };
                if *e != self.s.eq {
                    continue;
                }
                let (a, b) = (sub(&ab[0], binds), sub(&ab[1], binds));
                for (p, t) in [(&a, &b), (&b, &a)] {
                    if unbound(p, binds) && !unbound(t, binds) && injective(self, p, vars) {
                        let mut bs = binds.clone();
                        if pmatch(self.env, p, &self.term(t), vars, &mut bs) {
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
                    // (only for a variable occurring nowhere but under
                    // projections: elsewhere its value is to be matched)
                    if glits.iter().any(|l| self.occurs_bare(&sub(l, binds), *v)) {
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

    /// The variable v occurs in t other than under projections (fst, snd,
    /// out_state, out_value).
    fn occurs_bare(&self, t: &Term, v: crate::term::VarId) -> bool {
        let s = &self.s;
        match t.node() {
            Node::Var(w, a) => (*w == v && a.is_empty()) || a.iter().any(|x| self.occurs_bare(x, v)),
            Node::App(f, a) => {
                let proj = [s.fst, s.snd, s.out_state, s.out_value].iter().any(|p| is(*f, *p));
                if proj && a.len() == 1 {
                    // a chain of projections ending at v: not bare
                    let mut x = &a[0];
                    loop {
                        match x.node() {
                            Node::Var(w, b) if *w == v && b.is_empty() => return false,
                            Node::App(g, b) if b.len() == 1 && [s.fst, s.snd, s.out_state, s.out_value].iter().any(|p| is(*g, *p)) => x = &b[0],
                            _ => break,
                        }
                    }
                }
                a.iter().any(|x| self.occurs_bare(x, v))
            }
            _ => false,
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
        let ok = lg.tautology(self.env, lits, &want).is_ok() || lg.arith(self.env, lits, &want).is_ok();
        if !ok && std::env::var("WITNESS_DEBUG").is_ok() {
            let pr = crate::syntax::Printer::new(self.env);
            let mut ws = Vec::new();
            self.conjuncts(&want, &mut ws);
            for w in ws {
                if lg.tautology(self.env, lits, &w).is_err() && lg.arith(self.env, lits, &w).is_err() {
                    let t = pr.term(&w); if std::env::var("WITNESS_FULL").is_ok() { eprintln!("witness: not shown: {}", t); } else { eprintln!("witness: not shown: {} ... {}", t.chars().take(200).collect::<String>(), t.chars().rev().take(3000).collect::<String>().chars().rev().collect::<String>()); }
                }
            }
            eprintln!("witness: --");
        }
        ok
    }

    fn witnessed(&self, lits: &[Term], goal: &Term, fresh: &mut u32, lg: &Logic) -> bool {
        let mut ds = Vec::new();
        self.disjuncts(goal, &mut ds);
        for d in ds {
            // (no held disjunctions in the goal: matching needs its
            // alternatives open)
            self.no_hold.set(true);
            self.eager_tried.set(false);
            let mut gps = self.paths(&d, fresh);
            // (too many: the runs the path knows the outcomes of taken as
            // witnesses first, which prunes the program's alternatives)
            if gps.is_none() {
                self.set_nats(lits);
                self.eager_runs.set(true);
                self.memo.borrow_mut().clear();
                let d2 = self.prop(&d, Pol::Goal);
                if std::env::var("WITNESS_EAGER").is_ok() {
                    eprintln!("witness: eager goal {}", crate::syntax::Printer::new(self.env).term(&d2));
                }
                self.eager_runs.set(false);
                self.memo.borrow_mut().clear();
                gps = self.paths(&d2, fresh);
                self.eager_tried.set(true);
            }
            self.no_hold.set(false);
            if std::env::var("WITNESS_DEBUG").is_ok() {
                eprintln!("witness: goal disjunct: {} paths", gps.as_ref().map_or(usize::MAX, |g| g.len()));
            }
            let Some(gps) = gps else { continue };
            // (the typing of the path, not of the goal's paths)
            self.set_nats(lits);
            for gp in gps {
                if gp.vars.is_empty() {
                    // (nothing to bind: holds if its literals do -- a goal
                    // the eager step above reduced to the path's facts)
                    if self.eager_tried.get() && self.witness_ok(lits, &gp.lits, &[], lg) {
                        return true;
                    }
                    continue;
                }
                // the bindings from matching goal literals with path
                // literals, each goal literal matched or not (a search,
                // matches first; at most WITNESS_TRIES complete ones tried)
                let witness_tries: usize = std::env::var("WITNESS_TRIES").ok().and_then(|v| v.parse().ok()).unwrap_or(64);
                #[allow(non_snake_case)]
                let WITNESS_TRIES = witness_tries;
                let (mut tries, mut nodes) = (0, 0);
                // (each entry: the next literal, the bindings, how many there
                // were when this pass over the literals began)
                let mut stack: Vec<(usize, Vec<(crate::term::VarId, Term)>, usize)> = vec![(0, Vec::new(), 0)];
                let debug = std::env::var("WITNESS_DEBUG").is_ok();
                let mut best: Vec<(crate::term::VarId, Term)> = Vec::new();
                while let Some((i, mut binds, start)) = stack.pop() {
                    nodes += 1;
                    if nodes > 64 * WITNESS_TRIES {
                        break;
                    }
                    self.solve_goal_eqs(&gp.lits, &gp.vars, &mut binds);
                    if debug && binds.len() > best.len() {
                        best = binds.clone();
                    }
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
                        // another pass, if this one bound more: literals
                        // passed over may match now
                        if binds.len() > start {
                            let n = binds.len();
                            stack.push((0, binds, n));
                            continue;
                        }
                        // nothing binds the rest: a variable only typed
                        // `x in bits(n)` / `x in omega` (a value left open,
                        // e.g. an uninitialized local) takes 0, the rest may
                        // follow from it (checked as any witness)
                        let mut more = binds.clone();
                        for l in &gp.lits {
                            if let Node::App(m, ab) = l.node() {
                                if !is(*m, self.s.in_) || ab.len() != 2 {
                                    continue;
                                }
                                if let (Node::Var(v, va), Node::App(set, sa)) = (ab[0].node(), ab[1].node()) {
                                    let zero_in = is(*set, self.s.omega) || (self.env.ksym("bits") == Some(*set) && sa.len() == 1);
                                    if va.is_empty() && zero_in && gp.vars.contains(v) && !more.iter().any(|(w, _)| w == v) {
                                        more.push((*v, Term::nat(crate::nat::Nat::zero())));
                                    }
                                }
                            }
                        }
                        if more.len() > binds.len() {
                            let n = more.len();
                            stack.push((0, more, n));
                        }
                        continue;
                    }
                    // (pushed last: tried first)
                    stack.push((i + 1, binds.clone(), start));
                    // (the literal with the bindings so far, simplified:
                    // bound parts compute, as the path's literals did)
                    let pat = if binds.is_empty() {
                        gp.lits[i].clone()
                    } else {
                        let bf = self.env.binders_fn();
                        let mut t = gp.lits[i].clone();
                        for (v, x) in &binds {
                            t = t.subst_var(*v, x, &bf);
                        }
                        self.prop(&t, Pol::Other)
                    };
                    // (a typing `x in S` of an unbound x does not bind it:
                    // checked once x is bound by something else)
                    let typing = matches!(pat.node(), Node::App(m, ab) if is(*m, self.s.in_) && matches!(ab[0].node(), Node::Var(v, a) if a.is_empty() && gp.vars.contains(v)));
                    if typing {
                        continue;
                    }
                    for pl in lits.iter().rev() {
                        let mut b = binds.clone();
                        if pmatch(self.env, &pat, pl, &gp.vars, &mut b) && b.len() > binds.len() {
                            stack.push((i + 1, b, start));
                        } else if debug && std::env::var("WITNESS_HEAD").is_ok_and(|h| matches!((pat.node(), pl.node()), (Node::App(f, _), Node::App(g, _)) if f == g && self.env.kname(*f) == h)) {
                            let pr = crate::syntax::Printer::new(self.env);
                            eprintln!("witness: no match\n  pattern {}\n  literal {}", pr.term(&pat), pr.term(pl));
                        }
                    }
                }
                if debug {
                    // the goal path's literals still unbound in the best
                    // partial binding
                    let pr = crate::syntax::Printer::new(self.env);
                    let bf = self.env.binders_fn();
                    eprintln!("witness: path of {} vars, best binds {}", gp.vars.len(), best.len());
                    for l in &gp.lits {
                        let mut t = l.clone();
                        for (v, x) in &best {
                            t = t.subst_var(*v, x, &bf);
                        }
                        if gp.vars.iter().any(|v| has_var(&t, *v)) {
                            eprintln!("witness:   unbound in: {}", pr.term(&t).chars().take(3000).collect::<String>());
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
                if pmatch(self.env, c, pl, &vs, &mut bd) {
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
    env: &Env,
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
        if pmatch(env, &hyps[i], pl, vs, &mut b) {
            any = true;
            instances(env, hyps, i + 1, lits, vs, b, open.clone(), out);
        }
    }
    if !any {
        let mut o = open;
        o.push(i);
        instances(env, hyps, i + 1, lits, vs, binds, o, out);
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
        let name = |t: &Term| match t.node() {
            Node::App(h, _) => self.env.kname(*h).to_string(),
            _ => String::new(),
        };
        // the domain of a function the path types: a record type's keys,
        // fn_space(A, B)'s A (and so it is a function)
        let domain = |b: &Term| -> Option<Term> {
            self.types_of(lits, b, 3).into_iter().find_map(|ty| {
                if let Some(rt) = self.rec_type(&ty) {
                    return Some(rt.keys);
                }
                match ty.node() {
                    Node::App(fs, fa) if self.env.ksym("fn_space") == Some(*fs) && fa.len() == 2 => Some(fa[0].clone()),
                    _ => None,
                }
            })
        };
        if self.env.ksym("is_fun") == Some(*i) && ab.len() == 1 {
            return domain(&ab[0]).is_some();
        }
        // `dom(b) = A` for b of a type with the domain A
        if *i == self.s.eq && name(&ab[0]) == "dom" {
            let Node::App(_, db) = ab[0].node() else { unreachable!() };
            return domain(&db[0]).is_some_and(|d| d == ab[1]);
        }
        // `x = false || x = true` (x in bool, unfolded): x of the type `bool`
        if is(*i, self.s.or) {
            if let (Node::App(e1, x), Node::App(e2, y)) = (ab[0].node(), ab[1].node()) {
                if *e1 == self.s.eq && *e2 == self.s.eq && x[0] == y[0] && self.is_bool_pair(&x[1], &y[1]) {
                    return self.types_of(lits, &x[0], 3).iter().any(|t| name(t) == "bool");
                }
            }
        }
        if !is(*i, self.s.in_) {
            return false;
        }
        // an open flag (`x = false || x = true` on the path) in univ(u):
        // false and true are (the prelude's `prop_univ`: in univ(0))
        if let Node::App(u, ub) = ab[1].node() {
            if is(*u, self.s.univ) && matches!(ub[0].node(), Node::Nat(_)) && self.env.axioms.iter().any(|(n, _)| n == "prop_univ") {
                let choice = lits.iter().any(|l| {
                    let mut ds = Vec::new();
                    self.disjuncts(l, &mut ds);
                    ds.len() == 2 && self.const_choice(&ds) && ds.iter().all(|d| matches!(d.node(), Node::App(e, x) if *e == self.s.eq && (x[0] == ab[0] || x[1] == ab[0])))
                });
                if choice {
                    return true;
                }
            }
        }
        if name(&ab[1]) == "dom" {
            let Node::App(_, db) = ab[1].node() else { unreachable!() };
            if let Some(d) = domain(&db[0]) {
                if self.key_in(&ab[0], &d) == Some(true) {
                    return true;
                }
            }
        }
        self.set_nats(lits);
        let by_form = match ab[1].node() {
            Node::App(o, x) if x.is_empty() && is(*o, self.s.omega) => self.nat_term(&ab[0]),
            Node::App(o, x) if x.is_empty() && self.env.ksym("int") == Some(*o) => self.int_term(&ab[0]),
            Node::App(b, x) if self.env.ksym("bits") == Some(*b) && x.len() == 1 => match x[0].node() {
                Node::Nat(k) => k.to_u64().is_some_and(|k| self.bits_term(&ab[0], k)),
                _ => false,
            },
            _ => false,
        };
        // (or a field of a record of a known record type)
        // (or stores to bytes: bytes)
        by_form
            || matches!(ab[0].node(), Node::App(a, _) if is(*a, self.s.app) || self.env.ksym("x86_64_linux.store_le") == Some(*a) || is(*a, self.s.fn_update))
                && self.types_of(lits, &ab[0], 3).contains(&ab[1])
    }

    /// The types the path gives `t`: its literals `t in T`, and for a field
    /// `app(r, k)` the type of the field k in a record type of r
    /// (`depth` levels of fields).
    fn types_of(&self, lits: &[Term], t: &Term, depth: u32) -> Vec<Term> {
        let mut out: Vec<Term> = lits
            .iter()
            .filter_map(|l| match l.node() {
                Node::App(i, ab) if is(*i, self.s.in_) && ab[0] == *t => Some(ab[1].clone()),
                _ => None,
            })
            .collect();
        if depth > 0 {
            // stores to bytes: bytes (x86.store_typed; a byte at a 64-bit
            // key: fn_update in the function space)
            if let Node::App(st, sa) = t.node() {
                let byte_update = is(*st, self.s.fn_update) && sa.len() == 3 && self.bits_term(&sa[1], 64) && self.bits_term(&sa[2], 8);
                if (self.env.ksym("x86_64_linux.store_le") == Some(*st) && sa.len() == 4) || byte_update {
                    for r in self.types_of(lits, &sa[0], depth) {
                        if let Node::App(fs, fa) = r.node() {
                            let bits_k = |x: &Term, k: u64| matches!(x.node(), Node::App(b, ba) if self.env.ksym("bits") == Some(*b) && ba.len() == 1 && matches!(ba[0].node(), Node::Nat(n) if n.to_u64() == Some(k)));
                            if self.env.ksym("fn_space") == Some(*fs) && fa.len() == 2 && bits_k(&fa[0], 64) && bits_k(&fa[1], 8) && !out.contains(&r) {
                                out.push(r.clone());
                                // (a set of pairs of naturals: in univ(1))
                                if let Some(u) = self.s.univ {
                                    out.push(Term::app(u, vec![Term::nat(crate::nat::Nat::from_u64(1))]));
                                }
                            }
                        }
                    }
                }
            }
            if let Node::App(a, ab) = t.node() {
                if is(*a, self.s.app) {
                    for r in self.types_of(lits, &ab[0], depth - 1) {
                        if let Some(rt) = self.rec_type(&r) {
                            if let Some((_, ty)) = rt.fields.iter().find(|(k, _)| *k == ab[1]) {
                                out.push(ty.clone());
                            }
                        }
                        // an argument of a function in fn_space(A, B) (`fn_space_app`)
                        if let Node::App(fs, fa) = r.node() {
                            if self.env.ksym("fn_space") == Some(*fs) && fa.len() == 2 && self.key_in(&ab[1], &fa[0]) == Some(true) {
                                out.push(fa[1].clone());
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// A record type: `set_select(powerset(cart(K, univ(u))), x. P(x))`
    /// with P a conjunction of `is_fun(x)`, `dom(x) = K` and field types
    /// `app(x, "k") in T` (T closed), possibly a constant defined as one
    /// (`x86_64_linux.Machine`).
    fn rec_type(&self, set: &Term) -> Option<RecType> {
        let name = |g: SymId| self.env.kname(g);
        let mut set = set.clone();
        if let Node::App(g, a) = set.node() {
            if a.is_empty() {
                if let SymKind::Defined { params, body } = &self.env.syms[*g as usize].kind {
                    if params.is_empty() {
                        set = body.clone();
                    }
                }
            }
        }
        let Node::App(sel, sb) = set.node() else { return None };
        if !is(*sel, self.s.set_select) {
            return None;
        }
        let Node::App(pw, pa) = sb[0].node() else { return None };
        let Node::App(ca, cb) = pa.first()?.node() else { return None };
        let Node::App(un, ub) = cb.get(1)?.node() else { return None };
        if name(*pw) != "powerset" || name(*ca) != "cart" || !is(*un, self.s.univ) {
            return None;
        }
        let u = ub.first()?.clone();
        let keys = cb[0].clone();
        let mut cs = Vec::new();
        self.conjuncts(&sb[1], &mut cs);
        let x0 = |t: &Term| matches!(t.node(), Node::BVar(0));
        let mut fields = Vec::new();
        let (mut fun, mut dom) = (false, false);
        for c in cs {
            let Node::App(h, b) = c.node() else { return None };
            if name(*h) == "is_fun" && x0(&b[0]) {
                fun = true;
            } else if *h == self.s.eq && matches!(b[0].node(), Node::App(d, db) if name(*d) == "dom" && x0(&db[0])) && b[1] == keys {
                dom = true;
            } else if is(*h, self.s.in_) && !has_bvar(self.env, &b[1], 0) && matches!(b[0].node(), Node::App(ap, xb) if is(*ap, self.s.app) && x0(&xb[0]) && matches!(xb[1].node(), Node::Bytes(_) | Node::Nat(_))) {
                let Node::App(_, xb) = b[0].node() else { unreachable!() };
                fields.push((xb[1].clone(), lower(self.env, &b[1], 0)));
            } else {
                return None;
            }
        }
        if !fun || !dom {
            return None;
        }
        Some(RecType { u, keys, fields })
    }

    /// In the goal (strengthening): `x in T` for x updates of a base b
    /// (literal keys): for a record type T, b in T (or, b = `empty`, every
    /// key updated), the updated keys T's, each value of its field's type,
    /// and `w in univ(u)` for w the outermost record x is a field of (x
    /// itself at the top; its values, as fields of it, are then members);
    /// for `fn_space(A, B)`, b in it, the keys in A, the values in B.
    /// (By `rec_type_intro`, `fn_update_fd`, `dom_update`, `app_univ`,
    /// `fn_space_univ`'s argument: the update's pairs are b's or the new
    /// ones.)
    fn typed_goal(&self, x: &Term, set: &Term, outer: Option<&Term>) -> Option<Term> {
        let s = &self.s;
        let x = self.term(x);
        if self.known_mems.borrow().iter().any(|l| matches!(l.node(), Node::App(_, ab) if ab[0] == x && ab[1] == *set)) {
            return Some(self.tt());
        }
        let mut keys: Vec<Term> = Vec::new();
        let mut vals: Vec<Term> = Vec::new();
        let mut b = x.clone();
        while let Node::App(g, a) = b.node() {
            if !is(*g, s.fn_update) || !matches!(a[1].node(), Node::Bytes(_) | Node::Nat(_)) {
                break;
            }
            if !keys.contains(&a[1]) {
                keys.push(a[1].clone());
                vals.push(a[2].clone());
            }
            b = a[0].clone();
        }
        if keys.is_empty() {
            return None;
        }
        let in_ = s.in_?;
        let mem = |y: &Term, t: &Term, w: Option<&Term>| -> Term {
            self.typed_goal(y, t, w).unwrap_or_else(|| self.prop(&Term::app(in_, vec![y.clone(), t.clone()]), Pol::Goal))
        };
        if let Some(rt) = self.rec_type(set) {
            if !keys.iter().all(|k| self.key_in(k, &rt.keys) == Some(true)) {
                return None;
            }
            let base_empty = matches!(b.node(), Node::App(e, ea) if ea.is_empty() && self.env.ksym("empty") == Some(*e));
            let mut r = if base_empty {
                // every key updated (and only keys: checked above)
                let n = self.key_count(&rt.keys)?;
                if n != keys.len() || !rt.fields.iter().all(|(k, _)| keys.contains(k)) {
                    return None;
                }
                self.tt()
            } else {
                self.prop(&Term::app(in_, vec![b.clone(), set.clone()]), Pol::Goal)
            };
            let w = outer.unwrap_or(&x);
            for (k, v) in keys.iter().zip(&vals) {
                if let Some((_, ty)) = rt.fields.iter().find(|(fk, _)| fk == k) {
                    r = self.and(r, mem(v, ty, Some(w)));
                }
            }
            let univ = Term::app(s.univ?, vec![rt.u.clone()]);
            return Some(self.and(r, self.prop(&Term::app(in_, vec![w.clone(), univ]), Pol::Goal)));
        }
        let Node::App(fs, fa) = set.node() else { return None };
        if self.env.kname(*fs) != "fn_space" || fa.len() != 2 {
            return None;
        }
        let mut r = self.prop(&Term::app(in_, vec![b.clone(), set.clone()]), Pol::Goal);
        for (k, v) in keys.iter().zip(&vals) {
            r = self.and(r, self.prop(&Term::app(in_, vec![k.clone(), fa[0].clone()]), Pol::Goal));
            r = self.and(r, mem(v, &fa[1], None));
        }
        Some(r)
    }

    /// The elements of a finite set of literals (`insert(a, .. empty)`).
    fn key_list(&self, d: &Term) -> Option<Vec<Term>> {
        let mut out: Vec<Term> = Vec::new();
        let mut d = d.clone();
        loop {
            let next = {
                let Node::App(g, a) = d.node() else { return None };
                match self.env.kname(*g) {
                    "empty" if a.is_empty() => return Some(out),
                    "insert" if matches!(a[0].node(), Node::Bytes(_) | Node::Nat(_)) => {
                        if !out.contains(&a[0]) {
                            out.push(a[0].clone());
                        }
                        a[1].clone()
                    }
                    _ => return None,
                }
            };
            d = next;
        }
    }

    /// The number of elements of a finite set of distinct literals
    /// (`insert(a, insert(b, .. empty))`).
    fn key_count(&self, d: &Term) -> Option<usize> {
        let mut n = 0;
        let mut seen: Vec<&Term> = Vec::new();
        let mut d = d;
        loop {
            let Node::App(g, a) = d.node() else { return None };
            match self.env.kname(*g) {
                "empty" if a.is_empty() => return Some(n),
                "insert" => {
                    if !matches!(a[0].node(), Node::Bytes(_) | Node::Nat(_)) {
                        return None;
                    }
                    if !seen.contains(&&a[0]) {
                        seen.push(&a[0]);
                        n += 1;
                    }
                    d = &a[1];
                }
                _ => return None,
            }
        }
    }

    /// `t` is an instance of a literal `all xs. C` (C not an implication).
    fn instance_of_all(&self, lits: &[Term], t: &Term) -> bool {
        if self.instance_of_all_at(lits, t) {
            return true;
        }
        // (t universal, with hypotheses: its conclusion, its variables
        // fixed, is an instance: `all i. i in omega -> P(f(i))` from
        // `all a. P(a)`)
        let mut c = t.clone();
        let mut fresh = lits.iter().map(max_var).max().unwrap_or(0).max(max_var(t)) + 1;
        let mut opened = false;
        loop {
            match c.node() {
                Node::App(q, a) if *q == self.s.all => {
                    c = inst_k(self.env, &a[0], &[Term::var(fresh, vec![])]);
                    fresh += 1;
                }
                Node::App(q, a) if *q == self.s.imp => c = a[1].clone(),
                _ => break,
            }
            opened = true;
        }
        opened && self.instance_of_all_at(lits, &c)
    }

    fn instance_of_all_at(&self, lits: &[Term], t: &Term) -> bool {
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
                if !matches!(b.node(), Node::App(i, _) if *i == self.s.imp) && pmatch(self.env, &b, t, &vs, &mut Vec::new()) {
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
        // (the literals to match a rule's hypotheses against: also `t in
        // omega` for a word t, `t in bits(k)` -- words are naturals)
        let mut match_lits = p.lits.clone();
        if let (Some(in_), Some(omega)) = (self.s.in_, self.s.omega) {
            for l in &p.lits {
                if let Node::App(i, ab) = l.node() {
                    if is(*i, Some(in_)) && ab.len() == 2 && matches!(ab[1].node(), Node::App(b, _) if self.env.ksym("bits") == Some(*b)) {
                        let t = Term::app(in_, vec![ab[0].clone(), Term::app(omega, vec![])]);
                        if !match_lits.contains(&t) {
                            match_lits.push(t);
                        }
                    }
                }
            }
        }
        for l in &p.lits {
            let Some((vs, hyps, concl)) = self.rule(l, fresh) else { continue };
            let mut insts = Vec::new();
            // (goal-directed first: the conclusion matching a conjunct of
            // the goal binds its variables, the hypotheses then; a typing
            // hypothesis would otherwise bind a variable to any literal of
            // its type)
            if !matches!(concl.node(), Node::App(e, _) if *e == self.s.eq) {
                let mut gs = Vec::new();
                self.conjuncts(goal, &mut gs);
                // (also as simp reads them: the conclusion is in its forms)
                let normed: Vec<Term> = gs.iter().map(|u| self.prop(u, Pol::Other)).filter(|u| !gs.contains(u)).collect();
                gs.extend(normed);
                if std::env::var("SIMP_CHAIN").is_ok() {
                    let pr = crate::syntax::Printer::new(self.env);
                    for u in &gs {
                        if u.loose_depth(&bf) == 0 {
                            eprintln!("chain: goal {}", pr.term(u).chars().take(3000).collect::<String>());
                        }
                    }
                }
                for u in &gs {
                    let mut b = Vec::new();
                    if pmatch(self.env, &concl, u, &vs, &mut b) && !b.is_empty() {
                        instances(self.env, &hyps, 0, &match_lits, &vs, b, Vec::new(), &mut insts);
                    }
                }
            }
            // variables only in the conclusion `lhs = rhs`: from the terms
            let lhs = match concl.node() {
                Node::App(e, ab) if *e == self.s.eq => Some(ab[0].clone()),
                _ => None,
            };
            // (an equation: first where its left side occurs -- a typing
            // hypothesis binds its variable to any typed literal)
            if let Some(lhs) = &lhs {
                for u in &subs {
                    let mut b = Vec::new();
                    if pmatch(self.env, lhs, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                        instances(self.env, &hyps, 0, &match_lits, &vs, b, Vec::new(), &mut insts);
                    }
                }
            }
            instances(self.env, &hyps, 0, &match_lits, &vs, Vec::new(), Vec::new(), &mut insts);
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
                            pmatch(self.env, &h, l, &vs, &mut b).then_some(b)
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
                        if pmatch(self.env, lhs, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                            all_insts.push((b, open.clone()));
                        }
                    }
                } else {
                    // (otherwise from the goal: a conjunct the conclusion matches)
                    let mut gs = Vec::new();
                    self.conjuncts(goal, &mut gs);
                    for u in &gs {
                        let mut b = binds.clone();
                        if pmatch(self.env, &concl, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                            all_insts.push((b, open.clone()));
                        }
                    }
                }
                if all_insts.len() >= MAX_INSTANCES {
                    break;
                }
            }
            // a run's rule also at the goal's runs (its outcome may be no
            // literal's: `all o. o in univ(1) -> runs(P, s, o)`), the
            // hypotheses to show
            if matches!(concl.node(), Node::App(r, _) if is(*r, self.s.runs)) && all_insts.len() < MAX_INSTANCES {
                let mut gs = Vec::new();
                self.conjuncts(goal, &mut gs);
                for u in &gs {
                    let mut b = Vec::new();
                    if pmatch(self.env, &concl, u, &vs, &mut b) && vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) && !all_insts.iter().any(|(x, _)| *x == b) {
                        all_insts.push((b, (0..hyps.len()).collect()));
                    }
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
                    // (and the path's definitions of variables, `x = t`: the
                    // literals have t for x)
                    for l in &p.lits {
                        if let Node::App(e, ab) = l.node() {
                            if *e == self.s.eq && ab.len() == 2 {
                                if let Node::Var(v, va) = ab[0].node() {
                                    if va.is_empty() && !has_var(&ab[1], *v) && has_var(&h, *v) {
                                        h = self.prop(&h.subst_var(*v, &ab[1], &bf), Pol::Other);
                                    }
                                }
                            }
                        }
                    }
                    let h = &h;
                    if self.is_false(h) || self.is_true(h) {
                        return self.is_true(h);
                    }
                    if p.lits.contains(h) {
                        return true;
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
                // (an instance's conjunction by its conjuncts)
                let shown_all = |h: &Term| {
                    let mut cs = Vec::new();
                    self.conjuncts(h, &mut cs);
                    cs.iter().all(|c| shown(c))
                };
                if !open.iter().all(|&i| shown_all(&inst(&hyps[i]))) {
                    continue;
                }
                let c = inst(&concl);
                // (known: a literal, or by taut from the literals -- not the
                // rule itself, which with its hypotheses gives c by modus
                // ponens, c then never split into its cases)
                let others: Vec<Term> = p.lits.iter().filter(|x| *x != l).cloned().collect();
                if self.is_true(&c) || p.done.contains(&c) || lg.tautology(self.env, &others, &c).is_ok() {
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
        let Some(wr) = self.env.ksym("while_rel") else { return Ok(None) };
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
                // (the step is the lemma `while_unroll`, core/loop.core)
                let used = &lg.simp_used;
                if !used.borrow().iter().any(|n| n == "while_unroll") {
                    used.borrow_mut().push("while_unroll".into());
                }
                let out = self.unroll(a, fresh)?;
                return replace(out, fresh);
            }
        }
        Ok(None)
    }

    /// In the goal (strengthening), `while_rel(l0, l. C, l o. B, l. T, r)`
    /// with C(l0) decided: false -- it stops, `r = ok(l0, empty)`
    /// (`while_stop`); true -- the body leaves (`while_leave`) or goes on to
    /// some l1 from which the loop gives r (`while_step`).
    fn goal_loop(&self, a: &[Term]) -> Option<Term> {
        let env = self.env;
        let wr = env.ksym("while_rel")?;
        let is_ok = env.ksym("is_ok")?;
        let empty = Term::app(env.ksym("empty")?, vec![]);
        let (l0, r) = (self.term(&a[0]), &a[4]);
        // (from a known state: not one bound inside the goal, which one-point
        // fixes first; an iteration per round of the goal's simplification)
        if has_bvar_any(env, &l0, 0) {
            return None;
        }
        let c = self.prop(&inst_k(env, &a[1], &[l0.clone()]), Pol::Other);
        let ok = |x: &Term| Term::app(self.s.ok.expect("ok"), vec![x.clone(), empty.clone()]);
        let use_ = |n: &str| {
            if !self.used.borrow().iter().any(|m| m == n) {
                self.used.borrow_mut().push(n.into());
            }
        };
        if self.is_false(&c) {
            use_("while_stop");
            return Some(self.eq(r, &ok(&l0)));
        }
        if !self.is_true(&c) {
            return None;
        }
        use_("while_leave");
        use_("while_step");
        let body = |x: &Term, o: &Term| inst_k(env, &a[2], &[x.clone(), o.clone()]);
        let leave = self.and(body(&l0, r), self.not(Term::app(is_ok, vec![r.clone()])));
        // ex l1. B(l0, ok(l1)) && while_rel(l1, ..., r) && !(fst(r) = 2)
        let l1 = Term::bvar(0);
        let bf = env.binders_fn();
        // (under the new binder: the loop's parts shifted past their own
        // binders)
        let sh = |t: &Term, k: u32| t.shift(1, k, &bf);
        let (c1, b1, t1) = (sh(&a[1], 1), sh(&a[2], 2), sh(&a[3], 1));
        let again = Term::app(wr, vec![l1.clone(), c1, b1.clone(), t1, sh(r, 0)]);
        let fst = Term::app(self.s.fst.expect("fst"), vec![sh(r, 0)]);
        let not_div = self.not(Term::app(self.s.eq, vec![fst, Term::nat(crate::nat::Nat::from_u64(2))]));
        let step_body = self.and(self.and(inst_k(env, &b1, &[sh(&l0, 0), ok(&l1)]), again), not_div);
        let step = Term::app(self.s.ex, vec![step_body]);
        Some(self.prop(&self.or(leave, step), Pol::Goal))
    }

    /// One iteration of `while_rel(l0, l. C, l o. B, l. T, r)` (theorem
    /// `while_unroll`, core/loop.core): it stops at l0, the body leaves, or
    /// the body continues to l1 and the loop runs on from there (or
    /// diverges).
    fn unroll(&self, a: &[Term], fresh: &mut u32) -> crate::env::KResult<Term> {
        let env = self.env;
        let wr = env.ksym("while_rel").ok_or_else(|| crate::env::KernelError("no while_rel".into()))?;
        let is_ok = env.ksym("is_ok").ok_or_else(|| crate::env::KernelError("no is_ok".into()))?;
        let empty = Term::app(env.ksym("empty").ok_or_else(|| crate::env::KernelError("no empty".into()))?, vec![]);
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
        let sym = |n: &str| env.ksym(n).ok_or_else(|| crate::env::KernelError(format!("loops need `{}`", n)));
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
fn pmatch(env: &Env, pat: &Term, t: &Term, pvars: &[crate::term::VarId], binds: &mut Vec<(crate::term::VarId, Term)>) -> bool {
    match (pat.node(), t.node()) {
        // (a closed subterm only: one under a binder of the matched term may
        // refer to it, and a pattern variable's value is substituted as is)
        (Node::Var(v, a), _) if a.is_empty() && pvars.contains(v) => match binds.iter().find(|(w, _)| w == v) {
            Some((_, b)) => b == t,
            None if t.loose_depth(&env.binders_fn()) == 0 => {
                binds.push((*v, t.clone()));
                true
            }
            None => false,
        },
        (Node::App(f, a), Node::App(g, b)) => f == g && a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| pmatch(env, x, y, pvars, binds)),
        (Node::Var(v, a), Node::Var(w, b)) => v == w && a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| pmatch(env, x, y, pvars, binds)),
        _ => pat == t,
    }
}

/// t with the closed term `atom` replaced by `val` where it stands as a
/// proposition (`pos`): the operands of the connectives, quantifier bodies,
/// an `ite`'s condition (and its branches where the `ite` is one) -- what
/// only its truth matters to
fn subst_prop_pos(sp: &Simp, t: &Term, atom: &Term, val: &Term, pos: bool) -> Term {
    if pos && t == atom {
        return val.clone();
    }
    let Node::App(f, a) = t.node() else { return t.clone() };
    let s = &sp.s;
    let conn = *f == s.imp || *f == s.ex || *f == s.all || is(*f, s.not) || is(*f, s.and) || is(*f, s.or);
    let ite = is(*f, s.ite) && a.len() == 3;
    // (an `ite`'s condition anywhere, e.g. in an equation's side)
    t.with_args(a.iter().enumerate().map(|(i, x)| subst_prop_pos(sp, x, atom, val, conn || (ite && (i == 0 || pos)))).collect())
}

/// whether t mentions the symbol f
fn mentions_sym(t: &Term, f: Option<SymId>) -> bool {
    match t.node() {
        Node::App(g, a) => Some(*g) == f || a.iter().any(|x| mentions_sym(x, f)),
        Node::Var(_, a) => a.iter().any(|x| mentions_sym(x, f)),
        _ => false,
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
        // (SIMP_SLOW=secs: the calls taking longer, reported)
        let slow = std::env::var("SIMP_SLOW").ok().and_then(|v| v.parse::<f64>().ok());
        let t0 = std::time::Instant::now();
        // (large lets kept; else, as the goal may need their values, all
        // reduced)
        let attempt = |eager: bool| {
            let prev = LET_EAGER.with(|e| e.replace(eager));
            let r = self.simp_prove_loops_(env, premises, goal, hints);
            LET_EAGER.with(|e| e.set(prev));
            r
        };
        let r = crate::ext::inventory::measure("simp", env, goal, || match attempt(LET_EAGER.with(|e| e.get())) {
            Err(_) if !LET_EAGER.with(|e| e.get()) => {
                let r = attempt(true);
                if r.is_ok() && std::env::var("SIMP_LET_TRACE").is_ok() {
                    eprintln!("simp: proven only with every let reduced: {}", crate::syntax::Printer::new(env).term(goal).chars().take(300).collect::<String>());
                }
                r
            }
            r => r,
        });
        if let Some(th) = slow {
            let dt = t0.elapsed().as_secs_f64();
            if dt > th {
                let pr = crate::syntax::Printer::new(env);
                eprintln!("simp slow: {:.3}s, {}, {} facts: {}", dt, if r.is_ok() { "ok" } else { "failed" }, premises.len(), pr.term(goal).chars().take(3000).collect::<String>());
            }
        }
        r
    }

    fn simp_prove_loops_(&self, env: &Env, premises: &[Term], goal: &Term, hints: &[LoopHint]) -> crate::env::KResult<()> {
        // fresh variables above every variable of the input
        let mut fresh = env.vars.len() as u32 + 2_000_000;
        for t in premises.iter().chain([goal]).chain(hints.iter().flat_map(|h| [&h.inv].into_iter().chain(&h.var))) {
            fresh = fresh.max(max_var(t) + 1);
        }
        let first = self.prove_paths(env, premises, goal, hints, &mut fresh);
        if first.is_ok() {
            return first;
        }
        // else, a goal `all xs. A1 -> .. -> An -> C`: C, the xs fresh, the
        // A's premises (introduction; the xs occur nowhere else)
        let mut g = goal.clone();
        let mut prem = premises.to_vec();
        let mut opened = false;
        loop {
            match g.node() {
                Node::App(q, a) if *q == self.all && a.len() == 1 => {
                    g = inst_k(env, &a[0], &[Term::var(fresh, vec![])]);
                    fresh += 1;
                }
                Node::App(i, a) if *i == env.builtins.imp && a.len() == 2 => {
                    prem.push(a[0].clone());
                    g = a[1].clone();
                }
                _ => break,
            }
            opened = true;
        }
        if opened {
            match self.prove_paths(env, &prem, &g, hints, &mut fresh) {
                Ok(()) => return Ok(()),
                Err(e) if std::env::var("SIMP_INTRO").is_ok() => eprintln!("simp: after introduction: {}", e.0),
                Err(_) => {}
            }
        }
        first
    }

    /// The premises that unfold a defined symbol: `all x1 .. xn. f(x1, ..,
    /// xn) = rhs` (n >= 1, the xs distinct and in order, f not in rhs).
    fn rewrite_rules(&self, env: &Env, premises: &[Term]) -> Vec<(SymId, usize, Term)> {
        fn mentions(t: &Term, f: SymId) -> bool {
            match t.node() {
                Node::App(g, a) => *g == f || a.iter().any(|x| mentions(x, f)),
                Node::Var(_, a) => a.iter().any(|x| mentions(x, f)),
                _ => false,
            }
        }
        let mut out = Vec::new();
        for p in premises {
            let mut n = 0;
            let mut b = p;
            while let Node::App(q, a) = b.node() {
                if *q != self.all {
                    break;
                }
                b = &a[0];
                n += 1;
            }
            let Node::App(e, ab) = b.node() else { continue };
            if *e != self.eq || n == 0 {
                continue;
            }
            let Node::App(f, xs) = ab[0].node() else { continue };
            let in_order = xs.len() == n && xs.iter().enumerate().all(|(i, x)| matches!(x.node(), Node::BVar(j) if *j as usize == n - 1 - i));
            if in_order && matches!(env.syms[*f as usize].kind, SymKind::Defined { .. }) && !mentions(&ab[1], *f) {
                out.push((*f, n, p.clone()));
            }
        }
        out
    }

    fn prove_paths(&self, env: &Env, premises: &[Term], goal: &Term, hints: &[LoopHint], fresh: &mut u32) -> crate::env::KResult<()> {
        // (the caller's rules kept: simp may run nested)
        let saved = std::mem::replace(&mut *self.simp_rewrites.borrow_mut(), self.rewrite_rules(env, premises));
        let r = self.prove_paths_with(env, premises, goal, hints, fresh);
        *self.simp_rewrites.borrow_mut() = saved;
        r
    }

    fn prove_paths_with(&self, env: &Env, premises: &[Term], goal: &Term, hints: &[LoopHint], fresh: &mut u32) -> crate::env::KResult<()> {
        let sp = Simp::new(env, self);
        let t0 = std::time::Instant::now();
        let mut prem = sp.tt();
        for p in premises {
            prem = sp.and(prem, self.simp_fact(env, p));
        }
        let t1 = std::time::Instant::now();
        // (the premises' `t in univ(u)` hold on every path: known to the
        // goal's strengthening, which would take such a t apart)
        let mut cs = Vec::new();
        sp.conjuncts(&prem, &mut cs);
        // (and as given: `args in set_select(..)` is split above)
        for p in premises {
            sp.conjuncts(p, &mut cs);
        }
        cs.retain(|c| matches!(c.node(), Node::App(i, _) if is(*i, sp.s.in_)));
        let g = self.simp_eqv_known(env, goal, &cs);
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
            let var = |t: &Term| match t.node() {
                Node::Var(x, xa) if xa.is_empty() => Some(*x),
                _ => None,
            };
            // (the equations rewritten by one another, left to right, so
            // they chain: `f(a) = 1` with `a = b` is `f(b) = 1` -- all hold
            // on the path; a few rounds)
            let mut eqs_owned = eqs_owned;
            for _round in 0..3 {
                let mut changed = false;
                for j in 0..eqs_owned.len() {
                    let (a, b) = eqs_owned[j].clone();
                    if var(&a).is_some() || var(&b).is_some() || a == b {
                        continue;
                    }
                    for i in 0..eqs_owned.len() {
                        if i == j {
                            continue;
                        }
                        let (l, r) = eqs_owned[i].clone();
                        let rw = |t: &Term| {
                            let body = super::seq::abstract_term(t, &a, 0, &bf);
                            if body == *t { None } else { Some(inst_k(env, &body, &[b.clone()])) }
                        };
                        let (l2, r2) = (rw(&l), rw(&r));
                        if l2.is_some() || r2.is_some() {
                            eqs_owned[i] = (l2.unwrap_or(l), r2.unwrap_or(r));
                            changed = true;
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            let eqs: Vec<(&Term, &Term)> = eqs_owned.iter().map(|(a, b)| (a, b)).collect();
            let mut substs: Vec<(crate::term::VarId, Term)> = Vec::new();
            // (t built from constructors: x := t, so the goal computes; t
            // opaque: t becomes x in the goal, as in the literals)
            let ctor = |t: &Term| match t.node() {
                Node::Nat(_) | Node::Bytes(_) => true,
                Node::App(h, _) => [sp.s.pair, sp.s.tag, sp.s.ok, sp.s.exc, sp.s.diverge, sp.s.fn_update, sp.s.some, sp.s.none, sp.s.empty].iter().any(|c| is(*h, *c)),
                _ => false,
            };
            // (repeated: the goal simplified again may show a rewritten term
            // anew, e.g. `restrict(s, d)` from a restriction of updates of s)
            for _round in 0..4 {
                let g0 = g.clone();
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
                for &(a, b) in &eqs {
                    if var(a).is_none() && var(b).is_none() {
                        let body = super::seq::abstract_term(&g, a, 0, &bf);
                        if body != g {
                            g = sp.eqv(&inst_k(env, &body, &[b.clone()]));
                        }
                    }
                }
                // (equations of update chains the rewriting brought to
                // light: the goal-side rule, as in the goal's first
                // simplification)
                g = sp.chain_eqs_goal(&g, &p.lits);
                if g.ptr_eq(&g0) || g == g0 {
                    break;
                }
                // (rewritten: the goal's rules again, e.g. the universe
                // closure of what an equation brought in)
                g = sp.prop(&g, Pol::Goal);
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
                // (a proposition: `true` (`false`) in any position; another
                // term only where it stands as a proposition -- a set x that
                // holds need not equal `true`)
                if !self.prop_valued(env, atom) {
                    if atom.loose_depth(&bf) == 0 {
                        let g2 = subst_prop_pos(&sp, &g, atom, &val, true);
                        if g2 != g {
                            g = g2;
                            known = true;
                        }
                    }
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
            if std::env::var("SIMP_GOAL").is_ok() {
                let pr = crate::syntax::Printer::new(env);
                for (a, b) in &eqs {
                    eprintln!("simp: equation on the path: {} = {}", pr.term(a), pr.term(b));
                }
                eprintln!("simp: goal on the path: {}", pr.term(&g));
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
            let closes = |g: &Term| {
                !waits
                    && (sp.typed(&p.lits, g)
                        || self.tautology(env, &p.lits, g).is_ok()
                        || self.arith(env, &p.lits, g).is_ok()
                        || sp.instance_of_all(&p.lits, g)
                        // (with the widths of words read from memory)
                        || self.arith(env, &sp.width_facts(&p.lits), g).is_ok())
            };
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
                    eprintln!("simp: new fact {}", crate::syntax::Printer::new(env).term(&c).chars().take(3000).collect::<String>());
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
                let width = if std::env::var("SIMP_DEBUG").is_ok_and(|v| v == "full") { usize::MAX } else { 400 };
                for l in &p.lits {
                    eprintln!("simp: literal {}", pr.term(l).chars().take(width).collect::<String>());
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
            // the goal computes a branch `ite(c, a, b)` its path does not
            // decide: split on c (c || !c)
            // (a compound condition: an atom of it the path does not have)
            let split_on = |c: Term| -> Option<Term> {
                fn atoms(sp: &Simp, t: &Term, out: &mut Vec<Term>) {
                    match t.node() {
                        Node::App(f, a) if is(*f, sp.s.and) || is(*f, sp.s.or) || is(*f, sp.s.not) => a.iter().for_each(|x| atoms(sp, x, out)),
                        _ => out.push(t.clone()),
                    }
                }
                let mut cands = vec![c.clone()];
                atoms(&sp, &c, &mut cands);
                cands.into_iter().find(|a| {
                    let na = Term::app(sp.s.not.unwrap(), vec![a.clone()]);
                    !full.lits.contains(a) && !full.lits.contains(&na)
                })
            };
            if let Some(c) = open_ite(env, sp.s.ite, &g).and_then(split_on) {
                let nc = Term::app(sp.s.not.unwrap(), vec![c.clone()]);
                {
                    steps += 1;
                    if steps > MAX_PATHS {
                        return Err(crate::env::KernelError("simp: too many paths".into()));
                    }
                    work.extend(sp.extend(self, &full, c, fresh)?);
                    work.extend(sp.extend(self, &full, nc, fresh)?);
                    continue;
                }
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
        self.simp_eqv_known(env, t, &[])
    }

    /// `simp_eqv` with the facts `known` (literals `t in univ(u)`) in the
    /// typing context.
    fn simp_eqv_known(&self, env: &Env, t: &Term, known: &[Term]) -> Term {
        let sp = Simp::new(env, self);
        sp.set_nats(known);
        let mut t = t.clone();
        // (more rounds when running a loop of the goal: one per iteration)
        for _ in 0..if sp.goal_loops { 64 } else { 8 } {
            let u = sp.prop(&t, Pol::Goal);
            if u == t {
                break;
            }
            t = u;
        }
        for n in sp.used.borrow().iter() {
            if !self.simp_used.borrow().contains(n) {
                self.simp_used.borrow_mut().push(n.clone());
            }
        }
        t
    }
}
