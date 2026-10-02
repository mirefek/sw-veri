//! Forward execution of a spec program (part of the trusted `simp`
//! extension; proof-plan section 6.2): `spec_run({P}, {W}, facts..)` runs
//! the program P from the world W symbolically and states, per branch,
//!
//!   all ps. C1 -> .. -> Cn -> runs(P, W, O)
//!
//! for the outcome O the branch reaches under its conditions Ci; the ps are
//! the values the program leaves open (`any`: uninitialized locals, an
//! unused result register; what undefined behaviour leaves open), kept as
//! parameters, with their typing among the Ci. Branches come from the
//! program's `if`s whose condition the facts do not decide, and from its
//! operations: a `runs(Q, s, X)` with Q an operation is solved by its lemmas
//! among the facts (`all xs. H.. -> runs(Q(xs), s, O)`, e.g. `g.ld8_ok`
//! and `g.ld8_ub`), their premises becoming the branch's conditions; other
//! programs are unfolded (procs, accessors, operations without lemmas), and
//! a built function applied to an argument in its domain (`app(F, args)`
//! of a `_fun` wrapper) is its program for the argument. A value an
//! operation's lemma leaves open (the exception of undefined behaviour) is
//! a parameter, its lemma's premises about it among the conditions.
//!
//! Conditions are decided from the facts and the branch's conditions (as
//! symex decides; conjunctions by their parts; with the arithmetic helpers
//! unfolded and an `ite` of a signed value's range split), and stated in
//! word form: `gimple.wrap(T, x)` of a literal type T is
//! `bits_add(n, x, 0)`; `gimple.sval(T, v)` of an n-bit v is `sint(n, v)`
//! (signed) or v; `gimple.fits(T, sint(m, y))` is true for a signed T of
//! n >= m bits; `sint(n, x)` of an x the context bounds below 2^(n-1) is
//! x; an n-bit sum of an m-bit word and a literal c that does not wrap
//! (2^m + c <= 2^n) is the integer sum. The output's conditions are split
//! into conjuncts, without repetition or what the facts show; a parameter
//! only typed as a word (`x in bits(n)`, a value nothing reads) is
//! dropped, as its witness 0 would be.
//!
//! The branches of undefined behaviour -- `C1 -> .. -> Cn -> runs(P, W,
//! exc(S, x))` for any x in univ(1), all with the same S or with any S
//! (undefined behaviour leaves the world open: the `_ub` lemmas raise from
//! any world), and those with any outcome at all (a wrapper's missing
//! argument) -- are stated together, as the disjunction of their
//! conditions:
//!
//!   all s e. s in univ(1) -> e in univ(1) -> !D -> runs(P, W, exc(s, e))
//!
//! with D the conjunction of their `C1 -> .. -> !Cn` (what defined means:
//! the reads each path makes can be made). A proof of a `raises` lemma
//! then only shows its own definedness to imply D.
//!
//! Loops: without a hint, a loop from a known state is unrolled (resting
//! on `while_stop`, `while_leave`, `while_step`). With `spec_run({P}, {W},
//! {l. I}, {l. m}, ..)`, the program's loop (not the GIMPLE layer's, over
//! an access's bytes) is run by the invariant I and variant m, as
//! `while_exists` (core/loop.core) allows: I at the entry a condition; the
//! body once, from a state lv with I and the loop's condition; the
//! obligations -- m(lv) a natural; each branch going on to l2 giving I(l2)
//! and m(l2) < m(lv); the body's branches covering the case -- decided, or
//! stated as hypotheses (closed in lv); the exits -- the condition failing
//! at lv, or a body branch leaving (a break, undefined behaviour) -- with
//! lv existential. Per such loop one statement:
//!
//!   all ps. pre.. -> typing.. -> obligations.. ->
//!     (ex lv. D1 && runs(P, W, O1)) || ..
//!
//! one disjunct per branch past the loop, its exit's conditions and its own
//! in Di; the branches past an exit covering it is an obligation too. The
//! loop's state has its entry's shape: a pair of variables for a pair
//! (`(world, i)`; `while_exists` with the invariant `l is such a pair &&
//! I(l)`, each state the body goes on to checked to be one), so that the
//! invariant's equations define variables. An obligation is also tried by
//! simp, from the premises (the user's lemmas about the loop: its entry,
//! one pass, its exit) and the conditions on the way.
//! Parameters the body or the rest leave open (an exception value of
//! undefined behaviour) are chosen once, for all iterations: universal,
//! their typing among the hypotheses.
//!
//! Each branch is shown by construction: the program's relation holds for
//! the branch's outcome when its conditions do (`runs(mkprog(R), s, o)` is
//! `pair(s, o) in univ(1) && R(s, o)`, whose membership is among the
//! conditions unless decided). An equation on projections of an unknown
//! (`fst(x) = 1`: an outcome's tag) gives it pair structure. The search is
//! not complete -- a branch may be missing -- and needs not be: the
//! statements are existence statements, what the spec allows.

use super::*;
use crate::env::KResult;
use crate::ext::seq::abstract_term;
use crate::term::VarId;

type Assign = Vec<(VarId, Term)>;

const UNSOLVED: &str = "unsolved: ";
/// arithmetic helpers unfolded in conditions (layers/gimple.sl and the
/// prelude): a signed value, a type's range test, wrapping
const ARITH_DEFS: &[&str] = &["sint", "gimple.sval", "gimple.fits", "gimple.wrap"];
/// steps of the search
const FUEL: usize = 200_000;

#[derive(Clone, Default)]
struct Br {
    a: Assign,
    conds: Vec<Term>,
    /// a branch past a loop run by its invariant: (the loop's group, which
    /// exit of the loop)
    group: Option<(usize, usize)>,
}

/// A loop run by its invariant P and variant m (`run_loop_inv`): the
/// conditions on the way to it (P(l0) among them), the obligations left
/// (closed in the loop's state), the variable for the state at the exit,
/// and per exit its conditions on that state.
struct Group {
    pre: Vec<Term>,
    hyps: Vec<Term>,
    /// the variables of the state at the exit (its components, when the
    /// loop's state is a pair)
    lv: Vec<VarId>,
    exits: Vec<Vec<Term>>,
}

/// t with the variables vs bound by q (`all`/`ex`), those it has.
fn bind_vars(q: SymId, t: &Term, vs: &[VarId], bf: &dyn Fn(SymId, usize) -> u32) -> Term {
    let mut t = t.clone();
    for v in vs.iter().rev() {
        if has_var(&t, *v) {
            t = Term::app(q, vec![abstract_term(&t, &Term::var(*v, vec![]), 0, bf)]);
        }
    }
    t
}

struct Sr<'s, 'a> {
    sp: &'s Simp<'a>,
    lg: &'s Logic,
    facts: Vec<Term>,
    lemmas: Vec<Term>,
    fresh: u32,
    /// the unknowns (bound by a branch's assignment, or open)
    us: std::collections::HashSet<VarId>,
    fuel: usize,
    depth: usize,
    /// the loops' invariants and variants (`{l. I}`, `{l. m}`)
    hints: Vec<(Term, Term)>,
    groups: Vec<Group>,
    /// inside an operation of the GIMPLE layer (its loops unrolled)
    op_depth: usize,
    /// the premises as given (for simp, on a loop's obligations)
    premises: Vec<Term>,
}

fn err<T>(m: impl Into<String>) -> Result<T, String> {
    Err(m.into())
}

impl Sr<'_, '_> {
    fn var(&mut self) -> (VarId, Term) {
        let v = self.fresh;
        self.fresh += 1;
        (v, Term::var(v, vec![]))
    }

    fn unknown(&mut self) -> (VarId, Term) {
        let (v, t) = self.var();
        self.us.insert(v);
        (v, t)
    }

    /// t with the assignment's unknowns replaced by their values (and
    /// theirs, transitively; a parameter is bound to itself). The values
    /// are closed (no loose bound variables), so binders need no shifting.
    fn subst(&self, t: &Term, a: &Assign) -> Term {
        if a.is_empty() {
            return t.clone();
        }
        let map: std::collections::HashMap<VarId, &Term> = a.iter().map(|(v, x)| (*v, x)).collect();
        fn go(t: &Term, map: &std::collections::HashMap<VarId, &Term>, memo: &mut std::collections::HashMap<usize, Term>, depth: u32) -> Term {
            match t.node() {
                Node::Var(v, args) if args.is_empty() => match map.get(v) {
                    Some(x) if depth < 64 && !matches!(x.node(), Node::Var(w, wa) if w == v && wa.is_empty()) => go(x, map, memo, depth + 1),
                    _ => t.clone(),
                },
                Node::App(_, xs) | Node::Var(_, xs) if !xs.is_empty() => {
                    let key = t.node() as *const Node as usize;
                    if let Some(r) = memo.get(&key) {
                        return r.clone();
                    }
                    let ys: Vec<Term> = xs.iter().map(|x| go(x, map, memo, depth)).collect();
                    let r = if ys.iter().zip(xs.iter()).all(|(y, x)| y.node() as *const Node == x.node() as *const Node) { t.clone() } else { t.with_args(ys) };
                    memo.insert(key, r.clone());
                    r
                }
                _ => t.clone(),
            }
        }
        go(t, &map, &mut std::collections::HashMap::new(), 0)
    }

    fn open(&self, t: &Term, a: &Assign) -> bool {
        let mut vs = Vec::new();
        t.vars(&mut vs);
        vs.iter().any(|v| self.us.contains(v) && !a.iter().any(|(w, _)| w == v))
    }

    fn show(&self, t: &Term) -> String {
        crate::syntax::Printer::new(self.sp.env).term(t).chars().take(300).collect()
    }

    /// A closed proposition in the branch: true, false, or undecided (a
    /// defined predicate, or its negation, tried once more unfolded: the
    /// range tests of arithmetic, `gimple.fits`).
    fn decide(&self, c: &Term, br: &Br) -> Option<bool> {
        let ctx: Vec<Term> = self.facts.iter().chain(&br.conds).cloned().collect();
        self.decide_in(&ctx, c, 2)
    }

    /// `decide` in the context ctx: as symex decides; else with the
    /// arithmetic helpers unfolded (`ARITH_DEFS`: their `ite`s the range
    /// cases of a signed value), and an `ite` of the condition split (both
    /// cases deciding it the same way).
    fn decide_in(&self, ctx: &[Term], c: &Term, depth: u32) -> Option<bool> {
        self.sp.set_nats(ctx);
        let c = &self.sp.prop(&self.word(ctx, c), Pol::Other);
        if let Some(r) = self.lg.symex_decide(self.sp, ctx, c) {
            return Some(r);
        }
        // (true by a stronger form: simp's strengthening of goals, e.g. a
        // function update of members is in a universe)
        let g = self.sp.prop(c, Pol::Goal);
        if g != *c && self.lg.symex_decide(self.sp, ctx, &g) == Some(true) {
            return Some(true);
        }
        let u = self.sp.prop(&self.unfold_arith(c), Pol::Other);
        if u != *c {
            if let Some(r) = self.lg.symex_decide(self.sp, ctx, &u) {
                return Some(r);
            }
        }
        // connectives: by their components
        if let Node::App(f, a) = u.node() {
            let sub = |t: &Term| self.decide_in(ctx, t, depth);
            if is(*f, self.sp.s.not) && a.len() == 1 && matches!(a[0].node(), Node::App(..)) {
                if let Some(r) = sub(&a[0]) {
                    return Some(!r);
                }
            } else if (is(*f, self.sp.s.and) || is(*f, self.sp.s.or)) && a.len() == 2 {
                let conj = is(*f, self.sp.s.and);
                let (l, r) = (sub(&a[0]), sub(&a[1]));
                match (l, r) {
                    (Some(x), _) | (_, Some(x)) if x != conj => return Some(x),
                    (Some(_), Some(_)) => return Some(conj),
                    _ => {}
                }
            }
        }
        if depth == 0 {
            return None;
        }
        if std::env::var("SPEC_DEBUG").is_ok() {
            eprintln!("spec_run: undecided {}\n  unfolded {}", self.show(c), self.show(&u));
        }
        let k = open_ite(self.sp.env, self.sp.s.ite, &u)?;
        let (mut c1, mut c2) = (ctx.to_vec(), ctx.to_vec());
        c1.push(k.clone());
        c2.push(self.sp.not(k.clone()));
        // (k replaced by its value in each case)
        let body = abstract_term(&u, &k, 0, &self.sp.env.binders_fn());
        let (u1, u2) = (inst_k(self.sp.env, &body, &[self.sp.tt()]), inst_k(self.sp.env, &body, &[self.sp.ff()]));
        // (a case the context contradicts does not count)
        let env = self.sp.env;
        let absurd = |cx: &[Term], k: &Term| {
            let near = relevant(cx, k);
            self.lg.arith(env, &near, &self.sp.ff()).is_ok() || self.lg.tautology(env, &near, &self.sp.ff()).is_ok()
        };
        let not_k = self.sp.not(k.clone());
        if std::env::var("SPEC_DEBUG").is_ok() {
            eprintln!("  split {} absurd {} {}\n  u1 {}", self.show(&k), absurd(&c1, &k), absurd(&c2, &not_k), self.show(&self.sp.prop(&u1, Pol::Other)));
        }
        let r1 = if absurd(&c1, &k) { None } else { Some(self.decide_in(&c1, &u1, depth - 1)?) };
        let r2 = if absurd(&c2, &not_k) { None } else { Some(self.decide_in(&c2, &u2, depth - 1)?) };
        self.sp.set_nats(ctx);
        match (r1, r2) {
            (Some(a), Some(b)) => (a == b).then_some(a),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        }
    }

    /// The arithmetic helpers of a literal type in their word forms
    /// (bottom-up), then simplified: `gimple.wrap(T, x)` is x mod 2^n
    /// (`bits_add(n, x, 0)`); `gimple.sval(T, v)` of an n-bit v is
    /// `sint(n, v)` (signed) or v; `gimple.fits(T, sint(m, y))` is true for
    /// a signed T of n >= m bits.
    fn word(&self, ctx: &[Term], t: &Term) -> Term {
        Words { sp: self.sp, lg: self.lg, bytes: false, memo: Default::default(), eqs: Vec::new() }.word(ctx, t)
    }

    /// The arithmetic helpers unfolded in t (bottom-up).
    fn unfold_arith(&self, t: &Term) -> Term {
        let Node::App(g, x) = t.node() else { return t.clone() };
        let bind = self.sp.env.binders_fn();
        let x: Vec<Term> = x.iter().enumerate().map(|(i, y)| if bind(*g, i) == 0 { self.unfold_arith(y) } else { y.clone() }).collect();
        if ARITH_DEFS.contains(&self.sp.env.syms[*g as usize].name.as_str()) {
            if let Some(u) = self.sp.unfold(*g, &x) {
                return self.unfold_arith(&self.sp.term(&u));
            }
        }
        t.with_args(x)
    }
}

/// The word normalization under a context (the spec's, and the machine's
/// states and premises, at the bridge: one form for both).
pub(super) struct Words<'s, 'a> {
    pub(super) sp: &'s Simp<'a>,
    pub(super) lg: &'s Logic,
    /// memory reads of a few bytes as their sums of bytes: the spec's
    /// `gimple.bytes_at(vm, a, k)` and the machine's
    /// `x86_64_linux.le(b, a, k)` (k <= 8 a literal) unfolded -- one form
    /// for both, where they are compared
    pub(super) bytes: bool,
    /// the forms found, under the one context (cleared when it changes)
    pub(super) memo: std::cell::RefCell<std::collections::HashMap<Term, Term>>,
    /// the premises' equations `all xs. H.. -> l = r` (math lemmas: the
    /// machine's computation l as the spec's r), applied where H holds
    pub(super) eqs: Vec<(Vec<VarId>, Vec<Term>, Term, Term)>,
}

impl<'s, 'a> Words<'s, 'a> {
    pub(super) fn new(sp: &'s Simp<'a>, lg: &'s Logic, bytes: bool, premises: &[Term]) -> Self {
        let mut fresh = sp.env.vars.len() as u32 + 7_000_000;
        for p in premises {
            fresh = fresh.max(max_var(p) + 1);
        }
        let mut eqs = Vec::new();
        for p in premises {
            if !matches!(p.node(), Node::App(q, _) if *q == lg.all) {
                continue;
            }
            let Some((vs, hyps, concl)) = sp.rule(p, &mut fresh) else { continue };
            let Node::App(e, ab) = concl.node() else { continue };
            if *e != sp.s.eq || !matches!(ab[0].node(), Node::App(..)) {
                continue;
            }
            let mut lv = Vec::new();
            ab[0].vars(&mut lv);
            if vs.iter().all(|v| lv.contains(v)) {
                eqs.push((vs, hyps, ab[0].clone(), ab[1].clone()));
            }
        }
        // (the equations in the same forms -- their reads of memory as
        // sums of bytes -- no context: nothing decided)
        let plain = Words { sp, lg, bytes, memo: Default::default(), eqs: Vec::new() };
        let eqs = eqs
            .into_iter()
            .map(|(vs, hyps, l, r)| {
                let hyps = hyps.iter().map(|h| plain.word(&[], h)).collect();
                (vs, hyps, plain.word(&[], &l), plain.word(&[], &r))
            })
            .collect();
        Words { sp, lg, bytes, memo: Default::default(), eqs }
    }

    /// t by an equation whose left side it is, its hypotheses shown
    fn by_eqs(&self, ctx: &[Term], t: &Term) -> Option<Term> {
        let bf = self.sp.env.binders_fn();
        for (vs, hyps, l, r) in &self.eqs {
            let mut b = Vec::new();
            if !super::pmatch(l, t, vs, &mut b) || !vs.iter().all(|v| b.iter().any(|(w, _)| w == v)) {
                continue;
            }
            let sub = |x: &Term| b.iter().fold(x.clone(), |x, (v, y)| x.subst_var(*v, y, &bf));
            let shown = hyps.iter().all(|h| {
                let h = self.sp.prop(&sub(h), Pol::Other);
                self.sp.is_true(&h) || ctx.contains(&h) || self.sp.typed(ctx, &h) || self.lg.symex_decide(self.sp, ctx, &h) == Some(true)
            });
            if shown {
                return Some(self.sp.term(&sub(r)));
            }
        }
        None
    }
}

impl Words<'_, '_> {
    pub(super) fn word(&self, ctx: &[Term], t: &Term) -> Term {
        if std::env::var("WORDS_DEBUG").is_ok_and(|v| v == "2") && t.loose_depth(&self.sp.env.binders_fn()) == 0 {
            let pr = crate::syntax::Printer::new(self.sp.env);
            let s = pr.term(t);
            if s.starts_with("bits_add(64, app(args, 0), 32)") || s.starts_with("bits_add(64, bits_add(64, app(args") {
                eprintln!("words: word of {} (memo {})", s, self.memo.borrow().contains_key(t));
            }
        }
        if let Some(u) = self.memo.borrow().get(t) {
            return u.clone();
        }
        let u = self.word_of(ctx, t);
        self.memo.borrow_mut().insert(t.clone(), u.clone());
        u
    }

    fn word_of(&self, ctx: &[Term], t: &Term) -> Term {
        let u = self.word_base(ctx, t);
        if self.eqs.is_empty() || u.loose_depth(&self.sp.env.binders_fn()) > 0 {
            return u;
        }
        match self.by_eqs(ctx, &u) {
            Some(r) if r != u => self.word(ctx, &r),
            _ => u,
        }
    }

    fn word_base(&self, ctx: &[Term], t: &Term) -> Term {
        let Node::App(g, x) = t.node() else { return t.clone() };
        let bind = self.sp.env.binders_fn();
        // (under binders too: the context decides closed subterms only)
        let x: Vec<Term> = x.iter().map(|y| self.word(ctx, y)).collect();
        let t = t.with_args(x.clone());
        let name = self.sp.env.syms[*g as usize].name.as_str();
        if self.bytes && matches!(name, "gimple.bytes_at" | "x86_64_linux.le") && x.len() == 3 && matches!(x[2].node(), Node::Nat(k) if k.to_u64().is_some_and(|k| (1..=8).contains(&k))) {
            if let Some(u) = self.sp.unfold(*g, &x) {
                return self.word(ctx, &self.sp.term(&u));
            }
        }
        if t.loose_depth(&bind) > 0 {
            return t;
        }
        // an n-bit sum of an m-bit word and a literal c that does not wrap
        // (2^m + c <= 2^n): the integer sum c + x (an address, as the
        // spec's operations compute it)
        if name == "bits_add" && x.len() == 3 {
            if let (Node::Nat(n), Some(ia)) = (x[0].node(), self.sp.env.sym_by_name.get("int_add")) {
                for (y, c) in [(&x[1], &x[2]), (&x[2], &x[1])] {
                    let Node::Nat(c) = c.node() else { continue };
                    let fits = (1..64u64).find(|&m| self.sp.bits_term(y, m)).is_some_and(|m| crate::nat::Nat::pow2(m).add(c) <= *n.to_u64().map(crate::nat::Nat::pow2).as_ref().unwrap_or(&crate::nat::Nat::zero()));
                    if fits && !c.is_zero() && !matches!(y.node(), Node::Nat(_)) {
                        let lit = Term::nat(c.clone());
                        return if *c >= crate::nat::Nat::from_u64(4096) { Term::app(*ia, vec![lit, y.clone()]) } else { Term::app(*ia, vec![y.clone(), lit]) };
                    }
                }
            }
        }
        // an n-bit sum of a word y and a literal c the context shows does not
        // wrap (y + c < 2^n): the integer sum -- an address as base + offset
        // (c a large literal first), an index as i + c
        if name == "bits_add" && x.len() == 3 {
            if let (Node::Nat(n), Some(ia), Some(lt)) = (x[0].node(), self.sp.env.sym_by_name.get("int_add"), self.sp.env.sym_by_name.get("int_lt")) {
                if let Some(n) = n.to_u64().filter(|&n| (1..=128).contains(&n)) {
                    for (y, c) in [(&x[1], &x[2]), (&x[2], &x[1])] {
                        let Node::Nat(cv) = c.node() else { continue };
                        // (c below 2^(n-1): a negative c, a subtraction, wraps
                        // unless y is large -- not an address's offset)
                        if cv.is_zero() || *cv >= crate::nat::Nat::pow2(n - 1) || matches!(y.node(), Node::Nat(_)) || !self.sp.bits_term(y, n) {
                            if std::env::var("WORDS_DEBUG").is_ok() && !cv.is_zero() {
                                let pr = crate::syntax::Printer::new(self.sp.env);
                                let ty = ctx.iter().find(|l| matches!(l.node(), Node::App(i, ab) if is(*i, self.sp.s.in_) && ab[0] == *y)).map(|l| pr.term(l));
                                eprintln!("words: no sum (typing {}, in context {:?}): {}", self.sp.bits_term(y, n), ty, pr.term(&t));
                            }
                            continue;
                        }
                        let sum = if *cv >= crate::nat::Nat::from_u64(4096) { Term::app(*ia, vec![c.clone(), y.clone()]) } else { Term::app(*ia, vec![y.clone(), c.clone()]) };
                        let lim = Term::nat(crate::nat::Nat::pow2(n));
                        let goal = Term::app(*lt, vec![Term::app(*ia, vec![y.clone(), c.clone()]), lim]);
                        let d = self.lg.symex_decide(self.sp, ctx, &goal);
                        if std::env::var("WORDS_DEBUG").is_ok() {
                            let pr = crate::syntax::Printer::new(self.sp.env);
                            eprintln!("words: no wrap {:?}: {} (as {})", d, pr.term(&goal), pr.term(&self.sp.prop(&goal, Pol::Other)));
                            if d.is_none() {
                                for l in ctx.iter().filter(|l| pr.term(l).contains("int_lt(") && pr.term(l).len() < 200) {
                                    eprintln!("   ctx: {}", pr.term(l));
                                }
                            }
                        }
                        if d == Some(true) {
                            return sum;
                        }
                    }
                }
            }
        }
        // the sign extension of an m-bit x the context bounds below
        // 2^(m-1): x
        if name == "bits_sext" && x.len() == 3 {
            if let (Node::Nat(m), Some(lt)) = (x[0].node(), self.sp.env.sym_by_name.get("int_lt")) {
                if let Some(m) = m.to_u64().filter(|&m| (2..=128).contains(&m) && self.sp.bits_term(&x[2], m)) {
                    let half = Term::nat(crate::nat::Nat::pow2(m - 1));
                    if self.lg.symex_decide(self.sp, ctx, &Term::app(*lt, vec![x[2].clone(), half])) == Some(true) {
                        return x[2].clone();
                    }
                }
            }
        }
        // the signed value of an n-bit x the context bounds below 2^(n-1): x
        if name == "sint" && x.len() == 2 {
            if let (Node::Nat(n), Some(lt)) = (x[0].node(), self.sp.env.sym_by_name.get("int_lt")) {
                if let Some(n) = n.to_u64().filter(|&n| (2..=128).contains(&n) && self.sp.bits_term(&x[1], n)) {
                    let half = Term::nat(crate::nat::Nat::pow2(n - 1));
                    if self.lg.symex_decide(self.sp, ctx, &Term::app(*lt, vec![x[1].clone(), half])) == Some(true) {
                        return x[1].clone();
                    }
                }
            }
        }
        if !matches!(name, "gimple.wrap" | "gimple.sval" | "gimple.fits") || x.len() != 2 {
            return self.sp.term(&t);
        }
        let field = |f: &str| {
            let app = self.sp.s.app?;
            Some(self.sp.term(&Term::app(app, vec![x[0].clone(), Term::bytes(f.as_bytes())])))
        };
        let (Some(prec), Some(signed)) = (field("prec"), field("signed")) else { return self.sp.term(&t) };
        let Node::Nat(n) = prec.node() else { return self.sp.term(&t) };
        let Some(n) = n.to_u64().filter(|&n| (1..=128).contains(&n)) else { return self.sp.term(&t) };
        let signed = if self.sp.is_true(&signed) {
            true
        } else if self.sp.is_false(&signed) || matches!(signed.node(), Node::Nat(z) if z.is_zero()) || matches!(signed.node(), Node::App(e, a) if a.is_empty() && is(*e, self.sp.s.empty)) {
            // (a type without the field: unsigned)
            false
        } else {
            return self.sp.term(&t);
        };
        let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
        let sym = |s: &str| self.sp.env.sym_by_name.get(s).copied();
        match name {
            "gimple.wrap" => {
                let Some(ba) = self.sp.s.bits_add else { return t };
                self.sp.term(&Term::app(ba, vec![nat(n), x[1].clone(), nat(0)]))
            }
            "gimple.sval" if self.sp.bits_term(&x[1], n) => match (signed, sym("sint")) {
                (false, _) => x[1].clone(),
                (true, Some(si)) => self.sp.term(&Term::app(si, vec![nat(n), x[1].clone()])),
                _ => t,
            },
            "gimple.fits" if signed => match x[1].node() {
                Node::App(h, b) if Some(*h) == sym("sint") && b.len() == 2 && matches!(b[0].node(), Node::Nat(m) if m.to_u64().is_some_and(|m| m <= n)) => self.sp.tt(),
                _ => self.sp.term(&t),
            },
            _ => self.sp.term(&t),
        }
    }
}

impl Sr<'_, '_> {
    /// The branch with the condition c: kept, dropped, or c added.
    fn with_cond(&self, c: &Term, br: Br) -> Vec<Br> {
        match self.decide(c, &br) {
            Some(true) => vec![br],
            Some(false) => vec![],
            None => {
                let mut b = br;
                self.sp.set_nats(&self.facts.iter().chain(&b.conds).cloned().collect::<Vec<_>>());
                let mut cs = Vec::new();
                self.sp.conjuncts(&self.sp.prop(&self.word(&self.facts.iter().chain(&b.conds).cloned().collect::<Vec<_>>(), c), Pol::Other), &mut cs);
                for c in cs {
                    if !b.conds.contains(&c) && !self.facts.contains(&c) {
                        b.conds.push(c);
                    }
                }
                vec![b]
            }
        }
    }

    /// `out_state(o)` / `out_value(o)` as the projections they are, then
    /// simplified (projections of pairs computed).
    fn proj_norm(&self, t: &Term) -> Term {
        fn go(sr: &Sr, t: &Term) -> Term {
            let Node::App(g, x) = t.node() else { return t.clone() };
            let x: Vec<Term> = x.iter().map(|y| go(sr, y)).collect();
            let name = sr.sp.env.syms[*g as usize].name.as_str();
            if (name == "out_state" || name == "out_value") && x.len() == 1 {
                if let Some(u) = sr.sp.unfold(*g, &x) {
                    return u;
                }
            }
            t.with_args(x)
        }
        self.sp.term(&go(self, t))
    }

    /// An unbound unknown under projections (`fst(snd(x))`): x.
    fn proj_root(&self, t: &Term, a: &Assign) -> Option<VarId> {
        let s = &self.sp.s;
        match t.node() {
            Node::Var(v, va) if va.is_empty() && self.us.contains(v) && !a.iter().any(|(w, _)| w == v) => Some(*v),
            Node::App(g, x) if x.len() == 1 => {
                let name = self.sp.env.syms[*g as usize].name.as_str();
                if is(*g, s.fst) || is(*g, s.snd) || name == "out_state" || name == "out_value" {
                    self.proj_root(&x[0], a)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn solve(&mut self, p: &Term, br: Br) -> Result<Vec<Br>, String> {
        if self.depth > 600 {
            return err(format!("too deep at {}", self.show(&self.subst(p, &br.a))));
        }
        self.depth += 1;
        let r = self.solve1(p, br);
        self.depth -= 1;
        r
    }

    fn solve1(&mut self, p: &Term, br: Br) -> Result<Vec<Br>, String> {
        if self.fuel == 0 {
            return err("the program's search ran out of fuel");
        }
        self.fuel -= 1;
        let p = self.subst(p, &br.a);
        let sp = self.sp;
        let s = &sp.s;
        let Node::App(f, x) = p.node() else { return err(format!("{}{}", UNSOLVED, self.show(&p))) };
        let f = *f;
        if is(f, s.and) {
            return match self.solve(&x[0], br.clone()) {
                Ok(bs) => {
                    let mut out = Vec::new();
                    for b in bs {
                        out.extend(self.solve(&x[1], b)?);
                    }
                    Ok(out)
                }
                Err(m) if m.starts_with(UNSOLVED) => {
                    if std::env::var("SPEC_DEBUG").is_ok() {
                        eprintln!("spec_run: and, left {}", m.chars().take(300).collect::<String>());
                    }
                    let mut out = Vec::new();
                    for b in self.solve(&x[1], br).map_err(|_| m.clone())? {
                        out.extend(self.solve(&x[0], b).map_err(|_| m.clone())?);
                    }
                    Ok(out)
                }
                Err(m) => Err(m),
            };
        }
        if is(f, s.or) {
            // (a disjunct that cannot be solved is left out: the branches
            // need not be all; e.g. undefined behaviour continuing as if an
            // operation had returned some state)
            let (l, r) = (self.solve(&x[0], br.clone()), self.solve(&x[1], br));
            return match (l, r) {
                (Ok(mut a), Ok(b)) => {
                    a.extend(b);
                    Ok(a)
                }
                (Ok(a), Err(m)) | (Err(m), Ok(a)) if m.starts_with(UNSOLVED) => Ok(a),
                (Err(m), _) | (_, Err(m)) => Err(m),
            };
        }
        if f == s.imp {
            let q = sp.or(sp.not(x[0].clone()), x[1].clone());
            return self.solve(&q, br);
        }
        if f == s.ex {
            let (_, vt) = self.unknown();
            let body = inst_k(sp.env, &x[0], &[vt]);
            return self.solve(&body, br);
        }
        if f == s.eq {
            for (pat, val) in [(&x[0], &x[1]), (&x[1], &x[0])] {
                if self.open(pat, &br.a) && !self.open(val, &br.a) {
                    let v = sp.term(val);
                    let mut b = br.clone();
                    match self.unify(pat, &v, &mut b)? {
                        Some(true) => return Ok(vec![b]),
                        Some(false) => return Ok(vec![]),
                        None => {}
                    }
                    // a projection of an unknown: it is a pair (fresh parts)
                    if let Some(r) = self.proj_root(&self.proj_norm(pat), &br.a) {
                        let (_, u1) = self.unknown();
                        let (_, u2) = self.unknown();
                        let mut b = br.clone();
                        b.a.push((r, Term::app(s.pair.unwrap(), vec![u1, u2])));
                        return self.solve(&p, b);
                    }
                    return err(format!("{}{}", UNSOLVED, self.show(&p)));
                }
            }
            if !self.open(&p, &br.a) {
                return Ok(self.with_cond(&p, br));
            }
            // the same constructor on both sides: its arguments equal
            if let (Node::App(g, ga), Node::App(h, ha)) = (x[0].node(), x[1].node()) {
                let ctor = [s.pair, s.tag, s.ok, s.exc, s.diverge].iter().any(|c| is(*g, *c));
                let outcome = |k: &SymId| [s.ok, s.exc, s.diverge].iter().any(|c| is(*k, *c));
                if g != h && outcome(g) && outcome(h) {
                    return Ok(vec![]);
                }
                if g == h && ctor && ga.len() == ha.len() {
                    let mut q = sp.tt();
                    for (a, c) in ga.iter().zip(ha.iter()).rev() {
                        q = Term::app(s.and.unwrap(), vec![Term::app(s.eq, vec![a.clone(), c.clone()]), q]);
                    }
                    return self.solve(&q, br);
                }
            }
            // an unknown defined by a term with other unknowns
            for (pat, val) in [(&x[0], &x[1]), (&x[1], &x[0])] {
                if let Node::Var(v, va) = pat.node() {
                    if va.is_empty() && self.us.contains(v) && !br.a.iter().any(|(w, _)| w == v) && !has_var(val, *v) {
                        let mut b = br;
                        b.a.push((*v, sp.term(val)));
                        return Ok(vec![b]);
                    }
                }
            }
            return err(format!("{}{}", UNSOLVED, self.show(&p)));
        }
        if Some(f) == sp.env.sym_by_name.get("while_rel").copied() && x.len() == 5 && !self.open(&x[0], &br.a) {
            if !self.hints.is_empty() && self.op_depth == 0 {
                return self.run_loop_inv(x, br);
            }
            return self.run_loop(x, br);
        }
        if is(f, s.runs) {
            if self.open(&x[0], &br.a) || self.open(&x[1], &br.a) {
                return err(format!("{}{}", UNSOLVED, self.show(&p)));
            }
            return self.run(&x[0], &x[1], &x[2], br);
        }
        if is(f, s.in_) {
            // an open value with its type only: any value of the type (it
            // stays a parameter; the typing a condition)
            if let Node::Var(v, va) = x[0].node() {
                if va.is_empty() && self.us.contains(v) && !br.a.iter().any(|(w, _)| w == v) && !self.open(&x[1], &br.a) {
                    let mut b = br;
                    b.a.push((*v, x[0].clone()));
                    b.conds.push(p.clone());
                    return Ok(vec![b]);
                }
            }
        }
        if s.unfold.contains(&f) {
            if let Some(u) = sp.unfold(f, x) {
                return self.solve(&u, br);
            }
        }
        if is(f, s.letin) {
            let v = sp.term(&x[0]);
            return self.solve(&inst_k(sp.env, &x[1], &[v]), br);
        }
        if !self.open(&p, &br.a) {
            return Ok(self.with_cond(&p, br));
        }
        if matches!(sp.env.syms[f as usize].kind, SymKind::Defined { .. }) && !is(f, s.mkprog) {
            if let Some(u) = sp.unfold(f, x) {
                return self.solve(&u, br);
            }
        }
        let q = sp.prop(&p, Pol::Other);
        if q != p {
            return self.solve(&q, br);
        }
        err(format!("{}{}", UNSOLVED, self.show(&p)))
    }

    /// A loop `while_rel(l0, l. C, l o. B, l. T, r)` from a known state, an
    /// iteration at a time (as simp's `unroll`, resting on the open lemmas
    /// of core/loop.core): C(l0) false -- it stops, r = ok(l0, empty)
    /// (`while_stop`); true -- the body's branches from l0: one that leaves
    /// is r (`while_leave`), one that goes on to l1 runs the loop from l1
    /// (`while_step`; a divergence after a step is not derived). A C(l0)
    /// the branch does not decide splits it.
    fn run_loop(&mut self, a: &[Term], br: Br) -> Result<Vec<Br>, String> {
        let sp = self.sp;
        let s = &sp.s;
        let empty = Term::app(s.empty.unwrap(), vec![]);
        let used = |n: &str| {
            let mut u = self.lg.simp_used.borrow_mut();
            if !u.iter().any(|m| m == n) {
                u.push(n.into());
            }
        };
        used("while_stop");
        used("while_leave");
        used("while_step");
        let r = a[4].clone();
        let mut out = Vec::new();
        // (state, branch, iterations so far)
        let mut work = vec![(sp.term(&self.subst(&a[0], &br.a)), br, 0usize)];
        while let Some((l0, br, k)) = work.pop() {
            if self.fuel == 0 {
                return err("the program's search ran out of fuel (a loop)");
            }
            self.fuel -= 1;
            let c = sp.prop(&inst_k(sp.env, &a[1], &[l0.clone()]), Pol::Other);
            let cases: Vec<(bool, Br)> = match self.decide(&c, &br) {
                Some(v) => vec![(v, br)],
                None => {
                    let mut v: Vec<(bool, Br)> = self.with_cond(&c, br.clone()).into_iter().map(|b| (true, b)).collect();
                    v.extend(self.with_cond(&sp.not(c.clone()), br).into_iter().map(|b| (false, b)));
                    v
                }
            };
            for (cv, b) in cases {
                if !cv {
                    let mut b = b;
                    let stop = Term::app(s.ok.unwrap(), vec![l0.clone(), empty.clone()]);
                    if self.unify(&r, &stop, &mut b)? == Some(true) {
                        out.push(b);
                    }
                    continue;
                }
                let (_, xo) = self.unknown();
                let body = inst_k(sp.env, &a[2], &[l0.clone(), xo.clone()]);
                for mut bb in self.solve(&body, b)? {
                    let o = sp.term(&self.subst(&xo, &bb.a));
                    match o.node() {
                        Node::App(g, oa) if is(*g, s.ok) && oa.len() == 2 && sp.is_true(&sp.prop(&Term::app(s.eq, vec![oa[1].clone(), empty.clone()]), Pol::Other)) => {
                            work.push((oa[0].clone(), bb, k + 1));
                        }
                        Node::App(g, _) if is(*g, s.exc) || (is(*g, s.diverge) && k == 0) => {
                            if self.unify(&r, &o, &mut bb)? == Some(true) {
                                out.push(bb);
                            }
                        }
                        Node::App(g, _) if is(*g, s.diverge) => {}
                        _ => return err(format!("{}a loop's body outcome {}", UNSOLVED, self.show(&o))),
                    }
                }
            }
        }
        Ok(out)
    }

    /// A loop `while_rel(l0, l. C, l o. B, l. T, r)` by the invariant P and
    /// variant m (the hint): P(l0) a condition; the body run once from a
    /// state lv with P(lv) and C(lv); the obligations of `while_exists`
    /// (core/loop.core) -- m(lv) a natural, each body branch that continues
    /// to l2 giving P(l2) and m(l2) < m(lv), the body's branches covering
    /// P(lv) && C(lv) -- decided, or kept for the statement (closed in lv).
    /// The loop's outcome: the state lv where C fails (r = ok(lv, empty)),
    /// or a body branch that leaves (r its outcome, lv where it does), lv
    /// existential in the statement (`while_exists` with g: the body's
    /// branches that leave). The branches go on after the loop from there,
    /// marked with the loop's group and exit.
    fn run_loop_inv(&mut self, a: &[Term], br: Br) -> Result<Vec<Br>, String> {
        let sp = self.sp;
        let s = &sp.s;
        let env = sp.env;
        if std::env::var("SPEC_DEBUG").is_ok() {
            eprintln!("spec_run: loop at {} (group {:?}), raw {}", self.show(&self.subst(&a[0], &br.a)), br.group, self.show(&a[0]));
            let mut vs = Vec::new();
            a[0].vars(&mut vs);
            for v in vs {
                if let Some((_, x)) = br.a.iter().find(|(w, _)| *w == v) {
                    eprintln!("    ?v{} := {}", v, self.show(x));
                }
            }
        }
        if br.group.is_some() {
            return err(format!("{}a loop past a loop run by its invariant (not supported yet)", UNSOLVED));
        }
        if self.hints.len() != 1 {
            return err("one loop invariant and variant: more loops by invariants are not supported yet");
        }
        let (inv, var) = self.hints[0].clone();
        for n in ["while_stop", "while_leave", "while_step"] {
            let mut u = self.lg.simp_used.borrow_mut();
            if !u.iter().any(|m| m == n) {
                u.push(n.into());
            }
        }
        let empty = Term::app(s.empty.unwrap(), vec![]);
        let at = |t: &Term, l: &Term| sp.prop(&inst_k(env, t, &[l.clone()]), Pol::Other);
        // the entry: P(l0)
        let l0 = sp.term(&self.subst(&a[0], &br.a));
        let p0 = at(&inv, &l0);
        let Some(b0) = self.with_cond(&p0, br).pop() else {
            return err(format!("the loop's invariant fails at its entry: {}", self.show(&p0)));
        };
        let pre = b0.conds.clone();
        if std::env::var("SPEC_DEBUG").is_ok() {
            eprintln!("spec_run: loop group {} pre {:?}", self.groups.len(), pre.iter().map(|c| self.show(&self.subst(c, &b0.a))).collect::<Vec<_>>());
        }
        // the state lv, any with P and C -- of l0's shape: a pair of fresh
        // variables for a pair (`while_exists` with the invariant `l is a
        // pair of that shape && P(l)`: l0 is one, each state the body goes
        // on to is checked to be one)
        let mut lv_ids: Vec<VarId> = Vec::new();
        let lv = self.shaped(&l0, &mut lv_ids);
        let pl = at(&inv, &lv);
        let cl = at(&a[1], &lv);
        let ml = inst_k(env, &var, &[lv.clone()]);
        let ctx0: Vec<Term> = self.facts.iter().chain(&pre).cloned().collect();
        let mut hyps = Vec::new();
        let omega = Term::app(s.omega.ok_or("no omega")?, vec![]);
        let in_ = s.in_.unwrap();
        self.obligation(&ctx0, &[pl.clone()], &Term::app(in_, vec![ml.clone(), omega]), &lv_ids, &mut hyps);
        // the body, once
        let (_, xo) = self.unknown();
        let body = inst_k(env, &a[2], &[lv.clone(), xo.clone()]);
        let mut start = b0.clone();
        start.conds.push(pl.clone());
        if !sp.is_true(&cl) {
            start.conds.push(cl.clone());
        }
        let lt = env.sym_by_name.get("int_lt").copied().ok_or("no int_lt")?;
        let mut cover: Vec<Term> = Vec::new();
        let mut leaves: Vec<(Vec<Term>, Br, Term)> = Vec::new();
        // (in word form under P(lv) and C(lv), which hold on each of the
        // body's paths: a value P bounds read as such)
        let mut lctx = ctx0.clone();
        sp.conjuncts(&pl, &mut lctx);
        sp.conjuncts(&cl, &mut lctx);
        for bb in self.solve(&body, start.clone())? {
            sp.set_nats(&lctx);
            let o = sp.term(&self.word(&lctx, &self.subst(&xo, &bb.a)));
            // (a divergence of the body is no exit `while_exists` takes:
            // left out, its case covered by the other branches or not)
            if matches!(o.node(), Node::App(g, _) if is(*g, s.diverge)) {
                continue;
            }
            let mut new: Vec<Term> = Vec::new();
            let mut dead = false;
            for c in bb.conds.iter().filter(|c| !start.conds.contains(c)) {
                sp.set_nats(&lctx);
                let mut xs = Vec::new();
                sp.conjuncts(&sp.prop(&self.word(&lctx, &self.subst(c, &bb.a)), Pol::Other), &mut xs);
                for x in xs {
                    if sp.is_true(&x) || new.contains(&x) || lctx.contains(&x) || sp.typed(&lctx, &x) {
                        continue;
                    }
                    match self.decide_in(&lctx, &x, 1) {
                        Some(true) => {}
                        Some(false) => dead = true,
                        None => new.push(x),
                    }
                }
            }
            // (a branch P(lv) and C(lv) rule out: not taken)
            if dead {
                continue;
            }
            // (the outcome in word form under the branch's conditions too:
            // the bounds of its path)
            let mut octx = lctx.clone();
            for c in &new {
                sp.conjuncts(c, &mut octx);
            }
            sp.set_nats(&octx);
            let o = sp.term(&self.word(&octx, &o));
            let core: Vec<Term> = new.iter().filter(|c| !self.param_typing(c, &lv_ids)).cloned().collect();
            cover.push(core.iter().cloned().reduce(|x, y| sp.and(x, y)).unwrap_or_else(|| sp.tt()));
            match o.node() {
                Node::App(g, oa) if is(*g, s.ok) && oa.len() == 2 && oa[1] == empty => {
                    // continues: P(l2), m(l2) < m(lv) -- l2 of the state's shape
                    let l2 = oa[0].clone();
                    if !Self::same_shape(sp, &lv, &l2) {
                        return err(format!("the loop's body goes on to a state not of its entry's shape: {}", self.show(&l2)));
                    }
                    let goal = sp.and(at(&inv, &l2), Term::app(lt, vec![inst_k(env, &var, &[l2.clone()]), ml.clone()]));
                    let mut ants = vec![pl.clone(), cl.clone()];
                    ants.extend(new.iter().cloned());
                    self.obligation(&ctx0, &ants, &goal, &lv_ids, &mut hyps);
                }
                Node::App(g, _) if is(*g, s.exc) => leaves.push((new, bb, o)),
                _ => return err(format!("a loop's body outcome other than ok or an exception: {}", self.show(&o))),
            }
        }
        // the body's branches cover P(lv) && C(lv)
        let any = cover.into_iter().reduce(|x, y| sp.or(x, y)).unwrap_or_else(|| sp.ff());
        self.obligation(&ctx0, &[pl.clone(), cl.clone()], &any, &lv_ids, &mut hyps);
        // the exits
        let gid = self.groups.len();
        let mut exits: Vec<Vec<Term>> = Vec::new();
        let mut out = Vec::new();
        let mut cx: Vec<Term> = ctx0.clone();
        cx.push(pl.clone());
        if self.decide_in(&cx, &cl, 2) != Some(true) {
            let d = vec![pl.clone(), sp.prop(&sp.not(cl.clone()), Pol::Other)];
            let mut b = b0.clone();
            b.conds.extend(d.iter().cloned());
            if self.unify(&a[4], &Term::app(s.ok.unwrap(), vec![lv.clone(), empty.clone()]), &mut b)? == Some(true) {
                b.group = Some((gid, exits.len()));
                exits.push(d);
                out.push(b);
            }
        }
        for (new, mut bb, o) in leaves {
            let mut d = vec![pl.clone()];
            if !sp.is_true(&cl) {
                d.push(cl.clone());
            }
            d.extend(new);
            if self.unify(&a[4], &o, &mut bb)? == Some(true) {
                bb.group = Some((gid, exits.len()));
                exits.push(d);
                out.push(bb);
            }
        }
        self.groups.push(Group { pre, hyps, lv: lv_ids, exits });
        Ok(out)
    }

    /// A state of t's shape: a pair of such states for a pair, else a fresh
    /// variable (pushed to vs).
    fn shaped(&mut self, t: &Term, vs: &mut Vec<VarId>) -> Term {
        let pair = self.sp.s.pair.unwrap();
        match t.node() {
            Node::App(p, x) if *p == pair && x.len() == 2 => {
                let a = self.shaped(&x[0], vs);
                let b = self.shaped(&x[1], vs);
                Term::app(pair, vec![a, b])
            }
            _ => {
                let (v, t) = self.var();
                vs.push(v);
                t
            }
        }
    }

    /// t has the pairs `shape` has (where shape is a pair, t is one).
    fn same_shape(sp: &Simp, shape: &Term, t: &Term) -> bool {
        let pair = sp.s.pair.unwrap();
        match (shape.node(), t.node()) {
            (Node::App(p, x), Node::App(q, y)) if *p == pair && x.len() == 2 => *q == pair && y.len() == 2 && Self::same_shape(sp, &x[0], &y[0]) && Self::same_shape(sp, &x[1], &y[1]),
            (Node::App(p, _), _) if *p == pair => false,
            _ => true,
        }
    }

    /// An obligation `all lv. A.. -> G` (lv the loop's state): decided in
    /// the context with the A's, or kept.
    fn obligation(&self, ctx: &[Term], ants: &[Term], goal: &Term, lv: &[VarId], hyps: &mut Vec<Term>) {
        let t0 = std::time::Instant::now();
        let how = self.obligation_with(ctx, ants, goal, lv, hyps);
        if std::env::var("SPEC_DEBUG").is_ok() {
            eprintln!("spec_run: obligation {} in {:?}", how, t0.elapsed());
        }
    }

    fn obligation_with(&self, ctx: &[Term], ants: &[Term], goal: &Term, lv: &[VarId], hyps: &mut Vec<Term>) -> &'static str {
        let sp = self.sp;
        let mut cx = ctx.to_vec();
        for a in ants {
            sp.conjuncts(a, &mut cx);
        }
        if self.decide_in(&cx, goal, 2) == Some(true) {
            return "decided";
        }
        // (vacuous: an antecedent the others refute)
        for k in ctx.len()..cx.len() {
            let others: Vec<Term> = cx.iter().enumerate().filter(|(j, _)| *j != k).map(|(_, t)| t.clone()).collect();
            if self.decide_in(&others, &cx[k], 1) == Some(false) {
                return "vacuous";
            }
        }
        let mut t = goal.clone();
        for a in ants.iter().rev().filter(|a| !sp.is_true(a)) {
            t = Term::app(sp.env.builtins.imp, vec![a.clone(), t]);
        }
        let t = bind_vars(self.lg.all, &t, lv, &sp.env.binders_fn());
        // (by simp, from the premises -- the user's lemmas about the loop --
        // and the conditions on the way; opened: lv's variables fresh, the
        // antecedents premises)
        let mut ps = self.premises.clone();
        ps.extend(ctx.iter().cloned());
        ps.extend(ants.iter().filter(|a| !sp.is_true(a)).cloned());
        if self.lg.simp_prove_loops(sp.env, &ps, goal, &[]).is_ok() {
            return "by simp";
        }
        if !hyps.contains(&t) {
            hyps.push(t);
        }
        "kept"
    }

    /// `x in S` for a parameter x (not the loop's state) of an inhabited
    /// type: a universe or words (its typing, stated outside)
    fn param_typing(&self, c: &Term, lv: &[VarId]) -> bool {
        let sp = self.sp;
        match c.node() {
            Node::App(i, ab) if is(*i, sp.s.in_) && ab.len() == 2 => {
                let param = matches!(ab[0].node(), Node::Var(v, va) if va.is_empty() && !lv.contains(v) && self.us.contains(v));
                let inhabited = matches!(ab[1].node(), Node::App(u, _) if is(*u, sp.s.univ) || Some(*u) == sp.env.sym_by_name.get("bits").copied());
                param && inhabited && !lv.iter().any(|v| has_var(&ab[1], *v))
            }
            _ => false,
        }
    }

    /// The pattern (with unknowns) matched against a value: constructors
    /// argument by argument, an unknown bound. None: undecided.
    fn unify(&mut self, pat: &Term, v: &Term, b: &mut Br) -> Result<Option<bool>, String> {
        let pat = self.proj_norm(&self.subst(pat, &b.a));
        if !self.open(&pat, &b.a) {
            let e = Term::app(self.sp.s.eq, vec![pat, v.clone()]);
            return Ok(match self.decide(&e, b) {
                Some(r) => Some(r),
                None => {
                    b.conds.push(self.sp.prop(&e, Pol::Other));
                    Some(true)
                }
            });
        }
        if let Node::Var(w, args) = pat.node() {
            if args.is_empty() && self.us.contains(w) && !b.a.iter().any(|(x, _)| x == w) {
                b.a.push((*w, v.clone()));
                return Ok(Some(true));
            }
        }
        let s = &self.sp.s;
        // (outcomes and tags are pairs: compared as such)
        let as_pair = |t: &Term| -> Option<Vec<Term>> {
            match t.node() {
                Node::App(g, x) if is(*g, s.pair) => Some(x.to_vec()),
                Node::App(g, x) if is(*g, s.tag) => Some(x.to_vec()),
                Node::App(g, x) if is(*g, s.ok) || is(*g, s.exc) => {
                    let k = if is(*g, s.ok) { 0 } else { 1 };
                    Some(vec![Term::nat(crate::nat::Nat::from_u64(k)), Term::app(s.pair.unwrap(), x.to_vec())])
                }
                Node::App(g, x) if is(*g, s.diverge) => Some(vec![Term::nat(crate::nat::Nat::from_u64(2)), x[0].clone()]),
                _ => None,
            }
        };
        let (Some(ap), Some(av)) = (as_pair(&pat), as_pair(v)) else { return Ok(None) };
        for (x, y) in ap.iter().zip(&av) {
            match self.unify(x, y, b)? {
                Some(true) => {}
                r => return Ok(r),
            }
        }
        Ok(Some(true))
    }

    /// `runs(q, st, out)` (q and st closed): by the lemmas for q's operation,
    /// else by q's definition.
    fn run(&mut self, q: &Term, st: &Term, out: &Term, br: Br) -> Result<Vec<Br>, String> {
        let sp = self.sp;
        let q = sp.term(q);
        let st = sp.term(st);
        // the operation's lemmas
        let mut found = false;
        let mut res = Vec::new();
        for l in self.lemmas.clone() {
            let mut vs = Vec::new();
            let mut t = l.clone();
            while let Node::App(a, b) = t.node() {
                if *a != self.lg.all {
                    break;
                }
                let (v, vt) = self.var();
                vs.push(v);
                t = inst_k(sp.env, &b[0], &[vt]);
            }
            let mut hyps = Vec::new();
            while let Node::App(i, ab) = t.node() {
                if *i != sp.env.builtins.imp {
                    break;
                }
                hyps.push(ab[0].clone());
                t = ab[1].clone();
            }
            let Node::App(r, ra) = t.node() else { continue };
            if !is(*r, sp.s.runs) {
                continue;
            }
            let mut binds = Vec::new();
            if !(pmatch(&ra[0], &q, &vs, &mut binds) && pmatch(&ra[1], &st, &vs, &mut binds)) {
                continue;
            }
            found = true;
            // (values only its outcome has, an undefined behaviour's
            // exception: open, parameters of the branch)
            for v in &vs {
                if !binds.iter().any(|(w, _)| w == v) {
                    let (_, u) = self.unknown();
                    binds.push((*v, u));
                }
            }
            let bf = sp.env.binders_fn();
            let close = |t: &Term| {
                let mut t = t.clone();
                for (v, x) in &binds {
                    t = t.subst_var(*v, x, &bf);
                }
                t
            };
            let lo = sp.term(&close(&ra[2]));
            let mut b = br.clone();
            match self.unify(out, &lo, &mut b)? {
                Some(true) => {}
                _ => continue,
            }
            let mut bs = vec![b];
            for h in &hyps {
                let h = sp.prop(&close(h), Pol::Other);
                bs = bs.into_iter().flat_map(|b| self.with_cond(&h, b)).collect();
            }
            res.extend(bs);
        }
        if found {
            return Ok(res);
        }
        // the program's definition: its relation, and the pair in univ(1)
        let mut p = q.clone();
        for _ in 0..8 {
            match p.node() {
                Node::App(m, _) if is(*m, sp.s.mkprog) => break,
                // a built function's program for an argument in its domain
                Node::App(ap, b) if is(*ap, sp.s.app) && b.len() == 2 => {
                    let mut f = b[0].clone();
                    for _ in 0..4 {
                        match f.node() {
                            Node::App(g, x) if !is(*g, sp.s.fn_build) && matches!(sp.env.syms[*g as usize].kind, SymKind::Defined { .. }) => match sp.unfold(*g, x) {
                                Some(u) => f = u,
                                None => break,
                            },
                            _ => break,
                        }
                    }
                    let Node::App(fb, fx) = f.node() else { return err(format!("not a program: {} ({})", self.show(&q), self.show(&f))) };
                    if !is(*fb, sp.s.fn_build) || fx.len() != 2 {
                        return err(format!("not a program: {} ({})", self.show(&q), self.show(&f)));
                    }
                    let mem = Term::app(sp.s.in_.unwrap(), vec![b[1].clone(), fx[0].clone()]);
                    if self.decide(&mem, &br) != Some(true) {
                        return err(format!("the argument not shown in the domain: {}", self.show(&mem)));
                    }
                    p = sp.term(&inst_k(sp.env, &fx[1], &[b[1].clone()]));
                }
                Node::App(g, b) if matches!(sp.env.syms[*g as usize].kind, SymKind::Defined { .. }) => match sp.unfold(*g, b) {
                    Some(u) => p = sp.term(&u),
                    None => return err(format!("not a program: {}", self.show(&q))),
                },
                _ => return err(format!("not a program (and no lemma for it): {}", self.show(&q))),
            }
        }
        let Node::App(m, r) = p.node() else { return err("not a program") };
        if !is(*m, sp.s.mkprog) {
            return err(format!("not a program: {}", self.show(&q)));
        }
        let rel = inst_k(sp.env, &r[0], &[st.clone(), out.clone()]);
        let mut res = Vec::new();
        // (an operation of the GIMPLE layer: its loops -- over an access's
        // bytes -- are unrolled, the invariants are for the program's own)
        let op = matches!(q.node(), Node::App(g, _) if sp.env.syms[*g as usize].name.starts_with("gimple."));
        self.op_depth += op as usize;
        let solved = self.solve(&rel, br);
        self.op_depth -= op as usize;
        for b in solved? {
            let o = self.subst(out, &b.a);
            let mem = Term::app(sp.s.in_.unwrap(), vec![Term::app(sp.s.pair.unwrap(), vec![st.clone(), o]), Term::app(sp.s.univ.unwrap(), vec![Term::nat(crate::nat::Nat::from_u64(1))])]);
            res.extend(self.with_cond(&mem, b));
        }
        Ok(res)
    }
}

/// spec_run's result: the statement, and for the bridge its parts -- the
/// branches not past a loop (their conditions and outcome, the parameters
/// `>= first` universal), and D, the condition whose failure is the
/// merged undefined behaviour (the spec raising from any world)
pub(super) struct SpecOut {
    pub statement: Term,
    pub branches: Vec<(Vec<Term>, Term)>,
    pub ub: Option<Term>,
    pub first: u32,
}

impl Logic {
    /// The branches of the program `p` run from the world `w` (see the
    /// module): `all ps. C.. -> runs(p, w, O)` per branch, conjoined.
    pub fn spec_run(&self, env: &Env, p: &Term, w: &Term, hints: &[(Term, Term)], premises: &[Term]) -> KResult<Term> {
        Ok(self.spec_run_out(env, p, w, hints, premises)?.statement)
    }

    pub(super) fn spec_run_out(&self, env: &Env, p: &Term, w: &Term, hints: &[(Term, Term)], premises: &[Term]) -> KResult<SpecOut> {
        *self.simp_rewrites.borrow_mut() = self.rewrite_rules(env, premises);
        let r = self.spec_run_with(env, p, w, hints, premises);
        self.simp_rewrites.borrow_mut().clear();
        r
    }

    fn spec_run_with(&self, env: &Env, p: &Term, w: &Term, hints: &[(Term, Term)], premises: &[Term]) -> KResult<SpecOut> {
        let kerr = |m: String| crate::env::KernelError(format!("spec_run: {}", m));
        let sp = Simp::new(env, self);
        let runs = sp.s.runs.ok_or_else(|| kerr("no `runs`".into()))?;
        // the operations' lemmas (`all xs. .. -> runs(Q, s, O)`), the facts
        let mut lemmas = Vec::new();
        let mut facts = Vec::new();
        for t in premises {
            let mut c = t.clone();
            let mut quantified = false;
            while let Node::App(a, b) = c.node() {
                if *a != self.all {
                    break;
                }
                quantified = true;
                c = b[0].clone();
            }
            while let Node::App(i, ab) = c.node() {
                if *i != env.builtins.imp {
                    break;
                }
                c = ab[1].clone();
            }
            if quantified && matches!(c.node(), Node::App(r, _) if *r == runs) {
                lemmas.push(t.clone());
            } else {
                sp.conjuncts(&self.simp_fact(env, t), &mut facts);
            }
        }
        let mut fresh = env.vars.len() as u32 + 4_000_000;
        for t in premises.iter().chain([p, w]).chain(hints.iter().flat_map(|(i, m)| [i, m])) {
            fresh = fresh.max(max_var(t) + 1);
        }
        let first = fresh;
        let mut sr = Sr { sp: &sp, lg: self, facts, lemmas, fresh, us: Default::default(), fuel: FUEL, depth: 0, hints: hints.to_vec(), groups: Vec::new(), op_depth: 0, premises: premises.to_vec() };
        let (_, ot) = sr.unknown();
        let t0 = std::time::Instant::now();
        let bs = sr.run(p, w, &ot, Br::default()).map_err(kerr)?;
        if std::env::var("SPEC_DEBUG").is_ok() {
            eprintln!("spec_run: {} branches in {:?}", bs.len(), t0.elapsed());
        }
        if bs.is_empty() {
            return Err(kerr("no branch of the program found".into()));
        }
        let bf = env.binders_fn();
        // each branch: its conditions, in word form, and its outcome
        let mut done: Vec<(Vec<Term>, Term)> = Vec::new();
        for b in &bs {
            // (the conditions in word form, by conjuncts, those the facts
            // show dropped)
            let mut conds: Vec<Term> = Vec::new();
            for c in &b.conds {
                let mut cs = Vec::new();
                sp.set_nats(&sr.facts);
                sp.conjuncts(&sp.prop(&sr.word(&sr.facts, &sr.subst(c, &b.a)), Pol::Other), &mut cs);
                for c in cs {
                    if !conds.contains(&c) {
                        conds.push(c);
                    }
                }
            }
            // (each in the context of the others: a value it reads known)
            let mut kept: Vec<Term> = Vec::new();
            for i in 0..conds.len() {
                let ctx: Vec<Term> = sr.facts.iter().chain(&kept).chain(&conds[i + 1..]).cloned().collect();
                sp.set_nats(&ctx);
                let c = sp.prop(&sr.word(&ctx, &conds[i]), Pol::Other);
                let mut cs = Vec::new();
                sp.conjuncts(&c, &mut cs);
                for c in cs {
                    if !(sp.is_true(&c) || kept.contains(&c) || sr.facts.contains(&c) || sp.typed(&ctx, &c) || self.symex_decide(&sp, &sr.facts, &c) == Some(true)) {
                        kept.push(c);
                    }
                }
            }
            let ctx: Vec<Term> = sr.facts.iter().chain(&kept).cloned().collect();
            sp.set_nats(&ctx);
            let o = sr.word(&ctx, &sr.subst(&ot, &b.a));
            // (a parameter only typed as a word: 0)
            let unused = |v: VarId| {
                let x = Term::var(v, vec![]);
                let occurs = |t: &Term| has_var(t, v);
                !occurs(&o)
                    && kept.iter().all(|c| {
                        !occurs(c) || matches!(c.node(), Node::App(i, ab) if is(*i, sp.s.in_) && ab[0] == x && matches!(ab[1].node(), Node::App(bt, _) if Some(*bt) == env.sym_by_name.get("bits").copied()))
                    })
            };
            let mut vs = Vec::new();
            for c in &kept {
                c.vars(&mut vs);
            }
            vs.retain(|v| *v >= first && unused(*v));
            kept.retain(|c| !vs.iter().any(|v| has_var(c, *v)));
            done.push((kept, o));
        }
        // the branches of undefined behaviour, `C.. -> runs(P, W, exc(S,
        // x))` for any x in univ(1) (or any outcome x), stated together:
        // `all e. e in univ(1) -> !D -> runs(P, W, exc(S, e))` with D the
        // conjunction of their `C1 -> .. -> !Cn` (D fails: one of them
        // holds)
        let param = |t: &Term| match t.node() {
            Node::Var(v, a) if a.is_empty() && *v >= first => Some(*v),
            _ => None,
        };
        // (the conditions without the parameter's typing, and that typing's set)
        let strip = |conds: &[Term], x: VarId| -> Option<(Vec<Term>, Option<Term>)> {
            let mut rest = Vec::new();
            let mut set = None;
            for c in conds {
                if !has_var(c, x) {
                    rest.push(c.clone());
                    continue;
                }
                match c.node() {
                    Node::App(i, ab) if is(*i, sp.s.in_) && param(&ab[0]) == Some(x) && !has_var(&ab[1], x) => set = Some(ab[1].clone()),
                    _ => return None,
                }
            }
            Some((rest, set))
        };
        let mut ub: Vec<(usize, Vec<Term>, bool)> = Vec::new();
        let mut any: Vec<(usize, Vec<Term>, Option<Term>)> = Vec::new();
        // (the exception's world: a common one, or any -- a parameter, as
        // undefined behaviour leaves it)
        let mut state: Option<Term> = None;
        let mut set: Option<Term> = None;
        let mut same = true;
        for (i, (kept, o)) in done.iter().enumerate() {
            if bs[i].group.is_some() {
                continue;
            }
            match o.node() {
                Node::App(ex, ab) if Some(*ex) == sp.s.exc && ab.len() == 2 => {
                    let Some(x) = param(&ab[1]) else { continue };
                    if has_var(&ab[0], x) {
                        continue;
                    }
                    let Some((rest, s)) = strip(kept, x) else { continue };
                    let (rest, free) = match param(&ab[0]) {
                        Some(y) => match strip(&rest, y) {
                            Some((r, sy)) if sy.is_some() && (s.is_none() || sy == s) => (r, true),
                            _ => continue,
                        },
                        None => (rest, false),
                    };
                    if !free {
                        same &= state.as_ref().is_none_or(|t| *t == ab[0]);
                        state = Some(ab[0].clone());
                    }
                    same &= set.is_none() || s.is_none() || set == s;
                    set = set.or(s);
                    ub.push((i, rest, free));
                }
                Node::Var(..) => {
                    if let Some(x) = param(o) {
                        if let Some((rest, s)) = strip(kept, x) {
                            any.push((i, rest, s));
                        }
                    }
                }
                _ => {}
            }
        }
        let mut merged: Option<Term> = None;
        let mut ub_d: Option<Term> = None;
        let mut gone: Vec<usize> = Vec::new();
        if let (true, Some(set)) = (same && !ub.is_empty(), set) {
            let in_ = sp.s.in_.unwrap();
            let univ = matches!(set.node(), Node::App(u, _) if is(*u, sp.s.univ));
            // the world: the common one, or (all branches leaving it open)
            // a parameter in the set
            let (s, s_cond) = match state {
                Some(s) => (s, None),
                None => {
                    let (_, st) = sr.var();
                    (st.clone(), Some(Term::app(in_, vec![st, set.clone()])))
                }
            };
            // (exc(S, e) is an outcome of a branch leaving the world open,
            // or any outcome, when S is in the set, a universe)
            let s_ok = univ && (s_cond.is_some() || sp.typed(&sr.facts, &Term::app(in_, vec![s.clone(), set.clone()])) || sr.facts.contains(&Term::app(in_, vec![s.clone(), set.clone()])));
            let mut all_ub: Vec<(usize, Vec<Term>)> = ub.iter().filter(|(_, _, free)| !free || s_ok).map(|(i, r, _)| (*i, r.clone())).collect();
            if s_ok {
                all_ub.extend(any.iter().filter(|(_, _, s)| s.as_ref() == Some(&set)).map(|(i, r, _)| (*i, r.clone())));
            }
            let chain = |cs: &[Term]| -> Term {
                match cs.split_last() {
                    None => sp.ff(),
                    Some((last, init)) => init.iter().rev().fold(sp.prop(&sp.not(last.clone()), Pol::Other), |t, c| Term::app(env.builtins.imp, vec![c.clone(), t])),
                }
            };
            if let Some(d) = all_ub.iter().map(|(_, cs)| chain(cs)).reduce(|a, b| sp.and(a, b)) {
                // (for the bridge: D, when the raise is from any world)
                if s_cond.is_some() {
                    ub_d = Some(d.clone());
                }
                let (_, et) = sr.var();
                let mut t = Term::app(env.builtins.imp, vec![Term::app(in_, vec![et.clone(), set]), Term::app(env.builtins.imp, vec![sp.not(d), Term::app(runs, vec![p.clone(), w.clone(), Term::app(sp.s.exc.unwrap(), vec![s, et.clone()])])])]);
                if let Some(c) = s_cond {
                    t = Term::app(env.builtins.imp, vec![c, t]);
                }
                merged = Some(t);
                gone = all_ub.iter().map(|(i, _)| *i).collect();
            }
        }
        let and = sp.s.and.unwrap();
        let mut ts: Vec<Term> = Vec::new();
        for (i, (kept, o)) in done.iter().enumerate() {
            if gone.contains(&i) || bs[i].group.is_some() {
                continue;
            }
            let mut t = Term::app(runs, vec![p.clone(), w.clone(), o.clone()]);
            for c in kept.iter().rev() {
                t = Term::app(env.builtins.imp, vec![c.clone(), t]);
            }
            ts.push(t);
        }
        ts.extend(merged);
        // the branches past a loop run by its invariant, per loop:
        //   pre -> typing -> obligations -> (ex lv. D1 && runs(P, W, O1)) || ..
        // (`while_exists`: the loop has a run to one of its exits, from
        // there the program to one of the branches past that exit -- which
        // cover it, an obligation too)
        let imp = env.builtins.imp;
        for (gid, g) in sr.groups.iter().enumerate() {
            let members: Vec<usize> = (0..bs.len()).filter(|i| bs[*i].group.map(|x| x.0) == Some(gid)).collect();
            let norm = |cs: &[Term], a: &Assign| -> Vec<Term> {
                sp.set_nats(&sr.facts);
                let mut out = Vec::new();
                for c in cs {
                    let mut xs = Vec::new();
                    sp.conjuncts(&sp.prop(&sr.word(&sr.facts, &sr.subst(c, a)), Pol::Other), &mut xs);
                    for x in xs {
                        if !out.contains(&x) && !sp.is_true(&x) {
                            out.push(x);
                        }
                    }
                }
                out
            };
            let base_a = members.first().map(|i| bs[*i].a.clone()).unwrap_or_default();
            let pre = norm(&g.pre, &base_a);
            let conj = |cs: &[Term]| cs.iter().cloned().reduce(|x, y| sp.and(x, y)).unwrap_or_else(|| sp.tt());
            let mut typing: Vec<Term> = Vec::new();
            let mut disj: Vec<Term> = Vec::new();
            let mut post: Vec<Vec<Term>> = vec![Vec::new(); g.exits.len()];
            let mut exit_d: Vec<Option<Vec<Term>>> = vec![None; g.exits.len()];
            for &i in &members {
                let e = bs[i].group.unwrap().1;
                let dex = norm(&g.exits[e], &bs[i].a);
                // (the branch's conditions and outcome in word form, in the
                // context of the exit: its state's invariant known)
                let mut gctx: Vec<Term> = sr.facts.iter().chain(&pre).cloned().collect();
                for c in &dex {
                    sp.conjuncts(c, &mut gctx);
                }
                let mut kept: Vec<Term> = Vec::new();
                for c in &bs[i].conds {
                    sp.set_nats(&gctx);
                    let mut xs = Vec::new();
                    sp.conjuncts(&sp.prop(&sr.word(&gctx, &sr.subst(c, &bs[i].a)), Pol::Other), &mut xs);
                    for x in xs {
                        let implied = !dex.contains(&x) && (gctx.contains(&x) || sp.typed(&gctx, &x) || sr.decide_in(&gctx, &x, 1) == Some(true));
                        if !sp.is_true(&x) && !kept.contains(&x) && !implied {
                            kept.push(x);
                        }
                    }
                }
                sp.set_nats(&gctx);
                let o = &sr.word(&gctx, &sr.subst(&ot, &bs[i].a));
                let kept = &kept;
                let mut d = Vec::new();
                for c in kept {
                    if pre.contains(c) {
                        continue;
                    }
                    if sr.param_typing(c, &g.lv) {
                        if !typing.contains(c) {
                            typing.push(c.clone());
                        }
                        continue;
                    }
                    d.push(c.clone());
                }
                let after: Vec<Term> = d.iter().filter(|c| !dex.contains(c)).cloned().collect();
                post[e].push(conj(&after));
                exit_d[e].get_or_insert(dex);
                let body = sp.and(conj(&d), Term::app(runs, vec![p.clone(), w.clone(), o.clone()]));
                disj.push(bind_vars(self.ex, &body, &g.lv, &bf));
            }
            // (each exit covered by the branches past it)
            let mut hyps = g.hyps.clone();
            for (e, ps) in post.iter().enumerate() {
                let dex = exit_d[e].clone().unwrap_or_else(|| norm(&g.exits[e], &base_a));
                let goal = ps.iter().cloned().reduce(|x, y| sp.or(x, y)).unwrap_or_else(|| sp.ff());
                let ctx: Vec<Term> = sr.facts.iter().chain(&pre).chain(&dex).cloned().collect();
                if sr.decide_in(&ctx, &goal, 2) != Some(true) {
                    let t = Term::app(imp, vec![conj(&dex), goal]);
                    let t = bind_vars(self.all, &t, &g.lv, &bf);
                    if !hyps.contains(&t) {
                        hyps.push(t);
                    }
                }
            }
            let body = disj.into_iter().reduce(|x, y| sp.or(x, y)).unwrap_or_else(|| sp.ff());
            // (a parameter only typed, in a universe or words, and nowhere
            // else: dropped, as any value of its type would do)
            let conds: Vec<Term> = pre.iter().chain(&typing).chain(&hyps).cloned().collect();
            let only_typed = |c: &Term| {
                let Node::App(i, ab) = c.node() else { return false };
                if !is(*i, sp.s.in_) || ab.len() != 2 {
                    return false;
                }
                let Node::Var(v, va) = ab[0].node() else { return false };
                let inhabited = matches!(ab[1].node(), Node::App(u, _) if is(*u, sp.s.univ) || Some(*u) == env.sym_by_name.get("bits").copied());
                va.is_empty() && *v >= first && !g.lv.contains(v) && inhabited && !has_var(&body, *v) && conds.iter().filter(|d| has_var(d, *v)).count() == 1
            };
            let mut t = body.clone();
            for c in conds.iter().rev().filter(|c| !only_typed(c)) {
                t = Term::app(imp, vec![c.clone(), t]);
            }
            ts.push(t);
        }
        // (the values left open, among them an outcome undefined behaviour
        // leaves open: parameters)
        let ts: Vec<Term> = ts
            .into_iter()
            .map(|mut t| {
                let mut vs = Vec::new();
                t.vars(&mut vs);
                vs.retain(|v| *v >= first);
                vs.sort();
                vs.dedup();
                for v in vs.iter().rev() {
                    t = Term::app(self.all, vec![abstract_term(&t, &Term::var(*v, vec![]), 0, &bf)]);
                }
                t
            })
            .collect();
        let statement = ts.into_iter().rev().reduce(|r, t| Term::app(and, vec![t, r])).unwrap();
        let branches = done.into_iter().enumerate().filter(|(i, _)| bs[*i].group.is_none() && !gone.contains(i)).map(|(_, b)| b).collect();
        Ok(SpecOut { statement, branches, ub: ub_d, first })
    }
}
