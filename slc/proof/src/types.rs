//! `types(p1, ..)`: a membership goal `t in T` (or `k in dom(r)`,
//! `is_fun(r)`) by the forms of t and T -- determined, no search: each step
//! one lemma of core/sets.core and core/records.core.
//!
//! Inference (`infer`): t's set from the facts given and the block's facts
//! (their conjuncts too), from a record's field (the record type's
//! conjunct for it), a function's value (`fn_space(A, B)`), or an update of
//! a typed record (the record's type).
//!
//! Checking (`check`), by T's form:
//! * `univ(u)`: by t's form -- literals (`nat_univ0`, `bytes_univ`, raised
//!   by `univ_next`), `pair`, `upair`, `single`, `insert`, `union2`,
//!   `fn_update`, `tag`, `set_select`, `empty`, `app`, a defined head
//!   unfolded; else from t's inferred set (a word or natural: `nat_univ0`;
//!   a record: `rec_univ`; a function: `fn_space_univ`);
//! * a record type `set_select(powerset(cart(K, univ(u))), x. p)`: t's
//!   inferred type, or an update `fn_update(r, k, v)` of a record of it
//!   (`rec_type_intro`, the fields read through the update);
//! * `bits(n)`, `omega`, `int` and their subsets: arith, with the facts
//!   inferred for the goal's atoms;
//! * a defined T (a record type's name): unfolded.
//!
//! Untrusted: every step a kernel rule, a lemma's instance, `taut` or
//! `arith`.

use super::*;
use std::collections::HashMap;

/// (names of the symbols the rules look at)
struct Syms {
    in_: SymId,
    univ: SymId,
    set_select: SymId,
    powerset: SymId,
    cart: SymId,
    and: SymId,
    app: SymId,
    fn_update: SymId,
    fn_space: SymId,
    dom: SymId,
    is_fun: SymId,
    insert: SymId,
    eq: SymId,
}

pub(crate) struct Typer<'a> {
    st: &'a State,
    lg: &'a Logic,
    s: Syms,
    /// the facts: (conjunct, the fact it is a conjunct of, its path there)
    known: Vec<(Term, usize, Vec<bool>)>,
    facts: Vec<Seq>,
    /// a term's known memberships: indices into `known`
    by_term: HashMap<Term, Vec<usize>>,
    memo: HashMap<Term, Option<Seq>>,
    /// a record's type taken apart: `r in s && p(r)` by r's membership
    unsels: HashMap<Term, Seq>,
    depth: usize,
}

const MAX_DEPTH: usize = 60;

fn sym(env: &Env, n: &str) -> KResult<SymId> {
    env.sym_by_name.get(n).copied().ok_or_else(|| KernelError(format!("types: `{}` is not defined", n)))
}

/// `name`'s instance with its schematic variables bound by name
fn thm(env: &Env, name: &str, binds: &[(&str, &Term)]) -> KResult<Seq> {
    let mut s = facts::seq_of(env, name).ok_or_else(|| KernelError(format!("types: `{}` is not loaded", name)))?;
    let mut vs = Vec::new();
    s.concl().vars(&mut vs);
    for (n, t) in binds {
        let v = vs.iter().copied().find(|v| env.var(*v).name == *n).ok_or_else(|| KernelError(format!("types: `{}` has no `{}`", name, n)))?;
        s = Seq::inst(env, &s, v, t)?;
    }
    Ok(s)
}

/// a lemma's instance applied to its premises
fn use_thm(env: &Env, name: &str, binds: &[(&str, &Term)], prems: &[&Seq]) -> KResult<Seq> {
    let mut s = thm(env, name, binds)?;
    for p in prems {
        s = Seq::mp(env, &s, p)?;
    }
    Ok(s)
}

/// `!(a = b)` for distinct literals (numerals by arith; bytes literals by a
/// byte or their length: `bytes_at_ne`, `bytes_len_ne`)
pub(crate) fn lit_ne(env: &Env, lg: &Logic, a: &Term, b: &Term) -> Option<Seq> {
    let not = sym(env, "not").ok()?;
    let ne = |x: Term, y: Term| Term::app(not, vec![Term::app(env.builtins.eq, vec![x, y])]);
    match (a.node(), b.node()) {
        (Node::Nat(x), Node::Nat(y)) if x != y => Seq::arith(env, lg, &[], &ne(a.clone(), b.clone())).ok(),
        (Node::Bytes(x), Node::Bytes(y)) if x != y => {
            if x.len() != y.len() {
                let (la, lb) = (Seq::kernel(env.bytes_len(a)).ok()?, Seq::kernel(env.bytes_len(b)).ok()?);
                let len = |t: &Term| Term::app(env.builtins.bytes_len, vec![t.clone()]);
                let lens = Seq::arith(env, lg, &[&la, &lb], &ne(len(a), len(b))).ok()?;
                return use_thm(env, "bytes_len_ne", &[("a", a), ("b", b)], &[&lens]).ok();
            }
            let i = x.iter().zip(y.iter()).position(|(p, q)| p != q)?;
            let it = Term::nat(sl_kernel::Nat::from_u64(i as u64));
            let (ba, bb) = (Seq::kernel(env.bytes_at(a, &it)).ok()?, Seq::kernel(env.bytes_at(b, &it)).ok()?);
            let at = |t: &Term| Term::app(env.builtins.bytes_at, vec![t.clone(), it.clone()]);
            let bytes = Seq::arith(env, lg, &[&ba, &bb], &ne(at(a), at(b))).ok()?;
            use_thm(env, "bytes_at_ne", &[("a", a), ("b", b), ("i", &it)], &[&bytes]).ok()
        }
        _ => None,
    }
}

impl<'a> Typer<'a> {
    pub(crate) fn new(env: &Env, st: &'a State, lg: &'a Logic, given: &[Seq]) -> KResult<Typer<'a>> {
        let s = Syms {
            in_: sym(env, "in")?,
            univ: sym(env, "univ")?,
            set_select: sym(env, "set_select")?,
            powerset: sym(env, "powerset")?,
            cart: sym(env, "cart")?,
            and: sym(env, "and")?,
            app: sym(env, "app")?,
            fn_update: sym(env, "fn_update")?,
            fn_space: sym(env, "fn_space")?,
            dom: sym(env, "dom")?,
            is_fun: sym(env, "is_fun")?,
            insert: sym(env, "insert")?,
            eq: env.builtins.eq,
        };
        let mut t = Typer { st, lg, s, known: Vec::new(), facts: Vec::new(), by_term: HashMap::new(), memo: HashMap::new(), unsels: HashMap::new(), depth: 0 };
        // (the facts given first: they are found first)
        let block: Vec<Seq> = st.facts.iter().rev().map(|(_, f)| f.clone()).collect();
        for f in given.iter().cloned().chain(block) {
            t.add_fact(f);
        }
        Ok(t)
    }

    fn add_fact(&mut self, f: Seq) {
        let i = self.facts.len();
        let mut cs = Vec::new();
        self.conjuncts_at(f.concl(), &mut Vec::new(), &mut cs);
        self.facts.push(f);
        for (c, path) in cs {
            let k = self.known.len();
            if let Some(x) = self.subject(&c) {
                self.by_term.entry(x).or_default().push(k);
            }
            self.known.push((c, i, path));
        }
    }

    fn conjuncts(&self, t: &Term, out: &mut Vec<Term>) {
        match t.node() {
            Node::App(a, x) if *a == self.s.and => {
                self.conjuncts(&x[0], out);
                self.conjuncts(&x[1], out);
            }
            _ => out.push(t.clone()),
        }
    }

    /// the conjuncts with their paths (false: the left operand)
    fn conjuncts_at(&self, t: &Term, path: &mut Vec<bool>, out: &mut Vec<(Term, Vec<bool>)>) {
        match t.node() {
            Node::App(a, x) if *a == self.s.and => {
                path.push(false);
                self.conjuncts_at(&x[0], path, out);
                path.pop();
                path.push(true);
                self.conjuncts_at(&x[1], path, out);
                path.pop();
            }
            _ => out.push((t.clone(), path.clone())),
        }
    }

    /// the conjunct of s at `path`: and_left / and_right, one per level
    fn project(&self, env: &Env, s: &Seq, path: &[bool]) -> KResult<Seq> {
        let mut cur = s.clone();
        for &right in path {
            let (a, b) = match cur.concl().node() {
                Node::App(x, y) if *x == self.s.and => (y[0].clone(), y[1].clone()),
                _ => return err("types: not a conjunction"),
            };
            cur = use_thm(env, if right { "and_right" } else { "and_left" }, &[("a", &a), ("b", &b)], &[&cur])?;
        }
        Ok(cur)
    }

    /// the conjunct `want` of s, by its path
    fn conjunct(&self, env: &Env, s: &Seq, want: &Term) -> Option<Seq> {
        let mut cs = Vec::new();
        self.conjuncts_at(s.concl(), &mut Vec::new(), &mut cs);
        let (_, path) = cs.into_iter().find(|(c, _)| c == want)?;
        self.project(env, s, &path).ok()
    }

    /// every conjunct of s, proven
    fn split(&self, env: &Env, s: &Seq) -> Vec<Seq> {
        let mut cs = Vec::new();
        self.conjuncts_at(s.concl(), &mut Vec::new(), &mut cs);
        cs.into_iter().filter_map(|(_, p)| self.project(env, s, &p).ok()).collect()
    }

    /// the conjunction `target` from proofs of its conjuncts (and_intro)
    fn build(&self, env: &Env, target: &Term, have: &HashMap<Term, Seq>) -> Option<Seq> {
        if let Some(s) = have.get(target) {
            return Some(s.clone());
        }
        let (a, b) = match target.node() {
            Node::App(x, y) if *x == self.s.and => (y[0].clone(), y[1].clone()),
            _ => return None,
        };
        let pa = self.build(env, &a, have)?;
        let pb = self.build(env, &b, have)?;
        use_thm(env, "and_intro", &[("a", &a), ("b", &b)], &[&pa, &pb]).ok()
    }

    /// what a known fact is about: x of `x in T`, r of `is_fun(r)` and of
    /// `dom(r) = K`
    fn subject(&self, c: &Term) -> Option<Term> {
        match c.node() {
            Node::App(i, a) if *i == self.s.in_ => Some(a[0].clone()),
            Node::App(f, a) if *f == self.s.is_fun => Some(a[0].clone()),
            Node::App(e, a) if *e == self.s.eq => match a[0].node() {
                Node::App(d, b) if *d == self.s.dom => Some(b[0].clone()),
                // (an equation defining a term: `x = e`)
                _ => Some(a[0].clone()),
            },
            _ => None,
        }
    }

    /// a known equation `t = e` (e not t itself): e and its proof
    fn equation(&self, env: &Env, t: &Term) -> Option<(Term, Seq)> {
        let ks = self.by_term.get(t)?;
        for &k in ks {
            if let Some(a) = self.is(&self.known[k].0, self.s.eq) {
                if a[0] == *t && a[1] != *t && self.is(&a[0], self.s.dom).is_none() {
                    return Some((a[1].clone(), self.known_proof(env, k).ok()?));
                }
            }
        }
        None
    }

    /// the known conjunct k, proven
    fn known_proof(&self, env: &Env, k: usize) -> KResult<Seq> {
        let (_, i, path) = &self.known[k];
        self.project(env, &self.facts[*i], path)
    }

    fn mk(&self, s: SymId, args: Vec<Term>) -> Term {
        Term::app(s, args)
    }

    fn is(&self, t: &Term, s: SymId) -> Option<Vec<Term>> {
        match t.node() {
            Node::App(h, a) if *h == s => Some(a.to_vec()),
            _ => None,
        }
    }

    fn head_name<'e>(&self, env: &'e Env, t: &Term) -> Option<&'e str> {
        match t.node() {
            Node::App(h, _) => Some(env.syms[*h as usize].name.as_str()),
            _ => None,
        }
    }

    // -----------------------------------------------------------------
    //  The goal

    /// a proof of the goal (`t in T`, `k in dom(r)`, `is_fun(r)`)
    pub(crate) fn prove(&mut self, env: &mut Env, goal: &Term) -> KResult<Seq> {
        if let Some(a) = self.is(goal, self.s.in_) {
            if let Some(d) = self.is(&a[1], self.s.dom) {
                return self.in_dom(env, &a[0], &d[0]).ok_or_else(|| self.fail(env, goal));
            }
            return self.check(env, &a[0], &a[1]).ok_or_else(|| self.fail(env, goal));
        }
        if let Some(a) = self.is(goal, self.s.is_fun) {
            return self.rec_fact(env, &a[0], |c, s| c.is(s, c.s.is_fun).is_some()).ok_or_else(|| self.fail(env, goal));
        }
        err(format!("types: not a membership: {}", Printer::new(env).short(goal)))
    }

    fn fail(&self, env: &Env, goal: &Term) -> KernelError {
        KernelError(format!("types: not shown: {}", Printer::new(env).short(goal)))
    }

    // -----------------------------------------------------------------
    //  Checking

    /// `t in T`
    pub(crate) fn check(&mut self, env: &mut Env, t: &Term, set: &Term) -> Option<Seq> {
        let goal = self.mk(self.s.in_, vec![t.clone(), set.clone()]);
        if let Some(r) = self.memo.get(&goal) {
            return r.clone();
        }
        if self.depth > MAX_DEPTH {
            return None;
        }
        self.depth += 1;
        let r = self.check_(env, t, set, &goal);
        self.depth -= 1;
        // (TYPES_TRACE: the sub-goals not shown)
        if r.is_none() && std::env::var("TYPES_TRACE").is_ok() {
            eprintln!("types {:>2} not: {}", self.depth, Printer::new(env).short(&goal).chars().take(200).collect::<String>());
        }
        self.memo.insert(goal, r.clone());
        r
    }

    fn check_(&mut self, env: &mut Env, t: &Term, set: &Term, goal: &Term) -> Option<Seq> {
        // (known as it is)
        if let Some(ks) = self.by_term.get(t).cloned() {
            for k in ks {
                if self.known[k].0 == *goal {
                    return self.known_proof(env, k).ok();
                }
            }
        }
        // (t defined by a known equation `t = e`: e's)
        if let Some((e, eq)) = self.equation(env, t) {
            if let Some(p) = self.check(env, &e, set) {
                // (e back to t where the goal has t only -- not in the set)
                return Seq::rewrite_to(env, &Seq::sym(env, &eq).ok()?, &p, goal).ok();
            }
        }
        if let Some(u) = self.is(set, self.s.univ) {
            return self.univ(env, t, &u[0]);
        }
        // (an insert chain with t one of its elements: an enum's value)
        if self.is(set, self.s.insert).is_some() {
            if let Some(p) = self.in_set(env, t, set) {
                return Some(p);
            }
        }
        if self.rec_parts(set).is_some() {
            if let Some(p) = self.record(env, t, set) {
                return Some(p);
            }
        }
        // (a word operation: an n-bit word, n its width)
        if let (Some(w), Some(name)) = (self.is(set, sym(env, "bits").ok()?), self.head_name(env, t).map(|s| s.to_string())) {
            if let Some(p) = self.word_op(env, t, &name, &w[0]) {
                return Some(p);
            }
        }
        // (t's inferred set: the same)
        if let Some((ty, p)) = self.infer(env, t) {
            if ty == *set {
                return Some(p);
            }
            if let Ok(q) = self.same_set(env, &p, &ty, set) {
                return Some(q);
            }
        }
        // (a defined set, not one the rules know: unfolded)
        if let Some(name) = self.head_name(env, set) {
            if !["bits", "omega", "int", "fn_space", "univ", "set_select", "powerset", "cart", "dom", "insert"].contains(&name) {
                if let Some((u, d)) = unfold_head(env, set, false) {
                    let p = self.check(env, t, &u)?;
                    return Seq::conv(env, &p, goal, &[d]).ok();
                }
            }
        }
        // (numbers: arith, with the atoms' inferred sets)
        if let Some(name) = self.head_name(env, set) {
            if ["bits", "omega", "int"].contains(&name) || self.is(set, self.s.set_select).is_some() {
                return self.arith(env, goal);
            }
        }
        None
    }

    /// p: `t in ty`, and ty the same set as `set` after unfolding their
    /// defined heads
    fn same_set(&self, env: &Env, p: &Seq, ty: &Term, set: &Term) -> KResult<Seq> {
        let mut syms = Vec::new();
        for x in [ty, set] {
            let mut x = x.clone();
            while let Some((u, d)) = unfold_head(env, &x, false) {
                if !syms.contains(&d) {
                    syms.push(d);
                }
                x = u;
            }
        }
        if syms.is_empty() {
            return err("not the same set");
        }
        let goal = self.mk(self.s.in_, vec![p.concl().clone(), set.clone()]);
        let goal = match p.concl().node() {
            Node::App(_, a) => self.mk(self.s.in_, vec![a[0].clone(), set.clone()]),
            _ => goal,
        };
        Seq::conv(env, p, &goal, &syms)
    }

    // -----------------------------------------------------------------
    //  Universes

    /// `t in univ(u)`
    fn univ(&mut self, env: &mut Env, t: &Term, u: &Term) -> Option<Seq> {
        let un = |x: &Term| match x.node() {
            Node::Nat(n) => n.to_u64(),
            _ => None,
        };
        // (literals: from the least universe up)
        match t.node() {
            Node::Nat(_) => {
                let n = use_thm(env, "lit_nat", &[("n", t)], &[&Seq::kernel(env.lit_is_nat(t)).ok()?]).ok()?;
                let z = use_thm(env, "nat_univ0", &[("n", t)], &[&n]).ok()?;
                return self.raise(env, z, 0, un(u)?);
            }
            Node::Bytes(_) => {
                let z = use_thm(env, "bytes_univ", &[("b", t)], &[&Seq::kernel(env.lit_is_bytes(t)).ok()?]).ok()?;
                return self.raise(env, z, 0, un(u)?);
            }
            _ => {}
        }
        // (a proposition: prop_univ)
        if let Ok(ip) = Seq::prop(env, self.lg, t) {
            if let Ok(z) = use_thm(env, "prop_univ", &[("x", t)], &[&ip]) {
                return self.raise(env, z, 0, un(u)?);
            }
        }
        let name = self.head_name(env, t).map(|s| s.to_string());
        let args = match t.node() {
            Node::App(_, a) => a.to_vec(),
            _ => Vec::new(),
        };
        // (by the constructor: each argument a member)
        let by_args = |me: &mut Self, env: &mut Env, lemma: &str, names: &[&str]| -> Option<Seq> {
            let mut ps = Vec::new();
            for x in &args {
                ps.push(me.check(env, x, &Term::app(me.s.univ, vec![u.clone()]))?);
            }
            let mut binds: Vec<(&str, &Term)> = vec![("u", u)];
            for (n, x) in names.iter().zip(&args) {
                binds.push((n, x));
            }
            let refs: Vec<&Seq> = ps.iter().collect();
            use_thm(env, lemma, &binds, &refs).ok()
        };
        match name.as_deref() {
            Some("pair") => return by_args(self, env, "pair_univ", &["a", "b"]),
            Some("upair") => return by_args(self, env, "upair_univ", &["a", "b"]),
            Some("single") => return by_args(self, env, "single_univ", &["a"]),
            Some("insert") => return by_args(self, env, "insert_univ", &["a", "s"]),
            Some("union2") => return by_args(self, env, "union2_univ", &["a", "b"]),
            Some("fn_update") => return by_args(self, env, "fn_update_univ", &["f", "k", "v"]),
            Some("tag") => return by_args(self, env, "tag_univ", &["k", "v"]),
            Some("empty") => return thm(env, "univ_empty", &[("u", u)]).ok(),
            Some("set_select") => {
                let p = self.check(env, &args[0], &Term::app(self.s.univ, vec![u.clone()]))?;
                return use_thm(env, "select_univ", &[("u", u), ("s", &args[0]), ("p", &args[1])], &[&p]).ok();
            }
            Some("powerset") => {
                let p = self.check(env, &args[0], &Term::app(self.s.univ, vec![u.clone()]))?;
                return use_thm(env, "univ_powerset", &[("u", u), ("s", &args[0])], &[&p]).ok();
            }
            Some("cart") => return by_args(self, env, "cart_univ", &["a", "b"]),
            Some("bits") if un(u) == Some(1) => return thm(env, "bits_univ", &[("n", &args[0])]).ok(),
            Some("omega") if un(u) == Some(1) => return thm(env, "omega_univ", &[]).ok(),
            Some("app") => {
                // (a record's field or a function's value: of its set, if
                // known; else the whole a member)
                if let Some(p) = self.univ_by_type(env, t, u) {
                    return Some(p);
                }
                let p = self.check(env, &args[0], &Term::app(self.s.univ, vec![u.clone()]))?;
                return use_thm(env, "app_univ", &[("u", u), ("f", &args[0]), ("k", &args[1])], &[&p]).ok();
            }
            _ => {}
        }
        if let Some(p) = self.univ_by_type(env, t, u) {
            return Some(p);
        }
        // (a defined head: unfolded -- ok, exc, some, none, ..)
        if let Some((tu, d)) = unfold_head(env, t, false) {
            let p = self.check(env, &tu, &Term::app(self.s.univ, vec![u.clone()]))?;
            let goal = self.mk(self.s.in_, vec![t.clone(), Term::app(self.s.univ, vec![u.clone()])]);
            return Seq::conv(env, &p, &goal, &[d]).ok();
        }
        None
    }

    /// `t in univ(u)` from t's inferred set
    fn univ_by_type(&mut self, env: &mut Env, t: &Term, u: &Term) -> Option<Seq> {
        let (ty, p) = self.infer(env, t)?;
        let uu = Term::app(self.s.univ, vec![u.clone()]);
        // (its set a member: univ_trans)
        if let Some(name) = self.head_name(env, &ty) {
            if name == "bits" || name == "omega" {
                let om = Term::app(sym(env, "omega").ok()?, vec![]);
                let pn = if name == "omega" { p } else { Seq::arith(env, self.lg, &[&p], &self.mk(self.s.in_, vec![t.clone(), om])).ok()? };
                let z = use_thm(env, "nat_univ0", &[("n", t)], &[&pn]).ok()?;
                let un = match u.node() {
                    Node::Nat(n) => n.to_u64()?,
                    _ => return None,
                };
                return self.raise(env, z, 0, un);
            }
            if name == "fn_space" {
                let a = self.is(&ty, self.s.fn_space)?;
                let pa = self.check(env, &a[0], &uu)?;
                let pb = self.check(env, &a[1], &uu)?;
                return use_thm(env, "fn_space_univ", &[("u", u), ("a", &a[0]), ("b", &a[1]), ("f", t)], &[&pa, &pb, &p]).ok();
            }
        }
        // (a record of a record type over members: rec_univ)
        let full = self.unfold_set(env, &ty);
        let (k, ru, _) = self.rec_parts(&full)?;
        if ru != *u {
            return None;
        }
        let p = if full == ty { p } else { self.same_set(env, &p, &ty, &full).ok()? };
        let ty = full;
        let parts = self.unsel(env, &p).ok()?;
        let pw = self.mk(self.s.in_, vec![t.clone(), self.is(&ty, self.s.set_select)?[0].clone()]);
        let ppw = self.conjunct(env, &parts, &pw)?;
        let fun = self.conjunct(env, &parts, &self.mk(self.s.is_fun, vec![t.clone()]))?;
        let dom = self.conjunct(env, &parts, &self.mk(self.s.eq, vec![self.mk(self.s.dom, vec![t.clone()]), k.clone()]))?;
        let pk = self.check(env, &k, &uu)?;
        use_thm(env, "rec_univ", &[("u", u), ("k", &k), ("r", t)], &[&pk, &ppw, &fun, &dom]).ok()
    }

    /// `x in univ(n)` from `x in univ(m)`, m <= n literals (univ_next)
    fn raise(&self, env: &Env, mut s: Seq, m: u64, n: u64) -> Option<Seq> {
        if m > n {
            return None;
        }
        let x = match s.concl().node() {
            Node::App(_, a) => a[0].clone(),
            _ => return None,
        };
        for k in m..n {
            let kt = Term::nat(sl_kernel::Nat::from_u64(k));
            let next = use_thm(env, "univ_next", &[("u", &kt), ("x", &x)], &[&Seq::kernel(env.lit_is_nat(&kt)).ok()?, &s]).ok()?;
            // (lit_add(k, 1) computed)
            let e = Seq::kernel(env.lit_compute(env.builtins.lit_add, &kt, &Term::nat(sl_kernel::Nat::from_u64(1)))).ok()?;
            s = Seq::rewrite(env, &e, &next).ok()?;
        }
        Some(s)
    }

    // -----------------------------------------------------------------
    //  Records

    /// a record type's parts: `set_select(powerset(cart(K, univ(u))), x.
    /// p)` -> (K, u, p)
    fn rec_parts(&self, set: &Term) -> Option<(Term, Term, Term)> {
        let a = self.is(set, self.s.set_select)?;
        let pw = self.is(&a[0], self.s.powerset)?;
        let c = self.is(&pw[0], self.s.cart)?;
        let u = self.is(&c[1], self.s.univ)?;
        Some((c[0].clone(), u[0].clone(), a[1].clone()))
    }

    /// a set with its defined heads unfolded (a record type's name to its
    /// body)
    fn unfold_set(&self, env: &Env, set: &Term) -> Term {
        let mut x = set.clone();
        while self.rec_parts(&x).is_none() {
            match unfold_head(env, &x, false) {
                Some((u, _)) => x = u,
                None => break,
            }
        }
        x
    }

    /// from `z in set_select(s, x. p)`: `z in s && p(z)` (set_select_def,
    /// its equivalence's first direction: once per membership)
    fn unsel(&mut self, env: &Env, p: &Seq) -> KResult<Seq> {
        if let Some(s) = self.unsels.get(p.concl()) {
            return Ok(s.clone());
        }
        let (ax, rhs) = self.st.select_def(env, p.concl())?;
        let (a, b) = match ax.concl().node() {
            Node::App(_, x) if x.len() == 2 => (x[0].clone(), x[1].clone()),
            _ => return err("types: set_select_def is not an equivalence"),
        };
        // (a <-> b is (a -> b) && (b -> a): its left part, applied)
        let iff = sym(env, "iff")?;
        let imp = |x: &Term, y: &Term| Term::app(env.builtins.imp, vec![x.clone(), y.clone()]);
        let both = Term::app(self.s.and, vec![imp(&a, &b), imp(&b, &a)]);
        let ab = Seq::conv(env, &ax, &both, &[iff])?;
        let fwd = self.project(env, &ab, &[false])?;
        let s = Seq::mp(env, &fwd, p)?;
        debug_assert!(s.concl() == &rhs);
        self.unsels.insert(p.concl().clone(), s.clone());
        Ok(s)
    }

    /// r's record type's fact `want` (a conjunct of its predicate at r)
    fn rec_fact(&mut self, env: &mut Env, r: &Term, want: impl Fn(&Self, &Term) -> bool) -> Option<Seq> {
        // (known as it is)
        if let Some(ks) = self.by_term.get(r).cloned() {
            for k in ks {
                if want(self, &self.known[k].0) {
                    return self.known_proof(env, k).ok();
                }
            }
        }
        let (ty, p) = self.infer(env, r)?;
        let full = self.unfold_set(env, &ty);
        self.rec_parts(&full)?;
        let p = if full == ty { p } else { self.same_set(env, &p, &ty, &full).ok()? };
        let parts = self.unsel(env, &p).ok()?;
        let mut cs = Vec::new();
        self.conjuncts(parts.concl(), &mut cs);
        let c = cs.into_iter().find(|c| want(self, c))?;
        self.conjunct(env, &parts, &c)
    }

    /// `t in R`, R a record type: t's inferred type, or an update of a
    /// record of R (rec_type_intro)
    fn record(&mut self, env: &mut Env, t: &Term, set: &Term) -> Option<Seq> {
        let (k, u, pred) = self.rec_parts(set)?;
        let up = self.is(t, self.s.fn_update)?;
        let (r, key, v) = (&up[0], &up[1], &up[2]);
        // (r of the record type: its function, domain and fields)
        let rp = self.check(env, r, set)?;
        let rparts = self.unsel(env, &rp).ok()?;
        let rfun = self.conjunct(env, &rparts, &self.mk(self.s.is_fun, vec![r.clone()]))?;
        let rdom = self.conjunct(env, &rparts, &self.mk(self.s.eq, vec![self.mk(self.s.dom, vec![r.clone()]), k.clone()]))?;
        let kin = self.in_set(env, key, &k)?;
        let fd = use_thm(env, "fn_update_fd", &[("f", r), ("k", key), ("v", v), ("d", &k)], &[&rfun, &rdom, &kin]).ok()?;
        let uu = Term::app(self.s.univ, vec![u.clone()]);
        let tu = self.check(env, t, &uu)?;
        // p(t): its conjuncts, the fields read through the update
        let pt = pred.instantiate_params(std::slice::from_ref(t), &env.binders_fn());
        let mut cs = Vec::new();
        self.conjuncts(&pt, &mut cs);
        let fdl = self.split(env, &fd);
        let mut have: HashMap<Term, Seq> = fdl.iter().map(|s| (s.concl().clone(), s.clone())).collect();
        for c in &cs {
            if have.contains_key(c) {
                continue;
            }
            // `app(t, j) in T_j`
            let a = self.is(c, self.s.in_)?;
            let fld = self.is(&a[0], self.s.app)?;
            if fld[0] != *t {
                return None;
            }
            let j = &fld[1];
            let read = self.read_update(env, r, key, v, j)?;
            let val = match read.concl().node() {
                Node::App(_, x) => x[1].clone(),
                _ => return None,
            };
            let pv = self.check(env, &val, &a[1])?;
            let pc = Seq::rewrite_to(env, &Seq::sym(env, &read).ok()?, &pv, c).ok()?;
            have.insert(c.clone(), pc);
        }
        let ppt = self.build(env, &pt, &have)?;
        let isf = have.get(&self.mk(self.s.is_fun, vec![t.clone()]))?.clone();
        let dm = have.get(&self.mk(self.s.eq, vec![self.mk(self.s.dom, vec![t.clone()]), k.clone()]))?.clone();
        use_thm(env, "rec_type_intro", &[("u", &u), ("k", &k), ("p", &pred), ("r", t)], &[&tu, &isf, &dm, &ppt]).ok()
    }

    /// `app(fn_update(r, k, v), j) = ..`: v at k, r's field at another
    /// literal key
    fn read_update(&mut self, env: &mut Env, r: &Term, k: &Term, v: &Term, j: &Term) -> Option<Seq> {
        if j == k {
            return thm(env, "app_update_same", &[("f", r), ("k", k), ("v", v)]).ok();
        }
        let ne = self.lit_ne(env, j, k)?;
        use_thm(env, "app_update_other", &[("f", r), ("k", k), ("v", v), ("x", j)], &[&ne]).ok()
    }

    fn lit_ne(&self, env: &Env, a: &Term, b: &Term) -> Option<Seq> {
        lit_ne(env, self.lg, a, b)
    }

    /// `x in K`, K an insert chain with x one of its elements (the same
    /// term)
    fn in_set(&self, env: &Env, x: &Term, set: &Term) -> Option<Seq> {
        let a = self.is(set, self.s.insert)?;
        if a[0] == *x {
            return thm(env, "insert_l", &[("a", x), ("s", &a[1])]).ok();
        }
        let rest = self.in_set(env, x, &a[1])?;
        use_thm(env, "insert_r", &[("a", &a[0]), ("s", &a[1]), ("z", x)], &[&rest]).ok()
    }

    /// `k in dom(r)`: r's record type's domain; an update's key, or the
    /// updated record's domain (dom_update)
    fn in_dom(&mut self, env: &mut Env, k: &Term, r: &Term) -> Option<Seq> {
        if let Some(up) = self.is(r, self.s.fn_update) {
            let (f, key, v) = (&up[0], &up[1], &up[2]);
            let fun = self.rec_fact(env, f, |c, t| c.is(t, c.s.is_fun).is_some())?;
            let du = use_thm(env, "dom_update", &[("f", f), ("k", key), ("v", v)], &[&fun]).ok()?;
            let dset = self.mk(self.s.dom, vec![f.clone()]);
            let m = if k == key {
                thm(env, "insert_l", &[("a", key), ("s", &dset)]).ok()?
            } else {
                let rest = self.in_dom(env, k, f)?;
                use_thm(env, "insert_r", &[("a", key), ("s", &dset), ("z", k)], &[&rest]).ok()?
            };
            return Seq::rewrite(env, &Seq::sym(env, &du).ok()?, &m).ok();
        }
        let d = self.rec_fact(env, r, |c, t| c.is(t, c.s.eq).is_some_and(|a| c.is(&a[0], c.s.dom).is_some()))?;
        let keys = match d.concl().node() {
            Node::App(_, a) => a[1].clone(),
            _ => return None,
        };
        let m = self.in_set(env, k, &keys)?;
        Seq::rewrite(env, &Seq::sym(env, &d).ok()?, &m).ok()
    }

    // -----------------------------------------------------------------
    //  Inference

    /// t's set, proven: a known fact, a record's field, a function's
    /// value, an update of a typed record
    pub(crate) fn infer(&mut self, env: &mut Env, t: &Term) -> Option<(Term, Seq)> {
        if self.depth > MAX_DEPTH {
            return None;
        }
        self.depth += 1;
        let r = self.infer_(env, t);
        self.depth -= 1;
        r
    }

    fn infer_(&mut self, env: &mut Env, t: &Term) -> Option<(Term, Seq)> {
        // (a known membership, not a universe's: the most informative)
        if let Some(ks) = self.by_term.get(t).cloned() {
            let mut fallback = None;
            for k in ks {
                if let Some(a) = self.is(&self.known[k].0, self.s.in_) {
                    if self.is(&a[1], self.s.univ).is_some() {
                        fallback.get_or_insert(k);
                        continue;
                    }
                    return Some((a[1].clone(), self.known_proof(env, k).ok()?));
                }
            }
            if let Some(k) = fallback {
                let a = self.is(&self.known[k].0, self.s.in_)?;
                return Some((a[1].clone(), self.known_proof(env, k).ok()?));
            }
        }
        // (t defined by a known equation `t = e`: e's set)
        if let Some((e, eq)) = self.equation(env, t) {
            if let Some((ty, p)) = self.infer(env, &e) {
                let target = self.mk(self.s.in_, vec![t.clone(), ty.clone()]);
                return Some((ty, Seq::rewrite_to(env, &Seq::sym(env, &eq).ok()?, &p, &target).ok()?));
            }
        }
        let a = self.is(t, self.s.app);
        if let Some(a) = a {
            let (r, j) = (&a[0], &a[1]);
            let (ty, p) = self.infer(env, r)?;
            // (a function's value)
            if let Some(fs) = self.is(&ty, self.s.fn_space) {
                let px = self.check(env, j, &fs[0])?;
                let v = use_thm(env, "fn_space_app", &[("a", &fs[0]), ("b", &fs[1]), ("f", r), ("x", j)], &[&p, &px]).ok()?;
                return Some((fs[1].clone(), v));
            }
            // (a record's field: its type's conjunct)
            if matches!(j.node(), Node::Bytes(_) | Node::Nat(_)) {
                let full = self.unfold_set(env, &ty);
                self.rec_parts(&full)?;
                let p = if full == ty { p } else { self.same_set(env, &p, &ty, &full).ok()? };
                let parts = self.unsel(env, &p).ok()?;
                let mut cs = Vec::new();
                self.conjuncts(parts.concl(), &mut cs);
                let c = cs.into_iter().find(|c| self.is(c, self.s.in_).is_some_and(|x| x[0] == *t))?;
                let set = self.is(&c, self.s.in_)?[1].clone();
                return Some((set, self.conjunct(env, &parts, &c)?));
            }
            return None;
        }
        // (an update of a typed record: the record's type)
        if let Some(up) = self.is(t, self.s.fn_update) {
            let (ty, _) = self.infer(env, &up[0])?;
            let full = self.unfold_set(env, &ty);
            let p = self.check(env, t, &full)?;
            return Some((full, p));
        }
        None
    }

    // -----------------------------------------------------------------
    //  Numbers

    /// `t in bits(w)`, t a word operation of width n (its lemma
    /// `bits_<op>_in`), n = w by arith where written otherwise
    fn word_op(&mut self, env: &mut Env, t: &Term, name: &str, w: &Term) -> Option<Seq> {
        const OPS: &[(&str, &str, &[&str])] = &[
            ("bits_add", "bits_add_in", &["n", "a", "b"]),
            ("bits_sub", "bits_sub_in", &["n", "a", "b"]),
            ("bits_mul", "bits_mul_in", &["n", "a", "b"]),
            ("bits_neg", "bits_neg_in", &["n", "a"]),
            ("bits_of_int", "bits_of_int_in", &["n", "z"]),
            ("bits_shl", "bits_shl_in", &["n", "a", "k"]),
            ("bits_and", "bits_and_in", &["n", "x", "y"]),
            ("bits_or", "bits_or_in", &["n", "x", "y"]),
            ("bits_xor", "bits_xor_in", &["n", "x", "y"]),
            ("bits_not", "bits_not_in", &["n", "x"]),
            ("bits_set_slice", "bits_set_slice_in", &["n", "x", "hi", "lo", "v"]),
        ];
        let (_, lemma, names) = OPS.iter().find(|(op, _, _)| *op == name)?;
        let args = match t.node() {
            Node::App(_, a) => a.to_vec(),
            _ => return None,
        };
        if args.len() != names.len() {
            return None;
        }
        let om = Term::app(sym(env, "omega").ok()?, vec![]);
        let pn = self.check(env, &args[0], &om)?;
        let binds: Vec<(&str, &Term)> = names.iter().copied().zip(args.iter()).collect();
        let s = use_thm(env, lemma, &binds, &[&pn]).ok()?;
        if args[0] == *w {
            return Some(s);
        }
        let eq = Seq::arith(env, self.lg, &[], &self.mk(self.s.eq, vec![args[0].clone(), w.clone()])).ok()?;
        Seq::rewrite_to(env, &eq, &s, &self.mk(self.s.in_, vec![t.clone(), Term::app(sym(env, "bits").ok()?, vec![w.clone()])])).ok()
    }

    /// a numeric membership by arith, with the atoms' inferred sets
    fn arith(&mut self, env: &mut Env, goal: &Term) -> Option<Seq> {
        let mut atoms = Vec::new();
        self.atoms(env, goal, &mut atoms);
        let mut ps: Vec<Seq> = Vec::new();
        for a in atoms {
            if let Some((_, p)) = self.infer(env, &a) {
                ps.push(p);
            }
        }
        let refs: Vec<&Seq> = ps.iter().collect();
        Seq::arith(env, self.lg, &refs, goal).ok()
    }

    /// the goal's non-arithmetic subterms (fields, function values,
    /// variables)
    fn atoms(&self, env: &Env, t: &Term, out: &mut Vec<Term>) {
        const ARITH: &[&str] = &[
            "in", "int_add", "int_sub", "int_mul", "int_div", "int_mod", "int_neg", "int_lt", "int_le", "pow2", "int_pow", "bits_add", "bits_sub", "bits_mul",
            "bits_of_int", "bits_and", "bits_or", "bits_xor", "bits", "omega", "int", "set_select", "and", "or", "not", "eq", "seq_len",
        ];
        match t.node() {
            Node::App(h, a) => {
                let name = env.syms[*h as usize].name.as_str();
                if ARITH.contains(&name) {
                    for x in a.iter() {
                        self.atoms(env, x, out);
                    }
                } else if !out.contains(t) {
                    out.push(t.clone());
                }
            }
            Node::Var(_, _) => {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            }
            _ => {}
        }
    }
}
