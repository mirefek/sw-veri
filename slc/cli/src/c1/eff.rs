//! A spec's bookkeeping for its callers (`tr.callee_io`), proven from the
//! spec's structure with proofs/translate_effects.core's lemmas: one step
//! per construct, no search, through the kernel (`sl_proof::api`).
//!
//! The proof of `tr.eff(S, o. R)` (a program's outcomes R from the state S)
//! follows R:
//! - `bind_rel(p, S, s v. K, ..)`: tr.eff_bind, p's effect and K's (for
//!   each return of p);
//! - `any_rel(x. d, x. K)`: tr.eff_any, K's for each choice;
//! - `undefined if c; ..` (the elaborator's statement sequence):
//!   tr.eff_undef_if, the rest's when c fails;
//! - `o = ok(S, v)`: tr.eff_ret;
//! - `letin(a, x. R)`: R with a (unfolded);
//! - `runs(P(args), S, o)`: GIMPLE's primitive P (tr.eff_P), or a procedure
//!   of the program (its own lemma, proven first);
//! - `runs(call(G, args), S, o)` (or call1) of a callee G: tr.eff_call (or
//!   tr.eff_call1) from G's own `tr.callee_io` -- a hypothesis of the
//!   lemma, so a caller's lemmas hold for every callee with that property.

use sl_kernel::ext::seq::Seq;
use sl_kernel::syntax::Printer;
use sl_kernel::{Env, Node, SymId, SymKind, Term, VarId};
use sl_proof::api::{Api, A, G};
use std::collections::{BTreeSet, HashMap};

pub struct Eff<'e> {
    env: &'e mut Env,
    api: Api,
    /// the lemma prefix
    prefix: String,
    n: usize,
    /// the program's procedures with an effect lemma: its theorem
    procs: HashMap<SymId, Seq>,
    under_way: BTreeSet<SymId>,
    /// the theorems made, in order
    pub out: Vec<(String, Seq)>,
    /// the callees in scope (variables): their `tr.callee_io` hypothesis
    /// and their number of arguments
    hios: HashMap<VarId, (Seq, usize)>,
    /// a procedure's parameters that are callees (their indices)
    callee_params: HashMap<SymId, Vec<usize>>,
}

type R<T> = Result<T, String>;

fn e(x: sl_kernel::KernelError) -> String {
    x.0
}

impl<'e> Eff<'e> {
    pub fn new(env: &'e mut Env, prefix: &str) -> R<Eff<'e>> {
        let api = Api::new(env, Vec::new()).map_err(e)?;
        Ok(Eff { env, api, prefix: prefix.to_string(), n: 0, procs: HashMap::new(), under_way: BTreeSet::new(), out: Vec::new(), hios: HashMap::new(), callee_params: HashMap::new() })
    }

    fn app<'t>(&self, t: &'t Term, name: &str, n: usize) -> Option<&'t [Term]> {
        match t.node() {
            Node::App(s, a) if self.env.syms[*s as usize].name == name && a.len() == n => Some(a),
            _ => None,
        }
    }

    /// `name(args)`: a symbol's application, or an abbreviation's body
    fn mk(&self, name: &str, args: Vec<Term>) -> R<Term> {
        if let Some(s) = self.env.sym_by_name.get(name) {
            return Ok(Term::app(*s, args));
        }
        match self.env.abbrevs.get(name) {
            Some((k, body)) if *k == args.len() => Ok(body.instantiate_params(&args, &self.env.binders_fn())),
            _ => Err(format!("no `{}` loaded", name)),
        }
    }

    fn sym(&self, name: &str) -> R<SymId> {
        self.env.sym_by_name.get(name).copied().ok_or_else(|| format!("no `{}` loaded", name))
    }

    fn short(&self, t: &Term) -> String {
        Printer::new(self.env).short(t)
    }

    /// `t` with its `letin`s reduced (as unfolding `letin` reads it)
    fn unlet(&self, t: &Term) -> Term {
        match t.node() {
            Node::App(_, a) if self.app(t, "letin", 2).is_some() => {
                let a0 = self.unlet(&a[0]);
                self.unlet(&beta(self.env, &a[1], &a0, 0))
            }
            Node::App(_, a) => t.with_args(a.iter().map(|x| self.unlet(x)).collect()),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.unlet(x)).collect()),
            _ => t.clone(),
        }
    }

    fn fresh(&mut self, p: &str) -> (VarId, Term) {
        self.n += 1;
        let v = self.env.new_var(&format!("{}{}", p, self.n), 0);
        (v, Term::var(v, vec![]))
    }

    /// `t` under k binders, those bound to `vals` (outermost first)
    fn open(&self, t: &Term, vals: &[Term]) -> Term {
        t.instantiate_params(vals, &self.env.binders_fn())
    }

    /// `t` with the variable `v` bound (at the top: BVar(0))
    fn close_var(&self, t: &Term, v: VarId) -> Term {
        fn go(env: &Env, t: &Term, v: VarId, d: u32) -> Term {
            match t.node() {
                Node::Var(w, a) if *w == v && a.is_empty() => Term::bvar(d),
                Node::Var(_, a) => t.with_args(a.iter().map(|x| go(env, x, v, d)).collect()),
                Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| go(env, x, v, d + env.syms[*s as usize].binders[i])).collect()),
                _ => t.clone(),
            }
        }
        go(self.env, &t.shift(1, 0, &self.env.binders_fn()), v, 0)
    }

    /// `tr.eff(S, o. R)` (a program) or `tr.seff(S, x. R)` (a statement)
    fn eff(&self, st: bool, s: &Term, r: &Term, o: VarId) -> R<Term> {
        Ok(self.unlet(&self.mk(if st { "tr.seff" } else { "tr.eff" }, vec![s.clone(), self.close_var(r, o)])?))
    }

    /// a sequent's hypotheses `hs` discharged, its variables `vs`
    /// generalized: `all vs. hs -> ..`
    fn close(&self, s: Seq, hs: &[Term], vs: &[VarId]) -> R<Seq> {
        let mut s = s;
        for h in hs.iter().rev() {
            s = s.discharge(self.env, h).map_err(e)?;
        }
        for v in vs.iter().rev() {
            s = Seq::gen(self.env, &self.api.lg, &s, *v).map_err(e)?;
        }
        Ok(s)
    }

    /// the goal by `defs(apply(rule, {S}, args..), letin)`
    fn show(&mut self, goal: &Term, rule: &str, s: &Term, args: Vec<A>) -> R<Seq> {
        let f = self.api.fact(self.env, rule).map_err(e)?;
        let mut a = vec![A::T(s.clone())];
        a.extend(args);
        let letin = self.sym("letin")?;
        self.api.by(self.env, goal, G::Defs(Box::new(G::Apply(f, a)), vec![letin])).map_err(|x| format!("{}: {}", rule, x.0))
    }

    /// `tr.eff(S, o. R)` (`st`: `tr.seff`)
    fn prove(&mut self, st: bool, s: &Term, r: &Term, o: VarId) -> R<Seq> {
        let goal = self.eff(st, s, r, o)?;
        let ov = Term::var(o, vec![]);
        let pre = if st { "tr.seff" } else { "tr.eff" };
        // letin(a, x. R): R with a
        if let Some(a) = self.app(r, "letin", 2) {
            let r2 = self.open(&a[1], &[a[0].clone()]);
            return self.prove(st, s, &r2, o);
        }
        // o = ok(S, v); a statement's: o = ok(pair(S, l), v), o = exc(pair(S, l), pair("ret", v))
        if let Some(eq) = self.app(r, "eq", 2) {
            if eq[0] == ov {
                let at_s = |t: &Term| if st { self.app(t, "pair", 2).is_some_and(|p| p[0] == *s) } else { *t == *s };
                if let Some(k) = self.app(&eq[1], "ok", 2) {
                    if at_s(&k[0]) {
                        return self.show(&goal, &format!("{pre}_{}", if st { "ok" } else { "ret" }), s, vec![]);
                    }
                }
                if let Some(k) = self.app(&eq[1], "exc", 2) {
                    let label = |l: &[u8]| self.app(&k[1], "pair", 2).is_some_and(|p| matches!(p[0].node(), Node::Bytes(b) if &b[..] == l));
                    if st && at_s(&k[0]) && label(b"ret") {
                        return self.show(&goal, &format!("{pre}_ret"), s, vec![]);
                    }
                    if st && at_s(&k[0]) && label(b"brk") {
                        return self.show(&goal, &format!("{pre}_brk"), s, vec![]);
                    }
                }
            }
        }
        // bind_rel(p, S, s v. K, ..)
        if let Some(b) = self.app(r, "bind_rel", 5) {
            if b[1] != *s {
                return Err(format!("a sequence not from the current state: {}", self.short(r)));
            }
            let pe = self.prog_eff(s, &b[0])?;
            let (sn, sv) = self.fresh("ws");
            let (vn, vv) = self.fresh("vs");
            let k = self.open(&b[2], &[sv.clone(), vv.clone()]);
            let runs = self.unlet(&self.mk("runs", vec![b[0].clone(), s.clone(), self.mk("ok", vec![sv.clone(), vv.clone()])?])?);
            let _h = Seq::assume(self.env, runs.clone()).map_err(e)?;
            let kk = self.prove(st, &sv, &k, o)?;
            let hk = self.close(kk, &[runs], &[sn, vn])?;
            return self.show(&goal, &format!("{pre}_bind"), s, vec![A::G(G::By(pe)), A::G(G::By(hk))]);
        }
        // a statement `while`: while_rel(pair(S, loc), l. c, l o. B, l. tr, o), the body's
        // effect from each state with the condition
        if let Some(wl) = self.app(r, "while_rel", 5) {
            if st && wl[4] == ov && self.app(&wl[0], "pair", 2).is_some_and(|p| p[0] == *s) {
                let (ln, lv) = self.fresh("ls");
                let c = self.unlet(&self.open(&wl[1], &[lv.clone()]));
                let b = self.open(&wl[2], &[lv.clone(), ov.clone()]);
                let ls = self.mk("fst", vec![lv.clone()])?;
                let _h = Seq::assume(self.env, c.clone()).map_err(e)?;
                let kb = self.prove(true, &ls, &b, o)?;
                let hk = self.close(kb, &[c], &[ln])?;
                return self.show(&goal, &format!("{pre}_while"), s, vec![A::G(G::By(hk))]);
            }
        }
        // any_rel(x. d, x. K)
        if let Some(a) = self.app(r, "any_rel", 2) {
            let (xn, xv) = self.fresh("cs");
            let d = self.unlet(&self.open(&a[0], &[xv.clone()]));
            let k = self.open(&a[1], &[xv.clone()]);
            let _h = Seq::assume(self.env, d.clone()).map_err(e)?;
            let kk = self.prove(st, s, &k, o)?;
            let hk = self.close(kk, &[d], &[xn])?;
            return self.show(&goal, &format!("{pre}_any"), s, vec![A::G(G::By(hk))]);
        }
        if let Some(or) = self.app(r, "or", 2) {
            // a statement `undefined if c`: c || (!c && o = ok(pair(S, empty), empty))
            if st {
                if let Some(nc) = self.app(&or[1], "and", 2) {
                    if self.app(&nc[0], "not", 1).is_some_and(|n| n[0] == or[0]) && self.app(&nc[1], "eq", 2).is_some_and(|q| q[0] == ov) {
                        return self.show(&goal, &format!("{pre}_undef_if"), s, vec![]);
                    }
                }
            }
            // `if c`: (c && R1) || (!c && R2)
            if let (Some(a1), Some(a2)) = (self.app(&or[0], "and", 2), self.app(&or[1], "and", 2)) {
                if self.app(&a2[0], "not", 1).is_some_and(|n| n[0] == a1[0]) {
                    let (c, r1, r2) = (self.unlet(&a1[0]), a1[1].clone(), a2[1].clone());
                    let nc = self.mk("not", vec![c.clone()])?;
                    let _h1 = Seq::assume(self.env, c.clone()).map_err(e)?;
                    let k1 = self.prove(st, s, &r1, o)?;
                    let h1 = self.close(k1, &[c], &[])?;
                    let _h2 = Seq::assume(self.env, nc.clone()).map_err(e)?;
                    let k2 = self.prove(st, s, &r2, o)?;
                    let h2 = self.close(k2, &[nc], &[])?;
                    return self.show(&goal, &format!("{pre}_if"), s, vec![A::G(G::By(h1)), A::G(G::By(h2))]);
                }
            }
        }
        // a block: ex x. A(x) && ((fst(x) = 0 && K(x, o)) || ..), its statement's outcome dispatched
        if let Some(ex) = self.app(r, "ex", 1) {
            if let Some(a) = self.app(&ex[0], "and", 2) {
                let (x, xv) = self.fresh("xs");
                let stmt = self.open(&a[0], &[xv.clone()]);
                let disp = self.open(&a[1], &[xv.clone()]);
                let norm = self.app(&disp, "or", 2).and_then(|d| self.app(&d[0], "and", 2)).ok_or_else(|| format!("not a block's dispatch: {}", self.short(r)))?.to_vec();
                let k = norm[1].clone();
                // (after a loop: its normal or "brk" exit goes on; in a loop
                // body: a "brk" passed on)
                let after_loop = self.app(&norm[0], "or", 2).is_some();
                let passes_brk = self.app(&disp, "or", 2).is_some_and(|d| mentions_bytes(&d[1], b"brk"));
                let fst0 = self.mk("eq", vec![self.mk("fst", vec![xv.clone()])?, Term::nat(sl_kernel::Nat::from_u128(0))])?;
                let (rule, cond) = match (after_loop, st, passes_brk) {
                    (true, false, _) => {
                        let brk = self.mk(
                            "and",
                            vec![
                                self.mk("eq", vec![self.mk("fst", vec![xv.clone()])?, Term::nat(sl_kernel::Nat::from_u128(1))])?,
                                self.mk("eq", vec![self.mk("fst", vec![self.mk("out_value", vec![xv.clone()])?])?, Term::bytes(b"brk")])?,
                            ],
                        )?;
                        ("seq_loop", self.mk("or", vec![fst0, brk])?)
                    }
                    (false, true, true) => ("seq_brk", fst0),
                    (false, _, false) => ("seq", fst0),
                    _ => return Err(format!("a block's dispatch not covered: {}", self.short(r))),
                };
                let state = self.mk("fst", vec![self.mk("out_state", vec![xv.clone()])?])?;
                let ha = self.prove(true, s, &stmt, x)?;
                let stmt_u = self.unlet(&stmt);
                let _s1 = Seq::assume(self.env, stmt_u.clone()).map_err(e)?;
                let _s2 = Seq::assume(self.env, cond.clone()).map_err(e)?;
                let kk = self.prove(st, &state, &k, o)?;
                let hk = self.close(kk, &[stmt_u, cond], &[x])?;
                return self.show(&goal, &format!("{pre}_{rule}"), s, vec![A::G(G::By(ha)), A::G(G::By(hk))]);
            }
        }
        Err(format!("no effect rule for: {}", self.short(r)))
    }

    /// `tr.eff(S, o. runs(p, S, o))`
    fn prog_eff(&mut self, s: &Term, p: &Term) -> R<Seq> {
        let Node::App(f, args) = p.node() else { return Err(format!("not a program application: {}", self.short(p))) };
        let name = self.env.syms[*f as usize].name.clone();
        let mut terms = vec![A::T(self.unlet(s))];
        terms.extend(args.iter().map(|a| A::T(self.unlet(a))));
        // a call of a callee: its tr.callee_io
        if name == "gimple.call" || name == "gimple.call1" {
            let Node::Var(g, _) = args[0].node() else { return Err(format!("a call of other than a callee: {}", self.short(p))) };
            let (h, k) = self.hios.get(g).cloned().ok_or_else(|| format!("a call of an unknown callee: {}", self.short(p)))?;
            let rule = if name == "gimple.call" { "tr.eff_call" } else { "tr.eff_call1" };
            let f0 = self.api.fact(self.env, rule).map_err(e)?;
            let ord_le = self.sym("ord_le")?;
            let a = vec![
                A::T(self.unlet(&args[0])),
                A::T(self.unlet(&args[1])),
                A::T(Term::nat(sl_kernel::Nat::from_u128(k as u128))),
                A::T(self.unlet(s)),
                A::G(G::By(h)),
                A::G(G::Defs(Box::new(G::Arith(vec![])), vec![ord_le])),
            ];
            return self.api.mp(self.env, f0, a).map_err(|x| format!("{}: {}", rule, x.0));
        }
        let lemma = if let Some(prim) = name.strip_prefix("gimple.") {
            let l = format!("tr.eff_{}", prim);
            self.api.fact(self.env, &l).map_err(|_| format!("no effect lemma `{}` (proofs/translate_effects.core)", l))?
        } else {
            self.proc_lemma(*f)?
        };
        // (a procedure taking callees: their hypotheses)
        let mut a = terms;
        for &i in self.callee_params.get(f).cloned().unwrap_or_default().iter() {
            let Node::Var(g, _) = args[i].node() else { return Err(format!("a callee argument not a callee: {}", self.short(p))) };
            a.push(A::G(G::By(self.hios.get(g).ok_or_else(|| format!("a callee argument not in scope: {}", self.short(p)))?.0.clone())));
        }
        self.api.mp(self.env, lemma, a).map_err(|x| format!("{}: {}", name, x.0))
    }

    /// the variables called in t (`call(g, args)`, `call1(g, args)`), with
    /// their calls' numbers of arguments (the least)
    fn called(&self, t: &Term) -> HashMap<VarId, usize> {
        let mut m: HashMap<VarId, usize> = HashMap::new();
        self.called_in(t, &mut m);
        m
    }

    fn called_in(&self, t: &Term, m: &mut HashMap<VarId, usize>) {
        for name in ["gimple.call", "gimple.call1"] {
            if let Some(c) = self.app(t, name, 2) {
                if let (Node::Var(g, _), Some(k)) = (c[0].node(), list_len(self, &c[1])) {
                    let e = m.entry(*g).or_insert(k);
                    *e = (*e).min(k);
                }
            }
        }
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => a.iter().for_each(|x| self.called_in(x, m)),
            _ => {}
        }
    }

    /// The program's procedure `f` (a definition `mkprog(x0 x1. B)`): its
    /// effect lemma, proven once.
    fn proc_lemma(&mut self, f: SymId) -> R<Seq> {
        if let Some(s) = self.procs.get(&f) {
            return Ok(s.clone());
        }
        let name = self.env.syms[f as usize].name.clone();
        if !self.under_way.insert(f) {
            return Err(format!("`{}`: a recursive procedure", name));
        }
        let short = name.rsplit('.').next().unwrap_or(&name).to_string();
        let lemma = format!("{}.eff_{}", self.prefix, short);
        let SymKind::Defined { params, body } = self.env.syms[f as usize].kind.clone() else { return Err(format!("`{}` is not a definition", name)) };
        let (wn, wv) = self.fresh("ws");
        let mut pvars = Vec::new();
        let mut body = body;
        // (its callees: the parameters called, with their numbers of arguments)
        let called = self.called(&body);
        let mut hyps = Vec::new();
        for (i, p) in params.iter().enumerate() {
            if self.env.var(*p).arity > 0 {
                return Err(format!("`{}`: a procedure taking a function", name));
            }
            let (pn, pv) = self.fresh("as");
            if let Some(&k) = called.get(p) {
                let h = self.mk("tr.callee_io", vec![pv.clone(), Term::nat(sl_kernel::Nat::from_u128(k as u128))])?;
                let hs = Seq::assume(self.env, h.clone()).map_err(e)?;
                self.hios.insert(pn, (hs, k));
                hyps.push(h);
                self.callee_params.entry(f).or_default().push(i);
            }
            body = body.subst_var(*p, &pv, &self.env.binders_fn());
            pvars.push((pn, pv));
        }
        let m = self.app(&body, "mkprog", 1).ok_or_else(|| format!("`{}`: not a program", name))?.to_vec();
        let (o, ov) = self.fresh("os");
        let b = self.open(&m[0], &[wv.clone(), ov.clone()]);
        let call = self.mk(&name, pvars.iter().map(|(_, v)| v.clone()).collect())?;
        let runs = self.mk("runs", vec![call, wv.clone(), ov.clone()])?;
        let goal = self.eff(false, &wv, &runs, o)?;
        let kb = self.prove(false, &wv, &b, o)?;
        let ep = self.api.fact(self.env, "tr.eff_prog").map_err(e)?;
        let (fsym, letin) = (f, self.sym("letin")?);
        let r = self.api.by(self.env, &goal, G::Defs(Box::new(G::Apply(ep, vec![A::T(wv.clone()), A::G(G::By(kb))])), vec![fsym, letin])).map_err(|x| format!("{}: {}", lemma, x.0))?;
        let mut vs = vec![wn];
        vs.extend(pvars.iter().map(|(v, _)| *v));
        let s = self.close(r, &hyps, &vs)?;
        self.out.push((lemma, s.clone()));
        self.procs.insert(f, s.clone());
        Ok(s)
    }

    /// A CFG's loop body b (`l o. B`): `all l. tr.seff(fst(l), x. b(l,
    /// x))`; its callees' `tr.callee_io` (called with at least their
    /// fewest arguments) hypotheses of the result
    pub fn body_seff(&mut self, b: &Term) -> R<Seq> {
        let (ln, lv) = self.fresh("ls");
        let (o, ov) = self.fresh("os");
        let body = self.open(b, &[lv.clone(), ov.clone()]);
        for (g, k) in self.called(&body) {
            if !self.hios.contains_key(&g) {
                let h = self.mk("tr.callee_io", vec![Term::var(g, vec![]), Term::nat(sl_kernel::Nat::from_u128(k as u128))])?;
                let hs = Seq::assume(self.env, h).map_err(e)?;
                self.hios.insert(g, (hs, k));
            }
        }
        let s = self.mk("fst", vec![lv])?;
        let kb = self.prove(true, &s, &body, o)?;
        self.close(kb, &[], &[ln])
    }

    /// For the spec `spec` (a `_fun` wrapper; its parameters callees G0, ..,
    /// called with `callee_ns[i]` arguments): its effect lemmas, `{prefix}.io`
    /// (tr.callee_io, from the callees') and `{prefix}.typed` (in `out`);
    /// Err with the reason if a construct has no rule.
    pub fn callee_io(&mut self, spec: SymId, callee_ns: &[usize]) -> R<()> {
        let name = self.env.syms[spec as usize].name.clone();
        let SymKind::Defined { params, body } = self.env.syms[spec as usize].kind.clone() else { return Err(format!("`{}` is not a definition", name)) };
        // (the callees: G0, .., with their tr.callee_io hypotheses)
        let mut body = body;
        let mut gs = Vec::new();
        let mut ghyps = Vec::new();
        let cn = |i: usize| callee_ns.get(i).copied().unwrap_or(1);
        for (i, p) in params.iter().enumerate() {
            let gv = self.env.new_var(&format!("G{i}"), 0);
            let gt = Term::var(gv, vec![]);
            body = body.subst_var(*p, &gt, &self.env.binders_fn());
            let h = self.mk("tr.callee_io", vec![gt.clone(), Term::nat(sl_kernel::Nat::from_u128(cn(i) as u128))])?;
            let hs = Seq::assume(self.env, h.clone()).map_err(e)?;
            self.hios.insert(gv, (hs, cn(i)));
            ghyps.push(h);
            gs.push((gv, gt));
        }
        let app = self.mk(&name, gs.iter().map(|g| g.1.clone()).collect())?;
        // fn_build(abi.ARGS, x0. mkprog(x1 x2. !ord_le(n, seq_len(x0)) || B))
        let fb = self.app(&body, "fn_build", 2).ok_or("not a `_fun` wrapper")?.to_vec();
        let (an, av) = self.fresh("as");
        let (wn, wv) = self.fresh("ws");
        let (o, ov) = self.fresh("os");
        let m = self.open(&fb[1], &[av.clone()]);
        let mp = self.app(&m, "mkprog", 1).ok_or("not a `_fun` wrapper")?.to_vec();
        let wrapper = self.open(&mp[0], &[wv.clone(), ov.clone()]);
        // (the arity guard `!ord_le(n, seq_len(args)) || B`; none without arguments)
        let guard = self.app(&wrapper, "or", 2).and_then(|or| {
            let g = self.app(&or[0], "not", 1).and_then(|g| self.app(&g[0], "ord_le", 2))?;
            Some((g[0].clone(), or[1].clone()))
        });
        let zero = Term::nat(sl_kernel::Nat::from_u128(0));
        let (n, b) = match &guard {
            Some((n, b)) => (n.clone(), b.clone()),
            None => (zero, wrapper.clone()),
        };
        let runs = self.mk("runs", vec![m.clone(), wv.clone(), ov.clone()])?;
        let in_args = self.mk("in", vec![av.clone(), self.mk("abi.ARGS", vec![])?])?;
        let le = self.mk("ord_le", vec![n.clone(), self.mk("seq_len", vec![av.clone()])?])?;
        let _ha = Seq::assume(self.env, in_args.clone()).map_err(e)?;
        let hn = Seq::assume(self.env, le.clone()).map_err(e)?;
        let kb = self.prove(false, &wv, &b, o)?;
        let goal = self.eff(false, &wv, &runs, o)?;
        let letin = self.sym("letin")?;
        let ep = self.api.fact(self.env, "tr.eff_prog").map_err(e)?;
        let inner = if guard.is_some() {
            let eg = self.api.fact(self.env, "tr.eff_guard").map_err(e)?;
            G::Apply(eg, vec![A::T(wv.clone()), A::G(G::By(hn)), A::G(G::By(kb))])
        } else {
            G::By(kb)
        };
        let g1 = self.api.by(self.env, &goal, G::Defs(Box::new(G::Apply(ep, vec![A::T(wv.clone()), A::G(inner)])), vec![letin])).map_err(|x| format!("{}.io: {}", self.prefix, x.0))?;
        let g1 = self.close(g1, &[in_args, le], &[an, wn])?;
        let io_goal = self.mk("tr.callee_io", vec![app.clone(), n.clone()])?;
        let cio = self.api.fact(self.env, "tr.callee_io_fun").map_err(e)?;
        let io = self.api.by(self.env, &io_goal, G::Defs(Box::new(G::Apply(cio, vec![A::T(n), A::G(G::By(g1))])), vec![spec, letin])).map_err(|x| format!("{}.io: {}", self.prefix, x.0))?;
        let gvs: Vec<VarId> = gs.iter().map(|g| g.0).collect();
        let io = self.close(io, &ghyps, &gvs)?;
        self.out.push((format!("{}.io", self.prefix), io));
        // its spec typed
        let ty_goal = self.mk("in", vec![app, self.mk("fn_space", vec![self.mk("abi.ARGS", vec![])?, self.mk("powerset", vec![self.mk("univ", vec![Term::nat(sl_kernel::Nat::from_u128(1))])?])?])?])?;
        let ft = self.api.fact(self.env, "tr.fun_typed").map_err(e)?;
        let ty = self.api.by(self.env, &ty_goal, G::Defs(Box::new(G::By(ft)), vec![spec])).map_err(|x| format!("{}.typed: {}", self.prefix, x.0))?;
        let ty = self.close(ty, &[], &gvs)?;
        self.out.push((format!("{}.typed", self.prefix), ty));
        Ok(())
    }
}

/// `f[0 := a]` (de Bruijn: the variable bound at the top of `f`, at depth
/// k within it, replaced by `a` shifted by k; the others above it lowered)
fn beta(env: &Env, f: &Term, a: &Term, k: u32) -> Term {
    let bf = env.binders_fn();
    match f.node() {
        Node::BVar(i) if *i == k => a.shift(k, 0, &bf),
        Node::BVar(i) if *i > k => Term::bvar(i - 1),
        Node::App(s, xs) => f.with_args(xs.iter().enumerate().map(|(j, x)| beta(env, x, a, k + env.syms[*s as usize].binders[j])).collect()),
        Node::Var(_, xs) => f.with_args(xs.iter().map(|x| beta(env, x, a, k)).collect()),
        _ => f.clone(),
    }
}

/// `t` has the bytes literal `b`
fn mentions_bytes(t: &Term, b: &[u8]) -> bool {
    match t.node() {
        Node::Bytes(x) => &x[..] == b,
        Node::App(_, a) | Node::Var(_, a) => a.iter().any(|x| mentions_bytes(x, b)),
        _ => false,
    }
}

/// the length of a list literal (`seq_one`s concatenated)
fn list_len(e: &Eff, t: &Term) -> Option<usize> {
    if e.app(t, "empty", 0).is_some() {
        return Some(0);
    }
    if e.app(t, "seq_one", 1).is_some() {
        return Some(1);
    }
    let x = e.app(t, "seq_concat", 2)?;
    Some(list_len(e, &x[0])? + list_len(e, &x[1])?)
}
