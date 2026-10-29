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
//!   lemma, so a caller's lemmas hold for every callee with that property;
//! - (proofs/translate_struct.core) `!c || R` (a requirement): tr.eff_req,
//!   R's with c; `a || b` (a statement's choice): tr.seff_or; a block whose
//!   statement keeps the world (every outcome's at S: tr.sk), the rest
//!   from S itself (tr.eff_seq_same); a return to a changed world: its
//!   validity by the change's lemma (`VALID`), its premises from the facts
//!   in hand (exactly, a type by `ty`, else propositionally);
//! - a GIMPLE procedure without its own lemma: inlined (its body from S,
//!   with the facts in hand -- a caller's requirements).
//!
//! The facts in hand: the conditions, choices and requirements on the way
//! (their conjuncts, a case split's `ite(c, a, b)` as `c -> a`, `!c -> b`),
//! and a procedure's parameter types (the elaborator's `{proc}.dom`,
//! assumed by its lemma, shown at its calls by `ty`).

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
    /// the facts in hand (see the module's doc)
    ctx: Vec<Seq>,
    /// a procedure's lemma: the parameter types it assumes (indices into
    /// `param_types`)
    typed: HashMap<SymId, Vec<usize>>,
}

/// A world changed in a field (`fn_update(S, field, V)`): the lemma showing
/// it valid (proofs/translate_struct.core)
const VALID: &[(&str, &str)] = &[("vm", "tr.valid_vm"), ("vm", "tr.valid_gone"), ("objs", "tr.valid_objs")];

/// A term's type by its head (`f(a..) in T`): the lemma, all a.. ->
/// premises on the arguments (each `a in T'`) -> f(a..) in T
const TYPES: &[(&str, &str)] = &[("bits_of_int", "nf.of_int_in"), ("x86_64_linux.page_of", "tr.ty_page_of"), ("x86_64_linux.pages_for", "tr.ty_pages_for")];

type R<T> = Result<T, String>;

fn e(x: sl_kernel::KernelError) -> String {
    x.0
}

impl<'e> Eff<'e> {
    pub fn new(env: &'e mut Env, prefix: &str) -> R<Eff<'e>> {
        let api = Api::new(env, Vec::new()).map_err(e)?;
        Ok(Eff { env, api, prefix: prefix.to_string(), n: 0, procs: HashMap::new(), under_way: BTreeSet::new(), out: Vec::new(), hios: HashMap::new(), callee_params: HashMap::new(), ctx: Vec::new(), typed: HashMap::new() })
    }

    /// t assumed, a fact in hand (with its parts)
    fn assume(&mut self, t: &Term) -> R<Seq> {
        let h = Seq::assume(self.env, t.clone()).map_err(e)?;
        self.add_fact(h.clone())?;
        Ok(h)
    }

    /// a fact in hand, with its conjuncts and an `ite`'s two cases
    fn add_fact(&mut self, s: Seq) -> R<()> {
        let t = s.concl().clone();
        self.ctx.push(s.clone());
        if let Some(a) = self.app(&t, "and", 2) {
            for x in a.to_vec() {
                let p = self.api.by(self.env, &x, G::Taut(vec![s.clone()])).map_err(e)?;
                self.add_fact(p)?;
            }
        }
        if let Some(a) = self.app(&t, "ite", 3) {
            let a = a.to_vec();
            let imp = self.env.builtins.imp;
            let nc = self.mk("not", vec![a[0].clone()])?;
            for (c, b, rule) in [(a[0].clone(), a[1].clone(), "tr.ite_imp_t"), (nc, a[2].clone(), "tr.ite_imp_f")] {
                let f = self.api.fact(self.env, rule).map_err(e)?;
                let g = Term::app(imp, vec![c, b]);
                let p = self.api.by(self.env, &g, G::Apply(f, vec![A::G(G::By(s.clone()))])).map_err(|x| format!("{}: {}", rule, x.0))?;
                self.ctx.push(p);
            }
        }
        Ok(())
    }

    /// `t in set` from the facts in hand: one of them, or by t's head
    /// (`TYPES`), its arguments' types in turn
    fn ty(&mut self, t: &Term, set: &Term) -> R<Seq> {
        let goal = self.mk("in", vec![t.clone(), set.clone()])?;
        if let Some(f) = self.ctx.iter().find(|f| *f.concl() == goal) {
            return Ok(f.clone());
        }
        let rule = match t.node() {
            Node::App(h, _) => TYPES.iter().find(|(n, _)| *n == self.env.syms[*h as usize].name).map(|r| r.1),
            _ => None,
        };
        // (else arithmetic, from the types in hand)
        let Some(rule) = rule else {
            let tys: Vec<Seq> = self.ctx.iter().filter(|f| self.app(f.concl(), "in", 2).is_some()).cloned().collect();
            return self.api.by(self.env, &goal, G::Arith(tys)).map_err(|x| format!("no type for {}: {}", self.short(&goal), x.0));
        };
        let f = self.api.fact(self.env, rule).map_err(e)?;
        // (its arguments, then a proof of each premise: a type, else arithmetic)
        let Node::App(_, args) = t.node() else { unreachable!() };
        let mut a: Vec<A> = args.iter().map(|x| A::T(x.clone())).collect();
        let mut s = f.clone();
        for x in args.iter() {
            s = Seq::all_elim(self.env, &self.api.lg, &s, x).map_err(e)?;
        }
        for prem in self.premises(s.concl()).0 {
            let g = match self.app(&prem, "in", 2) {
                Some(p) if !matches!(p[0].node(), Node::Nat(_)) => {
                    let (x, st) = (p[0].clone(), p[1].clone());
                    G::By(self.ty(&x, &st)?)
                }
                _ => G::Arith(vec![]),
            };
            let pr = self.api.by(self.env, &prem, g).map_err(|x| format!("{}: {}", rule, x.0))?;
            a.push(A::G(G::By(pr)));
        }
        self.api.mp(self.env, f, a).map_err(|x| format!("{}: {}", rule, x.0))
    }

    /// `p1 -> .. -> c`: the premises, c
    fn premises(&self, t: &Term) -> (Vec<Term>, Term) {
        let imp = self.env.builtins.imp;
        let mut ps = Vec::new();
        let mut c = t.clone();
        while let Node::App(i, pc) = c.node() {
            if *i != imp {
                break;
            }
            ps.push(pc[0].clone());
            let n = pc[1].clone();
            c = n;
        }
        (ps, c)
    }

    /// f's parameter types (the elaborator's `{f}.dom`, its conjuncts `p in
    /// T`), over the arguments `args`: each `arg in T`
    fn param_types(&self, f: SymId, args: &[Term]) -> Vec<Term> {
        let name = format!("{}.dom", self.env.syms[f as usize].name);
        let Some(&d) = self.env.sym_by_name.get(&name) else { return Vec::new() };
        let SymKind::Defined { params, body } = self.env.syms[d as usize].kind.clone() else { return Vec::new() };
        let mut b = body;
        for (p, a) in params.iter().zip(args) {
            b = b.subst_var(*p, a, &self.env.binders_fn());
        }
        let mut parts = Vec::new();
        let mut todo = vec![b];
        while let Some(t) = todo.pop() {
            if let Some(a) = self.app(&t, "and", 2) {
                todo.push(a[1].clone());
                todo.push(a[0].clone());
            } else if self.app(&t, "in", 2).is_some() {
                parts.push(t);
            }
        }
        parts
    }

    /// `tr.returns_valid(s, s2)`, s2 a world changed (`VALID`): the lemma's
    /// variables by its conclusion, then by its premises in turn matched
    /// with the facts in hand; each premise one of them, a type, or by
    /// propositional logic from them
    fn valid(&mut self, s: &Term, s2: &Term) -> R<Seq> {
        let goal = self.mk("tr.returns_valid", vec![s.clone(), s2.clone()])?;
        let field = self.app(s2, "fn_update", 3).filter(|u| u[0] == *s).and_then(|u| match u[1].node() {
            Node::Bytes(b) => Some(String::from_utf8_lossy(b).to_string()),
            _ => None,
        });
        let Some(f) = field else { return Err(format!("no validity rule for a return to {}", self.short(s2))) };
        // (the field's lemmas in turn: the first whose premises the facts
        // in hand meet -- each change's lemma has its own, fresh pages',
        // pages gone)
        let mut errs = Vec::new();
        for (_, rule) in VALID.iter().filter(|(n, _)| *n == f) {
            match self.valid_by(rule, &goal) {
                Ok(x) => return Ok(x),
                Err(x) => errs.push(x),
            }
        }
        Err(if errs.is_empty() { format!("no validity rule for a return to {}", self.short(s2)) } else { errs.join("; ") })
    }

    /// `goal` (`tr.returns_valid(..)`) by the validity lemma `rule`
    fn valid_by(&mut self, rule: &str, goal: &Term) -> R<Seq> {
        let goal = goal.clone();
        let f = self.api.fact(self.env, rule).map_err(e)?;
        let mut vars = Vec::new();
        f.concl().vars(&mut vars);
        let (prems, c) = self.premises(f.concl());
        let mut b: HashMap<VarId, Term> = HashMap::new();
        if !self.pmatch(&c, &goal, &vars, &mut b, 0) {
            return Err(format!("{}: not of {}", rule, self.short(&goal)));
        }
        for p in &prems {
            let mut pv = Vec::new();
            p.vars(&mut pv);
            if pv.iter().all(|v| !vars.contains(v) || b.contains_key(v)) {
                continue;
            }
            let found = self.ctx.iter().map(|x| x.concl().clone()).find_map(|t| {
                let mut b2 = b.clone();
                self.pmatch(p, &t, &vars, &mut b2, 0).then_some(b2)
            });
            b = found.ok_or_else(|| format!("{}: no fact in hand for {}", rule, self.short(p)))?;
        }
        let mut fi = f.clone();
        for v in &vars {
            let val = b.get(v).ok_or_else(|| format!("{}: `{}` not determined", rule, self.env.var(*v).name))?;
            fi = self.api.inst_var(self.env, fi, *v, val).map_err(e)?;
        }
        let mut a = Vec::new();
        for prem in self.premises(fi.concl()).0 {
            let pr = if let Some(x) = self.ctx.iter().find(|x| *x.concl() == prem) {
                x.clone()
            } else if let Some(t) = self.app(&prem, "in", 2) {
                let (x, st) = (t[0].clone(), t[1].clone());
                self.ty(&x, &st)?
            } else {
                self.api.by(self.env, &prem, G::Taut(self.ctx.clone())).map_err(|x| format!("{}: {}: {}", rule, self.short(&prem), x.0))?
            };
            a.push(A::G(G::By(pr)));
        }
        self.api.mp(self.env, fi, a).map_err(|x| format!("{}: {}", rule, x.0))
    }

    /// first-order matching of `pat` (its variables `vars`, bound in b) with t
    fn pmatch(&self, pat: &Term, t: &Term, vars: &[VarId], b: &mut HashMap<VarId, Term>, d: u32) -> bool {
        match (pat.node(), t.node()) {
            (Node::Var(v, a), _) if a.is_empty() && vars.contains(v) => match b.get(v) {
                Some(x) => x == t,
                None if d == 0 => {
                    b.insert(*v, t.clone());
                    true
                }
                None => false,
            },
            (Node::App(s1, a1), Node::App(s2, a2)) => s1 == s2 && a1.len() == a2.len() && a1.iter().zip(a2.iter()).enumerate().all(|(i, (x, y))| self.pmatch(x, y, vars, b, d + self.env.syms[*s1 as usize].binders[i])),
            (Node::Var(v1, a1), Node::Var(v2, a2)) => v1 == v2 && a1.len() == a2.len() && a1.iter().zip(a2.iter()).all(|(x, y)| self.pmatch(x, y, vars, b, d)),
            _ => pat == t,
        }
    }

    /// every outcome of the statement a (its outcome the variable x) at the
    /// world s: a choice (`||`, `c && ..`) of `x = ok/exc(pair(s, l), v)`
    fn keeps(&self, a: &Term, x: VarId, s: &Term) -> bool {
        if let Some(o) = self.app(a, "or", 2) {
            return self.keeps(&o[0], x, s) && self.keeps(&o[1], x, s);
        }
        if let Some(o) = self.app(a, "and", 2) {
            return self.keeps(&o[1], x, s);
        }
        if let Some(q) = self.app(a, "eq", 2) {
            if matches!(q[0].node(), Node::Var(v, z) if *v == x && z.is_empty()) {
                let k = self.app(&q[1], "ok", 2).or_else(|| self.app(&q[1], "exc", 2));
                return k.and_then(|k| self.app(&k[0], "pair", 2)).is_some_and(|p| p[0] == *s);
            }
        }
        false
    }

    /// `tr.sk(s, x. a)` (`keeps`)
    fn sk(&mut self, s: &Term, a: &Term, x: VarId) -> R<Seq> {
        let goal = self.mk("tr.sk", vec![s.clone(), self.close_var(a, x)])?;
        if let Some(o) = self.app(a, "or", 2) {
            let (l, r) = (o[0].clone(), o[1].clone());
            let (kl, kr) = (self.sk(s, &l, x)?, self.sk(s, &r, x)?);
            return self.show(&goal, "tr.sk_or", s, vec![A::G(G::By(kl)), A::G(G::By(kr))]);
        }
        if let Some(o) = self.app(a, "and", 2) {
            let r = o[1].clone();
            let kr = self.sk(s, &r, x)?;
            return self.show(&goal, "tr.sk_and", s, vec![A::G(G::By(kr))]);
        }
        let q = self.app(a, "eq", 2).ok_or("not a statement keeping the world")?.to_vec();
        let rule = if self.app(&q[1], "ok", 2).is_some() { "tr.sk_ok" } else { "tr.sk_exc" };
        self.show(&goal, rule, s, vec![])
    }

    /// t with the subterm `from` replaced by `to`
    fn replace(&self, t: &Term, from: &Term, to: &Term) -> Term {
        if t == from {
            return to.clone();
        }
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => t.with_args(a.iter().map(|x| self.replace(x, from, to)).collect()),
            _ => t.clone(),
        }
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
                // (the world of a statement's outcome)
                let world = |t: &Term| if st { self.app(t, "pair", 2).map(|p| p[0].clone()) } else { Some(t.clone()) };
                if let Some(k) = self.app(&eq[1], "ok", 2) {
                    if at_s(&k[0]) {
                        return self.show(&goal, &format!("{pre}_{}", if st { "ok" } else { "ret" }), s, vec![]);
                    }
                    // (to a changed world: its validity)
                    if let Some(w2) = world(&k[0]) {
                        let v = self.valid(s, &w2)?;
                        return self.show(&goal, &format!("{pre}_{}_chg", if st { "ok" } else { "ret" }), s, vec![A::G(G::By(v))]);
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
                    if st && label(b"ret") {
                        if let Some(w2) = world(&k[0]) {
                            let v = self.valid(s, &w2)?;
                            return self.show(&goal, "tr.seff_ret_chg", s, vec![A::G(G::By(v))]);
                        }
                    }
                }
            }
        }
        // bind_rel(p, S, s v. K, ..)
        if let Some(b) = self.app(r, "bind_rel", 5) {
            if b[1] != *s {
                // (from a world changed and valid: the effect from there,
                // tr.eff_from -- the `_fun` wrapper's return with its
                // objects released)
                if st {
                    return Err(format!("a sequence not from the current state: {}", self.short(r)));
                }
                let v = self.valid(s, &self.unlet(&b[1]))?;
                let kk = self.prove(false, &b[1], r, o)?;
                return self.show(&goal, "tr.eff_from", s, vec![A::G(G::By(v)), A::G(G::By(kk))]);
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
                let sc = self.ctx.len();
                self.assume(&c)?;
                let kb = self.prove(true, &ls, &b, o)?;
                self.ctx.truncate(sc);
                let hk = self.close(kb, &[c], &[ln])?;
                return self.show(&goal, &format!("{pre}_while"), s, vec![A::G(G::By(hk))]);
            }
        }
        // any_rel(x. d, x. K)
        if let Some(a) = self.app(r, "any_rel", 2) {
            let (xn, xv) = self.fresh("cs");
            let d = self.unlet(&self.open(&a[0], &[xv.clone()]));
            let k = self.open(&a[1], &[xv.clone()]);
            let sc = self.ctx.len();
            self.assume(&d)?;
            let kk = self.prove(st, s, &k, o)?;
            self.ctx.truncate(sc);
            let hk = self.close(kk, &[d], &[xn])?;
            return self.show(&goal, &format!("{pre}_any"), s, vec![A::G(G::By(hk))]);
        }
        if let Some(or) = self.app(r, "or", 2) {
            let or = or.to_vec();
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
                    let sc = self.ctx.len();
                    self.assume(&c)?;
                    let k1 = self.prove(st, s, &r1, o)?;
                    self.ctx.truncate(sc);
                    let h1 = self.close(k1, &[c], &[])?;
                    self.assume(&nc)?;
                    let k2 = self.prove(st, s, &r2, o)?;
                    self.ctx.truncate(sc);
                    let h2 = self.close(k2, &[nc], &[])?;
                    return self.show(&goal, &format!("{pre}_if"), s, vec![A::G(G::By(h1)), A::G(G::By(h2))]);
                }
            }
            // `require c`: !c || R, R's with c
            if let (false, Some(n)) = (st, self.app(&or[0], "not", 1)) {
                let c = self.unlet(&n[0]);
                let sc = self.ctx.len();
                self.assume(&c)?;
                let k = self.prove(st, s, &or[1], o)?;
                self.ctx.truncate(sc);
                let h = self.close(k, &[c], &[])?;
                return self.show(&goal, "tr.eff_req", s, vec![A::G(G::By(h))]);
            }
            // a statement's choice (`either`): each one's
            if st {
                let k1 = self.prove(st, s, &or[0], o)?;
                let k2 = self.prove(st, s, &or[1], o)?;
                return self.show(&goal, "tr.seff_or", s, vec![A::G(G::By(k1)), A::G(G::By(k2))]);
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
                let stmt_u = self.unlet(&stmt);
                // (a statement keeping the world: the rest from S, its world
                // S there -- the facts in hand still of it)
                if rule != "seq_loop" && rule != "seq_brk" && self.keeps(&stmt_u, x, s) {
                    let hs = self.sk(s, &stmt_u, x)?;
                    let (sn, sv) = self.fresh("ws");
                    let ku = self.unlet(&k);
                    let k_s = self.replace(&ku, &state, s);
                    let kf = self.close_var(&self.close_var(&self.close_var(&self.replace(&ku, &state, &sv), sn), x), o);
                    let sc = self.ctx.len();
                    self.assume(&stmt_u)?;
                    self.assume(&cond)?;
                    let kk = self.prove(st, s, &k_s, o)?;
                    self.ctx.truncate(sc);
                    let hk = self.close(kk, &[stmt_u, cond], &[x])?;
                    let lemma = format!("{pre}_seq_same");
                    let f = self.api.fact(self.env, &lemma).map_err(e)?;
                    let f = self.api.inst(self.env, f, &[("k", kf)]).map_err(|x| format!("{lemma}: {}", x.0))?;
                    let letin = self.sym("letin")?;
                    return self
                        .api
                        .by(self.env, &goal, G::Defs(Box::new(G::Apply(f, vec![A::T(s.clone()), A::G(G::By(hs)), A::G(G::By(hk))])), vec![letin]))
                        .map_err(|x| format!("{lemma}: {}", x.0));
                }
                let ha = self.prove(true, s, &stmt, x)?;
                let sc = self.ctx.len();
                self.assume(&stmt_u)?;
                self.assume(&cond)?;
                let kk = self.prove(st, &state, &k, o)?;
                self.ctx.truncate(sc);
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
        // a call of a callee with stack arguments: its tr.callee_io_s (called with exactly its k)
        if name == "gimple.call1_s" {
            let Node::Var(g, _) = args[0].node() else { return Err(format!("a call of other than a callee: {}", self.short(p))) };
            let (h, k) = self.hios.get(g).cloned().ok_or_else(|| format!("a call of an unknown callee: {}", self.short(p)))?;
            let f0 = self.api.fact(self.env, "tr.eff_call1_s").map_err(e)?;
            let a = vec![
                A::T(self.unlet(&args[0])),
                A::T(self.unlet(&args[1])),
                A::T(Term::nat(sl_kernel::Nat::from_u128(k as u128))),
                A::T(self.unlet(s)),
                A::G(G::By(h)),
                A::G(G::Simp(vec![], vec![], false)),
            ];
            return self.api.mp(self.env, f0, a).map_err(|x| format!("tr.eff_call1_s: {}", x.0));
        }
        // an unsigned 64-bit division: its own lemma (w, a, b)
        if name == "gimple.cdiv" && args.len() == 4 && args[0] == Term::nat(sl_kernel::Nat::from_u128(64)) && self.app(&args[3], "false", 0).is_some() {
            let f0 = self.api.fact(self.env, "tr.eff_cdiv64u").map_err(e)?;
            let a = vec![A::T(self.unlet(s)), A::T(self.unlet(&args[1])), A::T(self.unlet(&args[2]))];
            return self.api.mp(self.env, f0, a).map_err(|x| format!("tr.eff_cdiv64u: {}", x.0));
        }
        let mut a = terms;
        let lemma = if let Some(prim) = name.strip_prefix("gimple.") {
            let l = format!("tr.eff_{}", prim);
            match self.api.fact(self.env, &l) {
                Ok(x) => x,
                // (a procedure of the layer: inlined)
                Err(_) => return self.inline(s, *f, args).map_err(|x| format!("{} (inlined; no effect lemma `{}`): {}", name, l, x)),
            }
        } else if let Ok(x) = self.api.fact(self.env, &format!("tr.eff_{}", name.replace('.', "_"))) {
            // (a procedure with an effect lemma of its own, for any
            // arguments -- a hand-written layer's primitive)
            x
        } else {
            let pl = self.proc_lemma(*f)?;
            // (the parameters' types its lemma needs)
            let ua: Vec<Term> = args.iter().map(|x| self.unlet(x)).collect();
            let tys = self.param_types(*f, &ua);
            for i in self.typed.get(f).cloned().unwrap_or_default() {
                let p = self.app(&tys[i], "in", 2).unwrap().to_vec();
                a.push(A::G(G::By(self.ty(&p[0], &p[1])?)));
            }
            pl
        };
        // (a procedure taking callees: their hypotheses)
        for &i in self.callee_params.get(f).cloned().unwrap_or_default().iter() {
            let Node::Var(g, _) = args[i].node() else { return Err(format!("a callee argument not a callee: {}", self.short(p))) };
            a.push(A::G(G::By(self.hios.get(g).ok_or_else(|| format!("a callee argument not in scope: {}", self.short(p)))?.0.clone())));
        }
        self.api.mp(self.env, lemma, a).map_err(|x| format!("{}: {}", name, x.0))
    }

    /// `tr.eff(S, o. runs(f(args), S, o))`, f's body from S with the facts
    /// in hand
    fn inline(&mut self, s: &Term, f: SymId, args: &[Term]) -> R<Seq> {
        let SymKind::Defined { params, body } = self.env.syms[f as usize].kind.clone() else { return Err("not a definition".into()) };
        let mut b = body;
        for (p, a) in params.iter().zip(args) {
            b = b.subst_var(*p, &self.unlet(a), &self.env.binders_fn());
        }
        let m = self.app(&b, "mkprog", 1).ok_or("not a program")?.to_vec();
        let (o, ov) = self.fresh("os");
        let bo = self.open(&m[0], &[s.clone(), ov.clone()]);
        let kb = self.prove(false, s, &bo, o)?;
        let p = Term::app(f, args.to_vec());
        let goal = self.eff(false, s, &self.mk("runs", vec![p, s.clone(), ov])?, o)?;
        let ep = self.api.fact(self.env, "tr.eff_prog").map_err(e)?;
        let letin = self.sym("letin")?;
        self.api.by(self.env, &goal, G::Defs(Box::new(G::Apply(ep, vec![A::T(s.clone()), A::G(G::By(kb))])), vec![f, letin])).map_err(|x| x.0)
    }

    /// a callee's hypothesis: `tr.callee_io(g, k)`, or with more than six
    /// arguments (stack arguments, CFunS) `tr.callee_io_s(g, k)`
    fn callee_hyp(&self, g: &Term, k: usize) -> R<Term> {
        self.mk(if k > 6 { "tr.callee_io_s" } else { "tr.callee_io" }, vec![g.clone(), Term::nat(sl_kernel::Nat::from_u128(k as u128))])
    }

    /// the variables called in t (`call(g, args)`, `call1(g, args)`), with
    /// their calls' numbers of arguments (the least)
    fn called(&self, t: &Term) -> HashMap<VarId, usize> {
        let mut m: HashMap<VarId, usize> = HashMap::new();
        self.called_in(t, &mut m);
        m
    }

    fn called_in(&self, t: &Term, m: &mut HashMap<VarId, usize>) {
        for name in ["gimple.call", "gimple.call1", "gimple.call1_s", "gimple.call0", "gimple.call1_0"] {
            if let Some(c) = self.app(t, name, 2) {
                if let (Node::Var(g, _), Some(k)) = (c[0].node(), list_len(self, &c[1])) {
                    let e = m.entry(*g).or_insert(k);
                    *e = (*e).min(k);
                }
            }
        }
        // (a call from a function with stack objects: `call_objs(objs, g, args)`)
        if let Some(c) = self.app(t, "gimple.call_objs", 3).or_else(|| self.app(t, "gimple.call0_objs", 3)) {
            if let (Node::Var(g, _), Some(k)) = (c[1].node(), list_len(self, &c[2])) {
                let e = m.entry(*g).or_insert(k);
                *e = (*e).min(k);
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
                let h = self.callee_hyp(&pv, k)?;
                let hs = Seq::assume(self.env, h.clone()).map_err(e)?;
                self.hios.insert(pn, (hs, k));
                hyps.push(h);
                self.callee_params.entry(f).or_default().push(i);
            }
            body = body.subst_var(*p, &pv, &self.env.binders_fn());
            pvars.push((pn, pv));
        }
        // (its parameters' types, facts in hand: the ones its proof uses
        // its premises, first)
        let sc = self.ctx.len();
        let tys = self.param_types(f, &pvars.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>());
        for t in &tys {
            self.assume(t)?;
        }
        let m = self.app(&body, "mkprog", 1).ok_or_else(|| format!("`{}`: not a program", name))?.to_vec();
        let (o, ov) = self.fresh("os");
        let b = self.open(&m[0], &[wv.clone(), ov.clone()]);
        let call = self.mk(&name, pvars.iter().map(|(_, v)| v.clone()).collect())?;
        let runs = self.mk("runs", vec![call, wv.clone(), ov.clone()])?;
        let goal = self.eff(false, &wv, &runs, o)?;
        let kb = self.prove(false, &wv, &b, o)?;
        self.ctx.truncate(sc);
        let ep = self.api.fact(self.env, "tr.eff_prog").map_err(e)?;
        let (fsym, letin) = (f, self.sym("letin")?);
        let r = self.api.by(self.env, &goal, G::Defs(Box::new(G::Apply(ep, vec![A::T(wv.clone()), A::G(G::By(kb))])), vec![fsym, letin])).map_err(|x| format!("{}: {}", lemma, x.0))?;
        let used: Vec<usize> = (0..tys.len()).filter(|i| r.hyps().contains(&tys[*i])).collect();
        for &i in used.iter().rev() {
            hyps.insert(0, tys[i].clone());
        }
        self.typed.insert(f, used);
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
                let h = self.callee_hyp(&Term::var(g, vec![]), k)?;
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
            let h = self.callee_hyp(&gt, cn(i))?;
            let hs = Seq::assume(self.env, h.clone()).map_err(e)?;
            self.hios.insert(gv, (hs, cn(i)));
            ghyps.push(h);
            gs.push((gv, gt));
        }
        let app = self.mk(&name, gs.iter().map(|g| g.1.clone()).collect())?;
        // fn_build(abi.ARGS, x0. mkprog(x1 x2. !ord_le(n, seq_len(x0)) || B))
        let fb = self.app(&body, "fn_build", 2).ok_or("not a `_fun` wrapper")?.to_vec();
        // (with stack arguments, a CFunS: its arguments words, exactly n)
        let words = self.mk("list_type", vec![self.mk("bits", vec![Term::nat(sl_kernel::Nat::from_u128(64))])?])?;
        let stack = fb[0] == words;
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
        let in_args = self.mk("in", vec![av.clone(), if stack { words.clone() } else { self.mk("abi.ARGS", vec![])? }])?;
        let ord_le = self.sym("ord_le")?;
        let le0 = self.mk("ord_le", vec![n.clone(), self.mk("seq_len", vec![av.clone()])?])?;
        let le = if stack { self.mk("eq", vec![self.mk("seq_len", vec![av.clone()])?, n.clone()])? } else { le0.clone() };
        let _ha = Seq::assume(self.env, in_args.clone()).map_err(e)?;
        let hl = Seq::assume(self.env, le.clone()).map_err(e)?;
        let hn = if stack { self.api.by(self.env, &le0, G::Defs(Box::new(G::Arith(vec![hl])), vec![ord_le])).map_err(|x| format!("{}.io: {}", self.prefix, x.0))? } else { hl };
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
        let io_goal = self.mk(if stack { "tr.callee_io_s" } else { "tr.callee_io" }, vec![app.clone(), n.clone()])?;
        let cio = self.api.fact(self.env, if stack { "tr.callee_io_s_fun" } else { "tr.callee_io_fun" }).map_err(e)?;
        let io = self.api.by(self.env, &io_goal, G::Defs(Box::new(G::Apply(cio, vec![A::T(n), A::G(G::By(g1))])), vec![spec, letin])).map_err(|x| format!("{}.io: {}", self.prefix, x.0))?;
        let gvs: Vec<VarId> = gs.iter().map(|g| g.0).collect();
        let io = self.close(io, &ghyps, &gvs)?;
        self.out.push((format!("{}.io", self.prefix), io));
        // its spec typed
        let ty_goal = self.mk("in", vec![app, self.mk("fn_space", vec![fb[0].clone(), self.mk("powerset", vec![self.mk("univ", vec![Term::nat(sl_kernel::Nat::from_u128(1))])?])?])?])?;
        let ft = self.api.fact(self.env, if stack { "tr.fun_typed_s" } else { "tr.fun_typed" }).map_err(e)?;
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
