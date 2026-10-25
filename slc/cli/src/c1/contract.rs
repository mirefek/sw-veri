//! A function's wrapper theorems (`contract FN SPEC by THM [call ABBR]
//! [using L, ..]`) from the refinement THM of its procedure, proven
//! through the kernel (`sl_proof::api`), no proof text:
//! - `THM_fun`: the C function value (FN's `_fun`, its arguments from the
//!   registers, its result cast) refines the spec function SPEC, by the
//!   wrapper lemma of its shape (`g.fun_res_ghost`, `_ghost0`,
//!   `g.fun_void_ghost`, `_void0_ghost`); THM's premises on the procedure's
//!   arguments shown (by `simp`, `arith`, the facts L), the others kept;
//! - `THM_divg`: SPEC diverges nowhere it does not also raise
//!   (`divergence`, with the ghost family's lemmas);
//! - `THM_implements`: FN's machine code implements SPEC (its C1 theorem
//!   `P.implements` and its CFG form refining the structured one, `refines`,
//!   by `tr.implements_refine`, `tr.implements_abi_g`), its callees given
//!   by their C1 premises and THM's;
//! - `THM_linked`: the same with the callees C1 linked (`P.linked`), their
//!   premises met by theorems (one of exactly that statement, or a callee's
//!   `_call_linked`), THM's others (the configuration's) kept;
//! - with `call ABBR` (what a caller relies on of a callee f called as FN,
//!   `ABBR(.., f)`): `THM_call_ref` (a callee refining one called as FN is
//!   called as FN too) and `THM_call_linked` (FN's CFG form, linked, called
//!   as FN: from `THM_q`, the structured form called as FN).
//!
//! THM: `all xs. ps -> refines_ghost(PROC(args), Q(sargs), abi.World, G)`
//! (or without the ghost part, `refines(PROC(args), Q(sargs), abi.World)`),
//! PROC the procedure FN's structured `_fun` calls.

use sl_kernel::ext::seq::Seq;
use sl_kernel::syntax::Printer;
use sl_kernel::{Env, Node, SymId, SymKind, Term, VarId};
use sl_proof::api::{Api, A, G};
use std::collections::HashMap;

type R<T> = Result<T, String>;

fn e(x: sl_kernel::KernelError) -> String {
    x.0
}

pub fn contract(env: &mut Env, fname: &str, spec: &str, by: &str, call: Option<&str>, hints: &[String]) -> R<Vec<(String, Seq)>> {
    let api = Api::new(env, Vec::new()).map_err(e)?;
    let mut hs = Vec::new();
    for h in hints {
        hs.push(api.fact(env, h).map_err(e)?);
    }
    let mut c = Ct { env, api, n: 0, hints: hs, out: Vec::new() };
    c.run(fname, spec, by, call).map_err(|x| format!("contract {}: {}", fname, x))?;
    Ok(c.out)
}

struct Ct<'e> {
    env: &'e mut Env,
    api: Api,
    n: usize,
    /// the facts L
    hints: Vec<Seq>,
    out: Vec<(String, Seq)>,
}

/// What `run` made and found, for the machine-code theorems
struct Cx {
    by: String,
    /// FN's CFG and structured `_fun`s
    csym: SymId,
    ssym: SymId,
    ws: Wrap,
    wq: Wrap,
    /// THM's premises kept (over SPEC's and the callees' parameters, and
    /// `extras`)
    kept: Vec<Term>,
    /// THM's variables only its premises have (a callee's own callees:
    /// `runs(g[regs], ..) -> runs(F(g2)[regs], ..)`), quantified after the
    /// callees
    extras: Vec<VarId>,
    /// THM_fun; THM_divg / THM_divw (open in SPEC's parameters)
    fun: Seq,
    divg: Seq,
    /// the ghost part (none: SPEC over the world alone)
    gh: Option<Term>,
    qf: Term,
    /// FN's C1 theorem (`P.implements`), its `refines` theorem
    c1: String,
    rf: String,
}

/// How a premise is met: assumed (a hypothesis of the theorem made), or a
/// linked callee's by a theorem
#[derive(Clone, Copy, PartialEq)]
enum Meet {
    Assume,
    Link,
}

/// A `_fun` definition opened: its parameters (fresh variables), the
/// argument list (a fresh variable), the procedure's call on it, the
/// arity guard's n (none: no arguments), the result's width (none: void)
struct Wrap {
    params: Vec<VarId>,
    regs: VarId,
    call: Term,
    n: Option<Term>,
    width: Option<Term>,
}

impl<'e> Ct<'e> {
    fn app<'t>(&self, t: &'t Term, name: &str, n: usize) -> Option<&'t [Term]> {
        match t.node() {
            Node::App(s, a) if self.env.syms[*s as usize].name == name && a.len() == n => Some(a),
            _ => None,
        }
    }

    fn head(&self, t: &Term) -> Option<String> {
        match t.node() {
            Node::App(s, _) => Some(self.env.syms[*s as usize].name.clone()),
            _ => None,
        }
    }

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

    fn fact(&self, name: &str) -> R<Seq> {
        self.api.fact(self.env, name).map_err(e)
    }

    fn fresh(&mut self, p: &str) -> (VarId, Term) {
        self.n += 1;
        let v = self.env.new_var(&format!("{}{}", p, self.n), 0);
        (v, Term::var(v, vec![]))
    }

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

    fn has_var(&self, t: &Term, v: VarId) -> bool {
        let mut vs = Vec::new();
        t.vars(&mut vs);
        vs.contains(&v)
    }

    /// `all xs. p1 -> .. -> c`: xs opened (fresh variables), the premises, c
    fn strip(&mut self, t: &Term) -> (Vec<VarId>, Vec<Term>, Term) {
        let all = self.api.lg.all;
        let imp = self.env.builtins.imp;
        let mut vs = Vec::new();
        let mut t = t.clone();
        while let Node::App(a, x) = t.node() {
            if *a != all {
                break;
            }
            let name = t.binder_name().unwrap_or("x").to_string();
            let (v, vt) = self.fresh(&name);
            let b = self.open(&x[0], &[vt]);
            vs.push(v);
            t = b;
        }
        let mut ps = Vec::new();
        while let Node::App(i, pc) = t.node() {
            if *i != imp {
                break;
            }
            ps.push(pc[0].clone());
            let n = pc[1].clone();
            t = n;
        }
        (vs, ps, t)
    }

    /// `all xs. p1 -> .. -> c`'s c, unopened (its bound variables BVars)
    fn final_concl(&self, t: &Term) -> Term {
        let all = self.api.lg.all;
        let imp = self.env.builtins.imp;
        let mut t = t.clone();
        loop {
            let n = match t.node() {
                Node::App(a, x) if *a == all => x[0].clone(),
                Node::App(i, x) if *i == imp => x[1].clone(),
                _ => return t,
            };
            t = n;
        }
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

    /// first-order matching of `pat` (its variables `vars`, bound in b) with t
    fn pmatch(&self, pat: &Term, t: &Term, vars: &[VarId], b: &mut HashMap<VarId, Term>, d: u32) -> bool {
        match (pat.node(), t.node()) {
            // (a variable bound to a term with no bound variable of the
            // binders above it: under them too)
            (Node::Var(v, a), _) if a.is_empty() && vars.contains(v) => match b.get(v) {
                Some(x) => x == t,
                None if d == 0 || t.loose_depth(&self.env.binders_fn()) == 0 => {
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

    /// the first `gimple.result(w, _)` in t: w
    fn result_width(&self, t: &Term) -> Option<Term> {
        if let Some(a) = self.app(t, "gimple.result", 2) {
            return Some(a[0].clone());
        }
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => a.iter().find_map(|x| self.result_width(x)),
            _ => None,
        }
    }

    /// the definition `name`: its parameters, its body
    fn def_of(&self, name: &str) -> R<(Vec<VarId>, Term)> {
        let s = self.sym(name)?;
        match &self.env.syms[s as usize].kind {
            SymKind::Defined { params, body } => Ok((params.clone(), body.clone())),
            _ => Err(format!("`{}` is not a definition", name)),
        }
    }

    /// a `_fun` definition opened: `fn_build(abi.ARGS, x0. mkprog(x1 x2.
    /// [!ord_le(n, seq_len(x0)) ||] bind_rel(P(x0), x1, K, ..)))`
    fn wrap(&mut self, name: &str) -> R<Wrap> {
        let (ps, body) = self.def_of(name)?;
        let mut params = Vec::new();
        let mut body = body;
        for (i, p) in ps.iter().enumerate() {
            let (v, vt) = self.fresh(&format!("g{}_", i));
            body = body.subst_var(*p, &vt, &self.env.binders_fn());
            params.push(v);
        }
        let fb = self.app(&body, "fn_build", 2).ok_or_else(|| format!("`{}`: not a `_fun` wrapper", name))?.to_vec();
        let (regs, rv) = self.fresh("regs");
        let (_, wv) = self.fresh("ws");
        let (_, ov) = self.fresh("os");
        let m = self.open(&fb[1], &[rv]);
        let mp = self.app(&m, "mkprog", 1).ok_or_else(|| format!("`{}`: not a `_fun` wrapper", name))?.to_vec();
        let w = self.open(&mp[0], &[wv, ov]);
        let guard = self.app(&w, "or", 2).and_then(|or| {
            let g = self.app(&or[0], "not", 1).and_then(|g| self.app(&g[0], "ord_le", 2))?;
            Some((g[0].clone(), or[1].clone()))
        });
        let (n, b) = match guard {
            Some((n, b)) => (Some(n), b),
            None => (None, w),
        };
        let br = self.app(&b, "bind_rel", 5).ok_or_else(|| format!("`{}`: its program not a procedure's call", name))?.to_vec();
        let width = self.result_width(&br[2]);
        Ok(Wrap { params, regs, call: br[0].clone(), n, width })
    }

    /// the theorems by their statement's last conclusion (and the statement)
    fn find_thm(&self, ok: impl Fn(&Self, &str, &Term, &Term) -> bool) -> Vec<String> {
        self.env
            .theorems
            .iter()
            .filter(|(n, t)| {
                let s = Seq::of_thm(t).concl().clone();
                ok(self, n, &self.final_concl(&s), &s)
            })
            .map(|(n, _)| n.clone())
            .collect()
    }

    /// `all x. b`: b (x a BVar)
    fn all_body(&self, t: &Term) -> Option<Term> {
        match t.node() {
            Node::App(a, x) if *a == self.api.lg.all => Some(x[0].clone()),
            _ => None,
        }
    }

    /// `a -> b`: a, b
    fn imp_parts(&self, t: &Term) -> Option<(Term, Term)> {
        match t.node() {
            Node::App(i, x) if *i == self.env.builtins.imp => Some((x[0].clone(), x[1].clone())),
            _ => None,
        }
    }

    /// t mentions the symbol s
    fn mentions(t: &Term, s: SymId) -> bool {
        match t.node() {
            Node::App(h, a) => *h == s || a.iter().any(|x| Self::mentions(x, s)),
            Node::Var(_, a) => a.iter().any(|x| Self::mentions(x, s)),
            _ => false,
        }
    }

    fn one(&self, what: &str, v: Vec<String>) -> R<String> {
        match v.as_slice() {
            [x] => Ok(x.clone()),
            [] => Err(format!("no theorem found for {}", what)),
            _ => Err(format!("several theorems for {}: {}", what, v.join(", "))),
        }
    }

    /// a premise on the procedure's arguments: by `simp`, `arith` or
    /// propositionally, from the facts L
    fn side(&mut self, p: &Term, prior: &[Seq]) -> R<Seq> {
        let mut hs = self.hints.clone();
        hs.extend(prior.iter().cloned());
        let mut errs = Vec::new();
        for g in [G::Simp(hs.clone(), Vec::new(), false), G::Arith(hs.clone()), G::Taut(hs.clone())] {
            match self.api.by(self.env, p, g) {
                Ok(s) => return Ok(s),
                Err(x) => errs.push(x.0),
            }
        }
        Err(format!("the premise `{}` on the arguments: not by simp, arith or taut ({})", self.short(p), errs.join("; ")))
    }

    fn run(&mut self, fname: &str, spec: &str, by: &str, call: Option<&str>) -> R<()> {
        let thm = self.fact(by)?;
        let (xs, xps, xc) = self.strip(&thm.concl().clone());
        // (with the ghost part G, or without: `refines(PROC(..), SPEC(..), abi.World)`)
        let rg = match self.app(&xc, "refines_ghost", 4).or_else(|| self.app(&xc, "refines", 3)) {
            Some(a) => a.to_vec(),
            None => return Err(format!("`{}`: not `.. -> refines_ghost(PROC(..), SPEC(..), abi.World, G)` or `refines(PROC(..), SPEC(..), abi.World)`", by)),
        };
        let gh = rg.get(3).cloned();
        let proc_name = self.head(&rg[0]).ok_or("the procedure: not an application")?;
        if !proc_name.ends_with(&format!(".{}", fname)) {
            return Err(format!("`{}` is of `{}`, not of `{}`", by, proc_name, fname));
        }
        let sfun = format!("{}_fun", proc_name);
        let (module, _) = proc_name.split_once('.').ok_or("the procedure's name: no module")?;
        let cfun = format!("{}_cfg.{}_fun", module, fname);
        let ws = self.wrap(&sfun)?;
        let wq = self.wrap(spec)?;
        if ws.n.as_ref().map(|t| self.short(t)) != wq.n.as_ref().map(|t| self.short(t)) || ws.width.as_ref().map(|t| self.short(t)) != wq.width.as_ref().map(|t| self.short(t)) {
            return Err(format!("`{}` and `{}`: other wrappers (arguments, result)", sfun, spec));
        }
        // (one argument list for both)
        let rt = Term::var(ws.regs, vec![]);
        let qcall = wq.call.subst_var(wq.regs, &rt, &self.env.binders_fn());
        // THM's variables by its conclusion: the procedure's call and the
        // spec's on the argument list
        // (SPEC's parameters unknowns too: THM may be of an instance, e.g.
        // `free_meta_spec(__malloc_context, m)`, its theorems then of it)
        let mut b = HashMap::new();
        let mut unk = xs.clone();
        unk.extend(wq.params.iter().copied());
        if !self.pmatch(&rg[0], &ws.call, &xs, &mut b, 0) || !self.unify(&rg[1], &qcall, &unk, &mut b, 0) {
            return Err(format!("`{}`'s conclusion does not match `{}` / `{}`:\n  {}\n  {}", by, sfun, spec, self.short(&ws.call), self.short(&qcall)));
        }
        // (SPEC's parameters fixed: everywhere at their values; the others
        // quantified)
        let mut wq = wq;
        let fixed: Vec<(VarId, Term)> = wq.params.iter().filter_map(|v| b.get(v).map(|x| (*v, x.clone()))).collect();
        let fix = |c: &Self, t: &Term| fixed.iter().fold(t.clone(), |t, (v, x)| t.subst_var(*v, x, &c.env.binders_fn()));
        for v in &xs {
            if let Some(t) = b.get(v).cloned() {
                b.insert(*v, fix(self, &t));
            }
        }
        let qvals: Vec<Term> = wq.params.iter().map(|v| fix(self, &Term::var(*v, vec![]))).collect();
        let qcall = fix(self, &qcall);
        wq.params.retain(|v| !b.contains_key(v));
        for (v, _) in &fixed {
            b.remove(v);
        }
        // (a variable only its premises have: kept, quantified)
        let mut extras = Vec::new();
        let mut inst = thm.clone();
        for v in &xs {
            let t = match b.get(v) {
                Some(t) => t.clone(),
                None if !self.has_var(&xc, *v) => {
                    extras.push(*v);
                    Term::var(*v, vec![])
                }
                None => return Err(format!("`{}`: its variable `{}` not determined by its conclusion", by, self.env.var(*v).name)),
            };
            inst = self.api.mp(self.env, inst, vec![A::T(t)]).map_err(e)?;
        }
        // its premises: on the arguments shown, the others kept
        // (one on the arguments: from the facts L and the kept ones before
        // it, the configuration's)
        let mut kept = Vec::new();
        let mut kept_s = Vec::new();
        let mut prems = Vec::new();
        for p in xps.iter() {
            let p = b.iter().fold(p.clone(), |t, (v, x)| t.subst_var(*v, x, &self.env.binders_fn()));
            if self.has_var(&p, ws.regs) {
                prems.push(A::G(G::By(self.side(&p, &kept_s)?)));
            } else {
                let h = Seq::assume(self.env, p.clone()).map_err(e)?;
                if !kept.contains(&p) {
                    kept.push(p);
                    kept_s.push(h.clone());
                }
                prems.push(A::G(G::By(h)));
            }
        }
        let hm = self.api.mp(self.env, inst, prems).map_err(|x| format!("`{}` instantiated: {}", by, x.0))?;
        // the wrapper lemma of the shape
        let univ = match &gh {
            Some(g) => Some(self.ghost_univ(g)?),
            None => None,
        };
        let has_args = ws.n.is_some();
        let lemma = match (&ws.width, has_args, gh.is_some()) {
            (Some(_), true, true) => "g.fun_res_ghost",
            (Some(_), false, true) => "g.fun_res_ghost0",
            (None, true, true) => "g.fun_void_ghost",
            (None, false, true) => "g.fun_void0_ghost",
            (Some(_), true, false) => "g.fun_res",
            (Some(_), false, false) => "g.fun_res0",
            (None, true, false) => "g.fun_void",
            (None, false, false) => "g.fun_void0",
        };
        let (p, q) = if has_args { (self.close_var(&ws.call, ws.regs), self.close_var(&qcall, ws.regs)) } else { (ws.call.clone(), qcall.clone()) };
        let mut binds = vec![("p", p), ("q", q)];
        if let Some(g) = &gh {
            binds.push(("G", g.clone()));
        }
        if let Some(w) = &ws.width {
            binds.push(("w", w.clone()));
        }
        if let Some(n) = &ws.n {
            binds.push(("n", n.clone()));
        }
        let lf = self.fact(lemma)?;
        let lf = self.api.inst(self.env, lf, &binds).map_err(|x| format!("{}: {}", lemma, x.0))?;
        let hm = if has_args { Seq::gen(self.env, &self.api.lg, &hm, ws.regs).map_err(e)? } else { hm };
        let mut la = Vec::new();
        if let Some(u) = &univ {
            la.push(A::G(G::By(self.fact(u)?)));
        }
        la.push(A::G(G::By(hm)));
        let wl = self.api.mp(self.env, lf, la).map_err(|x| format!("{}: {}", lemma, x.0))?;
        // ... at the argument list: the two `_fun`s
        let sf = Term::app(self.sym(&sfun)?, ws.params.iter().map(|v| Term::var(*v, vec![])).collect());
        let qf = Term::app(self.sym(spec)?, qvals.clone());
        let world = self.mk("abi.World", vec![])?;
        let unf = vec![self.sym(&sfun)?, self.sym(spec)?, self.sym("letin")?];
        let mut vs = wq.params.clone();
        vs.extend(ws.params.iter().copied());
        vs.extend(extras.iter().copied());
        vs.push(ws.regs);
        let mut hyps = kept.clone();
        let fun = if let Some(g) = &gh {
            // refines_ghost(SF[regs], QF[regs], abi.World, G), regs in abi.ARGS
            let argsin = self.mk("in", vec![rt.clone(), self.mk("abi.ARGS", vec![])?])?;
            let goal = self.mk("refines_ghost", vec![self.mk("app", vec![sf.clone(), rt.clone()])?, self.mk("app", vec![qf.clone(), rt.clone()])?, world, g.clone()])?;
            let ha = Seq::assume(self.env, argsin.clone()).map_err(e)?;
            hyps.push(argsin);
            self.api.by(self.env, &goal, G::Defs(Box::new(G::Mp(wl, vec![A::T(rt.clone()), A::G(G::By(ha))])), unf)).map_err(|x| format!("{}_fun: {}", by, x.0))?
        } else {
            // regs in list_type(bits(64)) -> int_le(seq_len(regs), 6) -> s in
            // abi.World -> runs(SF[regs], s, o) -> runs(QF[regs], s, o)
            let (sv, st) = self.fresh("s");
            let (ov, ot) = self.fresh("o");
            let words = self.mk("list_type", vec![self.mk("bits", vec![Term::nat(sl_kernel::Nat::from_u128(64))])?])?;
            let ps = vec![
                self.mk("in", vec![rt.clone(), words])?,
                self.mk("int_le", vec![self.mk("seq_len", vec![rt.clone()])?, Term::nat(sl_kernel::Nat::from_u128(6))])?,
                self.mk("in", vec![st.clone(), world])?,
            ];
            let mut a = vec![A::T(rt.clone()), A::T(st.clone()), A::T(ot.clone())];
            for p in &ps {
                a.push(A::G(G::By(Seq::assume(self.env, p.clone()).map_err(e)?)));
            }
            let r = self.api.mp(self.env, wl, a).map_err(|x| format!("{}_fun: {}", by, x.0))?;
            let hr = self.mk("runs", vec![self.mk("app", vec![sf.clone(), rt.clone()])?, st.clone(), ot.clone()])?;
            let goal = self.env.mk_imp(hr.clone(), self.mk("runs", vec![self.mk("app", vec![qf.clone(), rt.clone()])?, st, ot])?);
            let fi = self.api.by(self.env, &goal, G::Defs(Box::new(G::By(r)), unf)).map_err(|x| format!("{}_fun: {}", by, x.0))?;
            let f = self.api.mp(self.env, fi, vec![A::G(G::By(Seq::assume(self.env, hr.clone()).map_err(e)?))]).map_err(e)?;
            hyps.extend(ps);
            hyps.push(hr);
            vs.push(sv);
            vs.push(ov);
            f
        };
        let fun = self.close(fun, &hyps, &vs)?;
        self.out.push((format!("{}_fun", by), fun.clone()));
        // the divergence
        let (divg, dname) = match &gh {
            Some(g) => {
                let gs = self.ghost_join(g)?;
                let dgoal = self.mk("tr.div_raises_g", vec![g.clone(), qf.clone()])?;
                (self.api.by(self.env, &dgoal, G::Divergence(vec![univ.clone().unwrap(), gs])).map_err(|x| format!("{}_divg: {}", by, x.0))?, "divg")
            }
            None => {
                let dgoal = self.mk("tr.div_raises", vec![qf.clone()])?;
                (self.api.by(self.env, &dgoal, G::Divergence(Vec::new())).map_err(|x| format!("{}_divw: {}", by, x.0))?, "divw")
            }
        };
        let divg_c = self.close(divg.clone(), &[], &wq.params)?;
        self.out.push((format!("{}_{}", by, dname), divg_c));
        // the machine code: FN's C1 theorem (`.. -> tr.implements_at(f,
        // CFUN(..), base, code, statics)`) and its CFG form refining the
        // structured one (`refines`: `.. -> runs(CFUN(..)[regs], ..) ->
        // runs(SFUN(..)[regs], ..)`)
        let csym = self.sym(&cfun)?;
        let ssym = self.sym(&sfun)?;
        let c1 = self.one(&format!("`{}`'s C1 (`.. -> tr.implements_at(_, {}(..), ..)`)", cfun, cfun), self.find_thm(|c, n, t, _| {
            n.ends_with(".implements") && c.app(t, "tr.implements_at", 5).is_some_and(|a| matches!(a[1].node(), Node::App(s, _) if *s == csym))
        }))?;
        let rf = self.one(&format!("`{}` refining `{}`", cfun, sfun), self.find_thm(|c, _, t, s| {
            c.app(t, "runs", 3).is_some_and(|a| c.app(&a[0], "app", 2).is_some_and(|x| matches!(x[0].node(), Node::App(h, _) if *h == ssym))) && Self::mentions(s, csym)
        }))?;
        let cx = Cx { by: by.to_string(), csym, ssym, ws, wq, kept, extras, fun, divg, gh, qf, c1: c1.clone(), rf };
        self.implements(&cx)?;
        let cref = match call {
            Some(abbr) => Some(self.call_ref(&cx, abbr)?),
            None => None,
        };
        // linked: the callees C1's `.linked` has (none: no callees)
        let lname = format!("{}.linked", c1.trim_end_matches(".implements"));
        let gs = if self.fact(&lname).is_ok() {
            Some(self.linked(&cx, &lname)?)
        } else if cx.ws.params.is_empty() {
            Some(Vec::new())
        } else {
            None
        };
        if let (Some(gs), Some((abbr, fi, cr))) = (&gs, cref) {
            self.call_linked(&cx, &abbr, fi, &cr, gs)?;
        }
        // (without a ghost part: the CFG form, linked, refining SPEC -- what
        // a caller's hypothesis on it is)
        if let (Some(gs), None) = (&gs, &cx.gh) {
            self.calls_linked(&cx, gs)?;
        }
        Ok(())
    }

    /// `all h. h in G -> h in univ(1)`
    fn ghost_univ(&self, gh: &Term) -> R<String> {
        // (`all h. h in G -> h in univ(1)`, h the BVar)
        let found = self.find_thm(|c, _, _, s| {
            let Some(b) = c.all_body(s) else { return false };
            let Some((p, q)) = c.imp_parts(&b) else { return false };
            let isb = |t: &Term| matches!(t.node(), Node::BVar(0));
            c.app(&p, "in", 2).is_some_and(|a| isb(&a[0]) && a[1] == *gh) && c.app(&q, "in", 2).is_some_and(|a| isb(&a[0]) && c.head(&a[1]).as_deref() == Some("univ"))
        });
        self.one(&format!("`all h. h in {} -> h in univ(1)`", self.short(gh)), found)
    }

    /// `w in abi.World -> w in univ(1) -> h in G -> union2(w, h) in univ(1) && ..`
    fn ghost_join(&mut self, gh: &Term) -> R<String> {
        let names = self.find_thm(|c, _, t, _| c.app(t, "and", 2).and_then(|a| c.app(&a[0], "in", 2).map(|b| c.head(&b[0]).as_deref() == Some("union2"))).unwrap_or(false));
        let mut found = Vec::new();
        for n in names {
            let s = self.fact(&n)?;
            let (_, ps, _) = self.strip(&s.concl().clone());
            if ps.len() == 3 && self.app(&ps[2], "in", 2).is_some_and(|a| a[1] == *gh) {
                found.push(n);
            }
        }
        self.one(&format!("`w in abi.World -> w in univ(1) -> h in {} -> union2(w, h) in univ(1) && ..`", self.short(gh)), found)
    }

    /// a premise met (`Meet`); `config`: not a callee's (assumed even when
    /// linked)
    fn meet(&mut self, p: &Term, config: bool, how: Meet, hyps: &mut Vec<Term>) -> R<Seq> {
        if how == Meet::Assume || config {
            if !hyps.contains(p) {
                hyps.push(p.clone());
            }
            return Seq::assume(self.env, p.clone()).map_err(e);
        }
        self.establish(p, hyps)
    }

    /// a linked callee's premise by a theorem: a fact L or a theorem of
    /// exactly that statement, or a callee's `_call_linked` (its
    /// configuration's premises assumed)
    fn establish(&mut self, p: &Term, hyps: &mut Vec<Term>) -> R<Seq> {
        if let Some(h) = self.hints.iter().find(|h| h.concl() == p) {
            return Ok(h.clone());
        }
        if let Some(n) = self.find_thm(|_, _, _, s| s == p).into_iter().next() {
            return self.fact(&n);
        }
        for n in self.find_thm(|_, n, _, _| Self::linking(n)) {
            let s = self.fact(&n)?;
            let Some((vs, ps, b)) = self.fit(&s, p, &[]) else { continue };
            let mut r = s.clone();
            for v in &vs {
                r = self.api.mp(self.env, r, vec![A::T(b[v].clone())]).map_err(e)?;
            }
            // (its premises: a closed one -- a callee's -- by a theorem in
            // turn; one over the caller's variables -- its configuration's --
            // assumed)
            let mut pa = Vec::new();
            for q in &ps {
                let q = b.iter().fold(q.clone(), |t, (v, x)| t.subst_var(*v, x, &self.env.binders_fn()));
                let mut qv = Vec::new();
                q.vars(&mut qv);
                pa.push(A::G(G::By(self.meet(&q, !qv.is_empty(), Meet::Link, hyps)?)));
            }
            return self.api.mp(self.env, r, pa).map_err(|x| format!("{}: {}", n, x.0));
        }
        Err(format!("no theorem for the callee's premise `{}` (none of that statement, no `_ref` or `_call_linked`; or give one by `using`)", self.short(p)))
    }

    /// a theorem `all xs. ps -> R` (some leading quantifiers and premises
    /// taken, the rest R) whose R is p, by unification (the unknowns its xs
    /// and `extra`): xs, ps, the unifier
    fn fit(&mut self, s: &Seq, p: &Term, extra: &[VarId]) -> Option<(Vec<VarId>, Vec<Term>, HashMap<VarId, Term>)> {
        let mut vs = Vec::new();
        let mut ps = Vec::new();
        let mut t = s.concl().clone();
        loop {
            let mut unk = vs.clone();
            unk.extend(extra.iter().copied());
            let mut b = HashMap::new();
            if self.unify(&t, p, &unk, &mut b, 0) && vs.iter().all(|v| b.get(v).is_some_and(|x| !vs.iter().any(|w| self.has_var(x, *w)))) {
                // (a theorem's variable bound to one of the extras: those
                // fixed by it)
                return Some((vs, ps, b));
            }
            if let Some(body) = self.all_body(&t) {
                let name = t.binder_name().unwrap_or("x").to_string();
                let (v, vt) = self.fresh(&name);
                t = self.open(&body, &[vt]);
                vs.push(v);
            } else if let Some((a, r)) = self.imp_parts(&t) {
                ps.push(a);
                t = r;
            } else {
                return None;
            }
        }
    }

    /// the theorems a linked callee's premise may come from (besides one of
    /// exactly its statement): a CFG form refining the structured one
    /// (`refines`), a callee's `_call_linked`
    fn linking(n: &str) -> bool {
        n.ends_with("_ref") || n.ends_with("_call_linked")
    }

    /// first-order unification of a and b, the variables `vars` unknowns
    /// (bound in s); a variable bound to a term without the binders' bound
    /// variables only
    fn unify(&self, a: &Term, b: &Term, vars: &[VarId], s: &mut HashMap<VarId, Term>, d: u32) -> bool {
        let bf = self.env.binders_fn();
        let res = |t: &Term, s: &HashMap<VarId, Term>| match t.node() {
            Node::Var(v, x) if x.is_empty() && vars.contains(v) => s.get(v).cloned().unwrap_or_else(|| t.clone()),
            _ => t.clone(),
        };
        let (a, b) = (res(a, s), res(b, s));
        let unknown = |t: &Term| matches!(t.node(), Node::Var(v, x) if x.is_empty() && vars.contains(v) && !s.contains_key(v));
        if a == b {
            return true;
        }
        if unknown(&a) && (d == 0 || b.loose_depth(&bf) == 0) {
            let Node::Var(v, _) = a.node() else { return false };
            s.insert(*v, b);
            return true;
        }
        if unknown(&b) && (d == 0 || a.loose_depth(&bf) == 0) {
            let Node::Var(v, _) = b.node() else { return false };
            s.insert(*v, a);
            return true;
        }
        match (a.node(), b.node()) {
            (Node::App(s1, a1), Node::App(s2, a2)) => s1 == s2 && a1.len() == a2.len() && a1.iter().zip(a2.iter()).enumerate().all(|(i, (x, y))| self.unify(x, y, vars, s, d + self.env.syms[*s1 as usize].binders[i])),
            (Node::Var(v1, a1), Node::Var(v2, a2)) => v1 == v2 && a1.len() == a2.len() && a1.iter().zip(a2.iter()).all(|(x, y)| self.unify(x, y, vars, s, d)),
            _ => false,
        }
    }

    /// the extras' values at the linked callees gs: each premise over one
    /// not yet known unified with a theorem's conclusion (`linking`)
    fn solve_extras(&mut self, cx: &Cx, gs: &[Term]) -> R<Vec<Term>> {
        let mut bind: HashMap<VarId, Term> = HashMap::new();
        let names = self.find_thm(|_, n, _, _| Self::linking(n));
        for k in cx.kept.clone() {
            let k = cx.ws.params.iter().zip(gs).fold(k, |t, (v, g)| t.subst_var(*v, g, &self.env.binders_fn()));
            let k = bind.iter().fold(k, |t, (v, x)| t.subst_var(*v, x, &self.env.binders_fn()));
            let open: Vec<VarId> = cx.extras.iter().copied().filter(|v| self.has_var(&k, *v)).collect();
            if open.is_empty() {
                continue;
            }
            let mut got = None;
            for n in &names {
                let s = self.fact(n)?;
                let Some((vs, _, sb)) = self.fit(&s, &k, &open) else { continue };
                let vals: Option<Vec<(VarId, Term)>> = open.iter().map(|v| sb.get(v).filter(|t| !vs.iter().any(|w| self.has_var(t, *w))).map(|t| (*v, t.clone()))).collect();
                if let Some(vals) = vals {
                    got = Some(vals);
                    break;
                }
            }
            let vals = got.ok_or_else(|| format!("the linked callees' premise `{}`: no `_ref` or `_call_linked` theorem fixes its variables", self.short(&k)))?;
            bind.extend(vals);
        }
        cx.extras.iter().map(|v| bind.get(v).cloned().ok_or_else(|| format!("`{}`: its variable `{}` not fixed by linking", cx.by, self.env.var(*v).name))).collect()
    }

    /// the `refines` theorem at the callees gs: `all regs s o. .. ->
    /// runs(CFUN(gs)[regs], s, o) -> runs(SFUN(gs)[regs], s, o)`
    fn refines_at(&mut self, cx: &Cx, gs: &[Term], how: Meet, hyps: &mut Vec<Term>) -> R<Seq> {
        let mut r0 = self.fact(&cx.rf)?;
        for g in gs {
            r0 = self.api.mp(self.env, r0, vec![A::T(g.clone())]).map_err(e)?;
        }
        while let Some((a, _)) = self.imp_parts(r0.concl()) {
            let h = self.meet(&a, false, how, hyps)?;
            r0 = self.api.mp(self.env, r0, vec![A::G(G::By(h))]).map_err(e)?;
        }
        Ok(r0)
    }

    /// FN's machine code implements SPEC at the callees gs, from its C1
    /// theorem there (i0: `tr.implements_at(f, CFUN(gs), ..)`)
    fn implements_at(&mut self, cx: &Cx, gs: &[Term], ext: &[Term], i0: Seq, how: Meet, hyps: &mut Vec<Term>) -> R<Seq> {
        let r0 = self.refines_at(cx, gs, how, hyps)?;
        let ir = self.fact("tr.implements_refine")?;
        let stp = self.api.apply(self.env, ir.clone(), vec![A::G(G::By(i0)), A::G(G::By(r0))], None).map_err(|x| format!("tr.implements_refine: {}", x.0))?;
        let r = self.fun_at(cx, gs, ext, how, hyps)?;
        match &cx.gh {
            Some(g) => {
                let ok = self.ghost_ok(g)?;
                let iab = self.fact("tr.implements_abi_g")?;
                self.api.apply(self.env, iab, vec![A::G(G::By(ok)), A::G(G::By(cx.divg.clone())), A::G(G::By(stp)), A::G(G::By(r))], None).map_err(|x| format!("tr.implements_abi_g: {}", x.0))
            }
            None => self.api.apply(self.env, ir, vec![A::G(G::By(stp)), A::G(G::By(r))], None).map_err(|x| format!("tr.implements_refine: {}", x.0)),
        }
    }

    /// THM_fun at SPEC's parameters, the callees gs and the extras ext, its
    /// premises met: `all args. args in abi.ARGS -> refines_ghost(..)`, or
    /// (no ghost part) `all regs s o. .. -> runs(SF(gs)[regs], s, o) ->
    /// runs(QF[regs], s, o)`
    fn fun_at(&mut self, cx: &Cx, gs: &[Term], ext: &[Term], how: Meet, hyps: &mut Vec<Term>) -> R<Seq> {
        let mut f0 = cx.fun.clone();
        for v in &cx.wq.params {
            f0 = self.api.mp(self.env, f0, vec![A::T(Term::var(*v, vec![]))]).map_err(e)?;
        }
        for g in gs.iter().chain(ext.iter()) {
            f0 = self.api.mp(self.env, f0, vec![A::T(g.clone())]).map_err(e)?;
        }
        let names: &[&str] = if cx.gh.is_some() { &["args"] } else { &["regs", "s", "o"] };
        let mut fv = Vec::new();
        for n in names {
            let (v, t) = self.fresh(n);
            f0 = self.api.mp(self.env, f0, vec![A::T(t)]).map_err(e)?;
            fv.push(v);
        }
        let mut ka = Vec::new();
        for k in &cx.kept {
            let config = !cx.ws.params.iter().chain(cx.extras.iter()).any(|v| self.has_var(k, *v));
            let k = cx.ws.params.iter().zip(gs).chain(cx.extras.iter().zip(ext)).fold(k.clone(), |t, (v, g)| t.subst_var(*v, g, &self.env.binders_fn()));
            ka.push(A::G(G::By(self.meet(&k, config, how, hyps)?)));
        }
        let f0 = self.api.mp(self.env, f0, ka).map_err(e)?;
        self.close(f0, &[], &fv)
    }

    /// `abi.implements2_at(G, f, QF, base, code, st)`, or (no ghost part)
    /// `tr.implements_at(f, QF, base, code, st)`
    fn impl_goal(&self, cx: &Cx, ia: &[Term], st: &Term) -> R<Term> {
        match &cx.gh {
            Some(g) => self.mk("abi.implements2_at", vec![g.clone(), ia[0].clone(), cx.qf.clone(), ia[2].clone(), ia[3].clone(), st.clone()]),
            None => self.mk("tr.implements_at", vec![ia[0].clone(), cx.qf.clone(), ia[2].clone(), ia[3].clone(), st.clone()]),
        }
    }

    /// THM_calls_linked (no ghost part): `all ps. config -> all regs s o. ..
    /// -> runs(CFUN(gs)[regs], s, o) -> runs(QF[regs], s, o)`
    fn calls_linked(&mut self, cx: &Cx, gs: &[Term]) -> R<()> {
        let mut hyps = Vec::new();
        let ext = self.solve_extras(cx, gs)?;
        let rf = self.refines_at(cx, gs, Meet::Link, &mut hyps)?;
        let f = self.fun_at(cx, gs, &ext, Meet::Link, &mut hyps)?;
        let mut a = Vec::new();
        let mut vs = Vec::new();
        for n in ["regs", "s", "o"] {
            let (v, t) = self.fresh(n);
            a.push(A::T(t));
            vs.push(v);
        }
        let r1 = self.api.mp(self.env, rf, a).map_err(e)?;
        // (its premises: the argument list's, the world's, the run)
        let mut ps = Vec::new();
        let mut t = r1.concl().clone();
        while let Some((p, r)) = self.imp_parts(&t) {
            ps.push(p);
            t = r;
        }
        let pa: Vec<Seq> = ps.iter().map(|p| Seq::assume(self.env, p.clone())).collect::<Result<_, _>>().map_err(e)?;
        let r1 = self.api.mp(self.env, r1, pa.iter().map(|p| A::G(G::By(p.clone()))).collect()).map_err(e)?;
        let mut a: Vec<A> = vs.iter().map(|v| A::T(Term::var(*v, vec![]))).collect();
        for p in &pa[..pa.len() - 1] {
            a.push(A::G(G::By(p.clone())));
        }
        a.push(A::G(G::By(r1)));
        let r2 = self.api.mp(self.env, f, a).map_err(|x| format!("{}_calls_linked: {}", cx.by, x.0))?;
        let r2 = self.close(r2, &ps, &vs)?;
        let res = self.close(r2, &hyps, &cx.wq.params)?;
        self.out.push((format!("{}_calls_linked", cx.by), res));
        Ok(())
    }

    /// THM_implements: the callees variables, their C1 premises and THM's
    /// assumed
    fn implements(&mut self, cx: &Cx) -> R<()> {
        let (statics, st) = self.fresh("statics");
        let c1s = self.fact(&cx.c1)?;
        let (c1v, c1p, c1c) = self.strip(&c1s.concl().clone());
        let ia = self.app(&c1c, "tr.implements_at", 5).ok_or("C1: not implements_at")?.to_vec();
        let gargs: Vec<Term> = match ia[1].node() {
            Node::App(_, a) => a.to_vec(),
            _ => Vec::new(),
        };
        if gargs.len() != cx.ws.params.len() {
            return Err(format!("`{}`: other callees than the structured form's", cx.c1));
        }
        let gs: Vec<Term> = cx.ws.params.iter().map(|v| Term::var(*v, vec![])).collect();
        let mut sub: HashMap<VarId, Term> = HashMap::new();
        for (i, g) in gargs.iter().enumerate() {
            let Node::Var(v, _) = g.node() else { return Err(format!("`{}`: its callee {} not a variable", cx.c1, i)) };
            sub.insert(*v, gs[i].clone());
        }
        let Node::Var(sv, _) = ia[4].node() else { return Err(format!("`{}`: its statics not a variable", cx.c1)) };
        sub.insert(*sv, st.clone());
        let mut i0 = c1s.clone();
        for v in &c1v {
            let t = sub.get(v).cloned().ok_or_else(|| format!("`{}`: a variable not a callee's or the statics", cx.c1))?;
            i0 = self.api.mp(self.env, i0, vec![A::T(t)]).map_err(e)?;
        }
        let mut hyps: Vec<Term> = Vec::new();
        let mut pa = Vec::new();
        for p in &c1p {
            let p = sub.iter().fold(p.clone(), |t, (v, x)| t.subst_var(*v, x, &self.env.binders_fn()));
            pa.push(A::G(G::By(self.meet(&p, false, Meet::Assume, &mut hyps)?)));
        }
        let i0 = self.api.mp(self.env, i0, pa).map_err(|x| format!("{}: {}", cx.c1, x.0))?;
        let ext: Vec<Term> = cx.extras.iter().map(|v| Term::var(*v, vec![])).collect();
        let res = self.implements_at(cx, &gs, &ext, i0, Meet::Assume, &mut hyps)?;
        let goal = self.impl_goal(cx, &ia, &st)?;
        let res = self.api.check(self.env, res, &goal).map_err(e)?;
        let mut vs = cx.wq.params.clone();
        vs.push(statics);
        vs.extend(cx.ws.params.iter().copied());
        vs.extend(cx.extras.iter().copied());
        // (no ghost part: at the ABI's level too, by its divergence)
        if cx.gh.is_none() {
            let ia2 = self.fact("tr.implements_abi")?;
            let abi = self.api.apply(self.env, ia2, vec![A::G(G::By(cx.divg.clone())), A::G(G::By(res.clone()))], None).map_err(|x| format!("{}_abi: {}", cx.by, x.0))?;
            let abi = self.close(abi, &hyps, &vs)?;
            self.out.push((format!("{}_abi", cx.by), abi));
        }
        let res = self.close(res, &hyps, &vs)?;
        self.out.push((format!("{}_implements", cx.by), res));
        Ok(())
    }

    /// THM_linked: at the callees C1's `.linked` has; its callees' premises
    /// met by theorems. The callees.
    fn linked(&mut self, cx: &Cx, lname: &str) -> R<Vec<Term>> {
        let (statics, st) = self.fresh("statics");
        let ls = self.fact(lname)?;
        let (lv, lp, lc) = self.strip(&ls.concl().clone());
        let ia = self.app(&lc, "tr.implements_at", 5).ok_or_else(|| format!("`{}`: not implements_at", lname))?.to_vec();
        if lv.len() != 1 || !lp.is_empty() || ia[4] != Term::var(lv[0], vec![]) {
            return Err(format!("`{}`: not `all statics. tr.implements_at(..)`", lname));
        }
        let gs: Vec<Term> = match ia[1].node() {
            Node::App(_, a) => a.to_vec(),
            _ => Vec::new(),
        };
        let i0 = self.api.mp(self.env, ls, vec![A::T(st.clone())]).map_err(e)?;
        let mut hyps = Vec::new();
        let ext = self.solve_extras(cx, &gs)?;
        let res = self.implements_at(cx, &gs, &ext, i0, Meet::Link, &mut hyps)?;
        let goal = self.impl_goal(cx, &ia, &st)?;
        let res = self.api.check(self.env, res, &goal).map_err(e)?;
        let mut vs = cx.wq.params.clone();
        vs.push(statics);
        let res = self.close(res, &hyps, &vs)?;
        self.out.push((format!("{}_linked", cx.by), res));
        Ok(gs)
    }

    /// `all vs. body`
    fn forall(&self, vs: &[VarId], body: Term) -> Term {
        vs.iter().rev().fold(body, |b, v| Term::app(self.api.lg.all, vec![self.close_var(&b, *v)]))
    }

    fn imps(&self, ps: &[Term], c: Term) -> Term {
        ps.iter().rev().fold(c, |c, p| self.env.mk_imp(p.clone(), c))
    }

    /// THM_call_ref: `all ps f2. (all regs s o. regs in list_type(bits(64))
    /// -> int_le(seq_len(regs), 6) -> s in abi.World -> runs(f[regs], s, o)
    /// -> runs(f2[regs], s, o)) -> ABBR(.., f2, ..) -> ABBR(.., f, ..)`.
    /// ABBR, f's position in it, the theorem.
    fn call_ref(&mut self, cx: &Cx, abbr: &str) -> R<(String, usize, Seq)> {
        let k = self.env.abbrevs.get(abbr).map(|x| x.0).ok_or_else(|| format!("no abbreviation `{}`", abbr))?;
        let ps: Vec<(VarId, Term)> = (0..k).map(|i| self.fresh(&format!("p{}_", i))).collect();
        let pts: Vec<Term> = ps.iter().map(|p| p.1.clone()).collect();
        let body = self.mk(abbr, pts.clone())?;
        let (xs, prems, post) = self.strip(&body);
        // (the callee: the parameter run, `runs(f[R], T, O)`)
        let pos = prems.iter().position(|p| self.app(p, "runs", 3).is_some_and(|a| self.app(&a[0], "app", 2).is_some_and(|x| pts.contains(&x[0])))).ok_or_else(|| format!("`{}`: no premise `runs(f[regs], t, o)` of a parameter f", abbr))?;
        let ra = self.app(&prems[pos], "runs", 3).unwrap().to_vec();
        let fa = self.app(&ra[0], "app", 2).unwrap().to_vec();
        let fi = pts.iter().position(|p| *p == fa[0]).unwrap();
        let (rr, tt, oo) = (fa[1].clone(), ra[1].clone(), ra[2].clone());
        let (f2v, f2) = self.fresh("f2_");
        // the refinement hf
        let (rv, rt) = self.fresh("regs");
        let (sv, stt) = self.fresh("s");
        let (ov, ot) = self.fresh("o");
        let words = self.mk("list_type", vec![self.mk("bits", vec![Term::nat(sl_kernel::Nat::from_u128(64))])?])?;
        let six = Term::nat(sl_kernel::Nat::from_u128(6));
        let world = self.mk("abi.World", vec![])?;
        let hf_body = self.imps(
            &[
                self.mk("in", vec![rt.clone(), words.clone()])?,
                self.mk("int_le", vec![self.mk("seq_len", vec![rt.clone()])?, six.clone()])?,
                self.mk("in", vec![stt.clone(), world.clone()])?,
                self.mk("runs", vec![self.mk("app", vec![fa[0].clone(), rt.clone()])?, stt.clone(), ot.clone()])?,
            ],
            self.mk("runs", vec![self.mk("app", vec![f2.clone(), rt])?, stt, ot])?,
        );
        let hf = self.forall(&[rv, sv, ov], hf_body);
        let mut qps = pts.clone();
        qps[fi] = f2.clone();
        let q = self.mk(abbr, qps)?;
        let hfa = Seq::assume(self.env, hf.clone()).map_err(e)?;
        let qa = Seq::assume(self.env, q.clone()).map_err(e)?;
        // ABBR(.., f, ..): its premises assumed; f's run one of f2
        let pa: Vec<Seq> = prems.iter().map(|p| Seq::assume(self.env, p.clone())).collect::<Result<_, _>>().map_err(e)?;
        let lst = self.api.by(self.env, &self.mk("in", vec![rr.clone(), words])?, G::Taut(pa.clone())).map_err(|x| format!("`{}`: its argument list's type: {}", abbr, x.0))?;
        let le_goal = self.mk("int_le", vec![self.mk("seq_len", vec![rr.clone()])?, six])?;
        let le = self.api.by(self.env, &le_goal, G::Simp(pa.clone(), Vec::new(), false)).or_else(|_| self.api.by(self.env, &le_goal, G::Arith(pa.clone()))).map_err(|x| format!("`{}`: its argument list's length: {}", abbr, x.0))?;
        let wgoal = self.mk("in", vec![tt.clone(), world])?;
        let wl = self.api.by(self.env, &wgoal, G::Taut(pa.clone())).map_err(|x| format!("`{}`: its world's type: {}", abbr, x.0))?;
        let r2 = self.api.mp(self.env, hfa, vec![A::T(rr), A::T(tt), A::T(oo), A::G(G::By(lst)), A::G(G::By(le)), A::G(G::By(wl)), A::G(G::By(pa[pos].clone()))]).map_err(e)?;
        let mut qi = qa;
        for x in &xs {
            qi = self.api.mp(self.env, qi, vec![A::T(Term::var(*x, vec![]))]).map_err(e)?;
        }
        let qargs: Vec<A> = pa.iter().enumerate().map(|(i, p)| A::G(G::By(if i == pos { r2.clone() } else { p.clone() }))).collect();
        let res = self.api.mp(self.env, qi, qargs).map_err(|x| format!("{}_call_ref: {}", cx.by, x.0))?;
        let res = self.close(res, &prems, &xs)?;
        let res = self.api.check(self.env, res, &body).map_err(e)?;
        let _ = post;
        let mut vs: Vec<VarId> = ps.iter().map(|p| p.0).collect();
        vs.push(f2v);
        let res = self.close(res, &[hf, q], &vs)?;
        self.out.push((format!("{}_call_ref", cx.by), res.clone()));
        Ok((abbr.to_string(), fi, res))
    }

    /// THM_call_linked: `all ps. config -> ABBR(.., CFUN(gs), ..)`, from
    /// THM_call_ref, the `refines` theorem and THM_q (`.. -> ABBR(..,
    /// SFUN(..), ..)`)
    fn call_linked(&mut self, cx: &Cx, abbr: &str, fi: usize, cref: &Seq, gs: &[Term]) -> R<()> {
        let k = self.env.abbrevs.get(abbr).map(|x| x.0).unwrap_or(0);
        let ps: Vec<(VarId, Term)> = (0..k).map(|i| self.fresh(&format!("p{}_", i))).collect();
        let sf = Term::app(cx.ssym, gs.to_vec());
        let cf = Term::app(cx.csym, gs.to_vec());
        let mut tp: Vec<Term> = ps.iter().map(|p| p.1.clone()).collect();
        tp[fi] = sf.clone();
        let target = self.mk(abbr, tp.clone())?;
        let qn = format!("{}_q", cx.by);
        let qs = self.fact(&qn).map_err(|_| format!("no `{}` (the structured form called as `{}`) for `{}_call_linked`", qn, abbr, cx.by))?;
        let (qv, qp, qc) = self.strip(&qs.concl().clone());
        let mut b = HashMap::new();
        if !self.pmatch(&qc, &target, &qv, &mut b, 0) {
            return Err(format!("`{}`'s conclusion not `{}` at `{}`", qn, abbr, self.short(&sf)));
        }
        let mut qi = qs.clone();
        for v in &qv {
            let t = b.get(v).cloned().ok_or_else(|| format!("`{}`: its variable `{}` not determined by its conclusion", qn, self.env.var(*v).name))?;
            qi = self.api.mp(self.env, qi, vec![A::T(t)]).map_err(e)?;
        }
        let mut hyps = Vec::new();
        let mut pa = Vec::new();
        for p in &qp {
            let p = b.iter().fold(p.clone(), |t, (v, x)| t.subst_var(*v, x, &self.env.binders_fn()));
            let config = !gs.iter().any(|g| Self::contains(&p, g));
            pa.push(A::G(G::By(self.meet(&p, config, Meet::Link, &mut hyps)?)));
        }
        let qi = self.api.mp(self.env, qi, pa).map_err(|x| format!("{}: {}", qn, x.0))?;
        let hf = self.refines_at(cx, gs, Meet::Link, &mut hyps)?;
        let mut cr = cref.clone();
        for (i, p) in ps.iter().enumerate() {
            cr = self.api.mp(self.env, cr, vec![A::T(if i == fi { cf.clone() } else { p.1.clone() })]).map_err(e)?;
        }
        let cr = self.api.mp(self.env, cr, vec![A::T(sf), A::G(G::By(hf)), A::G(G::By(qi))]).map_err(|x| format!("{}_call_linked: {}", cx.by, x.0))?;
        let vs: Vec<VarId> = ps.iter().enumerate().filter(|(i, _)| *i != fi).map(|(_, p)| p.0).collect();
        let res = self.close(cr, &hyps, &vs)?;
        self.out.push((format!("{}_call_linked", cx.by), res));
        Ok(())
    }

    /// t has the subterm s
    fn contains(t: &Term, s: &Term) -> bool {
        t == s
            || match t.node() {
                Node::App(_, a) | Node::Var(_, a) => a.iter().any(|x| Self::contains(x, s)),
                _ => false,
            }
    }

    /// `abi.ghost_ok(G)`
    fn ghost_ok(&self, gh: &Term) -> R<Seq> {
        let goal = self.mk("abi.ghost_ok", vec![gh.clone()])?;
        let n = self.one(&format!("`{}`", self.short(&goal)), self.find_thm(|_, _, _, s| *s == goal))?;
        self.fact(&n)
    }
}
