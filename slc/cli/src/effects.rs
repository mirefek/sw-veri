//! A spec's bookkeeping for its callers (`tr.callee_io`), proven from the
//! spec's structure with proofs/translate_effects.core's lemmas: one step
//! per construct, no search. Emitted into the function's certificate by
//! `slc translate`.
//!
//! The proof of `tr.eff(S, o. R)` (a program's outcomes R from the state S)
//! follows R:
//! - `bind_rel(p, S, s v. K, ..)`: tr.eff_bind, p's effect and K's (for
//!   each return of p);
//! - `any_rel(x. d, x. K)`: tr.eff_any, K's for each choice;
//! - `undefined if c; ..` (the elaborator's statement sequence):
//!   tr.eff_undef_if, the rest's when c fails;
//! - `o = ok(S, v)`: tr.eff_ret;
//! - `letin(a, x. R)`: R with a (unfolded by `defs(.., letin)`);
//! - `runs(P(args), S, o)`: GIMPLE's primitive P (tr.eff_P), or a procedure
//!   of the program (its own lemma, emitted first).

use sl_kernel::syntax::Printer;
use sl_kernel::{Env, Node, SymId, SymKind, Term, VarId};
use std::collections::{BTreeSet, HashSet};

pub struct Eff<'e> {
    env: &'e mut Env,
    /// the lemma prefix (the certificate's)
    prefix: String,
    n: usize,
    /// the program's procedures with an effect lemma (emitted or under way)
    procs: BTreeSet<SymId>,
    /// the procedures' lemmas, in order
    out: Vec<String>,
    /// the lemmas loaded
    known: HashSet<String>,
}

type R<T> = Result<T, String>;

impl<'e> Eff<'e> {
    pub fn new(env: &'e mut Env, prefix: &str, known: HashSet<String>) -> Eff<'e> {
        Eff { env, prefix: prefix.to_string(), n: 0, procs: BTreeSet::new(), out: Vec::new(), known }
    }

    fn app<'t>(&self, t: &'t Term, name: &str, n: usize) -> Option<&'t [Term]> {
        match t.node() {
            Node::App(s, a) if self.env.syms[*s as usize].name == name && a.len() == n => Some(a),
            _ => None,
        }
    }

    fn mk(&self, name: &str, args: Vec<Term>) -> R<Term> {
        let s = self.env.sym_by_name.get(name).ok_or_else(|| format!("no `{}` loaded", name))?;
        Ok(Term::app(*s, args))
    }

    /// `t` printed, its `letin`s reduced (as `defs(.., letin)` reads it)
    fn print(&self, t: &Term) -> String {
        Printer::new(self.env).term(&self.unlet(t))
    }

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

    fn fresh(&mut self, p: &str) -> (String, Term) {
        self.n += 1;
        let name = format!("{}{}", p, self.n);
        let v = self.env.new_var(&name, 0);
        (name, Term::var(v, vec![]))
    }

    /// `t` under k binders, those bound to `vals` (outermost first)
    fn open(&self, t: &Term, vals: &[Term]) -> Term {
        t.instantiate_params(vals, &self.env.binders_fn())
    }

    /// `t` with the variable `v` bound (at the top: BVar(0))
    fn close(&self, t: &Term, v: VarId) -> Term {
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

    /// `tr.eff(S, o. R)` (a program) or `tr.seff(S, x. R)` (a statement),
    /// R over the outcome variable `o`
    fn eff(&self, st: bool, s: &Term, r: &Term, o: VarId) -> R<String> {
        Ok(self.print(&self.mk(if st { "tr.seff" } else { "tr.eff" }, vec![s.clone(), self.close(r, o)])?))
    }

    /// The proof lines (at `ind`) of `tr.eff(S, o. R)` (`st`: of
    /// `tr.seff(S, o. R)`), ending in `show`.
    fn prove(&mut self, st: bool, s: &Term, r: &Term, o: VarId, ind: &str) -> R<Vec<String>> {
        let ov = Term::var(o, vec![]);
        let (pre, sp) = (if st { "tr.seff" } else { "tr.eff" }, self.print(s));
        let show = |rule: &str, args: &str| format!("{ind}show by defs(apply({pre}_{rule}, {{{sp}}}{args}), letin)");
        // letin(a, x. R): R with a
        if let Some(a) = self.app(r, "letin", 2) {
            let r2 = self.open(&a[1], &[a[0].clone()]);
            return self.prove(st, s, &r2, o, ind);
        }
        // o = ok(S, v); a statement's: o = ok(pair(S, l), v), o = exc(pair(S, l), pair("ret", v))
        if let Some(e) = self.app(r, "eq", 2) {
            if e[0] == ov {
                let at_s = |t: &Term| if st { self.app(t, "pair", 2).is_some_and(|p| p[0] == *s) } else { *t == *s };
                if let Some(k) = self.app(&e[1], "ok", 2) {
                    if at_s(&k[0]) {
                        return Ok(vec![show(if st { "ok" } else { "ret" }, "")]);
                    }
                }
                if let Some(k) = self.app(&e[1], "exc", 2) {
                    let label = |l: &[u8]| self.app(&k[1], "pair", 2).is_some_and(|p| matches!(p[0].node(), Node::Bytes(b) if &b[..] == l));
                    if st && at_s(&k[0]) && label(b"ret") {
                        return Ok(vec![show("ret", "")]);
                    }
                    if st && at_s(&k[0]) && label(b"brk") {
                        return Ok(vec![show("brk", "")]);
                    }
                }
            }
        }
        // bind_rel(p, S, s v. K, ..)
        if let Some(b) = self.app(r, "bind_rel", 5) {
            if b[1] != *s {
                return Err(format!("a sequence not from the current state: {}", self.print(r)));
            }
            let pe = self.prog_eff(s, &b[0])?;
            let (sn, sv) = self.fresh("ws");
            let (vn, vv) = self.fresh("vs");
            let k = self.open(&b[2], &[sv.clone(), vv.clone()]);
            let h = format!("k{}", self.n);
            let runs = self.print(&self.mk("runs", vec![b[0].clone(), s.clone(), self.mk("ok", vec![sv.clone(), vv.clone()])?])?);
            let mut out = vec![format!("{ind}have {h}: all {sn} {vn}. {runs} -> {} proof", self.eff(st, &sv, &k, o)?), format!("{ind}  fix {sn} {vn}"), format!("{ind}  assume _")];
            out.extend(self.prove(st, &sv, &k, o, &format!("{ind}  "))?);
            out.push(format!("{ind}qed"));
            out.push(show("bind", &format!(", {pe}, {h}")));
            return Ok(out);
        }
        // a statement `while`: while_rel(pair(S, loc), l. c, l o. B, l. tr, o), the body's
        // effect from each state with the condition
        if let Some(wl) = self.app(r, "while_rel", 5) {
            if st && wl[4] == ov && self.app(&wl[0], "pair", 2).is_some_and(|p| p[0] == *s) {
                let (ln, lv) = self.fresh("ls");
                let c = self.open(&wl[1], &[lv.clone()]);
                let b = self.open(&wl[2], &[lv.clone(), ov.clone()]);
                let ls = self.mk("fst", vec![lv.clone()])?;
                let h = format!("k{}", self.n);
                let mut out = vec![format!("{ind}have {h}: all {ln}. {} -> {} proof", self.print(&c), self.eff(true, &ls, &b, o)?), format!("{ind}  fix {ln}"), format!("{ind}  assume _")];
                out.extend(self.prove(true, &ls, &b, o, &format!("{ind}  "))?);
                out.push(format!("{ind}qed"));
                out.push(show("while", &format!(", {h}")));
                return Ok(out);
            }
        }
        // any_rel(x. d, x. K)
        if let Some(a) = self.app(r, "any_rel", 2) {
            let (xn, xv) = self.fresh("cs");
            let d = self.open(&a[0], &[xv.clone()]);
            let k = self.open(&a[1], &[xv.clone()]);
            let h = format!("k{}", self.n);
            let mut out = vec![format!("{ind}have {h}: all {xn}. {} -> {} proof", self.print(&d), self.eff(st, s, &k, o)?), format!("{ind}  fix {xn}"), format!("{ind}  assume _")];
            out.extend(self.prove(st, s, &k, o, &format!("{ind}  "))?);
            out.push(format!("{ind}qed"));
            out.push(show("any", &format!(", {h}")));
            return Ok(out);
        }
        if let Some(or) = self.app(r, "or", 2) {
            // a statement `undefined if c`: c || (!c && o = ok(pair(S, empty), empty))
            if st {
                if let Some(nc) = self.app(&or[1], "and", 2) {
                    if self.app(&nc[0], "not", 1).is_some_and(|n| n[0] == or[0]) && self.app(&nc[1], "eq", 2).is_some_and(|e| e[0] == ov) {
                        return Ok(vec![show("undef_if", "")]);
                    }
                }
            }
            // `if c`: (c && R1) || (!c && R2)
            if let (Some(a1), Some(a2)) = (self.app(&or[0], "and", 2), self.app(&or[1], "and", 2)) {
                if self.app(&a2[0], "not", 1).is_some_and(|n| n[0] == a1[0]) {
                    let (c, r1, r2) = (a1[0].clone(), a1[1].clone(), a2[1].clone());
                    let cs = self.print(&c);
                    let h1 = format!("k{}", self.n + 1);
                    self.n += 1;
                    let mut out = vec![format!("{ind}have {h1}: {cs} -> {} proof", self.eff(st, s, &r1, o)?), format!("{ind}  assume _")];
                    out.extend(self.prove(st, s, &r1, o, &format!("{ind}  "))?);
                    out.push(format!("{ind}qed"));
                    let h2 = format!("k{}", self.n + 1);
                    self.n += 1;
                    out.push(format!("{ind}have {h2}: !({cs}) -> {} proof", self.eff(st, s, &r2, o)?));
                    out.push(format!("{ind}  assume _"));
                    out.extend(self.prove(st, s, &r2, o, &format!("{ind}  "))?);
                    out.push(format!("{ind}qed"));
                    out.push(show("if", &format!(", {h1}, {h2}")));
                    return Ok(out);
                }
            }
        }
        // a block: ex x. A(x) && ((fst(x) = 0 && K(x, o)) || ..), its statement's outcome dispatched
        if let Some(e) = self.app(r, "ex", 1) {
            if let Some(a) = self.app(&e[0], "and", 2) {
                let (xn, xv) = self.fresh("xs");
                let Node::Var(x, _) = xv.node() else { unreachable!() };
                let x = *x;
                let stmt = self.open(&a[0], &[xv.clone()]);
                let disp = self.open(&a[1], &[xv.clone()]);
                let norm = self.app(&disp, "or", 2).and_then(|d| self.app(&d[0], "and", 2)).ok_or_else(|| format!("not a block's dispatch: {}", Printer::new(self.env).short(r)))?.to_vec();
                let k = norm[1].clone();
                // (after a loop: its normal or "brk" exit goes on; in a loop
                // body: a "brk" passed on)
                let after_loop = self.app(&norm[0], "or", 2).is_some();
                let passes_brk = self.app(&disp, "or", 2).is_some_and(|d| mentions_bytes(&d[1], b"brk"));
                let (rule, cond) = match (after_loop, st, passes_brk) {
                    (true, false, _) => ("seq_loop", format!("(fst({xn}) = 0 || (fst({xn}) = 1 && fst(out_value({xn})) = \"brk\"))")),
                    (false, true, true) => ("seq_brk", format!("fst({xn}) = 0")),
                    (false, _, false) => ("seq", format!("fst({xn}) = 0")),
                    _ => return Err(format!("a block's dispatch not covered: {}", Printer::new(self.env).short(r))),
                };
                let state = self.mk("fst", vec![self.mk("out_state", vec![xv.clone()])?])?;
                let ha = format!("k{}", self.n);
                let mut out = vec![format!("{ind}have {ha}: {} proof", self.eff(true, s, &stmt, x)?)];
                out.extend(self.prove(true, s, &stmt, x, &format!("{ind}  "))?);
                out.push(format!("{ind}qed"));
                let hk = format!("k{}", self.n + 1);
                self.n += 1;
                out.push(format!("{ind}have {hk}: all {xn}. {} -> {cond} -> {} proof", self.print(&stmt), self.eff(st, &state, &k, o)?));
                out.push(format!("{ind}  fix {xn}"));
                out.push(format!("{ind}  assume _ _"));
                out.extend(self.prove(st, &state, &k, o, &format!("{ind}  "))?);
                out.push(format!("{ind}qed"));
                out.push(show(rule, &format!(", {ha}, {hk}")));
                return Ok(out);
            }
        }
        Err(format!("no effect rule for: {}", Printer::new(self.env).short(r)))
    }

    /// The proof expression of `tr.eff(S, o. runs(p, S, o))`.
    fn prog_eff(&mut self, s: &Term, p: &Term) -> R<String> {
        let Node::App(f, args) = p.node() else { return Err(format!("not a program application: {}", self.print(p))) };
        let name = self.env.syms[*f as usize].name.clone();
        let mut terms = vec![format!("{{{}}}", self.print(s))];
        terms.extend(args.iter().map(|a| format!("{{{}}}", self.print(a))));
        let lemma = if let Some(prim) = name.strip_prefix("gimple.") {
            let l = format!("tr.eff_{}", prim);
            if !self.known.contains(&l) {
                return Err(format!("no effect lemma `{}` (proofs/translate_effects.core)", l));
            }
            l
        } else {
            self.proc_lemma(*f)?
        };
        Ok(format!("all_elim({}, {})", lemma, terms.join(", ")))
    }

    /// The program's procedure `f` (a definition `mkprog(x0 x1. B)`): its
    /// effect lemma, emitted once.
    fn proc_lemma(&mut self, f: SymId) -> R<String> {
        let name = self.env.syms[f as usize].name.clone();
        let short = name.rsplit('.').next().unwrap_or(&name).to_string();
        let lemma = format!("{}.eff_{}", self.prefix, short);
        if self.procs.contains(&f) {
            return Ok(lemma);
        }
        self.procs.insert(f);
        let SymKind::Defined { params, body } = self.env.syms[f as usize].kind.clone() else { return Err(format!("`{}` is not a definition", name)) };
        let (wn, wv) = self.fresh("ws");
        let mut pnames = Vec::new();
        let mut body = body;
        for p in &params {
            if self.env.vars[*p as usize].arity > 0 {
                return Err(format!("`{}`: a procedure taking a function", name));
            }
            let (pn, pv) = self.fresh("as");
            body = body.subst_var(*p, &pv, &self.env.binders_fn());
            pnames.push((pn, pv));
        }
        let m = self.app(&body, "mkprog", 1).ok_or_else(|| format!("`{}`: not a program", name))?.to_vec();
        let (_, ov) = self.fresh("os");
        let Node::Var(o, _) = ov.node() else { unreachable!() };
        let o = *o;
        let b = self.open(&m[0], &[wv.clone(), ov.clone()]);
        let call = self.mk(&name, pnames.iter().map(|(_, v)| v.clone()).collect())?;
        let runs = self.mk("runs", vec![call, wv.clone(), ov.clone()])?;
        let stmt = format!("all {wn}{}. {}", pnames.iter().map(|(n, _)| format!(" {}", n)).collect::<String>(), self.eff(false, &wv, &runs, o)?);
        let mut lines = vec![
            format!("theorem {lemma}: {stmt}"),
            "proof".into(),
            format!("  fix {wn}{}", pnames.iter().map(|(n, _)| format!(" {}", n)).collect::<String>()),
            format!("  have kb: {} proof", self.eff(false, &wv, &b, o)?),
        ];
        lines.extend(self.prove(false, &wv, &b, o, "    ")?);
        lines.push("  qed".into());
        lines.push(format!("  show by defs(apply(tr.eff_prog, {{{wn}}}, kb), {name}, letin)"));
        lines.push("qed".into());
        self.out.push(lines.join("\n") + "\n");
        Ok(lemma)
    }

    /// For the spec `spec` (a `_fun` wrapper of one argument, no callee
    /// parameters): its effect lemmas, `{prefix}.io` (tr.callee_io) and
    /// `{prefix}.typed`; Err with the reason if a construct has no rule.
    pub fn callee_io(&mut self, spec: SymId) -> R<String> {
        let name = self.env.syms[spec as usize].name.clone();
        let SymKind::Defined { params, body } = self.env.syms[spec as usize].kind.clone() else { return Err(format!("`{}` is not a definition", name)) };
        if !params.is_empty() {
            return Err("a spec with callees: not yet".into());
        }
        for l in ["tr.eff", "tr.callee_io_fun", "tr.fun_typed"] {
            if !self.env.sym_by_name.contains_key(l) && !self.known.contains(l) {
                return Err(format!("`{}` not loaded (proofs/translate_effects.core)", l));
            }
        }
        // fn_build(abi.ARGS, x0. mkprog(x1 x2. !ord_le(n, seq_len(x0)) || B))
        let fb = self.app(&body, "fn_build", 2).ok_or("not a `_fun` wrapper")?.to_vec();
        let (an, av) = self.fresh("as");
        let (wn, wv) = self.fresh("ws");
        let (_, ov) = self.fresh("os");
        let Node::Var(o, _) = ov.node() else { unreachable!() };
        let o = *o;
        let m = self.open(&fb[1], &[av.clone()]);
        let mp = self.app(&m, "mkprog", 1).ok_or("not a `_fun` wrapper")?.to_vec();
        let wrapper = self.open(&mp[0], &[wv.clone(), ov.clone()]);
        // (the arity guard `!ord_le(n, seq_len(args)) || B`; none without arguments)
        let guard = self.app(&wrapper, "or", 2).and_then(|or| {
            let g = self.app(&or[0], "not", 1).and_then(|g| self.app(&g[0], "ord_le", 2))?;
            Some((self.print(&g[0]), or[1].clone()))
        });
        let (n, body) = match &guard {
            Some((n, b)) => (n.clone(), b.clone()),
            None => ("0".to_string(), wrapper.clone()),
        };
        let runs = self.mk("runs", vec![m.clone(), wv.clone(), ov.clone()])?;
        let mut lines = vec![
            format!("theorem {}.io: tr.callee_io({name}(), {n})", self.prefix),
            "proof".into(),
            format!(
                "  have g: all {an} {wn}. {an} in abi.ARGS -> ord_le({n}, seq_len({an})) -> {} proof",
                self.eff(false, &wv, &runs, o)?
            ),
            format!("    fix {an} {wn}"),
            "    assume _ hn".into(),
            format!("    have kb: {} proof", self.eff(false, &wv, &body, o)?),
        ];
        lines.extend(self.prove(false, &wv, &body, o, "      ")?);
        lines.push("    qed".into());
        lines.push(if guard.is_some() {
            format!("    show by defs(apply(tr.eff_prog, {{{wn}}}, apply(tr.eff_guard, {{{wn}}}, hn, kb)), letin)")
        } else {
            format!("    show by defs(apply(tr.eff_prog, {{{wn}}}, kb), letin)")
        });
        lines.push("  qed".into());
        lines.push(format!("  show by defs(apply(tr.callee_io_fun, {{{n}}}, g), {name}, letin)"));
        lines.push("qed".into());
        let mut text = String::from("// as a callee: its spec's returns keep the world valid, or it is undefined\n// (proofs/translate_effects.core); its spec typed\n");
        for l in &self.out {
            text.push_str(l);
            text.push('\n');
        }
        text.push_str(&(lines.join("\n") + "\n\n"));
        text.push_str(&format!(
            "theorem {p}.typed: {name}() in fn_space(abi.ARGS, powerset(univ(1)))\nproof\n  show by defs(tr.fun_typed, {name})\nqed\n",
            p = self.prefix
        ));
        Ok(text)
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
