//! A function's readable CFG refines its structured form (`refines NAME
//! LOW HIGH`, proofs/gimple_cfg.core): the CFG's procedure walked with the
//! structured one, the same operations, conditions, choices on both by
//! congruence (the same terms: no operation's meaning), one side's
//! reductions on their own (the structured side's by the spec reducer).
//!
//! The walk's claim `g.ref(o. L, q, w)`: every outcome o of the CFG's side
//! (the relation L) one of the structured side's (the program q from w).

use super::rec::*;
use super::*;

pub fn refines(env: &mut Env, name: &str, low: &str, high: &str) -> Result<Seq, String> {
    let empty = Term::app(env.sym_by_name["empty"], vec![]);
    let mut g = Gen::new(env, BTreeMap::new(), empty.clone(), empty, name, name, Vec::new())?;
    g.refines(low, high)
}

/// A lower side's block `ex x8. A && K` (under the outcome o): A, K
fn block(g: &Gen, lo: &Term) -> Option<(Term, Term)> {
    let b = g.app(lo, "ex", 1)?[0].clone();
    let x = g.app(&b, "and", 2)?;
    Some((x[0].clone(), x[1].clone()))
}

impl<'e> Gen<'e> {
    /// the definition of `name`: its parameters, its body
    fn def_of(&self, name: &str) -> Result<(Vec<VarId>, Term), String> {
        let s = *self.env.sym_by_name.get(name).ok_or_else(|| format!("no `{}`", name))?;
        match &self.env.syms[s as usize].kind {
            SymKind::Defined { params, body } => Ok((params.clone(), body.clone())),
            _ => Err(format!("`{}` is not a definition", name)),
        }
    }

    /// LOW refines HIGH: the function wrappers by their procedures'
    /// refinement (g.wrap_ref, g.fun_ref)
    fn refines(&mut self, low: &str, high: &str) -> Result<Seq, String> {
        let (pl, bl) = self.def_of(low)?;
        let (ph, bh) = self.def_of(high)?;
        if pl.len() != ph.len() {
            return Err(format!("`{}` and `{}` of other parameters", low, high));
        }
        // (the callees: fixed variables, the same on both)
        let gs: Vec<Term> = (0..pl.len()).map(|i| self.var(&format!("G{i}"))).collect();
        let (mut bl, mut bh) = (bl, bh);
        for (i, gv) in gs.iter().enumerate() {
            bl = bl.subst_var(pl[i], gv, &self.env.binders_fn());
            bh = bh.subst_var(ph[i], gv, &self.env.binders_fn());
        }
        let fl = self.app(&bl, "fn_build", 2).ok_or("the low function: not fn_build")?.to_vec();
        let fh = self.app(&bh, "fn_build", 2).ok_or("the high function: not fn_build")?.to_vec();
        if self.canon(&fl[0]) != self.canon(&fh[0]) {
            return Err("the two functions' domains differ".into());
        }
        // each argument list's program: mkprog(x1 x2. [c ||] bind_rel(P(..), x1, K, X, D))
        let parts = |g: &Gen, m: &Term| -> Option<(Option<Term>, Term, Vec<Term>)> {
            let body = g.app(m, "mkprog", 1)?[0].clone();
            let (c, b) = match g.app(&body, "or", 2) {
                Some(o) => (Some(o[0].clone()), o[1].clone()),
                None => (None, body),
            };
            let br = g.app(&b, "bind_rel", 5)?.to_vec();
            Some((c, br[0].clone(), br))
        };
        let (cl, procl, brl) = parts(self, &fl[1]).ok_or("the low function's program: not a procedure's call")?;
        let (ch, proch, brh) = parts(self, &fh[1]).ok_or("the high function's program: not a procedure's call")?;
        if cl.as_ref().map(|c| self.canon(c)) != ch.as_ref().map(|c| self.canon(c)) || (2..5).any(|i| self.canon(&brl[i]) != self.canon(&brh[i])) {
            return Err("the two functions' wrappers differ".into());
        }
        let (Node::App(sl, al), Node::App(sh, ah)) = (procl.node(), proch.node()) else { return Err("the procedures' calls".into()) };
        if al.len() != ah.len() || al.iter().zip(ah.iter()).any(|(x, y)| self.canon(x) != self.canon(y)) {
            return Err("the procedures' arguments differ".into());
        }
        let (nl, nh) = (self.env.syms[*sl as usize].name.clone(), self.env.syms[*sh as usize].name.clone());
        // the procedures' refinement, for every argument
        let pr = self.proc_ref(&nl, &nh, al.len())?;
        self.trace(|| format!("refines: {} refines {}", nl, nh));
        // the wrapper's, for an argument list a (x0 in the program), every
        // world and outcome
        let av = self.var("ra");
        let inst_a = |g: &Gen, t: &Term| t.instantiate_params(std::slice::from_ref(&av), &g.env.binders_fn());
        let (ml, mh) = (inst_a(self, &fl[1]), inst_a(self, &fh[1]));
        let (ca, pa, br) = parts(self, &ml).ok_or("the wrapper")?;
        let (_, pb, _) = parts(self, &mh).ok_or("the wrapper")?;
        let args: Vec<Term> = match pa.node() {
            Node::App(_, a) => a.to_vec(),
            _ => Vec::new(),
        };
        let prr = mp(R::S(pr), args.iter().map(t).collect());
        let k = self.lam(&br[2], &["x1", "x2", "y", "v"], &["y", "v", "x2"]).ok_or("the wrapper's continuation")?;
        let x = self.lam(&br[3], &["x1", "x2", "y", "e"], &["y", "e", "x2"]).ok_or("the wrapper's handler")?;
        let d = self.lam(&br[4], &["x1", "x2", "t"], &["t", "x2"]).ok_or("the wrapper's handler")?;
        let wrap = match &ca {
            Some(c) => {
                let c1 = self.lam(c, &["x1", "x2"], &["x1"]).ok_or("the wrapper's guard")?;
                R::Inst("g.wrap_ref1".into(), vec![("c", c1), ("p1", pa.clone()), ("p2", pb.clone()), ("k", k), ("x", x), ("d", d)])
            }
            None => R::Inst("g.wrap_ref0".into(), vec![("p1", pa.clone()), ("p2", pb.clone()), ("k", k), ("x", x), ("d", d)]),
        };
        let wr = self.run(&mp(wrap, vec![p(prr)]), &[])?;
        // (g.fun_ref's premise: all a s o. a in d -> runs(v1(a)) -> runs(v2(a)))
        let (sv, ov) = (self.var("rs"), self.var("ro"));
        let hdom = self.mk("in", vec![av.clone(), fl[0].clone()]);
        let hrun = self.mk("runs", vec![ml.clone(), sv.clone(), ov.clone()]);
        let hr = self.assume(&hrun)?;
        let r2 = self.run(&mp(R::S(wr), vec![t(&sv), t(&ov), s(&hr)]), &[])?;
        let prem = self.close(r2, &[hdom, hrun], &[Self::var_id(&av), Self::var_id(&sv), Self::var_id(&ov)])?;
        let fr = R::Inst("g.fun_ref".into(), vec![("d", fl[0].clone()), ("v1", fl[1].clone()), ("v2", fh[1].clone())]);
        let fun = self.run(&mp(fr, vec![s(&prem)]), &[])?;
        // the statement over the functions' names
        let fapp = |g: &Gen, n: &str| g.mk(n, gs.clone());
        let regs = self.var("regs");
        let w = self.var("w");
        let o = self.var("o");
        let concl = self.mk("runs", vec![self.mk("app", vec![fapp(self, high), regs.clone()]), w.clone(), o.clone()]);
        let prem_t = self.mk("runs", vec![self.mk("app", vec![fapp(self, low), regs.clone()]), w.clone(), o.clone()]);
        let lt = self.parse("list_type(bits(64))")?;
        let h1 = self.mk("in", vec![regs.clone(), lt]);
        let h2 = self.mk("int_le", vec![self.mk("seq_len", vec![regs.clone()]), lit(6)]);
        let h3 = self.mk("in", vec![w.clone(), self.mk("abi.World", vec![])]);
        let hp = self.assume(&prem_t)?;
        let hpl = self.run(&R::Expand(Box::new(R::S(hp)), vec![low.to_string()]), &[])?;
        let r1 = self.run(&mp(R::S(fun), vec![t(&regs), t(&w), t(&o), s(&hpl)]), &[])?;
        let r3 = self.evp(&RP::Defs(Box::new(RP::By(R::S(r1))), vec![high.to_string()]), &concl, &[])?;
        let mut vs: Vec<VarId> = gs.iter().map(Self::var_id).collect();
        vs.extend([Self::var_id(&regs), Self::var_id(&w), Self::var_id(&o)]);
        self.close(r3, &[h1, h2, h3, prem_t], &vs)
    }

    /// The procedures' refinement: `all ps s r. runs(PL(ps), s, r) ->
    /// runs(PH(ps), s, r)` by the walk
    fn proc_ref(&mut self, pl: &str, ph: &str, n: usize) -> Result<Seq, String> {
        let ps: Vec<Term> = (0..n).map(|i| self.var(&format!("pa{i}"))).collect();
        let w = self.var("pw");
        let o = self.var("po");
        self.w = w.clone();
        self.lf = Vec::new();
        let (dl, bl) = self.def_of(pl)?;
        let mut body = bl;
        for (i, x) in ps.iter().enumerate() {
            body = body.subst_var(dl[i], x, &self.env.binders_fn());
        }
        let mb = self.app(&body, "mkprog", 1).ok_or("the low procedure: not a program")?[0].clone();
        // the lower side: its body at w, o its outcome
        let lo = mb.instantiate_params(&[w.clone(), Term::bvar(0)], &self.env.binders_fn());
        let up = self.mk(ph, ps.clone());
        let qi = self.new_q(up.clone());
        let walk = self.walk(&lo, qi, &w)?;
        let low_app = self.mk(pl, ps.clone());
        let hr_t = self.mk("runs", vec![low_app.clone(), w.clone(), o.clone()]);
        let hr = self.assume(&hr_t)?;
        let hb = self.run(&R::Expand(Box::new(R::S(hr.clone())), vec![pl.to_string()]), &[])?;
        let e = self.run(&R::Apply(Box::new(f("g.runs_elim")), vec![s(&hb)]), &[])?;
        let u = self.run(&R::Apply(Box::new(f("g.runs_univ")), vec![s(&hb)]), &[])?;
        let wr = self.run(&R::Expand(Box::new(R::S(walk)), vec!["g.ref".into()]), &[])?;
        let r = self.run(&mp(R::S(wr), vec![t(&o), s(&e), s(&u)]), &[])?;
        let mut vs: Vec<VarId> = ps.iter().map(Self::var_id).collect();
        vs.extend([Self::var_id(&w), Self::var_id(&o)]);
        self.close(r, &[hr_t], &vs)
    }

    /// a closed condition decided by evaluation (no variables in it)
    fn decide(&mut self, c: &Term) -> Option<(bool, Seq)> {
        let mut vs = Vec::new();
        self.expand(c).vars(&mut vs);
        if !vs.is_empty() || c.loose_depth(&self.env.binders_fn()) > 0 {
            return None;
        }
        if let Ok(pf) = self.evp(&RP::Simp(false, vec![], vec![], false), c, &[]) {
            return Some((true, pf));
        }
        let n = self.mk("not", vec![c.clone()]);
        self.evp(&RP::Simp(false, vec![], vec![], false), &n, &[]).ok().map(|pf| (false, pf))
    }

    /// a lower step by a lemma `all o. lo(o) -> lo2(o)` (its instance): lo2
    fn low_by(&mut self, r: R) -> Result<(Term, Seq), String> {
        let sq = self.run(&r, &[])?;
        let st = sq.concl().clone();
        let body = self.app(&st, "all", 1).ok_or("a lower step: not all o")?[0].clone();
        let (_, rhs) = self.imps(&body);
        Ok((rhs, sq))
    }

    /// the walk on after a lower step `lo -> lo2` (its proof imp)
    fn after_low(&mut self, lo: &Term, lo2: Term, imp: Seq, qi: usize, w: &Term) -> Result<Seq, String> {
        let rest = self.walk(&lo2, qi, w)?;
        let r = mp(R::Inst("g.ref_low".into(), vec![("l", lo.clone()), ("l2", lo2), ("q", self.qs[qi].clone())]), vec![t(w), s(&imp), s(&rest)]);
        self.run(&r, &[])
    }

    /// `all r. runs(op, s, r) -> pair(s, r) in univ(1)`: op a procedure
    fn op_univ(&mut self, op: &Term, s0: &Term) -> Result<Seq, String> {
        let Node::App(f0, _) = op.node() else { return Err("an operation not a procedure's call".into()) };
        let name = self.env.syms[*f0 as usize].name.clone();
        let r = self.var("rr");
        let h = self.mk("runs", vec![op.clone(), s0.clone(), r.clone()]);
        let hs = self.assume(&h)?;
        let he = self.run(&R::Expand(Box::new(R::S(hs)), vec![name]), &[])?;
        let u = self.run(&R::Apply(Box::new(f("g.runs_univ")), vec![s(&he)]), &[])?;
        self.close(u, &[h], &[Self::var_id(&r)])
    }

    /// a rule's premise `all xs. g.ref(o. L, Q, S)` at fresh variables: L,
    /// Q, S, the variables
    fn ref_goal(&mut self, prem: &Term, names: &[&str]) -> Result<(Term, Term, Term, Vec<VarId>), String> {
        let mut cur = prem.clone();
        let mut vs = Vec::new();
        for nm in names {
            let b = self.app(&cur, "all", 1).ok_or("a rule's premise: not all")?[0].clone();
            let n = self.fresh(nm);
            let v = self.var(&n);
            cur = b.instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
            vs.push(Self::var_id(&v));
        }
        let x = self.app(&cur, "g.ref", 3).ok_or("a rule's premise: not g.ref")?.to_vec();
        Ok((x[0].clone(), x[1].clone(), x[2].clone(), vs))
    }

    /// prove a rule's walk premise: `all xs. g.ref(..)` (`hyp`: under an
    /// assumption, discharged)
    fn sub_walk(&mut self, prem: &Term, names: &[&str]) -> Result<Seq, String> {
        let (l, q, s0, vs) = self.ref_goal(prem, names)?;
        let qj = self.new_q(q);
        let saved = self.w.clone();
        let r = self.walk(&l, qj, &s0);
        self.w = saved;
        self.close(r?, &[], &vs)
    }

    /// The walk: `g.ref(o. lo, qs[qi], w)`
    fn walk(&mut self, lo: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
        self.w = w.clone();
        self.trace(|| format!("ref: low {} / high q{} {}", self.lambda(1, lo), qi, Printer::new(self.env).short(&self.qs[qi])));
        // (the lower side's projections of constructed tuples, at once)
        let lo2 = self.proj_simp(lo, &mut std::collections::HashMap::new());
        if lo2 != *lo {
            let rules = ["fst_pair", "snd_pair", "out_state_ok", "out_value_ok", "out_state_exc", "out_value_exc", "fst_ok", "fst_exc", "fst_diverge"];
            let goal = self.mk("all", vec![Term::app(self.env.builtins.imp, vec![lo.clone(), lo2.clone()])]);
            let imp = self.evp(&RP::Simp(false, rules.iter().map(|r| f(r)).collect(), vec![], false), &goal, &[])?;
            return self.after_low(lo, lo2, imp, qi, w);
        }
        let lctx = ["o", "x8"];
        let Some((a, k)) = block(self, lo) else {
            // (the result: the same on both)
            if let Some(x) = self.app(lo, "eq", 2).map(|x| x.to_vec()) {
                if matches!(x[0].node(), Node::BVar(0)) && x[1].loose_depth(&self.env.binders_fn()) == 0 {
                    return self.leaf_eq(&x[1], qi, w);
                }
            }
            // (into a block: the run's outcome named)
            let (lo2, imp) = self.low_by(R::Inst("g.low_intro".into(), vec![("l", lo.clone())]))?;
            return self.after_low(lo, lo2, imp, qi, w);
        };
        let kl = self.lam(&k, &lctx, &["x8", "o"]).ok_or("the lower block's rest")?;
        // lower one-sided steps
        if let Some(x) = self.app(&a, "letin", 2).map(|x| x.to_vec()) {
            let e = self.lam(&x[0], &lctx, &[]).ok_or("a let's value reads the block")?;
            let al = self.lam(&x[1], &["o", "x8", "x"], &["x", "x8"]).ok_or("a let")?;
            let (lo2, imp) = self.low_by(R::Inst("g.low_let".into(), vec![("e", e), ("a", al), ("k", kl)]))?;
            return self.after_low(lo, lo2, imp, qi, w);
        }
        if let Some(b) = self.app(&a, "ex", 1).map(|x| x[0].clone()) {
            if let Some(x) = self.app(&b, "and", 2).map(|x| x.to_vec()) {
                let a9 = self.lam(&x[0], &["o", "x8", "x9"], &["x9"]).ok_or("a nested block reads its outer one")?;
                let k9 = self.lam(&x[1], &["o", "x8", "x9"], &["x9", "x8"]).ok_or("a nested block's rest")?;
                let (lo2, imp) = self.low_by(R::Inst("g.low_assoc".into(), vec![("a", a9), ("k1", k9), ("k2", kl)]))?;
                return self.after_low(lo, lo2, imp, qi, w);
            }
        }
        if let Some(x) = self.app(&a, "eq", 2).map(|x| x.to_vec()) {
            if matches!(x[0].node(), Node::BVar(0)) {
                let e = self.lam(&x[1], &lctx, &[]).ok_or("a block's outcome reads its rest")?;
                let (lo2, imp) = self.low_by(R::Inst("g.low_eq".into(), vec![("e", e), ("k", kl)]))?;
                return self.after_low(lo, lo2, imp, qi, w);
            }
        }
        if let Some(x) = self.app(&a, "and", 2).map(|x| x.to_vec()) {
            if let Some(pc) = self.lam(&x[0], &lctx, &[]) {
                if let Some((true, pf)) = self.decide(&pc) {
                    let a2 = self.lam(&x[1], &lctx, &["x8"]).ok_or("a guarded block")?;
                    let (lo2, imp) = self.low_by(mp(R::Inst("g.low_and".into(), vec![("p", pc), ("a", a2), ("k", kl)]), vec![s(&pf)]))?;
                    return self.after_low(lo, lo2, imp, qi, w);
                }
            }
        }
        if let Some(x) = self.app(&a, "or", 2).map(|x| x.to_vec()) {
            // (a disjunct whose guard does not hold: dropped)
            for (side, lemma) in [(0usize, "g.low_orl"), (1, "g.low_orr")] {
                if let Some(g2) = self.app(&x[side], "and", 2).map(|y| y.to_vec()) {
                    if let Some(pc) = self.lam(&g2[0], &lctx, &[]) {
                        if let Some((false, pf)) = self.decide(&pc) {
                            let aa = self.lam(&g2[1], &lctx, &["x8"]).ok_or("a disjunct")?;
                            let rr = self.lam(&x[1 - side], &lctx, &["x8"]).ok_or("a disjunct")?;
                            let (lo2, imp) = self.low_by(mp(R::Inst(lemma.into(), vec![("p", pc), ("a", aa), ("r", rr), ("k", kl)]), vec![s(&pf)]))?;
                            return self.after_low(lo, lo2, imp, qi, w);
                        }
                    }
                }
            }
        }
        // the structured side: on to its head (its own reductions)
        if let Some(pf) = self.up_step(lo, qi, w)? {
            return Ok(pf);
        }
        // congruences: the same head on both
        let ub = self.app(&self.qs[qi], "mkprog", 1).ok_or("the structured side: not a program")?[0].clone();
        let (ua, uk) = block(self, &ub).ok_or_else(|| format!("the structured side not a block: {}", self.lambda(2, &ub)))?;
        let uctx = ["x0", "x1", "x8"];
        let ku = self.lam(&uk, &uctx, &["x8", "x1"]).ok_or("the structured block's rest reads the world")?;
        if let (Some(x), Some(y)) = (self.app(&a, "bind_rel", 5).map(|x| x.to_vec()), self.app(&ua, "bind_rel", 5).map(|x| x.to_vec())) {
            let opl = self.lam(&x[0], &lctx, &[]).ok_or("an operation reads the block")?;
            let opu = self.lam(&y[0], &uctx, &[]).ok_or("an operation reads the block")?;
            if self.canon(&opl) != self.canon(&opu) {
                return Err(format!("the operations differ: {} / {}", self.print(&opl), self.print(&opu)));
            }
            let ka = self.lam(&x[2], &["o", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's rest")?;
            let xa = self.lam(&x[3], &["o", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's handler")?;
            let da = self.lam(&x[4], &["o", "x8", "x9"], &["x9", "x8"]).ok_or("an operation's handler")?;
            let kb = self.lam(&y[2], &["x0", "x1", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's rest reads the world")?;
            let xb = self.lam(&y[3], &["x0", "x1", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's handler reads the world")?;
            let db = self.lam(&y[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("an operation's handler reads the world")?;
            let (rr, stmt) = self.inst("g.ref_op", &[("op", opl.clone()), ("ka", ka), ("xa", xa), ("da", da), ("kl", kl), ("kb", kb), ("xb", xb), ("db", db), ("ku", ku)])?;
            let body = self.app(&stmt, "all", 1).ok_or("g.ref_op")?[0].clone().instantiate_params(std::slice::from_ref(w), &self.env.binders_fn());
            let (prems, _) = self.imps(&body);
            let u = self.op_univ(&opl, w)?;
            let p1 = self.sub_walk(&prems[1], &["rs", "rv"])?;
            let p2 = self.sub_walk(&prems[2], &["rs", "re"])?;
            let p3 = self.sub_walk(&prems[3], &["rt"])?;
            return self.run(&mp(rr, vec![t(w), s(&u), s(&p1), s(&p2), s(&p3)]), &[]);
        }
        if let (Some(x), Some(y)) = (self.app(&a, "any_rel", 2).map(|x| x.to_vec()), self.app(&ua, "any_rel", 2).map(|x| x.to_vec())) {
            let d = self.lam(&x[0], &["o", "x8", "x"], &["x"]).ok_or("a choice's domain")?;
            let du = self.lam(&y[0], &["x0", "x1", "x8", "x"], &["x"]).ok_or("a choice's domain")?;
            if self.canon(&d) != self.canon(&du) {
                return Err("the choices' domains differ".into());
            }
            let al = self.lam(&x[1], &["o", "x8", "x"], &["x", "x8"]).ok_or("a choice")?;
            let bl = self.lam(&y[1], &["x0", "x1", "x8", "x"], &["x0", "x", "x8"]).ok_or("a choice")?;
            let (rr, stmt) = self.inst("g.ref_any", &[("d", d.clone()), ("a", al), ("kl", kl), ("b", bl), ("ku", ku)])?;
            let body = self.app(&stmt, "all", 1).ok_or("g.ref_any")?[0].clone().instantiate_params(std::slice::from_ref(w), &self.env.binders_fn());
            let (prems, _) = self.imps(&body);
            // (the domain a word's: not empty)
            let n = self.app(&d, "in", 2).and_then(|m| self.app(&m[1], "bits", 1).map(|b| b[0].clone())).ok_or("a choice not of a word")?;
            let ne = self.run(&mp(f("g.bits_ne"), vec![t(&n), simp0()]), &[])?;
            // all c. d(c) -> g.ref(..)
            let b0 = self.app(&prems[1], "all", 1).ok_or("g.ref_any's premise")?[0].clone();
            let cn = self.fresh("rc");
            let cv = self.var(&cn);
            let b1 = b0.instantiate_params(std::slice::from_ref(&cv), &self.env.binders_fn());
            let (hs, g0) = self.imps(&b1);
            let hd = self.assume(&hs[0])?;
            let _ = hd;
            let x2 = self.app(&g0, "g.ref", 3).ok_or("g.ref_any's premise")?.to_vec();
            let qj = self.new_q(x2[1].clone());
            let saved = self.w.clone();
            let r = self.walk(&x2[0], qj, &x2[2]);
            self.w = saved;
            let p1 = self.close(r?, &[hs[0].clone()], &[Self::var_id(&cv)])?;
            return self.run(&mp(rr, vec![t(w), s(&ne), s(&p1)]), &[]);
        }
        if let (Some(x), Some(y)) = (self.app(&a, "or", 2).map(|x| x.to_vec()), self.app(&ua, "or", 2).map(|x| x.to_vec())) {
            let parts = |g: &Gen, o: &[Term]| -> Option<(Term, Term, Term, Term)> {
                let l = g.app(&o[0], "and", 2)?;
                let r = g.app(&o[1], "and", 2)?;
                Some((l[0].clone(), l[1].clone(), r[0].clone(), r[1].clone()))
            };
            if let (Some((c, a1, nc, a2)), Some((cu, b1, ncu, b2))) = (parts(self, &x), parts(self, &y)) {
                let cl = self.lam(&c, &lctx, &[]).ok_or("a condition reads the block")?;
                let cu2 = self.lam(&cu, &uctx, &[]).ok_or("a condition reads the world")?;
                let ncl = self.lam(&nc, &lctx, &[]).ok_or("a condition")?;
                let ncu2 = self.lam(&ncu, &uctx, &[]).ok_or("a condition")?;
                if self.canon(&cl) == self.canon(&cu2) && self.canon(&ncl) == self.canon(&ncu2) && self.canon(&ncl) == self.canon(&self.mk("not", vec![cl.clone()])) {
                    let a1l = self.lam(&a1, &lctx, &["x8"]).ok_or("a way")?;
                    let a2l = self.lam(&a2, &lctx, &["x8"]).ok_or("a way")?;
                    let b1l = self.lam(&b1, &uctx, &["x0", "x8"]).ok_or("a way")?;
                    let b2l = self.lam(&b2, &uctx, &["x0", "x8"]).ok_or("a way")?;
                    let (rr, stmt) = self.inst("g.ref_if", &[("c", cl.clone()), ("a1", a1l), ("a2", a2l), ("kl", kl), ("b1", b1l), ("b2", b2l), ("ku", ku)])?;
                    let body = self.app(&stmt, "all", 1).ok_or("g.ref_if")?[0].clone().instantiate_params(std::slice::from_ref(w), &self.env.binders_fn());
                    let (prems, _) = self.imps(&body);
                    let mut pfs = Vec::new();
                    for pr in prems.iter().take(2) {
                        let (hs, g0) = self.imps(pr);
                        let _h = self.assume(&hs[0])?;
                        let x2 = self.app(&g0, "g.ref", 3).ok_or("g.ref_if's premise")?.to_vec();
                        let qj = self.new_q(x2[1].clone());
                        let saved = self.w.clone();
                        let r = self.walk(&x2[0], qj, &x2[2]);
                        self.w = saved;
                        pfs.push(self.close(r?, &[hs[0].clone()], &[])?);
                    }
                    return self.run(&mp(rr, vec![t(w), s(&pfs[0]), s(&pfs[1])]), &[]);
                }
            }
        }
        if self.app(&a, "while_rel", 5).is_some() {
            return Err(format!("the CFG's loop: not yet ({})", self.lambda(1, lo)));
        }
        Err(format!("no step: low {} / high {}", self.lambda(1, lo), self.lambda(2, &ub)))
    }

    /// the structured side's own reduction (its head neither an operation,
    /// a choice nor an undecided condition): the walk on, g.ref_up
    fn up_step(&mut self, lo: &Term, qi: usize, w: &Term) -> Result<Option<Seq>, String> {
        // (a procedure's name: its definition, by the reducer)
        let ub = self.app(&self.qs[qi], "mkprog", 1).map(|x| x[0].clone()).unwrap_or_else(|| Term::bvar(0));
        if let Some((ua, _)) = block(self, &ub) {
            if self.app(&ua, "any_rel", 2).is_some() {
                return Ok(None);
            }
            if let Some(x) = self.app(&ua, "bind_rel", 5) {
                if matches!(x[1].node(), Node::BVar(2)) {
                    return Ok(None);
                }
            }
        }
        // (the result: at the leaf)
        if let Some(x) = self.app(&ub, "eq", 2) {
            if matches!(x[0].node(), Node::BVar(0)) {
                return Ok(None);
            }
        }
        match self.reduce(qi, &[])? {
            Some(Red::Q(j, r)) => {
                let rest = self.walk(lo, j, w)?;
                let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
                self.run(&rr, &[]).map(Some)
            }
            None => Ok(None),
            Some(_) => Err(format!("the structured side: a step other than a reduction at {}", self.lambda(2, &ub))),
        }
    }

    /// the result o = e: the structured side's the same
    fn leaf_eq(&mut self, e: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
        let lo = self.mk("eq", vec![Term::bvar(0), e.clone()]);
        let ub = self.app(&self.qs[qi], "mkprog", 1).ok_or("the structured side: not a program")?[0].clone();
        if let Some(x) = self.app(&ub, "eq", 2) {
            if matches!(x[0].node(), Node::BVar(0)) {
                // (its world the start's: x0 the world here)
                if x[1].loose_depth(&self.env.binders_fn()) > 0 {
                    let b = self.lam(&ub, &["x0", "x1"], &["x0", "x1"]).ok_or("the result")?;
                    let (j, inst) = self.by(qi, "tr.q_at", &[("b", b), ("w", w.clone())])?;
                    let rest = self.leaf_eq(e, j, w)?;
                    let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(mp(inst, vec![t(w)]))]);
                    return self.run(&rr, &[]);
                }
                if self.canon(&x[1]) != self.canon(e) {
                    return Err(format!("the results differ: {} / {}", self.print(e), self.print(&x[1])));
                }
                return self.run(&mp(R::Inst("g.ref_eq".into(), vec![("e", e.clone())]), vec![t(w)]), &[]);
            }
        }
        match self.reduce(qi, &[])? {
            Some(Red::Q(j, r)) => {
                let rest = self.leaf_eq(e, j, w)?;
                let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
                self.run(&rr, &[])
            }
            _ => Err(format!("the result {}: the structured side at {}", self.print(e), self.lambda(2, &ub))),
        }
    }
}
