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

mod gloop;

pub fn refines(env: &mut Env, name: &str, low: &str, high: &str) -> Result<Seq, String> {
    let empty = Term::app(env.sym_by_name["empty"], vec![]);
    let t0 = std::time::Instant::now();
    let _rep = super::prof::Rep(name.to_string());
    let mut g = Gen::new(env, BTreeMap::new(), empty.clone(), empty, name, name, Vec::new())?;
    // (the same statements on both sides: their values as written)
    g.raw_lets = true;
    let r = g.refines(low, high);
    drop(g);
    // (its terms not kept alive by the environment's caches)
    env.clear_term_caches();
    // (C1_STATS=1: each refinement's time and the resident memory after it)
    if std::env::var("C1_STATS").is_ok_and(|v| v == "1") {
        let rss = std::fs::read_to_string("/proc/self/statm").ok().and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok()).map_or(0, |p| p * 4096 / (1 << 20));
        eprintln!("refines {}: {:.1} s, {} MB resident{}", name, t0.elapsed().as_secs_f64(), rss, if r.is_err() { " (failed)" } else { "" });
    }
    r
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
        // (two procedures: their refinement for every argument)
        if self.app(&bl, "mkprog", 1).is_some() && self.app(&bh, "mkprog", 1).is_some() {
            return self.proc_ref(low, high, pl.len());
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

    /// a callee's refinement `all s r. runs(PL(as), s, r) -> runs(PH(as),
    /// s, r)`: the calls of the same arguments, the procedures walked
    /// (once each)
    fn callee_ref(&mut self, opl: &Term, opu: &Term) -> Result<R, String> {
        let (Node::App(sl, al), Node::App(sh, ah)) = (opl.node(), opu.node()) else { return Err("the operations differ".into()) };
        if al.len() != ah.len() || al.iter().zip(ah.iter()).any(|(x, y)| self.canon(x) != self.canon(y)) {
            return Err(format!("the operations differ: {} / {}", self.print(opl), self.print(opu)));
        }
        let (nl, nh) = (self.env.syms[*sl as usize].name.clone(), self.env.syms[*sh as usize].name.clone());
        let key = (nl.clone(), nh.clone());
        let pr = match self.grefs.get(&key) {
            Some(pr) => pr.clone(),
            None => {
                self.trace(|| format!("ref: callee {} refines {}", nl, nh));
                let (sg, sw, slf) = (self.gref.take(), self.w.clone(), std::mem::take(&mut self.lf));
                let pr = self.proc_ref(&nl, &nh, al.len());
                (self.gref, self.w, self.lf) = (sg, sw, slf);
                let pr = pr?;
                self.grefs.insert(key, pr.clone());
                pr
            }
        };
        Ok(mp(R::S(pr), al.iter().map(t).collect()))
    }

    /// a closed condition decided by evaluation (no variables in it once
    /// its projections are taken: the label's test on a point's state)
    fn decide(&mut self, c: &Term) -> Option<(bool, Seq)> {
        let mut vs = Vec::new();
        let cp = self.proj_simp(c, &mut std::collections::HashMap::new());
        self.expand(&cp).vars(&mut vs);
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
        // (its values by their names, as the structured side's)
        Ok((self.canon(&rhs), sq))
    }

    /// the walk on after a lower step `lo -> lo2` (its proof imp)
    fn after_low(&mut self, lo: &Term, lo2: Term, imp: Seq, qi: usize, w: &Term) -> Result<Seq, String> {
        let rest = self.walk(&lo2, qi, w)?;
        let r = mp(R::Inst("g.ref_low".into(), vec![("l", lo.clone()), ("l2", lo2), ("q", self.qs[qi].clone())]), vec![t(w), s(&imp), s(&rest)]);
        self.run(&r, &[])
    }

    /// a program at a join, `mkprog(x0 x1. ex x2. x2 = ok(pair(x0, T),
    /// empty) && K)`: T (closed)
    fn join_tuple(&self, q: &Term) -> Option<Term> {
        self.app(q, "mkprog", 1)
            .and_then(|m| block(self, &m[0]))
            .and_then(|(a, _)| self.app(&a, "eq", 2).map(|e| e.to_vec()))
            .filter(|e| matches!(e[0].node(), Node::BVar(0)))
            .and_then(|e| self.app(&e[1], "ok", 2).map(|o| o[0].clone()))
            .and_then(|p0| self.app(&p0, "pair", 2).map(|p| p[1].clone()))
            .filter(|t| t.loose_depth(&self.env.binders_fn()) == 0)
    }

    /// the join's program q with its tuple T (join_tuple) the closed term
    /// `tup` -- there alone
    fn set_join_tuple(&self, q: &Term, tup: &Term) -> Option<Term> {
        let m = self.app(q, "mkprog", 1)?[0].clone();
        let b = self.app(&m, "ex", 1)?[0].clone();
        let a = self.app(&b, "and", 2)?.to_vec();
        let e = self.app(&a[0], "eq", 2)?.to_vec();
        let o = self.app(&e[1], "ok", 2)?.to_vec();
        let p0 = self.app(&o[0], "pair", 2)?.to_vec();
        let p1 = o[0].with_args(vec![p0[0].clone(), tup.clone()]);
        let o1 = e[1].with_args(vec![p1, o[1].clone()]);
        let e1 = a[0].with_args(vec![e[0].clone(), o1]);
        let a1 = b.with_args(vec![e1, a[1].clone()]);
        let b1 = m.with_args(vec![a1]);
        Some(q.with_args(vec![b1]))
    }

    /// a program at a loop, `mkprog(x0 x1. ex x9. while_rel(pair(x0, T),
    /// c, b, tr, x9) && K)`: T (closed)
    fn loop_tuple(&self, q: &Term) -> Option<Term> {
        let m = self.app(q, "mkprog", 1)?[0].clone();
        let (a, _) = block(self, &m)?;
        let wr = self.app(&a, "while_rel", 5)?;
        if !matches!(wr[4].node(), Node::BVar(0)) {
            return None;
        }
        let st = self.app(&wr[0], "pair", 2)?;
        (matches!(st[0].node(), Node::BVar(2)) && st[1].loose_depth(&self.env.binders_fn()) == 0).then(|| st[1].clone())
    }

    /// the loop's program q with its tuple T (loop_tuple) the closed term
    /// `tup`
    fn set_loop_tuple(&self, q: &Term, tup: &Term) -> Option<Term> {
        let m = self.app(q, "mkprog", 1)?[0].clone();
        let b = self.app(&m, "ex", 1)?[0].clone();
        let a = self.app(&b, "and", 2)?.to_vec();
        let wr = self.app(&a[0], "while_rel", 5)?.to_vec();
        let st = self.app(&wr[0], "pair", 2)?.to_vec();
        let st1 = wr[0].with_args(vec![st[0].clone(), tup.clone()]);
        let mut wr1 = wr.clone();
        wr1[0] = st1;
        let a0 = a[0].with_args(wr1);
        let b1 = b.with_args(vec![a0, a[1].clone()]);
        let m1 = m.with_args(vec![b1]);
        Some(q.with_args(vec![m1]))
    }

    /// q a join's program whose rest first passes the locals on as its own
    /// outcome (`ex x3. ((fst(x2) = 0 && x3 = ok(..)) || ..) && K`: the
    /// end of an enclosing branch's way)
    fn passes_on(&self, q: &Term) -> bool {
        let q = self.expand(q);
        if self.join_tuple(&q).is_none() {
            return false;
        }
        let Some((_, k)) = self.app(&q, "mkprog", 1).and_then(|m| block(self, &m[0])) else { return false };
        let Some((a3, _)) = block(self, &k) else { return false };
        let mut d = a3;
        while let Some(o) = self.app(&d, "or", 2).map(|o| o[0].clone()) {
            d = o;
        }
        let Some(c) = self.app(&d, "and", 2).map(|c| c.to_vec()) else { return false };
        self.app(&c[0], "eq", 2).is_some_and(|e| self.app(&e[0], "fst", 1).is_some() && nat(&e[1]) == Some(0))
            && self.app(&c[1], "eq", 2).is_some_and(|e| matches!(e[0].node(), Node::BVar(0)) && self.app(&e[1], "ok", 2).is_some())
    }

    /// the locals' tuple of the terms cs (a right-nested pair)
    fn tuple_of(&self, cs: &[Term]) -> Term {
        let mut t = cs[cs.len() - 1].clone();
        for c in cs[..cs.len() - 1].iter().rev() {
            t = self.mk("pair", vec![c.clone(), t]);
        }
        t
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

    /// a closed projection of a constructed tuple or outcome in the CFG
    /// side taken, by its equation (each occurrence of it at once)
    fn proj_step(&mut self, lo: &Term) -> Result<Option<(Term, Seq)>, String> {
        let lo0 = lo.clone();
        self.proj_step_in(lo, &lo0)
    }

    /// ... one in the part `sub` of it (a value about to be substituted, the
    /// block's head: not the other blocks of the dispatch)
    fn proj_step_in(&mut self, lo: &Term, sub: &Term) -> Result<Option<(Term, Seq)>, String> {
        let Some((r, eq)) = self.closed_redex(sub) else { return Ok(None) };
        let ab = self.abstract_(lo, &r, 0);
        let l = self.lam(&ab, &["o", "x"], &["o", "x"]).ok_or("a projection's context")?;
        let eqc = self.run(&eq, &[])?.concl().clone();
        let v = self.app(&eqc, "eq", 2).ok_or("a projection's equation")?[1].clone();
        self.low_by(mp(R::Inst("g.low_rw".into(), vec![("l", l), ("a", r), ("b", v)]), vec![p(eq)])).map(Some)
    }

    /// One step of the CFG's side on its own: a block's let, nesting,
    /// named outcome, a guard decided (the dispatch on the label first: the
    /// other blocks gone before the projections are taken), a projection,
    /// the iteration's end; into a block -- the next lower side and its
    /// proof `all o. lo(o) -> lo2(o)`; None at a leaf or a congruence's
    /// head
    fn low_step(&mut self, lo: &Term) -> Result<Option<(Term, Seq)>, String> {
        // (the result written e = o)
        if let Some(x) = self.app(lo, "eq", 2).map(|x| x.to_vec()) {
            if matches!(x[1].node(), Node::BVar(0)) && !matches!(x[0].node(), Node::BVar(0)) {
                if let Some(e) = self.lam(&x[0], &["o"], &[]) {
                    return self.low_by(R::Inst("g.low_sym".into(), vec![("e", e)])).map(Some);
                }
            }
        }
        let lctx = ["o", "x8"];
        let Some((a, k)) = block(self, lo) else {
            if self.jump_of(lo).is_some() {
                return Ok(None);
            }
            if let Some(r) = self.proj_step(lo)? {
                return Ok(Some(r));
            }
            if self.leaf_of(lo).is_some() {
                return Ok(None);
            }
            // (the CFG's iteration ending: going on, or leaving)
            if let Some(r) = self.nx_step(lo)? {
                return Ok(Some(r));
            }
            // (a block leaving the segment: not at the cut's mark)
            if let Some(r) = self.low_orn(lo)? {
                return Ok(Some(r));
            }
            return self.low_by(R::Inst("g.low_intro".into(), vec![("l", lo.clone())])).map(Some);
        };
        // (the segment's run on from a state: g.seg_step / g.seg_cut)
        if let Some(r) = self.seg_step(&a, &k)? {
            return Ok(Some(r));
        }
        let kl = self.lam(&k, &lctx, &["x8", "o"]).ok_or("the lower block's rest")?;
        // (the rest's last step the outcome itself: without it)
        if let Some(b9) = self.app(&k, "ex", 1).map(|b| b[0].clone()) {
            if let Some(c) = self.app(&b9, "and", 2).map(|c| c.to_vec()) {
                let id = self.app(&c[1], "eq", 2).is_some_and(|e| matches!(e[0].node(), Node::BVar(0)) && matches!(e[1].node(), Node::BVar(2)));
                if id {
                    if let (Some(al), Some(k9)) = (self.lam(&a, &lctx, &["x8"]), self.lam(&c[0], &["o", "x8", "x9"], &["x8", "x9"])) {
                        return self.low_by(R::Inst("g.low_kid".into(), vec![("a", al), ("k", k9)])).map(Some);
                    }
                }
            }
        }
        if let Some(x) = self.app(&a, "letin", 2).map(|x| x.to_vec()) {
            let e = self.lam(&x[0], &lctx, &[]).ok_or("a let's value reads the block")?;
            // (its projections taken first)
            if let Some(r) = self.proj_step_in(lo, &e)? {
                return Ok(Some(r));
            }
            // (named, as the structured side's values; as written on both)
            let e = self.value(&e);
            let al = self.lam(&x[1], &["o", "x8", "x"], &["x", "x8"]).ok_or("a let")?;
            return self.low_by(R::Inst("g.low_let".into(), vec![("e", e), ("a", al), ("k", kl)])).map(Some);
        }
        if let Some(b) = self.app(&a, "ex", 1).map(|x| x[0].clone()) {
            if let Some(x) = self.app(&b, "and", 2).map(|x| x.to_vec()) {
                let a9 = self.lam(&x[0], &["o", "x8", "x9"], &["x9"]).ok_or("a nested block reads its outer one")?;
                let k9 = self.lam(&x[1], &["o", "x8", "x9"], &["x9", "x8"]).ok_or("a nested block's rest")?;
                return self.low_by(R::Inst("g.low_assoc".into(), vec![("a", a9), ("k1", k9), ("k2", kl)])).map(Some);
            }
        }
        if let Some(x) = self.app(&a, "eq", 2).map(|x| x.to_vec()) {
            // (the outcome's projections taken before it is substituted)
            if matches!(x[0].node(), Node::BVar(0)) {
                let e = self.lam(&x[1], &lctx, &[]).ok_or("a block's outcome reads its rest")?;
                if let Some(r) = self.proj_step_in(lo, &e)? {
                    return Ok(Some(r));
                }
                return self.low_by(R::Inst("g.low_eq".into(), vec![("e", e), ("k", kl)])).map(Some);
            }
            if matches!(x[1].node(), Node::BVar(0)) {
                let e = self.lam(&x[0], &lctx, &[]).ok_or("a block's outcome reads its rest")?;
                if let Some(r) = self.proj_step_in(lo, &e)? {
                    return Ok(Some(r));
                }
                return self.low_by(R::Inst("g.low_eqr".into(), vec![("e", e), ("k", kl)])).map(Some);
            }
        }
        if let Some(x) = self.app(&a, "and", 2).map(|x| x.to_vec()) {
            if let Some(pc) = self.lam(&x[0], &lctx, &[]) {
                if let Some((true, pf)) = self.decide(&pc) {
                    let a2 = self.lam(&x[1], &lctx, &["x8"]).ok_or("a guarded block")?;
                    return self.low_by(mp(R::Inst("g.low_and".into(), vec![("p", pc), ("a", a2), ("k", kl)]), vec![s(&pf)])).map(Some);
                }
            }
        }
        if let Some(x) = self.app(&a, "or", 2).map(|x| x.to_vec()) {
            for (side, lemma) in [(0usize, "g.low_orl"), (1, "g.low_orr")] {
                if let Some(g2) = self.app(&x[side], "and", 2).map(|y| y.to_vec()) {
                    if let Some(pc) = self.lam(&g2[0], &lctx, &[]) {
                        if let Some((false, pf)) = self.decide(&pc) {
                            let aa = self.lam(&g2[1], &lctx, &["x8"]).ok_or("a disjunct")?;
                            let rr = self.lam(&x[1 - side], &lctx, &["x8"]).ok_or("a disjunct")?;
                            return self.low_by(mp(R::Inst(lemma.into(), vec![("p", pc), ("a", aa), ("r", rr), ("k", kl)]), vec![s(&pf)])).map(Some);
                        }
                    }
                }
            }
            // (the right side refuted as a whole: each disjunct's leading
            // guard false)
            if let (Some(aa), Some(rr)) = (self.lam(&x[0], &lctx, &["x8"]), self.lam(&x[1], &lctx, &["x8"])) {
                let n = self.fresh("x8");
                let v = self.var(&n);
                let r1 = x[1].instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
                if let Some(pf) = self.refute(&r1)? {
                    let all = self.close(pf, &[], &[Self::var_id(&v)])?;
                    return self.low_by(mp(R::Inst("g.low_orl2".into(), vec![("a", aa), ("r", rr), ("k", kl)]), vec![s(&all)])).map(Some);
                }
                let a1 = x[0].instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
                if let Some(pf) = self.refute(&a1)? {
                    let all = self.close(pf, &[], &[Self::var_id(&v)])?;
                    return self.low_by(mp(R::Inst("g.low_orr2".into(), vec![("a", aa), ("r", rr), ("k", kl)]), vec![s(&all)])).map(Some);
                }
            }
        }
        // (the head's projections: before a congruence)
        self.proj_step_in(lo, &a)
    }

    /// `!t`: t a tree of disjunctions whose leaves are conjunctions led by
    /// a closed condition decided false
    fn refute(&mut self, t: &Term) -> Result<Option<Seq>, String> {
        if let Some(x) = self.app(t, "or", 2).map(|x| x.to_vec()) {
            let (Some(a), Some(b)) = (self.refute(&x[0])?, self.refute(&x[1])?) else { return Ok(None) };
            return self.run(&mp(R::Inst("g.nor".into(), vec![("a", x[0].clone()), ("b", x[1].clone())]), vec![s(&a), s(&b)]), &[]).map(Some);
        }
        if let Some(x) = self.app(t, "and", 2).map(|x| x.to_vec()) {
            let pf = match self.decide(&x[0]) {
                Some((false, pf)) => pf,
                Some((true, _)) => return Ok(None),
                None => match self.refute(&x[0])? {
                    Some(pf) => pf,
                    None => return Ok(None),
                },
            };
            return self.run(&mp(R::Inst("g.nand".into(), vec![("p", x[0].clone()), ("a", x[1].clone())]), vec![s(&pf)]), &[]).map(Some);
        }
        Ok(match self.decide(t) {
            Some((false, pf)) => Some(pf),
            _ => None,
        })
    }

    /// an innermost closed projection of a constructed tuple or outcome
    /// in t: it, its equation
    fn closed_redex(&mut self, t: &Term) -> Option<(Term, R)> {
        if let Node::App(_, a) = t.node() {
            for x in a.iter() {
                if let Some(r) = self.closed_redex(x) {
                    return Some(r);
                }
            }
        }
        if self.env.loose_depth_m(t) > 0 {
            return None;
        }
        // (a constant defined as a literal: a layer's global, each layer's
        // its own name)
        if let Node::App(f0, a) = t.node() {
            if a.is_empty() {
                if let SymKind::Defined { params, body } = &self.env.syms[*f0 as usize].kind {
                    if params.is_empty() && nat(body).is_some() {
                        let (name, body) = (self.env.syms[*f0 as usize].name.clone(), body.clone());
                        let eq = self.mk("eq", vec![t.clone(), body]);
                        let pf = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![], vec![], false)), vec![name]), &eq, &[]).ok()?;
                        return Some((t.clone(), R::S(pf)));
                    }
                }
            }
        }
        let one = |f: &str| self.app(t, f, 1).map(|x| x[0].clone());
        if let Some(x) = one("fst") {
            if let Some(p2) = self.app(&x, "pair", 2) {
                return Some((t.clone(), R::Inst("fst_pair".into(), vec![("a", p2[0].clone()), ("b", p2[1].clone())])));
            }
            if let Some(o) = self.app(&x, "ok", 2) {
                return Some((t.clone(), R::Inst("fst_ok".into(), vec![("s", o[0].clone()), ("v", o[1].clone())])));
            }
            if let Some(o) = self.app(&x, "exc", 2) {
                return Some((t.clone(), R::Inst("fst_exc".into(), vec![("s", o[0].clone()), ("e", o[1].clone())])));
            }
            if let Some(o) = self.app(&x, "diverge", 1) {
                return Some((t.clone(), R::Inst("fst_diverge".into(), vec![("t", o[0].clone())])));
            }
        }
        if let Some(x) = one("snd") {
            if let Some(p2) = self.app(&x, "pair", 2) {
                return Some((t.clone(), R::Inst("snd_pair".into(), vec![("a", p2[0].clone()), ("b", p2[1].clone())])));
            }
            if let Some(o) = self.app(&x, "diverge", 1) {
                return Some((t.clone(), R::Inst("g.snd_diverge".into(), vec![("t", o[0].clone())])));
            }
        }
        for (f0, lk, le) in [("out_state", "out_state_ok", "out_state_exc"), ("out_value", "out_value_ok", "out_value_exc")] {
            if let Some(x) = one(f0) {
                if let Some(o) = self.app(&x, "ok", 2) {
                    return Some((t.clone(), R::Inst(lk.into(), vec![("s", o[0].clone()), ("v", o[1].clone())])));
                }
                if let Some(o) = self.app(&x, "exc", 2) {
                    return Some((t.clone(), R::Inst(le.into(), vec![("s", o[0].clone()), ("e", o[1].clone())])));
                }
            }
        }
        None
    }

    /// the result o = e: e
    fn leaf_of(&self, lo: &Term) -> Option<Term> {
        let x = self.app(lo, "eq", 2)?;
        (matches!(x[0].node(), Node::BVar(0)) && x[1].loose_depth(&self.env.binders_fn()) == 0).then(|| x[1].clone())
    }

    /// the CFG going on at x (`all q2. inv(x, q2) -> .. -> runs(q2, fst(x), o)`): x
    fn jump_of(&self, lo: &Term) -> Option<Term> {
        let b = self.app(lo, "all", 1)?[0].clone();
        let (hs, c) = self.imps(&b);
        if hs.len() != 2 {
            return None;
        }
        let r = self.app(&c, "runs", 3)?;
        let x = self.app(&r[1], "fst", 1)?[0].clone();
        (x.loose_depth(&self.env.binders_fn()) == 0).then_some(x)
    }

    /// the iteration's end `(ex l2. e = ok(l2) && J(l2, o)) || (!is_ok(e)
    /// && k(e, o))`: on at J(x, o) (e = ok(x)), or the rest k(e, o)
    fn nx_step(&mut self, lo: &Term) -> Result<Option<(Term, Seq)>, String> {
        let Some(x) = self.app(lo, "or", 2).map(|x| x.to_vec()) else { return Ok(None) };
        let Some(b) = self.app(&x[0], "ex", 1).map(|b| b[0].clone()) else { return Ok(None) };
        let Some(c) = self.app(&b, "and", 2).map(|c| c.to_vec()) else { return Ok(None) };
        let Some(eq) = self.app(&c[0], "eq", 2).map(|e| e.to_vec()) else { return Ok(None) };
        let Some(okl) = self.app(&eq[1], "ok", 2).map(|o| o.to_vec()) else { return Ok(None) };
        if !matches!(okl[0].node(), Node::BVar(0)) {
            return Ok(None);
        }
        if self.gref.is_none() {
            return Ok(None);
        }
        // (the leaving side as it stands: its projections already taken)
        let Some(lv) = self.app(&x[1], "and", 2).map(|c| c[1].clone()) else { return Ok(None) };
        let kk = self.lam(&lv, &["o"], &["o"]).ok_or("the iteration's leaving")?;
        let e = self.lam(&eq[0], &["o", "l2"], &[]).ok_or("the iteration's outcome")?;
        let j = self.lam(&c[1], &["o", "l2"], &["l2", "o"]).ok_or("the iteration's going on")?;
        if let Some(o2) = self.app(&e, "ok", 2) {
            if self.app(&o2[1], "empty", 0).is_some() {
                let x0 = o2[0].clone();
                return self.low_by(R::Inst("g.low_nx".into(), vec![("e", x0), ("j", j), ("k", kk)])).map(Some);
            }
        }
        let nk = if let Some(x) = self.app(&e, "exc", 2) {
            mp(f("g.not_ok_exc"), vec![t(&x[0]), t(&x[1])])
        } else if let Some(x) = self.app(&e, "diverge", 1) {
            mp(f("g.not_ok_div"), vec![t(&x[0])])
        } else {
            return Err(format!("the iteration's outcome {}", self.print(&e)));
        };
        self.low_by(mp(R::Inst("g.low_nx2".into(), vec![("e", e), ("j", j), ("k", kk)]), vec![p(nk)])).map(Some)
    }

    /// The walk: `g.ref(o. lo, qs[qi], w)`
    fn walk(&mut self, lo: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
        self.w = w.clone();
        self.trace(|| format!("ref: low {} / high q{} {}", self.lambda(1, lo), qi, Printer::new(self.env).short(&self.qs[qi])));
        // (the world: its projections taken, one at a time)
        if let Some((r, eq)) = self.closed_redex(w) {
            let ab = self.abstract_(w, &r, 0);
            let c = self.lam(&ab, &["x"], &["x"]).ok_or("the world's context")?;
            let eqc = self.run(&eq, &[])?.concl().clone();
            let v = self.app(&eqc, "eq", 2).ok_or("a projection's equation")?[1].clone();
            let w2 = ab.instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
            let rest = self.walk(lo, qi, &w2)?;
            let rr = mp(R::Inst("g.ref_wrw".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("c", c), ("a", r), ("b", v)]), vec![p(eq), s(&rest)]);
            return self.run(&rr, &[]);
        }
        // (the structured side reading the world here: from its start)
        if let Some(ub) = self.app(&self.qs[qi], "mkprog", 1).map(|x| x[0].clone()) {
            let leaf = self.app(&ub, "eq", 2).is_some_and(|x| matches!(x[0].node(), Node::BVar(0)));
            if !leaf && self.mentions(&ub, w) {
                let bb = self.abstract_(&ub, w, 0);
                let (_, stmt) = self.inst("g.q_gen", &[("b", bb.clone())])?;
                let (hs, _) = self.imps(&self.app(&self.app(&stmt, "all", 1).unwrap()[0], "all", 1).unwrap()[0].clone());
                let q2 = self.app(&hs[0], "runs", 3).ok_or("g.q_gen")?[0].clone();
                let j = self.new_q(q2);
                let rest = self.walk(lo, j, w)?;
                let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(mp(R::Inst("g.q_gen".into(), vec![("b", bb)]), vec![t(w)]))]);
                return self.run(&rr, &[]);
            }
        }
        // (a jump, as the rule states it; a result: its projections taken
        // first)
        if let Some(x) = self.jump_of(lo) {
            return self.leaf_jump(lo, &x, qi, w);
        }
        if block(self, lo).is_none() {
            if let Some((lo2, imp)) = self.proj_step(lo)? {
                return self.after_low(lo, lo2, imp, qi, w);
            }
        }
        if let Some(e) = self.leaf_of(lo) {
            return self.leaf_eq(&e, qi, w);
        }
        if let Some((lo2, imp)) = self.low_step(lo)? {
            return self.after_low(lo, lo2, imp, qi, w);
        }
        let (a, k) = block(self, lo).ok_or_else(|| format!("the CFG side: no step at {}", self.lambda(1, lo)))?;
        if self.app(&a, "while_rel", 5).is_some() {
            return self.cfg_loop(lo, &a, &k, qi, w);
        }
        let lctx = ["o", "x8"];
        let kl = self.lam(&k, &lctx, &["x8", "o"]).ok_or("the lower block's rest")?;
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
            let ka = self.lam(&x[2], &["o", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's rest")?;
            let xa = self.lam(&x[3], &["o", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's handler")?;
            let da = self.lam(&x[4], &["o", "x8", "x9"], &["x9", "x8"]).ok_or("an operation's handler")?;
            if self.canon(&opl) != self.canon(&opu) {
                // (the CFG layer's callee: the structured layer's, by its
                // refinement)
                let pr = self.callee_ref(&opl, &opu)?;
                let st = self.lam(&x[1], &lctx, &[]).ok_or("an operation's world reads the block")?;
                let r = R::Inst("g.low_op".into(), vec![("p1", opl), ("p2", opu), ("s", st.clone()), ("ka", ka), ("xa", xa), ("da", da), ("kl", kl.clone())]);
                let (lo2, imp) = self.low_by(mp(r, vec![p(mp(pr, vec![t(&st)]))]))?;
                return self.after_low(lo, lo2, imp, qi, w);
            }
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
            let n = self.app(&d, "in", 2).and_then(|m| self.app(&m[1], "bits", 1).map(|b| b[0].clone())).ok_or("a choice not of a word")?;
            let ne = self.run(&mp(f("g.bits_ne"), vec![t(&n), simp0()]), &[])?;
            let b0 = self.app(&prems[1], "all", 1).ok_or("g.ref_any's premise")?[0].clone();
            let cn = self.fresh("rc");
            let cv = self.var(&cn);
            let b1 = b0.instantiate_params(std::slice::from_ref(&cv), &self.env.binders_fn());
            let (hs, g0) = self.imps(&b1);
            let _hd = self.assume(&hs[0])?;
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
                let (c0, n0, nn0) = (self.canon(&cl), self.canon(&self.mk("not", vec![cl.clone()])), self.canon(&self.mk("not", vec![self.mk("not", vec![cl.clone()])])));
                let (cu0, ncu0) = (self.canon(&cu2), self.canon(&ncu2));
                // (the structured side's ways in the same order, or the
                // other way round -- its first under the negation)
                let way = if self.canon(&ncl) != n0 {
                    None
                } else if cu0 == c0 && ncu0 == n0 {
                    Some(("g.ref_if", b1, b2))
                } else if cu0 == n0 && ncu0 == nn0 {
                    Some(("g.ref_ifn", b2, b1))
                } else {
                    None
                };
                if way.is_none() {
                    self.trace(|| format!("ref: if differs: low {} / high {}", self.print(&self.expand(&cl)), self.print(&self.expand(&cu2))));
                }
                if let Some((lemma, b1, b2)) = way {
                    let a1l = self.lam(&a1, &lctx, &["x8"]).ok_or("a way")?;
                    let a2l = self.lam(&a2, &lctx, &["x8"]).ok_or("a way")?;
                    let b1l = self.lam(&b1, &uctx, &["x0", "x8"]).ok_or("a way")?;
                    let b2l = self.lam(&b2, &uctx, &["x0", "x8"]).ok_or("a way")?;
                    let (rr, stmt) = self.inst(lemma, &[("c", cl.clone()), ("a1", a1l), ("a2", a2l), ("kl", kl), ("b1", b1l), ("b2", b2l), ("ku", ku)])?;
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
        Err(format!("no step: low {} / high {}", self.lambda(1, lo), self.lambda(2, &ub)))
    }

    /// The CFG going on at x, the structured side at qi: x's cut point (made
    /// when first reached), `inv(x, q)` by its hypothesis, g.ref_jump
    fn leaf_jump(&mut self, lo: &Term, x: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
        // (to a loop head: the structured side on to its loop)
        let kx = self.app(x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).and_then(|q| nat(&q[0])));
        if kx.is_some_and(|k| self.gref.as_ref().is_some_and(|g| g.loop_heads.contains(&k))) && self.loop_tuple(&self.expand(&self.qs[qi])).is_none() {
            let red = match self.up_proj(qi, w)? {
                Some((j, r)) => Some(Red::Q(j, r)),
                None => self.reduce(qi, &[])?,
            };
            let Some(Red::Q(j, r)) = red else {
                let ub = self.app(&self.qs[qi], "mkprog", 1).map_or_else(|| self.qs[qi].clone(), |m| m[0].clone());
                return Err(format!("at a loop head: the structured side not at a loop: {}", self.lambda(2, &ub)));
            };
            let rest = self.leaf_jump(lo, x, j, w)?;
            let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
            return self.run(&rr, &[]);
        }
        // (the structured side's lets before it: run, as the CFG's block ran
        // them into its locals -- its point's template then on the same
        // values)
        let ub = self.app(&self.qs[qi], "mkprog", 1).map(|x| x[0].clone());
        if let Some((ua, _)) = ub.as_ref().and_then(|b| block(self, b)) {
            if self.app(&ua, "letin", 2).is_some() {
                if let Some(Red::Q(j, r)) = self.reduce(qi, &[])? {
                    let rest = self.leaf_jump(lo, x, j, w)?;
                    let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
                    return self.run(&rr, &[]);
                }
            }
        }
        // (at an inner join whose rest passes the locals on to the
        // enclosing one's: on to that one -- a join's cut point the same
        // however deep the way to it came)
        if self.passes_on(&self.qs[qi]) {
            let mut steps: Vec<(usize, usize, R)> = Vec::new();
            let mut cur = qi;
            let mut done = None;
            for _ in 0..256 {
                let red = match self.up_proj(cur, w)? {
                    Some((j, r)) => Some(Red::Q(j, r)),
                    None => self.reduce(cur, &[])?,
                };
                let Some(Red::Q(j, r)) = red else { break };
                steps.push((cur, j, r));
                cur = j;
                if self.join_tuple(&self.expand(&self.qs[cur])).is_some() && !self.passes_on(&self.qs[cur]) {
                    done = Some(cur);
                    break;
                }
            }
            match done {
                Some(fin) => {
                    let mut pf = self.leaf_jump(lo, x, fin, w)?;
                    for (a, b, r) in steps.into_iter().rev() {
                        let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[a].clone()), ("q2", self.qs[b].clone())]), vec![t(w), s(&pf), p(r)]);
                        pf = self.run(&rr, &[])?;
                    }
                    return Ok(pf);
                }
                None => self.trace(|| format!("ref: no enclosing join reached ({} steps)", steps.len())),
            }
        }
        // (the point found or made here, related by its hypothesis)
        let r = self.qs[qi].clone();
        let g = self.gref.as_ref().ok_or("the CFG going on outside its loop")?;
        let (cur, inv) = (g.cur, g.inv.clone());
        if g.inv_var.is_none() {
            return Err("the CFG going on outside its cut points' walks".into());
        }
        let xs = self.app(x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| q.to_vec())).ok_or("a CFG state not a world, a label and locals")?;
        let k = nat(&xs[0]).ok_or("a CFG state's label not a literal")?;
        let comps = self.locals_of(&xs[1]);
        let i = self.point_at(k, &comps, &r)?;
        self.trace(|| format!("ref: jump to point {} (label {}, from {})", i, k, cur));
        let h = self.point_hyp(i)?;
        let hs = self.assume(&h)?;
        let ip = self.run(&mp(R::S(hs), vec![t(x), t(&r), t(&xs[1]), simp0(), simp0()]), &[])?;
        self.run(&mp(R::Inst("g.ref_jump".into(), vec![("inv", inv)]), vec![t(x), t(&r), t(w), s(&ip), simp0()]), &[])
    }
    /// the structured side's own reduction (its head neither an operation,
    /// a choice nor an undecided condition): the walk on, g.ref_up
    fn up_step(&mut self, lo: &Term, qi: usize, w: &Term) -> Result<Option<Seq>, String> {
        // (a procedure's name: its definition, by the reducer)
        let ub = self.app(&self.qs[qi], "mkprog", 1).map(|x| x[0].clone()).unwrap_or_else(|| Term::bvar(0));
        if let Some((ua, _)) = block(self, &ub) {
            // (the head's projections and constants first, as the CFG
            // side's)
            if let Some((j, r)) = self.up_proj_in(qi, w, Some(&ua))? {
                let rest = self.walk(lo, j, w)?;
                let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
                return self.run(&rr, &[]).map(Some);
            }
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
        let red = match self.up_proj(qi, w)? {
            Some((j, r)) => Some(Red::Q(j, r)),
            None => self.reduce(qi, &[])?,
        };
        match red {
            Some(Red::Q(j, r)) => {
                let rest = self.walk(lo, j, w)?;
                let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
                self.run(&rr, &[]).map(Some)
            }
            None => Ok(None),
            Some(_) => Err(format!("the structured side: a step other than a reduction at {}", self.lambda(2, &ub))),
        }
    }

    /// the structured side's closed projection of a constructed tuple or
    /// outcome taken (`fst(diverge(t)) = 0`: decided after it): its next
    /// program, the step's proof
    fn up_proj(&mut self, qi: usize, w: &Term) -> Result<Option<(usize, R)>, String> {
        self.up_proj_in(qi, w, None)
    }

    /// ... one in the part `sub` of it (its head)
    fn up_proj_in(&mut self, qi: usize, w: &Term, sub: Option<&Term>) -> Result<Option<(usize, R)>, String> {
        let Some(ub) = self.app(&self.qs[qi], "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some((r, eq)) = self.closed_redex(sub.unwrap_or(&ub)) else { return Ok(None) };
        let eqc = self.run(&eq, &[])?.concl().clone();
        let v = self.app(&eqc, "eq", 2).ok_or("a projection's equation")?[1].clone();
        let bb = self.abstract_(&ub, &r, 0);
        let (j, inst) = self.by(qi, "tr.qe_eq", &[("b", bb), ("e", r), ("e2", v)])?;
        Ok(Some((j, mp(inst, vec![p(eq), t(w)]))))
    }

    /// the result o = e: the structured side's the same
    fn leaf_eq(&mut self, e: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
        let lo = self.mk("eq", vec![Term::bvar(0), e.clone()]);
        // (a procedure's name: unfolded by the reducer below)
        let ub = self.app(&self.qs[qi], "mkprog", 1).map_or_else(|| Term::bvar(0), |x| x[0].clone());
        if let Some(x) = self.app(&ub, "eq", 2) {
            if matches!(x[0].node(), Node::BVar(0)) {
                // (its world the start's: x0 the world here)
                if x[1].loose_depth(&self.env.binders_fn()) > 0 {
                    let b = self.lam(&ub, &["x0", "x1"], &["x0", "x1"]).ok_or("the result")?;
                    let (j, inst) = self.by(qi, "tr.q_at", &[("b", b), ("w", w.clone())])?;
                    let rest = self.leaf_eq(e, j, w)?;
                    let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(inst)]);
                    return self.run(&rr, &[]);
                }
                if self.canon(&x[1]) != self.canon(e) {
                    return Err(format!("the results differ: {} / {}", self.print(e), self.print(&x[1])));
                }
                return self.run(&mp(R::Inst("g.ref_eq".into(), vec![("e", e.clone())]), vec![t(w)]), &[]);
            }
        }
        let red = match self.up_proj(qi, w)? {
            Some((j, r)) => Some(Red::Q(j, r)),
            None => self.reduce(qi, &[])?,
        };
        match red {
            Some(Red::Q(j, r)) => {
                let rest = self.leaf_eq(e, j, w)?;
                let rr = mp(R::Inst("g.ref_up".into(), vec![("l", lo), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone())]), vec![t(w), s(&rest), p(r)]);
                self.run(&rr, &[])
            }
            _ => Err(format!("the result {}: the structured side at {}", self.print(e), self.lambda(2, &ub))),
        }
    }
}

/// A local's place in a point's shape: free (its own component), a
/// literal, the same as an earlier local
#[derive(Clone, PartialEq)]
enum Sh {
    Free,
    Lit(Term),
    Same(usize),
}

/// A point: a label, its locals' shape, the structured side's program
/// there (`y. u`, its free locals by y's projections)
#[derive(Clone)]
struct GPoint {
    label: u128,
    shape: Vec<Sh>,
    tmpl: Term,
}

/// The CFG's loop being walked: its locals' number, its cut points (made
/// as walks reach them), their relation inv
pub(super) struct GRef {
    m: usize,
    points: Vec<GPoint>,
    inv: Term,
    /// the loop's body (`l o. b`)
    b: Term,
    /// the label of the point walked
    cur: u128,
    /// by cut points (g.cut_acyclic): the labels' sets and ways
    cut: Option<GCut>,
    /// one pass (the cut points): inv a free relation `INV` while walking,
    /// a jump to point i by its hypothesis `hyps[i]` (`all l q y. l =
    /// pair(fst(l), pair(k, sh(y))) -> q = u(y) -> INV(l, q)`); each
    /// point's walk kept (`walked`), INV then the points' disjunction
    inv_var: Option<VarId>,
    hyps: Vec<Option<Term>>,
    walked: Vec<Seq>,
    /// the loop heads (g.cut_loops): a jump there goes on to the
    /// structured loop, its point's template the loop
    loop_heads: BTreeSet<u128>,
}

/// The cut points' walk (g.cut_acyclic): the CFG's labels (`v`, its
/// disjuncts' labels), each label's leaves (a jump's label, None a
/// `return`) -- found by its block's walk alone
pub(super) struct GCut {
    v: Term,
    labels: Vec<u128>,
    succ: BTreeMap<u128, Vec<Option<u128>>>,
    /// the labels' walks proving their ways on as they find them: v and m
    /// free relations V, M meanwhile, a leaf at label k2 by `hv[k2]` (`all
    /// w y. V(pair(w, pair(k2, y)))`), its rank by `hm[(k, k2)]` (`all w y
    /// w2 y2. int_lt(M(pair(w2, pair(k2, y2))), M(pair(w, pair(k, y))))`);
    /// each label's claim kept
    vm: Option<(VarId, VarId)>,
    hv: BTreeMap<u128, Term>,
    hm: BTreeMap<(u128, u128), Term>,
    ways: BTreeMap<u128, Seq>,
}

impl<'e> Gen<'e> {
    /// t with `from` (a closed term) written `to`
    fn replace_t(&self, t: &Term, from: &Term, to: &Term) -> Term {
        // (a part that cannot hold `from` as it is; each shared part once)
        fn go(t: &Term, from: &Term, to: &Term, memo: &mut std::collections::HashMap<Term, Term>) -> Term {
            if t == from {
                return to.clone();
            }
            if !t.may_contain_vars_of(from) {
                return t.clone();
            }
            match t.node() {
                Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => {
                    if let Some(x) = memo.get(t) {
                        return x.clone();
                    }
                    let out = t.with_args(a.iter().map(|x| go(x, from, to, memo)).collect());
                    memo.insert(t.clone(), out.clone());
                    out
                }
                _ => t.clone(),
            }
        }
        go(t, from, to, &mut std::collections::HashMap::new())
    }

    /// t's size as a tree (saturating; each shared part counted once)
    fn term_size(t: &Term) -> usize {
        fn go(t: &Term, memo: &mut std::collections::HashMap<Term, usize>) -> usize {
            match t.node() {
                Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => {
                    if let Some(n) = memo.get(t) {
                        return *n;
                    }
                    let n = a.iter().fold(1usize, |s, x| s.saturating_add(go(x, memo)));
                    memo.insert(t.clone(), n);
                    n
                }
                _ => 1,
            }
        }
        go(t, &mut std::collections::HashMap::new())
    }

    /// the shape of the locals comps (literals, the same values), the
    /// program r abstracted over the free ones (`y. u`)
    fn point_of(&mut self, label: u128, comps: &[Term], r: &Term) -> Result<GPoint, String> {
        let m = comps.len();
        let ce: Vec<Term> = comps.iter().map(|c| self.expand(c)).collect();
        let n = self.fresh("gy");
        let yv = self.var(&n);
        let mut t = self.expand(r);
        // (at a join -- `ex x2. x2 = ok(pair(x0, T), empty) && K`, K reading
        // the branch's assigned locals from x2 alone -- those locals free,
        // their components of T the projections: whatever each way assigned)
        let mut muts = vec![false; m];
        // (at a loop -- `ex x9. while_rel(pair(x0, T), ..) && K` -- the same,
        // T the loop's state's locals; every local free: a head's claims
        // for every state there)
        if let Some(tup) = self.loop_tuple(&t) {
            let tc = self.locals_of(&tup);
            let mut tc2 = Vec::new();
            let same = |g: &Self, a: &Term, b: &Term| {
                a == b || g.canon(a) == g.canon(b) || matches!((g.eval_lit(&g.lit_bits(a)), g.eval_lit(&g.lit_bits(b))), (Some(x), Some(y)) if x == y)
            };
            for c in &tc {
                match (0..m).find(|&j| !muts[j] && same(self, &ce[j], c)) {
                    Some(j) => {
                        muts[j] = true;
                        tc2.push(self.cfg_proj(&yv, j, m));
                    }
                    None => return Err(format!("label {}: the loop's local {} no CFG local's", label, self.print(c))),
                }
            }
            let tup2 = self.tuple_of(&tc2);
            t = self.set_loop_tuple(&t, &tup2).ok_or("a loop's tuple")?;
            let tmpl = self.abs(&t, &[Self::var_id(&yv)]);
            return Ok(GPoint { label, shape: vec![Sh::Free; m], tmpl });
        }
        if let Some(tup) = self.join_tuple(&t) {
            let tc = self.locals_of(&tup);
            let mut tc2 = Vec::new();
            // (the same value: as written, by its names, or the same literal)
            let same = |g: &Self, a: &Term, b: &Term| {
                a == b || g.canon(a) == g.canon(b) || matches!((g.eval_lit(&g.lit_bits(a)), g.eval_lit(&g.lit_bits(b))), (Some(x), Some(y)) if x == y)
            };
            for c in &tc {
                match (0..m).find(|&j| !muts[j] && same(self, &ce[j], c)) {
                    Some(j) => {
                        muts[j] = true;
                        tc2.push(self.cfg_proj(&yv, j, m));
                    }
                    None => {
                        self.trace(|| format!("ref: label {}: a join's component {} no local's ({})", label, self.print(c), ce.iter().map(|x| self.print(x)).collect::<Vec<_>>().join(", ")));
                        tc2.push(c.clone())
                    }
                }
            }
            let tup2 = self.tuple_of(&tc2);
            t = self.set_join_tuple(&t, &tup2).ok_or("a join's tuple")?;
        }
        let mut shape = Vec::new();
        for j in 0..m {
            if muts[j] {
                shape.push(Sh::Free);
            } else if nat(&ce[j]).is_some() || self.app(&ce[j], "empty", 0).is_some() {
                shape.push(Sh::Lit(ce[j].clone()));
            } else if let Some(i) = (0..j).find(|&i| !muts[i] && ce[i] == ce[j] && shape[i] == Sh::Free) {
                shape.push(Sh::Same(i));
            } else {
                shape.push(Sh::Free);
            }
        }
        let mut order: Vec<usize> = (0..m).filter(|&j| shape[j] == Sh::Free && !muts[j]).collect();
        let sizes: Vec<usize> = ce.iter().map(Self::term_size).collect();
        order.sort_by_key(|&j| std::cmp::Reverse(sizes[j]));
        for j in order {
            let pj = self.cfg_proj(&yv, j, m);
            t = self.replace_t(&t, &ce[j], &pj);
        }
        let tmpl = self.abs(&t, &[Self::var_id(&yv)]);
        Ok(GPoint { label, shape, tmpl })
    }

    /// a point's shape as a function of y: its locals' tuple
    fn shape_t(&self, p: &GPoint, y: &Term, m: usize) -> Term {
        let comps: Vec<Term> = (0..m)
            .map(|j| match &p.shape[j] {
                Sh::Free => self.cfg_proj(y, j, m),
                Sh::Lit(c) => c.clone(),
                Sh::Same(i) => self.cfg_proj(y, *i, m),
            })
            .collect();
        let mut t = comps[m - 1].clone();
        for c in comps[..m - 1].iter().rev() {
            t = self.mk("pair", vec![c.clone(), t]);
        }
        t
    }

    /// the cut points' relation inv (`l q. ..`): a disjunct per point, its
    /// label's states of its locals' shape and its program there
    fn points_inv(&mut self) -> Term {
        let g = self.gref.as_ref().expect("the points");
        let (m, points) = (g.m, g.points.clone());
        let lv = self.var("gl");
        let qv = self.var("gq");
        let yv = self.var("gyy");
        let mut inv = self.mk("false", vec![]);
        for p in points.iter().rev() {
            let sh = self.shape_t(p, &yv, m);
            let u = p.tmpl.instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
            let e1 = self.mk("eq", vec![lv.clone(), self.mk("pair", vec![self.mk("fst", vec![lv.clone()]), self.mk("pair", vec![lit(p.label), sh])])]);
            let e2 = self.mk("eq", vec![qv.clone(), u]);
            let body = self.abs(&self.mk("and", vec![e1, e2]), &[Self::var_id(&yv)]);
            inv = self.mk("or", vec![self.mk("ex", vec![body]), inv]);
        }
        self.abs(&inv, &[Self::var_id(&lv), Self::var_id(&qv)])
    }

    /// the point of the label k at locals comps and program r: its index
    /// (found here in the first pass)
    fn point_at(&mut self, k: u128, comps: &[Term], r: &Term) -> Result<usize, String> {
        let pt = self.point_of(k, comps, r)?;
        let g = self.gref.as_ref().expect("the points");
        let found = g.points.iter().position(|p| p.label == k && p.shape == pt.shape && p.tmpl == pt.tmpl);
        if let Some(i) = found {
            return Ok(i);
        }
        // (made only while the cut points are walked)
        if g.inv_var.is_none() {
            return Err(format!("label {}: not among the cut points", k));
        }
        // (C1_TRACE: how a label's new point differs from its others)
        if std::env::var("C1_TRACE").is_ok() {
            for p in g.points.iter().filter(|p| p.label == k) {
                let sh = |s: &Sh| match s {
                    Sh::Free => "free".to_string(),
                    Sh::Lit(c) => format!("lit {}", self.print(c)),
                    Sh::Same(i) => format!("same as {}", i),
                };
                let diff: Vec<String> = (0..pt.shape.len()).filter(|&j| p.shape[j] != pt.shape[j]).map(|j| format!("local {}: {} / {}", j, sh(&p.shape[j]), sh(&pt.shape[j]))).collect();
                // (the templates' first differing parts)
                fn first_diff(a: &Term, b: &Term) -> Option<(Term, Term)> {
                    if a == b {
                        return None;
                    }
                    if let (Node::App(s, x), Node::App(t, y)) = (a.node(), b.node()) {
                        if s == t && x.len() == y.len() {
                            return x.iter().zip(y.iter()).find_map(|(u, v)| first_diff(u, v));
                        }
                    }
                    Some((a.clone(), b.clone()))
                }
                let shown = |t: &Term| match t.node() {
                    _ if t.loose_depth(&self.env.binders_fn()) == 0 => self.print(t),
                    Node::App(s, _) => format!("<open {}>", self.env.syms[*s as usize].name),
                    _ => "<open>".into(),
                };
                let td = first_diff(&p.tmpl, &pt.tmpl).map(|(a, b)| format!("; the template: {} / {}", shown(&a), shown(&b))).unwrap_or_default();
                eprintln!("c1 ref: point differs at label {}: {}{}", k, diff.join(", "), td);
                // (C1_DUMP=dir: the two templates, instantiated at a variable)
                if let Ok(d) = std::env::var("C1_DUMP") {
                    let yv = Term::var(self.env.vars.len() as u32 - 1, vec![]);
                    let n = std::fs::read_dir(&d).map(|r| r.count()).unwrap_or(0);
                    for (i, tm) in [&p.tmpl, &pt.tmpl].into_iter().enumerate() {
                        let x = tm.instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
                        let _ = std::fs::write(format!("{}/l{}_{}_{}.txt", d, k, n, i), self.print(&x));
                    }
                }
            }
        }
        let g = self.gref.as_mut().unwrap();
        g.points.push(pt);
        Ok(g.points.len() - 1)
    }

    /// `inv(x, r)`: x the CFG's state (label k, locals comps), r the
    /// structured side's program -- its point's disjunct
    fn inv_at(&mut self, x: &Term, r: &Term) -> Result<Seq, String> {
        let xs = self.app(x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| q.to_vec())).ok_or("a CFG state not a world, a label and locals")?;
        let k = nat(&xs[0]).ok_or("a CFG state's label not a literal")?;
        let comps = self.locals_of(&xs[1]);
        let i = self.point_at(k, &comps, r)?;
        self.inv_at_pt(x, r, i)
    }

    /// ... at point i
    fn inv_at_pt(&mut self, x: &Term, r: &Term, i: usize) -> Result<Seq, String> {
        let xs = self.app(x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| q.to_vec())).ok_or("a CFG state not a world, a label and locals")?;
        let k = nat(&xs[0]).ok_or("a CFG state's label not a literal")?;
        let (m, p) = {
            let g = self.gref.as_ref().unwrap();
            (g.m, g.points[i].clone())
        };
        let yv = self.var("giy");
        let shl = {
            let s0 = self.shape_t(&p, &yv, m);
            self.abs(&s0, &[Self::var_id(&yv)])
        };
        let ys2 = xs[1].clone();
        let r1 = mpf_inst(
            "g.inv_intro",
            vec![("k", lit(k)), ("sh", shl), ("u", p.tmpl.clone())],
            vec![t(x), t(r), t(&ys2), simp0(), simp0()],
        );
        let one = self.run(&r1, &[])?;
        let inv = self.gref.as_ref().unwrap().inv.clone();
        let goal = inv.instantiate_params(&[x.clone(), r.clone()], &self.env.binders_fn());
        self.evp(&RP::Taut(vec![R::S(one)]), &goal, &[])
    }
}

/// `mp(Inst(lemma, binds), args)`
fn mpf_inst(lemma: &str, binds: Vec<(&'static str, Term)>, args: Vec<RA>) -> R {
    mp(R::Inst(lemma.into(), binds), args)
}

impl<'e> Gen<'e> {

    /// a premise `all l q. inv(l, q) -> G(l, q)`: G (`l q. ..`)
    fn claim_lam(&self, prem: &Term) -> Result<Term, String> {
        let b1 = self.app(prem, "all", 1).ok_or("a premise over the points")?[0].clone();
        let b2 = self.app(&b1, "all", 1).ok_or("a premise over the points")?[0].clone();
        let (hs, g) = self.imps(&b2);
        if hs.len() != 1 {
            return Err("a premise over the points: not inv -> ..".into());
        }
        Ok(g)
    }

    /// point i's g.inv_pt2 instance for the claim G: its proof term, its
    /// premise `all w y. G(pair(w, pair(k, sh(y))), u(y))`
    fn pt_prem(&mut self, gl: &Term, i: usize) -> Result<(R, Term), String> {
        let (m, p) = {
            let g = self.gref.as_ref().unwrap();
            (g.m, g.points[i].clone())
        };
        let yv = self.var("gsy");
        let shl = {
            let s0 = self.shape_t(&p, &yv, m);
            self.abs(&s0, &[Self::var_id(&yv)])
        };
        let (r, st) = self.inst("g.inv_pt2", &[("G", gl.clone()), ("k", lit(p.label)), ("sh", shl), ("u", p.tmpl.clone())])?;
        let (hs, _) = self.imps(&st);
        Ok((r, hs[0].clone()))
    }

    /// `all l q. inv(l, q) -> G(l, q)` from each point's claim (which: 0
    /// its segments' walk, else its label's state in v), by g.inv_or
    fn combine(&mut self, prem: &Term, which: u8) -> Result<Seq, String> {
        let gl = self.claim_lam(prem)?;
        let inv = self.gref.as_ref().unwrap().inv.clone();
        // inv's disjuncts: A_i, the rest after each
        let mut disj = Vec::new();
        let mut cur = inv.clone();
        while let Some(o) = self.app(&cur, "or", 2).map(|o| o.to_vec()) {
            disj.push((o[0].clone(), o[1].clone()));
            cur = o[1].clone();
        }
        let n = self.gref.as_ref().unwrap().points.len();
        if disj.len() != n {
            return Err("inv's disjuncts not the points".into());
        }
        let mut acc = self.run(&R::Inst("g.inv_none".into(), vec![("G", gl.clone())]), &[])?;
        for i in (0..n).rev() {
            let (r, prem_i) = self.pt_prem(&gl, i)?;
            self.gref.as_mut().unwrap().cur = self.gref.as_ref().unwrap().points[i].label;
            let pf = match which {
                // (walked already, in the one pass)
                0 => self.gref.as_ref().unwrap().walked.get(i).cloned().ok_or("a cut point not walked")?,
                _ => self.point_v(&prem_i)?,
            };
            self.trace(|| format!("ref: phase: point {} (label {}) proven", i, self.gref.as_ref().unwrap().points[i].label));
            let pt = self.run(&mp(r, vec![s(&pf)]), &[])?;
            acc = self.run(&mp(R::Inst("g.inv_or".into(), vec![("G", gl.clone()), ("A", disj[i].0.clone()), ("B", disj[i].1.clone())]), vec![s(&pt), s(&acc)]), &[])?;
            self.drop_caches();
        }
        Ok(acc)
    }

    /// the term caches (the environment's, canonical forms', expansions')
    /// emptied: a point's walk's terms not kept alive after it
    fn drop_caches(&self) {
        self.env.clear_term_caches();
        self.exp_memo.borrow_mut().clear();
        self.canon_memo.borrow_mut().clear();
    }

    /// a point's rank a number: `all w y. m(..) in omega`
    fn rank_ok(&mut self, prem: &Term) -> Result<Seq, String> {
        let (wv, yv) = (self.var("mw"), self.var("my"));
        let b = self.app(prem, "all", 1).ok_or("the rank's premise")?[0].clone().instantiate_params(std::slice::from_ref(&wv), &self.env.binders_fn());
        let b = self.app(&b, "all", 1).ok_or("the rank's premise")?[0].clone().instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
        let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &b, &[])?;
        self.close(pf, &[], &[Self::var_id(&wv), Self::var_id(&yv)])
    }

    /// The CFG's side alone: `g.post(o. lo, o. pp)` (l1 the iteration's
    /// state, for the rank)
    fn post(&mut self, lo: &Term, pp: &Term, l1: &Term) -> Result<Seq, String> {
        self.trace(|| format!("post: low {}", self.lambda(1, lo)));
        let proj = if block(self, lo).is_none() { self.proj_step(lo)? } else { None };
        if let Some((lo2, imp)) = proj {
            let rest = self.post(&lo2, pp, l1)?;
            return self.run(&mp(R::Inst("g.post_low".into(), vec![("l", lo.clone()), ("l2", lo2), ("p", pp.clone())]), vec![s(&imp), s(&rest)]), &[]);
        }
        if let Some(e) = self.leaf_of(lo) {
            let pe = self.post_leaf(&e, pp, l1)?;
            return self.run(&mp(R::Inst("g.post_eq".into(), vec![("e", e), ("p", pp.clone())]), vec![s(&pe)]), &[]);
        }
        if let Some((lo2, imp)) = self.low_step(lo)? {
            let rest = self.post(&lo2, pp, l1)?;
            return self.run(&mp(R::Inst("g.post_low".into(), vec![("l", lo.clone()), ("l2", lo2), ("p", pp.clone())]), vec![s(&imp), s(&rest)]), &[]);
        }
        let (a, k) = block(self, lo).ok_or_else(|| format!("the CFG side alone: no step at {}", self.lambda(1, lo)))?;
        let lctx = ["o", "x8"];
        let kl = self.lam(&k, &lctx, &["x8", "o"]).ok_or("the lower block's rest")?;
        if let Some(x) = self.app(&a, "bind_rel", 5).map(|x| x.to_vec()) {
            let op = self.lam(&x[0], &lctx, &[]).ok_or("an operation reads the block")?;
            let sw = self.lam(&x[1], &lctx, &[]).ok_or("an operation's world reads the block")?;
            let ka = self.lam(&x[2], &["o", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's rest")?;
            let xa = self.lam(&x[3], &["o", "x8", "x9", "x10"], &["x9", "x10", "x8"]).ok_or("an operation's handler")?;
            let da = self.lam(&x[4], &["o", "x8", "x9"], &["x9", "x8"]).ok_or("an operation's handler")?;
            let (rr, stmt) = self.inst("g.post_op", &[("op", op), ("ka", ka), ("xa", xa), ("da", da), ("kl", kl), ("p", pp.clone())])?;
            let body = self.app(&stmt, "all", 1).ok_or("g.post_op")?[0].clone().instantiate_params(std::slice::from_ref(&sw), &self.env.binders_fn());
            let (prems, _) = self.imps(&body);
            let mut pfs = Vec::new();
            for (pr, names) in prems.iter().zip([&["ps", "pv"][..], &["ps", "pe"][..], &["pt"][..]]) {
                pfs.push(self.sub_post(pr, names, l1)?);
            }
            return self.run(&mp(rr, vec![t(&sw), s(&pfs[0]), s(&pfs[1]), s(&pfs[2])]), &[]);
        }
        if let Some(x) = self.app(&a, "or", 2).map(|x| x.to_vec()) {
            let l = self.app(&x[0], "and", 2).map(|y| y.to_vec());
            let r = self.app(&x[1], "and", 2).map(|y| y.to_vec());
            if let (Some(l), Some(r)) = (l, r) {
                let c = self.lam(&l[0], &lctx, &[]).ok_or("a condition reads the block")?;
                let a1 = self.lam(&l[1], &lctx, &["x8"]).ok_or("a way")?;
                let a2 = self.lam(&r[1], &lctx, &["x8"]).ok_or("a way")?;
                let (rr, stmt) = self.inst("g.post_if", &[("c", c), ("a1", a1), ("a2", a2), ("kl", kl), ("p", pp.clone())])?;
                let (prems, _) = self.imps(&stmt);
                let mut pfs = Vec::new();
                for pr in prems.iter().take(2) {
                    let (hs, g0) = self.imps(pr);
                    let _h = self.assume(&hs[0])?;
                    let x2 = self.app(&g0, "g.post", 2).ok_or("g.post_if's premise")?.to_vec();
                    let r1 = self.post(&x2[0], &x2[1], l1)?;
                    pfs.push(self.close(r1, &[hs[0].clone()], &[])?);
                }
                return self.run(&mp(rr, vec![s(&pfs[0]), s(&pfs[1])]), &[]);
            }
        }
        Err(format!("the CFG side alone: no step at {}", self.lambda(1, lo)))
    }

    fn sub_post(&mut self, prem: &Term, names: &[&str], l1: &Term) -> Result<Seq, String> {
        let mut cur = prem.clone();
        let mut vs = Vec::new();
        for nm in names {
            let b = self.app(&cur, "all", 1).ok_or("a rule's premise: not all")?[0].clone();
            let n = self.fresh(nm);
            let v = self.var(&n);
            cur = b.instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
            vs.push(Self::var_id(&v));
        }
        let x = self.app(&cur, "g.post", 2).ok_or("a rule's premise: not g.post")?.to_vec();
        let r = self.post(&x[0], &x[1], l1)?;
        self.close(r, &[], &vs)
    }

    /// A label's walk's leaf e (its block's outcome; l1 the label's state):
    /// its way on found (a jump's label, a `return`); going on at label k2
    /// -- V there and M lower, by their hypotheses (g.post_leaf_v); leaving,
    /// no state (g.post_exc, g.post_div)
    fn post_leaf(&mut self, e: &Term, pp: &Term, l1: &Term) -> Result<Seq, String> {
        let (vv, mv) = self.gref.as_ref().and_then(|g| g.cut.as_ref()).and_then(|c| c.vm).ok_or("a leaf outside a label's walk")?;
        let cur = self.gref.as_ref().unwrap().cur;
        let leaf = if let Some(o) = self.app(e, "ok", 2) {
            let k = self.app(&o[0], "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).and_then(|q| nat(&q[0]))).ok_or("a block going on: not at a label")?;
            Some(Some(k))
        } else if let Some(x) = self.app(e, "exc", 2) {
            self.app(&x[1], "pair", 2).filter(|p| matches!(p[0].node(), Node::Bytes(b) if &b[..] == b"ret")).map(|_| None)
        } else {
            None
        };
        if let Some(l) = leaf {
            self.gref.as_mut().unwrap().cut.as_mut().unwrap().succ.entry(cur).or_default().push(l);
        }
        if let (Some(Some(k2)), Some(o)) = (leaf, self.app(e, "ok", 2).map(|o| o.to_vec())) {
            let parts = |g: &Self, x: &Term| g.app(x, "pair", 2).and_then(|p| g.app(&p[1], "pair", 2).map(|q| (p[0].clone(), q[1].clone())));
            let (w2, y2) = parts(self, &o[0]).ok_or("a block going on: not at a label")?;
            let (w1, y1) = parts(self, l1).ok_or("the label's state")?;
            let hv = self.label_hyp(k2, None)?;
            let hm = self.label_hyp(cur, Some(k2))?;
            let (hvs, hms) = (self.assume(&hv)?, self.assume(&hm)?);
            let vx = self.run(&mp(R::S(hvs), vec![t(&w2), t(&y2)]), &[])?;
            let mx = self.run(&mp(R::S(hms), vec![t(&w1), t(&y1), t(&w2), t(&y2)]), &[])?;
            let (vl, ml) = (Term::var(vv, vec![Term::bvar(0)]), Term::var(mv, vec![Term::bvar(0)]));
            return self.run(&mp(R::Inst("g.post_leaf_v".into(), vec![("v", vl), ("m", ml)]), vec![t(l1), t(&o[0]), s(&vx), s(&mx)]), &[]);
        }
        let ql = {
            let b = self.app(pp, "all", 1).ok_or("the ways' condition")?[0].clone();
            let (_, q) = self.imps(&b);
            self.lam(&q, &["o", "l2"], &["l2"]).ok_or("the ways' condition reads the outcome")?
        };
        if let Some(x) = self.app(e, "exc", 2).map(|x| x.to_vec()) {
            return self.run(&R::Inst("g.post_exc".into(), vec![("a", x[0].clone()), ("b", x[1].clone()), ("Q", ql)]), &[]);
        }
        if let Some(x) = self.app(e, "diverge", 1).map(|x| x.to_vec()) {
            return self.run(&R::Inst("g.post_div".into(), vec![("a", x[0].clone()), ("Q", ql)]), &[]);
        }
        Err(format!("a block's outcome {}: not ok, exc, diverge", self.print(e)))
    }
}

impl<'e> Gen<'e> {
    /// The CFG's loop by cut points (g.cut_acyclic): its labels and their
    /// ways found by each block's walk alone (from the first label); the
    /// cut labels the structuring's (crate::gimple::structure) on that
    /// graph -- its joins and loop heads, and the first label; a rank over
    /// all labels; the cut points (a cut label, its locals' shape, the
    /// structured side's program there) found in a first pass of their
    /// segments' walks, proven in a second
    fn cfg_loop(&mut self, lo: &Term, a: &Term, k: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
        let x = self.app(a, "while_rel", 5).ok_or("the CFG's loop")?.to_vec();
        let lctx = ["o", "x8"];
        let l0 = self.lam(&x[0], &lctx, &[]).ok_or("the loop's start reads the block")?;
        let b = self.lam(&x[2], &["o", "x8", "x9", "x10"], &["x9", "x10"]).ok_or("the loop's body")?;
        let tr = self.lam(&x[3], &["o", "x8", "x9"], &["x9"]).ok_or("the loop's trace")?;
        let kk = self.lam(k, &lctx, &["x8", "o"]).ok_or("the loop's rest")?;
        let xs = self.app(&l0, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| q.to_vec())).ok_or("the loop's start not a world, a label and locals")?;
        let k_e = nat(&xs[0]).ok_or("the first label not a literal")?;
        let comps = self.locals_of(&xs[1]);
        let q0 = self.qs[qi].clone();
        let fls = self.mk("false", vec![]);
        // (the labels' set and rank free relations V, M while their blocks
        // are walked)
        let (vv, mv) = (self.env.new_var("gv", 1), self.env.new_var("gm", 1));
        let cut = GCut { v: fls.clone(), labels: Vec::new(), succ: BTreeMap::new(), vm: Some((vv, mv)), hv: BTreeMap::new(), hm: BTreeMap::new(), ways: BTreeMap::new() };
        self.gref = Some(GRef { m: comps.len(), points: Vec::new(), inv: fls.clone(), b: b.clone(), cur: k_e, cut: Some(cut), inv_var: None, hyps: Vec::new(), walked: Vec::new(), loop_heads: BTreeSet::new() });
        // the labels: each block walked alone, its leaves found and its ways
        // on proven
        let mut work = vec![k_e];
        let mut seen: BTreeSet<u128> = BTreeSet::new();
        let mut ways: BTreeMap<u128, Seq> = BTreeMap::new();
        while let Some(kl) = work.pop() {
            if !seen.insert(kl) {
                continue;
            }
            self.gref.as_mut().unwrap().cur = kl;
            ways.insert(kl, self.label_ways(kl)?);
            self.drop_caches();
            let succ = self.gref.as_ref().unwrap().cut.as_ref().unwrap().succ.get(&kl).cloned().unwrap_or_default();
            work.extend(succ.into_iter().flatten());
        }
        let labels: Vec<u128> = seen.into_iter().collect();
        let succ = self.gref.as_ref().unwrap().cut.as_ref().unwrap().succ.clone();
        let cuts = cut_labels(&labels, &succ, k_e)?;
        self.trace(|| format!("ref: {} labels, cut at {:?}", labels.len(), cuts));
        // (a rank: the longest way on)
        let mut rank: BTreeMap<u128, u128> = BTreeMap::new();
        for _ in 0..=labels.len() {
            for &kl in &labels {
                let r = succ.get(&kl).into_iter().flatten().flatten().map(|s| rank.get(s).copied().unwrap_or(0) + 1).max().unwrap_or(0);
                rank.insert(kl, r);
            }
        }
        if labels.iter().any(|kl| succ.get(kl).into_iter().flatten().flatten().any(|s| rank[s] >= rank[kl])) {
            // (the labels go round a loop: g.cut_loops)
            return self.cfg_loops(lo, &l0, &b, &tr, &kk, &comps, k_e, &labels, &succ, &cuts, &q0, w);
        }
        let lv = self.var("gl");
        let mut table = self.mk("empty", vec![]);
        for (kl, r) in &rank {
            table = self.mk("fn_update", vec![table, lit(*kl), lit(*r)]);
        }
        let rank_l = self.abs(&self.mk("app", vec![table, self.mk("fst", vec![self.mk("snd", vec![lv.clone()])])]), &[Self::var_id(&lv)]);
        // (the labels' states v, the cut labels' pt)
        let yv = self.var("gly");
        let mut v = fls.clone();
        for &kl in labels.iter().rev() {
            let e = self.mk("eq", vec![lv.clone(), self.mk("pair", vec![self.mk("fst", vec![lv.clone()]), self.mk("pair", vec![lit(kl), yv.clone()])])]);
            let d = self.mk("ex", vec![self.abs(&e, &[Self::var_id(&yv)])]);
            v = self.mk("or", vec![d, v]);
        }
        let v_l = self.abs(&v, &[Self::var_id(&lv)]);
        let mut pt = fls.clone();
        for &kl in cuts.iter().rev() {
            let e = self.mk("eq", vec![self.mk("fst", vec![self.mk("snd", vec![lv.clone()])]), lit(kl)]);
            pt = self.mk("or", vec![e, pt]);
        }
        let pt_l = self.abs(&pt, &[Self::var_id(&lv)]);
        {
            let c = self.gref.as_mut().unwrap().cut.as_mut().unwrap();
            (c.v, c.labels) = (v_l.clone(), labels.clone());
        }
        // (V, M the labels' set and rank: each hypothesis proven -- a
        // label's state by its disjunct, a rank's step by evaluation -- and
        // each label's ways on discharged)
        let (hv, hm) = {
            let c = self.gref.as_ref().unwrap().cut.as_ref().unwrap();
            (c.hv.clone(), c.hm.clone())
        };
        let at = |g: &mut Self, h: &Term| -> Result<Term, String> {
            let a = g.assume(h)?;
            let a = Seq::inst(g.env, &a, vv, &v_l).map_err(|e| e.0)?;
            Ok(Seq::inst(g.env, &a, mv, &rank_l).map_err(|e| e.0)?.concl().clone())
        };
        let mut hps: Vec<(Term, Seq)> = Vec::new();
        for (k2, h) in hv {
            let hi = at(self, &h)?;
            let (w, y) = (self.var("vw"), self.var("vy"));
            let x = self.mk("pair", vec![w.clone(), self.mk("pair", vec![lit(k2), y.clone()])]);
            let pf = self.v_at(&x)?;
            hps.push((hi, self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])?));
        }
        for (_, h) in hm {
            let hi = at(self, &h)?;
            let mut body = hi.clone();
            let mut vs = Vec::new();
            for nm in ["mw", "my", "mw2", "my2"] {
                let v = self.var(nm);
                body = self.app(&body, "all", 1).ok_or("a rank's hypothesis")?[0].clone().instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
                vs.push(Self::var_id(&v));
            }
            let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &body, &[])?;
            hps.push((hi, self.close(pf, &[], &vs)?));
        }
        let mut done = BTreeMap::new();
        for (kl, pf) in ways {
            let s0 = Seq::inst(self.env, &pf, vv, &v_l).map_err(|e| e.0)?;
            let mut s0 = Seq::inst(self.env, &s0, mv, &rank_l).map_err(|e| e.0)?;
            for (hi, hp) in &hps {
                if s0.hyps().contains(hi) {
                    let d = s0.discharge(self.env, hi).map_err(|e| e.0)?;
                    s0 = Seq::mp(self.env, &d, hp).map_err(|e| e.0)?;
                }
            }
            if !s0.hyps().is_empty() {
                return Err(format!("label {}'s ways on: {} hypotheses left", kl, s0.hyps().len()));
            }
            done.insert(kl, s0);
        }
        self.gref.as_mut().unwrap().cut.as_mut().unwrap().ways = done;
        let inst = |g: &mut Self, inv: Term| g.inst("g.cut_acyclic", &[("b", b.clone()), ("tr", tr.clone()), ("k", kk.clone()), ("pt", pt_l.clone()), ("v", v_l.clone()), ("inv", inv), ("m", rank_l.clone())]);
        // each cut point's segments walked once, the cut points found as
        // they are reached: inv a free relation INV meanwhile, a jump by its
        // point's hypothesis
        let iv = self.env.new_var("ginv", 2);
        let inv_v = Term::var(iv, vec![Term::bvar(1), Term::bvar(0)]);
        {
            let g = self.gref.as_mut().unwrap();
            g.inv = inv_v.clone();
            g.inv_var = Some(iv);
        }
        self.point_at(k_e, &comps, &q0)?;
        let (_, stmt) = inst(self, inv_v)?;
        let (prems, _) = self.imps(&stmt);
        let gl = self.claim_lam(&prems[3])?;
        let mut i = 0;
        while i < self.gref.as_ref().unwrap().points.len() {
            let prem = self.pt_prem(&gl, i)?.1;
            self.gref.as_mut().unwrap().cur = self.gref.as_ref().unwrap().points[i].label;
            let pf = self.sub_walk(&prem, &["pw", "py"])?;
            self.gref.as_mut().unwrap().walked.push(pf);
            self.drop_caches();
            self.trace(|| format!("ref: phase: point {} (label {}) walked", i, self.gref.as_ref().unwrap().points[i].label));
            i += 1;
        }
        self.trace(|| format!("ref: {} cut points", self.gref.as_ref().unwrap().points.len()));
        // INV the points' disjunction: each hypothesis proven, each walk's
        // discharged
        let inv = self.points_inv();
        {
            let g = self.gref.as_mut().unwrap();
            g.inv = inv.clone();
            g.inv_var = None;
        }
        let n = self.gref.as_ref().unwrap().points.len();
        let mut hps: Vec<(Term, Seq)> = Vec::new();
        for j in 0..n {
            let Some(Some(h)) = self.gref.as_ref().unwrap().hyps.get(j).cloned() else { continue };
            let a = self.assume(&h)?;
            let hj = Seq::inst(self.env, &a, iv, &inv).map_err(|e| e.0)?.concl().clone();
            hps.push((hj, self.hyp_proof(j, &inv)?));
        }
        let walked = std::mem::take(&mut self.gref.as_mut().unwrap().walked);
        let mut done = Vec::new();
        for w0 in walked {
            let mut s0 = Seq::inst(self.env, &w0, iv, &inv).map_err(|e| e.0)?;
            for (hj, pf) in &hps {
                if s0.hyps().contains(hj) {
                    let d = s0.discharge(self.env, hj).map_err(|e| e.0)?;
                    s0 = Seq::mp(self.env, &d, pf).map_err(|e| e.0)?;
                }
            }
            if !s0.hyps().is_empty() {
                return Err(format!("a cut point's walk: {} hypotheses left", s0.hyps().len()));
            }
            done.push(s0);
        }
        self.gref.as_mut().unwrap().walked = done;
        let (rr, stmt) = inst(self, inv)?;
        let (prems, _) = self.imps(&stmt);
        self.trace(|| "ref: phase: the ways on".into());
        let pd = self.lab_combine(&prems[0], 1)?;
        self.trace(|| "ref: phase: the rank".into());
        let pm = self.lab_combine(&prems[1], 2)?;
        self.trace(|| "ref: phase: the points' labels".into());
        let pv = self.combine(&prems[2], 3)?;
        self.trace(|| "ref: phase: the points' walks".into());
        let ps = self.combine(&prems[3], 0)?;
        self.trace(|| "ref: phase: done".into());
        let main = self.run(&mp(rr, vec![s(&pd), s(&pm), s(&pv), s(&ps)]), &[])?;
        // at the loop's start: its point
        let i0 = self.inv_at(&l0, &q0)?;
        let (rv, ov) = (self.var("lr"), self.var("lo"));
        let c1 = self.run(&mp(R::S(main), vec![t(&l0), t(&q0), t(&rv), t(&ov), s(&i0)]), &[])?;
        let c1 = self.close(c1, &[], &[Self::var_id(&rv), Self::var_id(&ov)])?;
        let c2 = self.run(&mp(R::Inst("g.ref_cfg".into(), vec![("l", l0.clone()), ("q", q0.clone()), ("b", b), ("tr", tr), ("k", kk)]), vec![s(&c1)]), &[])?;
        self.gref = None;
        // (its world fst(l0): the walk's, w)
        let l0p = self.app(&l0, "pair", 2).ok_or("the loop's start not a pair")?.to_vec();
        if l0p[0] != *w {
            return Err(format!("the loop's start world {}: not the walk's", self.print(&l0p[0])));
        }
        let fe = R::Inst("fst_pair".into(), vec![("a", l0p[0].clone()), ("b", l0p[1].clone())]);
        let fl0 = self.mk("fst", vec![l0.clone()]);
        self.run(&mp(R::Inst("g.ref_ws".into(), vec![("l", lo.clone()), ("q", q0), ("a", fl0), ("b", w.clone())]), vec![p(fe), s(&c2)]), &[])
    }

    /// point i's claim `l = pair(fst(l), pair(k, sh(y)))`, `q = u(y)`, and
    /// the relation R at l, q (l, q, y given)
    fn point_rel(&self, i: usize, l: &Term, q: &Term, y: &Term, rel: &Term) -> (Term, Term, Term) {
        let g = self.gref.as_ref().unwrap();
        let p = g.points[i].clone();
        let sh = self.shape_t(&p, y, g.m);
        let u = p.tmpl.instantiate_params(std::slice::from_ref(y), &self.env.binders_fn());
        let e1 = self.mk("eq", vec![l.clone(), self.mk("pair", vec![self.mk("fst", vec![l.clone()]), self.mk("pair", vec![lit(p.label), sh])])]);
        let e2 = self.mk("eq", vec![q.clone(), u]);
        let c = rel.instantiate_params(&[l.clone(), q.clone()], &self.env.binders_fn());
        (e1, e2, c)
    }

    /// point i's hypothesis (one pass): `all l q y. l = pair(fst(l), pair(k,
    /// sh(y))) -> q = u(y) -> INV(l, q)`
    fn point_hyp(&mut self, i: usize) -> Result<Term, String> {
        if let Some(Some(h)) = self.gref.as_ref().unwrap().hyps.get(i) {
            return Ok(h.clone());
        }
        let iv = self.gref.as_ref().unwrap().inv_var.ok_or("a point's hypothesis outside one pass")?;
        let rel = Term::var(iv, vec![Term::bvar(1), Term::bvar(0)]);
        let (lv, qv, yv) = (self.var("hl"), self.var("hq"), self.var("hy"));
        let (e1, e2, c) = self.point_rel(i, &lv, &qv, &yv, &rel);
        let imp = |a: Term, b: Term| Term::app(self.env.builtins.imp, vec![a, b]);
        let body = imp(e1, imp(e2, c));
        let mut h = body;
        for v in [&yv, &qv, &lv] {
            h = self.mk("all", vec![self.abs(&h, &[Self::var_id(v)])]);
        }
        let g = self.gref.as_mut().unwrap();
        if g.hyps.len() <= i {
            g.hyps.resize(i + 1, None);
        }
        g.hyps[i] = Some(h.clone());
        Ok(h)
    }

    /// point i's hypothesis at the relation inv (`l q. ..`, the points'
    /// disjunction): by its disjunct (g.inv_intro)
    fn hyp_proof(&mut self, i: usize, inv: &Term) -> Result<Seq, String> {
        let (lv, qv, yv) = (self.var("pl"), self.var("pq"), self.var("py"));
        let (e1, e2, c) = self.point_rel(i, &lv, &qv, &yv, inv);
        let (a1, a2) = (self.assume(&e1)?, self.assume(&e2)?);
        let p = self.gref.as_ref().unwrap().points[i].clone();
        let m = self.gref.as_ref().unwrap().m;
        let y2 = self.var("py2");
        let shl = {
            let s0 = self.shape_t(&p, &y2, m);
            self.abs(&s0, &[Self::var_id(&y2)])
        };
        let one = self.run(&mpf_inst("g.inv_intro", vec![("k", lit(p.label)), ("sh", shl), ("u", p.tmpl.clone())], vec![t(&lv), t(&qv), t(&yv), s(&a1), s(&a2)]), &[])?;
        let pf = self.evp(&RP::Taut(vec![R::S(one)]), &c, &[])?;
        self.close(pf, &[e1, e2], &[Self::var_id(&lv), Self::var_id(&qv), Self::var_id(&yv)])
    }

    /// Label k's block walked alone, at any world and locals: `all l2. b(L,
    /// ok(l2, empty)) -> Q(l2)` (Q None: its leaves found, no proof)
    fn label_ways(&mut self, kl: u128) -> Result<Seq, String> {
        let bb = self.gref.as_ref().unwrap().b.clone();
        let (vv, mv) = self.gref.as_ref().unwrap().cut.as_ref().unwrap().vm.ok_or("the labels' relations")?;
        let (wv, yv) = (self.var("lw"), self.var("ly"));
        let l1 = self.mk("pair", vec![wv.clone(), self.mk("pair", vec![lit(kl), yv.clone()])]);
        // (Q: `l2. V(l2) && int_lt(M(l2), M(L))`)
        let ql = {
            let l2 = self.var("ll2");
            let c = self.mk("and", vec![Term::var(vv, vec![l2.clone()]), self.mk("int_lt", vec![Term::var(mv, vec![l2.clone()]), Term::var(mv, vec![l1.clone()])])]);
            self.abs(&c, &[Self::var_id(&l2)])
        };
        let bx = bb.instantiate_params(&[l1.clone(), Term::bvar(0)], &self.env.binders_fn());
        let (r, st) = self.inst("g.post_use", &[("b", bx), ("Q", ql)])?;
        let (ps, _) = self.imps(&st);
        let gp = self.app(&ps[0], "g.post", 2).ok_or("g.post_use's premise")?.to_vec();
        let pf = self.post(&gp[0], &gp[1], &l1)?;
        let one = self.run(&mp(r, vec![s(&pf)]), &[])?;
        self.close(one, &[], &[Self::var_id(&wv), Self::var_id(&yv)])
    }

    /// a label's hypothesis (its walk): `all w y. V(pair(w, pair(k, y)))`
    /// (`hm`: None), or the rank's from k to k2
    fn label_hyp(&mut self, k: u128, hm: Option<u128>) -> Result<Term, String> {
        {
            let c = self.gref.as_ref().unwrap().cut.as_ref().unwrap();
            let have = match hm {
                None => c.hv.get(&k),
                Some(k2) => c.hm.get(&(k, k2)),
            };
            if let Some(h) = have {
                return Ok(h.clone());
            }
        }
        let (vv, mv) = self.gref.as_ref().unwrap().cut.as_ref().unwrap().vm.ok_or("the labels' relations")?;
        let st = |g: &mut Self, k: u128| {
            let (w, y) = (g.var("hw"), g.var("hy"));
            (g.mk("pair", vec![w.clone(), g.mk("pair", vec![lit(k), y.clone()])]), vec![Self::var_id(&w), Self::var_id(&y)])
        };
        let (body, vs) = match hm {
            None => {
                let (l, vs) = st(self, k);
                (Term::var(vv, vec![l]), vs)
            }
            Some(k2) => {
                let (l, mut vs) = st(self, k);
                let (l2, vs2) = st(self, k2);
                vs.extend(vs2);
                (self.mk("int_lt", vec![Term::var(mv, vec![l2]), Term::var(mv, vec![l])]), vs)
            }
        };
        let mut h = body;
        for v in vs.iter().rev() {
            h = self.mk("all", vec![self.abs(&h, &[*v])]);
        }
        let c = self.gref.as_mut().unwrap().cut.as_mut().unwrap();
        match hm {
            None => c.hv.insert(k, h.clone()),
            Some(k2) => c.hm.insert((k, k2), h.clone()),
        };
        Ok(h)
    }

    /// `all l. v(l) -> G(l)` from each label's claim (which: 1 the ways on,
    /// 2 the rank), by g.lab_or
    fn lab_combine(&mut self, prem: &Term, which: u8) -> Result<Seq, String> {
        let b1 = self.app(prem, "all", 1).ok_or("a premise over the labels")?[0].clone();
        let (hs, gl) = self.imps(&b1);
        if hs.len() != 1 {
            return Err("a premise over the labels: not v -> ..".into());
        }
        let (v, labels) = {
            let c = self.gref.as_ref().unwrap().cut.as_ref().unwrap();
            (c.v.clone(), c.labels.clone())
        };
        let mut disj = Vec::new();
        let mut cur = v.clone();
        while let Some(o) = self.app(&cur, "or", 2).map(|o| o.to_vec()) {
            disj.push((o[0].clone(), o[1].clone()));
            cur = o[1].clone();
        }
        if disj.len() != labels.len() {
            return Err("v's disjuncts not the labels".into());
        }
        let mut acc = self.run(&R::Inst("g.lab_none".into(), vec![("G", gl.clone())]), &[])?;
        for i in (0..labels.len()).rev() {
            let (r, st) = self.inst("g.lab_pt", &[("G", gl.clone()), ("k", lit(labels[i]))])?;
            let (ps, _) = self.imps(&st);
            self.gref.as_mut().unwrap().cur = labels[i];
            let pf = match which {
                // (walked already, as its leaves were found)
                1 => self.gref.as_ref().unwrap().cut.as_ref().unwrap().ways.get(&labels[i]).cloned().ok_or("a label's block not walked")?,
                _ => self.rank_ok(&ps[0])?,
            };
            let one = self.run(&mp(r, vec![s(&pf)]), &[])?;
            acc = self.run(&mp(R::Inst("g.lab_or".into(), vec![("G", gl.clone()), ("A", disj[i].0.clone()), ("B", disj[i].1.clone())]), vec![s(&one), s(&acc)]), &[])?;
            self.drop_caches();
        }
        Ok(acc)
    }

    /// `v(x)`: x a state of a label (`pair(w, pair(k, ys))`), its disjunct
    fn v_at(&mut self, x: &Term) -> Result<Seq, String> {
        let xs = self.app(x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| vec![p[0].clone(), q[0].clone(), q[1].clone()])).ok_or("a CFG state not a world, a label and locals")?;
        let one = self.run(&mp(R::Inst("g.lab_intro".into(), vec![("k", xs[1].clone())]), vec![t(&xs[0]), t(&xs[2])]), &[])?;
        let v = self.gref.as_ref().unwrap().cut.as_ref().unwrap().v.clone();
        let goal = v.instantiate_params(std::slice::from_ref(x), &self.env.binders_fn());
        self.evp(&RP::Taut(vec![R::S(one)]), &goal, &[])
    }

    /// a cut point's claim `all w y. v(pair(w, pair(k, sh(y))))`
    fn point_v(&mut self, prem: &Term) -> Result<Seq, String> {
        let (wv, yv) = (self.var("vw"), self.var("vy"));
        let b = self.app(prem, "all", 1).ok_or("the labels' premise")?[0].clone().instantiate_params(std::slice::from_ref(&wv), &self.env.binders_fn());
        let b = self.app(&b, "all", 1).ok_or("the labels' premise")?[0].clone().instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
        let v = self.gref.as_ref().unwrap().cut.as_ref().unwrap().v.clone();
        // (the state: v's argument)
        let x = (|| {
            let o = self.app(&b, "or", 2)?;
            let e = self.app(&o[0], "ex", 1)?[0].clone();
            Some(self.app(&e, "eq", 2)?[0].clone())
        })()
        .ok_or("the labels' premise: not v")?;
        let _ = v;
        let pf = self.v_at(&x)?;
        self.close(pf, &[], &[Self::var_id(&wv), Self::var_id(&yv)])
    }

    /// The segment's run from the state x (the CFG side `ex x9.
    /// while_fin_rel(x, true, B, x9) && K(x9, o)`): x a cut state -- the
    /// claim there (g.seg_cut, the loop's rest refuted at the cut's mark);
    /// else its block, then on (g.seg_step)
    fn seg_step(&mut self, a: &Term, k: &Term) -> Result<Option<(Term, Seq)>, String> {
        let Some(wf) = self.app(a, "while_fin_rel", 4).map(|x| x.to_vec()) else { return Ok(None) };
        let ctx4 = ["o", "x8", "l", "y"];
        let x = self.lam(&wf[0], &["o", "x8"], &[]).ok_or("the segment's state reads the block")?;
        // (B: `(pt(l) && y = pair(3, l)) || (!pt(l) && b(l, y))`)
        let parts = (|| {
            let o = self.app(&wf[2], "or", 2)?;
            let l = self.app(&o[0], "and", 2)?;
            let r = self.app(&o[1], "and", 2)?;
            Some((l[0].clone(), r[1].clone()))
        })();
        let Some((ptb, bb)) = parts else { return Err("the segment's body".into()) };
        let pt = self.lam(&ptb, &ctx4, &["l"]).ok_or("the cut labels read the outcome")?;
        let b = self.lam(&bb, &ctx4, &["l", "y"]).ok_or("the segment's block")?;
        let kl = self.lam(k, &["o", "x8"], &["x8", "o"]).ok_or("the segment's rest")?;
        let ptx = pt.instantiate_params(std::slice::from_ref(&x), &self.env.binders_fn());
        match self.decide(&ptx) {
            Some((false, pf)) => self.low_by(mp(R::Inst("g.seg_step".into(), vec![("x", x), ("b", b), ("pt", pt), ("K", kl)]), vec![s(&pf)])).map(Some),
            Some((true, pf)) => {
                // (K: `(fst(x9) = 3 && J(snd(x9), o)) || k(x9, o)`)
                let o = self.app(&kl, "or", 2).ok_or("the segment's rest: not the cut's")?.to_vec();
                let l = self.app(&o[0], "and", 2).ok_or("the segment's rest: not the cut's")?.to_vec();
                let jl = un_snd(self, &l[1], 1).ok_or("the cut's claim reads more than its state")?;
                let k2 = o[1].clone();
                let ov = self.var("co");
                let mark = self.mk("pair", vec![lit(3), x.clone()]);
                let kx = k2.instantiate_params(&[mark, ov.clone()], &self.env.binders_fn());
                let nk = self.refute(&kx)?.ok_or("the loop's rest at the cut's mark: not refuted")?;
                let nk = self.close(nk, &[], &[Self::var_id(&ov)])?;
                self.low_by(mp(R::Inst("g.seg_cut".into(), vec![("x", x), ("b", b), ("pt", pt), ("J", jl), ("k", k2)]), vec![s(&pf), s(&nk)])).map(Some)
            }
            None => Err(format!("a cut label undecided at {}", self.print(&x))),
        }
    }

    /// `(p && a(o)) || r(o)`, p decided false: r (g.low_orn)
    fn low_orn(&mut self, lo: &Term) -> Result<Option<(Term, Seq)>, String> {
        let Some(o) = self.app(lo, "or", 2).map(|o| o.to_vec()) else { return Ok(None) };
        let Some(l) = self.app(&o[0], "and", 2).map(|l| l.to_vec()) else { return Ok(None) };
        let Some(pc) = self.lam(&l[0], &["o"], &[]) else { return Ok(None) };
        let Some((false, pf)) = self.decide(&pc) else { return Ok(None) };
        let al = self.lam(&l[1], &["o"], &["o"]).ok_or("a disjunct")?;
        let rl = self.lam(&o[1], &["o"], &["o"]).ok_or("a disjunct")?;
        self.low_by(mp(R::Inst("g.low_orn".into(), vec![("p", pc), ("a", al), ("r", rl)]), vec![s(&pf)])).map(Some)
    }
}

/// t (a body under `x9 o.`, x9 the bound variable `d` from its top) with
/// each `snd(x9)` x9 itself: None if x9 occurs otherwise
fn un_snd(g: &Gen, t: &Term, d: u32) -> Option<Term> {
    if let Some(a) = g.app(t, "snd", 1) {
        if matches!(a[0].node(), Node::BVar(i) if *i == d) {
            return Some(a[0].clone());
        }
    }
    match t.node() {
        Node::BVar(i) if *i == d => None,
        Node::App(s0, a) if !a.is_empty() => {
            let bs = &g.env.syms[*s0 as usize].binders;
            Some(t.with_args(a.iter().zip(bs).map(|(x, &n)| un_snd(g, x, d + n)).collect::<Option<_>>()?))
        }
        Node::Var(_, a) if !a.is_empty() => Some(t.with_args(a.iter().map(|x| un_snd(g, x, d)).collect::<Option<_>>()?)),
        _ => Some(t.clone()),
    }
}

/// The cut labels of the CFG's label graph (each label's leaves: a jump's
/// label, None a return): the structuring's joins and loop heads on it, and
/// the first label (crate::gimple::structure::label_cuts)
fn cut_labels(labels: &[u128], succ: &BTreeMap<u128, Vec<Option<u128>>>, entry: u128) -> Result<BTreeSet<u128>, String> {
    let s64: BTreeMap<u64, Vec<Option<u64>>> = labels.iter().map(|k| (*k as u64, succ.get(k).into_iter().flatten().map(|l| l.map(|x| x as u64)).collect())).collect();
    let cuts = crate::gimple::structure::label_cuts(&s64, entry as u64)?;
    Ok(cuts.into_iter().map(u128::from).collect())
}
