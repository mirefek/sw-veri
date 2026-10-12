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
    let t0 = std::time::Instant::now();
    let _rep = super::prof::Rep(name.to_string());
    let mut g = Gen::new(env, BTreeMap::new(), empty.clone(), empty, name, name, Vec::new())?;
    let r = g.refines(low, high);
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

    /// the CFG side's comparison c and the structured side's cu (both
    /// closed) of the same operation, an operand not the same term but of
    /// the same normal form: the CFG side's rewritten to the structured
    /// side's (N's equation, each occurrence at once)
    fn cond_match_step(&mut self, lo: &Term, c: &Term, cu: &Term) -> Result<Option<(Term, Seq)>, String> {
        let strip = |g: &Gen, t: &Term| {
            let mut t = t.clone();
            while let Some(x) = g.app(&t, "not", 1).map(|x| x[0].clone()) {
                t = x;
            }
            t
        };
        let (c0, u0) = (strip(self, c), strip(self, cu));
        let (Node::App(f1, a1), Node::App(f2, a2)) = (c0.node(), u0.node()) else { return Ok(None) };
        if f1 != f2 || a1.len() != a2.len() {
            return Ok(None);
        }
        for (al, au) in a1.to_vec().into_iter().zip(a2.to_vec()) {
            if self.canon(&al) == self.canon(&au) {
                continue;
            }
            let Some(pf) = self.eq_nf_seq(&al, &au)? else { return Ok(None) };
            let ab = self.abstract_(lo, &al, 0);
            let l = self.lam(&ab, &["o", "x"], &["o", "x"]).ok_or("a condition's context")?;
            return self.low_by(mp(R::Inst("g.low_rw".into(), vec![("l", l), ("a", al), ("b", au)]), vec![s(&pf)])).map(Some);
        }
        Ok(None)
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
            return self.low_by(R::Inst("g.low_intro".into(), vec![("l", lo.clone())])).map(Some);
        };
        let kl = self.lam(&k, &lctx, &["x8", "o"]).ok_or("the lower block's rest")?;
        if let Some(x) = self.app(&a, "letin", 2).map(|x| x.to_vec()) {
            let e = self.lam(&x[0], &lctx, &[]).ok_or("a let's value reads the block")?;
            // (its projections taken first)
            if let Some(r) = self.proj_step_in(lo, &e)? {
                return Ok(Some(r));
            }
            // (its value in the normal form first, as the structured side's)
            let (n, pf) = self.norm(&e)?;
            if let Some(pf) = pf {
                let ab = self.abstract_(lo, &e, 0);
                let l = self.lam(&ab, &["o", "x"], &["o", "x"]).ok_or("a let's context")?;
                return self.low_by(mp(R::Inst("g.low_rw".into(), vec![("l", l), ("a", e), ("b", n)]), vec![s(&pf)])).map(Some);
            }
            // (named, as the structured side's values: N then sees the same
            // terms on both)
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
                // (not the same: the CFG side's operands of the same normal
                // form as the structured side's made its)
                if way.is_none() {
                    if let Some((lo2, imp)) = self.cond_match_step(lo, &cl, &cu2)? {
                        return self.after_low(lo, lo2, imp, qi, w);
                    }
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

    /// The CFG going on at x, the structured side at qi: x's point (found in
    /// the first pass; in the second, `inv(x, q)` and g.ref_jump)
    fn leaf_jump(&mut self, lo: &Term, x: &Term, qi: usize, w: &Term) -> Result<Seq, String> {
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
        let r = self.qs[qi].clone();
        let g = self.gref.as_ref().ok_or("the CFG going on outside its loop")?;
        let (discover, cur, inv) = (g.discover, g.cur, g.inv.clone());
        if discover {
            let xs = self.app(x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| q.to_vec())).ok_or("a CFG state not a world, a label and locals")?;
            let k = nat(&xs[0]).ok_or("a CFG state's label not a literal")?;
            let comps = self.locals_of(&xs[1]);
            self.point_at(k, &comps, &r)?;
            self.gref.as_mut().unwrap().edges.insert((cur, k));
            self.trace(|| format!("ref: point at label {} (from {})", k, cur));
            let goal = self.mk("g.ref", vec![lo.clone(), r, w.clone()]);
            let fls = self.mk("false", vec![]);
            let h = self.assume(&fls)?;
            return self.run(&mp(R::Inst("g.efq".into(), vec![("a", goal)]), vec![s(&h)]), &[]);
        }
        let ip = self.inv_at(x, &r)?;
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

/// The CFG's loop being walked: its points (found in a first pass), the
/// labels' ways on, the locals' number; the rule's parameters
pub(super) struct GRef {
    m: usize,
    points: Vec<GPoint>,
    edges: BTreeSet<(u128, u128)>,
    discover: bool,
    inv: Term,
    rank: Term,
    /// the loop's body (`l o. b`)
    b: Term,
    /// the label of the point walked
    cur: u128,
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
        let mut shape = Vec::new();
        for j in 0..m {
            if nat(&ce[j]).is_some() || self.app(&ce[j], "empty", 0).is_some() {
                shape.push(Sh::Lit(ce[j].clone()));
            } else if let Some(i) = (0..j).find(|&i| ce[i] == ce[j] && shape[i] == Sh::Free) {
                shape.push(Sh::Same(i));
            } else {
                shape.push(Sh::Free);
            }
        }
        let n = self.fresh("gy");
        let yv = self.var(&n);
        let mut t = self.expand(r);
        let mut order: Vec<usize> = (0..m).filter(|&j| shape[j] == Sh::Free).collect();
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

    /// the points' relation inv (`l q. ..`) and rank (`l. ..`)
    fn gref_params(&mut self) -> (Term, Term) {
        let g = self.gref.as_ref().expect("the points");
        let (m, points, edges) = (g.m, g.points.clone(), g.edges.clone());
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
        let inv_l = self.abs(&inv, &[Self::var_id(&lv), Self::var_id(&qv)]);
        // (the rank: the longest way on, the labels' ways acyclic)
        let labels: BTreeSet<u128> = points.iter().map(|p| p.label).collect();
        let mut rank: BTreeMap<u128, u128> = BTreeMap::new();
        for _ in 0..=labels.len() {
            for &k in &labels {
                let r = edges.iter().filter(|e| e.0 == k).map(|e| rank.get(&e.1).copied().unwrap_or(0) + 1).max().unwrap_or(0);
                rank.insert(k, r);
            }
        }
        let mut table = self.mk("empty", vec![]);
        for (k, r) in &rank {
            table = self.mk("fn_update", vec![table, lit(*k), lit(*r)]);
        }
        let rk = self.mk("app", vec![table, self.mk("fst", vec![self.mk("snd", vec![lv.clone()])])]);
        let rank_l = self.abs(&rk, &[Self::var_id(&lv)]);
        (inv_l, rank_l)
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
        if !g.discover {
            return Err(format!("label {}: a point not found in the first pass", k));
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
    /// The CFG's loop (lo = `ex x8. while_rel(l0, true, b, tr, x8) && k(x8,
    /// o)`), the structured side's program qs[qi] from w: by g.cfg_ref, its
    /// points found in a first pass (the walks' proofs set aside), proven
    /// in a second
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
        self.gref = Some(GRef { m: comps.len(), points: Vec::new(), edges: BTreeSet::new(), discover: true, inv: fls.clone(), rank: fls, b: b.clone(), cur: k_e });
        self.point_at(k_e, &comps, &q0)?;
        // the first pass: each point's walk, its points found
        let mut i = 0;
        while i < self.gref.as_ref().unwrap().points.len() {
            let (inv, rank) = self.gref_params();
            {
                let g = self.gref.as_mut().unwrap();
                g.inv = inv.clone();
                g.rank = rank.clone();
            }
            let (_, stmt) = self.inst("g.cfg_ref", &[("b", b.clone()), ("tr", tr.clone()), ("k", kk.clone()), ("inv", inv), ("m", rank)])?;
            let (prems, _) = self.imps(&stmt);
            let gl = self.claim_lam(&prems[0])?;
            let prem = self.pt_prem(&gl, i)?.1;
            self.gref.as_mut().unwrap().cur = self.gref.as_ref().unwrap().points[i].label;
            self.sub_walk(&prem, &["pw", "py"])?;
            i += 1;
        }
        self.trace(|| format!("ref: {} points", self.gref.as_ref().unwrap().points.len()));
        // the second: the rule's premises, point by point
        let (inv, rank) = self.gref_params();
        {
            let g = self.gref.as_mut().unwrap();
            g.discover = false;
            g.inv = inv.clone();
            g.rank = rank.clone();
        }
        let (rr, stmt) = self.inst("g.cfg_ref", &[("b", b.clone()), ("tr", tr.clone()), ("k", kk.clone()), ("inv", inv.clone()), ("m", rank)])?;
        let (prems, _) = self.imps(&stmt);
        let ps = self.combine(&prems[0], 0)?;
        let pd = self.combine(&prems[1], 1)?;
        let pm = self.combine(&prems[2], 2)?;
        let main = self.run(&mp(rr, vec![s(&ps), s(&pd), s(&pm)]), &[])?;
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
    /// the walks, 1 the ways on, 2 the rank), by g.inv_or
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
                0 => self.sub_walk(&prem_i, &["pw", "py"])?,
                1 => self.ways_on(&prem_i)?,
                _ => self.rank_ok(&prem_i)?,
            };
            let pt = self.run(&mp(r, vec![s(&pf)]), &[])?;
            acc = self.run(&mp(R::Inst("g.inv_or".into(), vec![("G", gl.clone()), ("A", disj[i].0.clone()), ("B", disj[i].1.clone())]), vec![s(&pt), s(&acc)]), &[])?;
        }
        Ok(acc)
    }

    /// a point's rank a number: `all w y. m(..) in omega`
    fn rank_ok(&mut self, prem: &Term) -> Result<Seq, String> {
        let (wv, yv) = (self.var("mw"), self.var("my"));
        let b = self.app(prem, "all", 1).ok_or("the rank's premise")?[0].clone().instantiate_params(std::slice::from_ref(&wv), &self.env.binders_fn());
        let b = self.app(&b, "all", 1).ok_or("the rank's premise")?[0].clone().instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
        let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &b, &[])?;
        self.close(pf, &[], &[Self::var_id(&wv), Self::var_id(&yv)])
    }

    /// a point's block going on: to a related state, of a lower rank (the
    /// CFG's side alone, g.post_use)
    fn ways_on(&mut self, prem: &Term) -> Result<Seq, String> {
        let (wv, yv) = (self.var("dw"), self.var("dy"));
        let b = self.app(prem, "all", 1).ok_or("the ways' premise")?[0].clone().instantiate_params(std::slice::from_ref(&wv), &self.env.binders_fn());
        let b = self.app(&b, "all", 1).ok_or("the ways' premise")?[0].clone().instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
        // all l2. b(L, ok(l2, empty)) -> Q(l2)
        let inner = self.app(&b, "all", 1).ok_or("the ways' claim")?[0].clone();
        let (hs, ql) = self.imps(&inner);
        let bl = self.app(&hs[0], "bind_rel", 5).map(|_| ()).map(|_| hs[0].clone());
        let _ = bl;
        let bb = self.gref.as_ref().unwrap().b.clone();
        let l1 = self.ways_state(&hs[0])?;
        let bx = bb.instantiate_params(&[l1.clone(), Term::bvar(0)], &self.env.binders_fn());
        let (r, st) = self.inst("g.post_use", &[("b", bx), ("Q", ql)])?;
        let (ps, _) = self.imps(&st);
        let gp = self.app(&ps[0], "g.post", 2).ok_or("g.post_use's premise")?.to_vec();
        let pf = self.post(&gp[0], &gp[1], &l1)?;
        let r1 = self.run(&mp(r, vec![s(&pf)]), &[])?;
        self.close(r1, &[], &[Self::var_id(&wv), Self::var_id(&yv)])
    }

    /// `b(L, ok(l2, empty))` (under l2): L
    fn ways_state(&self, h: &Term) -> Result<Term, String> {
        // (the loop's body applied: its first argument, the state)
        let bb = self.gref.as_ref().unwrap().b.clone();
        let _ = bb;
        let mut found = None;
        fn walk_t(g: &Gen, t: &Term, out: &mut Option<Term>) {
            if out.is_some() {
                return;
            }
            if let Some(x) = g.app(t, "pair", 2) {
                if g.app(&x[1], "pair", 2).is_some_and(|y| nat(&y[0]).is_some()) && x[0].loose_depth(&g.env.binders_fn()) == 0 && t.loose_depth(&g.env.binders_fn()) == 0 {
                    *out = Some(t.clone());
                    return;
                }
            }
            if let Node::App(_, a) = t.node() {
                for y in a.iter() {
                    walk_t(g, y, out);
                }
            }
        }
        walk_t(self, h, &mut found);
        found.ok_or_else(|| "the ways' state".into())
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

    /// the leaf's p(e): going on at x related, of a lower rank; leaving
    fn post_leaf(&mut self, e: &Term, pp: &Term, l1: &Term) -> Result<Seq, String> {
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
        let o = self.app(e, "ok", 2).ok_or("an iteration's outcome")?.to_vec();
        let x = o[0].clone();
        let xs = self.app(&x, "pair", 2).and_then(|p| self.app(&p[1], "pair", 2).map(|q| q.to_vec())).ok_or("a CFG state")?;
        let k = nat(&xs[0]).ok_or("a CFG state's label")?;
        let comps = self.locals_of(&xs[1]);
        // (a point of the label and the locals' shape: its program there)
        let shape = self.point_of(k, &comps, &self.mk("empty", vec![]))?.shape;
        let i = self.gref.as_ref().unwrap().points.iter().position(|p| p.label == k && p.shape == shape).ok_or_else(|| format!("label {}: no point of the locals' shape", k))?;
        let tmpl = self.gref.as_ref().unwrap().points[i].tmpl.clone();
        let q = tmpl.instantiate_params(std::slice::from_ref(&xs[1]), &self.env.binders_fn());
        let ip = self.inv_at_pt(&x, &q, i)?;
        let (inv, rank) = {
            let g = self.gref.as_ref().unwrap();
            (g.inv.clone(), g.rank.clone())
        };
        self.run(&mp(R::Inst("g.post_leaf".into(), vec![("inv", inv), ("m", rank)]), vec![t(l1), t(&x), t(&q), s(&ip), simp0()]), &[])
    }
}
