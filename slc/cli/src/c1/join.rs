//! Joins: where the paths of a branch meet again, the claim for the rest
//! is proven once and used on each path that arrives, so a function's
//! proof grows with its code rather than with its paths.
//!
//! The claims come from the spec's structure, not from the paths: where a
//! block of the spec ends (its head done, `x8 = ok(pair(W, Y), E)`: the
//! world W and the locals Y after it) at an address with two predecessors
//! or more, the claim is the rest's for every world and locals --
//! - the rest with the block's outcome ok(pair(w, y), E): the same program
//!   text for each path that ends the block, whatever its W and Y;
//! - the homes holding locals as those locals (`link_homes`, as at a
//!   loop's head: the code's form of a value and the spec's made equal by
//!   the facts), the others as they are;
//! - the frame the function's own, no registers (`tr.lv_fd`, `tr.pt_rs`
//!   on use);
//! - the facts every path arriving has (`shared_facts`), and the locals'
//!   invariant (a home's local a word of its width).
//! It is proven by walking on from the point, then used for each path
//! whose rest is its instance (its W and Y), by `tr.pt_hs` (the claim's
//! homes among the path's). Where an enclosing block ends at the same
//! point, the claim is the outer one's. A loop's rule is shared the same
//! way: its claim is for every locals and world (`loop_claims`). Nothing
//! is trusted here: a claim the walk cannot prove, or a path it does not
//! fit, only loses the sharing.

use super::rec::*;
use super::*;

/// a branch on the path: the facts and calls' results then (their
/// counts), the variables then (those made after are the branch's own)
#[derive(Clone, PartialEq)]
pub(super) struct Split {
    hyps: usize,
    facts: usize,
    mark: usize,
}

impl<'e> Gen<'e> {
    /// the split of a branch at st
    pub(super) fn split(&self, st: &St) -> Split {
        Split { hyps: st.hyps.len(), facts: st.facts.len(), mark: self.env.vars.len() }
    }

    /// the code's successors of the instruction at a
    pub(super) fn succs(&self, a: u128) -> Vec<u128> {
        let Some(i) = self.insns.get(&a) else { return Vec::new() };
        let a2 = (a + i.len) % P64;
        match i.row {
            // ret
            122 => Vec::new(),
            // jmp rel8
            125 => match nat(&i.fields) {
                Some(r) => vec![(a2 + if r & 0x80 != 0 { r + 0xffff_ffff_ffff_ff00 } else { r }) % P64],
                None => Vec::new(),
            },
            // jmp rel32
            124 => match nat(&i.fields) {
                Some(r) => vec![(a2 + if r & 0x8000_0000 != 0 { r + 0xffff_ffff_0000_0000 } else { r }) % P64],
                None => Vec::new(),
            },
            // jcc rel8, rel32
            127 | 128 => match self.jcc(a) {
                Ok((_, _, a3, tt, _)) => vec![a3, tt],
                Err(_) => vec![a2],
            },
            _ => vec![a2],
        }
    }

    /// the number of a's predecessors in the code
    fn preds_of(&mut self, a: u128) -> usize {
        if self.preds.is_none() {
            let mut m: BTreeMap<u128, usize> = BTreeMap::new();
            for &x in self.insns.keys() {
                for y in self.succs(x) {
                    *m.entry(y).or_default() += 1;
                }
            }
            self.preds = Some(m);
        }
        self.preds.as_ref().and_then(|m| m.get(&a).copied()).unwrap_or(0)
    }

    /// The point claim at st by a join's claim: one st is an instance of,

    /// the homes' map term `hst`: its entries in order (key, bytes, value)
    pub(super) fn home_entries(&self, hst: &Term) -> Option<Vec<(u128, u128, Term)>> {
        let mut out = Vec::new();
        let mut m = hst.clone();
        while let Some((parent, k, pv)) = upd_parts(self, &m) {
            let x = self.app(&pv, "pair", 2)?;
            out.push((nat(&k)?, nat(&x[0])?, x[1].clone()));
            m = parent;
        }
        self.app(&m, "empty", 0)?;
        out.reverse();
        Some(out)
    }
}

/// a statement claim: at `a` (its frame, loop, and the walk's breakpoints
/// and wrapper), over the locals that are no literal (`ys`: a variable per
/// such component of the locals' `ny`) and the world wv: the rest `q`, the
/// homes `hs`, the frame depth `ds`; `all ys wv. Y in univ(1) && .. -> wv
/// a world -> yt(ys) -> tr.lv(..)`
#[derive(Clone)]
pub(super) struct StmtClaim {
    a: u128,
    fr: u128,
    lp: Option<usize>,
    ctx: [Term; 4],
    wv: VarId,
    ys: Vec<(usize, VarId)>,
    ny: usize,
    q: Term,
    hs: Term,
    ds: Term,
    claim: Seq,
}

impl<'e> Gen<'e> {
    /// the rest's head a block's end: `x8 = ok(pair(W, Y), E)`, Y and E
    /// closed, W closed or the rest's start world x0 -- its W, Y, E
    fn stmt_end(&self, q: &Term) -> Option<(Term, Term, Term)> {
        let body = self.app(q, "mkprog", 1)?[0].clone();
        let e = self.app(&body, "ex", 1)?[0].clone();
        let x = self.app(&e, "and", 2)?.to_vec();
        let eq = self.app(&x[0], "eq", 2)?.to_vec();
        if !matches!(eq[0].node(), Node::BVar(0)) {
            return None;
        }
        let o = self.app(&eq[1], "ok", 2)?.to_vec();
        let pr = self.app(&o[0], "pair", 2)?.to_vec();
        let bf = self.env.binders_fn();
        let w_ok = matches!(pr[0].node(), Node::BVar(2)) || pr[0].loose_depth(&bf) == 0;
        (w_ok && pr[1].loose_depth(&bf) == 0 && o[1].loose_depth(&bf) == 0).then(|| (pr[0].clone(), pr[1].clone(), o[1].clone()))
    }

    /// the rest q with its block's end the outcome ok(pair(w, y), e)
    fn stmt_with(&self, q: &Term, w: &Term, y: &Term, e: &Term) -> Term {
        let body = &self.app(q, "mkprog", 1).unwrap()[0];
        let ex = &self.app(body, "ex", 1).unwrap()[0];
        let x = self.app(ex, "and", 2).unwrap();
        let eq = &x[0];
        let o = self.mk("ok", vec![self.mk("pair", vec![w.clone(), y.clone()]), e.clone()]);
        let eq2 = eq.with_args(vec![Term::bvar(0), o]);
        let ex2 = ex.with_args(vec![eq2, x[1].clone()]);
        q.with_args(vec![body.with_args(vec![ex2])])
    }

    /// The point claim at st by a statement claim (made here if none fits)
    pub(super) fn stmt_join(&mut self, st: &St) -> Result<Option<Seq>, String> {
        if self.lpg.is_some() || st.z.is_some() || st.no_join == Some(st.a) || self.preds_of(st.a) < 2 {
            return Ok(None);
        }
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        let q = self.qs[qi].clone();
        let Some((w0, y0, e0)) = self.stmt_end(&q) else { return Ok(None) };
        if !matches!(w0.node(), Node::BVar(2)) && self.expand(&w0) != self.expand(&st.w) {
            self.trace(|| format!("stmt at {:x}: the block's world not the point's", st.a));
            return Ok(None);
        }
        // (an enclosing block ending here too -- the rest's reductions reach
        // its end before the machine's next step: the claim there, the same
        // for the paths that end only that one)
        if self.stmt_outer(qi, &st.hyps)? {
            return Ok(None);
        }
        for i in 0..self.stmts.len() {
            if let Some(pf) = self.stmt_use(i, st, &q, &y0)? {
                return Ok(Some(pf));
            }
        }
        if self.stmt_fail.contains(&st.a) {
            return Ok(None);
        }
        let Some(i) = self.stmt_make(st, &q, &w0, &y0, &e0)? else {
            self.stmt_fail.insert(st.a);
            return Ok(None);
        };
        let pf = self.stmt_use(i, st, &q, &y0)?;
        if pf.is_none() {
            self.trace(|| format!("stmt at {:x}: its claim does not fit the path it was made from", st.a));
        }
        Ok(pf)
    }

    /// whether the rest qi's reductions, after its block's end, reach
    /// another block's end (no machine step between)
    fn stmt_outer(&mut self, qi: usize, hyps: &[(Term, Seq)]) -> Result<bool, String> {
        let picked = self.picked.borrow().clone();
        let mut cur = qi;
        let mut res = false;
        for n in 0..32 {
            if n > 0 && self.stmt_end(&self.qs[cur].clone()).is_some() {
                res = true;
                break;
            }
            match self.reduce(cur, hyps) {
                Ok(Some(Red::Q(j, _))) => cur = j,
                _ => break,
            }
        }
        *self.picked.borrow_mut() = picked;
        Ok(res)
    }

    /// an assumption of the claim c not in st's scope (a claim made within
    /// another's walk may rest on that one's)
    pub(super) fn out_of_scope(&self, st: &St, c: &Seq) -> Option<Term> {
        let mut scope: Vec<&Term> = self.ambient.iter().collect();
        let lp = st.lp.map(|l| &self.loops[l]);
        let seqs = [&st.hw, &st.hvu].into_iter().chain(st.hyps.iter().map(|h| &h.1)).chain(st.facts.iter()).chain(st.lfx.iter());
        let seqs = seqs.chain(lp.into_iter().flat_map(|l| [&l.ih, &l.cc, &l.ci]));
        for q in seqs.chain(self.hl.iter()).chain(self.lf0.iter()).chain(self.hcall.iter().flatten()).chain(self.htyp.iter().flatten()).chain(self.hio.iter().flatten()).chain(self.hus.iter()) {
            scope.extend(q.hyps().iter());
        }
        c.hyps().iter().find(|h| !scope.contains(h)).cloned()
    }

    /// the facts at st that every path reaching its point has, for a claim
    /// there over the locals (now y0), its terms `ts`: those before the
    /// path's first branch, not of its own values (made after that branch,
    /// but the claim's variables `vs`), nor of the walk's values in the
    /// locals (the claim's premise says what it knows of them), nor of
    /// values the claim does not mention
    pub(super) fn shared_facts(&self, st: &St, y0: &Term, vs: &[VarId], ts: &[&Term]) -> (Vec<(Term, Seq)>, Vec<Seq>, Vec<Seq>) {
        let mark = st.splits.first().map(|sp| sp.mark).unwrap_or(self.env.vars.len());
        let mut yvs = Vec::new();
        self.expand(y0).vars(&mut yvs);
        yvs.retain(|v| (*v as usize) >= self.vmark0);
        let mut tvs = vs.to_vec();
        for t in ts {
            self.expand(t).vars(&mut tvs);
        }
        let keep = |t: &Term| {
            let mut tv = Vec::new();
            t.vars(&mut tv);
            !tv.iter().any(|v| ((*v as usize) >= mark && !vs.contains(v)) || yvs.contains(v) || ((*v as usize) >= self.vmark0 && !tvs.contains(v)))
        };
        let (nh, nf) = st.splits.first().map(|sp| (sp.hyps, sp.facts)).unwrap_or((st.hyps.len(), st.facts.len()));
        let hyps = st.hyps[..nh.min(st.hyps.len())].iter().filter(|h| keep(&self.expand(&h.0))).cloned().collect();
        let facts = st.facts[..nf.min(st.facts.len())].iter().filter(|f| keep(f.concl())).cloned().collect();
        let lfx = st.lfx.iter().filter(|f| keep(f.concl())).cloned().collect();
        (hyps, facts, lfx)
    }

    /// the locals' components: `pair(a, pair(b, .. z))` as a, b, .. z
    fn locals_of(&self, y: &Term) -> Vec<Term> {
        let mut comps = Vec::new();
        let mut cur = y.clone();
        while let Some(pa) = self.app(&cur, "pair", 2).map(|x| x.to_vec()) {
            comps.push(pa[0].clone());
            cur = pa[1].clone();
        }
        comps.push(cur);
        comps
    }

    fn stmt_ctx(&self) -> [Term; 4] {
        [self.bkp.clone(), self.bka.clone(), self.wrap.clone(), self.kw.clone()]
    }

    /// a statement claim at st, the rest q ending its block with the locals y0
    fn stmt_make(&mut self, st: &St, q: &Term, w0: &Term, y0: &Term, e0: &Term) -> Result<Option<usize>, String> {
        let a = st.a;
        let n = self.fresh("");
        let wv = self.var(&format!("sw{n}"));
        // the locals: a variable for each that is no literal (a literal one
        // kept: its home, if any, holds the literal too)
        let comps = self.locals_of(y0);
        let mut ys = Vec::new();
        let mut gen = Vec::new();
        for (i, ci) in comps.iter().enumerate() {
            if nat(ci).is_some() {
                gen.push(ci.clone());
            } else {
                let v = self.var(&format!("sy{n}_{i}"));
                ys.push((i, Self::var_id(&v)));
                gen.push(v);
            }
        }
        let y_gen = gen.iter().rev().cloned().reduce(|acc, x| self.mk("pair", vec![x, acc])).ok_or("no locals")?;
        // (a home holding a local's value -- the same term, or one the facts
        // make equal -- holds its variable)
        self.set_lf(st)?;
        let mut hsm_y = BTreeMap::new();
        let mut yts = Vec::new();
        for (c, (nb, x)) in &st.hsm {
            let xc = self.canon(x);
            let mut v = x.clone();
            for &(i, vi) in &ys {
                let ci = &comps[i];
                let same = self.canon(ci) == xc || self.evp(&RP::Simp(true, vec![], vec![], false), &self.mk("eq", vec![x.clone(), ci.clone()]), &[]).is_ok();
                if same {
                    v = Term::var(vi, vec![]);
                    yts.push(self.mk("in", vec![v.clone(), self.mk("bits", vec![lit(8 * nb)])]));
                    break;
                }
            }
            hsm_y.insert(*c, (*nb, v));
        }
        let yt_t = yts.into_iter().reduce(|a, b| self.mk("and", vec![a, b])).unwrap_or_else(|| self.mk("true", vec![]));
        let hst_y = self.hs_term(&hsm_y);
        let q_gen = self.stmt_with(q, if matches!(w0.node(), Node::BVar(2)) { w0 } else { &wv }, &y_gen, e0);
        // (the values of the path's own: made after its first branch)
        let mark = st.splits.first().map(|sp| sp.mark).unwrap_or(self.env.vars.len());
        let wid = Self::var_id(&wv);
        let mut vids: Vec<VarId> = ys.iter().map(|x| x.1).collect();
        vids.push(wid);
        let own = |t: &Term| {
            let mut vs = Vec::new();
            t.vars(&mut vs);
            vs.iter().any(|v| (*v as usize) >= mark && !vids.contains(v))
        };
        if own(&self.expand(&q_gen)) || own(&self.expand(&hst_y)) {
            self.trace(|| format!("stmt at {:x}: a value of the path's own not abstracted", a));
            return Ok(None);
        }
        // the frame: the function's own (the least a path has here)
        let ds = match nat(&self.expand(&st.ds)) {
            Some(d) if self.fd > 0 && d >= self.fd => lit(self.fd),
            _ => st.ds.clone(),
        };
        // the facts every path here has; the claim's premises
        let (hyps, mut facts, mut lfx) = self.shared_facts(st, y0, &vids, &[&q_gen, &hst_y]);
        let univ = |g: &Gen, x: &Term| g.mk("in", vec![x.clone(), g.mk("univ", vec![lit(1)])]);
        // (the locals in the universe, and each variable)
        let hu_t = ys.iter().fold(univ(self, &y_gen), |acc, (_, v)| self.mk("and", vec![acc, univ(self, &Term::var(*v, vec![]))]));
        let hw_t = self.mk("and", vec![self.mk("in", vec![wv.clone(), self.mk("abi.World", vec![])]), univ(self, &wv)]);
        let hw = self.assume(&hw_t)?;
        let hu = self.assume(&hu_t)?;
        // (no local in a home: the invariant true, proven, not assumed --
        // an assumption of true would be every enclosing walk's too)
        let hy = if self.app(&yt_t, "true", 0).is_some() { self.evp(&RP::Taut(vec![]), &yt_t, &[])? } else { self.assume(&yt_t)? };
        let hvu = self.evp(&RP::Taut(vec![R::S(hw.clone())]), &univ(self, &wv), &[])?;
        facts.push(hy.clone());
        facts.push(hu.clone());
        lfx.push(hy.clone());
        lfx.push(hu.clone());
        let jq = self.new_q(self.canon(&q_gen));
        let stg = St {
            a,
            fr: st.fr,
            regs: Vec::new(),
            rs: self.mk("empty", vec![]),
            ds: ds.clone(),
            w: wv.clone(),
            hvu,
            hw,
            hsm: hsm_y,
            hst: hst_y.clone(),
            lp: st.lp,
            spec: Spec::Proc(jq),
            hyps,
            facts,
            lfx,
            bconds: Vec::new(),
            spent: Vec::new(),
            splits: Vec::new(),
            no_join: Some(a),
            z: None,
        };
        self.trace(|| format!("stmt at {:x}: its claim, for every world and locals", a));
        // (its universe facts its own: an enclosing walk's are not every
        // path's)
        let hus = std::mem::replace(&mut self.hus, vec![hu]);
        let pf = self.prove_kept(stg);
        self.hus = hus;
        let pf = match pf {
            Ok(pf) => pf,
            Err(e) => {
                self.trace(|| format!("stmt at {:x}: its claim not proven ({}), the paths on their own", a, e.replace('\n', " / ")));
                return Ok(None);
            }
        };
        let claim = match self.close(pf, &[hu_t, hw_t, yt_t], &vids) {
            Ok(c) => c,
            Err(e) => {
                self.trace(|| format!("stmt at {:x}: its claim not closed ({})", a, e));
                return Ok(None);
            }
        };
        let ctx = self.stmt_ctx();
        self.stmts.push(StmtClaim { a, fr: st.fr, lp: st.lp, ctx, wv: wid, ys, ny: comps.len(), q: q_gen, hs: hst_y, ds, claim });
        Ok(Some(self.stmts.len() - 1))
    }

    /// The point claim at st by the statement claim i, if st's rest q (its
    /// block ending with the world w0, the locals y0) is its instance
    fn stmt_use(&mut self, i: usize, st: &St, q: &Term, y0: &Term) -> Result<Option<Seq>, String> {
        let c = self.stmts[i].clone();
        if c.a != st.a || c.fr != st.fr || c.lp != st.lp || c.ctx != self.stmt_ctx() {
            return Ok(None);
        }
        let comps = self.locals_of(y0);
        if comps.len() != c.ny {
            return Ok(None);
        }
        let vals: Vec<Term> = c.ys.iter().map(|(i, _)| comps[*i].clone()).collect();
        let bf = self.env.binders_fn();
        let inst = |x: &Term| c.ys.iter().zip(vals.iter()).fold(x.subst_var(c.wv, &st.w, &bf), |t, ((_, v), val)| t.subst_var(*v, val, &bf));
        let (q1, q2) = (self.expand(&inst(&c.q)), self.expand(q));
        if q1 != q2 {
            self.trace(|| {
                // (where: the first subterms that differ)
                fn diff(x: &Term, y: &Term, d: usize, env: &Env) -> (Term, Term, usize) {
                    match (x.node(), y.node()) {
                        (Node::App(f, a), Node::App(h, b)) if f == h && a.len() == b.len() => match (0..a.len()).find(|&k| a[k] != b[k]) {
                            Some(k) => diff(&a[k], &b[k], d + env.syms[*f as usize].binders[k] as usize, env),
                            None => (x.clone(), y.clone(), d),
                        },
                        _ => (x.clone(), y.clone(), d),
                    }
                }
                let (d1, d2, d) = diff(&q1, &q2, 0, self.env);
                format!("stmt at {:x}: not an instance of claim {} (the rest: {} / {})", st.a, i, self.lambda(d, &d1), self.lambda(d, &d2))
            });
            return Ok(None);
        }
        let hs1 = inst(&c.hs);
        drop(bf);
        // (the frame: the claim's at most st's)
        let (dc, dp) = (nat(&self.expand(&c.ds)), nat(&self.expand(&st.ds)));
        let fd_ok = self.expand(&c.ds) == self.expand(&st.ds) || matches!((dc, dp), (Some(x), Some(y)) if 0 < x && x <= y && y <= 65536);
        if !fd_ok {
            self.trace(|| format!("stmt at {:x}: not an instance of claim {} (the frame)", st.a, i));
            return Ok(None);
        }
        // (the claim's own assumptions in st's scope)
        if let Some(h) = self.out_of_scope(st, &c.claim) {
            self.trace(|| format!("stmt at {:x}: its claim rests on {}, not here", st.a, self.print(&h)));
            return Ok(None);
        }
        let res = (|| -> Result<Seq, String> {
            let mut args: Vec<RA> = vals.iter().map(t).collect();
            args.push(t(&st.w));
            args.extend([simp_lw([&st.hvu].into_iter().chain(self.hus.iter()).chain(st.lfx.iter()).map(|x| R::S(x.clone())).collect()), s(&st.hw), simp_l()]);
            let c0 = self.run(&mp(R::S(c.claim.clone()), args), &[])?;
            // (st's homes: the claim's, and more)
            let empty = self.mk("empty", vec![]);
            let mut sub_pf = mpf("tr.hsub_empty", vec![t(&st.hst)]);
            let mut fm = empty.clone();
            for (k, nb, x) in self.home_entries(&hs1).ok_or("stmt: the claim's homes")? {
                let v = self.mk("pair", vec![lit(nb), x.clone()]);
                sub_pf = mpf("tr.hsub_upd", vec![t(&st.hst), t(&fm), t(&lit(k)), t(&v), p(sub_pf), simp_l(), simp_l()]);
                fm = self.upd(&fm, k, nb, &x);
            }
            let pcl = self.p(&st.spec);
            let base = |g: &Gen| vec![t(&g.s.clone()), t(&g.v.clone()), t(&g.base.clone()), t(&g.code.clone()), t(&lit(st.fr)), t(&lit(st.a))];
            let mut a1 = base(self);
            a1.extend([t(&hs1), t(&st.hst), t(&c.ds), t(&empty), t(&pcl), t(&st.w), p(sub_pf), s(&c0)]);
            let c1 = self.run(&mpf("tr.pt_hs", a1), &[])?;
            let mut a2 = base(self);
            a2.extend([t(&st.hst), t(&c.ds), t(&st.rs), t(&pcl), t(&st.w), s(&c1)]);
            let c2 = self.run(&mpf("tr.pt_rs", a2), &[])?;
            if self.expand(&c.ds) == self.expand(&st.ds) {
                return Ok(c2);
            }
            let mut a3 = base(self);
            a3.extend([t(&st.hst), t(&st.ds), t(&c.ds), t(&st.rs), t(&pcl), t(&st.w), simp0(), simp0(), arith(vec![]), arith(vec![]), arith(vec![]), s(&c2)]);
            self.run(&mpf("tr.lv_fd", a3), &[])
        })();
        match res {
            Ok(pf) => {
                self.trace(|| format!("stmt at {:x}: by claim {}", st.a, i));
                Ok(Some(pf))
            }
            Err(e) => {
                self.trace(|| format!("stmt at {:x}: claim {} not used ({})", st.a, i, e.replace('\n', " / ")));
                Ok(None)
            }
        }
    }
}
