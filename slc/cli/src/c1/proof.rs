//! The point claims: their proofs at each address, by the spec's
//! reductions, the instructions' rules, branches, calls and loops.

use super::rec::*;
use super::*;

/// the context a point's recipes evaluate in (restored after a recursion)
struct Ctx {
    fr: u128,
    w: Term,
    hvu: Option<Seq>,
    lf: Vec<Seq>,
}

impl<'e> Gen<'e> {
    fn save(&self) -> Ctx {
        Ctx { fr: self.fr, w: self.w.clone(), hvu: self.hvu.clone(), lf: self.lf.clone() }
    }

    fn restore(&mut self, c: Ctx) {
        self.fr = c.fr;
        self.w = c.w;
        self.hvu = c.hvu;
        self.lf = c.lf;
    }

    /// the point claim at st2 proven, the context kept
    pub(super) fn prove_kept(&mut self, st2: St) -> Result<Seq, String> {
        let c = self.save();
        let r = self.prove(st2);
        self.restore(c);
        r
    }

    /// The spec's store at the head of `st`'s rest, the machine storing n
    /// bytes at `addr`: its definedness fact, the stored value, the state
    /// after (its world the one written), the reduction `tr.red(WRAP(q), w,
    /// WRAP(q2), w2)`'s proof, the address
    pub(super) fn spec_store(&mut self, st: &St, addr: &Term, n: u128) -> Result<(Seq, Term, St, R, Term), String> {
        let (hc, v, st2, red, sa, _) = self.spec_store_x(st, Some(addr), Some(n))?;
        Ok((hc, v, st2, red, sa))
    }

    /// the same, the machine's address and size not known yet (any): also
    /// the store
    pub(super) fn spec_store_x(&mut self, st: &St, addr: Option<&Term>, n: Option<u128>) -> Result<(Seq, Term, St, R, Term, StoreOp), String> {
        let Spec::Proc(qi) = st.spec else { return Err(format!("{:x}: a store after the procedure's result", st.a)) };
        let q = self.qs[qi].clone();
        let badm = format!("{:x}: a store the spec does not make here (its rest: {})", st.a, self.print(&q));
        let bad = || badm.clone();
        let body = self.app(&q, "mkprog", 1).ok_or_else(bad)?[0].clone();
        let ex = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())).ok_or_else(bad)?;
        let (a, k) = (ex[0].clone(), ex[1].clone());
        let x = self.app(&a, "bind_rel", 5).ok_or_else(bad)?.to_vec();
        let so = self.store_op(&x[0])?.ok_or_else(bad)?;
        let n = n.unwrap_or(so.n);
        if so.n != n {
            return Err(format!("{:x}: the machine stores {} bytes, the spec {}", st.a, n, so.n));
        }
        let hc = self.hyp_find(&st.hyps, &so.cond).map(|h| h.1.clone()).ok_or_else(bad)?;
        if let Some(addr) = addr {
            if self.canon(&so.addr) != self.canon(addr) && !(self.eval_lit(&so.addr).is_some() && self.eval_lit(&so.addr) == self.eval_lit(addr)) {
                return Err(format!("{:x}: the machine stores at {}, the spec at {}", st.a, self.print(addr), self.print(&so.addr)));
            }
        }
        let ctx = ["x0", "x1", "x8"];
        let kl = self.lam(&k, &ctx, &["x8", "x1"]).ok_or("a block's rest reads the world")?;
        let c5 = ["x0", "x1", "x8", "x9", "x10"];
        let al = self.lam(&x[2], &c5, &["x9", "x10", "x8"]).ok_or("a store's continuation reads the world before it")?;
        let xl = self.lam(&x[3], &c5, &["x9", "x10", "x8"]).ok_or("a store's handler reads the world before it")?;
        let dl = self.lam(&x[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("a store's handler reads the world before it")?;
        // the world after it (a value: the values read from it come after it)
        let wn2 = self.fresh("W");
        let w2 = self.var(&wn2);
        let w = st.w.clone();
        let vm = self.mk("app", vec![w.clone(), Term::bytes(b"vm")]);
        let bytes = self.mk("app", vec![vm.clone(), Term::bytes(b"bytes")]);
        let stored = self.mk("x86_64_linux.store_le", vec![bytes, so.addr.clone(), lit(n), so.v.clone()]);
        let w2term = self.mk("fn_update", vec![w.clone(), Term::bytes(b"vm"), self.mk("fn_update", vec![vm, Term::bytes(b"bytes"), stored])]);
        self.push_val(Self::var_id(&w2), w2term);
        let hw2 = self.run(
            &R::Apply(Box::new(f("tr.world_store")), vec![t(&w), t(&so.addr), t(&lit(n)), t(&so.v), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]), simp_l()]),
            &[],
        )?;
        let w2u = self.mk("in", vec![w2.clone(), self.mk("univ", vec![lit(1)])]);
        let hv2 = self.evp(&RP::Taut(vec![R::S(hw2.clone())]), &w2u, &[])?;
        // the store's run: ok, to the world after
        let empty = self.mk("empty", vec![]);
        let st8ok = match &so.data {
            Some(d) => mpf(
                "tr.stz_at_ok",
                vec![
                    t(&w),
                    t(&so.p),
                    t(&so.off),
                    t(d),
                    t(&so.addr),
                    t(&lit(n)),
                    taut(vec![R::S(st.hw.clone())]),
                    s(&st.hvu),
                    simp_l(),
                    simp_l(),
                    p(self.zeros_proof(d)?),
                    simp_l(),
                    arith(vec![]),
                    s(&hc),
                ],
            ),
            None => mpf(
                &format!("tr.st{}_at_ok", 8 * n),
                vec![t(&w), t(&so.p), t(&so.off), t(&so.v), t(&so.addr), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), simp_l(), simp_l(), simp_l(), simp_l(), s(&hc)],
            ),
        };
        let okp = match &so.helper {
            None => p(st8ok),
            Some(fname) => {
                let (okl, _) = self.inst("tr.call1w_ok", &[("op", so.inner.clone()), ("r", empty.clone())])?;
                RA::P(RP::Defs(Box::new(RP::Mp(okl, vec![t(&w), t(&w2), s(&st.hvu), s(&hv2), p(st8ok)])), vec![fname.clone()]))
            }
        };
        let (j, inst) = self.by(qi, "tr.qs_opw", &[("op", x[0].clone()), ("r", empty), ("a", al), ("xx", xl), ("dd", dl), ("k", kl)])?;
        let qred = mp(inst, vec![t(&w), t(&w2), s(&st.hvu), okp]);
        let wredw = R::Inst("tr.wredw".into(), vec![("w", w.clone()), ("w2", w2.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone()), ("kw", self.kw3())]);
        // (evaluated here: its literal facts are this point's)
        let red = R::S(self.run(&mp(wredw, vec![s(&st.hvu), p(qred)]), &[])?);
        let mut st2 = st.clone();
        st2.w = w2;
        st2.hvu = hv2;
        st2.hw = hw2;
        st2.spec = Spec::Proc(j);
        Ok((hc, so.v.clone(), st2, red, so.addr.clone(), so))
    }

    /// `tr.wred` at st, from the rest qi to j
    fn wred(&self, st: &St, qi: usize, j: usize) -> R {
        R::Inst(
            "tr.wred".into(),
            vec![
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("a", lit(st.a)),
                ("hs", st.hst.clone()),
                ("ds", st.ds.clone()),
                ("rs", st.rs.clone()),
                ("w", st.w.clone()),
                ("q", self.qs[qi].clone()),
                ("q2", self.qs[j].clone()),
                ("kw", self.kw3()),
            ],
        )
    }

    /// A proof that the rest `qi` raises from W (`x1 = exc(W, empty)` at its
    /// end): the reductions to it, backwards.
    fn raise_chain(&mut self, qi: usize) -> Result<Seq, String> {
        let mut cur = qi;
        let mut steps: Vec<R> = Vec::new();
        // (the world compared expanded: a lemma's instance holds it so)
        let vw = self.expand(&self.vw);
        let exc_end = |g: &Gen, q: &Term| {
            g.app(q, "mkprog", 1).and_then(|b| g.app(&b[0], "eq", 2).map(|x| x.to_vec())).map_or(false, |x| {
                matches!(x[0].node(), Node::BVar(0)) && g.app(&x[1], "exc", 2).map_or(false, |e| g.expand(&e[0]) == vw && g.app(&e[1], "empty", 0).is_some())
            })
        };
        let mut n = 0;
        while !exc_end(self, &self.qs[cur].clone()) {
            n += 1;
            if n > 10000 {
                return Err(format!("a raise that does not end: {}", self.print(&self.qs[cur])));
            }
            match self.reduce(cur, &[])? {
                Some(Red::Q(j, r)) => {
                    steps.push(r);
                    cur = j;
                }
                _ => return Err(format!("a raise that does not reach the result: {}", self.print(&self.qs[cur]))),
            }
        }
        let w = self.w.clone();
        let empty = self.mk("empty", vec![]);
        let mut r = self.run(&mpf("tr.q_exc_runs", vec![t(&w), t(&self.vw), t(&empty), p(self.hv_r()), p(self.hvu0_r()), simp0()]), &[])?;
        let ex = self.mk("exc", vec![self.vw.clone(), empty]);
        for st in steps.into_iter().rev() {
            r = self.run(&mp(st, vec![t(&ex), s(&r)]), &[])?;
        }
        Ok(r)
    }

    fn hv_r(&self) -> R {
        R::S(self.hvu.clone().expect("a point's world"))
    }

    fn hvu0_r(&self) -> R {
        R::S(self.hvu0.clone().expect("the entry's world"))
    }

    /// `tr.wsplit` at st over cond: the raise u when not, the claim d when
    fn wsplit(&mut self, st: &St, qi: usize, cond: &Term, u: Seq, d: Seq) -> Result<Seq, String> {
        let inst = R::Inst(
            "tr.wsplit".into(),
            vec![
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("a", lit(st.a)),
                ("hs", st.hst.clone()),
                ("ds", st.ds.clone()),
                ("rs", st.rs.clone()),
                ("w", st.w.clone()),
                ("q", self.qs[qi].clone()),
                ("kw", self.kw3()),
                ("c", cond.clone()),
            ],
        );
        let hw0 = self.hw0.clone().unwrap();
        self.run(&mp(inst, vec![t(&self.vw.clone()), taut(vec![R::S(hw0)]), p(self.hvu0_r()), s(&u), s(&d)]), &[])
    }

    /// the raise when `cond` fails: `!cond -> runs(Q, w, exc(W, empty))`
    fn raise_when_not(&mut self, cond: &Term, ub: &(usize, R)) -> Result<Seq, String> {
        let nc = self.mk("not", vec![cond.clone()]);
        let hn = self.assume(&nc)?;
        let chain = self.raise_chain(ub.0)?;
        let ex = self.mk("exc", vec![self.vw.clone(), self.mk("empty", vec![])]);
        let u = self.run(&mp(ub.1.clone(), vec![t(&ex), s(&chain)]), &[("HN", hn)])?;
        self.close(u, &[nc], &[])
    }

    /// The proof of the point claim at `st`.
    pub(super) fn prove(&mut self, st: St) -> Result<Seq, String> {
        // (a join's own claim: not joined at its address, joins after it)
        let mut st = st;
        if st.no_join.is_some_and(|j| j != st.a) {
            st.no_join = None;
        }
        self.trace(|| {
            let q = match &st.spec {
                Spec::Proc(i) => format!("q{}: {}", i, Printer::new(self.env).short(&self.qs[*i])),
                Spec::Ret(..) => "ret".into(),
            };
            format!("point {:x} spec {}", st.a, q)
        });
        self.fr = st.fr;
        self.w = st.w.clone();
        self.hvu = Some(st.hvu.clone());
        self.set_lf(&st)?;
        if let Some(pf) = self.loop_point(&st)? {
            return Ok(pf);
        }
        // (in a zero-initialization: the machine's stores only, the spec's made)
        if st.z.is_some() {
            return self.insn(st);
        }
        if let Spec::Proc(qi) = st.spec {
            // (the branch conditions spent: not to choose between an `if`'s
            // alternatives)
            *self.spent_now.borrow_mut() = st.spent.iter().map(|&i| self.expand(&st.hyps[i].0)).collect();
            self.picked.borrow_mut().clear();
            match self.reduce(qi, &st.hyps)? {
                Some(Red::Q(j, r)) => {
                    let rs = self.run(&r, &[])?;
                    let mut st2 = st.clone();
                    st2.spec = Spec::Proc(j);
                    // (a branch condition that decided an `if`: spent)
                    let used = std::mem::take(&mut *self.picked.borrow_mut());
                    for &i in &st.bconds {
                        if !st2.spent.contains(&i) && used.contains(&self.expand(&st.hyps[i].0)) {
                            st2.spent.push(i);
                        }
                    }
                    let rest = self.prove_kept(st2)?;
                    let wr = self.wred(&st, qi, j);
                    return self.run(&mp(wr, vec![s(&rs), s(&rest)]), &[]);
                }
                Some(Red::Ret(val)) => {
                    let body = self.kw.instantiate_params(&[Term::bvar(1), val.clone(), Term::bvar(0)], &self.env.binders_fn());
                    let pr = self.mk("mkprog", vec![body]);
                    let mut st2 = st.clone();
                    st2.spec = Spec::Ret(val.clone(), pr);
                    let rest = self.prove_kept(st2)?;
                    let inst = R::Inst(
                        "tr.wret".into(),
                        vec![
                            ("s", self.s.clone()),
                            ("v", self.v.clone()),
                            ("base", self.base.clone()),
                            ("code", self.code.clone()),
                            ("fr", lit(st.fr)),
                            ("a", lit(st.a)),
                            ("hs", st.hst.clone()),
                            ("ds", st.ds.clone()),
                            ("rs", st.rs.clone()),
                            ("w", st.w.clone()),
                            ("val", val),
                            ("kw", self.kw3()),
                        ],
                    );
                    return self.run(&mp(inst, vec![simpw(vec![R::S(st.hvu.clone())]), s(&rest)]), &[]);
                }
                Some(Red::Split { cond, ok, ub }) => {
                    self.trace(|| format!("split at {:x} on {}", st.a, self.print(&cond)));
                    let u = self.raise_when_not(&cond, &ub)?;
                    // defined: on with the condition
                    let hc = self.assume(&cond)?;
                    let okr = self.run(&ok.1, &[("HC", hc.clone())])?;
                    let mut st2 = st.clone();
                    st2.spec = Spec::Proc(ok.0);
                    st2.hyps.push((cond.clone(), hc));
                    let rest = self.prove_kept(st2)?;
                    let wr = self.wred(&st, qi, ok.0);
                    let body = self.run(&mp(wr, vec![s(&okr), s(&rest)]), &[])?;
                    let d = self.close(body, &[cond.clone()], &[])?;
                    return self.wsplit(&st, qi, &cond, u, d);
                }
                // (a call: at the machine's call; the instructions before it first)
                Some(Red::Call { g, args, list, one, a, xx, dd, k }) => {
                    if self.insns.get(&st.a).map(|i| i.row) == Some(120) {
                        return self.call_at(&st, qi, g, &args, list, one, a, xx, dd, k);
                    }
                }
                Some(Red::Guard { cond, ub }) => {
                    let u = self.raise_when_not(&cond, &ub)?;
                    // defined: the same rest, with the condition
                    let hc = self.assume(&cond)?;
                    let mut st2 = st.clone();
                    st2.hyps.push((cond.clone(), hc));
                    let rest = self.prove_kept(st2)?;
                    let d = self.close(rest, &[cond.clone()], &[])?;
                    return self.wsplit(&st, qi, &cond, u, d);
                }
                None => {}
            }
        }
        // (where branches meet: the claim proven once, for all of them)
        if let Some(pf) = self.join(&st)? {
            return Ok(pf);
        }
        self.insn(st)
    }

    /// the literal facts at st: `L`, a loop step's counter, the maps' deep
    /// `in dom` facts
    fn set_lf(&mut self, st: &St) -> Result<(), String> {
        let mut lf = vec![self.lf0.clone().expect("the literal facts")];
        lf.extend(st.lfx.iter().cloned());
        if let Some(l) = st.lp {
            lf.push(self.loops[l].ci.clone());
        }
        let mut deep = self.deep_doms(&st.rs);
        deep.extend(self.deep_doms(&st.hst));
        for d in deep {
            lf.push(self.ev(&d, &[])?);
        }
        self.lf = lf;
        Ok(())
    }

    /// `k in dom(m)` for the map m, by its updates: k's own (`tr.dom_upd`)
    /// under the later ones (`tr.dom_keep`) -- None for a key not in it
    pub(super) fn dom_pf(&self, m: &Term, k: u128) -> Option<R> {
        let (parent, r, pv) = upd_parts(self, m)?;
        if nat(&r) == Some(k) {
            return Some(R::Mp(Box::new(f("tr.dom_upd")), vec![t(&parent), t(&r), t(&pv)]));
        }
        let inner = self.dom_pf(&parent, k)?;
        Some(mpf("tr.dom_keep", vec![t(&parent), t(&lit(k)), t(&r), t(&pv), p(inner), simp0()]))
    }

    /// `!(k in dom(m))` for a key not in the map m, by its updates
    /// (`tr.dom_out`) down to empty (`tr.dom_none`)
    pub(super) fn dom_out_pf(&self, m: &Term, k: u128) -> Option<R> {
        if self.app(m, "empty", 0).is_some() {
            return Some(mpf("tr.dom_none", vec![t(&lit(k))]));
        }
        let (parent, r, pv) = upd_parts(self, m)?;
        if nat(&r) == Some(k) {
            return None;
        }
        let inner = self.dom_out_pf(&parent, k)?;
        Some(mpf("tr.dom_out", vec![t(&parent), t(&lit(k)), t(&r), t(&pv), p(inner), simp0()]))
    }

    /// the keys two updates or more below the top of the map m: their `in
    /// dom` facts (simp(L) shows the others)
    fn deep_doms(&self, m: &Term) -> Vec<R> {
        let mut seen = Vec::new();
        let mut out = Vec::new();
        let (mut cur, mut depth) = (m.clone(), 0);
        while let Some((parent, r, _)) = upd_parts(self, &cur) {
            if let Some(k) = nat(&r) {
                if !seen.contains(&k) {
                    seen.push(k);
                    if depth >= 2 {
                        out.extend(self.dom_pf(m, k));
                    }
                }
            }
            cur = parent;
            depth += 1;
        }
        out
    }

    /// `tr.hin(hs, fr)` for the homes' map hs: one `tr.hin_upd` per entry,
    /// as the map is nested
    fn hin_proof(&self, hs: &Term, fr: u128) -> Result<R, String> {
        if self.app(hs, "empty", 0).is_some() {
            return Ok(mpf("tr.hin_empty", vec![t(&lit(fr))]));
        }
        let (h, c, x) = upd_parts(self, hs).ok_or("the homes' map: not an update")?;
        let ph = self.hin_proof(&h, fr)?;
        Ok(mpf("tr.hin_upd", vec![t(&h), t(&lit(fr)), t(&c), t(&x), p(ph), simp0()]))
    }

    /// A call (tr.call, tr.call1 for call1): the machine's `call rel32` at
    /// st's address from a frame of fr bytes, the spec's call of g with the
    /// arguments in their registers; the claim after it (at the return
    /// address, rax:rdx the result -- rax for call1 --, the homes kept, the
    /// frame from the push up) for every world and result
    #[allow(clippy::too_many_arguments)]
    fn call_at(&mut self, st: &St, qi: usize, g: Term, args: &[Term], list: Term, one: bool, al: Term, xl: Term, dl: Term, kl: Term) -> Result<Seq, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        if insn.row != 120 {
            return Err(format!("{:x}: the spec calls, the machine does not", a));
        }
        if st.fr % 8 != 0 || st.fr < 8 || st.fr + 8 > 65536 {
            return Err(format!("{:x}: a call from a frame of {} bytes (a multiple of 8, at most 64 KiB expected)", a, st.fr));
        }
        let aligned = st.fr % 16 == 8;
        let nargs = args.len();
        if nargs > 6 {
            return Err(format!("{:x}: a call with {} arguments (at most 6 so far)", a, nargs));
        }
        let off = nat(&insn.fields).ok_or_else(|| format!("{:x}: the call's displacement", a))?;
        let a2 = (a + insn.len) % P64;
        let fa = (a2 + if off >= 1 << 31 { off + (P64 - (1 << 32)) } else { off }) % P64;
        // the arguments: arg(n, X), X in its register
        const ARGREGS: [u128; 6] = [7, 6, 2, 1, 8, 9];
        let mut aps = Vec::new();
        for (i, ar) in args.iter().enumerate() {
            let ax = self.app(ar, "gimple.arg", 2).ok_or_else(|| format!("{:x}: argument {} not a register argument", a, i))?;
            let nb = nat(&ax[0]).ok_or_else(|| format!("{:x}: argument {}'s width", a, i))?;
            let x = ax[1].clone();
            let r = ARGREGS[i];
            let (k, v) = self.reg(st, r).ok_or_else(|| format!("{:x}: register {} holds no value at the call", a, r))?;
            if ![1, 2, 4, 8].contains(&k) || self.canon(&v) != self.canon(&x) {
                return Err(format!("{:x}: register {} holds {}, the spec passes {}", a, r, self.print(&v), self.print(&x)));
            }
            aps.push(p(R::Apply(Box::new(f("tr.argv_reg")), vec![t(&st.rs), t(&lit(r)), t(&lit(k)), t(&lit(nb)), t(&x), simp_l(), simp_l(), simp0()])));
        }
        let hreg = if nargs == 0 { mpf("tr.args0", vec![t(&st.rs)]) } else { R::Apply(Box::new(f(&format!("tr.args{nargs}"))), aps) };
        let hin = self.hin_proof(&st.hst, st.fr)?;
        let ci = self.callees.iter().position(|c| c.0 == g && c.1 == fa).unwrap_or_else(|| {
            self.callees.push((g.clone(), fa, nargs, false));
            self.callees.len() - 1
        });
        self.callees[ci].3 |= !aligned;
        // (its premises: hcall{i} .. for the spec's parameter Gi)
        let gi: usize = self.env.vars[Self::var_id(&g) as usize].name.strip_prefix('G').and_then(|i| i.parse().ok()).ok_or_else(|| format!("{:x}: a call of {}, not a parameter of the spec", a, self.print(&g)))?;
        // (its premises, at its first call: its contract on the program text,
        // its spec typed, its returns' effects)
        if gi >= self.cinfo.len() {
            return Err(format!("{:x}: a call of G{}, not a parameter of the spec", a, gi));
        }
        match &self.cinfo[gi] {
            None => {
                let imp = if aligned { "tr.implements_at" } else { "tr.implements_at_u" };
                let (lb, lc, statics) = (self.lbase.clone(), self.lcode.clone(), self.statics_t.clone());
                let hc = self.mk(imp, vec![lit(fa), g.clone(), lb, lc, statics]);
                let ht = self.mk("in", vec![g.clone(), self.mk("fn_space", vec![self.mk("abi.ARGS", vec![]), self.mk("powerset", vec![self.mk("univ", vec![lit(1)])])])]);
                let hi = self.mk("tr.callee_io", vec![g.clone(), lit(nargs as u128)]);
                self.hcall[gi] = Some(self.assume(&hc)?);
                self.htyp[gi] = Some(self.assume(&ht)?);
                self.hio[gi] = Some(self.assume(&hi)?);
                self.cinfo[gi] = Some((fa, nargs, !aligned, [hc, ht, hi]));
            }
            Some((f0, n0, u0, _)) => {
                if (*f0, *n0, *u0) != (fa, nargs, !aligned) {
                    return Err(format!("{:x}: a call of G{} other than its first (at another address, with other arguments, or another alignment)", a, gi));
                }
            }
        }
        let (hcall, htyp, hio) = (self.hcall[gi].clone().unwrap(), self.htyp[gi].clone().unwrap(), self.hio[gi].clone().unwrap());
        // (the callee's contract at this call: the ABI's if aligned, else the one for any entry)
        let hcon = if aligned {
            let fr16 = self.evp(&RP::Simp(false, vec![], vec![], false), &self.mk("eq", vec![self.mk("int_mod", vec![lit(st.fr), lit(16)]), lit(8)]), &[])?;
            defs(RP::Taut(vec![R::S(hcall), R::S(fr16)]), &["tr.callee_contract"])
        } else {
            defs(RP::Taut(vec![R::S(hcall)]), &["tr.callee_contract"])
        };
        let w = st.w.clone();
        let hv = st.hvu.clone();
        // the continuation's raise and divergence: the function's
        let n = self.fresh("c");
        let (xv, ev, tv) = (self.var(&format!("XC{n}")), self.var(&format!("EC{n}")), self.var(&format!("TC{n}")));
        let x8 = Term::bvar(0);
        let mkq = |gg: &Gen, h: Term| -> Term {
            let kk = kl.instantiate_params(&[Term::bvar(0), Term::bvar(1)], &gg.env.binders_fn());
            gg.mk("mkprog", vec![gg.mk("ex", vec![gg.mk("and", vec![h, kk])])])
        };
        let qx = mkq(self, xl.instantiate_params(&[xv.clone(), ev.clone(), x8.clone()], &self.env.binders_fn()));
        let qd = mkq(self, dl.instantiate_params(&[tv.clone(), x8.clone()], &self.env.binders_fn()));
        let univ = |gg: &Gen, x: &Term| gg.mk("in", vec![x.clone(), gg.mk("univ", vec![lit(1)])]);
        // hk: all X E. X in univ(1) -> E in univ(1) -> runs(qx, w, exc(X, E))
        let (hx, he) = (univ(self, &xv), univ(self, &ev));
        let (hxs, hes) = (self.assume(&hx)?, self.assume(&he)?);
        let gk = self.mk("runs", vec![qx, w.clone(), self.mk("exc", vec![xv.clone(), ev.clone()])]);
        let k0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hxs), R::S(hes), R::S(hv.clone())], vec![], false)), vec!["runs".into(), "mkprog".into()]), &gk, &[])?;
        let hk = self.close(k0, &[hx, he], &[Self::var_id(&xv), Self::var_id(&ev)])?;
        // hd: all T. T in univ(1) -> runs(qd, w, diverge(T))
        let ht = univ(self, &tv);
        let hts = self.assume(&ht)?;
        let gd = self.mk("runs", vec![qd, w.clone(), self.mk("diverge", vec![tv.clone()])]);
        let d0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hts), R::S(hv.clone())], vec![], false)), vec!["runs".into(), "mkprog".into()]), &gd, &[])?;
        let hd = self.close(d0, &[ht], &[Self::var_id(&tv)])?;
        // the claim after the call, for every world W4 and result R0 (:R1)
        let (w4, r0, r1) = (self.var(&format!("WC{n}")), self.var(&format!("RC{n}")), self.var(&format!("RD{n}")));
        let res = if one { r0.clone() } else { self.mk("pair", vec![r0.clone(), r1.clone()]) };
        let ka = al.instantiate_params(&[Term::bvar(2), res, Term::bvar(0)], &self.env.binders_fn());
        let q2 = self.canon(&mkq(self, ka));
        let j = self.new_q(q2);
        let fd2 = st.fr + 8;
        let hw4t = self.mk("and", vec![self.mk("in", vec![w4.clone(), self.mk("abi.World", vec![])]), univ(self, &w4)]);
        let hw4 = self.assume(&hw4t)?;
        let hv4 = self.evp(&RP::Taut(vec![R::S(hw4.clone())]), &univ(self, &w4), &[])?;
        let b64 = |gg: &Gen, x: &Term| gg.mk("in", vec![x.clone(), gg.mk("bits", vec![lit(64)])]);
        let mut hs_after = vec![hw4t.clone(), b64(self, &r0)];
        let mut vs_after = vec![Self::var_id(&w4), Self::var_id(&r0)];
        if !one {
            hs_after.push(b64(self, &r1));
            vs_after.push(Self::var_id(&r1));
        }
        let mut st0 = st.clone();
        for h in &hs_after[1..] {
            let hf = self.assume(h)?;
            st0.facts.push(hf);
        }
        st0.a = a2;
        st0.regs = Vec::new();
        st0.rs = self.mk("empty", vec![]);
        st0.w = w4.clone();
        st0.hvu = hv4;
        st0.hw = hw4;
        st0.ds = lit(fd2);
        st0.spec = Spec::Proc(j);
        let mut st2 = self.set_reg(&st0, a2, 0, 8, r0.clone());
        if !one {
            st2 = self.set_reg(&st2, a2, 2, 8, r1.clone());
        }
        let rest = self.prove_kept(st2)?;
        let pc = self.close(rest, &hs_after, &vs_after)?;
        let inst = R::Inst(
            if one { "tr.call1" } else { "tr.call" }.into(),
            vec![
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("a", lit(a)),
                ("a2", lit(a2)),
                ("len", lit(insn.len)),
                ("off", lit(off)),
                ("f", lit(fa)),
                ("g", g.clone()),
                ("args", list),
                ("n", lit(nargs as u128)),
                ("cb", self.lbase.clone()),
                ("cc", self.lcode.clone()),
                ("st", self.statics_var()),
                ("hs", st.hst.clone()),
                ("ds", st.ds.clone()),
                ("fd2", lit(fd2)),
                ("rs", st.rs.clone()),
                ("w", w.clone()),
                ("ka", al),
                ("xx", xl),
                ("dd", dl),
                ("k", kl),
                ("kw", self.kw3()),
            ],
        );
        let _ = qi;
        let hl = self.hl.clone().unwrap();
        let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
        self.run(
            &mp(
                inst,
                vec![
                    p(f(&insn.name)),
                    simp_l(),
                    simp_l(),
                    simp_l(),
                    simp_l(),
                    hcon,
                    s(&hl),
                    simp0(),
                    cfr,
                    simp0(),
                    simp0(),
                    simp0(),
                    s(&htyp),
                    s(&hio),
                    p(hreg),
                    p(hin),
                    simp0(),
                    simp0(),
                    s(&hk),
                    s(&hd),
                    s(&pc),
                ],
            ),
            &[],
        )
    }

    /// a loop's head (the spec's loop there): its claim, by induction
    fn loop_point(&mut self, st: &St) -> Result<Option<Seq>, String> {
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        if self.loop_head(qi).is_none() || !self.is_loop_test(st.a) {
            return Ok(None);
        }
        if let Some(l) = st.lp {
            if self.loops[l].head == st.a {
                return self.loop_back(st, qi, l).map(Some);
            }
        }
        self.loop_start(st, qi).map(Some)
    }

    /// the machine's loop test at a: an instruction followed by a backward
    /// conditional jump
    fn is_loop_test(&self, a: u128) -> bool {
        let Some(i) = self.insns.get(&a) else { return false };
        matches!(self.jcc((a + i.len) % P64), Ok((_, _, _, tt, _)) if tt <= a)
    }

    /// A counting loop met at its head h (the machine's test `cmp dword [rsp
    /// + d], K; jle`, the counter in the home d): the claim at h for every
    /// world lw and counter li with the invariant, by induction on the
    /// variant (tr.wf2); here, at the counter's start value.
    fn loop_start(&mut self, st: &St, qi: usize) -> Result<Seq, String> {
        let h = st.a;
        let bad = |m: &str| format!("{:x}: a loop {}: not covered yet", h, m);
        // the machine's test: the counter's home, the bound
        let (d, kv) = {
            let i = &self.insns[&h];
            let x = (i.row == 60).then(|| self.pairs(&i.fields, 5)).flatten().ok_or_else(|| bad("whose test is not cmp dword [rsp + d], imm8"))?;
            let d = self.rsp_mem(&x[2]).and_then(|d| nat(&d)).ok_or_else(|| bad("whose test is not on a home"))?;
            let k = nat(&x[4]).filter(|k| *k < 128 && nat(&x[1]) == Some(7)).ok_or_else(|| bad("whose test is not cmp with a small immediate"))?;
            (self.hkey(d), k)
        };
        // the rest: ex x8. while_rel(pair(x0, I0), true, B, TR, x8) && K
        let q = self.qs[qi].clone();
        let body = self.app(&q, "mkprog", 1).unwrap()[0].clone();
        let y = self.app(&self.app(&body, "ex", 1).unwrap()[0], "and", 2).unwrap().to_vec();
        let ctx = ["x0", "x1", "x8"];
        let al = self.lam(&y[0], &ctx, &["x0", "x8"]).ok_or_else(|| bad("whose head reads the outcome"))?;
        let kl = self.lam(&y[1], &ctx, &["x8", "x1"]).ok_or_else(|| bad("whose rest reads the world"))?;
        let wr = self.app(&al, "while_rel", 5).ok_or_else(|| bad("not a while"))?.to_vec();
        let l0 = self.app(&wr[0], "pair", 2).ok_or_else(|| bad("whose state is not the world and one local"))?.to_vec();
        let i0 = l0[1].clone();
        let outer = {
            let bf = self.env.binders_fn();
            i0.loose_depth(&bf) > 0 || wr[2].loose_depth(&bf) > 2 || wr[3].loose_depth(&bf) > 1
        };
        if outer {
            return Err(bad("whose body reads the outer state"));
        }
        match st.hsm.get(&d) {
            Some((4, x)) if self.canon(x) == self.canon(&i0) => {}
            _ => return Err(bad("whose counter is not its home's value")),
        }
        if st.hsm.len() != 1 {
            return Err(bad("in a frame of other homes"));
        }
        if nat(&i0) != Some(0) {
            return Err(bad("whose counter does not start at 0"));
        }
        // (at the counter's start: the guarded rest, the claim's at i0)
        let (j0, nodiv0) = self.by(qi, "tr.qs_nodiv", &[("a", al.clone()), ("k", kl.clone())])?;
        // the step's variables: the world, the counter
        let ln = self.fresh("");
        let lw = self.var(&format!("lw{ln}"));
        let li = self.var(&format!("li{ln}"));
        let l0li = wr[0].with_args(vec![l0[0].clone(), li.clone()]);
        let mut wa: Vec<Term> = wr.clone();
        wa[0] = l0li;
        let al_li = al.with_args(wa);
        let (_, stmt) = self.inst("tr.qs_nodiv", &[("a", al_li), ("k", kl.clone())])?;
        let (_, qh) = self.qparts(&stmt).ok_or("qs_nodiv")?;
        let qhc = self.canon(&qh);
        let jh = self.new_q(qhc);
        let l0f = self.mk("pair", vec![Term::bvar(0), li.clone()]);
        let (ju, unroll) = self.by(jh, "tr.qs_loop", &[("l0", l0f), ("b", wr[2].clone()), ("tr", wr[3].clone()), ("k", kl.clone())])?;
        let hst = self.upd(&self.mk("empty", vec![]), d, 4, &li);
        // the claim, the invariant, the variant (of lw, li)
        let cl_t = self.mk(
            "tr.pt",
            vec![self.s.clone(), self.v.clone(), self.base.clone(), self.code.clone(), lit(st.fr), lit(h), hst.clone(), lit(self.fd), self.mk("empty", vec![]), self.wrap_of(&self.qs[jh].clone()), lw.clone()],
        );
        let inv_t = self.mk("tr.count_inv", vec![lit(kv), li.clone()]);
        let pi_t = self.mk("and", vec![inv_t.clone(), self.mk("and", vec![self.mk("in", vec![lw.clone(), self.mk("abi.World", vec![])]), self.mk("in", vec![lw.clone(), self.mk("univ", vec![lit(1)])])])]);
        let mv_t = self.mk("tr.count_var", vec![lit(kv), li.clone()]);
        let (lwv, liv) = (Self::var_id(&lw), Self::var_id(&li));
        let (cl, pi, mv) = (self.abs(&cl_t, &[lwv, liv]), self.abs(&pi_t, &[lwv, liv]), self.abs(&mv_t, &[lwv, liv]));
        // nat: all lw li. PI(lw, li) -> MV(lw, li) in omega
        let hpi = self.assume(&pi_t)?;
        let c = self.evp(&RP::Taut(vec![R::S(hpi.clone())]), &inv_t, &[])?;
        let mvo = self.mk("in", vec![mv_t.clone(), self.mk("omega", vec![])]);
        let n0 = self.evp(&RP::Apply(f("tr.count_nat"), vec![t(&lit(kv)), t(&li), simp0(), s(&c)]), &mvo, &[])?;
        let natf = self.close(n0, &[pi_t.clone()], &[lwv, liv])?;
        // step: all lw li. PI(lw, li) -> (all x2 y2. PI(x2, y2) -> MV(x2, y2) < MV(lw, li) -> CL(x2, y2)) -> CL(lw, li)
        let ih_t = {
            let x2 = self.var("x2");
            let y2 = self.var("y2");
            let app2 = |gg: &Gen, lam: &Term, a: &Term, b: &Term| lam.instantiate_params(&[a.clone(), b.clone()], &gg.env.binders_fn());
            let body = self.mk(
                "imp",
                vec![
                    app2(self, &pi, &x2, &y2),
                    self.mk("imp", vec![self.mk("int_lt", vec![app2(self, &mv, &x2, &y2), mv_t.clone()]), app2(self, &cl, &x2, &y2)]),
                ],
            );
            let inner = self.abs(&body, &[Self::var_id(&x2), Self::var_id(&y2)]);
            self.mk("all", vec![self.mk("all", vec![inner])])
        };
        let ih = self.assume(&ih_t)?;
        let hw = self.evp(&RP::Taut(vec![R::S(hpi.clone())]), &self.mk("and", vec![self.mk("in", vec![lw.clone(), self.mk("abi.World", vec![])]), self.mk("in", vec![lw.clone(), self.mk("univ", vec![lit(1)])])]), &[])?;
        let hv = self.evp(&RP::Taut(vec![R::S(hpi.clone())]), &self.mk("in", vec![lw.clone(), self.mk("univ", vec![lit(1)])]), &[])?;
        let cc = c.clone();
        let ci = self.ev(&R::Expand(Box::new(R::S(cc.clone())), vec!["tr.count_inv".into()]), &[])?;
        let idx = self.loops.len();
        self.loops.push(Loop { head: h, ih: ih.clone(), k: kv, d, qh: self.qs[jh].clone(), li: li.clone(), ci, cc });
        let st_head = St {
            a: h,
            fr: st.fr,
            regs: Vec::new(),
            rs: self.mk("empty", vec![]),
            ds: lit(self.fd),
            w: lw.clone(),
            hvu: hv,
            hw,
            hsm: [(d, (4, li.clone()))].into_iter().collect(),
            hst: hst.clone(),
            lp: Some(idx),
            spec: Spec::Proc(jh),
            hyps: st.hyps.clone(),
            facts: st.facts.clone(),
            lfx: st.lfx.clone(),
            bconds: st.bconds.clone(),
            spent: st.spent.clone(),
            splits: st.splits.clone(),
            no_join: None,
            z: None,
        };
        let mut st_body = st_head.clone();
        st_body.spec = Spec::Proc(ju);
        let body_pf = self.prove_kept(st_body)?;
        let wr_h = self.wred(&st_head, jh, ju);
        let step0 = self.run(&mp(wr_h, vec![p(mp(unroll, vec![t(&lw)])), s(&body_pf)]), &[])?;
        let stepf = self.close(step0, &[pi_t, ih_t], &[lwv, liv])?;
        let wf = R::Inst("tr.wf2".into(), vec![("claim", cl), ("p", pi), ("mm", mv)]);
        let loopf = self.run(&mp(wf, vec![s(&natf), s(&stepf)]), &[])?;
        let i0f = self.run(&R::Apply(Box::new(f("tr.count_init")), vec![t(&lit(kv)), simp0()]), &[])?;
        let c0 = self.run(&mp(R::S(loopf), vec![t(&st.w), t(&i0), taut(vec![R::S(i0f), R::S(st.hw.clone())])]), &[])?;
        let rs = mpf(
            "tr.pt_rs",
            vec![t(&self.s.clone()), t(&self.v.clone()), t(&self.base.clone()), t(&self.code.clone()), t(&lit(st.fr)), t(&lit(h)), t(&st.hst), t(&lit(self.fd)), t(&st.rs), t(&self.wrap_of(&self.qs[j0].clone())), t(&st.w), s(&c0)],
        );
        let wr0 = self.wred(st, qi, j0);
        self.run(&mp(wr0, vec![p(mp(nodiv0, vec![t(&st.w)])), p(rs)]), &[])
    }

    /// the loop's head again (its body's end): the claim there, by the
    /// induction hypothesis at the world and counter now
    fn loop_back(&mut self, st: &St, qi: usize, l: usize) -> Result<Seq, String> {
        let lp = self.loops[l].clone();
        let q = self.qs[qi].clone();
        let badm = format!("{:x}: back at the loop's head, the rest not the loop's: {}", st.a, self.print(&q));
        let bad = || badm.clone();
        // the rest: ex x8. (while_rel(pair(x0, T'), ..) && !(fst(x8) = 2)) && (ex x2. k(x8, x2) && x1 = x2)
        let body = self.app(&q, "mkprog", 1).ok_or_else(bad)?[0].clone();
        let y = self.app(&self.app(&body, "ex", 1).ok_or_else(bad)?[0], "and", 2).ok_or_else(bad)?.to_vec();
        let al = self.lam(&y[0], &["x0", "x1", "x8"], &["x0", "x8"]).ok_or_else(bad)?;
        let ek = self.app(&y[1], "ex", 1).ok_or_else(bad)?.to_vec();
        let ka = self.app(&ek[0], "and", 2).ok_or_else(bad)?.to_vec();
        let kl = self.lam(&ka[0], &["x0", "x1", "x8", "x2"], &["x8", "x2"]).ok_or_else(bad)?;
        let (j, settle) = self.by(qi, "tr.qs_settle", &[("a", al.clone()), ("k", kl)])?;
        // the counter now: T' = li + 1, at the home
        let g0 = self.app(&al, "and", 2).ok_or_else(bad)?[0].clone();
        let wr = self.app(&g0, "while_rel", 5).ok_or_else(bad)?.to_vec();
        let tp = self.app(&wr[0], "pair", 2).ok_or_else(bad)?[1].clone();
        let step = self.mk("bits_add", vec![lit(32), lp.li.clone(), lit(1)]);
        if self.expand(&tp) != self.expand(&step) {
            return Err(format!("{:x}: the counter at the loop's end {} is not {} + 1", st.a, self.print(&tp), self.print(&lp.li)));
        }
        match st.hsm.get(&lp.d) {
            Some((4, x)) if self.canon(x) == self.canon(&tp) && st.hsm.len() == 1 => {}
            _ => return Err(format!("{:x}: the counter's home not the counter at the loop's end", st.a)),
        }
        // (the rest now: the claim's at T')
        let liv = Self::var_id(&lp.li);
        let qh2 = self.canon(&lp.qh.subst_var(liv, &tp, &self.env.binders_fn()));
        if self.canon(&self.qs[j]) != qh2 {
            return Err(format!("{:x}: the rest at the loop's end not the claim's:\n  {}\n  {}", st.a, self.print(&self.qs[j]), self.print(&qh2)));
        }
        // the invariant at (W', T'), the variant smaller: by the counter's step
        let k = lp.k;
        let g = self.mk("not", vec![self.mk("int_lt", vec![self.mk("sint", vec![lit(32), lit(k)]), self.mk("sint", vec![lit(32), lp.li.clone()])])]);
        let hg = self.hyp_find(&st.hyps, &g).map(|h| h.1.clone()).ok_or_else(|| format!("{:x}: the loop's condition not in scope", st.a))?;
        let cs = self.run(&R::Apply(Box::new(f("tr.count_step")), vec![t(&lit(k)), t(&lp.li), simp0(), s(&lp.cc), simp0(), s(&hg)]), &[])?;
        let c = self.run(&mp(R::S(lp.ih.clone()), vec![t(&st.w), t(&tp), taut(vec![R::S(cs.clone()), R::S(st.hw.clone())]), taut(vec![R::S(cs)])]), &[])?;
        let rs = mpf(
            "tr.pt_rs",
            vec![t(&self.s.clone()), t(&self.v.clone()), t(&self.base.clone()), t(&self.code.clone()), t(&lit(st.fr)), t(&lit(st.a)), t(&st.hst), t(&lit(self.fd)), t(&st.rs), t(&self.wrap_of(&self.qs[j].clone())), t(&st.w), s(&c)],
        );
        let wr0 = self.wred(st, qi, j);
        self.run(&mp(wr0, vec![p(mp(settle, vec![t(&st.w)])), p(rs)]), &[])
    }

    /// the rest `qi`'s head a loop: `ex x8. while_rel(l0, c, b, tr, x8) && k`
    /// (its parts: l0, b, tr, k, as the rest has them)
    fn loop_head(&self, qi: usize) -> Option<Vec<Term>> {
        let body = self.app(&self.qs[qi], "mkprog", 1)?[0].clone();
        let e = self.app(&body, "ex", 1)?;
        let y = self.app(&e[0], "and", 2)?;
        // (or guarded: while_rel(..) && !(fst(x8) = 2), at the body's end)
        let w0 = self.app(&y[0], "and", 2).map(|g| g[0].clone()).unwrap_or(y[0].clone());
        let wr = self.app(&w0, "while_rel", 5)?;
        Some(vec![wr[0].clone(), wr[2].clone(), wr[3].clone(), y[1].clone()])
    }

    /// a linear step: the rule's instance (the slot `NEXT` the next point's
    /// claim), the state after
    pub(super) fn then(&mut self, r: R, st2: St) -> Result<Seq, String> {
        let a2 = st2.a;
        let (rs2, regs2) = (st2.rs.clone(), st2.regs.clone());
        let rest = self.prove_kept(st2)?;
        self.run(&r, &[("NEXT", rest)]).map_err(|e| {
            self.trace(|| {
                let regs: Vec<String> = regs2.iter().map(|(r, n, v)| format!("r{} ({} bytes) = {}", r, n, self.print(v))).collect();
                format!("failed step to {:x}: after it, rs {} / regs {}", a2, self.print(&rs2), regs.join("; "))
            });
            format!("the step to {:x}: {}", a2, e)
        })
    }

    /// a register r holding fewer than n bytes, as one holding n
    /// (`tr.pt_widen`): the step, before the instruction's own
    pub(super) fn widen(&mut self, st: &St, r: u128, n: u128) -> Result<Option<Seq>, String> {
        let Some((m, u)) = self.reg(st, r) else { return Ok(None) };
        if m >= n {
            return Ok(None);
        }
        let rule = mpf(
            "tr.pt_widen",
            vec![
                t(&self.s.clone()),
                t(&self.v.clone()),
                t(&self.base.clone()),
                t(&self.code.clone()),
                t(&lit(self.fr)),
                t(&lit(st.a)),
                t(&st.hst),
                t(&st.ds),
                t(&st.rs),
                t(&self.p(&st.spec)),
                t(&st.w),
                t(&lit(r)),
                t(&lit(m)),
                t(&lit(n)),
                t(&u),
                simp_l(),
                simp_l(),
                simp0(),
                simp0(),
                arith(vec![]),
                p(R::Slot("NEXT")),
            ],
        );
        let st2 = self.set_reg(st, st.a, r, n, u);
        Ok(Some(self.then(rule, st2)?))
    }

    /// a branch on c: on to a3 when c, to t when not (the rule's slots `T`,
    /// `F` the two)
    pub(super) fn branch(&mut self, st: &St, c: Term, a3: u128, tt: u128, rule: R) -> Result<Seq, String> {
        let nc = self.mk("not", vec![c.clone()]);
        let mut bs = Vec::new();
        for (cond, to, other) in [(c.clone(), a3, tt), (nc, tt, a3)] {
            let mut st2 = st.clone();
            st2.a = to;
            st2.splits.push(self.split(st, other));
            let hn = self.assume(&cond)?;
            // (a branch its earlier tests exclude: by their contradiction)
            let opp = match self.app(&cond, "not", 1) {
                Some(x) => x[0].clone(),
                None => self.mk("not", vec![cond.clone()]),
            };
            let body = if let Some(h) = self.hyp_find(&st.hyps, &opp) {
                let goal = self.pt(&st2, to);
                self.evp(&RP::Taut(vec![R::S(hn), R::S(h.1.clone())]), &goal, &[])?
            } else {
                st2.bconds.push(st2.hyps.len());
                st2.hyps.push((cond.clone(), hn));
                self.prove_kept(st2)?
            };
            bs.push(self.close(body, &[cond], &[])?);
        }
        let fb = bs.pop().unwrap();
        let tb = bs.pop().unwrap();
        self.run(&rule, &[("T", tb), ("F", fb)])
    }

    /// the instance's common head: `s, V, base, code, fr, a, a2, len`
    pub(super) fn head(&self, a: u128, insn: &Insn) -> Vec<RA> {
        vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit((a + insn.len) % P64)), t(&lit(insn.len))]
    }

    /// a home's key: the offset from the entry's rsp of rsp + d in the frame
    pub(super) fn hkey(&self, d: u128) -> u128 {
        (d + P64 - self.fr % P64) % P64
    }

    /// the instance's tail: the coupling's maps, the decode fact, n literal
    /// facts, the extra premises, the next point
    pub(super) fn tail(&self, st: &St, insn: &Insn, n: usize, extra: Vec<RA>) -> Vec<RA> {
        let mut v = vec![t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w), p(f(&insn.name))];
        v.extend((0..n).map(|_| simp_l()));
        v.extend(extra);
        v.push(p(R::Slot("NEXT")));
        v
    }

    /// the same for a rule writing a home: the homes it leaves (hs2) after
    /// the map
    pub(super) fn tail_h(&self, st: &St, insn: &Insn, hs2: &Term, n: usize, extra: Vec<RA>) -> Vec<RA> {
        let mut v = vec![t(&st.hst), t(hs2), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w), p(f(&insn.name))];
        v.extend((0..n).map(|_| simp_l()));
        v.extend(extra);
        v.push(p(R::Slot("NEXT")));
        v
    }

    /// a rule's instance: `mp(tr.RULE, head, terms, tail)`
    pub(super) fn step(&self, rule: &str, a: u128, insn: &Insn, ts: &[&Term], tail: Vec<RA>) -> R {
        let mut args = self.head(a, insn);
        args.extend(ts.iter().map(|x| t(x)));
        args.extend(tail);
        mpf(&format!("tr.{}", rule), args)
    }

    /// the homes' map
    pub(super) fn hs_term(&self, hsm: &BTreeMap<u128, (u128, Term)>) -> Term {
        let mut m = self.mk("empty", vec![]);
        for (c, (n, x)) in hsm {
            m = self.upd(&m, *c, *n, x);
        }
        m
    }

    /// a store of n bytes to the home c: the homes it leaves (apart from
    /// it), their map, and the `tr.hkeep` proof -- one `tr.hkeep_upd` per
    /// home left
    pub(super) fn hkeep(&self, st: &St, c: u128, n: u128) -> (BTreeMap<u128, (u128, Term)>, Term, R) {
        let mut kept = BTreeMap::new();
        let mut pf = mpf("tr.hkeep_empty", vec![t(&st.hst), t(&lit(c)), t(&lit(n))]);
        for (&k, (nk, xk)) in &st.hsm {
            if k + nk <= c || c + n <= k {
                let fm = self.hs_term(&kept);
                pf = mpf(
                    "tr.hkeep_upd",
                    vec![t(&st.hst), t(&fm), t(&lit(c)), t(&lit(n)), t(&lit(k)), t(&lit(*nk)), t(xk), p(pf), simp_l(), simp_l(), defs(RP::Simp(false, vec![], vec![], false), &["tr.hdisj"])],
                );
                kept.insert(k, (*nk, xk.clone()));
            }
        }
        let tm = self.hs_term(&kept);
        (kept, tm, pf)
    }

    /// after a write of n bytes x to the home c: the homes it left, and it
    pub(super) fn set_home(&mut self, st: &St, a2: u128, c: u128, n: u128, x: Term) -> St {
        let (mut kept, kt, _) = self.hkeep(st, c, n);
        let mut st2 = st.clone();
        st2.a = a2;
        st2.hst = self.upd(&kt, c, n, &x);
        kept.insert(c, (n, x));
        st2.hsm = kept;
        st2
    }

    /// the conditional jump at a2: its displacement field, decode fact's
    /// length, the fall-through, the target, the condition code
    pub(super) fn jcc(&self, a2: u128) -> Result<(Term, u128, u128, u128, u128), String> {
        let j = self.insns.get(&a2).ok_or_else(|| format!("no decode fact at {:x}", a2))?;
        // (row 127: rel8; 128: rel32)
        let x = (j.row == 127 || j.row == 128).then(|| self.pairs(&j.fields, 2)).flatten().ok_or_else(|| format!("{:x}: not a conditional jump", a2))?;
        let (cc, r) = (nat(&x[0]).ok_or("jcc")?, nat(&x[1]).ok_or("jcc")?);
        let a3 = (a2 + j.len) % P64;
        let d = if j.row == 127 {
            let r8 = r & 0xff;
            if r8 >= 128 { r8 + P64 - 256 } else { r8 }
        } else {
            let r32 = r & 0xffff_ffff;
            if r32 >= 1 << 31 { r32 + P64 - (1 << 32) } else { r32 }
        };
        let tt = (a3 + d) % P64;
        Ok((x[1].clone(), j.len, a3, tt, cc))
    }

    /// a branch's rule instance (cmp; jcc): `mp(tr.RULE, s, V, base, code,
    /// fr, a, a2, a3, t, len1, len2, ts.., hs, ds, rs, p, w, insn1, insn2,
    /// n literal facts, extra.., T, F)`
    #[allow(clippy::too_many_arguments)]
    pub(super) fn jstep(&self, rule: &str, st: &St, a: u128, a2: u128, a3: u128, tt: u128, len1: u128, len2: u128, ts: &[&Term], insn: &Insn, n: usize, extra: Vec<RA>) -> R {
        // (the jump's row and displacement width: 127 / 8, 128 / 32 -- one
        // more literal premise of the rule, theirs)
        let (jn, jw) = if self.insns[&a2].row == 128 { (128, 32) } else { (127, 8) };
        let mut v = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(a3)), t(&lit(tt)), t(&lit(len1)), t(&lit(len2)), t(&lit(jn)), t(&lit(jw))];
        v.extend(ts.iter().map(|x| t(x)));
        v.extend([t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w), p(f(&insn.name)), p(f(&self.insns[&a2].name))]);
        v.extend((0..n + 1).map(|_| simp_l()));
        v.extend(extra);
        v.push(p(R::Slot("T")));
        v.push(p(R::Slot("F")));
        mpf(&format!("tr.{}", rule), v)
    }

    /// the statics' variable
    pub(super) fn statics_var(&self) -> Term {
        let v = self.names.iter().find(|x| x.0 == "statics").expect("statics").1;
        Term::var(v, vec![])
    }
}
