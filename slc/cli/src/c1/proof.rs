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
        // (the world before bound once in its term, a let)
        let weq = self.push_world(Self::var_id(&w2), w2term, &w);
        let hw2 = self.run(
            &R::Apply(Box::new(f("tr.world_store")), vec![t(&w), t(&so.addr), t(&lit(n)), t(&so.v), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]), simp_l()]),
            &[],
        )?;
        let hw2 = match &weq {
            Some(eq) => self.world_conv(hw2, eq)?,
            None => hw2,
        };
        let w2u = self.mk("in", vec![w2.clone(), self.mk("univ", vec![lit(1)])]);
        let hv2 = self.evp(&RP::Taut(vec![R::S(hw2.clone())]), &w2u, &[])?;
        // the store's run: ok, to the world after
        let empty = self.mk("empty", vec![]);
        let st8ok = match (&so.data, &so.cas) {
            _ if so.bf.is_some() => {
                let (size, pos, k, fv) = so.bf.clone().unwrap();
                mpf(
                    "tr.stbf_at_ok",
                    vec![
                        t(&w),
                        t(&so.p),
                        t(&so.off),
                        t(&size),
                        t(&pos),
                        t(&k),
                        t(&fv),
                        t(&so.addr),
                        taut(vec![R::S(st.hw.clone())]),
                        s(&st.hvu),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        s(&hc),
                    ],
                )
            }
            (_, Some((tv, sv, _))) => mpf(
                "tr.cas32_at_ok",
                vec![t(&w), t(&so.p), t(tv), t(sv), t(&so.addr), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), simp_l(), simp_l(), simp_l(), simp_l(), s(&hc)],
            ),
            (Some(d), _) => mpf(
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
            (None, None) => mpf(
                &format!("tr.st{}_at_ok", 8 * n),
                vec![t(&w), t(&so.p), t(&so.off), t(&so.v), t(&so.addr), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), simp_l(), simp_l(), simp_l(), simp_l(), s(&hc)],
            ),
        };
        // (the store's run to the world as its lemma states it: to the let)
        let st8ok = match &weq {
            Some(eq) => {
                let ok = self.run(&st8ok, &[])?;
                R::S(self.world_conv(ok, eq)?)
            }
            None => st8ok,
        };
        let okp = match &so.helper {
            None => p(st8ok),
            Some(fname) => {
                let (okl, _) = self.inst("tr.call1w_ok", &[("op", so.inner.clone()), ("r", empty.clone())])?;
                RA::P(RP::Defs(Box::new(RP::Mp(okl, vec![t(&w), t(&w2), s(&st.hvu), s(&hv2), p(st8ok)])), vec![fname.clone()]))
            }
        };
        // (the op's result: a compare-and-swap's old dword, else none)
        let res = so.cas.as_ref().map_or(empty.clone(), |c| c.2.clone());
        let (j, inst) = self.by(qi, "tr.qs_opw", &[("op", x[0].clone()), ("r", res), ("a", al), ("xx", xl), ("dd", dl), ("k", kl)])?;
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
        let w = self.w.clone();
        let empty = self.mk("empty", vec![]);
        let ex = self.mk("exc", vec![self.vw.clone(), empty.clone()]);
        // (a loop's iteration left raising: the rest after it raises)
        let mut base: Option<Seq> = None;
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
                Some(Red::Exit { e, k, kw }) => {
                    let kb = k.instantiate_params(&[e.clone(), Term::bvar(0)], &self.env.binders_fn());
                    let qk = self.canon(&self.mk("mkprog", vec![kb]));
                    let jk = self.new_q(qk);
                    let rk = self.raise_chain(jk)?;
                    let inst = R::Inst("tr.lcont_raise".into(), vec![("k", k), ("kw", kw)]);
                    let args = vec![t(&w), t(&e), t(&self.vw.clone()), t(&empty), defs(RP::Simp(false, vec![], vec![], false), &["is_ok"]), simpw(vec![self.hvu0_r(), self.hv_r()]), s(&rk)];
                    base = Some(self.run(&mp(inst, args), &[])?);
                    break;
                }
                _ => return Err(format!("a raise that does not reach the result: {}", self.print(&self.qs[cur]))),
            }
        }
        let mut r = match base {
            Some(b) => b,
            None => self.run(&mpf("tr.q_exc_runs", vec![t(&w), t(&self.vw), t(&empty), p(self.hv_r()), p(self.hvu0_r()), simp0()]), &[])?,
        };
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

    /// The resource guard: past `C1_MAX_MB` of resident memory (default
    /// 3000), the check stops at once -- not an error a walk recovers from
    /// (by walking the paths on their own, which is how it would run on):
    /// where it was, how many points, the addresses walked most often
    /// (where paths do not join).
    fn guard_resources(&mut self, a: u128) {
        *self.visits.entry(a).or_insert(0) += 1;
        let n: usize = self.visits.values().sum();
        if n % 64 != 0 {
            return;
        }
        let max_mb: u64 = std::env::var("C1_MAX_MB").ok().and_then(|v| v.parse().ok()).unwrap_or(3000);
        let rss_mb = std::fs::read_to_string("/proc/self/statm").ok().and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok()).map(|p| p * 4096 / (1 << 20));
        let Some(mb) = rss_mb.filter(|mb| *mb > max_mb) else { return };
        let mut top: Vec<(u128, usize)> = self.visits.iter().map(|(a, k)| (*a, *k)).collect();
        top.sort_by(|x, y| y.1.cmp(&x.1));
        let top: Vec<String> = top.iter().take(8).map(|(a, k)| format!("{:x} ({}x)", a, k)).collect();
        eprintln!(
            "error: C1 of `{}` stopped: {} MB of memory (C1_MAX_MB {}) at {:x} after {} points; the addresses walked most often (paths not joined there): {}",
            self.fname, mb, max_mb, a, n, top.join(", ")
        );
        std::process::exit(1);
    }

    /// The proof of the point claim at `st`.
    pub(super) fn prove(&mut self, st: St) -> Result<Seq, String> {
        self.guard_resources(st.a);
        // (a join's own claim: not joined at its address, joins after it)
        let mut st = st;
        if st.no_join.is_some_and(|j| j != st.a) {
            st.no_join = None;
        }
        if st.no_block.is_some_and(|j| j != st.a) {
            st.no_block = None;
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
                    // (the value's facts: a call's result a word)
                    let univ = [&st.hvu].into_iter().chain(self.hus.iter()).chain(st.lfx.iter()).map(|x| R::S(x.clone())).collect();
                    return self.run(&mp(inst, vec![simpw(univ), s(&rest)]), &[]);
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
                // the loop's exit: the rest in the function's wrapper, no
                // arrival (tr.lv_exit)
                Some(Red::Exit { e, k, kw }) => {
                    let lg = self.lpg.clone().ok_or_else(|| format!("{:x}: an iteration's end outside its loop's walk", st.a))?;
                    let kb = k.instantiate_params(&[e.clone(), Term::bvar(0)], &self.env.binders_fn());
                    let qk = self.canon(&self.mk("mkprog", vec![kb]));
                    let jk = self.new_q(qk);
                    let mut st2 = st.clone();
                    st2.spec = Spec::Proc(jk);
                    let (bka, wrap, kw0) = (self.bka.clone(), self.wrap.clone(), self.kw.clone());
                    self.bka = self.mk("false", vec![]);
                    self.wrap = lg.wrap.clone();
                    self.kw = lg.kw.clone();
                    self.lpg = None;
                    self.trace(|| format!("loop at {:x}: its exit at {:x}", lg.head, st.a));
                    self.hus.push(lg.hu.clone());
                    let rest = self.exit_rest(st2, jk);
                    self.hus.pop();
                    self.bka = bka;
                    self.wrap = wrap;
                    self.kw = kw0;
                    self.lpg = Some(lg);
                    let rest = rest?;
                    let inst = R::Inst("tr.lv_exit".into(), vec![("bkp", self.bkp.clone()), ("bka", self.bka.clone()), ("k", k), ("kw", kw)]);
                    let args = vec![
                        t(&self.s.clone()),
                        t(&self.v.clone()),
                        t(&self.base.clone()),
                        t(&self.code.clone()),
                        t(&lit(st.fr)),
                        t(&lit(st.a)),
                        t(&st.hst),
                        t(&st.ds),
                        t(&st.rs),
                        t(&e),
                        t(&st.w),
                        defs(RP::Simp(false, vec![], vec![], false), &["is_ok"]),
                        simp_l(),
                        s(&rest),
                    ];
                    return self.run(&mp(inst, args), &[]);
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
        self.insn(st)
    }

    /// the literal facts at st: `L`, a loop step's counter, the maps' deep
    /// `in dom` facts
    pub(super) fn set_lf(&mut self, st: &St) -> Result<(), String> {
        let mut lf = vec![self.lf0.clone().expect("the literal facts")];
        lf.extend(st.lfx.iter().cloned());
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
            // (the same value computed otherwise: equal by arithmetic modulo
            // the width, from the facts in scope)
            let mut eqf = Vec::new();
            if [1, 2, 4, 8].contains(&k) && self.canon(&v) != self.canon(&x) {
                let facts: Vec<R> = st.lfx.iter().chain(st.hyps.iter().map(|h| &h.1)).cloned().map(R::S).collect();
                let e = self.mk("eq", vec![v.clone(), x.clone()]);
                let defs: Vec<String> = ["bits_add", "bits_mul", "bits_sext"].iter().map(|d| d.to_string()).collect();
                match self.evp(&RP::Defs(Box::new(RP::Arith(facts)), defs), &e, &[]) {
                    Ok(q) => eqf.push(R::S(q)),
                    Err(er) => self.trace(|| format!("{:x}: argument {} not shown equal: {}", a, i, er)),
                }
            }
            if ![1, 2, 4, 8].contains(&k) || (self.canon(&v) != self.canon(&x) && eqf.is_empty()) {
                return Err(format!(
                    "{:x}: register {} holds {} ({}), the spec passes {} ({})",
                    a,
                    r,
                    self.print(&v),
                    self.print(&self.expand(&v)),
                    self.print(&x),
                    self.print(&self.expand(&x))
                ));
            }
            aps.push(p(R::Apply(Box::new(f("tr.argv_reg")), vec![t(&st.rs), t(&lit(r)), t(&lit(k)), t(&lit(nb)), t(&x), simp_l(), simp_lw(eqf), simp0()])));
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
        // (in a loop's body, the rest ends in the iteration's end)
        // (its inner run of the rest kept for simp's own `runs(mkprog ..)`)
        let kd: Vec<String> = if self.lpg.is_some() { ["tr.lcont", "tr.isout", "tr.mk"].map(String::from).to_vec() } else { vec!["runs".into(), "mkprog".into()] };
        let k0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hxs), R::S(hes), R::S(hv.clone())], vec![], false)), kd.clone()), &gk, &[])?;
        let hk = self.close(k0, &[hx, he], &[Self::var_id(&xv), Self::var_id(&ev)])?;
        // hd: all T. T in univ(1) -> runs(qd, w, diverge(T))
        let ht = univ(self, &tv);
        let hts = self.assume(&ht)?;
        let gd = self.mk("runs", vec![qd, w.clone(), self.mk("diverge", vec![tv.clone()])]);
        let d0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hts), R::S(hv.clone())], vec![], false)), kd), &gd, &[])?;
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
        // (also for simp(L): a result used as a pointer, its word)
        for h in &hs_after[1..] {
            let hf = self.assume(h)?;
            st0.facts.push(hf.clone());
            st0.lfx.push(hf);
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
        let rest = self.prove_pt(st2)?;
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
                    self.nobp_below(&self.bkp.clone()),
                ],
            ),
            &[],
        )
    }

    /// An equation by arith over the definitions defs, its sides' largest
    /// common parts made variables first (in omega: shown of them by simp)
    /// -- their insides arith need not unfold; as it is when there are none,
    /// or that fails
    pub(super) fn arith_gen(&mut self, goal: &Term, defs: &[&str]) -> Result<Seq, String> {
        let ds: Vec<String> = defs.iter().map(|d| d.to_string()).collect();
        let plain = |g: &mut Gen| g.evp(&RP::Defs(Box::new(RP::Arith(vec![])), ds.clone()), goal, &[]);
        let ge = self.expand(goal);
        let Some(x) = self.app(&ge, "eq", 2).map(|x| x.to_vec()) else { return plain(self) };
        let mut rset = std::collections::HashSet::new();
        fn all(t: &Term, out: &mut std::collections::HashSet<Term>) {
            if let Node::App(_, a) | Node::Var(_, a) = t.node() {
                if out.insert(t.clone()) {
                    a.iter().for_each(|y| all(y, out));
                }
            }
        }
        all(&x[1], &mut rset);
        let mut commons: Vec<Term> = Vec::new();
        fn find(t: &Term, top: bool, rs: &std::collections::HashSet<Term>, out: &mut Vec<Term>) {
            let Node::App(_, a) = t.node() else { return };
            if a.is_empty() {
                return;
            }
            if !top && rs.contains(t) {
                if !out.contains(t) {
                    out.push(t.clone());
                }
                return;
            }
            a.iter().for_each(|y| find(y, false, rs, out));
        }
        find(&x[0], true, &rset, &mut commons);
        // (not a constant: its value arith reads)
        commons.retain(|c| {
            let mut vs = Vec::new();
            c.vars(&mut vs);
            *c != x[1] && !vs.is_empty()
        });
        if commons.is_empty() {
            return plain(self);
        }
        let n = self.fresh("");
        let vars: Vec<Term> = (0..commons.len()).map(|i| self.var(&format!("AX{n}_{i}"))).collect();
        let map: std::collections::HashMap<Term, Term> = commons.iter().cloned().zip(vars.iter().cloned()).collect();
        fn repl(t: &Term, m: &std::collections::HashMap<Term, Term>) -> Term {
            if let Some(v) = m.get(t) {
                return v.clone();
            }
            match t.node() {
                Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => t.with_args(a.iter().map(|y| repl(y, m)).collect()),
                _ => t.clone(),
            }
        }
        let g2 = repl(&ge, &map);
        let omega = self.mk("omega", vec![]);
        let hs: Vec<Term> = vars.iter().map(|v| self.mk("in", vec![v.clone(), omega.clone()])).collect();
        let res = (|| -> Result<Seq, String> {
            let hseqs: Vec<R> = hs.iter().map(|h| self.assume(h).map(R::S)).collect::<Result<_, _>>()?;
            let pf = self.evp(&RP::Defs(Box::new(RP::Arith(hseqs)), ds.clone()), &g2, &[])?;
            let closed = self.close(pf, &hs, &vars.iter().map(Self::var_id).collect::<Vec<_>>())?;
            let mut args: Vec<RA> = commons.iter().map(t).collect();
            args.extend(commons.iter().map(|_| simp_l()));
            self.run(&mp(R::S(closed), args), &[])
        })();
        match res {
            Ok(s) => Ok(s),
            Err(e) => {
                self.trace(|| format!("arith_gen: {}", e));
                plain(self)
            }
        }
    }

    /// The rest after a loop's exit (st's spec the rest jk): the exit's
    /// world in it (the body's outcome's) as the rest's start world
    /// (tr.q_from)
    fn exit_rest(&mut self, st: St, jk: usize) -> Result<Seq, String> {
        let w = st.w.clone();
        let body = self.app(&self.qs[jk], "mkprog", 1).ok_or("the loop's rest: not a program")?[0].clone();
        // (the world by its name or expanded: W, the view)
        let we = self.expand(&w);
        let w = if self.mentions(&body, &we) { we } else { w };
        if !self.mentions(&body, &w) {
            return self.prove_kept(st);
        }
        let b = self.abstract_(&body, &w, 0);
        let (j2, r) = self.by(jk, "tr.q_from", &[("b", b), ("w", w)])?;
        let rs = self.run(&r, &[])?;
        let mut st2 = st.clone();
        st2.spec = Spec::Proc(j2);
        let rest = self.prove_kept(st2)?;
        let wr = self.wred(&st, jk, j2);
        self.run(&mp(wr, vec![s(&rs), s(&rest)]), &[])
    }

    /// the callee's states (below the frame) no breakpoints of bkp: a
    /// loop's head (`tr.hd(z) = pair(h, x) || ..`) by tr.nobp_hd, at the
    /// frame x itself; the rest likewise
    fn nobp_below(&self, bkp: &Term) -> RA {
        let hd = (|| {
            let o = self.app(bkp, "or", 2)?;
            let e = self.app(&o[0], "eq", 2)?;
            let z = self.app(&e[0], "tr.hd", 1)?;
            matches!(z[0].node(), Node::BVar(0)).then_some(())?;
            let pr = self.app(&e[1], "pair", 2)?;
            Some((pr[0].clone(), pr[1].clone(), o[1].clone()))
        })();
        // (a CFG's cut points, at the frame: `tr.cut(s, fr, ct, z) || ..`)
        let cut = (|| {
            let o = self.app(bkp, "or", 2)?;
            let c = self.app(&o[0], "tr.cut", 4)?;
            matches!(c[3].node(), Node::BVar(0)).then_some(())?;
            Some((c[0].clone(), c[1].clone(), c[2].clone(), o[1].clone()))
        })();
        if let Some((s0, fr, ct, outer)) = cut {
            return p(R::Mp(Box::new(R::Inst("tr.nobp_cut".into(), vec![("s", s0), ("fr", fr), ("ct", ct), ("bkp", outer.clone())])), vec![self.nobp_below(&outer)]));
        }
        match hd {
            Some((h, x, outer)) => p(R::Mp(Box::new(R::Inst("tr.nobp_hd".into(), vec![("bkp", outer.clone())])), vec![t(&x), t(&h), self.nobp_below(&outer)])),
            None => simp0(),
        }
    }

    /// a loop's head (the spec's loop there): its claim, by induction
    fn loop_point(&mut self, st: &St) -> Result<Option<Seq>, String> {
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        if self.loop_head(qi).is_none() {
            return Ok(None);
        }
        // (the readable CFG: its loop at the body's start, by tr.cfg_lvk)
        if self.cfg.is_none() && st.a == self.cfg_start {
            return self.cfg_function(st, qi).map(Some);
        }
        Ok(None)
    }

    /// the loop's claim at its head h for st's locals and world (c0): st's
    /// homes and registers, the claim's and more
    pub(super) fn loop_at(&mut self, st: &St, h: u128, c0: Seq) -> Result<Seq, String> {
        // (the point's homes and registers: the claim's, and more)
        let hs1 = self.app(c0.concl(), "tr.lv", 13).map(|x| x[8].clone()).ok_or("the loop's claim")?;
        let empty = self.mk("empty", vec![]);
        let mut sub_pf = mpf("tr.hsub_empty", vec![t(&st.hst)]);
        let mut fm = empty.clone();
        for (k, nb, x) in self.home_entries(&hs1).ok_or("the loop's claim's homes")? {
            let v = self.mk("pair", vec![lit(nb), x.clone()]);
            sub_pf = mpf("tr.hsub_upd", vec![t(&st.hst), t(&fm), t(&lit(k)), t(&v), p(sub_pf), simp_l(), simp_l()]);
            fm = self.upd(&fm, k, nb, &x);
        }
        let pcl = self.p(&st.spec);
        let c1 = self.run(
            &mpf(
                "tr.pt_hs",
                vec![
                    t(&self.s.clone()),
                    t(&self.v.clone()),
                    t(&self.base.clone()),
                    t(&self.code.clone()),
                    t(&lit(st.fr)),
                    t(&lit(h)),
                    t(&hs1),
                    t(&st.hst),
                    t(&st.ds),
                    t(&empty),
                    t(&pcl),
                    t(&st.w),
                    p(sub_pf),
                    s(&c0),
                ],
            ),
            &[],
        )?;
        let rs = mpf(
            "tr.pt_rs",
            vec![t(&self.s.clone()), t(&self.v.clone()), t(&self.base.clone()), t(&self.code.clone()), t(&lit(st.fr)), t(&lit(h)), t(&st.hst), t(&st.ds), t(&st.rs), t(&pcl), t(&st.w), s(&c1)],
        );
        self.run(&rs, &[])
    }

    /// Back at the loop's head in its iteration's walk: the arrival -- the
    /// rest reduced to the marked return of the next locals Y2, the homes
    /// at Y2 among st's (tr.pt_head)
    fn arrive(&mut self, st: &St, lg: &LoopG) -> Result<Seq, String> {
        self.fr = st.fr;
        self.w = st.w.clone();
        self.hvu = Some(st.hvu.clone());
        self.set_lf(st)?;
        let Spec::Proc(qi) = st.spec else { return Err(format!("{:x}: back at the loop's head after its result", st.a)) };
        // the reductions to the marked return
        let mut cur = qi;
        let mut steps: Vec<R> = Vec::new();
        let marker = |g: &Gen, q: &Term| -> Option<(Term, Term)> {
            let b = g.app(q, "mkprog", 1)?[0].clone();
            let x = g.app(&b, "eq", 2)?.to_vec();
            if !matches!(x[0].node(), Node::BVar(0)) {
                return None;
            }
            let o = g.app(&x[1], "ok", 2)?.to_vec();
            let pr = g.app(&o[1], "pair", 2)?.to_vec();
            let bf = g.env.binders_fn();
            (nat(&pr[0]) == Some(1u128 << 64) && o[0].loose_depth(&bf) == 0 && pr[1].loose_depth(&bf) == 0).then(|| (o[0].clone(), pr[1].clone()))
        };
        let mut n = 0;
        let (w2, y2) = loop {
            if let Some(m) = marker(self, &self.qs[cur].clone()) {
                break m;
            }
            n += 1;
            if n > 10000 {
                return Err(format!("{:x}: the iteration's rest does not end", st.a));
            }
            match self.reduce(cur, &st.hyps)? {
                Some(Red::Q(j, r)) => {
                    steps.push(r);
                    cur = j;
                }
                _ => return Err(format!("{:x}: back at the loop's head, the iteration's rest not its marked return: {}", st.a, self.print(&self.qs[cur]))),
            }
        };
        if self.canon(&w2) != self.canon(&st.w) {
            return Err(format!("{:x}: the iteration's marked return of another world", st.a));
        }
        let o = self.mk("ok", vec![st.w.clone(), self.mk("pair", vec![lit(1u128 << 64), y2.clone()])]);
        let goal = self.mk("runs", vec![self.qs[cur].clone(), st.w.clone(), o.clone()]);
        // (the locals in the universe: the iteration's)
        let mut rr = self.evp(&RP::Defs(Box::new(RP::Simp(true, vec![R::S(st.hvu.clone()), R::S(lg.hu.clone())], vec![], false)), vec!["runs".into(), "mkprog".into()]), &goal, &[])?;
        for stp in steps.into_iter().rev() {
            rr = self.run(&mp(stp, vec![t(&o), s(&rr)]), &[])?;
        }
        // (in the identity wrapper)
        let qb = self.app(&self.qs[qi], "mkprog", 1).ok_or("the iteration's rest")?[0].clone();
        let io = R::Apply(Box::new(f("tr.isout_ok")), vec![t(&st.w), t(&self.mk("pair", vec![lit(1u128 << 64), y2.clone()]))]);
        let rw = R::Apply(Box::new(R::Inst("tr.wrap_id_in".into(), vec![("r", qb)])), vec![t(&st.w), t(&o), s(&rr), p(io)]);
        // the homes at Y2 among st's
        let hs2 = lg.hs.instantiate_params(std::slice::from_ref(&y2), &self.env.binders_fn());
        let mut sub_pf = mpf("tr.hsub_empty", vec![t(&st.hst)]);
        let mut fm = self.mk("empty", vec![]);
        for (k, nb, x) in self.home_entries(&hs2).ok_or("the loop's homes")? {
            let v = self.mk("pair", vec![lit(nb), x.clone()]);
            sub_pf = mpf("tr.hsub_upd", vec![t(&st.hst), t(&fm), t(&lit(k)), t(&v), p(sub_pf), simp_l(), simp_l()]);
            fm = self.upd(&fm, k, nb, &x);
        }
        let inst = R::Inst(
            "tr.pt_head".into(),
            vec![
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("ha", lit(lg.head)),
                ("fd", lg.fd.clone()),
                ("hs", lg.hs.clone()),
                ("yt", lg.yt.clone()),
                ("bkp", lg.bkp.clone()),
            ],
        );
        let pcl = self.p(&st.spec);
        self.trace(|| format!("loop at {:x}: arrived", st.a));
        let r = mp(inst, vec![t(&st.hst), t(&st.rs), t(&pcl), t(&st.w), t(&y2), p(sub_pf), simp_lw(vec![R::S(st.hvu.clone()), R::S(lg.hu.clone())]), simp_lw(vec![R::S(lg.hy.clone())]), p(rw)]);
        // (more of the frame here than at the head: the claim with the head's)
        if self.canon(&st.ds) == self.canon(&lg.fd) {
            return self.run(&r, &[]);
        }
        let args = vec![
            t(&self.s.clone()),
            t(&self.v.clone()),
            t(&self.base.clone()),
            t(&self.code.clone()),
            t(&lit(st.fr)),
            t(&lit(st.a)),
            t(&st.hst),
            t(&st.ds),
            t(&lg.fd),
            t(&st.rs),
            t(&pcl),
            t(&st.w),
            simp0(),
            simp0(),
            arith(vec![]),
            arith(vec![]),
            arith(vec![]),
            p(r),
        ];
        self.run(&mpf("tr.pt_fd", args), &[])
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

    /// a premise that no state there is a breakpoint (an address no loop's
    /// head of the walk; a callee's states, below the frame): by its form
    pub(super) fn nobp(&self) -> RA {
        defs(RP::Simp(false, vec![], vec![], false), &["tr.hd", "tr.cut"])
    }

    /// the claim reaching st's point (no breakpoint) from the claim leaving it
    pub(super) fn to_pt(&mut self, st: &St, lv: Seq) -> Result<Seq, String> {
        let args = vec![
            t(&self.s.clone()),
            t(&self.v.clone()),
            t(&self.base.clone()),
            t(&self.code.clone()),
            t(&lit(st.fr)),
            t(&lit(st.a)),
            t(&st.hst),
            t(&st.ds),
            t(&st.rs),
            t(&self.p(&st.spec)),
            t(&st.w),
            self.nobp(),
            s(&lv),
        ];
        self.run(&mpf("tr.lv_pt", args), &[])
    }

    /// the claim reaching st's point: the walk's from there (leaving it), or
    /// in a zero-initialization its own (`tr.ptz`)
    pub(super) fn prove_pt(&mut self, st2: St) -> Result<Seq, String> {
        if st2.z.is_some() {
            return self.prove_kept(st2);
        }
        // (a CFG walk at a cut point: its arrival)
        if self.cfg.as_ref().is_some_and(|c| c.cuts.contains(&st2.a)) && self.lpg.as_ref().is_some_and(|l| l.head == u128::MAX) {
            let c = self.save();
            let r = self.cfg_arrive(&st2);
            self.restore(c);
            match r? {
                Some(pf) => return Ok(pf),
                None => return Err(format!("{:x}: a cut point (a block's start), the spec not at a block's end: {}", st2.a, self.print(&self.p(&st2.spec)))),
            }
        }
        // (back at the head of the loop walked: its arrival)
        if let Some(lg) = self.lpg.clone() {
            if st2.a == lg.head {
                let c = self.save();
                let r = self.arrive(&st2, &lg);
                self.restore(c);
                return r;
            }
        }
        let lv = self.prove_kept(st2.clone())?;
        self.to_pt(&st2, lv)
    }

    /// a linear step: the rule's instance (the slot `NEXT` the next point's
    /// claim), the state after
    pub(super) fn then(&mut self, r: R, st2: St) -> Result<Seq, String> {
        self.then_x(r, st2, true)
    }

    /// ... the next state at the same point (its claim leaving it)
    pub(super) fn then_lv(&mut self, r: R, st2: St) -> Result<Seq, String> {
        self.then_x(r, st2, false)
    }

    fn then_x(&mut self, r: R, st2: St, reached: bool) -> Result<Seq, String> {
        let a2 = st2.a;
        let (rs2, regs2) = (st2.rs.clone(), st2.regs.clone());
        let rest = if reached { self.prove_pt(st2)? } else { self.prove_kept(st2)? };
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
        Ok(Some(self.then_lv(rule, st2)?))
    }

    /// a branch on c: on to a3 when c, to t when not (the rule's slots `T`,
    /// `F` the two)
    pub(super) fn branch(&mut self, st: &St, c: Term, a3: u128, tt: u128, rule: R) -> Result<Seq, String> {
        let nc = self.mk("not", vec![c.clone()]);
        let mut bs = Vec::new();
        for (cond, to) in [(c.clone(), a3), (nc, tt)] {
            let mut st2 = st.clone();
            st2.a = to;
            st2.splits.push(self.split(st));
            let hn = self.assume(&cond)?;
            // (a branch its earlier tests exclude: by their contradiction)
            let opp = match self.app(&cond, "not", 1) {
                Some(x) => x[0].clone(),
                None => self.mk("not", vec![cond.clone()]),
            };
            // (or a literal comparison false: by simp; a closed condition
            // false: by its negation evaluated)
            let lit_false = self.lit_value(&self.canon(&cond)) == Some(false);
            let closed_false = if lit_false { None } else { self.eval_closed(&opp) };
            let body = if let Some(h) = self.hyp_find(&st.hyps, &opp) {
                let goal = self.pt(&st2, to);
                self.evp(&RP::Taut(vec![R::S(hn), R::S(h.1.clone())]), &goal, &[])?
            } else if let Some(o) = closed_false {
                let goal = self.pt(&st2, to);
                self.evp(&RP::Taut(vec![R::S(hn), R::S(o)]), &goal, &[])?
            } else if lit_false {
                let goal = self.pt(&st2, to);
                self.evp(&RP::Simp(false, vec![R::S(hn)], vec![], false), &goal, &[])?
            } else {
                st2.bconds.push(st2.hyps.len());
                st2.hyps.push((cond.clone(), hn));
                self.prove_pt(st2)?
            };
            bs.push(self.close(body, &[cond], &[])?);
        }
        let fb = bs.pop().unwrap();
        let tb = bs.pop().unwrap();
        self.run(&rule, &[("T", tb), ("F", fb)])
    }

    /// a closed condition (no variables) true by evaluation: its proof
    fn eval_closed(&self, c: &Term) -> Option<Seq> {
        let e = self.expand(c);
        let mut vs = Vec::new();
        e.vars(&mut vs);
        if !vs.is_empty() || e.loose_depth(&self.env.binders_fn()) > 0 {
            return None;
        }
        let lg = &self.api.as_ref()?.lg;
        let r = Seq::eval_goal(self.env, lg, &[], &e);
        self.trace(|| format!("eval_closed {}: {}", self.print(&e), r.as_ref().map(|_| "true".to_string()).unwrap_or_else(|x| x.0.clone())));
        r.ok()
    }

    /// a condition's value where it is a comparison of literals (or of a
    /// term with itself), under negations
    fn lit_value(&self, c: &Term) -> Option<bool> {
        if let Some(x) = self.app(c, "not", 1) {
            return self.lit_value(&x[0]).map(|v| !v);
        }
        let y = self.app(c, "eq", 2)?;
        if y[0] == y[1] {
            return Some(true);
        }
        match (y[0].node(), y[1].node()) {
            (Node::Nat(p), Node::Nat(q)) => Some(p == q),
            _ => None,
        }
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

    /// A compare at a and the conditional jump after it
    /// (proofs/translate_flags.core): the compare's flags step (`tr.FS` at
    /// the operands ts, its n literal premises), the condition code's lemma
    /// on its flags (the fall-through's condition c), the jump (tr.jcc) --
    /// both branches walked
    #[allow(clippy::too_many_arguments)]
    pub(super) fn compare(&mut self, st: &St, a: u128, a2: u128, insn: &Insn, fs: &str, ts: &[&Term], n: usize, fl: Flags) -> Result<Seq, String> {
        let (j, len2, a3, tt, cc) = self.jcc(a2)?;
        let mut v = vec![t(&self.s), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(insn.len))];
        v.extend(ts.iter().map(|x| t(x)));
        v.extend([t(&st.hst), t(&st.rs), t(&st.w), p(f(&insn.name))]);
        v.extend((0..n).map(|_| simp_l()));
        let step = mpf(&format!("tr.{fs}"), v);
        let si = |g: &Gen, x: &Term| g.mk("sint", vec![lit(32), x.clone()]);
        let (lemma, c, args, ff) = match &fl {
            Flags::Sub(w, x, y) => {
                let (l, c) = match (cc, *w) {
                    (4, _) => ("ccs_e", self.mk("not", vec![self.mk("eq", vec![x.clone(), y.clone()])])),
                    (5, _) => ("ccs_ne", self.mk("eq", vec![x.clone(), y.clone()])),
                    (2, _) => ("ccs_b", self.mk("int_le", vec![y.clone(), x.clone()])),
                    (3, _) => ("ccs_ae", self.mk("int_lt", vec![x.clone(), y.clone()])),
                    (6, _) => ("ccs_be", self.mk("int_lt", vec![y.clone(), x.clone()])),
                    (7, _) => ("ccs_a", self.mk("int_le", vec![x.clone(), y.clone()])),
                    (12, 32) => ("ccs32_l", self.mk("int_le", vec![si(self, y), si(self, x)])),
                    (13, 32) => ("ccs32_ge", self.mk("int_lt", vec![si(self, x), si(self, y)])),
                    (14, 32) => ("ccs32_le", self.mk("int_lt", vec![si(self, y), si(self, x)])),
                    (15, 32) => ("ccs32_g", self.mk("int_le", vec![si(self, x), si(self, y)])),
                    // (jns after a compare with 0: x's sign, as GIMPLE writes
                    // `x <s 0`; else x - y's)
                    (9, 32) if nat(y) == Some(0) => ("ccs32_ns0", self.mk("int_lt", vec![si(self, x), si(self, y)])),
                    (9, 32) => ("ccs32_ns", self.mk("int_lt", vec![si(self, &self.mk("bits_sub", vec![lit(32), x.clone(), y.clone()])), lit(0)])),
                    _ => return Err(format!("{:x}: a {}-bit compare's jump on condition {}: no lemma", a, w, cc)),
                };
                // (ccs32_ns0: no y, a compare with 0)
                let args = if l == "ccs32_ns0" { vec![lit(*w), x.clone()] } else { vec![lit(*w), x.clone(), y.clone()] };
                (l, c, args, self.mk("x86i.subf", vec![lit(*w), x.clone(), y.clone(), Term::bvar(0)]))
            }
            Flags::Log(w, r) => {
                let z = self.mk("eq", vec![r.clone(), lit(0)]);
                let (l, c) = match cc {
                    4 => ("ccl_e", self.mk("not", vec![z])),
                    5 => ("ccl_ne", z),
                    _ => return Err(format!("{:x}: a test's jump on condition {}: no lemma", a, cc)),
                };
                (l, c, vec![lit(*w), r.clone()], self.mk("x86i.logf", vec![lit(*w), r.clone(), Term::bvar(0)]))
            }
        };
        let mut ca: Vec<RA> = args.iter().map(t).collect();
        ca.push(defs(RP::Simp(false, vec![], vec![], false), &["tr.width"]));
        let ccf = mpf(&format!("tr.{lemma}"), ca);
        // (the jump's row and displacement width: 127 / 8, 128 / 32)
        let (jn, jw) = if self.insns[&a2].row == 128 { (128, 32) } else { (127, 8) };
        let mut jv = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(a3)), t(&lit(tt))];
        jv.extend([t(&lit(len2)), t(&lit(jn)), t(&lit(jw)), t(&lit(cc)), t(&j), t(&c), t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w)]);
        jv.extend([p(step), p(ccf), p(f(&self.insns[&a2].name))]);
        jv.extend((0..6).map(|_| simp_l()));
        jv.extend([self.nobp(), p(R::Slot("T")), p(R::Slot("F"))]);
        let rule = mp(R::Inst("tr.jcc".into(), vec![("ff", ff)]), jv);
        self.branch(st, c, a3, tt, rule)
    }

    /// the statics' variable
    pub(super) fn statics_var(&self) -> Term {
        let v = self.names.iter().find(|x| x.0 == "statics").expect("statics").1;
        Term::var(v, vec![])
    }
}
