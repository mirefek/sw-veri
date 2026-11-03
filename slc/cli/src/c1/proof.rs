//! The point claims: their proofs at each address, by the spec's
//! reductions, the instructions' rules, branches, calls and loops.

use super::rec::*;
use super::*;

/// A statement the spec makes and the code implements by a call (a zero
/// store by memset's): the callee's contract, typing and returns' effects,
/// the statement, the proofs of its runs' inclusion and of the breakpoints'
/// relation kept (tr.call0_stb's last premises)
#[derive(Clone)]
pub(super) struct LibCall {
    hcall: Seq,
    htyp: Seq,
    hio: Seq,
    stmt: Term,
    incl: RA,
    bka: RA,
}

/// the context a point's recipes evaluate in (restored after a recursion)
struct Ctx {
    fr: u128,
    w: Term,
    hvu: Option<Seq>,
    hww: Option<Seq>,
    lf: Vec<Seq>,
}


/// The rules keeping the homes past the spec's store (their first premise
/// `tr.hapart`)
const HAPART: &[&str] = &[
    "store8i_rip", "store32i_rip", "store64i_rip", "store8_rip", "store8_bi", "store8i_bi", "store8_b", "store8i_b", "store32_b", "store16_b", "store64_bd",
    "store64i_bd", "store32i_bd", "store16i_bd", "store64_rip", "store32_rip", "store_reg_step", "cas32_b", "or32_b", "store32_bd", "store32_bd_eq", "store8_bd", "store16_bd",
    "store64_bd_eq", "store64_bi", "movsb", "rep_movsq", "rep_stosq", "store32_bd_w", "store8_bid", "store16_bid", "store32_bid", "store64_bid", "store64_rsib", "store32i_rsp",
    "store32_rip_w", "store64_bd_a",
];
impl<'e> Gen<'e> {
    fn save(&self) -> Ctx {
        Ctx { fr: self.fr, w: self.w.clone(), hvu: self.hvu.clone(), hww: self.hww.clone(), lf: self.lf.clone() }
    }

    fn restore(&mut self, c: Ctx) {
        self.fr = c.fr;
        self.w = c.w;
        self.hvu = c.hvu;
        self.hww = c.hww;
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
            _ if so.or.is_some() => mpf(
                "tr.or32_at_ok",
                vec![t(&w), t(&so.p), t(so.or.as_ref().unwrap()), t(&so.addr), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), simp_l(), simp_l(), simp_l(), s(&hc)],
            ),
            (Some(d), _) => mpf(
                "tr.stzero_at_ok",
                vec![t(&w), t(&so.p), t(&so.off), t(d), t(&so.addr), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), simp_l(), simp_l(), simp_l(), simp_l(), s(&hc)],
            ),
            (None, None) => mpf(
                &format!("tr.st{}_{}_ok", 8 * n, if so.soff { "s" } else { "at" }),
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

    /// The spec's move at the machine's movs (a string instruction: its
    /// destination d, source s, bytes n): its condition's proof, the state
    /// after it (the world with the n bytes at s stored at d), the
    /// reduction across it
    pub(super) fn spec_move(&mut self, st: &St, dst: &Term, src: &Term, n: &Term) -> Result<(Seq, St, R), String> {
        let Spec::Proc(qi) = st.spec else { return Err(format!("{:x}: a move after the procedure's result", st.a)) };
        let q = self.qs[qi].clone();
        let badm = format!("{:x}: a move the spec does not make here (its rest: {})", st.a, self.print(&q));
        let bad = || badm.clone();
        let body = self.app(&q, "mkprog", 1).ok_or_else(bad)?[0].clone();
        let ex = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())).ok_or_else(bad)?;
        let (a, k) = (ex[0].clone(), ex[1].clone());
        let x = self.app(&a, "bind_rel", 5).ok_or_else(bad)?.to_vec();
        let (md, ms, mn, cond, _, okr) = self.move_op(&x[0]).ok_or_else(bad)?;
        for (what, m, c) in [("destination", &md, dst), ("source", &ms, src), ("size", &mn, n)] {
            if self.canon(m) != self.canon(c) {
                return Err(format!("{:x}: the move's {}: the machine's {}, the spec's {}", st.a, what, self.print(c), self.print(m)));
            }
        }
        let hc = self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()).ok_or_else(bad)?;
        let ctx = ["x0", "x1", "x8"];
        let kl = self.lam(&k, &ctx, &["x8", "x1"]).ok_or("a block's rest reads the world")?;
        let c5 = ["x0", "x1", "x8", "x9", "x10"];
        let al = self.lam(&x[2], &c5, &["x9", "x10", "x8"]).ok_or("a move's continuation reads the world before it")?;
        let xl = self.lam(&x[3], &c5, &["x9", "x10", "x8"]).ok_or("a move's handler reads the world before it")?;
        let dl = self.lam(&x[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("a move's handler reads the world before it")?;
        // the world after it
        let wn2 = self.fresh("W");
        let w2 = self.var(&wn2);
        let w = st.w.clone();
        let vm = self.mk("app", vec![w.clone(), Term::bytes(b"vm")]);
        let bytes = self.mk("app", vec![vm.clone(), Term::bytes(b"bytes")]);
        // (the value stored: a move's bytes read at its source; a fill's
        // words, x86.fillv)
        let v = match self.app(&x[0], "musl_asm.fill_words", 3).map(|y| y.to_vec()) {
            Some(y) => self.mk("x86.fillv", vec![ms.clone(), y[2].clone()]),
            None => self.mk("gimple.bytes_at", vec![vm.clone(), ms.clone(), mn.clone()]),
        };
        let stored = self.mk("x86_64_linux.store_le", vec![bytes, md.clone(), mn.clone(), v.clone()]);
        let w2term = self.mk("fn_update", vec![w.clone(), Term::bytes(b"vm"), self.mk("fn_update", vec![vm, Term::bytes(b"bytes"), stored])]);
        let weq = self.push_world(Self::var_id(&w2), w2term, &w);
        let hw2 = self.run(&R::Apply(Box::new(f("tr.world_store")), vec![t(&w), t(&md), t(&mn), t(&v), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]), simp_l()]), &[])?;
        let hw2 = match &weq {
            Some(eq) => self.world_conv(hw2, eq)?,
            None => hw2,
        };
        let w2u = self.mk("in", vec![w2.clone(), self.mk("univ", vec![lit(1)])]);
        let hv2 = self.evp(&RP::Taut(vec![R::S(hw2.clone())]), &w2u, &[])?;
        // the move's run: ok, to the world after
        let hww = self.evp(&RP::Taut(vec![R::S(st.hw.clone())]), &self.mk("in", vec![w.clone(), self.mk("abi.World", vec![])]), &[])?;
        let ok = self.run(&okr, &[("HWW", hww), ("HWU", st.hvu.clone()), ("HC", hc.clone())])?;
        let ok = match &weq {
            Some(eq) => R::S(self.world_conv(ok, eq)?),
            None => R::S(ok),
        };
        let empty = self.mk("empty", vec![]);
        let (j, inst) = self.by(qi, "tr.qs_opw", &[("op", x[0].clone()), ("r", empty), ("a", al), ("xx", xl), ("dd", dl), ("k", kl)])?;
        let qred = mp(inst, vec![t(&w), t(&w2), s(&st.hvu), p(ok)]);
        let wredw = R::Inst("tr.wredw".into(), vec![("w", w.clone()), ("w2", w2.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone()), ("kw", self.kw3())]);
        let red = R::S(self.run(&mp(wredw, vec![s(&st.hvu), p(qred)]), &[])?);
        let mut st2 = st.clone();
        st2.w = w2;
        st2.hvu = hv2;
        st2.hw = hw2;
        st2.spec = Spec::Proc(j);
        Ok((hc, st2, red))
    }

    /// The frame's stack object allocated (`Red::Alloc`, the rest qi) at
    /// the machine's first store to it, `mov [rsp + d], r64` (tr.astore_r):
    /// the spec's allocation there, the object's bytes the stored word (any,
    /// as alloc_objs makes them); the claim on from it with the object
    /// (`tr.vone` assumed). None: not that store.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn alloc_at(&mut self, st: &St, qi: usize, op: &Term, al: &Term, xl: &Term, dl: &Term, kl: &Term) -> Result<Option<Seq>, String> {
        let Some(insn) = self.insns.get(&st.a).cloned() else { return Ok(None) };
        if insn.row != 75 {
            return Ok(None);
        }
        let Some(x) = self.pairs(&insn.fields, 5) else { return Ok(None) };
        let (Some(d), Some(8), Some(g)) = (self.rsp_mem(&x[2]), nat(&x[0]), nat(&x[1])) else { return Ok(None) };
        let Some(dn) = nat(&d) else { return Ok(None) };
        let c = self.hkey(dn);
        if !self.objk.contains(&c) {
            return Ok(None);
        }
        let a = st.a;
        if self.objk.len() != 1 || self.hvo.is_some() {
            return Err(format!("{:x}: more than one stack object (not yet)", a));
        }
        let a2 = (a + insn.len) % P64;
        let Some((8, u)) = self.reg(st, g) else { return Err(format!("{:x}: the object's first store not of a register's word", a)) };
        let s0 = self.s.clone();
        let ha = self.mk("tr.ha", vec![s0.clone(), lit(c)]);
        let w = st.w.clone();
        let vm = self.mk("app", vec![w.clone(), Term::bytes(b"vm")]);
        let bytes = self.mk("app", vec![vm.clone(), Term::bytes(b"bytes")]);
        let stored = self.mk("x86_64_linux.store_le", vec![bytes, ha.clone(), lit(8), u.clone()]);
        let objs = self.mk("app", vec![w.clone(), Term::bytes(b"objs")]);
        let w1 = self.mk("fn_update", vec![w.clone(), Term::bytes(b"vm"), self.mk("fn_update", vec![vm, Term::bytes(b"bytes"), stored])]);
        // (alloc_objs grows the live objects: `objs with { live: .. }`)
        let live = self.mk("app", vec![objs.clone(), Term::bytes(b"live")]);
        let objs2 = self.mk("fn_update", vec![objs, Term::bytes(b"live"), self.mk("tr.obj1s", vec![live, ha.clone()])]);
        let w2term = self.mk("fn_update", vec![w1, Term::bytes(b"objs"), objs2.clone()]);
        let wn2 = self.fresh("W");
        let w2 = self.var(&wn2);
        let weq = self.push_world(Self::var_id(&w2), w2term, &w);
        let hab = simp_l();
        let hw2 = self.run(&R::Apply(Box::new(f("tr.world_alloc")), vec![t(&w), t(&ha), t(&u), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]), hab.clone()]), &[])?;
        let hw2 = match &weq {
            Some(eq) => self.world_conv(hw2, eq)?,
            None => hw2,
        };
        let w2u = self.mk("in", vec![w2.clone(), self.mk("univ", vec![lit(1)])]);
        let hv2 = self.evp(&RP::Taut(vec![R::S(hw2.clone())]), &w2u, &[])?;
        // the allocation's run: the object's bytes outside the world's
        // domain, its slot aligned (tr.astore_r's, of the machine)
        let asl_t = self.mk("tr.aslot", vec![s0.clone(), lit(c)]);
        let nd_t = self.mk("tr.nodom", vec![w.clone(), ha.clone(), lit(8)]);
        let hasl = self.assume(&asl_t)?;
        let hnd = self.assume(&nd_t)?;
        let okr = self.run(
            &mpf(
                "tr.alloc1_run",
                vec![t(&w), t(&ha), t(&u), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]), hab.clone(), taut(vec![R::S(hasl.clone())]), taut(vec![R::S(hasl.clone())]), taut(vec![R::S(hasl)]), s(&hnd)],
            ),
            &[],
        )?;
        let okr = match &weq {
            Some(eq) => self.world_conv(okr, eq)?,
            None => okr,
        };
        let res = self.mk("seq_one", vec![ha.clone()]);
        let (j, inst) = self.by(qi, "tr.qs_opw", &[("op", op.clone()), ("r", res), ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone())])?;
        let qred = mp(inst, vec![t(&w), t(&w2), s(&st.hvu), s(&okr)]);
        let wredw = R::Inst("tr.wredw".into(), vec![("w", w.clone()), ("w2", w2.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone()), ("kw", self.kw3())]);
        let red = self.run(&mp(wredw, vec![s(&st.hvu), p(qred)]), &[])?;
        let red = self.close(red, &[asl_t, nd_t], &[])?;
        // the homes left (the object's bytes no home)
        let (kept, hs2, hk) = self.hkeep(st, c, 8);
        // the claim after it, with the object (tr.vone assumed)
        let v0 = self.v.clone();
        let vn = self.mk("tr.obj1", vec![v0.clone(), ha.clone()]);
        let vone_t = self.mk("tr.vone", vec![s0.clone(), vn.clone(), v0.clone(), lit(c)]);
        let hvo = self.assume(&vone_t)?;
        let mut st2 = st.clone();
        st2.a = a2;
        st2.w = w2.clone();
        st2.hvu = hv2;
        st2.hw = hw2.clone();
        st2.spec = Spec::Proc(j);
        st2.hst = hs2.clone();
        st2.hsm = kept;
        self.trace(|| format!("at {:x}: the stack object at {} allocated", a, self.print(&ha)));
        self.v = vn;
        self.hvo = Some((v0.clone(), c, hvo));
        self.objw = Some((w2.clone(), w.clone(), ha.clone(), u.clone(), objs2, weq.clone(), st.hw.clone()));
        let rest = self.prove_pt(st2);
        self.v = v0;
        self.hvo = None;
        self.objw = None;
        let rest = self.close(rest?, &[vone_t], &[])?;
        // the step
        let mut args = self.head(a, &insn);
        args.extend([&x[1], &d, &lit(c), &x[3], &x[4], &u].into_iter().map(t));
        let p2 = self.wrap_of(&self.qs[j].clone());
        args.extend([&st.hst, &hs2, &st.ds, &st.rs, &self.p(&st.spec), &p2, &w, &w2].into_iter().map(t));
        args.push(p(f(&insn.name)));
        args.extend((0..5).map(|_| simp_l()));
        args.push(simp_lw(self.facts_about(&st.facts, &u)));
        args.extend([simp_l(), simp_l(), defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]), simp_l(), simp_l(), simp_l()]);
        args.push(p(hk));
        args.push(p(self.hva_r()));
        args.push(match &weq {
            Some(eq) => p(eq.clone()),
            None => simp0(),
        });
        args.push(simp_l());
        args.push(taut(vec![R::S(hw2.clone())]));
        args.push(taut(vec![R::S(hw2)]));
        args.push(s(&red));
        args.push(s(&rest));
        self.run(&mpf("tr.astore_r", args), &[]).map(Some)
    }

    /// `tr.lv_red` at st, from the program qi to j (rs: j's runs are qi's),
    /// the claim on j `rest`
    fn lv_red_plain(&mut self, st: &St, qi: usize, j: usize, rs: Seq, rest: Seq) -> Result<Seq, String> {
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
            t(&self.qs[qi].clone()),
            t(&self.qs[j].clone()),
            t(&st.w),
            s(&rs),
            s(&rest),
        ];
        self.run(&mpf("tr.lv_red", args), &[])
    }

    /// the program qi a block of the procedure's call alone, `mkprog(x0 x1.
    /// ex x8. bind_rel(PROC(..), x0, ..) && x1 = x8)`: its head the program
    /// (tr.qs_outro)
    fn outro_at(&mut self, qi: usize) -> Result<Option<Red>, String> {
        let Some(ps) = self.reroot else { return Ok(None) };
        let q = self.qs[qi].clone();
        let Some(body) = self.app(&q, "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some(ex) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else { return Ok(None) };
        let Some(e) = self.app(&ex[1], "eq", 2) else { return Ok(None) };
        if !(matches!(e[0].node(), Node::BVar(1)) && matches!(e[1].node(), Node::BVar(0))) {
            return Ok(None);
        }
        let Some(br) = self.app(&ex[0], "bind_rel", 5) else { return Ok(None) };
        if !matches!(br[0].node(), Node::App(f, _) if *f == ps) {
            return Ok(None);
        }
        let Some(a) = self.lam(&ex[0], &["x0", "x1", "x8"], &["x0", "x8"]) else { return Ok(None) };
        let (j, inst) = self.by(qi, "tr.qs_outro", &[("a", a)])?;
        Ok(Some(Red::Q(j, mp(inst, vec![t(&self.w.clone())]))))
    }

    /// the program qi the procedure's call, `mkprog(x1 x2. bind_rel(PROC(..),
    /// x1, KW, ..))` (Spec::Plain): KW the walk's wrapper from here, the
    /// call's rest PROC(..)
    fn reroot_at(&mut self, qi: usize) -> Result<Option<usize>, String> {
        let Some(ps) = self.reroot else { return Ok(None) };
        let q = self.qs[qi].clone();
        let Some(body) = self.app(&q, "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some(br) = self.app(&body, "bind_rel", 5).map(|x| x.to_vec()) else { return Ok(None) };
        if !matches!(br[0].node(), Node::App(f, _) if *f == ps) || !matches!(br[1].node(), Node::BVar(1)) {
            return Ok(None);
        }
        let kw = self.lam(&br[2], &["x1", "x2", "x3", "x4"], &["x3", "x4", "x2"]).ok_or("the wrapper after the procedure's call reads its start")?;
        let q_t = self.var("q");
        let mut wa = vec![q_t.clone()];
        wa.extend(br[1..].iter().cloned());
        let wrap = self.mk("mkprog", vec![self.mk("bind_rel", wa)]);
        self.kw = kw;
        self.wrap = self.abs(&wrap, &[Self::var_id(&q_t)]);
        self.reroot = None;
        let j = self.new_q(br[0].clone());
        let back = self.wrap_of(&self.qs[j].clone());
        if self.expand(&back) != self.expand(&q) {
            return Err(format!("the procedure's call: its wrapper does not give the program back:\n  {}\n  {}", self.print(&back), self.print(&q)));
        }
        Ok(Some(j))
    }

    /// `tr.wred` at st, from the rest qi to j
    fn wred(&self, st: &St, qi: usize, j: usize) -> R {
        // (the flags kept: tr.wred_f, of their ff)
        let (name, ff) = match &st.fk {
            Some(fl) => ("tr.wred_f", Some(self.ff_term(fl))),
            None => ("tr.wred", None),
        };
        R::Inst(
            name.into(),
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
            ]
            .into_iter()
            .chain(ff.map(|f| ("ff", f)))
            .collect(),
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
                Spec::Plain(i) => format!("plain q{}: {}", i, Printer::new(self.env).short(&self.qs[*i])),
                Spec::Ret(_, pr) => format!("ret: {}", Printer::new(self.env).short(pr)),
            };
            format!("point {:x} spec {}", st.a, q)
        });
        self.fr = st.fr;
        self.w = st.w.clone();
        self.hvu = Some(st.hvu.clone());
        self.hww = Some(st.hw.clone());
        self.set_lf(&st)?;
        if let Some(pf) = self.loop_point(&st)? {
            return Ok(pf);
        }
        // (the rest undefined -- after a call never returning: it raises
        // nothing in the point's world; any claim, tr.raise0_ub)
        if let Spec::Proc(qi) = st.spec {
            let raise0 = (|| {
                let b = self.app(&self.qs[qi], "mkprog", 1)?[0].clone();
                let e = self.app(&b, "eq", 2)?;
                let x = self.app(&e[1], "exc", 2)?;
                (matches!(e[0].node(), Node::BVar(0)) && matches!(x[0].node(), Node::BVar(1)) && self.app(&x[1], "empty", 0).is_some()).then_some(())
            })();
            if raise0.is_some() {
                let inst = R::Inst("tr.raise0_ub".into(), vec![("kw", self.kw3()), ("bkp", self.bkp.clone()), ("bka", self.bka.clone())]);
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
                    t(&st.w),
                    taut(vec![R::S(st.hw.clone())]),
                    taut(vec![R::S(st.hw.clone())]),
                ];
                self.trace(|| format!("at {:x}: undefined (the rest raises nothing)", st.a));
                return self.run(&mp(inst, args), &[]);
            }
        }
        // (in a zero-initialization: the machine's stores only, the spec's made)
        if st.z.is_some() {
            return self.insn(st);
        }
        // a wrapper's part before the procedure's call: the claim on the
        // program itself, reduced (tr.lv_red, tr.psplit); at the call, the
        // walk's wrapper its rest (the same claim)
        if let Spec::Plain(qi) = st.spec {
            if let Some(j) = self.reroot_at(qi)? {
                let mut st2 = st.clone();
                st2.spec = Spec::Proc(j);
                self.trace(|| format!("at {:x}: the procedure's call, its wrapper the walk's", st.a));
                return self.prove(st2);
            }
            self.picked.borrow_mut().clear();
            let red = match self.outro_at(qi)? {
                Some(r) => Some(r),
                None => self.reduce(qi, &st.hyps)?,
            };
            return match red {
                Some(Red::Q(j, r)) => {
                    let rs = self.run(&r, &[])?;
                    let mut st2 = st.clone();
                    st2.spec = Spec::Plain(j);
                    let rest = self.prove_kept(st2)?;
                    self.lv_red_plain(&st, qi, j, rs, rest)
                }
                Some(Red::Split { cond, ok, ub }) => {
                    let u = self.raise_when_not(&cond, &ub)?;
                    let hc = self.assume(&cond)?;
                    let okr = self.run(&ok.1, &[("HC", hc.clone())])?;
                    let mut st2 = st.clone();
                    st2.spec = Spec::Plain(ok.0);
                    st2.hyps.push((cond.clone(), hc));
                    let rest = self.prove_kept(st2)?;
                    let body = self.lv_red_plain(&st, qi, ok.0, okr, rest)?;
                    let d = self.close(body, &[cond.clone()], &[])?;
                    self.psplit_at(&st, qi, &cond, u, d)
                }
                _ => Err(format!("{:x}: the wrapper before the procedure's call: {}", st.a, self.print(&self.qs[qi]))),
            };
        }
        if let Spec::Proc(qi) = st.spec {
            // (the branch conditions spent: not to choose between an `if`'s
            // alternatives)
            *self.spent_now.borrow_mut() = st.spent.iter().map(|&i| self.expand(&st.hyps[i].0)).collect();
            self.picked.borrow_mut().clear();
            if let Some(pf) = self.req_ub(&st, qi)? {
                return Ok(pf);
            }
            let red = self.reduce(qi, &st.hyps)?;
            // (the flags kept: the rest's plain reductions only, tr.wred_f)
            if st.fk.is_some() && !matches!(red, None | Some(Red::Q(..))) {
                return Err(format!("{:x}: the flags of a compare kept, the spec's rest not reduced plainly here: {}", st.a, self.print(&self.qs[qi])));
            }
            match red {
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
                Some(Red::Call { g, args, list, one, stk, a, xx, dd, k }) => {
                    if matches!(self.insns.get(&st.a).map(|i| i.row), Some(120 | 121)) {
                        return self.call_at(&st, qi, g, &args, list, one, stk, a, xx, dd, k, None);
                    }
                    // (a stack argument pushed: the call's first step)
                    if stk && self.insns.get(&st.a).map(|i| i.row) == Some(118) {
                        return self.push_c_at(&st, g, list, a, xx, dd, k);
                    }
                    // (... an immediate, in the startup mode)
                    if stk && self.startup && self.insns.get(&st.a).map(|i| i.row) == Some(116) {
                        return self.push_i_at(&st, g, list, a, xx, dd, k);
                    }
                }
                // (the frame's stack objects: at the machine's first store to
                // one; the instructions before it first)
                Some(Red::Alloc { op, a, xx, dd, k }) => {
                    if let Some(pf) = self.allocn_at(&st, qi, &op, &a, &xx, &dd, &k)? {
                        return Ok(pf);
                    }
                    if let Some(pf) = self.alloc_at(&st, qi, &op, &a, &xx, &dd, &k)? {
                        return Ok(pf);
                    }
                }
                // (a system call: at the machine's syscall)
                Some(Red::Sys { n, args, a, xx, dd, k, fs }) => {
                    if self.insns.get(&st.a).map(|i| i.row) == Some(156) {
                        return self.sys_at(&st, n, &args, a, xx, dd, k, fs);
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
                // (a zero store the code makes by a call: at the call)
                None => {
                    if let Some(pf) = self.stz_call_try(&st, qi)? {
                        return Ok(pf);
                    }
                }
            }
        }
        // after the procedure's result: the wrapper's rest reduced up to its
        // final part (the stack protector's check before it; the result and
        // rdx the return's), on the program itself (tr.lv_red, tr.psplit)
        if let Spec::Ret(val, pr) = st.spec.clone() {
            if !self.ret_final(&pr) {
                let qi = self.new_q(pr);
                self.picked.borrow_mut().clear();
                match self.reduce(qi, &st.hyps)? {
                    Some(Red::Q(j, r)) => {
                        let rs = self.run(&r, &[])?;
                        let mut st2 = st.clone();
                        st2.spec = Spec::Ret(val, self.qs[j].clone());
                        let rest = self.prove_kept(st2)?;
                        return self.lv_red_plain(&st, qi, j, rs, rest);
                    }
                    Some(Red::Split { cond, ok, ub }) => {
                        let u = self.raise_when_not(&cond, &ub)?;
                        let hc = self.assume(&cond)?;
                        let okr = self.run(&ok.1, &[("HC", hc.clone())])?;
                        let mut st2 = st.clone();
                        st2.spec = Spec::Ret(val, self.qs[ok.0].clone());
                        st2.hyps.push((cond.clone(), hc));
                        let rest = self.prove_kept(st2)?;
                        let body = self.lv_red_plain(&st, qi, ok.0, okr, rest)?;
                        let d = self.close(body, &[cond.clone()], &[])?;
                        return self.psplit_at(&st, qi, &cond, u, d);
                    }
                    None => {
                        if let Some(pf) = self.undef_at(&st, &self.p(&st.spec))? {
                            return Ok(pf);
                        }
                    }
                    _ => return Err(format!("{:x}: the wrapper's rest after the result: {}", st.a, self.print(&self.qs[qi]))),
                }
            }
        }
        self.insn(st)
    }

    /// the wrapper's rest after the result at its final part: the result's
    /// cast and rdx (any), the objects released -- the return's
    fn ret_final(&self, pr: &Term) -> bool {
        let Some(mut b) = self.app(pr, "mkprog", 1).map(|x| x[0].clone()) else { return true };
        loop {
            if let Some(x) = self.app(&b, "letin", 2) {
                b = x[1].clone();
                continue;
            }
            if let Some(x) = self.app(&b, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|y| y.to_vec())) {
                b = x[0].clone();
                continue;
            }
            break;
        }
        match self.app(&b, "bind_rel", 5) {
            Some(x) => self.app(&x[0], "gimple.result", 2).is_some(),
            None => self.app(&b, "any_rel", 2).is_some() || self.app(&b, "eq", 2).is_some(),
        }
    }

    /// the program pr at `if !C { undefined }` with C false by the facts in
    /// scope (the canary changed): any claim (tr.undef_ub)
    fn undef_at(&mut self, st: &St, pr: &Term) -> Result<Option<Seq>, String> {
        let Some(body) = self.app(pr, "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some(e) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else { return Ok(None) };
        let Some(or) = self.app(&e[0], "or", 2).map(|x| x.to_vec()) else { return Ok(None) };
        let Some(c) = self.app(&or[0], "not", 1).map(|x| x[0].clone()).filter(|c| c.loose_depth(&self.env.binders_fn()) == 0) else { return Ok(None) };
        let Some(b) = self.app(&e[1], "ex", 1).and_then(|x| self.app(&x[0], "and", 2).map(|y| y.to_vec())) else { return Ok(None) };
        let Some(l) = self.app(&b[0], "or", 2).and_then(|x| self.app(&x[0], "and", 2).map(|y| y[1].clone())) else { return Ok(None) };
        let Some(ll) = self.lam(&l, &["x0", "x1", "x2", "x3"], &["x2", "x3"]) else { return Ok(None) };
        let nc = self.mk("not", vec![c.clone()]);
        let Some((true, hn)) = self.guard(&nc, &st.hyps) else { return Ok(None) };
        self.trace(|| format!("at {:x}: undefined ({} false)", st.a, self.print(&c)));
        let inst = R::Inst("tr.undef_ub".into(), vec![("C", c), ("L", ll), ("bkp", self.bkp.clone()), ("bka", self.bka.clone())]);
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
            t(&st.w),
            hn,
            taut(vec![R::S(st.hw.clone())]),
            taut(vec![R::S(st.hw.clone())]),
        ];
        self.run(&mp(inst, args), &[]).map(Some)
    }

    /// the rest qi at `require C` with C false by the facts in scope: it
    /// raises (tr.req_raise), any claim (tr.wub)
    fn req_ub(&mut self, st: &St, qi: usize) -> Result<Option<Seq>, String> {
        let Some(body) = self.app(&self.qs[qi], "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some(e) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else { return Ok(None) };
        let Some(eq) = self.app(&e[1], "eq", 2).map(|x| x.to_vec()) else { return Ok(None) };
        if !(matches!(eq[0].node(), Node::BVar(1)) && matches!(eq[1].node(), Node::BVar(0))) {
            return Ok(None);
        }
        let Some(or) = self.app(&e[0], "or", 2).map(|x| x.to_vec()) else { return Ok(None) };
        let Some(c) = self.app(&or[0], "not", 1).map(|x| x[0].clone()).filter(|c| c.loose_depth(&self.env.binders_fn()) == 0) else { return Ok(None) };
        let Some(r) = self.lam(&or[1], &["x0", "x1", "x2"], &["x0", "x2"]) else { return Ok(None) };
        let nc = self.mk("not", vec![c.clone()]);
        let Some((true, hn)) = self.guard(&nc, &st.hyps) else { return Ok(None) };
        self.trace(|| format!("at {:x}: undefined (required {} false)", st.a, self.print(&c)));
        let vw = self.vw.clone();
        let hw0 = self.hw0.clone().unwrap();
        let ru = mp(R::Inst("tr.req_raise".into(), vec![("C", c), ("R", r)]), vec![t(&st.w), t(&vw), taut(vec![R::S(st.hw.clone())]), p(self.hvu0_r()), hn]);
        let inst = R::Inst(
            "tr.wub".into(),
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
                ("bkp", self.bkp.clone()),
                ("bka", self.bka.clone()),
            ],
        );
        self.run(&mp(inst, vec![t(&vw), taut(vec![R::S(hw0)]), p(self.hvu0_r()), p(ru)]), &[]).map(Some)
    }

    /// `tr.psplit` at st over cond (the program qi's): the raise u when not,
    /// the claim d when
    fn psplit_at(&mut self, st: &St, qi: usize, cond: &Term, u: Seq, d: Seq) -> Result<Seq, String> {
        let inst = R::Inst(
            "tr.psplit".into(),
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
                ("c", cond.clone()),
            ],
        );
        let hw0 = self.hw0.clone().unwrap();
        self.run(&mp(inst, vec![t(&self.vw.clone()), taut(vec![R::S(hw0)]), p(self.hvu0_r()), s(&u), s(&d)]), &[])
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

    /// At a `call f` against the spec's store of zeros (its definedness in
    /// hand), the startup mode's: f's contract `X.impl_m` (for any
    /// alignment, never stopping) with X.typed, X.io and X.stz_incl (the
    /// call's runs the store's but overflows) -- the call making the store
    /// (tr.call0_stb: memset's for a zeroed object). None if not so.
    fn stz_call_try(&mut self, st: &St, qi: usize) -> Result<Option<Seq>, String> {
        let Some(insn) = self.insns.get(&st.a).cloned() else { return Ok(None) };
        let (Some((tt, k)), true) = (self.stop, self.startup) else { return Ok(None) };
        if insn.row != 120 {
            return Ok(None);
        }
        let Some(off) = nat(&insn.fields) else { return Ok(None) };
        let a2 = (st.a + insn.len) % P64;
        let fa = (a2 + if off >= 1 << 31 { off + (P64 - (1 << 32)) } else { off }) % P64;
        // (the spec's head: a store of zeros, defined)
        let q = self.qs[qi].clone();
        self.trace(|| format!("at {:x}: a call of {:x}, the spec's rest {}", st.a, fa, self.print(&q)));
        let Some(body) = self.app(&q, "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some(ex) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else { return Ok(None) };
        let Some(x) = self.app(&ex[0], "bind_rel", 5).map(|x| x.to_vec()) else { return Ok(None) };
        let Some(so) = self.store_op(&x[0])? else { return Ok(None) };
        let Some(data) = so.data.clone() else { return Ok(None) };
        if so.inner != x[0] {
            self.trace(|| format!("at {:x}: a zero store through a helper, not by a call", st.a));
            return Ok(None);
        }
        let Some(hc) = self.hyp_find(&st.hyps, &so.cond).map(|h| h.1.clone()) else {
            self.trace(|| format!("at {:x}: a zero store, its definedness not in hand", st.a));
            return Ok(None);
        };
        // (f's contract: `all statics. tr.impl_m(false, true, f, G, t, k, ..)`)
        let statics = self.statics_var();
        let mut found = None;
        for (name, th) in self.env.theorems.iter() {
            let Some(pre) = name.strip_suffix(".impl_m") else { continue };
            let Some(b) = self.app(th.prop(), "all", 1).map(|x| x[0].clone()) else { continue };
            let b = b.instantiate_params(&[statics.clone()], &self.env.binders_fn());
            let Some(c) = self.app(&b, "tr.impl_m", 9).map(|x| x.to_vec()) else { continue };
            if nat(&c[2]) == Some(fa) && self.app(&c[0], "false", 0).is_some() && self.app(&c[1], "true", 0).is_some() && nat(&c[4]) == Some(tt) && self.app(&c[5], if k { "true" } else { "false" }, 0).is_some() {
                found = Some((name.clone(), pre.to_string(), c[3].clone()));
                break;
            }
        }
        let Some((cname, pre, g)) = found else {
            self.trace(|| format!("at {:x}: a zero store, no contract `X.impl_m` of the callee at {:x} (any alignment, the caller's stop)", st.a, fa));
            return Ok(None);
        };
        self.trace(|| format!("at {:x}: the zero store by the call of {:x} ({})", st.a, fa, cname));
        let hcall = self.run(&R::Apply(Box::new(f(&cname)), vec![t(&statics)]), &[])?;
        let htyp = self.run(&f(&format!("{pre}.typed")), &[])?;
        let hio = self.run(&f(&format!("{pre}.io")), &[])?;
        // (the statement's parts, as a store's: its continuation, handlers, rest)
        let kl = self.lam(&ex[1], &["x0", "x1", "x8"], &["x8", "x1"]).ok_or("a block's rest reads the world")?;
        let c5 = ["x0", "x1", "x8", "x9", "x10"];
        let al = self.lam(&x[2], &c5, &["x9", "x10", "x8"]).ok_or("a store's continuation reads the world before it")?;
        let xl = self.lam(&x[3], &c5, &["x9", "x10", "x8"]).ok_or("a store's handler reads the world before it")?;
        let dl = self.lam(&x[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("a store's handler reads the world before it")?;
        // (the call's arguments: the address, 0, the size)
        let arg = |gg: &Gen, v: Term| gg.mk("seq_one", vec![gg.mk("gimple.arg", vec![lit(64), v])]);
        let items = vec![self.mk("gimple.arg", vec![lit(64), so.addr.clone()]), self.mk("gimple.arg", vec![lit(64), lit(0)]), self.mk("gimple.arg", vec![lit(64), lit(so.n)])];
        let list = self.mk("seq_concat", vec![self.mk("seq_concat", vec![arg(self, so.addr.clone()), arg(self, lit(0))]), arg(self, lit(so.n))]);
        // (the rest passes the statement's raise on: `all x e x8 y. xx(x, e,
        // x8) -> k(x8, y) -> y = exc(x, e)` -- the raise's x8 put in the
        // rest, then simp; in a loop's body through the iteration's end)
        let hpass = {
            let n = self.fresh("p");
            let (xv, ev, x8v, yv) = (self.var(&format!("XP{n}")), self.var(&format!("EP{n}")), self.var(&format!("X8P{n}")), self.var(&format!("YP{n}")));
            let h1t = xl.instantiate_params(&[xv.clone(), ev.clone(), x8v.clone()], &self.env.binders_fn());
            let h2t = kl.instantiate_params(&[x8v.clone(), yv.clone()], &self.env.binders_fn());
            let (a1, a2) = (self.assume(&h1t)?, self.assume(&h2t)?);
            let body = self.abstract_sub(&self.expand(&h2t), &self.expand(&x8v));
            let a3 = Seq::subst(self.env, &a1, &body, &a2).map_err(|e| format!("{:x}: the rest's raise: {}", st.a, e.0))?;
            let goal = self.mk("eq", vec![yv.clone(), self.mk("exc", vec![xv.clone(), ev.clone()])]);
            // (the iteration's end, if the rest is in a loop's body: unfolded)
            let kd = ["tr.lcont", "tr.isout", "tr.mk"].map(String::from).to_vec();
            let a3 = R::Expand(Box::new(R::S(a3)), kd);
            let pf = self.evp(&RP::Simp(false, vec![a3], vec![], false), &goal, &[])?;
            self.close(pf, &[h1t, h2t], &[Self::var_id(&xv), Self::var_id(&ev), Self::var_id(&x8v), Self::var_id(&yv)])?
        };
        // (the call's runs the store's: X.stz_incl at the store; the I/O at
        // the call the entry's)
        let w = st.w.clone();
        let incl = p(R::Mp(
            Box::new(R::Inst(format!("{pre}.stz_incl"), vec![("ka", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone()), ("kw", self.kw3())])),
            vec![
                t(&self.s.clone()),
                t(&w),
                t(&so.p),
                t(&so.off),
                t(&data),
                t(&so.addr),
                taut(vec![R::S(st.hw.clone())]),
                s(&st.hvu),
                simp_l(),
                simp_l(),
                simp_l(),
                simp_l(),
                simp0(),
                s(&hc),
                simp_l(),
                s(&hpass),
            ],
        ));
        let bka = p(self.bka_ovs_pf(&self.bka.clone()).ok_or_else(|| format!("{:x}: the breakpoints' relation, not one kept by the runs (tr.bka_ovs)", st.a))?);
        let lib = LibCall { hcall, htyp, hio, stmt: x[0].clone(), incl, bka };
        self.call_at(st, qi, g, &items, list, false, false, al, xl, dl, kl, Some(lib)).map(Some)
    }

    /// `tr.bka_ovs(bka)` for the claim's breakpoints' relation (its body,
    /// z p w bound): the stop's (tr.bka_ovs_at), a CFG's cut points' ahead
    /// of another (tr.bka_ovs_cut)
    fn bka_ovs_pf(&self, bka: &Term) -> Option<R> {
        let zpw = ["z", "p", "w"];
        if let Some(x) = self.app(bka, "and", 2) {
            let at = self.app(&x[1], "tr.at_tm", 4)?;
            let k = self.lam(&x[0], &zpw, &[])?;
            return Some(R::Inst("tr.bka_ovs_at".into(), vec![("b", at[0].clone()), ("k", k)]));
        }
        let o = self.app(bka, "or", 2)?;
        let (c1, c2) = (self.app(&o[0], "and", 2)?, self.app(&o[1], "and", 2)?);
        let ex = self.app(&c1[1], "ex", 1)?;
        let dr = self.app(&ex[0], "and", 2)?;
        let c = self.lam(&c1[0], &zpw, &["z"])?;
        let d = self.lam(&dr[0], &["z", "p", "w", "y"], &["z", "w", "y"])?;
        let b = self.lam(&c2[0], &zpw, &["z"])?;
        let inner = self.lam(&c2[1], &zpw, &zpw)?;
        let hi = self.bka_ovs_pf(&inner)?;
        Some(mp(R::Inst("tr.bka_ovs_cut".into(), vec![("C", c), ("D", d), ("B", b), ("bka", inner)]), vec![p(hi)]))
    }

    /// A call (tr.call, tr.call1 for call1): the machine's `call rel32` at
    /// st's address from a frame of fr bytes, the spec's call of g with the
    /// arguments in their registers; the claim after it (at the return
    /// address, rax:rdx the result -- rax for call1 --, the homes kept, the
    /// frame from the push up) for every world and result. (lib: a call the
    /// spec makes as a statement of its own, tr.call0_stb -- its callee's
    /// facts given, no result.)
    #[allow(clippy::too_many_arguments)]
    fn call_at(&mut self, st: &St, qi: usize, g: Term, args_all: &[Term], list: Term, one: bool, stk: bool, al: Term, xl: Term, dl: Term, kl: Term, lib: Option<LibCall>) -> Result<Seq, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        let indirect = insn.row == 121;
        if insn.row != 120 && !indirect {
            return Err(format!("{:x}: the spec calls, the machine does not", a));
        }
        if lib.is_some() && (indirect || stk || one || !self.startup || self.stop.is_none()) {
            return Err(format!("{:x}: a statement by a call: only a direct call in the startup mode", a));
        }
        // (`call *%r` against a call through the code map G[p], stopping at
        // t: r holding p -- the register, the instruction's rest, p, G)
        let mut ind: Option<(u128, Term, Term, Term)> = None;
        let g = if indirect {
            if self.stop.is_none() && (self.startup || one) {
                return Err(format!("{:x}: a call through a pointer without a stop: only call, not in the startup mode", a));
            }
            let gp = self.app(&g, "app", 2).ok_or_else(|| format!("{:x}: `call *%r`, the spec's callee {} not the code map's entry", a, self.print(&g)))?.to_vec();
            let fl = self.app(&insn.fields, "pair", 2).ok_or_else(|| format!("{:x}: `call *`: not a register", a))?.to_vec();
            let (tg, rt) = self.tag(&fl[0]).ok_or_else(|| format!("{:x}: `call *`: not a register", a))?;
            let r = nat(&rt).filter(|_| tg == 0).ok_or_else(|| format!("{:x}: `call *`: not a register", a))?;
            let (kk, v) = self.reg(st, r).ok_or_else(|| format!("{:x}: register {} holds no value at the call", a, r))?;
            if kk != 8 || self.canon(&v) != self.canon(&gp[1]) {
                return Err(format!("{:x}: register {} holds {}, the spec calls the code map at {}", a, r, self.print(&v), self.print(&gp[1])));
            }
            ind = Some((r, fl[1].clone(), gp[1].clone(), gp[0].clone()));
            gp[0].clone()
        } else {
            g
        };
        if st.fr % 8 != 0 || st.fr + 8 > 65536 {
            return Err(format!("{:x}: a call from a frame of {} bytes (a multiple of 8, at most 64 KiB expected)", a, st.fr));
        }
        let aligned = st.fr % 16 == 8;
        let nargs = args_all.len();
        // (a callee with stack arguments: seven, the last the home at the
        // frame's bottom, pushed there; the call aligned, rax the result)
        if stk && (nargs != 7 || (!aligned && !self.startup) || !one) {
            return Err(format!("{:x}: a call with stack arguments other than seven, aligned, of call1_s", a));
        }
        if nargs > 6 && !stk {
            return Err(format!("{:x}: a call with {} arguments (at most 6 so far)", a, nargs));
        }
        let args = &args_all[..nargs.min(6)];
        let off = if indirect { 0 } else { nat(&insn.fields).ok_or_else(|| format!("{:x}: the call's displacement", a))? };
        let a2 = (a + insn.len) % P64;
        let fa = if indirect { 0 } else { (a2 + if off >= 1 << 31 { off + (P64 - (1 << 32)) } else { off }) % P64 };
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
            // (of the same normal form -- a stack object's address: N's)
            if [1, 2, 4, 8].contains(&k) && self.canon(&v) != self.canon(&x) {
                if let Some(q) = self.eq_nf_seq(&v, &x)? {
                    eqf.push(R::S(q));
                }
            }
            if [1, 2, 4, 8].contains(&k) && self.canon(&v) != self.canon(&x) && eqf.is_empty() {
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
        let hreg = if nargs == 0 { mpf("tr.args0", vec![t(&st.rs)]) } else { R::Apply(Box::new(f(&format!("tr.args{}", args.len()))), aps) };
        let hin = self.hin_proof(&st.hst, st.fr)?;
        let (hcall, htyp, hio) = match &lib {
            Some(l) => (l.hcall.clone(), l.htyp.clone(), l.hio.clone()),
            None => self.callee_facts(st, &g, fa, nargs, aligned, stk, &ind)?,
        };
        // (the callee's contract at this call: the ABI's if aligned, else the one for any entry)
        let ccname = if self.startup && stk { "tr.ccs_ms" } else if self.startup { "tr.ccs_m" } else if self.stop.is_some() { "tr.callee_contract_s" } else { "tr.callee_contract" };
        let hcon = if lib.is_some() {
            defs(RP::Taut(vec![R::S(hcall.clone())]), &[ccname])
        } else if (stk && !self.startup) || ind.is_some() {
            p(R::S(hcall.clone()))
        } else if aligned {
            let fr16 = self.evp(&RP::Simp(false, vec![], vec![], false), &self.mk("eq", vec![self.mk("int_mod", vec![lit(st.fr), lit(16)]), lit(8)]), &[])?;
            defs(RP::Taut(vec![R::S(hcall), R::S(fr16)]), &[ccname])
        } else {
            defs(RP::Taut(vec![R::S(hcall)]), &[ccname])
        };
        self.call_rest(st, qi, g, args_all, list, one, stk, al, xl, dl, kl, lib, insn, fa, off, a2, aligned, nargs, ind, hreg, hin, htyp, hio, hcon)
    }

    /// (a call's callee G{i}, a parameter of the spec: its contract, typing
    /// and returns' effects -- premises of the C1 theorem, assumed at its
    /// first call)
    #[allow(clippy::too_many_arguments)]
    fn callee_facts(&mut self, st: &St, g: &Term, fa: u128, nargs: usize, aligned: bool, stk: bool, ind: &Option<(u128, Term, Term, Term)>) -> Result<(Seq, Seq, Seq), String> {
        let a = st.a;
        let g = g.clone();
        let ci = self.callees.iter().position(|c| c.0 == g && c.1 == fa).unwrap_or_else(|| {
            self.callees.push((g.clone(), fa, nargs, false));
            self.callees.len() - 1
        });
        self.callees[ci].3 |= !aligned;
        // (its premises: hcall{i} .. for the spec's parameter Gi)
        let gi: usize = self.env.var(Self::var_id(&g)).name.strip_prefix('G').and_then(|i| i.parse().ok()).ok_or_else(|| format!("{:x}: a call of {}, not a parameter of the spec", a, self.print(&g)))?;
        // (its premises, at its first call: its contract on the program text,
        // its spec typed, its returns' effects)
        if gi >= self.cinfo.len() {
            return Err(format!("{:x}: a call of G{}, not a parameter of the spec", a, gi));
        }
        match &self.cinfo[gi] {
            None => {
                let imp = if stk { "tr.implements_at_s" } else if aligned { "tr.implements_at" } else { "tr.implements_at_u" };
                let (lb, lc, statics) = (self.lbase.clone(), self.lcode.clone(), self.statics_t.clone());
                // (stopping at t: the callee's contract with the stop at t, as
                // the caller's -- k)
                let hc = match self.stop {
                    // (through the code map, no stop: tr.code_okn, and G typed)
                    None if ind.is_some() => {
                        let hc = self.mk("tr.code_okn", vec![g.clone(), lit(nargs as u128), lit(st.fr), lb, lc, statics]);
                        let fs = self.mk("fn_space", vec![self.mk("abi.ARGS", vec![]), self.mk("powerset", vec![self.mk("univ", vec![lit(1)])])]);
                        let ht = self.mk("in", vec![g.clone(), self.mk("fn_space", vec![self.mk("bits", vec![lit(64)]), fs])]);
                        self.hcall[gi] = Some(self.assume(&hc)?);
                        let hts = self.assume(&ht)?;
                        self.htyp[gi] = Some(hts.clone());
                        self.hio[gi] = Some(hts);
                        self.cinfo[gi] = Some((fa, nargs, !aligned, vec![hc.clone(), ht]));
                        hc
                    }
                    // (through the code map: tr.code_ok, and G typed -- the
                    // startup mode's tr.code_okm(false, ..))
                    Some((tt, _)) if ind.is_some() => {
                        let hc = if self.startup {
                            self.mk("tr.code_okm", vec![self.bm(), g.clone(), lit(nargs as u128), lit(st.fr), lit(tt), lb, lc, statics])
                        } else {
                            self.mk("tr.code_ok", vec![g.clone(), lit(nargs as u128), lit(st.fr), lit(tt), lb, lc, statics])
                        };
                        let fs = self.mk("fn_space", vec![self.mk("abi.ARGS", vec![]), self.mk("powerset", vec![self.mk("univ", vec![lit(1)])])]);
                        let ht = self.mk("in", vec![g.clone(), self.mk("fn_space", vec![self.mk("bits", vec![lit(64)]), fs])]);
                        self.hcall[gi] = Some(self.assume(&hc)?);
                        let hts = self.assume(&ht)?;
                        self.htyp[gi] = Some(hts.clone());
                        self.hio[gi] = Some(hts);
                        self.cinfo[gi] = Some((fa, nargs, !aligned, vec![hc.clone(), ht]));
                        hc
                    }
                    Some((tt, k)) if self.startup => {
                        // (the startup mode's: tr.impl_m(false, u, ..), with
                        // stack arguments tr.impl_m_s)
                        let kt = self.mk(if k { "true" } else { "false" }, vec![]);
                        let (ff, ut) = (self.bm(), self.mk(if aligned { "false" } else { "true" }, vec![]));
                        self.mk(if stk { "tr.impl_m_s" } else { "tr.impl_m" }, vec![ff, ut, lit(fa), g.clone(), lit(tt), kt, lb, lc, statics])
                    }
                    Some((tt, k)) if !stk => {
                        let kt = self.mk(if k { "true" } else { "false" }, vec![]);
                        self.mk(if aligned { "tr.implements_stop" } else { "tr.implements_stop_u" }, vec![lit(fa), g.clone(), lit(tt), kt, lb, lc, statics])
                    }
                    _ => self.mk(imp, vec![lit(fa), g.clone(), lb, lc, statics]),
                };
                if ind.is_none() {
                    let dom = if stk { self.mk("list_type", vec![self.mk("bits", vec![lit(64)])]) } else { self.mk("abi.ARGS", vec![]) };
                    let ht = self.mk("in", vec![g.clone(), self.mk("fn_space", vec![dom, self.mk("powerset", vec![self.mk("univ", vec![lit(1)])])])]);
                    let hi = self.mk(if stk { "tr.callee_io_s" } else { "tr.callee_io" }, vec![g.clone(), lit(nargs as u128)]);
                    self.hcall[gi] = Some(self.assume(&hc)?);
                    self.htyp[gi] = Some(self.assume(&ht)?);
                    self.hio[gi] = Some(self.assume(&hi)?);
                    self.cinfo[gi] = Some((fa, nargs, !aligned, vec![hc, ht, hi]));
                }
            }
            Some((f0, n0, u0, _)) => {
                if (*f0, *n0, *u0) != (fa, nargs, !aligned) {
                    return Err(format!("{:x}: a call of G{} other than its first (at another address, with other arguments, or another alignment)", a, gi));
                }
            }
        }
        Ok((self.hcall[gi].clone().unwrap(), self.htyp[gi].clone().unwrap(), self.hio[gi].clone().unwrap()))
    }

    /// (the call's claim: its continuation's raise and divergence, the claim
    /// after it, the rule)
    #[allow(clippy::too_many_arguments)]
    fn call_rest(
        &mut self,
        st: &St,
        qi: usize,
        g: Term,
        args_all: &[Term],
        list: Term,
        one: bool,
        stk: bool,
        al: Term,
        xl: Term,
        dl: Term,
        kl: Term,
        lib: Option<LibCall>,
        insn: Insn,
        fa: u128,
        off: u128,
        a2: u128,
        aligned: bool,
        nargs: usize,
        ind: Option<(u128, Term, Term, Term)>,
        hreg: R,
        hin: R,
        htyp: Seq,
        hio: Seq,
        hcon: RA,
    ) -> Result<Seq, String> {
        let a = st.a;
        let args = &args_all[..nargs.min(6)];
        let _ = args;
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
        // (a statement by a call: no result)
        let res = if lib.is_some() {
            self.mk("empty", vec![])
        } else if one {
            r0.clone()
        } else {
            self.mk("pair", vec![r0.clone(), r1.clone()])
        };
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
        // (the callee-saved registers kept by the callee)
        let rc = self.cs_held(st);
        st0 = self.with_regs(&st0, &rc);
        st0.a = a2;
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
        if stk {
            // (the six in registers, then y: the home at the frame's bottom, x)
            let l6 = self.app(&list, "seq_concat", 2).ok_or_else(|| format!("{:x}: the arguments: not six, then one", a))?[0].clone();
            let y = args_all[6].clone();
            let cb = P64 - st.fr;
            let (kb, xh) = st.hsm.get(&cb).cloned().ok_or_else(|| format!("{:x}: no home at the frame's bottom (the stack argument)", a))?;
            let yv = self.app(&y, "gimple.arg", 2).map(|x| x[1].clone()).ok_or_else(|| format!("{:x}: the stack argument not an argument", a))?;
            // (the same value, or the same literal: an immediate pushed)
            let lit_eq = self.eval_lit(&xh).is_some() && self.eval_lit(&xh) == self.eval_lit(&self.lit_bits(&yv));
            if kb != 8 || (self.canon(&xh) != self.canon(&yv) && !lit_eq) {
                return Err(format!("{:x}: the frame's bottom holds {}, the spec passes {}", a, self.print(&xh), self.print(&yv)));
            }
            let mut binds = vec![
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
                ("G", g.clone()),
                ("x", xh.clone()),
                ("a6", l6),
                ("y", y),
                ("cb", self.lbase.clone()),
                ("cc", self.lcode.clone()),
                ("st", self.statics_var()),
                ("hs", st.hst.clone()),
                ("ds", st.ds.clone()),
                ("fd2", lit(fd2)),
                ("rs", st.rs.clone()),
                ("rc", self.regs_map(&rc)),
                ("w", w.clone()),
                ("ka", al),
                ("xx", xl),
                ("dd", dl),
                ("k", kl),
                ("kw", self.kw3()),
                ("bkp", self.bkp.clone()),
                ("bka", self.bka.clone()),
            ];
            let hl = self.hl.clone().unwrap();
            let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
            let csp = self.cs_sub_pf(&rc, &st.rs);
            // (the startup mode's, stopping at t: tr.call1_0_sc -- the
            // callee's contract tr.ccs_ms, t's states breakpoints, the
            // relation at a stop the caller's; the call aligned or not)
            let (rule, mid, tail) = match self.stop {
                Some((tt, k)) if self.startup => {
                    binds.extend([("t", lit(tt)), ("ks", self.mk(if k { "true" } else { "false" }, vec![]))]);
                    let hal = if aligned { taut(vec![R::S(self.sal16()?)]) } else { simp0() };
                    ("tr.call1_0_sc", vec![hcon, simp0(), hal], vec![simp0(), self.tbp_below(&self.bkp.clone(), st.fr, tt), self.hat_pf(tt, k)])
                }
                _ if self.startup => return Err(format!("{:x}: a call with stack arguments in the startup mode never stopping", a)),
                _ => {
                    let fr16 = self.evp(&RP::Simp(false, vec![], vec![], false), &self.mk("eq", vec![self.mk("int_mod", vec![lit(st.fr), lit(16)]), lit(8)]), &[])?;
                    let s16 = self.sal16()?;
                    ("tr.call1_sc", vec![s(&fr16), taut(vec![R::S(s16)]), hcon], vec![self.nobp_below(&self.bkp.clone(), st.fr)])
                }
            };
            let inst = R::Inst(rule.into(), binds);
            // (the six a list of univ(1): its items' by tr.seq_one_type, tr.concat_list)
            fn list_univ(g: &Gen, l: &Term) -> Option<R> {
                let u1 = g.mk("univ", vec![lit(1)]);
                if let Some(x) = g.app(l, "seq_one", 1) {
                    return Some(mpf("tr.seq_one_type", vec![t(&x[0]), t(&u1), defs(RP::Simp(false, vec![], vec![], false), &["gimple.arg"])]));
                }
                let c = g.app(l, "seq_concat", 2)?;
                Some(mpf("tr.concat_list", vec![t(&c[0]), t(&c[1]), t(&u1), p(list_univ(g, &c[0])?), p(list_univ(g, &c[1])?)]))
            }
            let l6t = list_univ(self, &self.app(&list, "seq_concat", 2).unwrap()[0].clone()).ok_or_else(|| format!("{:x}: the six: not a list literal", a))?;
            return self.run(
                &mp(
                    inst,
                    [vec![
                        simp0(),
                        p(self.ofr_pf(&self.mk("int_sub", vec![lit(st.fr), lit(8)]))),
                        p(self.hap_pf(&st.hst)),
                        p(f(&insn.name)),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                    ], mid, vec![
                        s(&hl),
                        simp0(),
                        cfr,
                        p(l6t),
                        simp0(),
                        defs(RP::Simp(false, vec![], vec![], false), &["gimple.arg"]),
                        defs(RP::Simp(true, vec![], vec![], false), &["gimple.arg", "gimple.in_reg"]),
                        simp_l(),
                        s(&htyp),
                        s(&hio),
                        p(hreg),
                        p(csp),
                        p(hin),
                        simp_l(),
                        simp_l(),
                        simp0(),
                        simp0(),
                        s(&hk),
                        s(&hd),
                        s(&pc),
                    ], tail]
                    .concat(),
                ),
                &[],
            );
        }
        let rname = match (self.stop.is_some(), one) {
            _ if lib.is_some() => "tr.call0_stb",
            (false, true) => "tr.call1",
            (false, false) => "tr.call",
            (true, true) if self.startup => "tr.call1_0_st",
            (true, false) if self.startup => "tr.call0_st",
            (true, true) => "tr.call1_st",
            (true, false) => "tr.call_st",
        };
        let mut binds = vec![
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
                ("args", list.clone()),
                ("n", lit(nargs as u128)),
                ("cb", self.lbase.clone()),
                ("cc", self.lcode.clone()),
                ("st", self.statics_var()),
                ("hs", st.hst.clone()),
                ("ds", st.ds.clone()),
                ("fd2", lit(fd2)),
                ("rs", st.rs.clone()),
                ("rc", self.regs_map(&rc)),
                ("w", w.clone()),
                ("ka", al.clone()),
                ("xx", xl.clone()),
                ("dd", dl.clone()),
                ("k", kl.clone()),
                ("kw", self.kw3()),
        ];
        // (stopping at t: t's states breakpoints, the callee's below the
        // frame none else, the relation at a stop the caller's)
        let stop_tail = match self.stop {
            Some((tt, k)) => {
                let kt = self.mk(if k { "true" } else { "false" }, vec![]);
                binds.extend([("t", lit(tt)), ("ks", kt.clone()), ("bkp", self.bkp.clone()), ("bka", self.bka.clone())]);
                let mut tl = vec![simp0(), self.tbp_below(&self.bkp.clone(), st.fr, tt), self.hat_pf(tt, k)];
                // (a statement by a call: the statement, the call's runs its
                // own, the breakpoints' relation kept)
                if let Some(l) = &lib {
                    binds.push(("S", l.stmt.clone()));
                    tl.extend([l.incl.clone(), l.bka.clone()]);
                }
                Some(tl)
            }
            None => None,
        };
        // (through the code map: tr.calli_st, the callee's stop allowed)
        if let (Some((r, z, tp, gv)), Some((tt, k))) = (ind.clone(), self.stop) {
            if !k {
                return Err(format!("{:x}: a call through a pointer in a function never stopping at main", a));
            }
            let kt = self.mk("true", vec![]);
            let _ = kt;
            let inst = R::Inst(
                match (one, self.startup) {
                    (true, false) => "tr.calli1_st",
                    (false, false) => "tr.calli_st",
                    (true, true) => "tr.calli1_0_st",
                    (false, true) => "tr.calli0_st",
                }
                .into(),
                vec![
                    ("s", self.s.clone()),
                    ("v", self.v.clone()),
                    ("base", self.base.clone()),
                    ("code", self.code.clone()),
                    ("fr", lit(st.fr)),
                    ("a", lit(a)),
                    ("a2", lit(a2)),
                    ("len", lit(insn.len)),
                    ("gr", lit(r)),
                    ("z", z),
                    ("nb", lit(8)),
                    ("T", tp),
                    ("fptr", gv),
                    ("args", list.clone()),
                    ("n", lit(nargs as u128)),
                    ("cb", self.lbase.clone()),
                    ("cc", self.lcode.clone()),
                    ("st", self.statics_var()),
                    ("hs", st.hst.clone()),
                    ("ds", st.ds.clone()),
                    ("fd2", lit(fd2)),
                    ("rs", st.rs.clone()),
                    ("rc", self.regs_map(&rc)),
                    ("w", w.clone()),
                    ("t", lit(tt)),
                    ("ka", al.clone()),
                    ("xx", xl.clone()),
                    ("dd", dl.clone()),
                    ("k", kl.clone()),
                    ("kw", self.kw3()),
                    ("bkp", self.bkp.clone()),
                    ("bka", self.bka.clone()),
                ],
            );
            let hl = self.hl.clone().unwrap();
            let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
            let hal = if aligned { taut(vec![R::S(self.sal16()?)]) } else { simp0() };
            let (ha, ho) = (p(self.hap_pf(&st.hst)), p(self.ofr_pf(&lit(st.fr))));
            let pre = if one { vec![simp0(), ha, ho] } else { vec![simp0(), ho, ha] };
            let hat = p(R::Mp(Box::new(self.hat_r(tt, true)), vec![taut(vec![])]));
            return self.run(
                &mp(
                    inst,
                    [pre, vec![
                        p(f(&insn.name)),
                        simp_l(),
                        simp0(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp0(),
                        hcon,
                        hal,
                        s(&hl),
                        simp0(),
                        cfr,
                        simp0(),
                        simp0(),
                        simp0(),
                        s(&htyp),
                        p(hreg),
                        p(self.cs_sub_pf(&rc, &st.rs)),
                        p(hin),
                        simp0(),
                        simp0(),
                        s(&hk),
                        s(&hd),
                        s(&pc),
                        simp0(),
                        self.tbp_below(&self.bkp.clone(), st.fr, tt),
                        hat,
                    ]]
                    .concat(),
                ),
                &[],
            );
        }
        // (through the code map, no stop: tr.calli)
        if let (Some((r, z, tp, gv)), None) = (ind.clone(), self.stop) {
            let inst = R::Inst(
                "tr.calli".into(),
                vec![
                    ("s", self.s.clone()),
                    ("v", self.v.clone()),
                    ("base", self.base.clone()),
                    ("code", self.code.clone()),
                    ("fr", lit(st.fr)),
                    ("a", lit(a)),
                    ("a2", lit(a2)),
                    ("len", lit(insn.len)),
                    ("gr", lit(r)),
                    ("z", z),
                    ("nb", lit(8)),
                    ("T", tp),
                    ("fptr", gv),
                    ("args", list.clone()),
                    ("n", lit(nargs as u128)),
                    ("cb", self.lbase.clone()),
                    ("cc", self.lcode.clone()),
                    ("st", self.statics_var()),
                    ("hs", st.hst.clone()),
                    ("ds", st.ds.clone()),
                    ("fd2", lit(fd2)),
                    ("rs", st.rs.clone()),
                    ("rc", self.regs_map(&rc)),
                    ("w", w.clone()),
                    ("ka", al.clone()),
                    ("xx", xl.clone()),
                    ("dd", dl.clone()),
                    ("k", kl.clone()),
                    ("kw", self.kw3()),
                    ("bkp", self.bkp.clone()),
                    ("bka", self.bka.clone()),
                ],
            );
            let hl = self.hl.clone().unwrap();
            let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
            let hal = if aligned { taut(vec![R::S(self.sal16()?)]) } else { simp0() };
            let (ha, ho) = (p(self.hap_pf(&st.hst)), p(self.ofr_pf(&lit(st.fr))));
            return self.run(
                &mp(
                    inst,
                    vec![
                        simp0(),
                        ho,
                        ha,
                        p(f(&insn.name)),
                        simp_l(),
                        simp0(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp0(),
                        hcon,
                        hal,
                        s(&hl),
                        simp0(),
                        cfr,
                        simp0(),
                        simp0(),
                        simp0(),
                        s(&htyp),
                        p(hreg),
                        p(self.cs_sub_pf(&rc, &st.rs)),
                        p(hin),
                        simp0(),
                        simp0(),
                        s(&hk),
                        s(&hd),
                        s(&pc),
                        self.nobp_below(&self.bkp.clone(), st.fr),
                    ],
                ),
                &[],
            );
        }
        if let Some(tail) = stop_tail {
            let inst = R::Inst(rname.into(), binds);
            let hl = self.hl.clone().unwrap();
            let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
            let hal = if aligned { taut(vec![R::S(self.sal16()?)]) } else { simp0() };
            let (ha, ho) = (p(self.hap_pf(&st.hst)), p(self.ofr_pf(&lit(st.fr))));
            let pre = if one { vec![simp0(), ha, ho] } else { vec![simp0(), ho, ha] };
            return self.run(
                &mp(
                    inst,
                    [pre, vec![
                        p(f(&insn.name)),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        hcon,
                        simp0(),
                        hal,
                        s(&hl),
                        simp0(),
                        cfr,
                        simp0(),
                        simp0(),
                        simp0(),
                        s(&htyp),
                        s(&hio),
                        p(hreg),
                        p(self.cs_sub_pf(&rc, &st.rs)),
                        p(hin),
                        simp0(),
                        simp0(),
                        s(&hk),
                        s(&hd),
                        s(&pc),
                    ], tail]
                    .concat(),
                ),
                &[],
            );
        }
        let inst = R::Inst(
            rname.into(),
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
                ("rc", self.regs_map(&rc)),
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
        // (an aligned call: the entry aligned; else the frame decides)
        let hal = if aligned { taut(vec![R::S(self.sal16()?)]) } else { simp0() };
        // (the homes apart from the objects, no object the function's own: in the rule's order)
        let (ha, ho) = (p(self.hap_pf(&st.hst)), p(self.ofr_pf(&lit(st.fr))));
        // (the main mode: the claim's objects' C bytes all but the canary)
        let pre = if one { vec![simp0(), ha, ho] } else { vec![simp0(), ho, ha] };
        self.run(
            &mp(
                inst,
                [pre, vec![
                    p(f(&insn.name)),
                    simp_l(),
                    simp_l(),
                    simp_l(),
                    simp_l(),
                    hcon,
                    hal,
                    s(&hl),
                    simp0(),
                    cfr,
                    simp0(),
                    simp0(),
                    simp0(),
                    s(&htyp),
                    s(&hio),
                    p(hreg),
                    p(self.cs_sub_pf(&rc, &st.rs)),
                    p(hin),
                    simp0(),
                    simp0(),
                    s(&hk),
                    s(&hd),
                    s(&pc),
                    self.nobp_below(&self.bkp.clone(), st.fr),
                ]]
                .concat(),
            ),
            &[],
        )
    }

    /// `push [rsp + d]` before a call with stack arguments (tr.push_m64_c):
    /// the home's word at the frame's new bottom, from any frame -- a fault
    /// the call's overflow
    #[allow(clippy::too_many_arguments)]
    fn push_c_at(&mut self, st: &St, g: Term, list: Term, al: Term, xl: Term, dl: Term, kl: Term) -> Result<Seq, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        let a2 = (a + insn.len) % P64;
        let bad = |m: &str| format!("{:x}: {}", a, m);
        let xs = self.pairs(&insn.fields, 2).ok_or_else(|| bad("fields"))?;
        let d = self.rsp_mem(&xs[0]).ok_or_else(|| bad("push of a memory operand not [rsp + d]"))?;
        let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
        let c0 = self.hkey(dn);
        let Some((8, x)) = st.hsm.get(&c0).cloned() else { return Err(bad("push of a word not a home")) };
        let fr2 = st.fr + 8;
        if fr2 > 65536 || st.fr % 8 != 0 {
            return Err(bad("push beyond the frame's bound"));
        }
        let c = P64 - fr2;
        let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
        let (_, hs2, hk) = self.hkeep(st, c, 8);
        // (the call's raise: the function's, as at the call)
        let w = st.w.clone();
        let hv = st.hvu.clone();
        let n = self.fresh("c");
        let (xv, ev) = (self.var(&format!("XP{n}")), self.var(&format!("EP{n}")));
        let x8 = Term::bvar(0);
        let kk = kl.instantiate_params(&[Term::bvar(0), Term::bvar(1)], &self.env.binders_fn());
        let qx = self.mk("mkprog", vec![self.mk("ex", vec![self.mk("and", vec![xl.instantiate_params(&[xv.clone(), ev.clone(), x8], &self.env.binders_fn()), kk])])]);
        let univ = |gg: &Gen, x: &Term| gg.mk("in", vec![x.clone(), gg.mk("univ", vec![lit(1)])]);
        let (hx, he) = (univ(self, &xv), univ(self, &ev));
        let (hxs, hes) = (self.assume(&hx)?, self.assume(&he)?);
        let gk = self.mk("runs", vec![qx, w.clone(), self.mk("exc", vec![xv.clone(), ev.clone()])]);
        let kd: Vec<String> = if self.lpg.is_some() { ["tr.lcont", "tr.isout", "tr.mk"].map(String::from).to_vec() } else { vec!["runs".into(), "mkprog".into()] };
        let k0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hxs), R::S(hes), R::S(hv)], vec![], false)), kd), &gk, &[])?;
        let hkx = self.close(k0, &[hx, he], &[Self::var_id(&xv), Self::var_id(&ev)])?;
        // (the startup mode's: tr.push_m64_c0, the call call1_0_s)
        let inst = R::Inst(
            if self.startup { "tr.push_m64_c0" } else { "tr.push_m64_c" }.into(),
            vec![("ka", al), ("xx", xl), ("dd", dl), ("k", kl), ("kw", self.kw3()), ("bkp", self.bkp.clone()), ("bka", self.bka.clone())],
        );
        let mut args = self.head(a, &insn);
        args.extend([&d, &lit(c0), &x, &lit(fr2), &lit(c), &g, &list].iter().map(|y| t(y)));
        let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
        let extra = vec![p(n4), simp_l(), simp_l(), simp_l(), cfr, p(hk), simp0(), s(&hkx)];
        args.extend(self.tail_h(st, &insn, &hs2, 6, extra));
        let tr = mp(inst, args);
        let mut st2 = self.set_home(st, a2, c, 8, x);
        st2.fr = fr2;
        self.then(tr, st2)
    }

    /// `push imm8` before a call with stack arguments, in the startup mode
    /// (tr.push_i8_c0): the word sext(k) at the frame's new bottom, a home
    #[allow(clippy::too_many_arguments)]
    fn push_i_at(&mut self, st: &St, g: Term, list: Term, al: Term, xl: Term, dl: Term, kl: Term) -> Result<Seq, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        let a2 = (a + insn.len) % P64;
        let bad = |m: &str| format!("{:x}: {}", a, m);
        let kb = nat(&insn.fields).ok_or_else(|| bad("push of an immediate not a literal"))?;
        let x = lit(if kb >= 128 { kb + 0xffff_ffff_ffff_ff00 } else { kb });
        let fr2 = st.fr + 8;
        if fr2 > 65536 || st.fr % 8 != 0 {
            return Err(bad("push beyond the frame's bound"));
        }
        let c = P64 - fr2;
        let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
        let (_, hs2, hk) = self.hkeep(st, c, 8);
        // (the call's raise: the function's, as at the call)
        let w = st.w.clone();
        let hv = st.hvu.clone();
        let n = self.fresh("c");
        let (xv, ev) = (self.var(&format!("XP{n}")), self.var(&format!("EP{n}")));
        let x8 = Term::bvar(0);
        let kk = kl.instantiate_params(&[Term::bvar(0), Term::bvar(1)], &self.env.binders_fn());
        let qx = self.mk("mkprog", vec![self.mk("ex", vec![self.mk("and", vec![xl.instantiate_params(&[xv.clone(), ev.clone(), x8], &self.env.binders_fn()), kk])])]);
        let univ = |gg: &Gen, x: &Term| gg.mk("in", vec![x.clone(), gg.mk("univ", vec![lit(1)])]);
        let (hx, he) = (univ(self, &xv), univ(self, &ev));
        let (hxs, hes) = (self.assume(&hx)?, self.assume(&he)?);
        let gk = self.mk("runs", vec![qx, w.clone(), self.mk("exc", vec![xv.clone(), ev.clone()])]);
        let kd: Vec<String> = if self.lpg.is_some() { ["tr.lcont", "tr.isout", "tr.mk"].map(String::from).to_vec() } else { vec!["runs".into(), "mkprog".into()] };
        let k0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hxs), R::S(hes), R::S(hv)], vec![], false)), kd), &gk, &[])?;
        let hkx = self.close(k0, &[hx, he], &[Self::var_id(&xv), Self::var_id(&ev)])?;
        let inst = R::Inst("tr.push_i8_c0".into(), vec![("ka", al), ("xx", xl), ("dd", dl), ("k", kl), ("kw", self.kw3()), ("bkp", self.bkp.clone()), ("bka", self.bka.clone())]);
        let mut args = self.head(a, &insn);
        args.extend([&lit(kb), &x, &lit(fr2), &lit(c), &g, &list].iter().map(|y| t(y)));
        let cfr = defs(RP::Simp(false, vec![], vec![], false), &["tr.cfr"]);
        let extra = vec![p(n4), simp_l(), simp_l(), simp_l(), cfr, p(hk), simp0(), s(&hkx)];
        args.extend(self.tail_h(st, &insn, &hs2, 4, extra));
        let tr = mp(inst, args);
        let mut st2 = self.set_home(st, a2, c, 8, x);
        st2.fr = fr2;
        self.then(tr, st2)
    }

    /// A system call (tr.sys_call1, tr.sys_call2, tr.sys_call3, tr.sys_call6): the machine's
    /// `syscall` at st's address, rax and rdi (rsi, rdx, r10, r8, r9) holding the spec's number and
    /// arguments; the claim after it (rax the result, the other registers
    /// not known, the frame rsp's page) for every world and result
    #[allow(clippy::too_many_arguments)]
    fn sys_at(&mut self, st: &St, nv: Term, args: &[Term], al: Term, xl: Term, dl: Term, kl: Term, fs: bool) -> Result<Seq, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        let a2 = (a + insn.len) % P64;
        let (rule, names): (&str, &[&str]) = match args.len() {
            2 if fs => ("tr.sys_set_fs", &["", "b2"]),
            1 => ("tr.sys_call1", &["a1"]),
            2 => ("tr.sys_call2", &["a1", "b2"]),
            3 => ("tr.sys_call3", &["a1", "b2", "b3"]),
            6 => ("tr.sys_call6", &["a1", "b2", "b3", "b4", "b5", "b6"]),
            n => return Err(format!("{:x}: a system call with {} arguments (1, 2, 3 or 6)", a, n)),
        };
        let mut regs = vec![(0u128, &nv)];
        // (Linux's argument registers: rdi, rsi, rdx, r10, r8, r9)
        for (r, x) in [7u128, 6, 2, 10, 8, 9].iter().zip(args.iter()) {
            regs.push((*r, x));
        }
        // (a register of 4 bytes -- `mov r32, imm32`: its 8, zero-extended)
        for (r, _) in &regs {
            if let Some(pf) = self.widen(st, *r, 8)? {
                return Ok(pf);
            }
        }
        for (r, x) in regs {
            let (k, v) = self.reg(st, r).ok_or_else(|| format!("{:x}: register {} holds no value at the syscall", a, r))?;
            if k != 8 || self.canon(&v) != self.canon(x) {
                return Err(format!("{:x}: register {} holds {}, the spec's system call passes {}", a, r, self.print(&v), self.print(x)));
            }
        }
        let w = st.w.clone();
        let hv = st.hvu.clone();
        // the continuation's raise: the function's (as at a call)
        let n = self.fresh("s");
        let (xv, ev) = (self.var(&format!("XS{n}")), self.var(&format!("ES{n}")));
        let x8 = Term::bvar(0);
        let mkq = |gg: &Gen, h: Term| -> Term {
            let kk = kl.instantiate_params(&[Term::bvar(0), Term::bvar(1)], &gg.env.binders_fn());
            gg.mk("mkprog", vec![gg.mk("ex", vec![gg.mk("and", vec![h, kk])])])
        };
        let qx = mkq(self, xl.instantiate_params(&[xv.clone(), ev.clone(), x8.clone()], &self.env.binders_fn()));
        let univ = |gg: &Gen, x: &Term| gg.mk("in", vec![x.clone(), gg.mk("univ", vec![lit(1)])]);
        let (hx, he) = (univ(self, &xv), univ(self, &ev));
        let (hxs, hes) = (self.assume(&hx)?, self.assume(&he)?);
        let gk = self.mk("runs", vec![qx, w.clone(), self.mk("exc", vec![xv.clone(), ev.clone()])]);
        let kd: Vec<String> = if self.lpg.is_some() { ["tr.lcont", "tr.isout", "tr.mk"].map(String::from).to_vec() } else { vec!["runs".into(), "mkprog".into()] };
        let k0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hxs), R::S(hes), R::S(hv.clone())], vec![], false)), kd), &gk, &[])?;
        let hk = self.close(k0, &[hx, he], &[Self::var_id(&xv), Self::var_id(&ev)])?;
        // the claim after the call, for every world W4 and result R0
        let (w4, r0) = (self.var(&format!("WS{n}")), self.var(&format!("RS{n}")));
        let ka = al.instantiate_params(&[Term::bvar(2), r0.clone(), Term::bvar(0)], &self.env.binders_fn());
        let q2 = self.canon(&mkq(self, ka));
        let j = self.new_q(q2);
        let hw4t = self.mk("and", vec![self.mk("in", vec![w4.clone(), self.mk("abi.World", vec![])]), univ(self, &w4)]);
        let hw4 = self.assume(&hw4t)?;
        let hv4 = self.evp(&RP::Taut(vec![R::S(hw4.clone())]), &univ(self, &w4), &[])?;
        let hr0t = self.mk("in", vec![r0.clone(), self.mk("bits", vec![lit(64)])]);
        let mut st0 = st.clone();
        let hr0 = self.assume(&hr0t)?;
        st0.facts.push(hr0.clone());
        st0.lfx.push(hr0);
        // (the callee-saved registers kept by the kernel)
        let rc = self.cs_held(st);
        st0 = self.with_regs(&st0, &rc);
        st0.a = a2;
        st0.w = w4.clone();
        st0.hvu = hv4;
        st0.hw = hw4;
        st0.ds = lit(8);
        st0.spec = Spec::Proc(j);
        let st2 = self.set_reg(&st0, a2, 0, 8, r0.clone());
        let rest = self.prove_pt(st2)?;
        let pc = self.close(rest, &[hw4t, hr0t], &[Self::var_id(&w4), Self::var_id(&r0)])?;
        let mut iv = vec![
            ("s", self.s.clone()),
            ("v", self.v.clone()),
            ("base", self.base.clone()),
            ("code", self.code.clone()),
            ("fr", lit(st.fr)),
            ("a", lit(a)),
            ("a2", lit(a2)),
            ("hs", st.hst.clone()),
            ("ds", st.ds.clone()),
            ("rs", st.rs.clone()),
            ("rc", self.regs_map(&rc)),
            ("w", w),
        ];
        // (sys_set_fs: rax and rdi literals of the rule's)
        if !fs {
            iv.push(("nv", nv));
        }
        iv.extend(names.iter().copied().zip(args.iter().cloned()).filter(|(nm, _)| !nm.is_empty()));
        iv.extend([("ka", al), ("xx", xl), ("dd", dl), ("k", kl), ("kw", self.kw3()), ("bkp", self.bkp.clone()), ("bka", self.bka.clone())]);
        let inst = R::Inst(rule.into(), iv);
        // (rip's step, then each register's two facts)
        let mut prem = vec![p(f(&insn.name))];
        prem.extend((0..1 + 2 * (1 + args.len())).map(|_| simp_l()));
        // (the frame of 8 bytes after it: the entry aligned -- for mmap's,
        // or a home within 4 KiB below rsp, tr.home8: no alignment needed)
        let home8 = if rule == "tr.sys_call6" {
            st.hsm.iter().find(|(c, (n, _))| *n > 0 && **c >= P64 - 4096 && **c <= P64 - 16).map(|(c, (n, x))| (*c, *n, x.clone()))
        } else {
            None
        };
        let h16 = match home8 {
            Some((c, n, x)) => {
                let h = mpf("tr.home8_intro", vec![t(&st.hst), t(&lit(c)), t(&lit(n)), t(&x), simp_l(), simp_l(), simp0(), simp0(), simp0()]);
                taut(vec![h])
            }
            None if rule == "tr.sys_call6" => taut(vec![R::S(self.sal16()?)]),
            None => s(&self.sal16()?),
        };
        prem.extend([p(self.cs_sub_pf(&rc, &st.rs)), h16]);
        // (sys_set_fs: the startup mode's objects, all bytes)
        if fs {
            prem.push(simpw(vec![f("tr.cbm_f")]));
        }
        prem.extend([s(&hk), s(&pc)]);
        self.run(&mp(inst, prem), &[])
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

    /// the function's relation at its breakpoints: about its program's
    /// exceptions only (the CFG rule's premise) -- none, or the stop's
    pub(super) fn ec_pf(&self) -> RA {
        match self.stop {
            None => p(f("tr.ec_false")),
            Some((_, k)) if self.startup => p(R::Inst("tr.ec_at_tm".into(), vec![("b", self.bm()), ("k", self.mk(if k { "true" } else { "false" }, vec![]))])),
            Some((_, k)) => p(R::Inst("tr.ec_at_t".into(), vec![("k", self.mk(if k { "true" } else { "false" }, vec![]))])),
        }
    }

    /// stopping at t, a callee stopping (k): the relation at a stop, t's
    /// state, holds at tr.at_t -- the function's own; in the CFG's walk the
    /// relation's stop case, the outer one (tr.hat_cut)
    fn hat_pf(&self, tt: u128, k: bool) -> RA {
        p(self.hat_r(tt, k))
    }

    fn hat_r(&self, tt: u128, k: bool) -> R {
        // (the startup mode's: tr.hat_nonem, tr.hat_topm, tr.hat_cutm with b false)
        let mb = |mut v: Vec<(&'static str, Term)>| {
            if self.startup {
                v.push(("b", self.bm()));
            }
            v
        };
        let nm = |n: &str| if self.startup { format!("{n}m") } else { n.to_string() };
        if !k {
            return R::Inst(nm("tr.hat_none"), mb(vec![("bka", self.bka.clone()), ("t", lit(tt))]));
        }
        let top = R::Inst(nm("tr.hat_top"), mb(vec![("t", lit(tt))]));
        match (&self.lpg, self.app(&self.bka, "or", 2)) {
            (Some(lg), Some(o)) => R::Mp(
                Box::new(R::Inst(nm("tr.hat_cut"), mb(vec![("l", o[0].clone()), ("bkp", lg.bkp.clone()), ("bka", lg.bka.clone()), ("t", lit(tt))]))),
                vec![p(top), simp0()],
            ),
            _ => top,
        }
    }

    /// stopping at t: the callee's states (below the frame) breakpoints of
    /// bkp only at t (a loop's head, a cut point: not below the frame)
    fn tbp_below(&self, bkp: &Term, frc: u128, tt: u128) -> RA {
        let hd = (|| {
            let o = self.app(bkp, "or", 2)?;
            let e = self.app(&o[0], "eq", 2)?;
            let z = self.app(&e[0], "tr.hd", 1)?;
            matches!(z[0].node(), Node::BVar(0)).then_some(())?;
            let pr = self.app(&e[1], "pair", 2)?;
            Some((pr[0].clone(), pr[1].clone(), o[1].clone()))
        })();
        let cut = (|| {
            let o = self.app(bkp, "or", 2)?;
            let c = self.app(&o[0], "tr.cut", 4)?;
            matches!(c[3].node(), Node::BVar(0)).then_some(())?;
            Some((c[0].clone(), c[1].clone(), c[2].clone(), o[1].clone()))
        })();
        if let Some((s0, fr, ct, outer)) = cut {
            // (from a deeper frame: rsp below the points' -- a call with
            // its arguments pushed)
            if nat(&fr).is_some_and(|f| f != frc) {
                return p(R::Mp(
                    Box::new(R::Inst("tr.tbp_cut_le".into(), vec![("s", s0), ("fr", fr), ("fr2", lit(frc)), ("ct", ct), ("bkp", outer.clone()), ("t", lit(tt))])),
                    vec![simp0(), self.tbp_below(&outer, frc, tt)],
                ));
            }
            return p(R::Mp(Box::new(R::Inst("tr.tbp_cut".into(), vec![("s", s0), ("fr", fr), ("ct", ct), ("bkp", outer.clone()), ("t", lit(tt))])), vec![self.tbp_below(&outer, frc, tt)]));
        }
        match hd {
            Some((h, x, outer)) => p(R::Mp(Box::new(R::Inst("tr.tbp_hd".into(), vec![("bkp", outer.clone()), ("t", lit(tt))])), vec![t(&x), t(&h), self.tbp_below(&outer, frc, tt)])),
            None => simp0(),
        }
    }

    /// the callee's states (below the frame) no breakpoints of bkp: a
    /// loop's head (`tr.hd(z) = pair(h, x) || ..`) by tr.nobp_hd, at the
    /// frame x itself; the rest likewise
    fn nobp_below(&self, bkp: &Term, frc: u128) -> RA {
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
            // (from a deeper frame: rsp below the points' -- a call with
            // its arguments pushed)
            if nat(&fr).is_some_and(|f| f != frc) {
                return p(R::Mp(
                    Box::new(R::Inst("tr.nobp_cut_le".into(), vec![("s", s0), ("fr", fr), ("fr2", lit(frc)), ("ct", ct), ("bkp", outer.clone())])),
                    vec![simp0(), self.nobp_below(&outer, frc)],
                ));
            }
            return p(R::Mp(Box::new(R::Inst("tr.nobp_cut".into(), vec![("s", s0), ("fr", fr), ("ct", ct), ("bkp", outer.clone())])), vec![self.nobp_below(&outer, frc)]));
        }
        match hd {
            Some((h, x, outer)) => p(R::Mp(Box::new(R::Inst("tr.nobp_hd".into(), vec![("bkp", outer.clone())])), vec![t(&x), t(&h), self.nobp_below(&outer, frc)])),
            None => simp0(),
        }
    }

    /// a loop's head (the spec's loop there): its claim, by induction
    fn loop_point(&mut self, st: &St) -> Result<Option<Seq>, String> {
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        if self.loop_head(qi).is_none() {
            return Ok(None);
        }
        // (the readable CFG: its loop at the body's start, by tr.cfg_lvk; a
        // hand-written one with locals in registers: its first block from
        // here, the arguments in theirs, tr.cfg_lvk_st)
        if self.cfg.is_none() && st.a == self.cfg_start {
            return self.cfg_function(st, qi, !self.cfg_regs.is_empty()).map(Some);
        }
        // (its loop reached within its first block, after the stack
        // object's allocation there: the CFG from here, tr.cfg_lvk_st)
        if self.cfg.is_none() && (self.hvo.is_some() || self.objs_n.is_some()) && self.cfg_meta.is_some() && self.lpg.is_none() {
            return self.cfg_function(st, qi, true).map(Some);
        }
        Ok(None)
    }

    /// the loop's claim at its head h for st's locals and world (c0, its
    /// registers rc's): st's homes and registers, the claim's and more
    pub(super) fn loop_at(&mut self, st: &St, h: u128, rc: &[(u128, u128, Term)], c0: Seq) -> Result<Seq, String> {
        // (the point's homes and registers: the claim's, and more)
        let hs1 = self.app(c0.concl(), "tr.lv", 13).map(|x| x[8].clone()).ok_or("the loop's claim")?;
        let rcm = self.regs_map(rc);
        let mut sub_pf = mpf("tr.hsub_empty", vec![t(&st.hst)]);
        let mut fm = self.mk("empty", vec![]);
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
                    t(&rcm),
                    t(&pcl),
                    t(&st.w),
                    p(sub_pf),
                    s(&c0),
                ],
            ),
            &[],
        )?;
        let rs = mpf(
            "tr.pt_rs_cs",
            vec![
                t(&self.s.clone()),
                t(&self.v.clone()),
                t(&self.base.clone()),
                t(&self.code.clone()),
                t(&lit(st.fr)),
                t(&lit(h)),
                t(&st.hst),
                t(&st.ds),
                t(&rcm),
                t(&st.rs),
                t(&pcl),
                t(&st.w),
                p(self.cs_sub_pf(rc, &st.rs)),
                s(&c1),
            ],
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
        self.hww = Some(st.hw.clone());
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
                ("rc", self.regs_map(&lg.rc)),
                ("hs", lg.hs.clone()),
                ("yt", lg.yt.clone()),
                ("bkp", lg.bkp.clone()),
            ],
        );
        let pcl = self.p(&st.spec);
        self.trace(|| format!("loop at {:x}: arrived", st.a));
        let r = mp(inst, vec![t(&st.hst), t(&st.rs), t(&pcl), t(&st.w), t(&y2), p(sub_pf), p(self.cs_sub_pf(&lg.rc, &st.rs)), simp_lw(vec![R::S(st.hvu.clone()), R::S(lg.hu.clone())]), simp_lw(vec![R::S(lg.hy.clone())]), p(rw)]);
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
        // (the flags kept: no cut point, no loop's head here -- tr.lvf_ptf)
        if let Some(fl) = st2.fk.clone() {
            if self.cfg.as_ref().is_some_and(|c| c.cuts.contains(&st2.a)) || self.lpg.as_ref().is_some_and(|l| l.head == st2.a) {
                return Err(format!("{:x}: a block's start or a loop's head, the flags of a compare kept across it", st2.a));
            }
            let lv = self.prove_kept(st2.clone())?;
            let args = vec![
                t(&self.s.clone()),
                t(&self.v.clone()),
                t(&self.base.clone()),
                t(&self.code.clone()),
                t(&lit(st2.fr)),
                t(&lit(st2.a)),
                t(&st2.hst),
                t(&st2.ds),
                t(&st2.rs),
                t(&self.p(&st2.spec)),
                t(&st2.w),
                self.nobp(),
                s(&lv),
            ];
            let ff = self.ff_term(&fl);
            return self.run(&mp(R::Inst("tr.lvf_ptf".into(), vec![("ff", ff)]), args), &[]);
        }
        // (a CFG walk at a cut point: its arrival)
        if self.cfg.as_ref().is_some_and(|c| c.cuts.contains(&st2.a)) && self.lpg.as_ref().is_some_and(|l| l.head == u128::MAX) {
            let c = self.save();
            let r = self.cfg_arrive(&st2);
            self.restore(c);
            match r? {
                Some(pf) => return Ok(pf),
                None => {
                    // (the machine's branch condition last assumed, its N form)
                    let last = st2.hyps.last().map(|h| format!("; the machine's condition: {} (N: {})", self.print(&h.0), self.print(&self.canon(&h.0)))).unwrap_or_default();
                    return Err(format!("{:x}: a cut point (a block's start), the spec not at a block's end{}: {}", st2.a, last, self.print(&self.p(&st2.spec))));
                }
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
    /// the map; the home written (`hkeep`'s) free of the objects
    pub(super) fn tail_h(&self, st: &St, insn: &Insn, hs2: &Term, n: usize, extra: Vec<RA>) -> Vec<RA> {
        let mut v = vec![t(&st.hst), t(hs2), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w), p(f(&insn.name))];
        v.extend((0..n).map(|_| simp_l()));
        v.extend(extra);
        let (c, k) = self.last_home.get();
        v.push(p(self.hfr_pf(c, k)));
        v.push(p(R::Slot("NEXT")));
        v
    }

    /// a rule's instance: `mp(tr.RULE, head, terms, tail)` (a rule keeping
    /// the homes past the spec's store: the homes apart from the objects
    /// first)
    pub(super) fn step(&self, rule: &str, a: u128, insn: &Insn, ts: &[&Term], tail: Vec<RA>) -> R {
        let mut args = self.head(a, insn);
        let n0 = args.len() + ts.len();
        args.extend(ts.iter().map(|x| t(x)));
        args.extend(tail);
        if HAPART.contains(&rule) {
            // (the homes: the tail's first term)
            let RA::T(hs) = &args[n0] else { panic!("tr.{}: a tail without the homes", rule) };
            let pf = self.hap_pf(&hs.clone());
            let i = args.iter().position(|x| !matches!(x, RA::T(_))).unwrap_or(args.len());
            args.insert(i, p(pf));
        }
        // (the flags kept across it: the rule's _f form, of the flags' ff)
        if let Some(ff) = &self.fk_ff {
            return mp(R::Inst(format!("tr.{}_f", rule), vec![("ff", ff.clone())]), args);
        }
        mpf(&format!("tr.{}", rule), args)
    }

    /// `tr.vabove(s, v)`: the entry's (assumed)
    pub(super) fn hva_r(&self) -> R {
        R::S(self.hva.clone().expect("tr.vabove assumed at the entry"))
    }

    /// `tr.hfree(s, c, n, v)`: the home at c no object
    pub(super) fn hfree_pf(&self, c: u128, n: u128) -> R {
        let hr = defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]);
        // (with the frame's object: apart from it by the ranges, tr.vone)
        if let Some((v0, c0, hvo)) = &self.hvo {
            return mpf("tr.hfree_one", vec![t(&self.s), t(&self.v), t(v0), t(&lit(*c0)), t(&lit(c)), t(&lit(n)), s(hvo), hr, simp0()]);
        }
        // (with several: apart from each, tr.hfree_objs)
        if self.objs_n.is_some() {
            return self.hfree_objs_pf(c, n);
        }
        mpf("tr.hfree_above", vec![t(&self.s), t(&self.v), t(&lit(c)), t(&lit(n)), p(self.hva_r()), hr])
    }

    /// `tr.hfr(s, c, n, v)`, as a home's store takes it: the callers'
    /// objects alone (`tr.vabove`)
    pub(super) fn hfr_pf(&self, c: u128, n: u128) -> R {
        if self.hvo.is_some() || self.objs_n.is_some() {
            return mpf("tr.hfr_r", vec![t(&self.s), t(&lit(c)), t(&lit(n)), t(&self.v), p(self.hfree_pf(c, n))]);
        }
        mpf("tr.hfr_l", vec![t(&self.s), t(&lit(c)), t(&lit(n)), t(&self.v), p(self.hva_r())])
    }

    /// `tr.hap(s, hs, v)`, as a store's rule takes it: the callers' objects
    /// alone (`tr.vabove`)
    pub(super) fn hap_pf(&self, hs: &Term) -> R {
        if self.hvo.is_some() || self.objs_n.is_some() {
            return mpf("tr.hap_r", vec![t(&self.s), t(hs), t(&self.v), p(self.hapart_term(hs))]);
        }
        mpf("tr.hap_l", vec![t(&self.s), t(hs), t(&self.v), p(self.hva_r())])
    }

    /// `tr.hapart(s, hs, v)` for the homes' map term hs (`hs_term`'s:
    /// `fn_update(.., c, pair(n, x))` from empty)
    pub(super) fn hapart_term(&self, hs: &Term) -> R {
        let mut cur = hs.clone();
        let mut order = Vec::new();
        while let Some(u) = self.app(&cur, "fn_update", 3).map(|u| u.to_vec()) {
            let (c, pr) = (nat(&u[1]).expect("a home's literal key"), self.app(&u[2], "pair", 2).expect("a home's pair").to_vec());
            order.push((c, nat(&pr[0]).expect("a home's literal size"), pr[1].clone()));
            cur = u[0].clone();
        }
        let mut m = self.mk("empty", vec![]);
        let mut pf = mpf("tr.hapart_empty", vec![t(&self.s), t(&self.v)]);
        for (c, n, x) in order.into_iter().rev() {
            pf = mpf("tr.hapart_upd", vec![t(&self.s), t(&m), t(&self.v), t(&lit(c)), t(&lit(n)), t(&x), p(pf), p(self.hfree_pf(c, n))]);
            m = self.upd(&m, c, n, &x);
        }
        pf
    }

    /// `tr.ofr(s, fr, v)`: no object the function's own
    pub(super) fn ofr_pf(&self, fr: &Term) -> R {
        // (with the frame's object: within any frame reaching it, tr.vone)
        if let Some((v0, c0, hvo)) = &self.hvo {
            return mpf("tr.ofr_one", vec![t(&self.s), t(fr), t(&self.v), t(v0), t(&lit(*c0)), s(hvo), simp0()]);
        }
        if self.objs_n.is_some() {
            return self.ofr_objs_pf(fr);
        }
        mpf("tr.ofr_above", vec![t(&self.s), t(fr), t(&self.v), p(self.hva_r())])
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
        self.last_home.set((c, n));
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
        let mut v = vec![t(&self.s), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(insn.len))];
        v.extend(ts.iter().map(|x| t(x)));
        v.extend([t(&st.hst), t(&st.rs), t(&st.w), p(f(&insn.name))]);
        v.extend((0..n).map(|_| simp_l()));
        let step = mpf(&format!("tr.{fs}"), v);
        self.compare_x(st, a, a2, step, fl, None)
    }

    /// ... the flags step `step` (`write`: writing a scratch register g its
    /// value x of n bytes too, tr.jcc_w)
    pub(super) fn compare_x(&mut self, st: &St, a: u128, a2: u128, step: R, fl: Flags, write: Option<(u128, Term, u128)>) -> Result<Seq, String> {
        // (setcc after it: the byte register written, tr.setcc)
        let set = self.insns.get(&a2).filter(|j| j.row == 31 && write.is_none()).map(|j| (j.fields.clone(), j.len));
        // (cmovcc r64, r64 after it: tr.cmov64)
        let cmov = self.insns.get(&a2).filter(|j| j.row == 84 && write.is_none()).map(|j| (j.fields.clone(), j.len, j.name.clone()));
        if let Some((fx, len2, iname)) = cmov {
            return self.cmov_after(st, a, a2, step, fl, fx, len2, iname);
        }
        // (neither: the flags kept to the jump on, tr.flags_set -- the
        // instructions between keeping them, their rules' _f forms)
        if set.is_none() && write.is_none() && !self.insns.get(&a2).is_some_and(|j| matches!(j.row, 127 | 128)) {
            let ff = self.ff_term(&fl);
            let args = vec![
                t(&self.s.clone()),
                t(&self.v.clone()),
                t(&self.base.clone()),
                t(&self.code.clone()),
                t(&lit(self.fr)),
                t(&lit(a)),
                t(&lit(a2)),
                t(&st.hst),
                t(&st.ds),
                t(&st.rs),
                t(&self.p(&st.spec)),
                t(&st.w),
                p(step),
                simp_l(),
                p(R::Slot("NEXT")),
            ];
            let rule = mp(R::Inst("tr.flags_set".into(), vec![("ff", ff)]), args);
            let mut st2 = st.clone();
            st2.a = a2;
            st2.fk = Some(fl);
            self.trace(|| format!("at {:x}: the flags kept to the jump on", a));
            return self.then(rule, st2);
        }
        let (j, len2, a3, tt, cc) = match &set {
            Some((fx, len2)) => {
                let x = self.pairs(fx, 3).ok_or_else(|| format!("{:x}: setcc's fields", a2))?;
                let cc = nat(&x[0]).ok_or_else(|| format!("{:x}: setcc's condition", a2))?;
                (x[2].clone(), *len2, (a2 + len2) % P64, 0, cc)
            }
            None => self.jcc(a2)?,
        };
        let (lemma, c, args, ff) = self.cc_lemma(a, &fl, cc)?;
        let mut ca: Vec<RA> = args.iter().map(t).collect();
        ca.push(defs(RP::Simp(false, vec![], vec![], false), &["tr.width"]));
        let ccf = mpf(&format!("tr.{lemma}"), ca);
        self.compare_jump(st, a, a2, step, ccf, c, ff, set.is_some(), j, len2, a3, tt, cc, write)
    }

    /// ... the compare's cmovcc r64 g, r64 h at a2 (tr.cmov64): g's value
    /// ite(c, u, x) -- named as GIMPLE's umin when c is u <= x
    #[allow(clippy::too_many_arguments)]
    fn cmov_after(&mut self, st: &St, a: u128, a2: u128, step: R, fl: Flags, fx: Term, len2: u128, iname: String) -> Result<Seq, String> {
        let bad = |m: &str| format!("{:x}: cmov: {}", a2, m);
        let x = self.pairs(&fx, 6).ok_or_else(|| bad("fields"))?;
        if nat(&x[0]) != Some(8) {
            return Err(bad("not 64-bit"));
        }
        let cc = nat(&x[1]).ok_or_else(|| bad("the condition"))?;
        let gn = nat(&x[2]).ok_or_else(|| bad("the destination"))?;
        let hn = self.tag(&x[3]).filter(|t| t.0 == 0).and_then(|t| nat(&t.1)).ok_or_else(|| bad("a source other than a register"))?;
        let u = self.need_reg(st, gn, 8)?;
        // (the source of 4 or 8 bytes: its value, zero-extended)
        let (nh, xv) = self.reg(st, hn).filter(|r| matches!(r.0, 4 | 8)).ok_or_else(|| bad("the source holds no 4- or 8-byte value"))?;
        let (lemma, c, args, ff) = self.cc_lemma(a, &fl, cc)?;
        let mut ca: Vec<RA> = args.iter().map(t).collect();
        ca.push(defs(RP::Simp(false, vec![], vec![], false), &["tr.width"]));
        let ccf = mpf(&format!("tr.{lemma}"), ca);
        let a3 = (a2 + len2) % P64;
        let e = self.mk("ite", vec![c.clone(), u.clone(), xv.clone()]);
        let le = self.mk("int_le", vec![u.clone(), xv.clone()]);
        let tv = if self.canon(&c) == self.canon(&le) { self.mk("gimple.umin", vec![lit(64), u.clone(), xv.clone()]) } else { e.clone() };
        let r = self.value(&tv);
        let hr = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![], vec![], false)), vec!["gimple.umin".into()]), &self.mk("eq", vec![r.clone(), e]), &[])?;
        let mut sv = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(a3))];
        sv.extend([t(&lit(len2)), t(&lit(cc)), t(&c), t(&x[2]), t(&lit(hn)), t(&x[4]), t(&x[5]), t(&u), t(&lit(nh)), t(&xv), t(&r), t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w)]);
        sv.extend([p(step), p(ccf), p(f(&iname))]);
        sv.extend((0..9).map(|_| simp_l()));
        sv.extend([self.nobp(), s(&hr), p(R::Slot("NEXT"))]);
        let rule = mp(R::Inst("tr.cmov64".into(), vec![("ff", ff)]), sv);
        self.scratch.insert(gn);
        let st2 = self.set_reg(st, a3, gn, 8, r);
        self.then(rule, st2)
    }

    /// the conditional jump at a, the flags fl's kept to it (tr.jcc_f):
    /// both branches walked
    pub(super) fn jcc_kept(&mut self, st: &St, a: u128, fl: Flags) -> Result<Seq, String> {
        let (j, len2, a3, tt, cc) = self.jcc(a)?;
        let (lemma, c, args, ff) = self.cc_lemma(a, &fl, cc)?;
        let mut ca: Vec<RA> = args.iter().map(t).collect();
        ca.push(defs(RP::Simp(false, vec![], vec![], false), &["tr.width"]));
        let ccf = mpf(&format!("tr.{lemma}"), ca);
        let (jn, jw) = if self.insns[&a].row == 128 { (128, 32) } else { (127, 8) };
        let mut jv = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a3)), t(&lit(tt))];
        jv.extend([t(&lit(len2)), t(&lit(jn)), t(&lit(jw)), t(&lit(cc)), t(&j), t(&c), t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w)]);
        jv.extend([p(ccf), p(f(&self.insns[&a].name))]);
        jv.extend((0..5).map(|_| simp_l()));
        jv.extend([p(R::Slot("T")), p(R::Slot("F"))]);
        let rule = mp(R::Inst("tr.jcc_f".into(), vec![("ff", ff)]), jv);
        let mut st2 = st.clone();
        st2.fk = None;
        self.branch(&st2, c, a3, tt, rule)
    }

    /// the flags' predicate ff (its bound variable the flags)
    pub(super) fn ff_term(&self, fl: &Flags) -> Term {
        match fl {
            Flags::Sub(w, x, y) => self.mk("x86i.subf", vec![lit(*w), x.clone(), y.clone(), Term::bvar(0)]),
            Flags::Log(w, r) => self.mk("x86i.logf", vec![lit(*w), r.clone(), Term::bvar(0)]),
            Flags::Zero(w, r) => self.mk("x86i.zff", vec![lit(*w), r.clone(), Term::bvar(0)]),
        }
    }

    /// the condition code cc's lemma on fl's flags: its name, the
    /// fall-through's condition c, its arguments, ff
    pub(super) fn cc_lemma(&self, a: u128, fl: &Flags, cc: u128) -> Result<(&'static str, Term, Vec<Term>, Term), String> {
        let si = |g: &Gen, x: &Term| g.mk("sint", vec![lit(32), x.clone()]);
        Ok(match fl {
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
                let (l, c) = match (cc, *w) {
                    (4, _) => ("ccl_e", self.mk("not", vec![z])),
                    (5, _) => ("ccl_ne", z),
                    // (jns after a test: r's sign, as GIMPLE writes `r <s 0`)
                    (9, 32) => ("ccl32_ns", self.mk("int_lt", vec![si(self, r), si(self, &lit(0))])),
                    (9, 64) => {
                        let s64 = |g: &Gen, x: &Term| g.mk("sint", vec![lit(64), x.clone()]);
                        ("ccl64_ns", self.mk("int_lt", vec![s64(self, r), s64(self, &lit(0))]))
                    }
                    _ => return Err(format!("{:x}: a {}-bit test's jump on condition {}: no lemma", a, w, cc)),
                };
                (l, c, vec![lit(*w), r.clone()], self.mk("x86i.logf", vec![lit(*w), r.clone(), Term::bvar(0)]))
            }
            Flags::Zero(w, r) => {
                let z = self.mk("eq", vec![r.clone(), lit(0)]);
                let (l, c) = match cc {
                    4 => ("ccz_e", self.mk("not", vec![z])),
                    5 => ("ccz_ne", z),
                    _ => return Err(format!("{:x}: a jump on condition {} after a zero flag only: no lemma", a, cc)),
                };
                (l, c, vec![lit(*w), r.clone()], self.mk("x86i.zff", vec![lit(*w), r.clone(), Term::bvar(0)]))
            }
        })
    }

    /// ... the compare's setcc or jump at a2 (`set`; j its field, its
    /// length, fall-through, target, condition code), the condition code's
    /// lemma ccf
    #[allow(clippy::too_many_arguments)]
    fn compare_jump(
        &mut self,
        st: &St,
        a: u128,
        a2: u128,
        step: R,
        ccf: R,
        c: Term,
        ff: Term,
        set: bool,
        j: Term,
        len2: u128,
        a3: u128,
        tt: u128,
        cc: u128,
        write: Option<(u128, Term, u128)>,
    ) -> Result<Seq, String> {
        // setcc r8 (al .. bl, holding u): its low byte 1 when the condition
        // holds (!c), else 0
        if set {
            let (k, g) = self.tag(&j).ok_or_else(|| format!("{:x}: setcc of other than a register", a2))?;
            let gn = nat(&g).ok_or_else(|| format!("{:x}: setcc's register not a literal", a2))?;
            if k != 0 || gn >= 4 {
                return Err(format!("{:x}: setcc of other than al .. bl", a2));
            }
            let (n, u) = self.reg(st, gn).ok_or_else(|| format!("{:x}: setcc's register holds no value (its high bytes kept)", a2))?;
            let z = self.pairs(&self.insns[&a2].fields.clone(), 3).unwrap()[1].clone();
            let b = self.mk("ite", vec![c.clone(), lit(0), lit(1)]);
            let x = self.mk("bits_set_slice", vec![lit(64), u.clone(), lit(7), lit(0), b]);
            let mut sv = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(a3))];
            sv.extend([t(&lit(len2)), t(&lit(cc)), t(&c), t(&g), t(&z), t(&lit(n)), t(&u), t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w)]);
            sv.extend([p(step), p(ccf), p(f(&self.insns[&a2].name))]);
            sv.extend((0..6).map(|_| simp_l()));
            sv.extend([self.nobp(), p(R::Slot("NEXT"))]);
            let rule = mp(R::Inst("tr.setcc".into(), vec![("ff", ff)]), sv);
            self.scratch.insert(gn);
            let st2 = self.set_reg(st, a3, gn, 8, x);
            return self.then(rule, st2);
        }
        // (the jump's row and displacement width: 127 / 8, 128 / 32)
        let (jn, jw) = if self.insns[&a2].row == 128 { (128, 32) } else { (127, 8) };
        let mut jv = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(self.fr)), t(&lit(a)), t(&lit(a2)), t(&lit(a3)), t(&lit(tt))];
        jv.extend([t(&lit(len2)), t(&lit(jn)), t(&lit(jw)), t(&lit(cc)), t(&j), t(&c), t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&st.w)]);
        if let Some((g, x, n)) = &write {
            jv.extend([t(&lit(*g)), t(x), t(&lit(*n))]);
        }
        jv.extend([p(step), p(ccf), p(f(&self.insns[&a2].name))]);
        jv.extend((0..6).map(|_| simp_l()));
        if write.is_some() {
            jv.extend([simp_l(), simp_l(), simp_l()]);
        }
        jv.extend([self.nobp(), p(R::Slot("T")), p(R::Slot("F"))]);
        let (lemma, st2) = match &write {
            Some((g, x, n)) => {
                self.scratch.insert(*g);
                ("tr.jcc_w", self.set_reg(st, st.a, *g, *n, x.clone()))
            }
            None => ("tr.jcc", st.clone()),
        };
        let rule = mp(R::Inst(lemma.into(), vec![("ff", ff)]), jv);
        self.branch(&st2, c, a3, tt, rule)
    }

    /// the statics' variable
    pub(super) fn statics_var(&self) -> Term {
        let v = self.names.iter().find(|x| x.0 == "statics").expect("statics").1;
        Term::var(v, vec![])
    }
}
