//! The instructions: each the instance of its pattern's rule.

use super::rec::*;
use super::*;

impl<'e> Gen<'e> {
    /// The instruction at st's address.
    pub(super) fn insn(&mut self, st: St) -> Result<Seq, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        self.insn_at(&st, &insn)
    }

    pub(super) fn insn_at(&mut self, st: &St, insn: &Insn) -> Result<Seq, String> {
        let a = st.a;
        let wn = self.print(&st.w);
        let a2 = (a + insn.len) % P64;
        let fs = self.print(&insn.fields);
        let bad = |what: &str| format!("{:x}: {} (row {}): {}", a, what, insn.row, fs);
        let reg = |g: &Term| nat(g).ok_or_else(|| bad("a register that is not a literal"));
        let f = insn.fields.clone();
        let fr = self.fr;
        let home_n = |hs: &BTreeMap<u128, (u128, Term)>, d: &Term, n: u128| -> Result<Term, String> {
            let d = nat(d).ok_or_else(|| bad("a displacement that is not a literal"))?;
            match hs.get(&((d + P64 - fr % P64) % P64)) {
                Some((k, x)) if *k == n => Ok(x.clone()),
                _ => Err(format!("{:x}: no {}-byte home at rsp{:+}", a, n, d as i128 - if d >= P64 / 2 { P64 as i128 } else { 0 })),
            }
        };
        let home = |hs: &BTreeMap<u128, (u128, Term)>, d: &Term| home_n(hs, d, 4);
        // (the flags of a compare kept: this instruction's rule its _f form;
        // the jump, tr.jcc_f)
        self.fk_ff = st.fk.as_ref().map(|fl| self.ff_term(fl));
        if let Some(fl) = st.fk.clone() {
            if matches!(insn.row, 127 | 128) {
                self.fk_ff = None;
                return self.jcc_kept(st, a, fl);
            }
        }
        // (in a zero-initialization: its stores only)
        if st.z.is_some() && !matches!(insn.row, 143 | 145 | 150) {
            return Err(bad("in a zero-initialization: not a store of the zero register"));
        }
        match insn.row {
            // push r64 (a callee-saved register's value x): the home at the
            // frame's new bottom, the frame 8 bytes more
            114 => {
                let g = reg(&f)?;
                let Some((8, x)) = self.reg(st, g) else { return Err(bad("push of a register not holding 8 bytes")) };
                let fr2 = fr + 8;
                if fr2 > 65536 {
                    return Err(bad("push beyond the frame's bound"));
                }
                let c = P64 - fr2;
                let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                let (_, hs2, hk) = self.hkeep(st, c, 8);
                let mut extra = vec![p(n4)];
                extra.extend((0..6).map(|_| simp_l()));
                extra.push(p(hk));
                let tr = self.step("push64", a, insn, &[&f, &x, &lit(fr2), &lit(c)], self.tail_h(st, insn, &hs2, 5, extra));
                let mut st2 = self.set_home(st, a2, c, 8, x);
                st2.fr = fr2;
                return self.then(tr, st2);
            }
            // push [rsp + d] (a home's word x -- a stack argument's): the home
            // at the frame's new bottom, the frame 8 bytes more
            118 => {
                let xs = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&xs[0]).ok_or_else(|| bad("push of a memory operand not [rsp + d]"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let c0 = self.hkey(dn);
                let Some((8, x)) = st.hsm.get(&c0).cloned() else { return Err(bad("push of a word not a home")) };
                let fr2 = fr + 8;
                if fr2 > 65536 {
                    return Err(bad("push beyond the frame's bound"));
                }
                let c = P64 - fr2;
                let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                let (_, hs2, hk) = self.hkeep(st, c, 8);
                let mut extra = vec![p(n4)];
                extra.extend((0..6).map(|_| simp_l()));
                extra.push(p(hk));
                let tr = self.step("push_m64", a, insn, &[&d, &lit(c0), &x, &lit(fr2), &lit(c)], self.tail_h(st, insn, &hs2, 6, extra));
                let mut st2 = self.set_home(st, a2, c, 8, x);
                st2.fr = fr2;
                return self.then(tr, st2);
            }
            // pop r64: g := the home at rsp (x), the frame 8 bytes less
            115 => {
                let g = reg(&f)?;
                if fr < 8 {
                    return Err(bad("pop beyond the frame"));
                }
                let c = (P64 - fr) % P64;
                let Some((8, x)) = st.hsm.get(&c).cloned() else { return Err(bad("pop of no 8-byte home")) };
                let fr2 = fr - 8;
                let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                let tr = self.step("pop64", a, insn, &[&f, &x, &lit(fr2), &lit(c)], self.tail(st, insn, 8, vec![p(n4)]));
                let mut st2 = self.set_reg(st, a2, g, 8, x);
                st2.fr = fr2;
                return self.then(tr, st2);
            }
            // cmp r64, qword [rsp + d]: g (u) against the home's word
            57 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // cmp r32 (xr: g's low 32 bits), dword [rsp + d] (u)
                if let (Some(d), Some(4)) = (self.rsp_mem(&x[2]).filter(|_| x[3] == x[2]), nat(&x[0])) {
                    let cn = self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?);
                    let u = home(&st.hsm, &d)?;
                    let (n, x0, xr) = self.low(st, g, 32)?;
                    return self.compare(st, a, a2, insn, "fs32_rh", &[&x[1], &d, &lit(cn), &lit(n), &x0, &xr, &u], 9, Flags::Sub(32, xr.clone(), u.clone()));
                }
                let d = self.rsp_mem(&x[2]).filter(|_| nat(&x[0]) == Some(8) && x[3] == x[2]).ok_or_else(|| bad("not cmp r64, qword [rsp + d]"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let cn = self.hkey(dn);
                let Some((8, xv)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                // (the register's whole word: its value, of any width)
                let (ng, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                return self.compare(st, a, a2, insn, "fs64_rh", &[&x[1], &d, &lit(cn), &lit(ng), &xv, &u], 8, Flags::Sub(64, u.clone(), xv.clone()));
            }
            // pxor x, x: a zero-initialization begun -- the spec's store of
            // zeros made at once (tr.ptz_red), the machine's by the stores of x
            135 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let xr = reg(&x[0])?;
                if self.tag(&x[1]).map(|(k, r)| (k, nat(&r))) != Some((0, Some(xr))) {
                    return Err(bad("pxor of two registers"));
                }
                let (hc, _, st2, red, sa, so) = self.spec_store_x(st, None, None)?;
                if so.data.is_none() {
                    return Err(bad("pxor before a spec's store that is not of zeros"));
                }
                let o = nat(&so.off).ok_or_else(|| bad("a zero-initialization at an offset that is not a literal"))?;
                let tr = self.step("pxor_z", a, insn, &[&x[0], &x[2], &x[3], &sa], self.tail(st, insn, 3, vec![]));
                let rd = mpf(
                    "tr.ptz_red",
                    vec![
                        t(&self.s.clone()),
                        t(&self.v.clone()),
                        t(&self.base.clone()),
                        t(&self.code.clone()),
                        t(&lit(st.fr)),
                        t(&lit(a2)),
                        t(&st.hst),
                        t(&st.ds),
                        t(&st.rs),
                        t(&lit(xr)),
                        t(&sa),
                        t(&lit(so.n)),
                        t(&so.p),
                        t(&so.off),
                        t(&self.p(&st.spec)),
                        t(&self.p(&st2.spec)),
                        t(&st.w),
                        t(&st2.w),
                        p(self.hap_pf(&st.hst)),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        s(&hc),
                        simp0(),
                        p(red),
                        p(R::Slot("NEXT")),
                    ],
                );
                let mut st3 = st2;
                st3.a = a2;
                st3.z = Some((xr, so.p.clone(), o, so.n));
                return self.then(fill(tr, "NEXT", &rd), st3);
            }
            // movups / movaps / movq [b + d], x (x zero): the next c of the bytes
            143 | 145 | 150 => {
                let Some((xr, bz, o, k)) = st.z.clone() else { return Err(bad("a store of an xmm register outside a zero-initialization")) };
                let (c, nf) = if insn.row == 150 { (8u128, 5) } else { (16u128, 4) };
                let x = self.pairs(&f, nf).ok_or_else(|| bad("fields"))?;
                if reg(&x[0])? != xr {
                    return Err(bad("a store of an xmm register not zeroed"));
                }
                // ([rsp + d]: a frame's stack object -- its address the
                // frame's at the offset cd, shown the bytes' by N; movaps's
                // aligned by the entry's alignment)
                if let Some(d) = self.rsp_mem(&x[1]).filter(|_| c <= k) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let cd = self.hkey(dn);
                    let at = |g: &Gen, o: u128| g.mk("bits_add", vec![lit(64), bz.clone(), lit(o)]);
                    let (aa, a2t) = (at(self, o), at(self, o + c));
                    let ha = self.mk("tr.ha", vec![self.s.clone(), lit(cd)]);
                    let q = self.addr_eq(st, &aa, &ha).map_err(|e| format!("{:x}: the zero-initialization's bytes at {} + {}, the machine's at [rsp + {}]: {}", a, self.print(&bz), o, dn, e))?;
                    let cdt = lit(cd);
                    let mut ts: Vec<&Term> = vec![&x[0], &d, &cdt];
                    ts.extend(x[2..].iter());
                    let (kt, k2t) = (lit(k), lit(k - c));
                    ts.extend([&aa, &kt, &a2t, &k2t]);
                    let mut extra = vec![simp0(), s(&q)];
                    if insn.row == 143 {
                        if (cd + 8) % 16 != 0 {
                            return Err(format!("{:x}: movaps at a frame offset not aligned to 16", a));
                        }
                        let sal = self.sal16()?;
                        let rsp = taut(vec![R::Expand(Box::new(self.hva_r()), vec!["tr.vabove".into()])]);
                        let al = mpf("tr.ha_al16", vec![t(&self.s.clone()), t(&lit(cd)), s(&sal), rsp, simp0(), simp0()]);
                        extra.push(simpw(vec![R::S(q.clone()), al]));
                    }
                    extra.extend([simp0(), simp0(), simp0(), arith(vec![]), arith(vec![])]);
                    let rule = match insn.row {
                        143 => "zst_aps_rsp",
                        145 => return Err(bad("movups at a frame offset (not yet)")),
                        _ => "zst_q_rsp",
                    };
                    let mut tl = self.tail(st, insn, 5, extra);
                    tl.insert(6, self.nobp());
                    let mut tr = self.step(rule, a, insn, &ts, tl);
                    let mut st2 = st.clone();
                    st2.a = a2;
                    if k == c {
                        let ex = mpf(
                            "tr.ptz_exit",
                            vec![
                                t(&self.s.clone()),
                                t(&self.v.clone()),
                                t(&self.base.clone()),
                                t(&self.code.clone()),
                                t(&lit(st.fr)),
                                t(&lit(a2)),
                                t(&st.hst),
                                t(&st.ds),
                                t(&st.rs),
                                t(&lit(xr)),
                                t(&a2t),
                                t(&self.p(&st.spec)),
                                t(&st.w),
                                simp_l(),
                                p(R::Slot("NEXT")),
                            ],
                        );
                        tr = fill(tr, "NEXT", &ex);
                        st2.z = None;
                    } else {
                        st2.z = Some((xr, bz, o + c, k - c));
                    }
                    return self.then(tr, st2);
                }
                let (bn, b, d) = self.base_disp(&x[1]).ok_or_else(|| bad("not [b + d]"))?;
                let bv = self.need_reg(st, bn, 8)?;
                if self.canon(&bv) != self.canon(&bz) || nat(&d) != Some(o) || c > k {
                    return Err(format!("{:x}: the machine stores {} bytes at {} + {}, the zero-initialization's rest: {} bytes at {} + {}", a, c, self.print(&bv), self.print(&d), k, self.print(&bz), o));
                }
                let at = |g: &Gen, o: u128| g.mk("bits_add", vec![lit(64), bz.clone(), lit(o)]);
                let (aa, a2t) = (at(self, o), at(self, o + c));
                let mut ts: Vec<&Term> = vec![&x[0], &b, &d];
                ts.extend(x[2..].iter());
                let (kt, k2t) = (lit(k), lit(k - c));
                ts.extend([&bv, &aa, &kt, &a2t, &k2t]);
                let rule = if insn.row == 145 { "zst_ups" } else { "zst_q" };
                // (mid-sequence: its address no breakpoint, after the decode fact)
                let mut tl = self.tail(st, insn, 11, vec![arith(vec![]), arith(vec![])]);
                tl.insert(6, self.nobp());
                let mut tr = self.step(rule, a, insn, &ts, tl);
                let mut st2 = st.clone();
                st2.a = a2;
                if k == c {
                    // (all stored: the plain claim on)
                    let ex = mpf(
                        "tr.ptz_exit",
                        vec![
                            t(&self.s.clone()),
                            t(&self.v.clone()),
                            t(&self.base.clone()),
                            t(&self.code.clone()),
                            t(&lit(st.fr)),
                            t(&lit(a2)),
                            t(&st.hst),
                            t(&st.ds),
                            t(&st.rs),
                            t(&lit(xr)),
                            t(&a2t),
                            t(&self.p(&st.spec)),
                            t(&st.w),
                            simp_l(),
                            p(R::Slot("NEXT")),
                        ],
                    );
                    tr = fill(tr, "NEXT", &ex);
                    st2.z = None;
                } else {
                    st2.z = Some((xr, bz, o + c, k - c));
                }
                return self.then(tr, st2);
            }
            // mov r32/r64, [rsp + d]: the home's value
            76 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // mov r64 / r32, [rip + d]: the spec's load of a static's word
                if let Some(m) = self.memop(&x[2]).filter(|m| self.tag(&m["base"]).is_some_and(|b| b.0 == 1) && matches!(nat(&x[0]), Some(8) | Some(4))) {
                    let n = nat(&x[0]).unwrap();
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = (a2 + d) % P64;
                    let (pp, off, hc) = self.static_mem_hyp(st, biga, n)?;
                    let rule = if n == 8 { "load64_rip" } else { "load32_rip" };
                    let v = self.parse(&format!("bits_of_int({}, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), {}))", 8 * n, self.print(&pp), self.print(&off), n))?;
                    // (the spec's load of the static at offset 0 already
                    // named -- at pp itself: that name, equal by evaluation)
                    let shared = if nat(&off) == Some(0) {
                        let v0 = self.parse(&format!("bits_of_int({}, gimple.bytes_at(app({wn}, \"vm\"), {}, {}))", 8 * n, self.print(&pp), n))?;
                        let c = self.canon(&v0);
                        if matches!(c.node(), Node::Var(..)) {
                            let e = self.mk("eq", vec![c.clone(), v.clone()]);
                            Some((c, s(&self.evp(&RP::Simp(false, vec![], vec![], false), &e, &[])?)))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let (v, hr) = match shared {
                        Some(x) => x,
                        None => self.result(&v)?,
                    };
                    let tr = self.step(rule, a, insn, &[&x[1], &lit(d), &x[4], &pp, &off, &v], self.tail(st, insn, 6, vec![s(&hc), hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, n, v);
                    return self.then(tr, st2);
                }
                // mov r64, fs:[d]: the spec's load at the world's fs_base + d
                // (the thread pointer's)
                if let Some(m) = self.memop(&x[2]).filter(|m| nat(&m["seg"]) == Some(2) && self.tag(&m["base"]).is_some_and(|b| b.0 == 0) && nat(&x[0]) == Some(8)) {
                    let d = m["disp"].clone();
                    // (fs:[0x28], the stack protector's word: the ABI's,
                    // the entry's -- no spec's load, tr.load64_can)
                    if nat(&d) == Some(40) {
                        let v = self.mk("tr.canv", vec![self.s.clone()]);
                        let tr = self.step("load64_can", a, insn, &[&x[1], &x[4]], self.tail(st, insn, 2, vec![simp0()]));
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 8, v);
                        return self.then(tr, st2);
                    }
                    // (fs:[0], the thread pointer: the spec's thread_ptr(),
                    // the thread sound, tr.load64_tp)
                    if nat(&d) != Some(0) {
                        return Err(bad("an fs: load other than the thread pointer or the stack protector's word"));
                    }
                    let fs = self.mk("app", vec![st.w.clone(), Term::bytes(b"fs_base")]);
                    let cond = self.mk("abi.thread_ok", vec![self.mk("app", vec![st.w.clone(), Term::bytes(b"vm")]), fs.clone()]);
                    let hc = self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()).ok_or_else(|| format!("{:x}: a thread pointer's load the spec does not make", st.a))?;
                    let v = self.mk("bits_of_int", vec![lit(64), fs]);
                    let tr = self.step("load64_tp", a, insn, &[&x[1], &x[4]], self.tail(st, insn, 2, vec![s(&hc)]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, v);
                    return self.then(tr, st2);
                }
                // mov r64, [b + i]: the spec's load at the address computed
                // otherwise
                if let Some(m) = self.memop(&x[2]).filter(|m| matches!(self.app(&m["index"], "some", 1), Some(_)) && nat(&m["scale"]) == Some(1) && nat(&m["disp"]) == Some(0)) {
                    let (Some((2, b)), Some(iv)) = (self.tag(&m["base"]), self.app(&m["index"], "some", 1).map(|x| x[0].clone())) else { return Err(bad("not [b + i]")) };
                    if nat(&x[0]) != Some(8) {
                        return Err(bad("not mov r64, [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&iv)?);
                    for r in [bn, inn] {
                        if let Some(pf) = self.widen(st, r, 8)? {
                            return Ok(pf);
                        }
                    }
                    let bv = self.need_reg(st, bn, 8)?;
                    let ixv = self.need_reg(st, inn, 8)?;
                    let ea = self.mk("bits_add", vec![lit(64), bv.clone(), ixv.clone()]);
                    let (pp, off, hc, heq) = self.mem_hyp_eq(st, &ea, 8)?;
                    let v = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 8))", self.print(&pp), self.print(&off)))?;
                    let (v, hr) = self.result(&v)?;
                    let tr = self.step("load64_bi", a, insn, &[&x[1], &b, &iv, &x[4], &bv, &ixv, &pp, &off, &v], self.tail(st, insn, 10, vec![s(&heq), s(&hc), hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, v);
                    return self.then(tr, st2);
                }
                // mov r64 / r32, [b + d] (b holding a pointer): the spec's field load
                if self.rsp_mem(&x[2]).is_none() && matches!(nat(&x[0]), Some(8) | Some(4)) {
                    let n = nat(&x[0]).unwrap();
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let rd = |ea: &str| format!("bits_of_int({}, gimple.bytes_at(app({wn}, \"vm\"), {ea}, {}))", 8 * n, n);
                    let eb = format!("bits_add(64, {}, {})", self.print(&bp), self.print(&d));
                    let v = self.parse(&rd(&eb))?;
                    // (b holding a static's address, a literal: the spec's
                    // load at that static, as its symbol names it -- the
                    // fact by simp)
                    let at_static = self.eval_lit(&bp).zip(nat(&d)).map(|(pv, dv)| (pv + dv) % P64);
                    let (tr, v) = if n == 8 {
                        // (also the bytes of the spec's store there: a bitfield's)
                        let (hc, wt) = match (self.mem_hyp_rw(st, &bp, &d, 8), at_static) {
                            (Ok((h, wt)), _) => (s(&h), wt),
                            (Err(_), Some(av)) => (simp_lw(vec![R::S(self.static_mem_hyp(st, av, 8)?.2)]), self.mk("false", vec![])),
                            (Err(e), None) => return Err(e),
                        };
                        let (v, hr) = self.result(&v)?;
                        (self.step("load64_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &wt, &v], self.tail(st, insn, 6, vec![hc, hr])), v)
                    } else {
                        let hc = self.mem_hyp(st, &bp, &d, n)?;
                        // (at offset 0: the address as the spec read it, p or p + 0)
                        let v0 = self.parse(&rd(&self.print(&bp)))?;
                        let (ea, v) = if nat(&d) == Some(0) && self.val_of.contains_key(&self.expand(&v0)) { (bp.clone(), v0) } else { (self.parse(&eb)?, v) };
                        let (v, hr) = self.result(&v)?;
                        (self.step("load32_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &ea, &v], self.tail(st, insn, 7, vec![s(&hc), hr])), v)
                    };
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, n, v);
                    return self.then(tr, st2);
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let c = lit(self.hkey(dn));
                // (above the return slot, no home: a stack argument's)
                let hk = self.hkey(dn);
                if let (8, None, Some(sa)) = (n, st.hsm.get(&hk), self.sargs.clone()) {
                    let j = hk.wrapping_sub(8) / 8;
                    if hk >= 8 && hk % 8 == 0 && j < sa.args.len() as u128 {
                        let (xv, hlt, hx) = sa.args[j as usize].clone();
                        let tr = self.step(
                            "load64_sarg",
                            a,
                            insn,
                            &[&x[1], &d, &c, &x[3], &x[4], &sa.stk, &lit(j), &xv],
                            self.tail(st, insn, 6, vec![s(&sa.hsa), simpw(vec![R::S(sa.hso.clone())]), s(&sa.hstk), s(&hlt), s(&hx)]),
                        );
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 8, xv);
                        return self.then(tr, st2);
                    }
                }
                // (a stack object's bytes, allocated: the spec's load there)
                if n == 8 && ((self.hvo.is_some() && self.objk.contains(&hk)) || self.obj_byte(hk)) {
                    let ha = self.mk("tr.ha", vec![self.s.clone(), lit(hk)]);
                    let (pp, off, hc, heq) = self.mem_hyp_eq(st, &ha, 8)?;
                    let v = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 8))", self.print(&pp), self.print(&off)))?;
                    let (v, hr) = self.result(&v)?;
                    let tr = self.step("load64_obj", a, insn, &[&x[1], &d, &c, &x[4], &pp, &off, &v], self.tail(st, insn, 6, vec![s(&heq), s(&hc), hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, v);
                    return self.then(tr, st2);
                }
                let v = match (n, st.hsm.get(&self.hkey(dn))) {
                    (4, _) => home(&st.hsm, &d)?,
                    (8, Some((8, x))) => x.clone(),
                    _ => return Err(bad("no home of the load's width")),
                };
                let rule = if n == 8 { "load64_home" } else { "load32_home" };
                let tr = self.step(rule, a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v], self.tail(st, insn, 6, vec![]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, n, v);
                self.then(tr, st2)
            }
            // neg / not r32, neg r64
            64 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let op = nat(&x[1]);
                if !(op == Some(3) || op == Some(2)) || k != 0 {
                    return Err(bad("not neg / not r32"));
                }
                let gn = reg(&g)?;
                // neg r64
                if nat(&x[0]) == Some(8) && op == Some(3) {
                    if let Some(pf) = self.widen(st, gn, 8)? {
                        return Ok(pf);
                    }
                    let u = self.need_reg(st, gn, 8)?;
                    let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(64), lit(0), u.clone()]))?;
                    let tr = self.step("neg64", a, insn, &[&g, &x[3], &u, &r], self.tail(st, insn, 4, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, r);
                    return self.then(tr, st2);
                }
                // neg r32 of a 64-bit word: of its low half
                if let (Some(3), Some((8, w8))) = (op, self.reg(st, gn)) {
                    let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(32), lit(0), self.mk("bits_of_int", vec![lit(32), w8.clone()])]))?;
                    let tr = self.step("neg32_w", a, insn, &[&g, &x[3], &w8, &r], self.tail(st, insn, 4, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(tr, st2);
                }
                let u = self.need_reg(st, gn, 4)?;
                let (rule, r) = if op == Some(2) { ("not32", self.mk("bits_not", vec![lit(32), u.clone()])) } else { ("neg32", self.mk("bits_sub", vec![lit(32), lit(0), u.clone()])) };
                let (r, hr) = self.result(&r)?;
                let tr = self.step(rule, a, insn, &[&g, &x[3], &u, &r], self.tail(st, insn, 4, vec![hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // and r32, [rsp + d]
            48 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&st.hsm, &d)?;
                let u = self.need_reg(st, g, 4)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                // (the result as the spec orders it)
                let op = self.mk("bits_and", vec![lit(32), v.clone(), u.clone()]);
                let (r, hr) = self.result(&op)?;
                let tr = self.step("and32_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
            }
            // div qword [rsp + d] (rdx 0, the slot's word not 0 -- the spec's
            // division defined): rax := rax / x, rdx := rax mod x
            68 => {
                let x = self.pairs(&f, 3).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[1]).ok_or_else(|| bad("a division not by a home"))?;
                if nat(&x[0]) != Some(8) {
                    return Err(bad("a division not of 64 bits"));
                }
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let c = lit(self.hkey(dn));
                let xv = home_n(&st.hsm, &d, 8)?;
                let (n0, u) = self.reg(st, 0).ok_or_else(|| bad("rax holds no value"))?;
                let (n2, z) = self.reg(st, 2).ok_or_else(|| bad("rdx holds no value"))?;
                if self.eval_lit(&z) != Some(0) {
                    return Err(bad("rdx not 0 (a 128-bit dividend)"));
                }
                let nz = self.mk("not", vec![self.mk("eq", vec![xv.clone(), lit(0)])]);
                let hnz = self.hyp_find(&st.hyps, &nz).map(|h| h.1.clone()).ok_or_else(|| format!("{:x}: a division by {}, not known to be not 0", a, self.print(&xv)))?;
                let (q, hq) = self.result(&self.mk("int_div", vec![u.clone(), xv.clone()]))?;
                let (r, hr) = self.result(&self.mk("int_mod", vec![u.clone(), xv.clone()]))?;
                let tr = self.step("div64_home", a, insn, &[&d, &c, &x[2], &xv, &lit(n0), &u, &lit(n2), &q, &r], self.tail(st, insn, 9, vec![s(&hnz), hq, hr]));
                self.scratch.insert(0);
                self.scratch.insert(2);
                let st2 = self.set_reg(st, a2, 0, 8, q);
                let st2 = self.set_reg(&st2, a2, 2, 8, r);
                self.then(tr, st2)
            }
            // xor r32, [rsp + d]
            54 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&st.hsm, &d)?;
                let u = self.need_reg(st, g, 4)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let op = self.mk("bits_xor", vec![lit(32), u.clone(), v.clone()]);
                let (r, hr) = self.result(&op)?;
                let tr = self.step("xor32_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
            }
            // imul r64, [rsp + d]: the product (as the spec orders it)
            70 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                // imul r32, r32 / [rsp + d]
                if nat(&x[0]) == Some(4) {
                    let g = reg(&x[1])?;
                    let u = self.need_reg(st, g, 4)?;
                    let (rule, v, mid): (&str, Term, Vec<Term>) = if let Some((0, h)) = self.tag(&x[2]) {
                        ("imul32_rr", self.need_reg(st, reg(&h)?, 4)?, vec![h])
                    } else {
                        let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not imul r32, r32 / [rsp + d]"))?;
                        let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                        ("imul32_home", home(&st.hsm, &d)?, vec![d, c])
                    };
                    let op = self.mk("bits_mul", vec![lit(32), u.clone(), v.clone()]);
                    let (r, hr) = self.result(&op)?;
                    let mut ts: Vec<&Term> = vec![&x[1]];
                    ts.extend(mid.iter());
                    ts.extend([&x[3], &x[4], &v, &u, &r]);
                    let n = if rule == "imul32_rr" { 7 } else { 8 };
                    let tr = self.step(rule, a, insn, &ts, self.tail(st, insn, n, vec![hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, r);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not imul r64, [rsp + d]"));
                }
                // imul r64, r64
                if let Some((0, h)) = self.tag(&x[2]) {
                    let (g, hn) = (reg(&x[1])?, reg(&h)?);
                    for r in [g, hn] {
                        if let Some(pf) = self.widen(st, r, 8)? {
                            return Ok(pf);
                        }
                    }
                    let u = self.need_reg(st, g, 8)?;
                    let v = self.need_reg(st, hn, 8)?;
                    let op = self.mk("bits_mul", vec![lit(64), u.clone(), v.clone()]);
                    let (r, hr) = self.result(&op)?;
                    let tr = self.step("imul64_rr", a, insn, &[&x[1], &h, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(tr, st2);
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home_n(&st.hsm, &d, 8)?;
                let u = self.need_reg(st, g, 8)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let op = self.mk("bits_mul", vec![lit(64), u.clone(), v.clone()]);
                let (r, hr) = self.result(&op)?;
                let tr = self.step("imul64_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, r);
                self.then(tr, st2)
            }
            // sub r32, [rsp + d]
            51 if self.pairs(&f, 5).is_some_and(|x| nat(&x[0]) == Some(4)) => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&st.hsm, &d)?;
                let u = self.need_reg(st, g, 4)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(32), u.clone(), v.clone()]))?;
                let tr = self.step("sub32_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
            }
            // sub r64, [rsp + d]
            51 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not sub r64, [rsp + d]"));
                }
                // sub r64, fs:[d]; jcc: g's word less the spec's at the world's
                // fs_base + d (the stack protector's check), the jump on it
                if let Some(m) = self.memop(&x[2]).filter(|m| nat(&m["seg"]) == Some(2) && self.tag(&m["base"]).is_some_and(|b| b.0 == 0)) {
                    let d = m["disp"].clone();
                    let g = reg(&x[1])?;
                    let u = self.need_reg(st, g, 8)?;
                    // (fs:[0x28]: the entry's stack protector's word, the
                    // ABI's -- its copy from the frame less it, tr.fsub64_can)
                    if nat(&d) == Some(40) {
                        let y = self.mk("tr.canv", vec![self.s.clone()]);
                        let r = self.mk("bits_sub", vec![lit(64), u.clone(), y.clone()]);
                        let mut v = self.head(a, insn);
                        v.extend([&x[1], &x[4], &u, &st.hst, &st.rs, &st.w].into_iter().map(t));
                        v.push(p(R::F(insn.name.clone())));
                        v.extend((0..4).map(|_| simp_l()));
                        v.push(simp0());
                        let step = mpf("tr.fsub64_can", v);
                        return self.compare_x(st, a, a2, step, Flags::Sub(64, u, y), Some((g, r, 8)));
                    }
                    let fs = self.mk("app", vec![st.w.clone(), Term::bytes(b"fs_base")]);
                    let hc = self.mem_hyp(st, &fs, &d, 8)?;
                    let y = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 8))", self.print(&fs), self.print(&d)))?;
                    let (y, hy) = self.result(&y)?;
                    let r = self.mk("bits_sub", vec![lit(64), u.clone(), y.clone()]);
                    let mut v = self.head(a, insn);
                    v.extend([&x[1], &d, &x[4], &u, &y, &st.hst, &st.rs, &st.w].into_iter().map(t));
                    v.push(p(R::F(insn.name.clone())));
                    v.extend((0..5).map(|_| simp_l()));
                    v.extend([s(&hc), hy]);
                    let step = mpf("tr.fsub64_fs", v);
                    return self.compare_x(st, a, a2, step, Flags::Sub(64, u, y), Some((g, r, 8)));
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home_n(&st.hsm, &d, 8)?;
                let u = self.need_reg(st, g, 8)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(64), u.clone(), v.clone()]))?;
                let tr = self.step("sub64_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, r);
                self.then(tr, st2)
            }
            // imul r32, r32, imm
            89 => {
                let x = self.pairs(&f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let (k, h) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 {
                    return Err(bad("imul of memory"));
                }
                let hn = reg(&h)?;
                let c = nat(&x[5]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                if c >= 1 << 31 {
                    return Err(bad("a negative immediate (no product lemma yet)"));
                }
                // imul r64, r64, imm32: the word product
                if nat(&x[0]) == Some(8) {
                    let u = self.need_reg(st, hn, 8)?;
                    let (r, hr) = self.result(&self.mk("bits_mul", vec![lit(64), u.clone(), x[5].clone()]))?;
                    let tr = self.step("imul64", a, insn, &[&x[1], &h, &x[3], &x[4], &x[5], &u, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(tr, st2);
                }
                let u = self.need_reg(st, hn, 4)?;
                let by = self.imul_fact(c)?;
                let (r, hr) = self.result(&self.mk("bits_mul", vec![lit(32), u.clone(), x[5].clone()]))?;
                let tr = self.step("imul32", a, insn, &[&x[1], &h, &x[3], &x[4], &x[5], &u, &r], self.tail(st, insn, 4, vec![s(&by), simp_l(), simp_l(), hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
            }
            // shr/shl r16/r32/r64, imm
            // lock cmpxchg [b], r32 (eax t): the spec's compare-and-swap at
            // b's pointer; eax its old dword after
            97 => {
                let x = self.pairs(&f, 6).ok_or_else(|| bad("fields"))?;
                let (Some((bn, b, d)), Some(4)) = (self.base_disp(&x[2]), nat(&x[0])) else { return Err(bad("not lock cmpxchg [b], r32")) };
                if nat(&d) != Some(0) || bn == 4 {
                    return Err(bad("lock cmpxchg at [b + d], d not 0"));
                }
                let g = reg(&x[1])?;
                let bv = self.need_reg(st, bn, 8)?;
                let sv = self.need_reg(st, g, 4)?;
                let tv = self.need_reg(st, 0, 4)?;
                let (hc, _, st2, red, _, so) = self.spec_store_x(st, Some(&bv), Some(4))?;
                let Some((t2, s2, dv)) = so.cas.clone() else { return Err(bad("a compare-and-swap the spec does not make here")) };
                if self.canon(&t2) != self.canon(&tv) || self.canon(&s2) != self.canon(&sv) {
                    return Err(format!("{:x}: the machine's compare-and-swap of {}, {}; the spec's of {}, {}", a, self.print(&tv), self.print(&sv), self.print(&t2), self.print(&s2)));
                }
                let (dv, hr) = self.result(&dv)?;
                let tr = self.step("cas32_b", a, insn, &[&x[1], &b, &x[3], &x[4], &x[5], &bv, &tv, &sv, &dv], self.tail_s(st, &st2, insn, 11, vec![hr], &hc, &red));
                self.scratch.insert(0);
                let st3 = self.set_reg(&st2, a2, 0, 4, dv);
                self.then(tr, st3)
            }
            // lock or [b], r32: the spec's or32 at b's pointer
            101 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let (Some((bn, b, d)), Some(4)) = (self.base_disp(&x[2]), nat(&x[0])) else { return Err(bad("not lock or [b], r32")) };
                if nat(&d) != Some(0) || bn == 4 {
                    return Err(bad("lock or at [b + d], d not 0"));
                }
                let g = reg(&x[1])?;
                let bv = self.need_reg(st, bn, 8)?;
                let sv = self.need_reg(st, g, 4)?;
                let (hc, _, st2, red, _, so) = self.spec_store_x(st, Some(&bv), Some(4))?;
                let Some(s2) = so.or.clone() else { return Err(bad("a locked or the spec does not make here")) };
                if self.canon(&s2) != self.canon(&sv) {
                    return Err(format!("{:x}: the machine's or of {}; the spec's of {}", a, self.print(&sv), self.print(&s2)));
                }
                let tr = self.step("or32_b", a, insn, &[&x[1], &b, &x[3], &x[4], &bv, &sv], self.tail_s(st, &st2, insn, 9, vec![], &hc, &red));
                let mut st3 = st2;
                st3.a = a2;
                self.then(tr, st3)
            }
            // cmp ax / eax, imm16 / imm32: rax's low bits (u) against k
            58 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                // cmp rax, imm32: rax against the immediate sign-extended
                if nat(&x[0]) == Some(8) {
                    let imm = nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    let (n, u) = self.reg(st, 0).ok_or_else(|| bad("rax holds no value of the procedure"))?;
                    let kk = lit(if imm >= 1 << 31 { imm + (P64 - (1 << 32)) } else { imm });
                    return self.compare(st, a, a2, insn, "fs64_rax", &[&x[1], &kk, &lit(n), &u], 5, Flags::Sub(64, u.clone(), kk.clone()));
                }
                let (fs, w) = match nat(&x[0]) {
                    Some(2) => ("fs16_ax", 16),
                    Some(4) => ("fs32_eax", 32),
                    _ => return Err(bad("not cmp ax / eax / rax, imm")),
                };
                let (n, x0, u) = self.low(st, 0, w)?;
                let k = x[1].clone();
                self.compare(st, a, a2, insn, fs, &[&k, &k, &lit(n), &x0, &u], 6, Flags::Sub(w, u.clone(), k.clone()))
            }
            // shr / shl r32, shl r64, cl: by the spec's count (below the
            // width, a fact in scope)
            74 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not shr / shl r32, cl")) };
                let h = match nat(&x[1]) {
                    Some(5) => "shr",
                    Some(4) => "shl",
                    _ => return Err(bad("not shr / shl r32, cl")),
                };
                let n = nat(&x[0]).unwrap_or(0);
                if n != 4 && !(n == 8 && h == "shl") {
                    return Err(bad("not shr / shl r32, shl r64, cl"));
                }
                let gn = reg(&g)?;
                if let Some(pf) = self.widen(st, gn, n)? {
                    return Ok(pf);
                }
                let w = 8 * n;
                let u = self.need_reg(st, gn, n)?;
                let c = self.need_reg(st, 1, 4)?;
                let lt = self.mk("int_lt", vec![c.clone(), lit(w)]);
                // (a fact in scope, or one of the count computed otherwise:
                // as a condition is decided)
                let hc = match self.hyp_find(&st.hyps, &lt).map(|h| h.1.clone()) {
                    Some(h) => h,
                    None => match self.guard_val(&lt, &st.hyps) {
                        Some((true, fs)) => self.evp(&RP::Simp(true, fs.into_iter().map(R::S).collect(), vec![], false), &lt, &[])?,
                        _ => return Err(bad("a shift by cl not known below the width")),
                    },
                };
                let (r, hr) = self.result(&self.mk(&format!("bits_{h}"), vec![lit(w), u.clone(), c.clone()]))?;
                let tr = self.step(&format!("{h}{w}_cl"), a, insn, &[&g, &x[3], &c, &u, &r], self.tail(st, insn, 6, vec![s(&hc), hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, n, r);
                self.then(tr, st2)
            }
            // shr r8, c (al .. bl): the machine's value
            32 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                // (op, rm, rm8, count): the shift on rm8
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let c = nat(&x[3]).ok_or_else(|| bad("a count that is not a literal"))?;
                let gn = reg(&g)?;
                if nat(&x[0]) != Some(5) || k != 0 || gn >= 4 || c == 0 || c >= 8 {
                    return Err(bad("not shr al .. bl, 1..7"));
                }
                let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                // (a byte, zero-extended: u >> c)
                if n <= 4 {
                    let (r, hr) = self.result(&self.mk("bits_shr", vec![lit(8), u.clone(), x[3].clone()]))?;
                    let tr = self.step("shr8_imm_b", a, insn, &[&g, &x[1], &x[3], &lit(n), &u, &r], self.tail(st, insn, 9, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 1, r);
                    return self.then(tr, st2);
                }
                let r = self.parse(&format!("bits_set_slice(64, {u}, 7, 0, bits_shr(8, bits_slice({u}, 7, 0), {c}))", u = self.print(&u)))?;
                let (r, hr) = self.result(&r)?;
                let tr = self.step("shr8_imm", a, insn, &[&g, &x[1], &x[3], &lit(n), &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 8, r);
                self.then(tr, st2)
            }
            72 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let c = nat(&x[4]).ok_or_else(|| bad("a count that is not a literal"))?;
                let (size, op) = (nat(&x[0]).ok_or_else(|| bad("fields"))?, nat(&x[1]).ok_or_else(|| bad("fields"))?);
                if k != 0 || c == 0 || c >= 8 * size {
                    return Err(bad("not a register shift by 1..width-1"));
                }
                let gn = reg(&g)?;
                match (size, op) {
                    (4, 5) => {}
                    // shl r64, c
                    (8, 4) if c != 12 || !self.reg(st, gn).is_some_and(|(_, u)| self.app(&self.expand(&u), "bits_shr", 3).is_some()) => {
                        if let Some(pf) = self.widen(st, gn, 8)? {
                            return Ok(pf);
                        }
                        let u = self.need_reg(st, gn, 8)?;
                        let (r, hr) = self.result(&self.mk("bits_shl", vec![lit(64), u.clone(), x[4].clone()]))?;
                        let tr = self.step("shl64_imm", a, insn, &[&g, &x[3], &x[4], &u, &r], self.tail(st, insn, 7, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shr r64, c
                    (8, 5) => {
                        let u = self.need_reg(st, gn, 8)?;
                        let (r, hr) = self.result(&self.mk("bits_shr", vec![lit(64), u.clone(), x[4].clone()]))?;
                        let tr = self.step("shr64_imm", a, insn, &[&g, &x[3], &x[4], &u, &r], self.tail(st, insn, 7, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shl r64, 12 of a word shifted down by 12: the field above
                    // its first byte, times 4096
                    (8, 4) if c == 12 && self.reg(st, gn).is_some_and(|(_, u)| self.app(&self.expand(&u), "bits_shr", 3).is_some()) => {
                        let (_, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                        let shape = (|| {
                            let s = self.expand(&u);
                            let sh = self.app(&s, "bits_shr", 3)?;
                            (nat(&sh[0])? == 64 && nat(&sh[2])? == 12).then_some(())?;
                            let y = self.app(&sh[1], "bits_of_int", 2)?;
                            (nat(&y[0])? == 64).then_some(())?;
                            let ba = self.app(&y[1], "gimple.bytes_at", 3)?;
                            (nat(&ba[2])? == 8).then_some(())?;
                            let ad = self.app(&ba[1], "bits_add", 3)?;
                            (nat(&ad[0])? == 64).then_some(())?;
                            Some((ad[1].clone(), nat(&ad[2])?))
                        })();
                        let (bp, off) = shape.ok_or_else(|| bad("shl 12 of a value not a word's field"))?;
                        let bp = self.canon(&bp);
                        let r = self.parse(&format!(
                            "bits_mul(64, bits_of_int(52, int_mod(int_div(gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 8), int_pow(2, 12)), int_pow(2, 52))), 4096)",
                            self.print(&bp),
                            off
                        ))?;
                        let (r, hr) = self.result(&r)?;
                        let tr = self.step("shl12_field", a, insn, &[&g, &x[3], &bp, &lit(off), &r], self.tail(st, insn, 4, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shr r16, c: the machine's value (a field rule reads it)
                    (2, 5) => {
                        let u = self.need_reg(st, gn, 2)?;
                        let r = self.parse(&format!("bits_set_slice(64, {u}, 15, 0, bits_shr(16, bits_slice({u}, 15, 0), {c}))", u = self.print(&u)))?;
                        let (r, hr) = self.result(&r)?;
                        let tr = self.step("shr16_imm", a, insn, &[&g, &x[3], &x[4], &u, &r], self.tail(st, insn, 7, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shl r32, c: a product by 2^c
                    (4, 4) => {
                        let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                        let mk = 1u128 << c;
                        let (r, hr) = self.result(&self.mk("bits_mul", vec![lit(32), u.clone(), lit(mk)]))?;
                        let tr = self.step("shl32_imm", a, insn, &[&g, &x[3], &x[4], &lit(mk), &lit(n), &u, &r], self.tail(st, insn, 9, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(tr, st2);
                    }
                    _ => return Err(bad("no rule for the shift")),
                }
                let u = self.need_reg(st, gn, 4)?;
                let (r, hr) = self.result(&self.mk("bits_shr", vec![lit(32), u.clone(), x[4].clone()]))?;
                let tr = self.step("shr32", a, insn, &[&g, &x[3], &x[4], &u, &r], self.tail(st, insn, 7, vec![hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // mov r32, r32 (the store form: rm the destination)
            75 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // mov [b + i + d], r16 / r32 / r64 (d not 0): the spec's
                // n-byte store at a computed offset (memset's)
                if let Some(pf) = self.store_bid(st, insn, a, a2, &x[2], &x[0], &[&x[3], &x[4]], g, &x[1])? {
                    return Ok(pf);
                }
                // mov [rsp + d], r32 / r64: the home c := the register's low n bytes
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                    if n != 4 && n != 8 {
                        return Err(bad("a store to a home of other than 4 or 8 bytes"));
                    }
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let cn = self.hkey(dn);
                    let (ng, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                    // (a narrower register's value of an operation of at
                    // most 8n bits: the value itself, x = bits_of_int(8n, x)
                    // by N's width fact)
                    let narrow = if ng < n { self.word_of(&u).filter(|(m, _)| *m <= 8 * n) } else { None };
                    // (the value: the register's; its low bytes, of a 64-bit word bits_of_int(64, y): y's)
                    let xv = if ng == n || narrow.is_some() {
                        u.clone()
                    } else {
                        let y = self.app(&u, "bits_of_int", 2).filter(|y| nat(&y[0]) == Some(64)).map(|y| y[1].clone()).unwrap_or_else(|| u.clone());
                        self.mk("bits_of_int", vec![lit(8 * n), y])
                    };
                    let (_, hs2, hk) = self.hkeep(st, cn, n);
                    // (x = bits_of_int(8n, u): of a call's result, by its
                    // being in bits(64))
                    let hx = match narrow {
                        Some((m, hin)) => {
                            // (the width as the rule states it: 8 * n)
                            let w8 = self.mk("int_mul", vec![lit(8), lit(n)]);
                            let hin = mp(R::Inst("nf.bits_le".into(), vec![("m", lit(m)), ("n", w8.clone()), ("x", u.clone())]), vec![simp0(), simp0(), simp0(), p(hin)]);
                            let e = mp(R::Inst("nf.boi_in".into(), vec![("n", w8.clone()), ("x", u.clone())]), vec![simp0(), p(hin)]);
                            p(mp(R::Inst("eq_sym".into(), vec![("a", self.mk("bits_of_int", vec![w8, u.clone()])), ("b", u.clone())]), vec![p(e)]))
                        }
                        None => simp_lw(self.facts_about(&st.facts, &u)),
                    };
                    let tr = self.step(
                        "store_home_r",
                        a,
                        insn,
                        &[&x[0], &x[1], &d, &lit(cn), &x[3], &x[4], &lit(ng), &u, &xv],
                        self.tail_h(st, insn, &hs2, 6, vec![hx, simp_l(), simp_l(), defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]), simp_l(), simp_l(), simp_l(), p(hk.clone())]),
                    );
                    let st2 = self.set_home(st, a2, cn, n, xv);
                    return self.then(tr, st2);
                }
                // mov [b], r16 (b holding a pointer): the spec's 2-byte store at it,
                // the register's low word
                if let (Some((bn, b, d)), Some(2)) = (self.base_disp(&x[2]).filter(|z| z.0 != 4), nat(&x[0])) {
                    // mov [b + d], r16: the spec's 2-byte field store (a
                    // bitfield's merged word)
                    if nat(&d) != Some(0) {
                        let bv = self.need_reg(st, bn, 8)?;
                        let (n, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                        let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                        let w0 = st.w.clone();
                        let (hc, v, st2, red, sa, so) = self.spec_store_x(st, Some(&ad), Some(2))?;
                        let low = self.mk("bits_slice", vec![u.clone(), lit(15), lit(0)]);
                        let lp = match &so.bf {
                            Some((_, pos, k, fv)) => self.bf_merge(st, &w0, &sa, 2, pos, k, fv, &u, &low)?,
                            None => RA::P(RP::Defs(Box::new(RP::Simp(true, vec![], vec![], false)), vec!["bits_slice".into(), "bits_of_int".into()])),
                        };
                        let tr = self.step("store16_bd", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &lit(n), &u, &v], self.tail_s(st, &st2, insn, 10, vec![lp], &hc, &red));
                        let mut st3 = st2;
                        st3.a = a2;
                        return self.then(tr, st3);
                    }
                    let bv = self.need_reg(st, bn, 8)?;
                    let (n, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                    let (hc, v, st2, red, _) = self.spec_store(st, &bv, 2)?;
                    let lp = RA::P(RP::Defs(Box::new(RP::Simp(true, vec![], vec![], false)), vec!["bits_slice".into(), "bits_of_int".into()]));
                    let tr = self.step("store16_b", a, insn, &[&x[1], &b, &x[3], &x[4], &bv, &lit(n), &u, &v], self.tail_s(st, &st2, insn, 9, vec![lp], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                // mov [b], r32 (b holding a pointer): the spec's 4-byte store at it
                if let (Some((bn, b, d)), Some(4)) = (self.base_disp(&x[2]).filter(|z| z.0 != 4), nat(&x[0])) {
                    let bv = self.need_reg(st, bn, 8)?;
                    // mov [b + d], r32 of a 64-bit word: its low dword, the spec's by N
                    if let (Some((8, u8)), false) = (self.reg(st, g), nat(&d) == Some(0)) {
                        let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                        let (hc, v, st2, red, _) = self.spec_store(st, &ad, 4)?;
                        let low = self.mk("bits_of_int", vec![lit(32), u8.clone()]);
                        let hux = self.eq_nf(&low, &v)?.ok_or_else(|| format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&low), self.print(&self.expand(&low)), self.print(&v), self.print(&self.expand(&v))))?;
                        let tr = self.step("store32_bd_w", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &lit(8), &u8, &v], self.tail_s(st, &st2, insn, 10, vec![hux], &hc, &red));
                        let mut st3 = st2;
                        st3.a = a2;
                        return self.then(tr, st3);
                    }
                    let u = self.need_reg(st, g, 4)?;
                    // mov [b + d], r32: the spec's 4-byte field store
                    if nat(&d) != Some(0) {
                        let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                        let (hc, v, st2, red, _) = self.spec_store(st, &ad, 4)?;
                        // (the spec's value, or the same written otherwise)
                        let tr = if self.canon(&v) == self.canon(&u) {
                            self.step("store32_bd", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u], self.tail_s(st, &st2, insn, 10, vec![], &hc, &red))
                        } else {
                            let hux = self.eq_nf(&u, &v)?.ok_or_else(|| format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&u), self.print(&self.expand(&u)), self.print(&v), self.print(&self.expand(&v))))?;
                            self.step("store32_bd_eq", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u, &v], self.tail_s(st, &st2, insn, 10, vec![hux], &hc, &red))
                        };
                        let mut st3 = st2;
                        st3.a = a2;
                        return self.then(tr, st3);
                    }
                    let (hc, v, st2, red, _) = self.spec_store(st, &bv, 4)?;
                    if self.canon(&v) != self.canon(&u) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&u), self.print(&v)));
                    }
                    let tr = self.step("store32_b", a, insn, &[&x[1], &b, &x[3], &x[4], &bv, &u], self.tail_s(st, &st2, insn, 9, vec![], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                // mov qword [rsp + i*k + d], r64: the spec's 8-byte store
                // into a frame's stack object, an element (the object's
                // address at the offset c, plus i*k: shown the spec's)
                if let (Some(m), Some(8)) = (self.memop(&x[2]), nat(&x[0])) {
                    if let (Some((2, b)), Some(ix), Some(k), Some(dn)) = (self.tag(&m["base"]), self.app(&m["index"], "some", 1).map(|y| y[0].clone()), nat(&m["scale"]), nat(&m["disp"])) {
                        if nat(&b) == Some(4) && self.objs_n.is_some() {
                            let iv = self.need_reg(st, reg(&ix)?, 8)?;
                            if let Some(pf) = self.widen(st, g, 8)? {
                                return Ok(pf);
                            }
                            let u = self.need_reg(st, g, 8)?;
                            let (hc, v, st2, red, _, so) = self.spec_store_x(st, None, Some(8))?;
                            let hux = self.eq_nf(&u, &v)?.ok_or_else(|| format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&u), self.print(&self.expand(&u)), self.print(&v), self.print(&self.expand(&v))))?;
                            let c = self.hkey(dn);
                            let ha = self.mk("tr.ha", vec![self.s.clone(), lit(c)]);
                            let ea = self.mk("bits_add", vec![lit(64), ha, self.mk("bits_mul", vec![lit(64), iv.clone(), lit(k)])]);
                            let ad = self.mk("bits_add", vec![lit(64), so.p.clone(), so.off.clone()]);
                            let q = self.addr_eq(st, &ea, &ad)?;
                            let tr = self.step(
                                "store64_rsib",
                                a,
                                insn,
                                &[&x[1], &ix, &lit(k), &lit(dn), &lit(c), &x[3], &x[4], &iv, &u, &v, &so.p, &so.off],
                                self.tail_s(st, &st2, insn, 9, vec![hux, simp_l(), simp_l(), simp_l(), simp_l(), s(&q)], &hc, &red),
                            );
                            let mut st3 = st2;
                            st3.a = a2;
                            return self.then(tr, st3);
                        }
                    }
                }
                // mov qword [b + i], r64: the spec's 8-byte store, its
                // address computed otherwise (b + i shown the spec's)
                if let (Some(m), Some(8)) = (self.memop(&x[2]), nat(&x[0])) {
                    if let (Some((2, b)), Some(ix)) = (self.tag(&m["base"]), self.app(&m["index"], "some", 1).map(|y| y[0].clone())) {
                        if nat(&m["scale"]) == Some(1) && nat(&m["disp"]) == Some(0) {
                            let (bv, iv) = (self.need_reg(st, reg(&b)?, 8)?, self.need_reg(st, reg(&ix)?, 8)?);
                            // (a 4-byte value zero-extended: the register's 8 bytes)
                            if let Some(pf) = self.widen(st, g, 8)? {
                                return Ok(pf);
                            }
                            let u = self.need_reg(st, g, 8)?;
                            let (hc, v, st2, red, _, so) = self.spec_store_x(st, None, Some(8))?;
                            // (the spec's value: the same normal form)
                            let hux = self.eq_nf(&u, &v)?.ok_or_else(|| format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&u), self.print(&self.expand(&u)), self.print(&v), self.print(&self.expand(&v))))?;
                            let ea = self.mk("bits_add", vec![lit(64), bv.clone(), iv.clone()]);
                            let ad = self.mk("bits_add", vec![lit(64), so.p.clone(), so.off.clone()]);
                            let q = self.addr_eq(st, &ea, &ad)?;
                            let tr = self.step(
                                "store64_bi",
                                a,
                                insn,
                                &[&x[1], &b, &ix, &x[3], &x[4], &bv, &iv, &u, &v, &so.p, &so.off],
                                self.tail_s(st, &st2, insn, 11, vec![hux, simp_l(), simp_l(), s(&q)], &hc, &red),
                            );
                            let mut st3 = st2;
                            st3.a = a2;
                            return self.then(tr, st3);
                        }
                    }
                }
                // mov [b + d], r64 (b holding a pointer): the spec's 8-byte field store
                if let (Some((bn, b, d)), Some(8)) = (self.base_disp(&x[2]).filter(|z| z.0 != 4), nat(&x[0])) {
                    let bv = self.need_reg(st, bn, 8)?;
                    // (a 4-byte value zero-extended: the register's 8 bytes)
                    if let Some(pf) = self.widen(st, g, 8)? {
                        return Ok(pf);
                    }
                    let u = self.need_reg(st, g, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                    let w0 = st.w.clone();
                    let (hc, v, st2, red, sa, so) = self.spec_store_x(st, Some(&ad), Some(8))?;
                    // (a bitfield's merged word: the register's, shown equal)
                    if let Some((_, pos, k, fv)) = &so.bf {
                        let lp = self.bf_merge(st, &w0, &sa, 8, pos, k, fv, &u, &u)?;
                        let tr = self.step("store64_bd_eq", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u, &v], self.tail_s(st, &st2, insn, 10, vec![lp], &hc, &red));
                        let mut st3 = st2;
                        st3.a = a2;
                        return self.then(tr, st3);
                    }
                    // (the spec's value, or the same by its normal form: a
                    // static's word read at its address, the spec at its name)
                    let tr = if self.canon(&v) == self.canon(&u) {
                        self.step("store64_bd", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u], self.tail_s(st, &st2, insn, 10, vec![], &hc, &red))
                    } else {
                        let hux = self.eq_nf(&u, &v)?.ok_or_else(|| format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&u), self.print(&self.expand(&u)), self.print(&v), self.print(&self.expand(&v))))?;
                        self.step("store64_bd_eq", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u, &v], self.tail_s(st, &st2, insn, 10, vec![hux], &hc, &red))
                    };
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                // mov qword [rip + d], r64: the spec's 8-byte store at a
                // static's address
                if let (Some(m), Some(8)) = (self.memop(&x[2]).filter(|m| self.tag(&m["base"]).is_some_and(|b| b.0 == 1)), nat(&x[0])) {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    // (a 4-byte value zero-extended: the register's 8 bytes)
                    if let Some(pf) = self.widen(st, g, 8)? {
                        return Ok(pf);
                    }
                    let u = self.need_reg(st, g, 8)?;
                    let (hc, v, st2, red, _) = self.spec_store(st, &biga, 8)?;
                    if self.canon(&v) != self.canon(&u) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&u), self.print(&v)));
                    }
                    let tr = self.step("store64_rip", a, insn, &[&x[1], &lit(d), &x[3], &x[4], &u, &biga], self.tail_s(st, &st2, insn, 7, vec![], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                // mov dword [rip + d], r32: the spec's 4-byte store at a
                // static's address
                if let (Some(m), Some(4)) = (self.memop(&x[2]).filter(|m| self.tag(&m["base"]).is_some_and(|b| b.0 == 1)), nat(&x[0])) {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    // (a register of 8 bytes: its low dword, tr.store32_rip_w)
                    if let Some((8, u8)) = self.reg(st, g) {
                        let (hc, v, st2, red, _) = self.spec_store(st, &biga, 4)?;
                        let lo = self.mk("bits_of_int", vec![lit(32), u8.clone()]);
                        let hux = if self.canon(&lo) == self.canon(&v) {
                            simp0()
                        } else {
                            self.eq_nf(&lo, &v)?.ok_or_else(|| format!("{:x}: the machine stores {}'s low dword, the spec {}", a, self.print(&u8), self.print(&v)))?
                        };
                        let tr = self.step("store32_rip_w", a, insn, &[&x[1], &lit(d), &x[3], &x[4], &lit(8), &u8, &v, &biga], self.tail_s(st, &st2, insn, 6, vec![hux, simp_l()], &hc, &red));
                        let mut st3 = st2;
                        st3.a = a2;
                        return self.then(tr, st3);
                    }
                    let u = self.need_reg(st, g, 4)?;
                    let (hc, v, st2, red, _) = self.spec_store(st, &biga, 4)?;
                    if self.canon(&v) != self.canon(&u) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&u), self.print(&v)));
                    }
                    let tr = self.step("store32_rip", a, insn, &[&x[1], &lit(d), &x[3], &x[4], &u, &biga], self.tail_s(st, &st2, insn, 7, vec![], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                let Some((0, h)) = self.tag(&x[2]) else { return Err(bad("a store to memory other than a home")) };
                let hn = reg(&h)?;
                // (mov r32, r32 / mov r64, r64)
                let n = if nat(&x[0]) == Some(8) { 8 } else { 4 };
                // (mov r32, r32 of a 64-bit word: its low half)
                if n == 4 {
                    if let Some((8, u)) = self.reg(st, g) {
                        let (r, hr) = self.result(&self.mk("bits_of_int", vec![lit(32), u.clone()]))?;
                        let tr = self.step("mov32_rr8", a, insn, &[&x[1], &h, &x[3], &x[4], &u, &r], self.tail(st, insn, 5, vec![hr]));
                        self.scratch.insert(hn);
                        let st2 = self.set_reg(st, a2, hn, 4, r);
                        return self.then(tr, st2);
                    }
                }
                if let Some(pf) = self.widen(st, g, n)? {
                    return Ok(pf);
                }
                let u = self.need_reg(st, g, n)?;
                let tr = self.step(if n == 8 { "mov64_rr" } else { "mov32_rr" }, a, insn, &[&x[1], &h, &x[3], &x[4], &u], self.tail(st, insn, 5, vec![]));
                self.scratch.insert(hn);
                let st2 = self.set_reg(st, a2, hn, n, u);
                self.then(tr, st2)
            }
            // shr r32 / dword [rsp + d], 1
            73 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                // shr r64, 1
                if let (Some(8), Some(5), Some((0, g))) = (nat(&x[0]), nat(&x[1]), self.tag(&x[2])) {
                    if x[2] == x[3] {
                        let gn = reg(&g)?;
                        let u = self.need_reg(st, gn, 8)?;
                        let (r, hr) = self.result(&self.mk("bits_shr", vec![lit(64), u.clone(), lit(1)]))?;
                        let tr = self.step("shr64_1", a, insn, &[&g, &u, &r], self.tail(st, insn, 4, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                }
                // sar dword [rsp + d], 1: the home's value shifted, signed
                if let (Some(4), Some(7), Some(d)) = (nat(&x[0]), nat(&x[1]), self.rsp_mem(&x[2]).filter(|_| x[2] == x[3])) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let u = home(&st.hsm, &d)?;
                    let cn = self.hkey(dn);
                    let (_, hs2, hk) = self.hkeep(st, cn, 4);
                    let (r, hr) = self.result(&self.mk("bits_sar", vec![lit(32), u.clone(), lit(1)]))?;
                    let tr = self.step("sar32_1_home", a, insn, &[&d, &lit(cn), &u, &r], self.tail_h(st, insn, &hs2, 6, vec![p(hk.clone()), hr]));
                    let st2 = self.set_home(st, a2, cn, 4, r);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(4) || nat(&x[1]) != Some(5) || x[2] != x[3] {
                    return Err(bad("not shr / sar r/m32, 1"));
                }
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let u = home(&st.hsm, &d)?;
                    let cn = self.hkey(dn);
                    let (_, hs2, hk) = self.hkeep(st, cn, 4);
                    let (r, hr) = self.result(&self.mk("bits_shr", vec![lit(32), u.clone(), lit(1)]))?;
                    let tr = self.step("shr32_1_home", a, insn, &[&d, &lit(cn), &u, &r], self.tail_h(st, insn, &hs2, 6, vec![p(hk.clone()), hr]));
                    let st2 = self.set_home(st, a2, cn, 4, r);
                    return self.then(tr, st2);
                }
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not shr r/m32, 1")) };
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, 4)?;
                let (r, hr) = self.result(&self.mk("bits_shr", vec![lit(32), u.clone(), lit(1)]))?;
                let tr = self.step("shr32_1", a, insn, &[&g, &u, &r], self.tail(st, insn, 4, vec![hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // or dword [rsp + d], r32
            38 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                // or r64, r64 (registers of any widths)
                if let (Some(8), Some((0, g))) = (nat(&x[0]), self.tag(&x[2])) {
                    if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                        return Err(bad("not or r64, r64"));
                    }
                    let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                    let (n1, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    let (n2, xv) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    let (r, hr) = self.result(&self.mk("bits_or", vec![lit(64), u.clone(), xv.clone()]))?;
                    let tr = self.step("or64_rr", a, insn, &[&g, &x[1], &lit(n1), &u, &lit(n2), &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, r);
                    return self.then(tr, st2);
                }
                // or r32, r32
                if let (Some(4), Some((0, g))) = (nat(&x[0]), self.tag(&x[2])) {
                    if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                        return Err(bad("not or r32, r32"));
                    }
                    let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                    for r in [gn, hn] {
                        if let Some(pf) = self.widen(st, r, 4)? {
                            return Ok(pf);
                        }
                    }
                    let u = self.need_reg(st, gn, 4)?;
                    let xv = self.need_reg(st, hn, 4)?;
                    let (r, hr) = self.result(&self.mk("bits_or", vec![lit(32), u.clone(), xv.clone()]))?;
                    let tr = self.step("or32_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(tr, st2);
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not or [rsp + d], r32"))?;
                let g = reg(&x[1])?;
                let n = nat(&x[0]).unwrap_or(0);
                if (n != 4 && n != 8) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not or dword / qword [rsp + d], r"));
                }
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let u = home_n(&st.hsm, &d, n)?;
                let v = self.need_reg(st, g, n)?;
                let cn = self.hkey(dn);
                let (_, hs2, hk) = self.hkeep(st, cn, n);
                let rule = if n == 8 { "or64_home" } else { "or32_home" };
                let (r, hr) = self.result(&self.mk("bits_or", vec![lit(8 * n), u.clone(), v.clone()]))?;
                let tr = self.step(rule, a, insn, &[&d, &lit(cn), &x[1], &v, &u, &r], self.tail_h(st, insn, &hs2, 9, vec![p(hk.clone()), hr]));
                let st2 = self.set_home(st, a2, cn, n, r);
                self.then(tr, st2)
            }
            // or r32, [rsp + d]: g := its value | the home's
            39 if self.pairs(&f, 5).is_some_and(|x| self.rsp_mem(&x[2]).is_some() && nat(&x[0]) == Some(4)) => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&st.hsm, &d)?;
                let u = self.need_reg(st, g, 4)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let (r, hr) = self.result(&self.mk("bits_or", vec![lit(32), u.clone(), v.clone()]))?;
                let tr = self.step("or32_r_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
            }
            // cmp r64, r64 / cmp [rsp + d], r32 / r64: the first operand
            // against the second
            56 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                // cmp r64 (u), r64 (xh)
                if let (Some(8), Some((0, g))) = (nat(&x[0]), self.tag(&x[2])) {
                    if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                        return Err(bad("not cmp r64, r64"));
                    }
                    let (n1, u) = self.reg(st, reg(&g)?).ok_or_else(|| bad("an empty register"))?;
                    let (n2, xh) = self.reg(st, reg(&x[1])?).ok_or_else(|| bad("an empty register"))?;
                    return self.compare(st, a, a2, insn, "fs64_rr", &[&g, &x[1], &lit(n1), &lit(n2), &u, &xh], 7, Flags::Sub(64, u.clone(), xh.clone()));
                }
                // cmp r32 (u), r32 (xh): both 32-bit values
                if let (Some(4), Some((0, g))) = (nat(&x[0]), self.tag(&x[2])) {
                    if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                        return Err(bad("not cmp r32, r32"));
                    }
                    let u = self.need_reg(st, reg(&g)?, 4)?;
                    let xh = self.need_reg(st, reg(&x[1])?, 4)?;
                    return self.compare(st, a, a2, insn, "fs32_rr", &[&g, &x[1], &u, &xh], 7, Flags::Sub(32, u.clone(), xh.clone()));
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not cmp [rsp + d], r"))?;
                if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not cmp [rsp + d], r"));
                }
                let cn = self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?);
                let g = reg(&x[1])?;
                // cmp dword [rsp + d] (u), r32 (xr: g's low 32 bits)
                if nat(&x[0]) == Some(4) {
                    let u = home(&st.hsm, &d)?;
                    let (n, x0, xr) = self.low(st, g, 32)?;
                    return self.compare(st, a, a2, insn, "fs32_hr", &[&x[1], &d, &lit(cn), &lit(n), &x0, &xr, &u], 9, Flags::Sub(32, u.clone(), xr.clone()));
                }
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not cmp qword [rsp + d], r64"));
                }
                let Some((8, xv)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                let (n, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                self.compare(st, a, a2, insn, "fs64_hr", &[&x[1], &d, &lit(cn), &lit(n), &u, &xv], 8, Flags::Sub(64, xv.clone(), u.clone()))
            }
            // sub r32, r32 (the source's low 32 bits)
            50 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not sub r32, r32")) };
                // sub r64, r64
                if nat(&x[0]) == Some(8) && x[3] == x[2] && self.tag(&x[4]) == Some((0, x[1].clone())) {
                    let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                    // (a register of 4 bytes zero-extended: its 8)
                    for r in [gn, hn] {
                        if let Some(pf) = self.widen(st, r, 8)? {
                            return Ok(pf);
                        }
                    }
                    let u = self.need_reg(st, gn, 8)?;
                    let xv = self.need_reg(st, hn, 8)?;
                    let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(64), u.clone(), xv.clone()]))?;
                    let tr = self.step("sub64_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, r);
                    return self.then(tr, st2);
                }
                // (x[3], x[4]: the operands' byte readings, unused)
                if nat(&x[0]) != Some(4) {
                    return Err(bad("not sub r32, r32"));
                }
                let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                let u = self.need_reg(st, gn, 4)?;
                let (nh, xv) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                // (h holding 32 bits: its value itself)
                let (tr, r) = if nh == 4 {
                    let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(32), u.clone(), xv.clone()]))?;
                    (self.step("sub32_rr4", a, insn, &[&g, &x[1], &x[3], &x[4], &u, &xv, &r], self.tail(st, insn, 7, vec![hr])), r)
                } else {
                    let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(32), u.clone(), self.mk("bits_of_int", vec![lit(32), xv.clone()])]))?;
                    (self.step("sub32_rr", a, insn, &[&g, &x[1], &x[3], &x[4], &u, &lit(nh), &xv, &r], self.tail(st, insn, 7, vec![hr])), r)
                };
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // and r32, r32 / r64, r64 (the result as the spec orders it)
            47 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not and r32, r32")) };
                if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not and r, r"));
                }
                let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                // and r64, r64
                if nat(&x[0]) == Some(8) {
                    for r in [gn, hn] {
                        if let Some(pf) = self.widen(st, r, 8)? {
                            return Ok(pf);
                        }
                    }
                    let u = self.need_reg(st, gn, 8)?;
                    let xv = self.need_reg(st, hn, 8)?;
                    let op = self.mk("bits_and", vec![lit(64), u.clone(), xv.clone()]);
                    let (r, hr) = self.result(&op)?;
                    let tr = self.step("and64_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, r);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(4) {
                    return Err(bad("not and r32, r32"));
                }
                for r in [gn, hn] {
                    if let Some(pf) = self.widen(st, r, 4)? {
                        return Ok(pf);
                    }
                }
                let u = self.need_reg(st, gn, 4)?;
                let xv = self.need_reg(st, hn, 4)?;
                let op = self.mk("bits_and", vec![lit(32), u.clone(), xv.clone()]);
                let (r, hr) = self.result(&op)?;
                let tr = self.step("and32_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // add r32, r32 / add r64, r64 (the source holding as many bits)
            35 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                // add dword / qword [rsp + d], r: the home := its word + g's (as the spec orders it)
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let n = nat(&x[0]).filter(|n| *n == 4 || *n == 8).ok_or_else(|| bad("not add dword / qword [rsp + d], r"))?;
                    if x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                        return Err(bad("not add [rsp + d], r"));
                    }
                    let g = reg(&x[1])?;
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let u = home_n(&st.hsm, &d, n)?;
                    let v = self.need_reg(st, g, n)?;
                    let cn = self.hkey(dn);
                    let (_, hs2, hk) = self.hkeep(st, cn, n);
                    let op = self.mk("bits_add", vec![lit(8 * n), u.clone(), v.clone()]);
                    let (r, hr) = self.result(&op)?;
                    let rule = if n == 8 { "add64_home_r" } else { "add32_home_r" };
                    let tr = self.step(rule, a, insn, &[&d, &lit(cn), &x[1], &v, &u, &r], self.tail_h(st, insn, &hs2, 9, vec![hr, p(hk.clone())]));
                    let st2 = self.set_home(st, a2, cn, n, r);
                    return self.then(tr, st2);
                }
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not add r, r")) };
                let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                if (n != 4 && n != 8) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not add r32, r32 / r64, r64"));
                }
                let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                for r in [gn, hn] {
                    if let Some(pf) = self.widen(st, r, n)? {
                        return Ok(pf);
                    }
                }
                let u = self.need_reg(st, gn, n)?;
                let (nh, xv) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                if nh != n {
                    return Err(bad("add of a register not holding the operation's width"));
                }
                let (tr, r) = if n == 4 {
                    // (the sum as the spec orders it)
                    let op = self.mk("bits_add", vec![lit(32), u.clone(), xv.clone()]);
                    let (r, hr) = self.result(&op)?;
                    let tr = self.step("add32_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    (tr, r)
                } else {
                    let (r, hr) = self.result(&self.mk("bits_add", vec![lit(64), u.clone(), xv.clone()]))?;
                    let tr = self.step("add64_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    (tr, r)
                };
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, n, r);
                self.then(tr, st2)
            }
            // add rax, imm32: GIMPLE's u + k
            37 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not add rax, imm32"));
                }
                let k = nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k };
                if let Some(pf) = self.widen(st, 0, 8)? {
                    return Ok(pf);
                }
                let u = self.need_reg(st, 0, 8)?;
                let (r, hr) = self.result(&self.mk("bits_add", vec![lit(64), u.clone(), lit(kk)]))?;
                let tr = self.step("add64_rax_imm", a, insn, &[&x[1], &lit(kk), &u, &r], self.tail(st, insn, 5, vec![hr]));
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(tr, st2)
            }
            // sub rax, imm32
            52 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not sub rax, imm32"));
                }
                let k = nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k };
                if let Some(pf) = self.widen(st, 0, 8)? {
                    return Ok(pf);
                }
                let u = self.need_reg(st, 0, 8)?;
                let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(64), u.clone(), lit(kk)]))?;
                let tr = self.step("sub64_rax_imm", a, insn, &[&x[1], &lit(kk), &u, &r], self.tail(st, insn, 5, vec![hr]));
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(tr, st2)
            }
            // mov r64, imm64
            112 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[0])?;
                nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let tr = self.step("mov64_imm", a, insn, &[&x[0], &x[1]], self.tail(st, insn, 3, vec![]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, x[1].clone());
                self.then(tr, st2)
            }
            // xor r32, r32 of one register: g := 0 (the canary cleared)
            53 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let h = reg(&x[1])?;
                // xor r64, r64 (registers of any widths)
                if let (Some(8), Some((0, g))) = (nat(&x[0]), self.tag(&x[2])) {
                    if x[3] == x[2] && self.tag(&x[4]) == Some((0, x[1].clone())) && nat(&g) != Some(h) {
                        let gn = reg(&g)?;
                        let (n1, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                        let (n2, xv) = self.reg(st, h).ok_or_else(|| bad("an empty register"))?;
                        let (r, hr) = self.result(&self.mk("bits_xor", vec![lit(64), u.clone(), xv.clone()]))?;
                        let tr = self.step("xor64_rr", a, insn, &[&g, &x[1], &lit(n1), &u, &lit(n2), &xv, &r], self.tail(st, insn, 7, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                }
                let same = |t: &Term| self.tag(t).is_some_and(|(k, r)| k == 0 && nat(&r) == Some(h));
                if nat(&x[0]) != Some(4) || !same(&x[2]) || !same(&x[3]) || !same(&x[4]) {
                    return Err(bad("xor of two registers"));
                }
                let tr = self.step("xor32_self", a, insn, &[&x[1]], self.tail(st, insn, 2, vec![]));
                self.scratch.insert(h);
                let st2 = self.set_reg(st, a2, h, 4, lit(0));
                return self.then(tr, st2);
            }
            // mov r32, imm32
            111 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[0])?;
                nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let tr = self.step("mov32_imm", a, insn, &[&x[0], &x[1]], self.tail(st, insn, 3, vec![]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, x[1].clone());
                self.then(tr, st2)
            }
            // cmp dword [rsp + d], imm32: the home (u) against k
            59 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                // or r16, imm16 (a register holding a 16-bit value): u | k
                if let (Some((0, g)), Some(2), Some(1)) = (self.tag(&x[2]), nat(&x[0]), nat(&x[1])) {
                    let gn = reg(&g)?;
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    let (r, hr) = self.result(&self.mk("bits_or", vec![lit(16), u.clone(), x[4].clone()]))?;
                    let tr = self.step("or16_imm", a, insn, &[&g, &x[3], &x[4], &lit(n), &u, &r], self.tail(st, insn, 6, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 2, r);
                    return self.then(tr, st2);
                }
                // and r32, imm32 (a register of 4 or 8 bytes): its low 32
                // bits & k, zero-extended
                if let (Some((0, g)), Some(4), Some(4)) = (self.tag(&x[2]), nat(&x[0]), nat(&x[1])) {
                    let gn = reg(&g)?;
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    let k = x[4].clone();
                    let (r, hr) = self.result(&self.mk("bits_and", vec![lit(32), self.mk("bits_slice", vec![u.clone(), lit(31), lit(0)]), k.clone()]))?;
                    let tr = self.step("and32_imm32", a, insn, &[&g, &x[3], &k, &lit(n), &u, &r], self.tail(st, insn, 5, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(tr, st2);
                }
                // sub / add rsp, imm32: the frame grows / ends (row 60's)
                if let (Some((0, g)), Some(8), Some(op @ (0 | 5))) = (self.tag(&x[2]), nat(&x[0]), nat(&x[1])) {
                    if reg(&g)? == 4 {
                        let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                        let fr2 = if op == 5 {
                            if imm >= 1 << 31 || self.fr + imm > 65536 {
                                return Err(bad("sub rsp beyond the frame's bound"));
                            }
                            self.fr + imm
                        } else {
                            if imm >= 1 << 31 || imm > self.fr {
                                return Err(bad("add rsp beyond the frame"));
                            }
                            self.fr - imm
                        };
                        let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                        let rule = if op == 5 { "sub_rsp32" } else { "add_rsp32" };
                        let tr = self.step(rule, a, insn, &[&x[3], &x[4], &lit(fr2)], self.tail(st, insn, 6, vec![p(n4)]));
                        let mut st2 = st.clone();
                        st2.a = a2;
                        st2.fr = fr2;
                        return self.then(tr, st2);
                    }
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("an imm32 operation not on a home"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                // cmp qword [rsp + d], imm32: the home's word against the
                // immediate sign-extended
                if nat(&x[0]) == Some(8) && x[3] == x[2] && nat(&x[1]) == Some(7) {
                    let u = home_n(&st.hsm, &d, 8)?;
                    let cn = self.hkey(dn);
                    let kk = lit(if imm >= 1 << 31 { imm + (P64 - (1 << 32)) } else { imm });
                    return self.compare(st, a, a2, insn, "fs64_hi32", &[&d, &lit(cn), &x[4], &kk, &u], 7, Flags::Sub(64, u.clone(), kk.clone()));
                }
                if nat(&x[0]) != Some(4) || x[3] != x[2] || nat(&x[1]) != Some(7) {
                    return Err(bad("not cmp dword [rsp + d], imm32"));
                }
                let u = home(&st.hsm, &d)?;
                let cn = self.hkey(dn);
                self.compare(st, a, a2, insn, "fs32_hi32", &[&d, &lit(cn), &x[4], &lit(imm), &u], 7, Flags::Sub(32, u.clone(), lit(imm)))
            }
            // sub r32, imm8: GIMPLE's x + -k
            60 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                // add / cmp dword [rsp + d], imm8: the home d (u)
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    // cmp qword [rsp + d], imm8: the home's word against the immediate
                    if nat(&x[0]) == Some(8) && x[3] == x[2] && nat(&x[1]) == Some(7) {
                        let kk = lit(if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm });
                        let cn = self.hkey(dn);
                        let Some((8, xv)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                        return self.compare(st, a, a2, insn, "fs64_hi8", &[&d, &lit(cn), &x[4], &kk, &xv], 7, Flags::Sub(64, xv.clone(), kk.clone()));
                    }
                    // add / sub qword [rsp + d], imm8: the 8-byte home's u + kk / u - kk
                    if nat(&x[0]) == Some(8) && x[3] == x[2] && matches!(nat(&x[1]), Some(0 | 5)) {
                        let sub = nat(&x[1]) == Some(5);
                        let kk = lit(if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm });
                        let cn = self.hkey(dn);
                        let Some((8, u)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                        let (_, hs2, hk) = self.hkeep(st, cn, 8);
                        let (r, hr) = self.result(&self.mk(if sub { "bits_sub" } else { "bits_add" }, vec![lit(64), u.clone(), kk.clone()]))?;
                        let tr = self.step(if sub { "sub64_home_imm" } else { "add64_home" }, a, insn, &[&d, &lit(cn), &x[4], &kk, &u, &r], self.tail_h(st, insn, &hs2, 8, vec![p(hk.clone()), hr]));
                        let st2 = self.set_home(st, a2, cn, 8, r);
                        return self.then(tr, st2);
                    }
                    let kk = lit(if imm >= 128 { imm + 0xffff_ff00 } else { imm });
                    if nat(&x[0]) != Some(4) || x[3] != x[2] {
                        return Err(bad("not dword [rsp + d], imm8"));
                    }
                    let u = home(&st.hsm, &d)?;
                    let cn = self.hkey(dn);
                    let ck = lit(cn);
                    return match nat(&x[1]) {
                        Some(0) => {
                            let (_, hs2, hk) = self.hkeep(st, cn, 4);
                            let (r, hr) = self.result(&self.mk("bits_add", vec![lit(32), u.clone(), kk.clone()]))?;
                            let tr = self.step("add32_home", a, insn, &[&d, &ck, &x[4], &kk, &u, &r], self.tail_h(st, insn, &hs2, 8, vec![p(hk.clone()), hr]));
                            let st2 = self.set_home(st, a2, cn, 4, r);
                            self.then(tr, st2)
                        }
                        // or: the home u | kk
                        Some(1) => {
                            let (_, hs2, hk) = self.hkeep(st, cn, 4);
                            let (r, hr) = self.result(&self.mk("bits_or", vec![lit(32), u.clone(), kk.clone()]))?;
                            let tr = self.step("or32_home_i", a, insn, &[&d, &ck, &x[4], &kk, &u, &r], self.tail_h(st, insn, &hs2, 8, vec![p(hk.clone()), hr]));
                            let st2 = self.set_home(st, a2, cn, 4, r);
                            self.then(tr, st2)
                        }
                        // cmp: the home (u) against kk
                        Some(7) => self.compare(st, a, a2, insn, "fs32_hi8", &[&d, &ck, &x[4], &kk, &u], 7, Flags::Sub(32, u.clone(), kk.clone())),
                        _ => Err(bad("an operation on a home other than add, or, cmp")),
                    };
                }
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if imm >= 128 { imm + 0xffff_ff00 } else { imm };
                let size = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                if k != 0 || (size != 4 && size != 8) {
                    return Err(bad("not r32/r64, imm8"));
                }
                let gn = reg(&g)?;
                // sub rsp, k: the frame grows (the prologue)
                if (size, nat(&x[1]), gn) == (8, Some(5), 4) {
                    if imm >= 128 || self.fr + imm > 65536 {
                        return Err(bad("sub rsp beyond the frame's bound"));
                    }
                    let fr2 = self.fr + imm;
                    let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                    let tr = self.step("sub_rsp", a, insn, &[&x[3], &x[4], &lit(fr2)], self.tail(st, insn, 6, vec![p(n4)]));
                    let mut st2 = st.clone();
                    st2.a = a2;
                    st2.fr = fr2;
                    return self.then(tr, st2);
                }
                // add rsp, k: the frame's end (k at most the frame)
                if (size, nat(&x[1]), gn) == (8, Some(0), 4) {
                    if imm >= 128 || imm > self.fr {
                        return Err(bad("add rsp beyond the frame"));
                    }
                    let fr2 = self.fr - imm;
                    let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                    let tr = self.step("add_rsp", a, insn, &[&x[3], &x[4], &lit(fr2)], self.tail(st, insn, 6, vec![p(n4)]));
                    let mut st2 = st.clone();
                    st2.a = a2;
                    st2.fr = fr2;
                    return self.then(tr, st2);
                }
                // and r32, imm8, a jump on its flags after it: g := g's low 32
                // bits and k (4 bytes)
                if (size, nat(&x[1])) == (4, Some(4)) && self.insns.get(&a2).is_some_and(|j| matches!(j.row, 127 | 128)) {
                    let (n, x0, u) = self.low(st, gn, 32)?;
                    let kl = lit(kk);
                    let (r, hr) = self.result(&self.mk("bits_and", vec![lit(32), u.clone(), kl.clone()]))?;
                    let mut v = self.head(a, insn);
                    v.extend([&g, &x[3], &x[4], &kl, &lit(n), &x0, &u, &r, &st.hst, &st.rs, &st.w].into_iter().map(t));
                    v.push(p(R::F(insn.name.clone())));
                    v.extend((0..7).map(|_| simp_l()));
                    v.push(hr);
                    let step = mpf("tr.fs_and32_imm", v);
                    return self.compare_x(st, a, a2, step, Flags::Log(32, r.clone()), Some((gn, r, 4)));
                }
                // and r32, imm8 of a byte: in 8 bits; of a shifted word: the field
                if (size, nat(&x[1])) == (4, Some(4)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n == 1 {
                        // (a low mask 2^kb - 1 of a byte read: the bitfield's
                        // form, when the spec has read it so)
                        let mut r = self.mk("bits_and", vec![lit(8), u.clone(), lit(kk)]);
                        if let (Some(kb), Some(b)) = ((1..8).find(|kb| (1u128 << kb) - 1 == kk), self.app(&self.expand(&u), "bits_of_int", 2).filter(|b| nat(&b[0]) == Some(8)).map(|b| b[1].clone())) {
                            let fd = self.parse(&format!("bits_of_int({kb}, int_mod(int_div({}, int_pow(2, 0)), int_pow(2, {kb})))", self.print(&b)))?;
                            let fd = self.norm(&fd)?.0;
                            if self.val_of.contains_key(&self.expand(&fd)) {
                                r = fd;
                            }
                        }
                        let tr = self.step("and8_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u, &r], self.tail(st, insn, 7, vec![]));
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 1, r);
                        return self.then(tr, st2);
                    }
                    if n == 8 {
                        // bits_set_slice(64, W, 15, 0, bits_shr(16, bits_slice(W, 15, 0), pos)), W the word at q
                        let shape = (|| {
                            let s = self.expand(&u);
                            let ss = self.app(&s, "bits_set_slice", 5)?;
                            let sh = self.app(&ss[4], "bits_shr", 3)?;
                            let w16 = self.app(&ss[1], "bits_of_int", 2)?;
                            (nat(&w16[0])? == 16).then_some(())?;
                            let ba = self.app(&w16[1], "gimple.bytes_at", 3)?;
                            (nat(&ba[2])? == 2).then_some(())?;
                            Some((ba[1].clone(), nat(&sh[2])?))
                        })();
                        // (a plain mask below 128: the 64-bit and, the upper half cleared)
                        if shape.is_none() && nat(&x[4]).is_some_and(|k| k < 128) {
                            let (r, hr) = self.result(&self.mk("bits_and", vec![lit(64), u.clone(), x[4].clone()]))?;
                            let tr = self.step("and32_imm_w", a, insn, &[&g, &x[3], &x[4], &u, &r], self.tail(st, insn, 6, vec![hr]));
                            self.scratch.insert(gn);
                            let st2 = self.set_reg(st, a2, gn, 8, r);
                            return self.then(tr, st2);
                        }
                        let (q, pos) = shape.ok_or_else(|| bad("and of a 64-bit value not a shifted word"))?;
                        let kb = (0..16).find(|kb| (1u128 << kb) - 1 == kk).ok_or_else(|| bad("a field mask not 2^k - 1"))?;
                        self.fields.insert((pos, kb, kk));
                        let q = self.canon(&q);
                        let ff = self.field_fact(pos, kb, kk)?;
                        let r = self.parse(&format!(
                            "bits_of_int({kb}, int_mod(int_div(gimple.bytes_at(app({wn}, \"vm\"), {}, 2), int_pow(2, {pos})), int_pow(2, {kb})))",
                            self.print(&q)
                        ))?;
                        let (r, hr) = self.result(&r)?;
                        let tr = self.step("and_field16", a, insn, &[&g, &x[3], &x[4], &lit(kk), &q, &lit(pos), &lit(kb), &r], self.tail(st, insn, 4, vec![s(&ff), simp_l(), simp_l(), simp_l(), hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(tr, st2);
                    }
                }
                // or r32, imm8 (g holding a value of at most 4 bytes): g := u | kk
                if (size, nat(&x[1])) == (4, Some(1)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n > 4 {
                        return Err(bad("or r32 of a wider value"));
                    }
                    let (r, hr) = self.result(&self.mk("bits_or", vec![lit(32), u.clone(), lit(kk)]))?;
                    let tr = self.step("or32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &lit(n), &u, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(tr, st2);
                }
                // add r32, imm8 (g holding a value of at most 4 bytes): g := u + kk
                if (size, nat(&x[1])) == (4, Some(0)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n > 4 {
                        return Err(bad("add r32 of a wider value"));
                    }
                    let (r, hr) = self.result(&self.mk("bits_add", vec![lit(32), u.clone(), lit(kk)]))?;
                    let tr = self.step("add32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &lit(n), &u, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(tr, st2);
                }
                // (sub r32 of a 64-bit word: its own arm, on the low half)
                let low_sub = size == 4 && nat(&x[1]) == Some(5) && matches!(self.reg(st, gn), Some((8, _)));
                // (cmp r32: its arm reads the low half itself, of any width)
                let low_cmp = size == 4 && nat(&x[1]) == Some(7);
                let u = if low_sub || low_cmp { lit(0) } else { self.need_reg(st, gn, size)? };
                match (size, nat(&x[1])) {
                    // add r64, imm8: GIMPLE's u + k
                    (8, Some(0)) => {
                        let kk = if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm };
                        let (r, hr) = self.result(&self.mk("bits_add", vec![lit(64), u.clone(), lit(kk)]))?;
                        let tr = self.step("add64_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(tr, st2)
                    }
                    // sub r64, imm8: GIMPLE's p + -k
                    (8, Some(5)) => {
                        let kk = if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm };
                        let neg = self.mk("bits_neg", vec![lit(64), lit(kk)]);
                        let (r, hr) = self.result(&self.mk("bits_add", vec![lit(64), u.clone(), neg]))?;
                        let tr = self.step("sub64_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(tr, st2)
                    }
                    // and r64, imm8: g := u & kk
                    (8, Some(4)) => {
                        let kk = if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm };
                        let (r, hr) = self.result(&self.mk("bits_and", vec![lit(64), u.clone(), lit(kk)]))?;
                        let tr = self.step("and64_imm8", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(tr, st2)
                    }
                    // and r32, imm8
                    (4, Some(4)) => {
                        let (r, hr) = self.result(&self.mk("bits_and", vec![lit(32), u.clone(), lit(kk)]))?;
                        let tr = self.step("and32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(tr, st2)
                    }
                    // sub r32, imm8 of a 64-bit word: its low half
                    (4, Some(5)) if low_sub => {
                        let (_, w8) = self.reg(st, gn).unwrap();
                        let lo = self.mk("bits_of_int", vec![lit(32), w8.clone()]);
                        let (r, hr) = self.result(&self.mk("bits_add", vec![lit(32), lo, self.mk("bits_neg", vec![lit(32), lit(kk)])]))?;
                        let tr = self.step("sub32_imm_w", a, insn, &[&g, &x[3], &x[4], &lit(kk), &w8, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(tr, st2)
                    }
                    (4, Some(5)) => {
                        let neg = self.mk("bits_neg", vec![lit(32), lit(kk)]);
                        let (r, hr) = self.result(&self.mk("bits_add", vec![lit(32), u.clone(), neg]))?;
                        let tr = self.step("sub32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(tr, st2)
                    }
                    // cmp r64, imm8: g (u) against kk (for je / jne as GIMPLE
                    // writes it: a negative one bits_neg(64, -k))
                    (8, Some(7)) => {
                        let kk = lit(if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm });
                        self.compare(st, a, a2, insn, "fs64_ri8", &[&g, &x[3], &x[4], &kk, &u], 6, Flags::Sub(64, u.clone(), kk.clone()))
                    }
                    // cmp r32, imm8: g's low 32 bits (u) against kk
                    (4, Some(7)) => {
                        let (n, x0, u) = self.low(st, gn, 32)?;
                        self.compare(st, a, a2, insn, "fs32_ri8", &[&g, &x[3], &x[4], &lit(kk), &lit(n), &x0, &u], 7, Flags::Sub(32, u.clone(), lit(kk)))
                    }
                    _ => Err(bad("unknown operation")),
                }
            }
            // cmp al, imm8: al (b, rax's low byte) against k
            23 => {
                let k = nat(&f).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = lit(k);
                let (n, x0, b) = self.low(st, 0, 8)?;
                self.compare(st, a, a2, insn, "fs8_al", &[&f, &kk, &lit(n), &x0, &b], 6, Flags::Sub(8, b.clone(), kk.clone()))
            }
            // movsxd r64, r32: g := h's 32 bits sign-extended
            113 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (k, h) = self.tag(&x[1]).ok_or_else(|| bad("fields"))?;
                if k != 0 {
                    return Err(bad("not movsxd r64, r32"));
                }
                let (g, hn) = (reg(&x[0])?, reg(&h)?);
                let u = self.need_reg(st, hn, 4)?;
                let (r, hr) = self.result(&self.mk("bits_sext", vec![lit(32), lit(64), u.clone()]))?;
                let tr = self.step("movsxd", a, insn, &[&x[0], &h, &x[2], &x[3], &u, &r], self.tail(st, insn, 5, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, r);
                self.then(tr, st2)
            }
            // cwde: eax := ax sign-extended (a 2-byte value's: tr.cwde)
            91 if nat(&f) == Some(4) => {
                let u = self.need_reg(st, 0, 2)?;
                let (r, hr) = self.result(&self.mk("bits_sext", vec![lit(16), lit(32), u.clone()]))?;
                let tr = self.step("cwde", a, insn, &[&u, &r], self.tail(st, insn, 3, vec![hr]));
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 4, r);
                self.then(tr, st2)
            }
            // cdqe
            91 => {
                if nat(&f) != Some(8) {
                    return Err(bad("cbw (not cwde, cdqe)"));
                }
                let u = self.need_reg(st, 0, 4)?;
                let (r, hr) = self.result(&self.mk("bits_sext", vec![lit(32), lit(64), u.clone()]))?;
                let tr = self.step("cdqe", a, insn, &[&u, &r], self.tail(st, insn, 3, vec![hr]));
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(tr, st2)
            }
            // lea r64, [rip + d]: a static's address (the spec's name for it)
            78 => {
                let x = self.pairs(&f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let m = self.record(&x[5]).ok_or_else(|| bad("fields"))?;
                // lea r64, [rsp + d]: the frame's bytes at c (a stack object's address)
                let rsp_base = m.get("base").and_then(|b| self.tag(b)).is_some_and(|(k, r)| k == 2 && nat(&r) == Some(4));
                if nat(&x[0]) == Some(8) && rsp_base && m.get("index").is_some_and(|i| self.app(i, "none", 0).is_some()) && m.get("scale").and_then(nat) == Some(1) {
                    let d = m.get("disp").cloned().ok_or_else(|| bad("fields"))?;
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let c = self.hkey(dn);
                    let tr = self.step("lea_rsp", a, insn, &[&x[1], &d, &lit(c), &x[2], &x[3], &x[4]], self.tail(st, insn, 4, vec![]));
                    self.scratch.insert(g);
                    let ha = self.mk("tr.ha", vec![self.s.clone(), lit(c)]);
                    let st2 = self.set_reg(st, a2, g, 8, ha);
                    return self.then(tr, st2);
                }
                // lea r32, [b + d]: u + d, 32 bits
                if nat(&x[0]) == Some(4) {
                    let (bk, b) = m.get("base").and_then(|b| self.tag(b)).ok_or_else(|| bad("fields"))?;
                    let d = m.get("disp").and_then(nat).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    // lea r32, [i * k]: u * k, 32 bits (GIMPLE's product)
                    if let (0, Some(idx), Some(k), 0) = (bk, m.get("index").and_then(|i| self.app(i, "some", 1)).map(|i| i[0].clone()), m.get("scale").and_then(nat), d) {
                        let i = reg(&idx)?;
                        let u = self.need_reg(st, i, 4)?;
                        let (r, hr) = self.result(&self.mk("bits_mul", vec![lit(32), u.clone(), lit(k)]))?;
                        let tr = self.step("lea32_is", a, insn, &[&x[1], &idx, &lit(k), &x[2], &x[3], &x[4], &u, &r], self.tail(st, insn, 6, vec![hr]));
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 4, r);
                        return self.then(tr, st2);
                    }
                    if bk != 2 || m.get("index").map_or(true, |i| self.app(i, "none", 0).is_none()) || m.get("scale").and_then(nat) != Some(1) {
                        return Err(bad("not lea r32, [b + d]"));
                    }
                    let bn = reg(&b)?;
                    let (nb, u) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let (kk, hk) = (lit(d % (1 << 32)), simp_l());
                    let (r, hr) = self.result(&self.mk("bits_add", vec![lit(32), u.clone(), kk.clone()]))?;
                    let tr = self.step("lea32_bd", a, insn, &[&x[1], &b, &lit(d), &x[2], &x[3], &x[4], &lit(nb), &u, &kk, &r], self.tail(st, insn, 6, vec![hk, hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, r);
                    return self.then(tr, st2);
                }
                // lea r64, [i * k]: u * k
                if let (Some((0, _)), Some(idx), Some(k), Some(0)) = (m.get("base").and_then(|b| self.tag(b)), m.get("index").and_then(|i| self.app(i, "some", 1)).map(|i| i[0].clone()), m.get("scale").and_then(nat), m.get("disp").and_then(nat)) {
                    let i = reg(&idx)?;
                    let (n, u) = self.reg(st, i).ok_or_else(|| bad("an empty index register"))?;
                    let (r, hr) = self.result(&self.mk("bits_mul", vec![lit(64), u.clone(), lit(k)]))?;
                    let tr = self.step("lea64_is", a, insn, &[&x[1], &idx, &lit(k), &x[2], &x[3], &x[4], &lit(n), &u, &r], self.tail(st, insn, 6, vec![hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(tr, st2);
                }
                // lea r64, [b + i]: iv + bv
                if let Some(idx) = m.get("index").and_then(|i| self.app(i, "some", 1)).map(|i| i[0].clone()) {
                    let (bk, b) = m.get("base").and_then(|b| self.tag(b)).ok_or_else(|| bad("fields"))?;
                    if bk != 2 || m.get("disp").and_then(nat) != Some(0) || m.get("scale").and_then(nat) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&idx)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let (r, hr) = self.result(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]))?;
                    let tr = self.step("lea_bi", a, insn, &[&x[1], &b, &idx, &x[2], &x[3], &x[4], &lit(nb), &bv, &iv, &r], self.tail(st, insn, 8, vec![hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(tr, st2);
                }
                // lea r64, [b + d]: u + d
                if let (Some((2, b)), Some(d), Some(1)) = (m.get("base").and_then(|b| self.tag(b)), m.get("disp").and_then(nat), m.get("scale").and_then(nat)) {
                    let (nb, u) = self.reg(st, reg(&b)?).ok_or_else(|| bad("an empty base register"))?;
                    if nb != 8 {
                        return Err(bad("a base register not holding 64 bits"));
                    }
                    let dd = lit(d);
                    let (r, hr) = self.result(&self.mk("bits_add", vec![lit(64), u.clone(), dd.clone()]))?;
                    let tr = self.step("lea64_bd", a, insn, &[&x[1], &b, &lit(d), &dd, &x[2], &x[3], &x[4], &u, &r], self.tail(st, insn, 7, vec![hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(tr, st2);
                }
                let d = m.get("disp").and_then(nat).ok_or_else(|| bad("not rip-relative"))?;
                if !m.get("base").map_or(false, |b| self.tag(b).map_or(false, |(k, _)| k == 1)) {
                    return Err(bad("not rip-relative"));
                }
                let addr = (a2 + d) % P64;
                let named = self.vals.iter().find(|(_, tr)| self.eval_lit(tr) == Some(addr)).map(|(v, _)| Term::var(*v, vec![]));
                let biga = match named {
                    Some(tr) => tr,
                    None => {
                        let q = match &st.spec {
                            Spec::Proc(i) | Spec::Plain(i) => self.qs[*i].clone(),
                            Spec::Ret(v, _) => v.clone(),
                        };
                        let mut found = None;
                        self.statics(&q, addr, &mut found);
                        for (_, tr) in &self.vals {
                            self.statics(tr, addr, &mut found);
                        }
                        found.unwrap_or_else(|| lit(addr))
                    }
                };
                let tr = self.step("lea_rip", a, insn, &[&x[1], &lit(d), &x[2], &x[3], &x[4], &biga], self.tail(st, insn, 4, vec![]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, biga);
                self.then(tr, st2)
            }
            // movzx r32, word [rsp + i*k + d]: the spec's 2-byte load at an
            // element of a frame's stack object (its address the frame's at
            // the offset c, plus i*k; the other forms below)
            80 if self.objs_n.is_some()
                && self
                    .pairs(&f, 5)
                    .and_then(|x| self.memop(&x[2]))
                    .is_some_and(|m| self.tag(&m["base"]).is_some_and(|b| b.0 == 2 && nat(&b.1) == Some(4)) && self.app(&m["index"], "some", 1).is_some()) =>
            {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let m = self.memop(&x[2]).filter(|_| x[3] == x[2] && nat(&x[0]) == Some(4)).ok_or_else(|| bad("not movzx r32, word [m]"))?;
                let (Some((2, b)), Some(ix), Some(k), Some(dn)) = (self.tag(&m["base"]), self.app(&m["index"], "some", 1).map(|y| y[0].clone()), nat(&m["scale"]), nat(&m["disp"])) else {
                    return Err(bad("movzx r32, word [m] other than [rsp + i*k + d]"));
                };
                if nat(&b) != Some(4) || self.objs_n.is_none() {
                    return Err(bad("movzx r32, word [b + i*k + d] other than a frame object's"));
                }
                if let Some(pf) = self.widen(st, reg(&ix)?, 8)? {
                    return Ok(pf);
                }
                let iv = self.need_reg(st, reg(&ix)?, 8)?;
                let c = self.hkey(dn);
                let ha = self.mk("tr.ha", vec![self.s.clone(), lit(c)]);
                let ea = self.mk("bits_add", vec![lit(64), ha, self.mk("bits_mul", vec![lit(64), iv.clone(), lit(k)])]);
                let (pp, off, hc, heq) = self.mem_hyp_eq(st, &ea, 2)?;
                let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 2))", self.print(&pp), self.print(&off)))?;
                let (v, hr) = self.result(&v)?;
                let tr = self.step("movzx16_rsib", a, insn, &[&x[1], &ix, &lit(k), &lit(dn), &lit(c), &x[4], &iv, &pp, &off, &v], self.tail(st, insn, 10, vec![s(&heq), s(&hc), hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 2, v);
                self.then(tr, st2)
            }
            // movzx r32, byte [b + i]: the spec's byte load at i + b
            79 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // movzx r64, r8 (memset's: REX.W, the byte register as the
                // decoder has it -- h holding x of k bytes): its low byte
                if let (Some((0, h)), Some(8)) = (self.tag(&x[2]), nat(&x[0])) {
                    let hn = reg(&h)?;
                    if x[3] != x[2] {
                        return Err(bad("not movzx r64, r8"));
                    }
                    let (k, xv) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    let tr = self.step("movzx8_rq", a, insn, &[&x[1], &h, &x[4], &lit(k), &xv], self.tail(st, insn, 5, vec![]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, self.mk("bits_of_int", vec![lit(8), xv.clone()]));
                    return self.then(tr, st2);
                }
                // movzx r32, r8 (h holding the byte b)
                if let Some((0, h)) = self.tag(&x[2]) {
                    let hn = reg(&h)?;
                    if x[3] != x[2] || hn >= 4 {
                        return Err(bad("not movzx r32, r8"));
                    }
                    let (n, b) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    // (its low byte set, setcc's: that byte)
                    if let Some(y) = self.app(&b, "bits_set_slice", 5).map(|y| y.to_vec()).filter(|y| nat(&y[0]) == Some(64) && nat(&y[2]) == Some(7) && nat(&y[3]) == Some(0)) {
                        let tr = self.step("movzx8_set", a, insn, &[&x[1], &h, &x[4], &lit(n), &y[1], &y[4]], self.tail(st, insn, 7, vec![]));
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 4, y[4].clone());
                        return self.then(tr, st2);
                    }
                    // (a word, the spec masking it: u & 255)
                    let masked = self.mk("bits_and", vec![lit(32), b.clone(), lit(255)]);
                    let nm = self.norm(&masked)?.0;
                    if n > 1 && n <= 4 && matches!(nm.node(), Node::Var(..)) {
                        let (r, hr) = self.result(&masked)?;
                        let tr = self.step("movzx8_rrm", a, insn, &[&x[1], &h, &x[4], &lit(n), &b, &r], self.tail(st, insn, 7, vec![hr]));
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 4, r);
                        return self.then(tr, st2);
                    }
                    // (a value of more bytes, of 8 bits)
                    let tr = if n == 1 {
                        self.step("movzx8_rr", a, insn, &[&x[1], &h, &x[4], &b], self.tail(st, insn, 6, vec![]))
                    } else {
                        self.step("movzx8_rrw", a, insn, &[&x[1], &h, &x[4], &lit(n), &b], self.tail(st, insn, 7, vec![]))
                    };
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, b);
                    return self.then(tr, st2);
                }
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                // movzx r32, byte [rip + d]: the spec's load of a static's byte
                if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = (a2 + d) % P64;
                    let hc = self.static_hyp(st, biga, false)?;
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({wn}, \"vm\"), {biga}, 1))"))?;
                    let (v, hr) = self.result(&v)?;
                    let tr = self.step("movzx8_rip", a, insn, &[&x[1], &lit(d), &x[4], &lit(biga), &v], self.tail(st, insn, 4, vec![simp_lw(vec![R::S(hc.clone())]), hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, v);
                    return self.then(tr, st2);
                }
                // movzx r32, byte [b + d] (b holding a pointer): the spec's field load
                if self.app(&m["index"], "none", 0).is_some() && nat(&m["disp"]) != Some(0) {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    // (defined for reading, or for the spec's store there)
                    let (hc, wt) = self.mem_hyp_rw(st, &bp, &d, 1)?;
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 1))", self.print(&bp), self.print(&d)))?;
                    let (v, hr) = self.result(&v)?;
                    let tr = self.step("movzx8_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &wt, &v], self.tail(st, insn, 6, vec![s(&hc), hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, v);
                    return self.then(tr, st2);
                }
                // movzx r32, byte [b] (b holding the pointer)
                if self.app(&m["index"], "none", 0).is_some() {
                    if bk != 2 || nat(&m["disp"]) != Some(0) || x[3] != x[2] {
                        return Err(bad("not [b]"));
                    }
                    let bn = reg(&b)?;
                    let bv = self.need_reg(st, bn, 8)?;
                    let cond = self.ld8_cond(&bv);
                    let Some(hc) = self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()) else {
                        // (the spec's byte at the address computed otherwise)
                        let (ad, hc, heq) = self.byte_hyp_eq(st, &bv)?;
                        let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                        let (by, hr) = self.result(&self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, ad.clone(), lit(1)])]))?;
                        let tr = self.step("movzx8_beq", a, insn, &[&x[1], &b, &x[4], &bv, &ad, &by], self.tail(st, insn, 5, vec![s(&heq), taut(vec![R::S(hc)]), hr]));
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 1, by);
                        return self.then(tr, st2);
                    };
                    let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                    let (by, hr) = self.result(&self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, bv.clone(), lit(1)])]))?;
                    let tr = self.step("movzx8_b", a, insn, &[&x[1], &b, &x[4], &bv, &by], self.tail(st, insn, 5, vec![taut(vec![R::S(hc.clone())]), hr]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, by);
                    return self.then(tr, st2);
                }
                let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) || x[3] != x[2] {
                    return Err(bad("not [b + i]"));
                }
                let (bn, inn) = (reg(&b)?, reg(&i)?);
                let (nb, bv) = self.reg(st, bn).ok_or_else(|| format!("{:x}: register {} holds no value of the procedure", a, bn))?;
                let iv = self.need_reg(st, inn, 8)?;
                let (ad, had) = self.result(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]))?;
                let cond = self.ld8_cond(&ad);
                let hc = self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()).ok_or_else(|| {
                    let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
                    let vals: Vec<String> = self.vals.iter().map(|(v, tr)| format!("{} = {}", self.env.var(*v).name, self.print(tr))).collect();
                    format!("{:x}: a byte load at {} the spec does not load (the facts: {}; the values: {})", a, self.print(&ad), facts.join(", "), vals.join(", "))
                })?;
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let (by, hr) = self.result(&self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, ad.clone(), lit(1)])]))?;
                let tr = self.step("movzx8_ld", a, insn, &[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv, &ad, &by], self.tail(st, insn, 8, vec![had, taut(vec![R::S(hc.clone())]), hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 1, by);
                self.then(tr, st2)
            }
            // movzx r32, word: from r16, [b + d], [b + i]
            80 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                if x[3] != x[2] || nat(&x[0]) != Some(4) {
                    return Err(bad("not movzx r32, word"));
                }
                if let Some((0, h)) = self.tag(&x[2]) {
                    let hn = reg(&h)?;
                    let (n, b) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    let tr = self.step("movzx16_rrw", a, insn, &[&x[1], &h, &x[4], &lit(n), &b], self.tail(st, insn, 6, vec![]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, b);
                    return self.then(tr, st2);
                }
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                if self.app(&m["index"], "none", 0).is_some() {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let (hc, wt) = self.mem_hyp_rw(st, &bp, &d, 2)?;
                    let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 2))", self.print(&bp), self.print(&d)))?;
                    // (at d = 0: the spec's word at bp, if it has it)
                    let v0 = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), {}, 2))", self.print(&bp)))?;
                    let v = match self.canon(&v0).node() {
                        Node::Var(w0, _) if nat(&d) == Some(0) && self.vals.iter().any(|x| x.0 == *w0) => self.canon(&v0),
                        _ => self.value(&v),
                    };
                    let tr = self.step("movzx16_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &wt, &v], self.tail(st, insn, 6, vec![s(&hc), simp_l()]));
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 2, v);
                    return self.then(tr, st2);
                }
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                    return Err(bad("not [b + i]"));
                }
                let (bn, inn) = (reg(&b)?, reg(&i)?);
                let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                let iv = self.need_reg(st, inn, 8)?;
                let (ad, had) = self.result(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]))?;
                let hc = self.mem_hyp(st, &ad, &lit(0), 2)?;
                let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), {}, 2))", self.print(&ad)))?;
                let (v, hr) = self.result(&v)?;
                let tr = self.step("movzx16_ld", a, insn, &[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv, &ad, &v], self.tail(st, insn, 8, vec![had, s(&hc), hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 2, v);
                self.then(tr, st2)
            }
            // and rax, imm32 (sign-extended): the spec's form of the immediate
            49 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let k = nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                // and ax, imm16 (rax holding a 16-bit value)
                if nat(&x[0]) == Some(2) {
                    let (n, u) = self.reg(st, 0).ok_or_else(|| bad("an empty register"))?;
                    let (r, hr) = self.result(&self.mk("bits_and", vec![lit(16), u.clone(), x[1].clone()]))?;
                    let tr = self.step("and16_ax", a, insn, &[&x[1], &lit(n), &u, &r], self.tail(st, insn, 5, vec![hr]));
                    self.scratch.insert(0);
                    let st2 = self.set_reg(st, a2, 0, 2, r);
                    return self.then(tr, st2);
                }
                // and eax, imm32
                if nat(&x[0]) == Some(4) {
                    if let Some(pf) = self.widen(st, 0, 4)? {
                        return Ok(pf);
                    }
                    // (of a 64-bit word, a mask below 2^31: the 64-bit and, the upper half cleared)
                    if let (Some((8, u)), Some(kn)) = (self.reg(st, 0), nat(&x[1])) {
                        if kn < 1 << 31 {
                            let (r, hr) = self.result(&self.mk("bits_and", vec![lit(64), u.clone(), x[1].clone()]))?;
                            let tr = self.step("and32_imm_ax_w", a, insn, &[&x[1], &u, &r], self.tail(st, insn, 5, vec![hr]));
                            self.scratch.insert(0);
                            let st2 = self.set_reg(st, a2, 0, 8, r);
                            return self.then(tr, st2);
                        }
                    }
                    let u = self.need_reg(st, 0, 4)?;
                    let (r, hr) = self.result(&self.mk("bits_and", vec![lit(32), u.clone(), x[1].clone()]))?;
                    let tr = self.step("and32_imm_ax", a, insn, &[&x[1], &u, &r], self.tail(st, insn, 4, vec![hr]));
                    self.scratch.insert(0);
                    let st2 = self.set_reg(st, a2, 0, 4, r);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not and rax, imm32"));
                }
                let u = self.need_reg(st, 0, 8)?;
                let kk64 = if k >= 1 << 31 { k + 0xffff_ffff_0000_0000 } else { k };
                let kk = lit(kk64);
                let (r, hr) = self.result(&self.mk("bits_and", vec![lit(64), u.clone(), kk.clone()]))?;
                let tr = self.step("and64_imm", a, insn, &[&x[1], &kk, &u, &r], self.tail(st, insn, 5, vec![hr]));
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(tr, st2)
            }
            // test r8 / r32 / r64, itself: g's value (u, its low bits)
            25 | 61 => {
                let (g, size) = if insn.row == 25 {
                    let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                    (x[0].clone(), 1)
                } else {
                    let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                    (x[1].clone(), if nat(&x[0]) == Some(4) { 4 } else { 8 })
                };
                let gn = reg(&g)?;
                if size == 8 {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    return self.compare(st, a, a2, insn, "fs_test64", &[&g, &lit(n), &u], 4, Flags::Log(64, u.clone()));
                }
                let (n, x0, u) = self.low(st, gn, 8 * size)?;
                let (fs, np) = if size == 1 { ("fs_test8", 6) } else { ("fs_test32", 5) };
                self.compare(st, a, a2, insn, fs, &[&g, &lit(n), &x0, &u], np, Flags::Log(8 * size, u.clone()))
            }
            // movsx r32, r8
            81 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let (k, h) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 || x[3] != x[2] {
                    return Err(bad("not movsx r32, r8"));
                }
                let hn = reg(&h)?;
                if hn >= 4 {
                    return Err(bad("a high byte register"));
                }
                let b = self.need_reg(st, hn, 1)?;
                let (r, hr) = self.result(&self.mk("bits_sext", vec![lit(8), lit(32), b.clone()]))?;
                let tr = self.step("movsx8", a, insn, &[&x[1], &h, &x[4], &b, &r], self.tail(st, insn, 6, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
            }
            // test r32, imm32: g's low 32 bits and k, for the jump after it
            63 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (k0, g) = self.tag(&x[1]).ok_or_else(|| bad("fields"))?;
                if nat(&x[0]) != Some(4) || k0 != 0 {
                    return Err(bad("not test r32, imm32"));
                }
                let gn = reg(&g)?;
                let (n, x0, u) = self.low(st, gn, 32)?;
                let r = self.mk("bits_and", vec![lit(32), u.clone(), x[3].clone()]);
                self.compare(st, a, a2, insn, "fs_test32_imm", &[&g, &x[2], &x[3], &lit(n), &x0, &u], 6, Flags::Log(32, r))
            }
            // dec r64: g := u - 1; dec r32, the jump on its zero flag after it:
            // g := g's low 32 bits less 1 (4 bytes)
            66 => {
                let x = self.pairs(&f, 3).ok_or_else(|| bad("fields"))?;
                let (k0, g) = self.tag(&x[1]).ok_or_else(|| bad("fields"))?;
                if k0 != 0 || x[1] != x[2] {
                    return Err(bad("not dec r"));
                }
                let gn = reg(&g)?;
                match nat(&x[0]) {
                    Some(8) => {
                        let u = self.need_reg(st, gn, 8)?;
                        let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(64), u.clone(), lit(1)]))?;
                        let tr = self.step("dec64", a, insn, &[&g, &u, &r], self.tail(st, insn, 4, vec![hr]));
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(tr, st2)
                    }
                    Some(4) if self.insns.get(&a2).is_some_and(|j| matches!(j.row, 127 | 128)) => {
                        let (n, x0, u) = self.low(st, gn, 32)?;
                        let (r, hr) = self.result(&self.mk("bits_sub", vec![lit(32), u.clone(), lit(1)]))?;
                        let mut v = self.head(a, insn);
                        v.extend([&g, &lit(n), &x0, &u, &r, &st.hst, &st.rs, &st.w].into_iter().map(t));
                        v.push(p(R::F(insn.name.clone())));
                        v.extend((0..5).map(|_| simp_l()));
                        v.push(hr);
                        let step = mpf("tr.fs_dec32", v);
                        self.compare_x(st, a, a2, step, Flags::Zero(32, r.clone()), Some((gn, r, 4)))
                    }
                    _ => Err(bad("dec of a width other than 8, or 4 before a jump")),
                }
            }
            // movsb: the spec's move of the byte at rsi to rdi, both one up
            131 => {
                let si = self.need_reg(st, 6, 8)?;
                let di = self.need_reg(st, 7, 8)?;
                let (hc, st2, red) = self.spec_move(st, &di, &si, &lit(1))?;
                let (r6, h6) = self.result(&self.mk("bits_add", vec![lit(64), si.clone(), lit(1)]))?;
                let (r7, h7) = self.result(&self.mk("bits_add", vec![lit(64), di.clone(), lit(1)]))?;
                let tr = self.step("movsb", a, insn, &[&di, &si, &r6, &r7], self.tail_s(st, &st2, insn, 8, vec![h6, h7], &hc, &red));
                self.scratch.extend([6, 7]);
                let st3 = self.set_reg(&st2, a2, 6, 8, r6);
                let st3 = self.set_reg(&st3, a2, 7, 8, r7);
                self.then(tr, st3)
            }
            // rep movsq: the spec's move of the rcx words at rsi to rdi, both
            // 8 rcx up, rcx 0
            85 if nat(&f) == Some(8) => {
                let si = self.need_reg(st, 6, 8)?;
                let di = self.need_reg(st, 7, 8)?;
                let c = self.need_reg(st, 1, 8)?;
                let n = self.mk("int_mul", vec![lit(8), c.clone()]);
                let (hc, st2, red) = self.spec_move(st, &di, &si, &n)?;
                let c8 = self.mk("bits_mul", vec![lit(64), c.clone(), lit(8)]);
                let (r6, h6) = self.result(&self.mk("bits_add", vec![lit(64), si.clone(), c8.clone()]))?;
                let (r7, h7) = self.result(&self.mk("bits_add", vec![lit(64), di.clone(), c8]))?;
                let tr = self.step("rep_movsq", a, insn, &[&di, &si, &c, &r6, &r7], self.tail_s(st, &st2, insn, 11, vec![h6, h7], &hc, &red));
                self.scratch.extend([1, 6, 7]);
                let st3 = self.set_reg(&st2, a2, 6, 8, r6);
                let st3 = self.set_reg(&st3, a2, 7, 8, r7);
                let st3 = self.set_reg(&st3, a2, 1, 8, lit(0));
                self.then(tr, st3)
            }
            // rep stosq: the spec's fill of the rcx words rax at rdi, rdi
            // 8 rcx up, rcx 0
            86 if nat(&f) == Some(8) => {
                let di = self.need_reg(st, 7, 8)?;
                let c = self.need_reg(st, 1, 8)?;
                let xv = self.need_reg(st, 0, 8)?;
                let n = self.mk("int_mul", vec![lit(8), c.clone()]);
                let (hc, st2, red) = self.spec_move(st, &di, &xv, &n)?;
                let c8 = self.mk("bits_mul", vec![lit(64), c.clone(), lit(8)]);
                let (r7, h7) = self.result(&self.mk("bits_add", vec![lit(64), di.clone(), c8]))?;
                let tr = self.step("rep_stosq", a, insn, &[&di, &c, &xv, &r7], self.tail_s(st, &st2, insn, 10, vec![h7], &hc, &red));
                self.scratch.extend([1, 7]);
                let st3 = self.set_reg(&st2, a2, 7, 8, r7);
                let st3 = self.set_reg(&st3, a2, 1, 8, lit(0));
                self.then(tr, st3)
            }
            // ret: eax the spec's result
            122 => {
                if st.fr != 0 {
                    return Err(format!("{:x}: ret with a frame of {} bytes", a, st.fr));
                }
                let Spec::Ret(val, pr) = &st.spec else {
                    return Err(format!("{:x}: ret before the procedure's result (the spec at {})", a, match &st.spec {
                        Spec::Proc(i) => self.print(&self.qs[*i]),
                        _ => String::new(),
                    }));
                };
                // (two words, a small struct: rax:rdx the result's)
                if let Some(pv) = self.app(&self.expand(val), "pair", 2).map(|x| x.to_vec()) {
                    let (Some((n1, x)), Some((n2, y))) = (self.reg(st, 0), self.reg(st, 2)) else {
                        return Err(format!("{:x}: a two-word result, rax or rdx empty", a));
                    };
                    if self.expand(&x) != pv[0] || self.expand(&y) != pv[1] {
                        return Err(format!("{:x}: rax:rdx hold {}, {}; the spec returns {}", a, self.print(&x), self.print(&y), self.print(val)));
                    }
                    let res = mpf("tr.result_pair", vec![t(&st.w), t(&x), t(&y), simp_l(), simp_l()]);
                    let mut v = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(a)), t(&lit(insn.len)), t(&st.hst), t(&st.ds), t(&st.rs), t(pr), t(&st.w)];
                    v.extend([t(&lit(n1)), t(&lit(n2)), t(&x), t(&y), p(R::F(insn.name.clone())), simp_l(), simp_l(), simp_l(), simp_l(), p(self.cs_rs_pf(&st.rs)), p(res)]);
                    return self.run(&mpf("tr.ret_pair", v), &[]);
                }
                // (no result: rax:rdx anything; the objects released, the
                // result's world w with the callers' objects -- tr.ret_void_w)
                if let (0, Some(l)) = (self.rbytes, self.live_back(pr)) {
                    let ol = self.mk("fn_update", vec![self.mk("app", vec![st.w.clone(), Term::bytes(b"objs")]), Term::bytes(b"live"), l.clone()]);
                    let w2 = self.mk("fn_update", vec![st.w.clone(), Term::bytes(b"objs"), ol]);
                    let hw0 = self.hw0.clone().ok_or("the entry's world")?;
                    let wo = self.run(&mpf("tr.world_live", vec![t(&st.w), t(&self.vw), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]),
                        taut(vec![R::S(hw0.clone())]), taut(vec![R::S(hw0)])]), &[])?;
                    let res = mpf("tr.result_void_live", vec![t(&st.w), t(&l), taut(vec![R::S(wo.clone())])]);
                    let mut v = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(a)), t(&lit(insn.len)), t(&st.hst), t(&st.ds), t(&st.rs), t(pr), t(&st.w)];
                    v.extend([t(&w2), p(R::F(insn.name.clone())), p(self.cs_rs_pf(&st.rs))]);
                    v.extend((0..6).map(|_| taut(vec![R::S(wo.clone())])));
                    v.push(p(res));
                    return self.run(&mpf("tr.ret_void_w", v), &[]);
                }
                if self.rbytes == 0 {
                    let r = self.ret_step("tr.ret_void", a, insn, pr, vec![], mpf("tr.result_void", vec![t(&st.w)]), st);
                    return self.run(&r, &[]);
                }
                let n = self.rbytes;
                // (a 32-bit result in a 64-bit rax: its low half)
                if n == 4 {
                    if let Some((8, u)) = self.reg(st, 0) {
                        let low = self.mk("bits_of_int", vec![lit(32), u.clone()]);
                        if self.canon(&low) == self.canon(val) {
                            let r = self.ret_step("tr.ret_insn", a, insn, pr, vec![t(&lit(8)), t(&u)], mpf("tr.result32w", vec![t(&st.w), t(&u)]), st);
                            return self.run(&r, &[]);
                        }
                    }
                }
                // (a 32-bit write's value as a wider one: zero-extended)
                if let Some(pf) = self.widen(st, 0, n)? {
                    return Ok(pf);
                }
                let v = self.need_reg(st, 0, n)?;
                // (the same number written otherwise: equal by arithmetic)
                let mut eqf = None;
                if self.expand(&v) != self.expand(val) {
                    let defs: Vec<String> = ["bits_neg", "bits_add", "bits_sub", "pow2"].iter().map(|d| d.to_string()).collect();
                    match self.evp(&RP::Defs(Box::new(RP::Arith(vec![])), defs), &self.mk("eq", vec![v.clone(), val.clone()]), &[]) {
                        Ok(q) => eqf = Some(q),
                        Err(_) => {
                            return Err(format!("{:x}: rax holds {} = {}, the spec returns {} = {}", a, self.print(&v), self.print(&self.expand(&v)), self.print(val), self.print(&self.expand(val))))
                        }
                    }
                }
                // (the objects released, `objs := objs with { live: live0 }`:
                // the result's world w with the callers' objects L -- the
                // entry's --, its own bytes kept, tr.ret_insn_w)
                if let (Some(l), 8, None) = (self.live_back(pr), n, &eqf) {
                    let ol = self.mk("fn_update", vec![self.mk("app", vec![st.w.clone(), Term::bytes(b"objs")]), Term::bytes(b"live"), l.clone()]);
                    let w2 = self.mk("fn_update", vec![st.w.clone(), Term::bytes(b"objs"), ol]);
                    let hw0 = self.hw0.clone().ok_or("the entry's world")?;
                    let wo = self.run(&mpf("tr.world_live", vec![t(&st.w), t(&self.vw), taut(vec![R::S(st.hw.clone())]), taut(vec![R::S(st.hw.clone())]),
                        taut(vec![R::S(hw0.clone())]), taut(vec![R::S(hw0)])]), &[])?;
                    let res = mpf("tr.result64_live", vec![t(&st.w), t(val), t(&l), taut(vec![R::S(wo.clone())])]);
                    let mut v = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(a)), t(&lit(insn.len)), t(&st.hst), t(&st.ds), t(&st.rs), t(pr), t(&st.w)];
                    v.extend([t(&lit(8)), t(val), t(&w2), p(R::F(insn.name.clone())), simp_l(), simp_l(), p(self.cs_rs_pf(&st.rs))]);
                    v.extend((0..6).map(|_| taut(vec![R::S(wo.clone())])));
                    v.push(p(res));
                    return self.run(&mpf("tr.ret_insn_w", v), &[]);
                }
                let mut r = self.ret_step("tr.ret_insn", a, insn, pr, vec![t(&lit(n)), t(val)], mpf(&format!("tr.result{}", 8 * n), vec![t(&st.w), t(val)]), st);
                if let (Some(q), R::Mp(_, args)) = (eqf, &mut r) {
                    // (rax's entry: the spec's value, by the equation)
                    let i = args.len() - 3;
                    args[i] = simp_lw(vec![R::S(q)]);
                }
                self.run(&r, &[])
            }
            // mov byte [b + i], imm8 / mov byte [rip + d], imm8: the spec's store
            30 => {
                let x = self.pairs(&f, 3).ok_or_else(|| bad("fields"))?;
                let m = self.memop(&x[0]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let k = x[2].clone();
                if x[1] != x[0] {
                    return Err(bad("not mov byte [m], imm8"));
                }
                let mut extra = vec![];
                let (rule, terms, n, ad) = if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    ("store8i_rip", vec![lit(d), k.clone(), biga.clone()], 5, biga)
                } else if bk == 2 && self.app(&m["index"], "some", 1).is_none() && nat(&m["disp"]) == Some(0) {
                    // [b]: the address b's value
                    let (nb, bv) = self.reg(st, reg(&b)?).ok_or_else(|| bad("an empty base register"))?;
                    if nb != 8 {
                        return Err(bad("a base register not holding 64 bits"));
                    }
                    ("store8i_b", vec![b.clone(), k.clone(), bv.clone()], 7, bv)
                } else {
                    let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                    if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&i)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let (ad, had) = self.result(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]))?;
                    extra.push(had);
                    ("store8i_bi", vec![b.clone(), i.clone(), k.clone(), lit(nb), bv, iv, ad.clone()], 9, ad)
                };
                let (hc, v, st2, red, sa) = self.spec_store(st, &ad, 1)?;
                if self.eval_lit(&v) != nat(&k) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&k), self.print(&v)));
                }
                let _ = &sa;
                let tr: Vec<&Term> = terms.iter().collect();
                let tr = self.step(rule, a, insn, &tr, self.tail_s(st, &st2, insn, n, extra, &hc, &red));
                let mut st3 = st2;
                st3.a = a2;
                self.then(tr, st3)
            }
            // mov byte [rip + d] / [b + i], r8: the spec's store of the
            // register's low byte
            28 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let (gk, g) = self.tag(&x[3]).ok_or_else(|| bad("fields"))?;
                let gn = reg(&g)?;
                // mov byte [b + i + d], r8 (d not 0; any low byte register,
                // sil too): the spec's byte store at a computed offset
                if gk == 0 {
                    if let Some(pf) = self.store_bid(st, insn, a, a2, &x[2], &lit(1), &[&x[0], &x[1]], gn, &g)? {
                        return Ok(pf);
                    }
                }
                // (gp(g): g's low byte, any g -- the decoder's ah..bh are hi8)
                if gk != 0 {
                    return Err(bad("not mov byte [m], r8"));
                }
                let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                // (the address: a static's, or b + i; the rule's terms and
                // its literal facts' count)
                let mut hads = vec![];
                let (rule, terms, nlit, ad) = if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    ("store8_rip", vec![g.clone(), lit(d), x[0].clone(), x[1].clone(), lit(n), u.clone()], 7, biga)
                } else if bk == 2 && self.app(&m["index"], "some", 1).is_none() && nat(&m["disp"]) == Some(0) {
                    // [b]: the address b's value
                    let bv = self.need_reg(st, reg(&b)?, 8)?;
                    ("store8_b", vec![g.clone(), b.clone(), x[0].clone(), x[1].clone(), bv.clone(), lit(n), u.clone()], 9, bv)
                } else if bk == 2 && self.app(&m["index"], "some", 1).is_none() {
                    // [b + d]: b's value + d
                    let d = m["disp"].clone();
                    let bv = self.need_reg(st, reg(&b)?, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                    ("store8_bd", vec![g.clone(), b.clone(), d, x[0].clone(), x[1].clone(), bv, lit(n), u.clone()], 10, ad)
                } else {
                    let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                    if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&i)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let (ad, had) = self.result(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]))?;
                    hads.push(had);
                    ("store8_bi", vec![g.clone(), b.clone(), i.clone(), x[0].clone(), x[1].clone(), lit(nb), bv, iv, ad.clone(), lit(n), u.clone()], 11, ad)
                };
                let w0 = st.w.clone();
                let (hc, v, st2, red, sa, so) = self.spec_store_x(st, Some(&ad), Some(1))?;
                // (the register's low byte: the spec's value, u + k against v + k)
                let (ue, ve) = (self.expand(&u), self.expand(&v));
                // (a constant: a literal, or bits_neg(n, k) -- 2^n - k)
                let konst = |tr: &Term| -> Option<u128> {
                    self.eval_lit(tr).or_else(|| {
                        let x = self.app(tr, "bits_neg", 2)?;
                        let (n, k) = (nat(&x[0])?, self.eval_lit(&x[1])?);
                        (n < 64).then(|| ((1u128 << n) - k % (1u128 << n)) % (1u128 << n))
                    })
                };
                let low8 = (|| {
                    let x = self.app(&ue, "bits_add", 3)?;
                    let y = self.app(&ve, "bits_add", 3)?;
                    (nat(&x[0])? == 32 && nat(&y[0])? == 8 && self.canon(&x[1]) == self.canon(&y[1]) && konst(&x[2])? % 256 == konst(&y[2])? % 256)
                        .then(|| (x[1].clone(), x[2].clone(), y[2].clone()))
                })();
                // (a bitfield's: the bytes merged with the field, bit by bit)
                let lp = if let Some((_, pos, k, fv)) = &so.bf {
                    let low = self.mk("bits_slice", vec![u.clone(), lit(7), lit(0)]);
                    self.bf_merge(st, &w0, &sa, 1, pos, k, fv, &u, &low)?
                } else {
                    match low8 {
                    Some((bb, kk, kk2)) if self.eval_lit(&kk).is_some() && self.eval_lit(&kk) == self.eval_lit(&kk2) => {
                        p(mpf("tr.low8_add", vec![t(&bb), t(&kk), simp_l(), simp_l()]))
                    }
                    Some((bb, kk, kk2)) => p(mpf("tr.low8_add_mod", vec![t(&bb), t(&kk), t(&kk2), simp_l(), simp_l(), simp_l(), simp_l()])),
                    None => {
                        // (the register's low 8 bits and the spec's value: one
                        // normal form)
                        let lo = self.mk("bits_add", vec![lit(8), u.clone(), lit(0)]);
                        let by_nf = match self.nat_of(&u) {
                            Some(un) => match self.eq_nf_bits(&lo, &v)? {
                                Some(e) => {
                                    let l = self.run(&rec::mp(R::Inst("tr.low8_lo".into(), vec![("u", u.clone())]), vec![un]), &[])?;
                                    Some(rec::s(&Seq::trans(self.env, &l, &e).map_err(|e| e.0)?))
                                }
                                None => None,
                            },
                            None => None,
                        };
                        // (else: the low byte of a sum of words, shifts, bytes --
                        // their arithmetic modulo 2^8, the words' definitions)
                        by_nf.unwrap_or_else(|| {
                            RA::P(RP::Defs(Box::new(RP::Simp(true, vec![], vec![], false)), ["bits_slice", "bits_add", "bits_shl", "bits_mul", "bits_of_int"].iter().map(|x| x.to_string()).collect()))
                        })
                    }
                    }
                };
                let _ = &sa;
                let mut terms: Vec<&Term> = terms.iter().collect();
                terms.push(&v);
                if rule == "store8_rip" {
                    terms.push(&ad);
                }
                let mut extra = vec![lp];
                extra.extend(hads);
                let tr = self.step(rule, a, insn, &terms, self.tail_s(st, &st2, insn, nlit, extra, &hc, &red));
                let mut st3 = st2;
                st3.a = a2;
                self.then(tr, st3)
            }
            // nop
            109 => {
                let tr = mpf(
                    "tr.nop",
                    vec![
                        t(&self.s.clone()),
                        t(&self.v.clone()),
                        t(&self.base.clone()),
                        t(&self.code.clone()),
                        t(&lit(self.fr)),
                        t(&lit(a)),
                        t(&lit(a2)),
                        t(&lit(insn.len)),
                        t(&f),
                        t(&st.hst),
                        t(&st.ds),
                        t(&st.rs),
                        t(&self.p(&st.spec)),
                        t(&st.w),
                        p(R::F(insn.name.clone())),
                        simp_l(),
                        p(R::Slot("NEXT")),
                    ],
                );
                let mut st2 = st.clone();
                st2.a = a2;
                self.then(tr, st2)
            }
            // jmp rel8 / rel32
            124 | 125 => {
                let r = nat(&f).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let sx = if insn.row == 124 {
                    if r & 0x8000_0000 != 0 { r + 0xffff_ffff_0000_0000 } else { r }
                } else if r & 0x80 != 0 {
                    r + 0xffff_ffff_ffff_ff00
                } else {
                    r
                };
                let tt = (a2 + sx) % P64;
                let tr = mpf(
                    if insn.row == 124 { "tr.jmp32" } else { "tr.jmp8" },
                    vec![
                        t(&self.s.clone()),
                        t(&self.v.clone()),
                        t(&self.base.clone()),
                        t(&self.code.clone()),
                        t(&lit(self.fr)),
                        t(&lit(a)),
                        t(&lit(a2)),
                        t(&lit(tt)),
                        t(&lit(insn.len)),
                        t(&lit(r)),
                        t(&st.hst),
                        t(&st.ds),
                        t(&st.rs),
                        t(&self.p(&st.spec)),
                        t(&st.w),
                        p(R::F(insn.name.clone())),
                        simp_l(),
                        simp_l(),
                        simp_l(),
                        p(R::Slot("NEXT")),
                    ],
                );
                let mut st2 = st.clone();
                st2.a = tt;
                self.then(tr, st2)
            }
            // mov dword [rip + d], imm32: the spec's 4-byte store of k at a
            // static's address
            77 if self.pairs(&f, 4).and_then(|x| self.memop(&x[1])).and_then(|m| self.tag(&m["base"])).map_or(false, |b| b.0 == 1) => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let m = self.memop(&x[1]).ok_or_else(|| bad("fields"))?;
                // mov qword [rip + d], simm32: the spec's 8-byte store of the
                // immediate sign-extended
                if nat(&x[0]) == Some(8) && x[2] == x[1] {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    let kk = if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k };
                    let (hc, v, st2, red, _) = self.spec_store(st, &biga, 8)?;
                    if self.eval_lit(&v) != Some(kk) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, kk, self.print(&v)));
                    }
                    let tr = self.step("store64i_rip", a, insn, &[&lit(d), &x[3], &v, &biga], self.tail_s(st, &st2, insn, 6, vec![], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                if nat(&x[0]) != Some(4) || x[2] != x[1] {
                    return Err(bad("not mov dword [rip + d], imm32"));
                }
                let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let biga = lit((a2 + d) % P64);
                let k = x[3].clone();
                let (hc, v, st2, red, sa) = self.spec_store(st, &biga, 4)?;
                if self.eval_lit(&v) != nat(&k) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&k), self.print(&v)));
                }
                let _ = &sa;
                let tr = self.step("store32i_rip", a, insn, &[&lit(d), &k, &biga], self.tail_s(st, &st2, insn, 5, vec![], &hc, &red));
                let mut st3 = st2;
                st3.a = a2;
                self.then(tr, st3)
            }
            // mov qword [b + d], imm32 (b holding a pointer): the spec's 8-byte
            // field store of the immediate sign-extended
            77 if self.pairs(&f, 4).and_then(|x| self.base_disp(&x[1])).map_or(false, |z| z.0 != 4) => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (bn, b, d) = self.base_disp(&x[1]).ok_or_else(|| bad("not [b + d]"))?;
                // mov dword [b + d], imm32: the spec's 4-byte store of k
                if nat(&x[0]) == Some(4) && x[2] == x[1] {
                    let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    let bv = self.need_reg(st, bn, 8)?;
                    // (at offset 0: the address as the spec has it, p)
                    let ad = if nat(&d) == Some(0) { bv.clone() } else { self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()])) };
                    let (hc, v, st2, red, _) = self.spec_store(st, &ad, 4)?;
                    if self.eval_lit(&v) != Some(k) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, k, self.print(&v)));
                    }
                    let tr = self.step("store32i_bd", a, insn, &[&b, &d, &x[3], &bv, &ad], self.tail_s(st, &st2, insn, 9, vec![], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                // mov word [b + d], imm16: the spec's 2-byte store of k
                if nat(&x[0]) == Some(2) && x[2] == x[1] {
                    let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    let bv = self.need_reg(st, bn, 8)?;
                    let ad = if nat(&d) == Some(0) { bv.clone() } else { self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()])) };
                    let (hc, v, st2, red, _) = self.spec_store(st, &ad, 2)?;
                    if self.eval_lit(&v) != Some(k) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, k, self.print(&v)));
                    }
                    let tr = self.step("store16i_bd", a, insn, &[&b, &d, &x[3], &bv, &ad], self.tail_s(st, &st2, insn, 9, vec![], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                if nat(&x[0]) != Some(8) || x[2] != x[1] {
                    return Err(bad("not mov qword [b + d], imm32"));
                }
                let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k };
                let bv = self.need_reg(st, bn, 8)?;
                let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                let (hc, v, st2, red, _) = self.spec_store(st, &ad, 8)?;
                if self.eval_lit(&v) != Some(kk) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, kk, self.print(&v)));
                }
                let tr = self.step("store64i_bd", a, insn, &[&b, &d, &x[3], &lit(kk), &bv], self.tail_s(st, &st2, insn, 9, vec![], &hc, &red));
                let mut st3 = st2;
                st3.a = a2;
                self.then(tr, st3)
            }
            // mov dword [rsp + d], imm32: the home d := k (the frame written)
            77 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                // mov r64, simm32: the constant sign-extended (its numeral, N)
                if let (Some(8), Some((0, g))) = (nat(&x[0]), self.tag(&x[1])) {
                    let gn = reg(&g)?;
                    let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    // (a static's address: the spec's constant, as for lea)
                    let kv = if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k };
                    let q = match &st.spec {
                        Spec::Proc(i) | Spec::Plain(i) => self.qs[*i].clone(),
                        Spec::Ret(v, _) => v.clone(),
                    };
                    let mut found = None;
                    if kv >= 0x400000 {
                        self.statics(&q, kv, &mut found);
                    }
                    let (kk, hkk) = match found {
                        Some(c) => (c, simp0()),
                        None => self.result(&self.mk("bits_sext", vec![lit(32), lit(64), lit(k)]))?,
                    };
                    let tr = self.step("mov64_simm", a, insn, &[&g, &x[2], &x[3], &kk], self.tail(st, insn, 3, vec![hkk]));
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, kk);
                    return self.then(tr, st2);
                }
                let d = self.rsp_mem(&x[1]).ok_or_else(|| bad("not a home"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                // mov qword [rsp + d], simm32: the home d := k sign-extended
                if nat(&x[0]) == Some(8) && x[2] == x[1] {
                    let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    let kk = lit(if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k });
                    let cn = self.hkey(dn);
                    let (_, hs2, hk) = self.hkeep(st, cn, 8);
                    let tr = self.step("store64i_home", a, insn, &[&d, &lit(cn), &x[3], &kk], self.tail_h(st, insn, &hs2, 4, vec![defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]), simp_l(), simp_l(), simp_l(), simp_l(), simp0(), p(hk.clone())]));
                    let st2 = self.set_home(st, a2, cn, 8, kk);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(4) || x[2] != x[1] {
                    return Err(bad("not mov dword [rsp + d], imm32"));
                }
                let cn = self.hkey(dn);
                // (into a frame's object: the spec's 4-byte store there, its
                // address the frame's at cn -- shown the spec's by N)
                if self.obj_byte(cn) {
                    let k = x[3].clone();
                    let (hc, v, st2, red, _, so) = self.spec_store_x(st, None, Some(4))?;
                    if self.eval_lit(&v) != nat(&k) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&k), self.print(&v)));
                    }
                    let ha = self.mk("tr.ha", vec![self.s.clone(), lit(cn)]);
                    let ad = self.mk("bits_add", vec![lit(64), so.p.clone(), so.off.clone()]);
                    let q = self.addr_eq(st, &ha, &ad)?;
                    let tr = self.step("store32i_rsp", a, insn, &[&d, &lit(cn), &k, &so.p, &so.off], self.tail_s(st, &st2, insn, 4, vec![simp0(), simp_l(), simp_l(), simp_l(), s(&q)], &hc, &red));
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then(tr, st3);
                }
                let (_, hs2, hk) = self.hkeep(st, cn, 4);
                let k = x[3].clone();
                let tr = self.step("store32i_home", a, insn, &[&d, &lit(cn), &k], self.tail_h(st, insn, &hs2, 4, vec![defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]), simp_l(), simp_l(), simp_l(), simp_l(), p(hk.clone())]));
                let st2 = self.set_home(st, a2, cn, 4, k);
                self.then(tr, st2)
            }
            _ => {
                self.trace(|| {
                    let hyps: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
                    let vals: Vec<String> = self.vals.iter().map(|(v, tr)| format!("{} := {}", self.env.var(*v).name, self.print(tr))).collect();
                    format!("no rule at {:x}: facts {}; values {}", a, hyps.join(", "), vals.join(", "))
                });
                Err(bad("no rule for the instruction"))
            }
        }
    }

    /// A bitfield store's merged word (k bits at bit pos of the n bytes at
    /// a in w, the field fv): `low`, the register u's low n bytes as the
    /// store rule takes them, is GIMPLE's value -- bit by bit (`bitwise`)
    /// against the old bytes with the field replaced, `(H * 2^k + F) *
    /// 2^pos + L` (tr.bf_val; the old bytes' bound tr.bf_old)
    #[allow(clippy::too_many_arguments)]
    fn bf_merge(&mut self, st: &St, w: &Term, a: &Term, n: u128, pos: &Term, k: &Term, fv: &Term, u: &Term, low: &Term) -> Result<RA, String> {
        let pw = |g: &Gen, e: &Term| g.mk("pow2", vec![e.clone()]);
        let (pp, pk) = (pw(self, pos), pw(self, k));
        let vm = self.mk("app", vec![w.clone(), Term::bytes(b"vm")]);
        let old = self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(n)]);
        // (the field as the machine has it: shifted to pos, under its masks
        // in u -- its bits the spec's, by arith modulo 2^k)
        let old1 = self.mk("gimple.bytes_at", vec![self.mk("app", vec![w.clone(), Term::bytes(b"vm")]), a.clone(), lit(1)]);
        let fm = self.bf_field(&self.expand(u), &[self.expand(&old1), self.expand(&old)], pos, k).ok_or_else(|| format!("{:x}: a bitfield's merge {} not read", st.a, self.print(&self.expand(u))))?;
        let mk_mod = |g: &Gen, x: &Term| g.mk("int_mod", vec![x.clone(), g.mk("pow2", vec![k.clone()])]);
        let hm = self.arith_gen(&self.mk("eq", vec![mk_mod(self, fv), mk_mod(self, &fm)]), &["bits_add", "bits_of_int", "bits_neg", "bits_slice", "pow2"])?;
        // (H * 2^k + F) * 2^pos + L
        let h = self.mk("int_div", vec![self.mk("int_div", vec![old.clone(), pp.clone()]), pk.clone()]);
        let mid = self.mk("int_add", vec![self.mk("int_mul", vec![h, pk.clone()]), mk_mod(self, &fm)]);
        let rhs = self.mk("int_add", vec![self.mk("int_mul", vec![mid, pp.clone()]), self.mk("int_mod", vec![old.clone(), pp])]);
        let both = self.run(&mpf("tr.bf_old", vec![t(w), t(a), t(&lit(n)), taut(vec![R::S(st.hw.clone())]), simp_l()]), &[])?;
        let omega = self.mk("omega", vec![]);
        // (its two facts apart: arith reads a membership given on its own)
        let oo = self.evp(&RP::Taut(vec![R::S(both.clone())]), &self.mk("in", vec![old.clone(), omega.clone()]), &[])?;
        let ol = self.evp(&RP::Taut(vec![R::S(both)]), &self.mk("int_lt", vec![old.clone(), self.mk("int_pow", vec![lit(256), lit(n)])]), &[])?;
        let uo = self.evp(&RP::Simp(true, vec![], vec![], false), &self.mk("in", vec![u.clone(), omega.clone()]), &[])?;
        let fo = self.evp(&RP::Simp(true, vec![], vec![], false), &self.mk("in", vec![fm.clone(), omega]), &[])?;
        // (u's low n bytes as an 8n-bit word)
        let wb = self.mk("bits_of_int", vec![lit(8 * n), u.clone()]);
        let sl = self.evp(&RP::Defs(Box::new(RP::Simp(true, vec![R::S(uo.clone())], vec![], false)), vec!["bits_slice".into(), "bits_of_int".into()]), &self.mk("eq", vec![low.clone(), wb.clone()]), &[])?;
        // (the merged word an 8n-bit word: pos and k literals, so linear)
        let rb = self.evp(&RP::Defs(Box::new(RP::Arith(vec![R::S(oo.clone()), R::S(ol.clone()), R::S(fo.clone())])), vec!["pow2".into()]), &self.mk("in", vec![rhs.clone(), self.mk("bits", vec![lit(8 * n)])]), &[])?;
        let m0 = self.evp(&RP::Bitwise(vec![R::S(oo.clone()), R::S(ol.clone()), R::S(uo), R::S(fo), R::S(rb)], 8 * n), &self.mk("eq", vec![wb, rhs.clone()]), &[])?;
        let m = self.evp(&RP::Arith(vec![R::S(sl), R::S(m0)]), &self.mk("eq", vec![low.clone(), rhs]), &[])?;
        // (the old bytes below 2^64)
        let lt64 = RA::P(RP::Defs(Box::new(RP::Arith(vec![R::S(ol)])), vec!["pow2".into()]));
        Ok(p(mpf("tr.bf_val", vec![t(&old), t(pos), t(k), t(fv), t(&fm), t(low), s(&oo), lt64, simp_l(), simp_l(), simp_l(), s(&hm), s(&m)])))
    }

    /// a merge's field (k bits at pos): of its `or` (operands in N's order),
    /// the operand without the old bytes (their first, or all n: `olds`),
    /// below its shift by pos and its `and`s with 2^k - 1 (a literal:
    /// shifted down); no `or` -- the field cleared: 0
    fn bf_field(&self, u: &Term, olds: &[Term], pos: &Term, k: &Term) -> Option<Term> {
        let (ps, mask) = (nat(pos)?, (1u128 << nat(k)?) - 1);
        let Some(o) = self.app(u, "bits_or", 3).map(|o| o.to_vec()) else { return Some(lit(0)) };
        let x = [&o[2], &o[1]].into_iter().find(|x| !olds.iter().any(|old| self.mentions(x, old)))?.clone();
        if let Some(c) = nat(&x) {
            return (c % (1u128 << ps) == 0).then(|| lit(c >> ps));
        }
        // (shifted to pos: a shift, or a product by 2^pos -- `shl` read as one)
        let mut cur = match (self.app(&x, "bits_shl", 3), self.app(&x, "bits_mul", 3)) {
            (Some(y), _) if nat(&y[2]) == Some(ps) => y[1].clone(),
            (_, Some(y)) if ps > 0 && nat(&y[2]) == Some(1u128 << ps) => y[1].clone(),
            (_, Some(y)) if ps > 0 && nat(&y[1]) == Some(1u128 << ps) => y[2].clone(),
            _ if ps == 0 => x,
            _ => return None,
        };
        while let Some(y) = self.app(&cur, "bits_and", 3).map(|y| y.to_vec()) {
            if nat(&y[2]) != Some(mask) {
                break;
            }
            cur = y[1].clone();
        }
        Some(cur)
    }

    /// A register's low w bits as a compare reads them (tr.reg_low*): its
    /// entry's width, its value x0, and the operand -- x0 itself (at its own
    /// width, or known to fit), a 64-bit word's low half as a value of its
    /// own (a call's 32-bit result)
    fn low(&mut self, st: &St, g: u128, w: u128) -> Result<(u128, Term, Term), String> {
        let (n, x0) = self.reg(st, g).ok_or_else(|| format!("{:x}: register {} holds no value of the procedure", st.a, g))?;
        if w == 32 && n == 8 {
            let x = self.value(&self.mk("bits_of_int", vec![lit(32), x0.clone()]));
            return Ok((n, x0, x));
        }
        Ok((n, x0.clone(), x0))
    }

    /// a return's rule: `mp(RULE, s, V, base, code, a, len, hs, ds, rs, pr, w, ts.., decode, [simp(L), simp(L)], callee-saved, result)`
    /// the live objects the wrapper's last part restores (`objs := objs
    /// with { live: live0 }`: its `fn_update(.., "objs", fn_update(..,
    /// "live", L))`), if any
    fn live_back(&self, pr: &Term) -> Option<Term> {
        fn go(g: &Gen, t: &Term) -> Option<Term> {
            if let Some(x) = g.app(t, "fn_update", 3) {
                if x[1] == Term::bytes(b"objs") {
                    if let Some(y) = g.app(&x[2], "fn_update", 3) {
                        if y[1] == Term::bytes(b"live") && y[2].loose_depth(&g.env.binders_fn()) == 0 {
                            return Some(y[2].clone());
                        }
                    }
                }
            }
            match t.node() {
                Node::App(_, a) => a.iter().find_map(|x| go(g, x)),
                _ => None,
            }
        }
        go(self, pr)
    }

    fn ret_step(&self, rule: &str, a: u128, insn: &Insn, pr: &Term, ts: Vec<RA>, res: R, st: &St) -> R {
        let mut v = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(a)), t(&lit(insn.len)), t(&st.hst), t(&st.ds), t(&st.rs), t(pr), t(&st.w)];
        let has = !ts.is_empty();
        v.extend(ts);
        v.push(p(R::F(insn.name.clone())));
        if has {
            v.push(simp_l());
            v.push(simp_l());
        }
        v.push(p(self.cs_rs_pf(&st.rs)));
        v.push(p(res));
        mpf(rule, v)
    }

    /// a store's tail (the spec's store made at it): the maps, the specs
    /// before and after, the worlds, the decode fact, n literal facts, the
    /// extra premises, its definedness, the world after, the reduction, the
    /// next point
    /// mov [b + i + d], r (n bytes, d not 0; the fields z the decode's
    /// others): the spec's n-byte store at pp + off, off computed (memset's
    /// from n) -- the address (b + i) + d its, by their normal forms; the
    /// value the register's low n bytes. None: not this form
    #[allow(clippy::too_many_arguments)]
    pub(super) fn store_bid(&mut self, st: &St, insn: &Insn, a: u128, a2: u128, mem: &Term, nt: &Term, z: &[&Term; 2], g: u128, gt: &Term) -> Result<Option<Seq>, String> {
        let Some(m) = self.memop(mem) else { return Ok(None) };
        let (Some((2, b)), Some(ix), Some(n)) = (self.tag(&m["base"]), self.app(&m["index"], "some", 1).map(|y| y[0].clone()), nat(nt)) else { return Ok(None) };
        if nat(&m["scale"]) != Some(1) || nat(&m["disp"]) == Some(0) || nat(&m["seg"]) != Some(0) || ![1, 2, 4, 8].contains(&n) {
            return Ok(None);
        }
        let d = m["disp"].clone();
        let reg = |g: &Term| nat(g).ok_or_else(|| format!("{:x}: a register that is not a literal", a));
        let (bv, iv) = (self.need_reg(st, reg(&b)?, 8)?, self.need_reg(st, reg(&ix)?, 8)?);
        let (k, u) = if n == 8 { (8, self.need_reg(st, g, 8)?) } else { self.reg(st, g).ok_or_else(|| format!("{:x}: a store of an empty register", a))? };
        let (hc, v, st2, red, _, so) = self.spec_store_x(st, None, Some(n))?;
        if !so.soff {
            return Err(format!("{:x}: a store at [b + i + d], the spec's at {} + {} (an offset not computed)", a, self.print(&so.p), self.print(&so.off)));
        }
        // (the value: the register's low n bytes, the spec's by N)
        let low = if n == 8 { u.clone() } else { self.mk("bits_of_int", vec![lit(8 * n), u.clone()]) };
        let hux = self.eq_nf(&low, &v)?.ok_or_else(|| format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&low), self.print(&self.expand(&low)), self.print(&v), self.print(&self.expand(&v))))?;
        // (the address: (b + i) + d, the spec's pp + off by N)
        let bi = self.mk("bits_add", vec![lit(64), bv.clone(), iv.clone()]);
        let ea = self.mk("bits_add", vec![lit(64), bi, d.clone()]);
        let ad = self.mk("bits_add", vec![lit(64), so.p.clone(), so.off.clone()]);
        let q = self.addr_eq(st, &ea, &ad)?;
        let extra = vec![hux, simp_l(), simp_l(), s(&q)];
        let tr = if n == 8 {
            self.step("store64_bid", a, insn, &[gt, &b, &ix, &d, z[0], z[1], &bv, &iv, &u, &v, &so.p, &so.off], self.tail_s(st, &st2, insn, 12, extra, &hc, &red))
        } else {
            let rule = format!("store{}_bid", 8 * n);
            self.step(&rule, a, insn, &[gt, &b, &ix, &d, z[0], z[1], &bv, &iv, &lit(k), &u, &v, &so.p, &so.off], self.tail_s(st, &st2, insn, 12, extra, &hc, &red))
        };
        let mut st3 = st2;
        st3.a = a2;
        self.then(tr, st3).map(Some)
    }

    pub(super) fn tail_s(&self, st: &St, st2: &St, insn: &Insn, n: usize, extra: Vec<RA>, hc: &Seq, red: &R) -> Vec<RA> {
        let mut v = vec![t(&st.hst), t(&st.ds), t(&st.rs), t(&self.p(&st.spec)), t(&self.p(&st2.spec)), t(&st.w), t(&st2.w), p(R::F(insn.name.clone()))];
        v.extend((0..n).map(|_| simp_l()));
        v.extend(extra);
        v.push(simp_lw(vec![R::S(hc.clone())]));
        v.push(simp0());
        v.push(p(red.clone()));
        v.push(p(R::Slot("NEXT")));
        v
    }

    /// nullary defined constants of `t` whose value is `addr`
    fn statics(&self, t: &Term, addr: u128, found: &mut Option<Term>) {
        match t.node() {
            Node::App(s, a) => {
                if a.is_empty() {
                    if let SymKind::Defined { params, body } = &self.env.syms[*s as usize].kind {
                        if params.is_empty() && nat(body) == Some(addr) {
                            *found = Some(t.clone());
                        }
                    }
                }
                a.iter().for_each(|x| self.statics(x, addr, found));
            }
            Node::Var(_, a) => a.iter().for_each(|x| self.statics(x, addr, found)),
            _ => {}
        }
    }
}
