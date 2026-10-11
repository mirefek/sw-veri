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
        // (in a zero-initialization: its stores only)
        if st.z.is_some() && insn.row != 145 && insn.row != 150 {
            return Err(bad("in a zero-initialization: not a store of the zero register"));
        }
        match insn.row {
            // cmp r64, qword [rsp + d]: g (u) against the home's word
            57 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
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
            // movups / movq [b + d], x (x zero): the next c of the bytes
            145 | 150 => {
                let Some((xr, bz, o, k)) = st.z.clone() else { return Err(bad("a store of an xmm register outside a zero-initialization")) };
                let (c, nf) = if insn.row == 145 { (16u128, 4) } else { (8u128, 5) };
                let x = self.pairs(&f, nf).ok_or_else(|| bad("fields"))?;
                if reg(&x[0])? != xr {
                    return Err(bad("a store of an xmm register not zeroed"));
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
                // mov r64, [rip + d]: the spec's load of a static's word
                if let Some(m) = self.memop(&x[2]).filter(|m| self.tag(&m["base"]).is_some_and(|b| b.0 == 1) && nat(&x[0]) == Some(8)) {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = (a2 + d) % P64;
                    let (pp, off, hc) = self.static_mem_hyp(st, biga, 8)?;
                    let tr = self.step("load64_rip", a, insn, &[&x[1], &lit(d), &x[4], &pp, &off], self.tail(st, insn, 6, vec![s(&hc)]));
                    let v = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 8))", self.print(&pp), self.print(&off)))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, v);
                    return self.then(tr, st2);
                }
                // mov r64 / r32, [b + d] (b holding a pointer): the spec's field load
                if self.rsp_mem(&x[2]).is_none() && matches!(nat(&x[0]), Some(8) | Some(4)) {
                    let n = nat(&x[0]).unwrap();
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let hc = self.mem_hyp(st, &bp, &d, n)?;
                    let rd = |ea: &str| format!("bits_of_int({}, gimple.bytes_at(app({wn}, \"vm\"), {ea}, {}))", 8 * n, n);
                    let eb = format!("bits_add(64, {}, {})", self.print(&bp), self.print(&d));
                    let v = self.parse(&rd(&eb))?;
                    let (tr, v) = if n == 8 {
                        (self.step("load64_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp], self.tail(st, insn, 6, vec![s(&hc)])), v)
                    } else {
                        // (at offset 0: the address as the spec read it, p or p + 0)
                        let v0 = self.parse(&rd(&self.print(&bp)))?;
                        let (ea, v) = if nat(&d) == Some(0) && self.val_of.contains_key(&self.expand(&v0)) { (bp.clone(), v0) } else { (self.parse(&eb)?, v) };
                        (self.step("load32_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &ea], self.tail(st, insn, 7, vec![s(&hc)])), v)
                    };
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, n, v);
                    return self.then(tr, st2);
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let c = lit(self.hkey(dn));
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
            // neg r32
            64 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let op = nat(&x[1]);
                if !(op == Some(3) || op == Some(2)) || k != 0 {
                    return Err(bad("not neg / not r32"));
                }
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, 4)?;
                let (rule, r) = if op == Some(2) { ("not32", self.mk("bits_not", vec![lit(32), u.clone()])) } else { ("neg32", self.mk("bits_sub", vec![lit(32), lit(0), u.clone()])) };
                let tr = self.step(rule, a, insn, &[&g, &x[3], &u], self.tail(st, insn, 4, vec![]));
                let r = self.value(&r);
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
                let r = self.value_comm(&op);
                let hr = self.comm_premise(&r, &op);
                let tr = self.step("and32_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u, &r], self.tail(st, insn, 8, vec![hr]));
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
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
                let r = self.value_comm(&op);
                let hr = self.comm_premise(&r, &op);
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
                    let r = self.value_comm(&op);
                    let hr = self.comm_premise(&r, &op);
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
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home_n(&st.hsm, &d, 8)?;
                let u = self.need_reg(st, g, 8)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let op = self.mk("bits_mul", vec![lit(64), u.clone(), v.clone()]);
                let r = self.value_comm(&op);
                let hr = self.comm_premise(&r, &op);
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
                let tr = self.step("sub32_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u], self.tail(st, insn, 8, vec![]));
                let r = self.mk("bits_sub", vec![lit(32), u, v]);
                let r = self.value(&r);
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
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home_n(&st.hsm, &d, 8)?;
                let u = self.need_reg(st, g, 8)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let tr = self.step("sub64_home", a, insn, &[&x[1], &d, &c, &x[3], &x[4], &v, &u], self.tail(st, insn, 8, vec![]));
                let r = self.mk("bits_sub", vec![lit(64), u, v]);
                let r = self.value(&r);
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
                let u = self.need_reg(st, hn, 4)?;
                let by = self.imul_fact(c)?;
                let tr = self.step("imul32", a, insn, &[&x[1], &h, &x[3], &x[4], &x[5], &u], self.tail(st, insn, 4, vec![s(&by), simp_l(), simp_l()]));
                let r = self.mk("bits_mul", vec![lit(32), u, x[5].clone()]);
                let r = self.value(&r);
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
                let tr = self.step("cas32_b", a, insn, &[&x[1], &b, &x[3], &x[4], &x[5], &bv, &tv, &sv], self.tail_s(st, &st2, insn, 11, vec![], &hc, &red));
                let dv = self.value(&dv);
                self.scratch.insert(0);
                let st3 = self.set_reg(&st2, a2, 0, 4, dv);
                self.then(tr, st3)
            }
            // cmp ax / eax, imm16 / imm32: rax's low bits (u) against k
            58 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let (fs, w) = match nat(&x[0]) {
                    Some(2) => ("fs16_ax", 16),
                    Some(4) => ("fs32_eax", 32),
                    _ => return Err(bad("not cmp ax / eax, imm")),
                };
                let (n, x0, u) = self.low(st, 0, w)?;
                let k = x[1].clone();
                self.compare(st, a, a2, insn, fs, &[&k, &k, &lit(n), &x0, &u], 6, Flags::Sub(w, u.clone(), k.clone()))
            }
            // shr / shl r32, cl: by the spec's count (below 32, a fact in scope)
            74 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not shr / shl r32, cl")) };
                let h = match nat(&x[1]) {
                    Some(5) => "shr",
                    Some(4) => "shl",
                    _ => return Err(bad("not shr / shl r32, cl")),
                };
                if nat(&x[0]) != Some(4) {
                    return Err(bad("not shr / shl r32, cl"));
                }
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, 4)?;
                let c = self.need_reg(st, 1, 4)?;
                let lt = self.mk("int_lt", vec![c.clone(), lit(32)]);
                let hc = self.hyp_find(&st.hyps, &lt).map(|h| h.1.clone()).ok_or_else(|| bad("a shift by cl not known below 32"))?;
                // (a literal shifted: the spec's value, its literal as bits_of_int(32, k), if it has one)
                let op = self.mk(&format!("bits_{h}"), vec![lit(32), u.clone(), c.clone()]);
                let spec_form = nat(&u).and_then(|_| {
                    let alt = self.canon(&self.mk(&format!("bits_{h}"), vec![lit(32), self.mk("bits_of_int", vec![lit(32), u.clone()]), c.clone()]));
                    matches!(alt.node(), Node::Var(v, _) if self.vals.iter().any(|x| x.0 == *v)).then_some(alt)
                });
                let (r, hr) = match spec_form {
                    Some(r) => (r, RA::P(RP::Defs(Box::new(RP::Simp(true, vec![], vec![], false)), vec!["bits_of_int".into()]))),
                    None => (self.value(&op), simp_l()),
                };
                let tr = self.step(&format!("{h}32_cl"), a, insn, &[&g, &x[3], &c, &u, &r], self.tail(st, insn, 6, vec![s(&hc), hr]));
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
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
                    // shr r64, c
                    (8, 5) => {
                        let u = self.need_reg(st, gn, 8)?;
                        let tr = self.step("shr64_imm", a, insn, &[&g, &x[3], &x[4], &u], self.tail(st, insn, 7, vec![]));
                        let r = self.mk("bits_shr", vec![lit(64), u, x[4].clone()]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shl r64, 12 of a word shifted down by 12: the field above
                    // its first byte, times 4096
                    (8, 4) if c == 12 => {
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
                        let tr = self.step("shl12_field", a, insn, &[&g, &x[3], &bp, &lit(off), &lit(off + 1)], self.tail(st, insn, 5, vec![]));
                        let r = self.parse(&format!(
                            "bits_mul(64, bits_of_int(52, int_mod(int_div(gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 7), int_pow(2, 4)), int_pow(2, 52))), 4096)",
                            self.print(&bp),
                            off + 1
                        ))?;
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shr r16, c: the machine's value (a field rule reads it)
                    (2, 5) => {
                        let u = self.need_reg(st, gn, 2)?;
                        let tr = self.step("shr16_imm", a, insn, &[&g, &x[3], &x[4], &u], self.tail(st, insn, 7, vec![]));
                        let r = self.parse(&format!("bits_set_slice(64, {u}, 15, 0, bits_shr(16, bits_slice({u}, 15, 0), {c}))", u = self.print(&u)))?;
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                    // shl r32, c: a product by 2^c
                    (4, 4) => {
                        let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                        let mk = 1u128 << c;
                        let tr = self.step("shl32_imm", a, insn, &[&g, &x[3], &x[4], &lit(mk), &lit(n), &u], self.tail(st, insn, 9, vec![]));
                        let r = self.mk("bits_mul", vec![lit(32), u, lit(mk)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(tr, st2);
                    }
                    _ => return Err(bad("no rule for the shift")),
                }
                let u = self.need_reg(st, gn, 4)?;
                let tr = self.step("shr32", a, insn, &[&g, &x[3], &x[4], &u], self.tail(st, insn, 7, vec![]));
                let r = self.mk("bits_shr", vec![lit(32), u, x[4].clone()]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // mov r32, r32 (the store form: rm the destination)
            75 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // mov [rsp + d], r32 / r64: the home c := the register's low n bytes
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                    if n != 4 && n != 8 {
                        return Err(bad("a store to a home of other than 4 or 8 bytes"));
                    }
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let cn = self.hkey(dn);
                    let (ng, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                    // (the value: the register's; its low bytes, of a 64-bit word bits_of_int(64, y): y's)
                    let xv = if ng == n {
                        u.clone()
                    } else {
                        let y = self.app(&u, "bits_of_int", 2).filter(|y| nat(&y[0]) == Some(64)).map(|y| y[1].clone()).unwrap_or_else(|| u.clone());
                        self.mk("bits_of_int", vec![lit(8 * n), y])
                    };
                    let (_, hs2, hk) = self.hkeep(st, cn, n);
                    // (x = bits_of_int(8n, u): of a call's result, by its
                    // being in bits(64))
                    let hx = simp_lw(self.facts_about(&st.facts, &u));
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
                    if nat(&d) != Some(0) {
                        return Err(bad("a 2-byte store at [b + d], d not 0"));
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
                    let u = self.need_reg(st, g, 4)?;
                    // mov [b + d], r32: the spec's 4-byte field store
                    if nat(&d) != Some(0) {
                        let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                        let (hc, v, st2, red, _) = self.spec_store(st, &ad, 4)?;
                        if self.canon(&v) != self.canon(&u) {
                            return Err(format!("{:x}: the machine stores {} ({}), the spec {} ({})", a, self.print(&u), self.print(&self.expand(&u)), self.print(&v), self.print(&self.expand(&v))));
                        }
                        let tr = self.step("store32_bd", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u], self.tail_s(st, &st2, insn, 10, vec![], &hc, &red));
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
                // mov [b + d], r64 (b holding a pointer): the spec's 8-byte field store
                if let (Some((bn, b, d)), Some(8)) = (self.base_disp(&x[2]).filter(|z| z.0 != 4), nat(&x[0])) {
                    let bv = self.need_reg(st, bn, 8)?;
                    let u = self.need_reg(st, g, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                    let (hc, v, st2, red, _) = self.spec_store(st, &ad, 8)?;
                    if self.canon(&v) != self.canon(&u) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&u), self.print(&v)));
                    }
                    let tr = self.step("store64_bd", a, insn, &[&x[1], &b, &d, &x[3], &x[4], &bv, &u], self.tail_s(st, &st2, insn, 10, vec![], &hc, &red));
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
                        let tr = self.step("mov32_rr8", a, insn, &[&x[1], &h, &x[3], &x[4], &u], self.tail(st, insn, 5, vec![]));
                        self.scratch.insert(hn);
                        let r = self.mk("bits_of_int", vec![lit(32), u]);
                        let r = self.value(&r);
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
                        let tr = self.step("shr64_1", a, insn, &[&g, &u], self.tail(st, insn, 4, vec![]));
                        let r = self.mk("bits_shr", vec![lit(64), u, lit(1)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(tr, st2);
                    }
                }
                if nat(&x[0]) != Some(4) || nat(&x[1]) != Some(5) || x[2] != x[3] {
                    return Err(bad("not shr r/m32, 1"));
                }
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let u = home(&st.hsm, &d)?;
                    let cn = self.hkey(dn);
                    let (_, hs2, hk) = self.hkeep(st, cn, 4);
                    let tr = self.step("shr32_1_home", a, insn, &[&d, &lit(cn), &u], self.tail_h(st, insn, &hs2, 6, vec![p(hk.clone())]));
                    let r = self.mk("bits_shr", vec![lit(32), u, lit(1)]);
                    let r = self.value(&r);
                    let st2 = self.set_home(st, a2, cn, 4, r);
                    return self.then(tr, st2);
                }
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not shr r/m32, 1")) };
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, 4)?;
                let tr = self.step("shr32_1", a, insn, &[&g, &u], self.tail(st, insn, 4, vec![]));
                let r = self.mk("bits_shr", vec![lit(32), u, lit(1)]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // or dword [rsp + d], r32
            38 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
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
                    let op = self.mk("bits_or", vec![lit(32), u.clone(), xv.clone()]);
                    let r = self.value(&op);
                    let tr = self.step("or32_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![simp_l()]));
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
                let tr = self.step(rule, a, insn, &[&d, &lit(cn), &x[1], &v, &u], self.tail_h(st, insn, &hs2, 9, vec![p(hk.clone())]));
                let r = self.mk("bits_or", vec![lit(8 * n), u, v]);
                let r = self.value(&r);
                let st2 = self.set_home(st, a2, cn, n, r);
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
                    let u = self.need_reg(st, gn, 8)?;
                    let xv = self.need_reg(st, hn, 8)?;
                    let tr = self.step("sub64_rr", a, insn, &[&g, &x[1], &u, &xv], self.tail(st, insn, 7, vec![]));
                    let r = self.mk("bits_sub", vec![lit(64), u, xv]);
                    let r = self.value(&r);
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, r);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(4) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not sub r32, r32"));
                }
                let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                let u = self.need_reg(st, gn, 4)?;
                let (nh, xv) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                // (h holding 32 bits: its value itself)
                let (tr, r) = if nh == 4 {
                    let tr = self.step("sub32_rr4", a, insn, &[&g, &x[1], &u, &xv], self.tail(st, insn, 7, vec![]));
                    (tr, self.mk("bits_sub", vec![lit(32), u, xv.clone()]))
                } else {
                    let tr = self.step("sub32_rr", a, insn, &[&g, &x[1], &u, &lit(nh), &xv], self.tail(st, insn, 7, vec![]));
                    (tr, self.mk("bits_sub", vec![lit(32), u, self.mk("bits_of_int", vec![lit(32), xv.clone()])]))
                };
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(tr, st2)
            }
            // and r32, r32 (the result as the spec orders it)
            47 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not and r32, r32")) };
                if nat(&x[0]) != Some(4) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not and r32, r32"));
                }
                let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                for r in [gn, hn] {
                    if let Some(pf) = self.widen(st, r, 4)? {
                        return Ok(pf);
                    }
                }
                let u = self.need_reg(st, gn, 4)?;
                let xv = self.need_reg(st, hn, 4)?;
                let op = self.mk("bits_and", vec![lit(32), u.clone(), xv.clone()]);
                let r = self.value_comm(&op);
                let hr = self.comm_premise(&r, &op);
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
                    let r = self.value_comm(&op);
                    let hr = self.comm_premise(&r, &op);
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
                    let r = self.value_comm(&op);
                    let hr = self.comm_premise(&r, &op);
                    let tr = self.step("add32_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 7, vec![hr]));
                    (tr, r)
                } else {
                    let r = self.value_comm(&self.mk("bits_add", vec![lit(64), u.clone(), xv.clone()]));
                    let tr = self.step("add64_rr", a, insn, &[&g, &x[1], &u, &xv, &r], self.tail(st, insn, 8, vec![]));
                    (tr, r)
                };
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, n, r);
                self.then(tr, st2)
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
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("an imm32 operation not on a home"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
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
                    // add qword [rsp + d], imm8: the 8-byte home's u + kk
                    if nat(&x[0]) == Some(8) && x[3] == x[2] && nat(&x[1]) == Some(0) {
                        let kk = lit(if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm });
                        let cn = self.hkey(dn);
                        let Some((8, u)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                        let (_, hs2, hk) = self.hkeep(st, cn, 8);
                        let tr = self.step("add64_home", a, insn, &[&d, &lit(cn), &x[4], &kk, &u], self.tail_h(st, insn, &hs2, 8, vec![p(hk.clone())]));
                        let r = self.mk("bits_add", vec![lit(64), u, kk]);
                        let r = self.value(&r);
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
                            let tr = self.step("add32_home", a, insn, &[&d, &ck, &x[4], &kk, &u], self.tail_h(st, insn, &hs2, 8, vec![p(hk.clone())]));
                            let r = self.mk("bits_add", vec![lit(32), u, kk]);
                            let r = self.value(&r);
                            let st2 = self.set_home(st, a2, cn, 4, r);
                            self.then(tr, st2)
                        }
                        // cmp: the home (u) against kk
                        Some(7) => self.compare(st, a, a2, insn, "fs32_hi8", &[&d, &ck, &x[4], &kk, &u], 7, Flags::Sub(32, u.clone(), kk.clone())),
                        _ => Err(bad("an operation on a home other than add, cmp")),
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
                // and r32, imm8 of a byte: in 8 bits; of a shifted word: the field
                if (size, nat(&x[1])) == (4, Some(4)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n == 1 {
                        // (a low mask 2^kb - 1 of a byte read: the bitfield's
                        // form, when the spec has read it so)
                        let mut r = self.mk("bits_and", vec![lit(8), u.clone(), lit(kk)]);
                        if let (Some(kb), Some(b)) = ((1..8).find(|kb| (1u128 << kb) - 1 == kk), self.app(&self.expand(&u), "bits_of_int", 2).filter(|b| nat(&b[0]) == Some(8)).map(|b| b[1].clone())) {
                            let fd = self.parse(&format!("bits_of_int({kb}, int_mod(int_div({}, int_pow(2, 0)), int_pow(2, {kb})))", self.print(&b)))?;
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
                            let tr = self.step("and32_imm_w", a, insn, &[&g, &x[3], &x[4], &u], self.tail(st, insn, 6, vec![]));
                            let r = self.mk("bits_and", vec![lit(64), u, x[4].clone()]);
                            let r = self.value(&r);
                            self.scratch.insert(gn);
                            let st2 = self.set_reg(st, a2, gn, 8, r);
                            return self.then(tr, st2);
                        }
                        let (q, pos) = shape.ok_or_else(|| bad("and of a 64-bit value not a shifted word"))?;
                        let kb = (0..16).find(|kb| (1u128 << kb) - 1 == kk).ok_or_else(|| bad("a field mask not 2^k - 1"))?;
                        self.fields.insert((pos, kb, kk));
                        let q = self.canon(&q);
                        let ff = self.field_fact(pos, kb, kk)?;
                        let tr = self.step("and_field16", a, insn, &[&g, &x[3], &x[4], &lit(kk), &q, &lit(pos), &lit(kb)], self.tail(st, insn, 4, vec![s(&ff), simp_l(), simp_l(), simp_l()]));
                        let r = self.parse(&format!(
                            "bits_of_int({kb}, int_mod(int_div(gimple.bytes_at(app({wn}, \"vm\"), {}, 2), int_pow(2, {pos})), int_pow(2, {kb})))",
                            self.print(&q)
                        ))?;
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(tr, st2);
                    }
                }
                // add r32, imm8 (g holding a value of at most 4 bytes): g := u + kk
                if (size, nat(&x[1])) == (4, Some(0)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n > 4 {
                        return Err(bad("add r32 of a wider value"));
                    }
                    let tr = self.step("add32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &lit(n), &u], self.tail(st, insn, 7, vec![]));
                    let r = self.mk("bits_add", vec![lit(32), u, lit(kk)]);
                    let r = self.value(&r);
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(tr, st2);
                }
                let u = self.need_reg(st, gn, size)?;
                match (size, nat(&x[1])) {
                    // add r64, imm8: GIMPLE's u + k
                    (8, Some(0)) => {
                        let kk = if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm };
                        let tr = self.step("add64_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u], self.tail(st, insn, 6, vec![]));
                        let r = self.mk("bits_add", vec![lit(64), u, lit(kk)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(tr, st2)
                    }
                    // sub r64, imm8: GIMPLE's p + -k
                    (8, Some(5)) => {
                        let kk = if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm };
                        let tr = self.step("sub64_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u], self.tail(st, insn, 6, vec![]));
                        let neg = self.mk("bits_neg", vec![lit(64), lit(kk)]);
                        let r = self.mk("bits_add", vec![lit(64), u, neg]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(tr, st2)
                    }
                    // and r32, imm8
                    (4, Some(4)) => {
                        let tr = self.step("and32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u], self.tail(st, insn, 6, vec![]));
                        let r = self.mk("bits_and", vec![lit(32), u, lit(kk)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(tr, st2)
                    }
                    (4, Some(5)) => {
                        let tr = self.step("sub32_imm", a, insn, &[&g, &x[3], &x[4], &lit(kk), &u], self.tail(st, insn, 6, vec![]));
                        let neg = self.mk("bits_neg", vec![lit(32), lit(kk)]);
                        let r = self.mk("bits_add", vec![lit(32), u, neg]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(tr, st2)
                    }
                    // cmp r32, imm8: g's low 32 bits (u) against kk
                    (4, Some(7)) => {
                        let (n, x0, u) = self.low(st, gn, 32)?;
                        self.compare(st, a, a2, insn, "fs32_ri8", &[&g, &x[3], &x[4], &lit(kk), &lit(n), &x0, &u], 7, Flags::Sub(32, u.clone(), lit(kk)))
                    }
                    _ => Err(bad("unknown operation")),
                }
            }
            // cmp al, imm8: al (b, rax's low byte) against k (for je / jne as
            // GIMPLE writes it: a negative byte bits_neg(8, -k))
            23 => {
                let k = nat(&f).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let cc = self.jcc(a2)?.4;
                let kk = if k >= 128 && (cc == 4 || cc == 5) { self.mk("bits_neg", vec![lit(8), lit(256 - k)]) } else { lit(k) };
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
                let tr = self.step("movsxd", a, insn, &[&x[0], &h, &x[2], &x[3], &u], self.tail(st, insn, 5, vec![]));
                let r = self.mk("bits_sext", vec![lit(32), lit(64), u]);
                let r = self.value(&r);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, r);
                self.then(tr, st2)
            }
            // cdqe
            91 => {
                let u = self.need_reg(st, 0, 4)?;
                let tr = self.step("cdqe", a, insn, &[&u], self.tail(st, insn, 3, vec![]));
                let r = self.mk("bits_sext", vec![lit(32), lit(64), u]);
                let r = self.value(&r);
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(tr, st2)
            }
            // lea r64, [rip + d]: a static's address (the spec's name for it)
            78 => {
                let x = self.pairs(&f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let m = self.record(&x[5]).ok_or_else(|| bad("fields"))?;
                // lea r32, [b + d]: u + d, 32 bits
                if nat(&x[0]) == Some(4) {
                    let (bk, b) = m.get("base").and_then(|b| self.tag(b)).ok_or_else(|| bad("fields"))?;
                    let d = m.get("disp").and_then(nat).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    // lea r32, [i * k]: u * k, 32 bits (GIMPLE's product)
                    if let (0, Some(idx), Some(k), 0) = (bk, m.get("index").and_then(|i| self.app(i, "some", 1)).map(|i| i[0].clone()), m.get("scale").and_then(nat), d) {
                        let i = reg(&idx)?;
                        let u = self.need_reg(st, i, 4)?;
                        let tr = self.step("lea32_is", a, insn, &[&x[1], &idx, &lit(k), &x[2], &x[3], &x[4], &u], self.tail(st, insn, 6, vec![]));
                        let r = self.mk("bits_mul", vec![lit(32), u, lit(k)]);
                        let r = self.value(&r);
                        self.scratch.insert(g);
                        let st2 = self.set_reg(st, a2, g, 4, r);
                        return self.then(tr, st2);
                    }
                    if bk != 2 || m.get("index").map_or(true, |i| self.app(i, "none", 0).is_none()) || m.get("scale").and_then(nat) != Some(1) {
                        return Err(bad("not lea r32, [b + d]"));
                    }
                    let bn = reg(&b)?;
                    let (nb, u) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    // (a negative displacement as GIMPLE writes it: bits_neg(32, -d))
                    let k32 = d % (1 << 32);
                    let (kk, hk) = if k32 >= 1 << 31 {
                        (self.mk("bits_neg", vec![lit(32), lit((1 << 32) - k32)]), defs(RP::Arith(vec![]), &["bits_neg", "pow2"]))
                    } else {
                        (lit(k32), simp_l())
                    };
                    let tr = self.step("lea32_bd", a, insn, &[&x[1], &b, &lit(d), &x[2], &x[3], &x[4], &lit(nb), &u, &kk], self.tail(st, insn, 6, vec![hk]));
                    let r = self.mk("bits_add", vec![lit(32), u, kk]);
                    let r = self.value(&r);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, r);
                    return self.then(tr, st2);
                }
                // lea r64, [i * k]: u * k
                if let (Some((0, _)), Some(idx), Some(k), Some(0)) = (m.get("base").and_then(|b| self.tag(b)), m.get("index").and_then(|i| self.app(i, "some", 1)).map(|i| i[0].clone()), m.get("scale").and_then(nat), m.get("disp").and_then(nat)) {
                    let i = reg(&idx)?;
                    let (n, u) = self.reg(st, i).ok_or_else(|| bad("an empty index register"))?;
                    let tr = self.step("lea64_is", a, insn, &[&x[1], &idx, &lit(k), &x[2], &x[3], &x[4], &lit(n), &u], self.tail(st, insn, 6, vec![]));
                    let r = self.mk("bits_mul", vec![lit(64), u, lit(k)]);
                    let r = self.value(&r);
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
                    let tr = self.step("lea_bi", a, insn, &[&x[1], &b, &idx, &x[2], &x[3], &x[4], &lit(nb), &bv, &iv], self.tail(st, insn, 8, vec![]));
                    let r = self.mk("bits_add", vec![lit(64), iv, bv]);
                    let r = self.value(&r);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(tr, st2);
                }
                // lea r64, [b + d]: u + d (a negative d as GIMPLE writes it:
                // bits_neg(64, -d))
                if let (Some((2, b)), Some(d), Some(1)) = (m.get("base").and_then(|b| self.tag(b)), m.get("disp").and_then(nat), m.get("scale").and_then(nat)) {
                    let (nb, u) = self.reg(st, reg(&b)?).ok_or_else(|| bad("an empty base register"))?;
                    if nb != 8 {
                        return Err(bad("a base register not holding 64 bits"));
                    }
                    let dd = if d >= 1 << 63 { self.mk("bits_neg", vec![lit(64), lit(P64 - d)]) } else { lit(d) };
                    let tr = self.step("lea64_bd", a, insn, &[&x[1], &b, &lit(d), &dd, &x[2], &x[3], &x[4], &u], self.tail(st, insn, 7, vec![]));
                    let r = self.mk("bits_add", vec![lit(64), u, dd]);
                    let r = self.value(&r);
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
                            Spec::Proc(i) => self.qs[*i].clone(),
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
            // movzx r32, byte [b + i]: the spec's byte load at i + b
            79 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // movzx r32, r8 (h holding the byte b)
                if let Some((0, h)) = self.tag(&x[2]) {
                    let hn = reg(&h)?;
                    if x[3] != x[2] || hn >= 4 {
                        return Err(bad("not movzx r32, r8"));
                    }
                    let (n, b) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    // (a word, the spec masking it: u & 255)
                    let masked = self.mk("bits_and", vec![lit(32), b.clone(), lit(255)]);
                    if n > 1 && n <= 4 && matches!(self.canon(&masked).node(), Node::Var(..)) {
                        let r = self.canon(&masked);
                        let tr = self.step("movzx8_rrm", a, insn, &[&x[1], &h, &x[4], &lit(n), &b], self.tail(st, insn, 7, vec![]));
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
                    let tr = self.step("movzx8_rip", a, insn, &[&x[1], &lit(d), &x[4], &lit(biga)], self.tail(st, insn, 4, vec![simp_lw(vec![R::S(hc.clone())])]));
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({wn}, \"vm\"), {biga}, 1))"))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, v);
                    return self.then(tr, st2);
                }
                // movzx r32, byte [b + d] (b holding a pointer): the spec's field load
                if self.app(&m["index"], "none", 0).is_some() && nat(&m["disp"]) != Some(0) {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    // (defined for reading, or for the spec's store there)
                    let (hc, wr) = match self.mem_hyp(st, &bp, &d, 1) {
                        Ok(h) => (h, false),
                        Err(e) => match self.hyp_find(&st.hyps, &self.mem_defined(&st.w, &bp, &d, 1, true)) {
                            Some(h) => (h.1.clone(), true),
                            None => return Err(e),
                        },
                    };
                    let wt = self.mk(if wr { "true" } else { "false" }, vec![]);
                    let tr = self.step("movzx8_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &wt], self.tail(st, insn, 6, vec![s(&hc)]));
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 1))", self.print(&bp), self.print(&d)))?;
                    let v = self.value(&v);
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
                    let hc = self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()).ok_or_else(|| {
                        let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
                        format!("{:x}: a byte load at {} the spec does not load ({}; the facts: {})", a, self.print(&bv), self.print(&cond), facts.join(", "))
                    })?;
                    let tr = self.step("movzx8_b", a, insn, &[&x[1], &b, &x[4], &bv], self.tail(st, insn, 5, vec![taut(vec![R::S(hc.clone())])]));
                    let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                    let by = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, bv, lit(1)])]);
                    let by = self.value(&by);
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
                let ad = self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]);
                let ad = self.canon(&ad);
                let cond = self.ld8_cond(&ad);
                let hc = self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()).ok_or_else(|| {
                    let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
                    let vals: Vec<String> = self.vals.iter().map(|(v, tr)| format!("{} = {}", self.env.vars[*v as usize].name, self.print(tr))).collect();
                    format!("{:x}: a byte load at {} the spec does not load (the facts: {}; the values: {})", a, self.print(&ad), facts.join(", "), vals.join(", "))
                })?;
                let tr = self.step("movzx8_ld", a, insn, &[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv], self.tail(st, insn, 8, vec![taut(vec![R::S(hc.clone())])]));
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let by = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, ad, lit(1)])]);
                let by = self.value(&by);
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
                    let hc = self.mem_hyp(st, &bp, &d, 2)?;
                    let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 2))", self.print(&bp), self.print(&d)))?;
                    // (at d = 0: the spec's word at bp, if it has it)
                    let v0 = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), {}, 2))", self.print(&bp)))?;
                    let v = match self.canon(&v0).node() {
                        Node::Var(w0, _) if nat(&d) == Some(0) && self.vals.iter().any(|x| x.0 == *w0) => self.canon(&v0),
                        _ => self.value(&v),
                    };
                    let tr = self.step("movzx16_bd", a, insn, &[&x[1], &b, &d, &x[4], &bp, &v], self.tail(st, insn, 6, vec![s(&hc), simp_l()]));
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
                let ad = self.canon(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]));
                let hc = self.mem_hyp(st, &ad, &lit(0), 2)?;
                let tr = self.step("movzx16_ld", a, insn, &[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv], self.tail(st, insn, 8, vec![s(&hc)]));
                let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), {}, 2))", self.print(&ad)))?;
                let v = self.value(&v);
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
                    let tr = self.step("and16_ax", a, insn, &[&x[1], &lit(n), &u], self.tail(st, insn, 5, vec![]));
                    let r = self.mk("bits_and", vec![lit(16), u, x[1].clone()]);
                    let r = self.value(&r);
                    self.scratch.insert(0);
                    let st2 = self.set_reg(st, a2, 0, 2, r);
                    return self.then(tr, st2);
                }
                // and eax, imm32
                if nat(&x[0]) == Some(4) {
                    if let Some(pf) = self.widen(st, 0, 4)? {
                        return Ok(pf);
                    }
                    let u = self.need_reg(st, 0, 4)?;
                    let tr = self.step("and32_imm_ax", a, insn, &[&x[1], &u], self.tail(st, insn, 4, vec![]));
                    let r = self.mk("bits_and", vec![lit(32), u, x[1].clone()]);
                    let r = self.value(&r);
                    self.scratch.insert(0);
                    let st2 = self.set_reg(st, a2, 0, 4, r);
                    return self.then(tr, st2);
                }
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not and rax, imm32"));
                }
                let u = self.need_reg(st, 0, 8)?;
                let kk64 = if k >= 1 << 31 { k + 0xffff_ffff_0000_0000 } else { k };
                // (a negative immediate as GIMPLE writes it: bits_neg(64, -k))
                let kk = if kk64 >= 1 << 63 { self.mk("bits_neg", vec![lit(64), lit(P64 - kk64)]) } else { lit(kk64) };
                let tr = self.step("and64_imm", a, insn, &[&x[1], &kk, &u], self.tail(st, insn, 5, vec![]));
                let r = self.mk("bits_and", vec![lit(64), u, kk]);
                let r = self.value(&r);
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
                let tr = self.step("movsx8", a, insn, &[&x[1], &h, &x[4], &b], self.tail(st, insn, 6, vec![]));
                let r = self.mk("bits_sext", vec![lit(8), lit(32), b]);
                let r = self.value(&r);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(tr, st2)
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
                // (no result: rax:rdx anything)
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
                let mut r = self.ret_step("tr.ret_insn", a, insn, pr, vec![t(&lit(n)), t(val)], mpf(&format!("tr.result{}", 8 * n), vec![t(&st.w), t(val)]), st);
                if let (Some(q), R::Mp(_, args)) = (eqf, &mut r) {
                    // (rax's entry: the spec's value, by the equation)
                    let i = args.len() - 2;
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
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]));
                    ("store8i_bi", vec![b.clone(), i.clone(), k.clone(), lit(nb), bv, iv], 9, ad)
                };
                let (hc, v, st2, red, sa) = self.spec_store(st, &ad, 1)?;
                if self.eval_lit(&v) != nat(&k) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&k), self.print(&v)));
                }
                let _ = &sa;
                let tr: Vec<&Term> = terms.iter().collect();
                let tr = self.step(rule, a, insn, &tr, self.tail_s(st, &st2, insn, n, vec![], &hc, &red));
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
                if gk != 0 || gn >= 4 {
                    return Err(bad("not mov byte [m], r8"));
                }
                let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                // (the address: a static's, or b + i; the rule's terms and
                // its literal facts' count)
                let (rule, terms, nlit, ad) = if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    ("store8_rip", vec![g.clone(), lit(d), x[0].clone(), x[1].clone(), lit(n), u.clone()], 8, biga)
                } else if bk == 2 && self.app(&m["index"], "some", 1).is_none() && nat(&m["disp"]) == Some(0) {
                    // [b]: the address b's value
                    let bv = self.need_reg(st, reg(&b)?, 8)?;
                    ("store8_b", vec![g.clone(), b.clone(), x[0].clone(), x[1].clone(), bv.clone(), lit(n), u.clone()], 10, bv)
                } else if bk == 2 && self.app(&m["index"], "some", 1).is_none() {
                    // [b + d]: b's value + d
                    let d = m["disp"].clone();
                    let bv = self.need_reg(st, reg(&b)?, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                    ("store8_bd", vec![g.clone(), b.clone(), d, x[0].clone(), x[1].clone(), bv, lit(n), u.clone()], 11, ad)
                } else {
                    let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                    if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&i)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]));
                    ("store8_bi", vec![g.clone(), b.clone(), i.clone(), x[0].clone(), x[1].clone(), lit(nb), bv, iv, lit(n), u.clone()], 12, ad)
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
                let lp = if let Some((_, _, k, fv)) = &so.bf {
                    self.bf_merge(st, &w0, &sa, k, fv, &u)?
                } else {
                    match low8 {
                    Some((bb, kk, kk2)) if self.eval_lit(&kk).is_some() && self.eval_lit(&kk) == self.eval_lit(&kk2) => {
                        p(mpf("tr.low8_add", vec![t(&bb), t(&kk), simp_l(), simp_l()]))
                    }
                    Some((bb, kk, kk2)) => p(mpf("tr.low8_add_mod", vec![t(&bb), t(&kk), t(&kk2), simp_l(), simp_l(), simp_l(), simp_l()])),
                    // (else: the low byte of a sum of words, shifts, bytes --
                    // their arithmetic modulo 2^8, the words' definitions)
                    None => RA::P(RP::Defs(Box::new(RP::Simp(true, vec![], vec![], false)), ["bits_slice", "bits_add", "bits_shl", "bits_mul", "bits_of_int"].iter().map(|x| x.to_string()).collect())),
                    }
                };
                let _ = &sa;
                let mut terms: Vec<&Term> = terms.iter().collect();
                terms.push(&v);
                if rule == "store8_rip" {
                    terms.push(&ad);
                }
                let tr = self.step(rule, a, insn, &terms, self.tail_s(st, &st2, insn, nlit, vec![lp], &hc, &red));
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
                // mov r64, simm32: the constant as GIMPLE writes it (a
                // negative one bits[64](-k): bits_of_int(64, int_neg(k)))
                if let (Some(8), Some((0, g))) = (nat(&x[0]), self.tag(&x[1])) {
                    let gn = reg(&g)?;
                    let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    let kk = if k >= 1 << 31 { self.mk("bits_of_int", vec![lit(64), self.mk("int_neg", vec![lit((1 << 32) - k)])]) } else { lit(k) };
                    let tr = self.step("mov64_simm", a, insn, &[&g, &x[2], &x[3], &kk], self.tail(st, insn, 4, vec![]));
                    let kk = self.value(&kk);
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 8, kk);
                    return self.then(tr, st2);
                }
                let d = self.rsp_mem(&x[1]).ok_or_else(|| bad("not a home"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                if nat(&x[0]) != Some(4) || x[2] != x[1] {
                    return Err(bad("not mov dword [rsp + d], imm32"));
                }
                let cn = self.hkey(dn);
                let (_, hs2, hk) = self.hkeep(st, cn, 4);
                let k = x[3].clone();
                let tr = self.step("store32i_home", a, insn, &[&d, &lit(cn), &k], self.tail_h(st, insn, &hs2, 4, vec![defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]), simp_l(), simp_l(), simp_l(), simp_l(), p(hk.clone())]));
                let st2 = self.set_home(st, a2, cn, 4, k);
                self.then(tr, st2)
            }
            _ => {
                self.trace(|| {
                    let hyps: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
                    let vals: Vec<String> = self.vals.iter().map(|(v, tr)| format!("{} := {}", self.env.vars[*v as usize].name, self.print(tr))).collect();
                    format!("no rule at {:x}: facts {}; values {}", a, hyps.join(", "), vals.join(", "))
                });
                Err(bad("no rule for the instruction"))
            }
        }
    }

    /// A bitfield store's byte (k bits at bit 0, the field fv; at a in w):
    /// the register u's low byte is GIMPLE's value -- bit by bit (`bitwise`)
    /// against the bytes' cleared word as a multiple of 2^k plus the field
    /// (tr.bf0_val, its facts tr.bf0_facts)
    fn bf_merge(&mut self, st: &St, w: &Term, a: &Term, k: &Term, fv: &Term, u: &Term) -> Result<RA, String> {
        let pk = self.mk("pow2", vec![k.clone()]);
        let vm = self.mk("app", vec![w.clone(), Term::bytes(b"vm")]);
        let old = self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(1)]);
        let mask = self.mk("bits_not", vec![lit(128), self.mk("int_sub", vec![pk.clone(), lit(1)])]);
        let cleared = self.mk("bits_and", vec![lit(128), self.mk("bits_of_int", vec![lit(128), old]), mask]);
        let hi = self.mk("int_mul", vec![self.mk("int_div", vec![cleared, pk.clone()]), pk.clone()]);
        // (the field as the machine has it: under its masks in u -- its
        // bits the spec's, by arith modulo 2^k)
        let fm = self.bf_field(&self.expand(u), k).unwrap_or_else(|| fv.clone());
        let mk_mod = |g: &Gen, x: &Term| g.mk("int_mod", vec![x.clone(), g.mk("pow2", vec![k.clone()])]);
        let hm = self.evp(
            &RP::Defs(Box::new(RP::Arith(vec![])), ["bits_add", "bits_of_int", "bits_neg", "pow2"].iter().map(|x| x.to_string()).collect()),
            &self.mk("eq", vec![mk_mod(self, fv), mk_mod(self, &fm)]),
            &[],
        )?;
        let field = self.mk("int_mul", vec![self.mk("int_mod", vec![fm.clone(), pk]), lit(1)]);
        let low = self.mk("bits_slice", vec![u.clone(), lit(7), lit(0)]);
        let rhs = self.mk("int_add", vec![hi, field]);
        let facts = self.run(&mpf("tr.bf0_facts", vec![t(w), t(a), t(k), taut(vec![R::S(st.hw.clone())]), simp_l(), simp_l(), simp_l()]), &[])?;
        // (the low byte as an 8-bit word of u)
        let omega = self.mk("omega", vec![]);
        let uo = self.evp(&RP::Simp(true, vec![], vec![], false), &self.mk("in", vec![u.clone(), omega]), &[])?;
        let b8 = self.mk("bits_of_int", vec![lit(8), u.clone()]);
        let sl = self.evp(&RP::Defs(Box::new(RP::Simp(true, vec![R::S(uo.clone())], vec![], false)), vec!["bits_slice".into(), "bits_of_int".into()]), &self.mk("eq", vec![low.clone(), b8.clone()]), &[])?;
        let fo = self.evp(&RP::Simp(true, vec![], vec![], false), &self.mk("in", vec![fm.clone(), self.mk("omega", vec![])]), &[])?;
        let m0 = self.evp(&RP::Bitwise(vec![R::S(facts), R::S(uo), R::S(fo)], 8), &self.mk("eq", vec![b8, rhs.clone()]), &[])?;
        let m = self.evp(&RP::Arith(vec![R::S(sl), R::S(m0)]), &self.mk("eq", vec![low.clone(), rhs]), &[])?;
        Ok(p(mpf("tr.bf0_val", vec![t(w), t(a), t(fv), t(&fm), t(k), t(&low), taut(vec![R::S(st.hw.clone())]), simp_l(), simp_l(), simp_l(), s(&hm), s(&m)])))
    }

    /// a merge's field: an operand of its `or` under `and`s with 2^k - 1
    fn bf_field(&self, u: &Term, k: &Term) -> Option<Term> {
        let mask = (1u128 << nat(k)?) - 1;
        let o = self.app(u, "bits_or", 3)?.to_vec();
        for x in [&o[2], &o[1]] {
            let mut cur = x.clone();
            let mut n = 0;
            while let Some(y) = self.app(&cur, "bits_and", 3).map(|y| y.to_vec()) {
                if nat(&y[2]) != Some(mask) {
                    break;
                }
                cur = y[1].clone();
                n += 1;
            }
            if n > 0 {
                return Some(cur);
            }
        }
        None
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

    /// a return's rule: `mp(RULE, s, V, base, code, a, len, hs, ds, rs, pr, w, ts.., decode, [simp(L), simp(L)], result)`
    fn ret_step(&self, rule: &str, a: u128, insn: &Insn, pr: &Term, ts: Vec<RA>, res: R, st: &St) -> R {
        let mut v = vec![t(&self.s), t(&self.v), t(&self.base), t(&self.code), t(&lit(a)), t(&lit(insn.len)), t(&st.hst), t(&st.ds), t(&st.rs), t(pr), t(&st.w)];
        let has = !ts.is_empty();
        v.extend(ts);
        v.push(p(R::F(insn.name.clone())));
        if has {
            v.push(simp_l());
            v.push(simp_l());
        }
        v.push(p(res));
        mpf(rule, v)
    }

    /// a store's tail (the spec's store made at it): the maps, the specs
    /// before and after, the worlds, the decode fact, n literal facts, the
    /// extra premises, its definedness, the world after, the reduction, the
    /// next point
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
