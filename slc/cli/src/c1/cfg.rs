//! C1 by GIMPLE's control-flow graph (`slc gimple --readable --cfg`,
//! proofs/translate_cfg.core): the claim at each basic block's entry (a
//! cut point), for every world and locals, from each block walked once up
//! to the cut point it goes on at (`tr.cfg_lvk`).
//!
//! The readable CFG is `var bb = entry; loop { .. }`, the locals y =
//! pair(bb, ys). The cut points are known from the code alone (its blocks'
//! first instructions -- jump targets, the instructions after jumps --, the
//! body's first after the prologue; not the epilogue nor a lone `jmp`), so
//! that every other point is shown no breakpoint. Which cut point is which
//! label's (`ad(c) = app(AD, c)`) is found as the walks arrive: the first
//! arrival at a label assumes `app(AD, c) = a`, every later one must be at
//! a; at the end AD is the table found. The homes at a label: the live
//! locals' (the generator's `F_cfg_live`, by the location map) and the
//! parameters' (as at the body's start).

use super::rec::*;
use super::*;

/// A function's CFG walk.
pub(super) struct Cfg {
    /// the labels (GCC's block numbers) in kk's order, each with its live
    /// locals (a bit per position in ys)
    labels: Vec<(u128, u128)>,
    widths: Vec<u64>,
    /// each local's homes (the location map: key, the scope's addresses;
    /// several -- C variables of one name in other scopes -- the one whose
    /// scope has the label's address)
    lent: Vec<Vec<(u128, u128, u128)>>,
    /// the cut points' addresses
    pub(super) cuts: BTreeSet<u128>,
    /// AD, the labels' addresses found, their equations' assumptions
    ad: Term,
    addr: BTreeMap<u128, u128>,
    hyp: BTreeMap<u128, (Term, Seq)>,
    todo: Vec<u128>,
    /// the rule's parameters
    hs_lam: Term,
    yt_lam: Term,
    ct_lam: Term,
    kk_lam: Term,
    /// the function's breakpoints and arrival (outside the walks)
    bkp0: Term,
    /// the rule's premise per label (`c. all ys w. ..`), its claims made
    body: Term,
    done: BTreeMap<u128, Seq>,
    /// the per-label walks' breakpoints and arrival
    bkp2: Term,
    bka2: Term,
    /// the homes kept at every label (the parameters'), the frame, its depth
    fixed: BTreeMap<u128, (u128, Term)>,
    fr: u128,
    fd: Term,
    /// the registers at every label: the callee-saved ones at their entry
    /// values, not saved in a home (Gen::cs_fixed)
    rc: Vec<(u128, u128, Term)>,
    /// each local's register, if it lives in one (a hand-written CFG's);
    /// the registers at a label as a function of the locals (the rule's
    /// rc: rc's and the live locals'), whether that is rc's at every label
    rreg: Vec<Option<u128>>,
    rc_lam: Term,
    rc_const: bool,
    /// the facts every block has (the body's start's, on fixed values)
    hyps: Vec<(Term, Seq)>,
    facts: Vec<Seq>,
    lfx: Vec<Seq>,
    /// the loop's body, rest, the wrapper's continuation (the function's)
    b: Term,
    kl: Term,
    kw: Term,
    wrap: Term,
}

impl<'e> Gen<'e> {
    /// the body's first instruction: after the prologue (the callee-saved
    /// registers pushed, `sub rsp, k`, the argument registers stored to
    /// their homes)
    pub(super) fn cfg_body_start(&self, entry: u128) -> u128 {
        let mut a = entry;
        while let Some(i) = self.insns.get(&a) {
            let x = self.pairs(&i.fields, 5);
            let rsp_reg = |t: &Term| self.tag(t).is_some_and(|(k, r)| k == 0 && nat(&r) == Some(4));
            let sub_rsp = matches!(i.row, 59 | 60) && x.as_ref().is_some_and(|x| nat(&x[1]) == Some(5) && rsp_reg(&x[2]));
            let arg_store = i.row == 75 && x.as_ref().is_some_and(|x| self.rsp_mem(&x[2]).is_some() && nat(&x[1]).is_some_and(|g| [7, 6, 2, 1, 8, 9].contains(&g)));
            let push_cs = i.row == 114 && nat(&i.fields).is_some_and(|g| CS_REGS.contains(&g));
            if !sub_rsp && !arg_store && !push_cs {
                break;
            }
            a = (a + i.len) % P64;
        }
        a
    }

    /// the cut points: the code's blocks' first instructions (jump targets,
    /// those after jumps and returns), the body's start; not the epilogue,
    /// nor a lone `jmp` (a block of GIMPLE's with no code of its own)
    fn cfg_cuts(&mut self, start: u128) -> BTreeSet<u128> {
        let mut cuts = BTreeSet::from([start]);
        let addrs: Vec<u128> = self.insns.keys().copied().collect();
        for a in addrs {
            let i = &self.insns[&a];
            let next = (a + i.len) % P64;
            match i.row {
                124 | 125 => {
                    cuts.extend(self.succs(a));
                    cuts.insert(next);
                }
                127 | 128 => cuts.extend(self.succs(a)),
                122 => {
                    cuts.insert(next);
                }
                _ => {}
            }
        }
        let epi = self.cfg_epilogue();
        // (nor a `nop` before a lone `jmp`: the same)
        let lone_jmp = |g: &Self, a: &u128| g.insns.get(a).is_some_and(|i| matches!(i.row, 124 | 125));
        let nop_jmp = |g: &Self, a: &u128| g.insns.get(a).is_some_and(|i| i.row == 109 && lone_jmp(g, &((a + i.len) % P64)));
        cuts.retain(|a| self.insns.get(a).is_some() && !lone_jmp(self, a) && !nop_jmp(self, a) && !epi.contains(a));
        cuts.insert(start);
        cuts
    }

    /// the epilogue (not cut points): the code from which every way runs
    /// to a `ret` by the frame's code (`nop`, `add rsp, k`, the callee-saved
    /// registers popped), jumps, and the result set (rax loaded from a home,
    /// or an immediate): a `return`'s code, shared by the ways that return
    fn cfg_epilogue(&mut self) -> BTreeSet<u128> {
        let tail = |g: &Gen, a: u128| {
            let Some(i) = g.insns.get(&a) else { return false };
            let x = g.pairs(&i.fields, 5);
            let rsp = || x.as_ref().and_then(|x| g.tag(&x[2])).is_some_and(|(k, r)| k == 0 && nat(&r) == Some(4));
            let ld_rax = || i.row == 76 && x.as_ref().is_some_and(|x| nat(&x[1]) == Some(0) && g.rsp_mem(&x[2]).is_some());
            let imm_rax = || matches!(i.row, 111 | 112) && g.pairs(&i.fields, 2).is_some_and(|x| nat(&x[0]) == Some(0));
            let pop_cs = || i.row == 115 && nat(&i.fields).is_some_and(|g| CS_REGS.contains(&g));
            matches!(i.row, 109 | 122 | 124 | 125) || (matches!(i.row, 59 | 60) && rsp()) || ld_rax() || imm_rax() || pop_cs()
        };
        let addrs: Vec<u128> = self.insns.keys().copied().collect();
        let mut out: BTreeSet<u128> = addrs.iter().copied().filter(|a| self.insns[a].row == 122).collect();
        // (the stack protector's check: the canary's word from its home,
        // `sub r64, fs:[0x28]`, the `je` past `call __stack_chk_fail`)
        let mut canary = BTreeSet::new();
        for &a in &addrs {
            let i = &self.insns[&a];
            let fs40 = i.row == 51 && self.pairs(&i.fields, 5).and_then(|x| self.memop(&x[2])).is_some_and(|m| nat(&m["seg"]) == Some(2) && nat(&m["disp"]) == Some(40));
            if !fs40 {
                continue;
            }
            canary.insert(a);
            if let Some(&p) = addrs.iter().find(|&&p| (p + self.insns[&p].len) % P64 == a && self.insns[&p].row == 76) {
                canary.insert(p);
            }
            let j = (a + i.len) % P64;
            if self.insns.get(&j).is_some_and(|x| matches!(x.row, 127 | 128)) {
                canary.insert(j);
                let k = (j + self.insns[&j].len) % P64;
                if self.insns.get(&k).is_some_and(|x| x.row == 120) {
                    canary.insert(k);
                }
            }
        }
        loop {
            let more: Vec<u128> = addrs
                .iter()
                .copied()
                .filter(|&p| {
                    let s = self.succs(p);
                    !out.contains(&p) && ((tail(self, p) && s.len() == 1 && out.contains(&s[0])) || (canary.contains(&p) && !s.is_empty() && s.iter().all(|x| out.contains(x))))
                })
                .collect();
            if more.is_empty() {
                break;
            }
            out.extend(more);
        }
        out
    }

    /// local j of the locals ys (m of them): its projection
    pub(super) fn cfg_proj(&self, ys: &Term, j: usize, m: usize) -> Term {
        // (a pair's parts taken: `fst(pair(a, b))` is a)
        let part = |t: &Term, i: usize, nm: &str| self.app(t, "pair", 2).map(|x| x[i].clone()).unwrap_or_else(|| self.mk(nm, vec![t.clone()]));
        let mut t = ys.clone();
        for _ in 0..j {
            t = part(&t, 1, "snd");
        }
        if j + 1 < m { part(&t, 0, "fst") } else { t }
    }

    /// the homes at a label at address a (its live locals, mask) of the
    /// locals ys: the fixed ones and each live local's (a local of one
    /// home first, by key; then those of several, the scope's at a), as a
    /// map and its term in that order
    fn cfg_homes(&self, c: &Cfg, mask: u128, ys: &Term, a: u128) -> Result<(BTreeMap<u128, (u128, Term)>, Term), String> {
        let m = c.widths.len();
        let mut one = c.fixed.clone();
        let mut several = Vec::new();
        for j in 0..m {
            if mask & (1u128 << j) == 0 || c.rreg[j].is_some() {
                continue;
            }
            let es = &c.lent[j];
            let nb = (c.widths[j] / 8) as u128;
            let v = self.cfg_proj(ys, j, m);
            match es.len() {
                0 => return Err(format!("local {} lives at a block's entry with no home (a register's value)", j)),
                1 => {
                    one.insert(es[0].0, (nb, v));
                }
                _ => {
                    let key = es.iter().find(|e| e.1 <= a && a < e.2).unwrap_or(es.last().unwrap()).0;
                    several.push((key, nb, v));
                }
            }
        }
        let mut term = self.hs_term(&one);
        let mut map = one;
        for (key, nb, v) in several {
            term = self.upd(&term, key, nb, &v);
            map.insert(key, (nb, v));
        }
        Ok((map, term))
    }

    /// ... the rule's: a local of several homes at the one whose scope has
    /// `ad` (the label's address, a term)
    fn cfg_homes_t(&self, c: &Cfg, mask: u128, ys: &Term, ad: &Term) -> Result<Term, String> {
        let m = c.widths.len();
        let mut one = c.fixed.clone();
        let mut several = Vec::new();
        for j in 0..m {
            if mask & (1u128 << j) == 0 || c.rreg[j].is_some() {
                continue;
            }
            let es = &c.lent[j];
            let nb = (c.widths[j] / 8) as u128;
            let v = self.cfg_proj(ys, j, m);
            match es.len() {
                0 => return Err(format!("local {} lives at a block's entry with no home (a register's value)", j)),
                1 => {
                    one.insert(es[0].0, (nb, v));
                }
                _ => {
                    let mut key = lit(es.last().unwrap().0);
                    for e in es[..es.len() - 1].iter().rev() {
                        let inside = self.mk("and", vec![self.mk("int_le", vec![lit(e.1), ad.clone()]), self.mk("int_lt", vec![ad.clone(), lit(e.2)])]);
                        key = self.mk("ite", vec![inside, lit(e.0), key]);
                    }
                    several.push((key, nb, v));
                }
            }
        }
        let mut term = self.hs_term(&one);
        for (key, nb, v) in several {
            term = self.mk("fn_update", vec![term, key, self.mk("pair", vec![lit(nb), v])]);
        }
        Ok(term)
    }

    /// the registers at a label (its live locals, mask) of the locals ys:
    /// rc's, then each live local's living in one (register, bytes, value)
    fn cfg_rc(&self, c: &Cfg, mask: u128, ys: &Term) -> Vec<(u128, u128, Term)> {
        let m = c.widths.len();
        let mut out = c.rc.clone();
        for j in 0..m {
            if let (true, Some(r)) = (mask & (1u128 << j) != 0, c.rreg[j]) {
                out.push((r, (c.widths[j] / 8) as u128, self.cfg_proj(ys, j, m)));
            }
        }
        out
    }

    /// `tr.rsub(rc, rs)`, rc the map of es (each rs's entry)
    fn rsub_pf(&self, es: &[(u128, u128, Term)], rs: &Term) -> R {
        let mut pf = R::Inst("tr.rsub_empty".into(), vec![("rs", rs.clone())]);
        let mut rc = self.mk("empty", vec![]);
        for (r, n, v) in es {
            pf = mpf("tr.rsub_add", vec![t(&rc), t(rs), t(&lit(*r)), t(&lit(*n)), t(v), p(pf), simp_l(), simp_l()]);
            rc = self.upd(&rc, *r, *n, v);
        }
        pf
    }

    /// `x in bits(w)` for each live local of ys
    fn cfg_widths(&self, c: &Cfg, mask: u128, ys: &Term) -> Vec<Term> {
        let m = c.widths.len();
        (0..m).filter(|j| mask & (1u128 << j) != 0).map(|j| self.mk("in", vec![self.cfg_proj(ys, j, m), self.mk("bits", vec![lit(c.widths[j] as u128)])])).collect()
    }

    fn or_chain(&self, ts: Vec<Term>) -> Term {
        ts.into_iter().rev().fold(self.mk("false", vec![]), |acc, t| self.mk("or", vec![t, acc]))
    }

    fn and_all(&self, ts: Vec<Term>) -> Term {
        ts.into_iter().reduce(|a, b| self.mk("and", vec![a, b])).unwrap_or_else(|| self.mk("true", vec![]))
    }

    /// premises `p1 -> p2 -> .. -> c` as [p1, ..], c
    pub(super) fn imps(&self, t: &Term) -> (Vec<Term>, Term) {
        let imp = self.env.builtins.imp;
        let mut ps = Vec::new();
        let mut t = t.clone();
        while let Node::App(s, a) = t.node() {
            if *s != imp {
                break;
            }
            ps.push(a[0].clone());
            t = a[1].clone();
        }
        (ps, t)
    }

    /// The function's CFG at the body's start (st, the spec at its loop):
    /// the claim there by tr.cfg_lvk -- each label walked once
    /// (`start`: entered within the first label's block -- after its stack
    /// object's allocation --, its rest walked from st, tr.cfg_lvk_st)
    pub(super) fn cfg_function(&mut self, st: &St, qi: usize, start: bool) -> Result<Seq, String> {
        let (live, _) = self.cfg_meta.clone().ok_or("the CFG: no live locals")?;
        let all: BTreeSet<u128> = live.iter().map(|x| x.0).collect();
        match self.cfg_labels(st, qi, &all, start)? {
            Ok(pf) => Ok(pf),
            // (labels no walk reached -- the compiler's code has none, a
            // constant condition decided: the claim by the others)
            Err(reached) => {
                self.trace(|| format!("cfg at {:x}: labels not reached: {:?}, again without them", st.a, all.difference(&reached).collect::<Vec<_>>()));
                self.cfg_labels(st, qi, &reached, start)?.map_err(|_| format!("{:x}: the CFG: labels not reached again", st.a))
            }
        }
    }

    /// ... by the labels `only`: the claim, or the labels the walks reached
    /// (fewer than `only`)
    fn cfg_labels(&mut self, st: &St, qi: usize, only: &BTreeSet<u128>, start: bool) -> Result<Result<Seq, BTreeSet<u128>>, String> {
        let bad = |m: &str| format!("{:x}: the CFG: {}", st.a, m);
        let (live, widths) = self.cfg_meta.clone().ok_or_else(|| bad("no live locals"))?;
        let live: Vec<(u128, u128)> = live.into_iter().filter(|x| only.contains(&x.0)).collect();
        let q = self.qs[qi].clone();
        let body = self.app(&q, "mkprog", 1).ok_or_else(|| bad("rest"))?[0].clone();
        let y = self.app(&self.app(&body, "ex", 1).ok_or_else(|| bad("not its loop"))?[0], "and", 2).ok_or_else(|| bad("not its loop"))?.to_vec();
        let ctx = ["x0", "x1", "x8"];
        let al = self.lam(&y[0], &ctx, &["x0", "x8"]).ok_or_else(|| bad("its loop reads the outcome"))?;
        let kl = self.lam(&y[1], &ctx, &["x8", "x1"]).ok_or_else(|| bad("its rest reads the world"))?;
        let wr = self.app(&al, "while_rel", 5).ok_or_else(|| bad("not a while"))?.to_vec();
        let l0 = self.app(&wr[0], "pair", 2).ok_or_else(|| bad("its state not the world and the locals"))?.to_vec();
        let y0 = self.app(&l0[1], "pair", 2).ok_or_else(|| bad("its locals not a label and the rest"))?.to_vec();
        let k_e = nat(&y0[0]).ok_or_else(|| bad("the first label not a literal"))?;
        let ys0 = y0[1].clone();
        // (started within the first label's block: that label's claim the
        // start's, not one at its address)
        let live: Vec<(u128, u128)> = if start { live.into_iter().filter(|x| x.0 != k_e).collect() } else { live };
        let mask_e0 = self.cfg_meta.as_ref().and_then(|(l, _)| l.iter().find(|x| x.0 == k_e).map(|x| x.1)).ok_or_else(|| bad("the first label not among the labels"))?;
        let m = widths.len();
        let cuts = self.cfg_cuts(st.a);
        // the locals' homes (the location map: of one key, or several by scope)
        let lent: Vec<Vec<(u128, u128, u128)>> = (0..m)
            .map(|j| {
                // (the innermost scope first: nested scopes' variables of a name)
                let mut es: Vec<(u128, u128, u128)> = self.locmap.iter().filter(|e| e.0 == j).map(|e| (e.1, e.2, e.3)).collect();
                es.sort_by_key(|e| e.2 - e.1);
                let ks: BTreeSet<u128> = es.iter().map(|e| e.0).collect();
                if ks.len() == 1 { vec![es[0]] } else { es }
            })
            .collect();
        // the fixed homes: the body's start's not of a local
        let local_keys: BTreeSet<u128> = self.locmap.iter().filter(|e| e.0 < m).map(|e| e.1).collect();
        let fixed: BTreeMap<u128, (u128, Term)> = st.hsm.iter().filter(|(k, _)| !local_keys.contains(k)).map(|(k, v)| (*k, v.clone())).collect();
        self.trace(|| format!("cfg at {:x}: {} labels, cut points {}", st.a, live.len(), cuts.iter().map(|a| format!("{:x}", a)).collect::<Vec<_>>().join(" ")));
        let n = self.fresh("");
        let ad = self.var(&format!("AD{n}"));
        // the rule's parameters, as functions of y (a label c, an address a)
        let yv = self.var(&format!("cfy{n}"));
        let cv = self.var(&format!("cfc{n}"));
        let av = self.var(&format!("cfa{n}"));
        let ysv = self.mk("snd", vec![yv.clone()]);
        let fy = self.mk("fst", vec![yv.clone()]);
        let mut c = Cfg {
            labels: live.clone(),
            widths: widths.clone(),
            lent,
            cuts: cuts.clone(),
            ad: ad.clone(),
            addr: BTreeMap::new(),
            hyp: BTreeMap::new(),
            todo: Vec::new(),
            hs_lam: Term::bvar(0),
            yt_lam: Term::bvar(0),
            ct_lam: Term::bvar(0),
            kk_lam: Term::bvar(0),
            bkp0: self.bkp.clone(),
            body: Term::bvar(0),
            done: BTreeMap::new(),
            bkp2: Term::bvar(0),
            bka2: Term::bvar(0),
            fixed,
            fr: st.fr,
            fd: st.ds.clone(),
            rc: self.cs_fixed(st),
            rreg: (0..m).map(|j| self.cfg_regs.iter().find(|x| x.0 == j).map(|x| x.1)).collect(),
            rc_lam: Term::bvar(0),
            rc_const: true,
            hyps: Vec::new(),
            facts: Vec::new(),
            lfx: Vec::new(),
            b: wr[2].clone(),
            kl: kl.clone(),
            kw: self.kw.clone(),
            wrap: self.wrap.clone(),
        };
        let mut hs_t = self.mk("empty", vec![]);
        for &(k, mask) in live.iter().rev() {
            let adk = self.mk("app", vec![ad.clone(), lit(k)]);
            let h = self.cfg_homes_t(&c, mask, &ysv, &adk)?;
            hs_t = self.mk("ite", vec![self.mk("eq", vec![fy.clone(), lit(k)]), h, hs_t]);
        }
        let yts: Vec<Term> = live.iter().map(|&(k, mask)| self.mk("and", vec![self.mk("eq", vec![fy.clone(), lit(k)]), self.and_all(self.cfg_widths(&c, mask, &ysv))])).collect();
        let yt_t = self.or_chain(yts);
        let kk_t = self.or_chain(live.iter().map(|&(k, _)| self.mk("eq", vec![cv.clone(), lit(k)])).collect());
        let ct_t = self.or_chain(cuts.iter().map(|&a| self.mk("eq", vec![av.clone(), lit(a)])).collect());
        let ad_t = self.mk("app", vec![ad.clone(), cv.clone()]);
        // (the registers: rc's at every label, or by label with its live
        // locals' in registers)
        c.rc_const = !live.iter().any(|&(_, mask)| (0..m).any(|j| mask & (1u128 << j) != 0 && c.rreg[j].is_some()));
        let rc_t = if c.rc_const {
            self.regs_map(&c.rc)
        } else {
            let mut acc = self.mk("empty", vec![]);
            for &(k, mask) in live.iter().rev() {
                let r = self.regs_map(&self.cfg_rc(&c, mask, &ysv));
                acc = self.mk("ite", vec![self.mk("eq", vec![fy.clone(), lit(k)]), r, acc]);
            }
            acc
        };
        c.rc_lam = self.abs(&rc_t, &[Self::var_id(&yv)]);
        c.hs_lam = self.abs(&hs_t, &[Self::var_id(&yv)]);
        c.yt_lam = self.abs(&yt_t, &[Self::var_id(&yv)]);
        c.ct_lam = self.abs(&ct_t, &[Self::var_id(&av)]);
        let kk_lam = self.abs(&kk_t, &[Self::var_id(&cv)]);
        c.kk_lam = kk_lam.clone();
        let ad_lam = self.abs(&ad_t, &[Self::var_id(&cv)]);
        let mut rargs: Vec<(&'static str, Term)> = Vec::new();
        if start {
            rargs.extend([("a0", lit(st.a)), ("hs0", st.hst.clone()), ("rs0", st.rs.clone())]);
        }
        let mut iargs: Vec<(&'static str, Term)> = vec![
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("fd", st.ds.clone()),
                ("rc", c.rc_lam.clone()),
                ("ct", c.ct_lam.clone()),
                ("ad", ad_lam),
                ("hs", c.hs_lam.clone()),
                ("yt", c.yt_lam.clone()),
                ("kk", kk_lam),
                ("bkp", self.bkp.clone()),
                ("bka", self.bka.clone()),
                ("b", wr[2].clone()),
                ("tr", wr[3].clone()),
                ("k", kl.clone()),
                ("kw", self.kw.clone()),
        ];
        iargs.extend(rargs);
        let (lr, stmt) = self.inst(if start { "tr.cfg_lvk_st" } else { "tr.cfg_lvk" }, &iargs)?;
        let (prems, _) = self.imps(&stmt);
        if prems.len() != if start { 7 } else { 5 } {
            return Err(bad("tr.cfg_lvk's premises"));
        }
        // the premise per label: all c. kk(c) -> P(c); P's claim's breakpoints
        let under = |g: &Gen, t: &Term| -> Option<Term> {
            let a = g.app(t, "all", 1)?[0].clone();
            let (_, r) = g.imps(&a);
            Some(r)
        };
        c.body = under(self, &prems[4]).ok_or_else(|| bad("its premise per label"))?;
        let lv_b = (|| {
            let a1 = self.app(&c.body, "all", 1)?[0].clone();
            let a2 = self.app(&a1, "all", 1)?[0].clone();
            let (_, lv) = self.imps(&a2);
            self.app(&lv, "tr.lv", 13).map(|x| x.to_vec())
        })()
        .ok_or_else(|| bad("its claim per label"))?;
        c.bkp2 = lv_b[1].clone();
        c.bka2 = lv_b[2].clone();
        // (the facts every block has: the body start's on fixed values)
        let (hyps, facts, lfx) = self.shared_facts(st, &ys0, &[], &[]);
        c.hyps = hyps;
        c.facts = facts;
        c.lfx = lfx;
        // the first label at the body's start (or its rest from st: the
        // start's walk, the labels its arrivals find); each label walked once
        let y0t = self.mk("pair", vec![lit(k_e), ys0.clone()]);
        let mut wf = vec![R::S(st.hvu.clone())];
        wf.extend(st.facts.iter().map(|f| R::S(f.clone())));
        let start_h = if start {
            let hu_t = self.mk("in", vec![self.mk("pair", vec![st.w.clone(), y0t.clone()]), self.mk("univ", vec![lit(1)])]);
            let hu = self.evp(&RP::Simp(true, vec![R::S(st.hvu.clone())], vec![], false), &hu_t, &[])?;
            let hy_t = self.and_all(self.cfg_widths(&c, mask_e0, &ys0));
            let hy = self.evp(&RP::Simp(true, wf.clone(), vec![], false), &hy_t, &[])?;
            Some((hu, hy))
        } else {
            let h0 = self.mk("eq", vec![self.mk("app", vec![ad.clone(), lit(k_e)]), lit(st.a)]);
            let hs0 = self.assume(&h0)?;
            c.addr.insert(k_e, st.a);
            c.hyp.insert(k_e, (h0, hs0));
            c.todo.push(k_e);
            None
        };
        let outer = (self.bkp.clone(), self.bka.clone(), self.wrap.clone(), self.kw.clone(), self.lpg.take());
        self.cfg = Some(c);
        let sw = match &start_h {
            Some((hu, hy)) => Some(self.cfg_start_walk(st, &y0t, hu.clone(), hy.clone())),
            None => None,
        };
        let res = self.cfg_walks();
        let c = self.cfg.take().expect("the CFG walk");
        self.bkp = outer.0;
        self.bka = outer.1;
        self.wrap = outer.2;
        self.kw = outer.3;
        self.lpg = outer.4;
        let sw = sw.transpose()?;
        res?;
        let reached: BTreeSet<u128> = c.done.keys().copied().collect();
        if reached.len() < c.labels.len() {
            return Ok(Err(reached));
        }
        self.fr = st.fr;
        self.w = st.w.clone();
        self.hvu = Some(st.hvu.clone());
        self.hww = Some(st.hw.clone());
        self.set_lf(st)?;
        // the labels' claims gathered (the last first), the cut points'
        // premise likewise
        let gather = |g: &mut Gen, body: &Term, each: &dyn Fn(&mut Gen, u128, &Term) -> Result<Seq, String>| -> Result<Seq, String> {
            let lam = body.clone();
            let mut acc = g.ev(&R::Inst("tr.cfg_kk_nil".into(), vec![("P", lam.clone())]), &[])?;
            let mut kk_cur = g.mk("false", vec![]);
            for &(k, _) in c.labels.iter().rev() {
                let pk_t = lam.instantiate_params(&[lit(k)], &g.env.binders_fn());
                let pk = each(g, k, &pk_t)?;
                let kk_lam = g.abs(&kk_cur, &[Self::var_id(&cv)]);
                acc = g.ev(&mp(R::Inst("tr.cfg_kk_cons".into(), vec![("P", lam.clone()), ("d", lit(k)), ("kk", kk_lam)]), vec![s(&pk), s(&acc)]), &[])?;
                kk_cur = g.mk("or", vec![g.mk("eq", vec![cv.clone(), lit(k)]), kk_cur]);
            }
            Ok(acc)
        };
        let done = c.done.clone();
        let p5 = gather(self, &c.body, &|_g, k, _| done.get(&k).cloned().ok_or_else(|| format!("the CFG: label {} not reached", k)))?;
        let ct_body = under(self, &prems[2]).ok_or_else(|| bad("its cut points' premise"))?;
        let hyp = c.hyp.clone();
        let p3 = gather(self, &ct_body, &|g, k, goal| {
            let h = hyp.get(&k).ok_or_else(|| format!("the CFG: label {} not reached", k))?;
            g.evp(&RP::Simp(false, vec![R::S(h.1.clone())], vec![], false), goal, &[])
        })?;
        // (no cut point a breakpoint: each label's address, by its equation)
        let nb_body = under(self, &prems[3]).ok_or_else(|| bad("its no-breakpoint premise"))?;
        let p4 = gather(self, &nb_body, &|g, k, goal| {
            let h = hyp.get(&k).ok_or_else(|| format!("the CFG: label {} not reached", k))?;
            g.evp(&RP::Simp(false, vec![R::S(h.1.clone())], vec![], false), goal, &[])
        })?;
        // (started within the first block: the start's claim, the rule at
        // st itself)
        if let (Some((hu, _)), Some(sw)) = (&start_h, &sw) {
            let rule = self.run(&mp(lr, vec![simp0(), p(f("tr.tr_univ")), s(&p3), s(&p4), s(&p5), simp0(), simp0()]), &[])?;
            let c0 = self.run(&mp(R::S(rule), vec![t(&y0t), t(&st.w), s(hu), defs(RP::By(R::S(sw.clone())), &["tr.lone"])]), &[])?;
            let c1 = self.run(&R::Expand(Box::new(R::S(c0)), vec!["tr.lprog".into(), "tr.lp0".into()]), &[])?;
            let hts: Vec<Term> = c.hyp.values().map(|h| h.0.clone()).collect();
            let closed = self.close(c1, &hts, &[Self::var_id(&ad)])?;
            let mut table = self.mk("empty", vec![]);
            for (k, a) in &c.addr {
                table = self.mk("fn_update", vec![table, lit(*k), lit(*a)]);
            }
            let mut args = vec![t(&table)];
            args.extend(hts.iter().map(|_| simp0()));
            self.trace(|| format!("cfg within its first block at {:x}: {} labels walked", st.a, c.addr.len()));
            return self.run(&mp(R::S(closed), args), &[]).map(Ok);
        }
        let rule = self.run(&mp(lr, vec![simp0(), p(f("tr.tr_univ")), s(&p3), s(&p4), s(&p5)]), &[])?;
        // at the first label, the locals now
        let (_, mask_e) = *c.labels.iter().find(|x| x.0 == k_e).ok_or_else(|| bad("the first label not among the labels"))?;
        let c0 = self.run(&mp(R::S(rule), vec![t(&lit(k_e)), t(&ys0), t(&st.w), simp0(), simp_lw(vec![R::S(st.hvu.clone())]), simp_lw(wf)]), &[])?;
        let lv0 = self.app(c0.concl(), "tr.lv", 13).ok_or_else(|| bad("the rule's claim"))?.to_vec();
        let (_, hs_e) = self.cfg_homes(&c, mask_e, &ys0, st.a)?;
        // (the first label's registers: rc's -- none of its live locals in
        // one, the entry's registers are the arguments')
        if self.cfg_rc(&c, mask_e, &ys0).len() != c.rc.len() {
            return Err(bad("the first label's live locals in registers"));
        }
        let (_, h0s) = c.hyp[&k_e].clone();
        let conv = mpf(
            "tr.lv_conv",
            vec![
                t(&self.s.clone()),
                t(&self.v.clone()),
                t(&self.base.clone()),
                t(&self.code.clone()),
                t(&lit(st.fr)),
                t(&lit(st.a)),
                t(&lv0[7]),
                t(&hs_e),
                t(&lv0[8]),
                t(&lv0[9]),
                t(&self.regs_map(&c.rc)),
                t(&lv0[10]),
                t(&lv0[11]),
                t(&lv0[12]),
                simpw(vec![R::S(h0s.clone())]),
                simpw(vec![R::S(h0s)]),
                simp0(),
                s(&c0),
            ],
        );
        let c1 = self.run(&R::Expand(Box::new(conv), vec!["tr.lprog".into(), "tr.lp0".into()]), &[])?;
        let at = self.loop_at(st, st.a, &c.rc, c1)?;
        // AD: the table found
        let hts: Vec<Term> = c.hyp.values().map(|h| h.0.clone()).collect();
        let closed = self.close(at, &hts, &[Self::var_id(&ad)])?;
        let mut table = self.mk("empty", vec![]);
        for (k, a) in &c.addr {
            table = self.mk("fn_update", vec![table, lit(*k), lit(*a)]);
        }
        let mut args = vec![t(&table)];
        args.extend(hts.iter().map(|_| simp0()));
        self.trace(|| format!("cfg at {:x}: {} labels walked", st.a, c.addr.len()));
        self.run(&mp(R::S(closed), args), &[]).map(Ok)
    }

    /// each label walked from its cut point (the labels found as walks
    /// arrive)
    fn cfg_walks(&mut self) -> Result<(), String> {
        while let Some(k) = self.cfg.as_mut().and_then(|c| c.todo.pop()) {
            let pk = self.cfg_walk(k)?;
            self.cfg.as_mut().expect("the CFG walk").done.insert(k, pk);
        }
        Ok(())
    }

    /// label k's claim P(k): its block walked from its address, for every
    /// rest of the locals and world
    fn cfg_walk(&mut self, k: u128) -> Result<Seq, String> {
        let c = self.cfg.as_ref().expect("the CFG walk");
        let a = c.addr[&k];
        let mask = c.labels.iter().find(|x| x.0 == k).map(|x| x.1).ok_or_else(|| format!("{:x}: the CFG: label {} not among the labels", a, k))?;
        let pk_t = c.body.instantiate_params(&[lit(k)], &self.env.binders_fn());
        let (bkp2, bka2, hs_lam, fr, fd, rc) = (c.bkp2.clone(), c.bka2.clone(), c.hs_lam.clone(), c.fr, c.fd.clone(), c.rc.clone());
        let bkp0 = c.bkp0.clone();
        let (hyps, facts, lfx) = (c.hyps.clone(), c.facts.clone(), c.lfx.clone());
        let (b, kl, kw, wrap) = (c.b.clone(), c.kl.clone(), c.kw.clone(), c.wrap.clone());
        let n = self.fresh("");
        let ys = self.var(&format!("cys{n}"));
        let wv = self.var(&format!("cw{n}"));
        // P(k) at ys, w: its assumptions, its claim
        let a1 = self.app(&pk_t, "all", 1).ok_or("the CFG: P(k)")?[0].clone().instantiate_params(std::slice::from_ref(&ys), &self.env.binders_fn());
        let a2 = self.app(&a1, "all", 1).ok_or("the CFG: P(k)")?[0].clone().instantiate_params(std::slice::from_ref(&wv), &self.env.binders_fn());
        let (asm, lv) = self.imps(&a2);
        if asm.len() != 3 {
            return Err("the CFG: P(k)'s assumptions".into());
        }
        let hu = self.assume(&asm[0])?;
        let hy = self.assume(&asm[1])?;
        let hw = self.assume(&asm[2])?;
        let hv = self.evp(&RP::Taut(vec![R::S(hw.clone())]), &self.mk("in", vec![wv.clone(), self.mk("univ", vec![lit(1)])]), &[])?;
        let c = self.cfg.as_ref().expect("the CFG walk");
        let (hsm, hst) = self.cfg_homes(c, mask, &ys, a)?;
        let regs = self.cfg_rc(c, mask, &ys);
        let wts = self.cfg_widths(c, mask, &ys);
        let mut wfacts = Vec::new();
        for wt in wts {
            wfacts.push(self.evp(&RP::Simp(false, vec![R::S(hy.clone())], vec![], false), &wt, &[])?);
        }
        let y = self.mk("pair", vec![lit(k), ys.clone()]);
        let qit = self.mk("tr.liter", vec![y.clone(), b.clone(), kl.clone(), kw.clone()]);
        let jq = self.new_q(qit);
        let qv = self.var(&format!("cq{n}"));
        let wid = self.parse(&format!("mkprog(x1 x2. bind_rel(cq{n}, x1, x3 x4. x2 = ok(x3, x4), x3 x4. x2 = exc(x3, x4), x3. x2 = diverge(x3)))"))?;
        let wrap_id = self.abs(&wid, &[Self::var_id(&qv)]);
        let kw_id = self.mk("eq", vec![Term::bvar(0), self.mk("ok", vec![Term::bvar(2), Term::bvar(1)])]);
        let rs_k = self.regs_map(&regs);
        let st_body = St {
            a,
            fr,
            regs,
            rs: rs_k.clone(),
            ds: fd.clone(),
            w: wv.clone(),
            hvu: hv,
            hw: hw.clone(),
            hsm,
            hst: hst.clone(),
            spec: Spec::Proc(jq),
            hyps,
            bconds: Vec::new(),
            spent: Vec::new(),
            facts: facts.into_iter().chain(wfacts.iter().cloned()).collect(),
            lfx: lfx.into_iter().chain(wfacts).collect(),
            splits: Vec::new(),
            no_join: Some(a),
            no_block: Some(a),
            z: None,
        };
        self.bkp = bkp2;
        self.bka = bka2;
        self.wrap = wrap_id;
        self.kw = kw_id;
        self.lpg = Some(LoopG { head: u128::MAX, hs: hs_lam.clone(), bkp: bkp0, wrap, kw, hu: hu.clone(), fd: fd.clone(), rc, yt: hs_lam, hy: hy.clone() });
        self.trace(|| format!("cfg label {} at {:x}", k, a));
        let hus = std::mem::take(&mut self.hus);
        let res = self.prove(st_body);
        self.hus = hus;
        let walk = res?;
        // its claim at app(AD, k), hs(pair(k, ys))
        let lvx = self.app(&lv, "tr.lv", 13).ok_or("the CFG: P(k)'s claim")?.to_vec();
        let (_, hk) = self.cfg.as_ref().expect("the CFG walk").hyp[&k].clone();
        let conv = mpf(
            "tr.lv_conv",
            vec![
                t(&self.s.clone()),
                t(&self.v.clone()),
                t(&self.base.clone()),
                t(&self.code.clone()),
                t(&lit(fr)),
                t(&lvx[7]),
                t(&lit(a)),
                t(&lvx[8]),
                t(&hst),
                t(&lvx[9]),
                t(&lvx[10]),
                t(&rs_k),
                t(&lvx[11]),
                t(&lvx[12]),
                simpw(vec![R::S(hk.clone())]),
                simpw(vec![R::S(hk)]),
                simp0(),
                s(&walk),
            ],
        );
        let pk = self.run(&conv, &[])?;
        self.close(pk, &asm, &[Self::var_id(&ys), Self::var_id(&wv)])
    }

    /// the start's claim (tr.cfg_lvk_st): the first iteration's rest, on
    /// the locals y0, walked from st (its homes, registers and world) up to
    /// the labels' cut points; hu, hy: y0's facts as a label's
    fn cfg_start_walk(&mut self, st: &St, y0: &Term, hu: Seq, hy: Seq) -> Result<Seq, String> {
        let c = self.cfg.as_ref().expect("the CFG walk");
        let (bkp2, bka2, hs_lam, fd, rc, bkp0) = (c.bkp2.clone(), c.bka2.clone(), c.hs_lam.clone(), c.fd.clone(), c.rc.clone(), c.bkp0.clone());
        let (b, kl, kw, wrap) = (c.b.clone(), c.kl.clone(), c.kw.clone(), c.wrap.clone());
        let n = self.fresh("");
        let qit = self.mk("tr.liter", vec![y0.clone(), b, kl, kw.clone()]);
        let jq = self.new_q(qit);
        let qv = self.var(&format!("cq{n}"));
        let wid = self.parse(&format!("mkprog(x1 x2. bind_rel(cq{n}, x1, x3 x4. x2 = ok(x3, x4), x3 x4. x2 = exc(x3, x4), x3. x2 = diverge(x3)))"))?;
        let wrap_id = self.abs(&wid, &[Self::var_id(&qv)]);
        let kw_id = self.mk("eq", vec![Term::bvar(0), self.mk("ok", vec![Term::bvar(2), Term::bvar(1)])]);
        let mut st_body = st.clone();
        st_body.spec = Spec::Proc(jq);
        st_body.no_join = Some(st.a);
        st_body.no_block = Some(st.a);
        st_body.splits = Vec::new();
        self.bkp = bkp2;
        self.bka = bka2;
        self.wrap = wrap_id;
        self.kw = kw_id;
        self.lpg = Some(LoopG { head: u128::MAX, hs: hs_lam.clone(), bkp: bkp0, wrap, kw, hu, fd, rc, yt: hs_lam, hy });
        self.trace(|| format!("cfg start at {:x}", st.a));
        let hus = std::mem::take(&mut self.hus);
        let res = self.prove(st_body);
        self.hus = hus;
        res
    }

    /// At a cut point in a label's walk: the spec reduced to its marked
    /// return (the next label and locals) -- the arrival (tr.pt_cut); None
    /// where the spec is not there
    pub(super) fn cfg_arrive(&mut self, st: &St) -> Result<Option<Seq>, String> {
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        self.fr = st.fr;
        self.w = st.w.clone();
        self.hvu = Some(st.hvu.clone());
        self.hww = Some(st.hw.clone());
        self.set_lf(st)?;
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
        let mut cur = qi;
        let mut steps: Vec<R> = Vec::new();
        let (w2, y2) = loop {
            if let Some(m) = marker(self, &self.qs[cur].clone()) {
                break m;
            }
            if steps.len() > 10000 {
                return Err(format!("{:x}: the block's rest does not end", st.a));
            }
            match self.reduce(cur, &st.hyps)? {
                Some(Red::Q(j, r)) => {
                    steps.push(r);
                    cur = j;
                }
                _ => return Ok(None),
            }
        };
        if self.canon(&w2) != self.canon(&st.w) {
            return Err(format!("{:x}: the block's marked return of another world", st.a));
        }
        let yp = self.app(&y2, "pair", 2).ok_or_else(|| format!("{:x}: the next locals not a label and the rest", st.a))?.to_vec();
        let k2 = nat(&yp[0]).ok_or_else(|| format!("{:x}: the next label not a literal: {}", st.a, self.print(&yp[0])))?;
        let ys2 = yp[1].clone();
        // its address: found here, or the one found before
        let c = self.cfg.as_mut().expect("the CFG walk");
        let mask = c.labels.iter().find(|x| x.0 == k2).map(|x| x.1).ok_or_else(|| format!("{:x}: the next label {} not among the labels", st.a, k2))?;
        match c.addr.get(&k2) {
            Some(&a0) if a0 != st.a => return Err(format!("{:x}: label {} arrived at here, at {:x} before", st.a, k2, a0)),
            Some(_) => {}
            None => {
                let h = self.mk("eq", vec![self.mk("app", vec![self.cfg.as_ref().unwrap().ad.clone(), lit(k2)]), lit(st.a)]);
                let hs = self.assume(&h)?;
                let c = self.cfg.as_mut().expect("the CFG walk");
                c.addr.insert(k2, st.a);
                c.hyp.insert(k2, (h, hs));
                c.todo.push(k2);
                self.trace(|| format!("cfg label {} at {:x}: found", k2, st.a));
            }
        }
        let c = self.cfg.as_ref().expect("the CFG walk");
        let (hk, ad, hs_lam, yt_lam, ct_lam, kk_lam, fd) = (c.hyp[&k2].1.clone(), c.ad.clone(), c.hs_lam.clone(), c.yt_lam.clone(), c.ct_lam.clone(), c.kk_lam.clone(), c.fd.clone());
        let (rc_lam, rc_const) = (c.rc_lam.clone(), c.rc_const);
        let (hs2, hs2e) = self.cfg_homes(c, mask, &ys2, st.a)?;
        let regs2 = self.cfg_rc(c, mask, &ys2);
        // (the homes there: each the point's; the registers likewise)
        for (key, (nb, v)) in &hs2 {
            match st.hsm.get(key) {
                Some((nb0, v0)) if nb0 == nb && self.canon(v0) == self.canon(v) => {}
                Some((nb0, v0)) => {
                    return Err(format!(
                        "{:x}: label {}'s home {:x} does not hold {} ({} bytes; N: {}) here: it holds {} ({} bytes; N: {})",
                        st.a,
                        k2,
                        key,
                        self.print(v),
                        nb,
                        self.print(&self.canon(v)),
                        self.print(v0),
                        nb0,
                        self.print(&self.canon(v0))
                    ))
                }
                None => return Err(format!("{:x}: label {}'s home {:x} does not hold {} here: not a home", st.a, k2, key, self.print(v))),
            }
        }
        for (r, nb, v) in &regs2 {
            match self.reg(st, *r) {
                Some((nb0, v0)) if nb0 == *nb && self.canon(&v0) == self.canon(v) => {}
                _ => return Err(format!("{:x}: label {}'s register {} does not hold {} here", st.a, k2, r, self.print(v))),
            }
        }
        // the reductions to the marked return
        let o = self.mk("ok", vec![st.w.clone(), self.mk("pair", vec![lit(1u128 << 64), y2.clone()])]);
        let goal = self.mk("runs", vec![self.qs[cur].clone(), st.w.clone(), o.clone()]);
        let lg = self.lpg.clone().ok_or("the CFG walk's state")?;
        let mut rr = self.evp(&RP::Defs(Box::new(RP::Simp(true, vec![R::S(st.hvu.clone()), R::S(lg.hu.clone())], vec![], false)), vec!["runs".into(), "mkprog".into()]), &goal, &[])?;
        for stp in steps.into_iter().rev() {
            rr = self.run(&mp(stp, vec![t(&o), s(&rr)]), &[])?;
        }
        let qb = self.app(&self.qs[qi], "mkprog", 1).ok_or("the block's rest")?[0].clone();
        let io = R::Apply(Box::new(f("tr.isout_ok")), vec![t(&st.w), t(&self.mk("pair", vec![lit(1u128 << 64), y2.clone()]))]);
        let rw = R::Apply(Box::new(R::Inst("tr.wrap_id_in".into(), vec![("r", qb)])), vec![t(&st.w), t(&o), s(&rr), p(io)]);
        // the homes at y2 among the point's
        let hs2t = hs_lam.instantiate_params(std::slice::from_ref(&y2), &self.env.binders_fn());
        let mut sub_pf = mpf("tr.hsub_empty", vec![t(&st.hst)]);
        let mut fm = self.mk("empty", vec![]);
        for (key, nb, x) in self.home_entries(&hs2e).ok_or("the label's homes")? {
            let v = self.mk("pair", vec![lit(nb), x.clone()]);
            sub_pf = mpf("tr.hsub_upd", vec![t(&st.hst), t(&fm), t(&lit(key)), t(&v), p(sub_pf), simp_l(), simp_l()]);
            fm = self.upd(&fm, key, nb, &x);
        }
        let sub = self.run(&sub_pf, &[])?;
        let heq = self.evp(&RP::Simp(false, vec![R::S(hk.clone())], vec![], false), &self.mk("eq", vec![hs2t.clone(), hs2e.clone()]), &[])?;
        let sub2 = self.evp(&RP::Simp(false, vec![R::S(sub), R::S(heq)], vec![], false), &self.mk("tr.hsub", vec![hs2t, st.hst.clone()]), &[])?;
        // (the registers at y2 among the point's)
        let rsub = if rc_const {
            self.rsub_pf(&lg.rc, &st.rs)
        } else {
            let rsub0 = self.run(&self.rsub_pf(&regs2, &st.rs), &[])?;
            let rc2t = rc_lam.instantiate_params(std::slice::from_ref(&y2), &self.env.binders_fn());
            let req = self.evp(&RP::Simp(false, vec![], vec![], false), &self.mk("eq", vec![rc2t.clone(), self.regs_map(&regs2)]), &[])?;
            R::S(self.evp(&RP::Simp(false, vec![R::S(rsub0), R::S(req)], vec![], false), &self.mk("tr.rsub", vec![rc2t, st.rs.clone()]), &[])?)
        };
        // the label's invariant: its live locals words
        let cyt_lam = self.mk("tr.cyt", vec![yt_lam.clone(), kk_lam.clone(), Term::bvar(0)]);
        let yt2 = R::Apply(
            Box::new(R::Inst("tr.cyt_intro".into(), vec![("yt", yt_lam.clone()), ("kk", kk_lam)])),
            vec![t(&lit(k2)), t(&ys2), simp0(), simp_lw(vec![R::S(lg.hy.clone())])],
        );
        let ad_y = {
            let fy = self.mk("fst", vec![Term::bvar(0)]);
            self.mk("app", vec![ad, fy])
        };
        let inst = R::Inst(
            "tr.pt_cut".into(),
            vec![
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("fd", fd.clone()),
                ("rc", rc_lam),
                ("ct", ct_lam),
                ("ad", ad_y),
                ("hs", hs_lam),
                ("yt", cyt_lam),
                ("bkp", lg.bkp.clone()),
            ],
        );
        let pcl = self.p(&st.spec);
        self.trace(|| format!("cfg at {:x}: arrived, label {}", st.a, k2));
        let r = mp(
            inst,
            vec![t(&lit(st.a)), t(&st.hst), t(&st.rs), t(&pcl), t(&st.w), t(&y2), simp0(), simpw(vec![R::S(hk)]), s(&sub2), p(rsub), simp_lw(vec![R::S(st.hvu.clone()), R::S(lg.hu.clone())]), p(yt2), p(rw)],
        );
        if self.canon(&st.ds) == self.canon(&fd) {
            return self.run(&r, &[]).map(Some);
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
            t(&fd),
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
        self.run(&mpf("tr.pt_fd", args), &[]).map(Some)
    }
}
