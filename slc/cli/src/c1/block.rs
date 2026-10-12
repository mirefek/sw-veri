//! Blocks (docs/overview.md, C1): per-block simulation. Where the code
//! branches (a conditional jump) on an `if` of the spec, the block -- from
//! the jump to the point where its paths meet again (the jump's immediate
//! post-dominator in the code) -- is proven on its own: its lemma is the
//! claim for the block's program alone (`tr.bone`: the block, then a marked
//! return of its locals) with its end a breakpoint, arrived at coupled to
//! the locals there (as at a loop's head: `tr.pt_head`). The rest after the
//! block is claimed from its end once, for every world and locals, the
//! homes of the locals live there (the location map) holding them;
//! `tr.block_lv` composes the two. Each path inside the block ends at the
//! block's end: the walk grows with the code, not with its paths.

use super::rec::*;
use super::*;

impl<'e> Gen<'e> {
    /// the immediate post-dominator of a in the function's code (its
    /// returns, and jumps out of it, the exit)
    pub(super) fn ipdom(&mut self, a: u128) -> Option<u128> {
        if self.pdoms.is_none() {
            let nodes: Vec<u128> = self.insns.keys().copied().collect();
            let all: BTreeSet<u128> = nodes.iter().copied().collect();
            let mut pd: BTreeMap<u128, BTreeSet<u128>> = nodes.iter().map(|&n| (n, all.clone())).collect();
            let succ: BTreeMap<u128, Vec<u128>> = nodes.iter().map(|&n| (n, self.succs(n))).collect();
            let mut changed = true;
            while changed {
                changed = false;
                for &n in nodes.iter().rev() {
                    let ss = &succ[&n];
                    // (an exit: no successor in the code)
                    let mut s: BTreeSet<u128> = if ss.is_empty() || ss.iter().any(|x| !all.contains(x)) {
                        BTreeSet::new()
                    } else {
                        let mut it = ss.iter().map(|x| pd[x].clone());
                        let first = it.next().unwrap();
                        it.fold(first, |acc, x| acc.intersection(&x).copied().collect())
                    };
                    s.insert(n);
                    if s != pd[&n] {
                        pd.insert(n, s);
                        changed = true;
                    }
                }
            }
            self.pdoms = Some(pd);
        }
        let pd = self.pdoms.as_ref()?;
        let mine = pd.get(&a)?;
        mine.iter().copied().find(|&d| d != a && pd.get(&d).is_some_and(|x| x.len() + 1 == mine.len()))
    }

    /// the function's epilogue: the frame's code (`nop`, `add rsp, k`)
    /// straight on to a `ret`, from where paths jump to it (the `return`s'
    /// target, and the end's)
    pub(super) fn epilogue(&mut self) -> BTreeSet<u128> {
        let frame_only = |g: &Gen, a: u128| {
            let Some(i) = g.insns.get(&a) else { return false };
            let rsp = || g.pairs(&i.fields, 5).and_then(|x| g.tag(&x[2])).is_some_and(|(k, r)| k == 0 && nat(&r) == Some(4));
            matches!(i.row, 109 | 122) || (matches!(i.row, 59 | 60) && rsp())
        };
        let rets: Vec<u128> = self.insns.iter().filter(|(_, i)| i.row == 122).map(|(a, _)| *a).collect();
        let mut out = BTreeSet::new();
        for r in rets {
            let mut x = r;
            out.insert(x);
            while self.preds_of(x) == 1 {
                let Some(p) = self.insns.iter().find(|(p, i)| (**p + i.len) % P64 == x && self.succs(**p) == vec![x]).map(|(p, _)| *p) else { break };
                if !frame_only(self, p) {
                    break;
                }
                x = p;
                out.insert(x);
            }
        }
        out
    }

    /// The end of the block of the conditional jump at b (al its spec,
    /// `x0 x8. (c && A) || (!c && B)`): where its branches meet. No
    /// `return` in it: b's immediate post-dominator. With `return`s
    /// (paths into the epilogue, leaving the function, not meeting): the
    /// first point after b both its targets reach outside the epilogue;
    /// else, a branch all `return`s (the spec's), the other's target (the
    /// then-branch the fall-through, its code ahead of the else-branch's);
    /// else no block (the `return`s and the end the same code)
    fn block_end(&mut self, b: u128, al: &Term) -> Result<u128, String> {
        // (a `return`: `exc(_, pair("ret", v))`, v not an inner outcome's
        // value passed on)
        let ret = |g: &Gen, t: &Term| {
            fn has(g: &Gen, t: &Term) -> bool {
                if let Some(pr) = g.app(t, "exc", 2).and_then(|e| g.app(&e[1], "pair", 2)) {
                    if matches!(pr[0].node(), Node::Bytes(x) if &x[..] == b"ret") && g.app(&pr[1], "snd", 1).and_then(|s| g.app(&s[0], "out_value", 1)).is_none() {
                        return true;
                    }
                }
                match t.node() {
                    Node::App(_, a) | Node::Var(_, a) => a.iter().any(|x| has(g, x)),
                    _ => false,
                }
            }
            has(g, &g.expand(t))
        };
        if !ret(self, al) {
            return self.ipdom(b).ok_or_else(|| "no post-dominator".into());
        }
        let epi = self.epilogue();
        let reach = |g: &Gen, s: u128| {
            let mut seen = BTreeSet::new();
            let mut todo = vec![s];
            while let Some(x) = todo.pop() {
                if g.insns.contains_key(&x) && !epi.contains(&x) && seen.insert(x) {
                    todo.extend(g.succs(x));
                }
            }
            seen
        };
        let ss = self.succs(b);
        if ss.len() != 2 {
            return Err("not a two-way branch".into());
        }
        let (r1, r2) = (reach(self, ss[0]), reach(self, ss[1]));
        if let Some(j) = r1.intersection(&r2).copied().filter(|&x| x > b).min() {
            return Ok(j);
        }
        let d = self.app(al, "or", 2).map(|x| x.to_vec()).ok_or("no `if`")?;
        let all_ret: Vec<bool> = d.iter().map(|x| ret(self, x) && self.block_outcomes(x).is_empty()).collect();
        match (all_ret[0], all_ret[1]) {
            (true, true) => Err("both branches `return`".into()),
            (true, false) => Ok(ss.iter().copied().max().unwrap()),
            _ => Err("a `return` inside, its end the function's".into()),
        }
    }

    /// the width of the home c: the operand size of the code's accesses to
    /// it (`[rsp + d]`, d's key c), if one size
    fn home_width(&self, c: u128) -> Option<u128> {
        fn memops<'t>(g: &Gen, t: &'t Term, out: &mut Vec<&'t Term>) {
            if g.rsp_mem(t).is_some() {
                out.push(t);
                return;
            }
            if let Node::App(_, a) = t.node() {
                a.iter().for_each(|x| memops(g, x, out));
            }
        }
        let mut sizes = BTreeSet::new();
        for i in self.insns.values() {
            let mut ms = Vec::new();
            memops(self, &i.fields, &mut ms);
            let at = ms.iter().any(|m| self.rsp_mem(m).and_then(|d| nat(&d)).is_some_and(|d| self.hkey(d) == c));
            if at {
                let size = self.pairs(&i.fields, 2).and_then(|x| nat(&x[0])).filter(|n| matches!(n, 1 | 2 | 4 | 8))?;
                sizes.insert(size);
            }
        }
        (sizes.len() == 1).then(|| *sizes.iter().next().unwrap())
    }

    /// the `if`'s outcomes' locals in its block head a, each branch's: Y of
    /// each `x8 = ok(pair(W, Y), E)`, and the binders above it in a
    fn block_outcomes(&self, al: &Term) -> Vec<(Term, u32)> {
        fn go(g: &Gen, t: &Term, d: u32, out: &mut Vec<(Term, u32)>) {
            if let Some(x) = g.app(t, "eq", 2) {
                if matches!(x[0].node(), Node::BVar(i) if *i == d) {
                    if let Some(pr) = g.app(&x[1], "ok", 2).and_then(|o| g.app(&o[0], "pair", 2)) {
                        out.push((pr[1].clone(), d));
                        return;
                    }
                }
            }
            if let Node::App(f, a) = t.node() {
                a.iter().enumerate().for_each(|(i, x)| go(g, x, d + g.env.binders_fn()(*f, i), out));
            }
        }
        let mut out = Vec::new();
        go(self, al, 0, &mut out);
        out
    }

    /// the `if`'s outcome's locals in its block head a (`x0 x8. A`): a
    /// `x8 = ok(pair(W, Y), E)` in it -- Y
    fn block_outcome(&self, al: &Term) -> Option<Term> {
        fn go(g: &Gen, t: &Term, d: u32) -> Option<Term> {
            if let Some(x) = g.app(t, "eq", 2) {
                if matches!(x[0].node(), Node::BVar(i) if *i == d) {
                    if let Some(o) = g.app(&x[1], "ok", 2) {
                        if let Some(pr) = g.app(&o[0], "pair", 2) {
                            return Some(pr[1].clone());
                        }
                    }
                }
            }
            match t.node() {
                Node::App(f, a) => a.iter().enumerate().find_map(|(i, x)| go(g, x, d + g.env.binders_fn()(*f, i))),
                _ => None,
            }
        }
        go(self, al, 0)
    }

    /// a block not proven (its end not the spec's -- a tail the compiler
    /// shares between branches): the branch as without it, its paths
    /// joined by the join claims (join.rs), reported
    fn block_fallback(&mut self, a: u128, why: String) -> Result<Option<Seq>, String> {
        self.trace(|| format!("block at {:x}: not proven ({}), the join claims instead", a, why.replace('\n', " / ")));
        self.block_fb.push(a);
        Ok(None)
    }

    /// The block at st (a conditional jump on the spec's `if`): its lemma,
    /// the rest's claim from its end, composed (tr.block_lv) -- the claim
    /// at st; None where st starts no block
    pub(super) fn block_point(&mut self, st: &St) -> Result<Option<Seq>, String> {
        // (the compare before a conditional jump: the engine takes the two
        // as one step)
        let Some(next) = self.insns.get(&st.a).map(|i| (st.a + i.len) % P64) else { return Ok(None) };
        if st.z.is_some() || st.no_block == Some(st.a) || self.block_fb.contains(&st.a) || !self.insns.get(&next).is_some_and(|i| matches!(i.row, 127 | 128)) {
            return Ok(None);
        }
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        let q = self.qs[qi].clone();
        let Some(body) = self.app(&q, "mkprog", 1).map(|x| x[0].clone()) else { return Ok(None) };
        let Some(y) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else { return Ok(None) };
        // (the head an `if` the machine branches on)
        if self.app(&y[0], "or", 2).is_none() {
            self.trace(|| format!("block at {:x}: no `if` at the head: {}", st.a, self.lambda(3, &y[0])));
            return Ok(None);
        }
        let ctx = ["x0", "x1", "x8"];
        let (Some(al), Some(kl)) = (self.lam(&y[0], &ctx, &["x0", "x8"]), self.lam(&y[1], &ctx, &["x8", "x1"])) else { return Ok(None) };
        let a = st.a;
        // (its end: where its branches meet -- a `return` inside jumps to
        // the function's end, not through it)
        let j = match self.block_end(next, &al) {
            Ok(j) => j,
            Err(e) => {
                self.trace(|| format!("block at {:x}: no block ({})", a, e));
                return Ok(None);
            }
        };
        if self.preds_of(j) < 2 || self.lpg.as_ref().is_some_and(|l| l.head == j) {
            return Ok(None);
        }
        // (no loop inside the block: its code from a to j on no cycle)
        let mut seen = BTreeSet::new();
        let mut todo = self.succs(next);
        while let Some(b) = todo.pop() {
            if b == j || !self.insns.contains_key(&b) || !seen.insert(b) {
                continue;
            }
            if self.on_cycle(b) {
                self.trace(|| format!("block at {:x}: a loop inside, not a block", a));
                return Ok(None);
            }
            todo.extend(self.succs(b));
        }
        let Some(y0) = self.block_outcome(&al) else { return Ok(None) };
        let nloc = self.locals_of(&y0).len();
        self.trace(|| format!("block at {:x}: to {:x} (the block {}; the rest {})", a, j, self.lambda(2, &al), self.lambda(2, &kl)));
        let n = self.fresh("");
        let yv = self.var(&format!("by{n}"));
        let wv = self.var(&format!("bw{n}"));
        // the homes at the block's end: those of the locals live there (the
        // location map), holding them
        let proj = |g: &Gen, i: usize| -> Term {
            let mut t = yv.clone();
            for _ in 0..i {
                t = g.mk("snd", vec![t]);
            }
            if i + 1 < nloc { g.mk("fst", vec![t]) } else { t }
        };
        let mut hsm_y = BTreeMap::new();
        let mut yts = Vec::new();
        for (c, (nb, x)) in &st.hsm {
            if let Some(i) = self.local_at(*c, j).filter(|&i| i < nloc) {
                let v = proj(self, i);
                yts.push(self.mk("in", vec![v.clone(), self.mk("bits", vec![lit(8 * nb)])]));
                hsm_y.insert(*c, (*nb, v));
                continue;
            }
            // (a home of no local there -- an argument's, a value from
            // before the block: as it is, the block not writing it)
            if self.local_at(*c, j).is_none() && !self.locmap.iter().any(|e| e.1 == *c && e.2 <= a && a < e.3 && self.local_at(*c, j).is_none() && e.3 <= j) {
                hsm_y.insert(*c, (*nb, x.clone()));
            }
        }
        // (a local live there whose home the block writes first: its home
        // too, of the width the code accesses it with)
        // (only one every branch computes: in each branch's outcome, the
        // local a literal or a value made in the block -- not the input's)
        let ends = self.block_outcomes(&al);
        let computed = |g: &Gen, i: usize| {
            let bf = g.env.binders_fn();
            // (the same in every branch: the input's -- an unassigned local's
            // placeholder too)
            let cs: Vec<Option<Term>> = ends.iter().map(|(y, _)| g.locals_of(y).get(i).cloned()).collect();
            if cs.windows(2).all(|w| w[0] == w[1]) && cs.iter().all(|c| c.as_ref().is_some_and(|c| c.loose_depth(&bf) == 0)) {
                return false;
            }
            ends.iter().all(|(y, d)| {
                let c = g.locals_of(y).get(i).cloned();
                c.is_some_and(|c| nat(&c).is_some() || c.loose_depth(&bf) > 0 && (0..*d).any(|k| bvar_free(&c, k, &bf)))
            })
        };
        let live: Vec<(usize, u128)> = self.locmap.iter().filter(|e| e.2 <= j && j < e.3 && e.0 < nloc).map(|e| (e.0, e.1)).collect();
        for (i, c) in live {
            if hsm_y.contains_key(&c) || self.local_at(c, j) != Some(i) {
                continue;
            }
            if !computed(self, i) {
                self.trace(|| {
                    let cs: Vec<String> = ends.iter().map(|(y, d)| self.locals_of(y).get(i).map(|c| self.lambda(*d as usize + 2, c)).unwrap_or_default()).collect();
                    format!("block at {:x}: local {} (home {:x}) not computed in every branch: {}", a, i, c, cs.join("; "))
                });
                continue;
            }
            let Some(nb) = self.home_width(c) else { continue };
            self.trace(|| {
                let cs: Vec<String> = ends.iter().map(|(y, d)| format!("{} (under {})", self.locals_of(y).get(i).map(|c| self.lambda(*d as usize + 2, c)).unwrap_or_default(), d)).collect();
                format!("block at {:x}: local {} (home {:x}) computed in the block: {}", a, i, c, cs.join("; "))
            });
            let v = proj(self, i);
            yts.push(self.mk("in", vec![v.clone(), self.mk("bits", vec![lit(8 * nb)])]));
            hsm_y.insert(c, (nb, v));
        }
        let yt_t = yts.into_iter().reduce(|a, b| self.mk("and", vec![a, b])).unwrap_or_else(|| self.mk("true", vec![]));
        let hst_y = self.hs_term(&hsm_y);
        let hs_lam = self.abs(&hst_y, &[Self::var_id(&yv)]);
        let yt_lam = self.abs(&yt_t, &[Self::var_id(&yv)]);
        // the rule's instance: the block's breakpoints
        let (lr, stmt) = self.inst(
            "tr.block_lv",
            &[
                ("s", self.s.clone()),
                ("v", self.v.clone()),
                ("base", self.base.clone()),
                ("code", self.code.clone()),
                ("fr", lit(st.fr)),
                ("ha", lit(j)),
                ("fd", st.ds.clone()),
                ("hs", hs_lam.clone()),
                ("yt", yt_lam.clone()),
                ("bkp", self.bkp.clone()),
                ("bka", self.bka.clone()),
                ("a", al.clone()),
                ("k", kl.clone()),
                ("kw", self.kw.clone()),
            ],
        )?;
        let lv_b = (|| {
            let imp = self.env.builtins.imp;
            let mut t0 = stmt.clone();
            for _ in 0..2 {
                let Node::App(s, x) = t0.node() else { return None };
                if *s != imp {
                    return None;
                }
                t0 = x[1].clone();
            }
            for _ in 0..4 {
                t0 = self.app(&t0, "all", 1)?[0].clone();
            }
            let Node::App(s, x) = t0.node() else { return None };
            (*s == imp).then(|| x[0].clone())
        })()
        .and_then(|t| self.app(&t, "tr.lv", 13).map(|x| x.to_vec()))
        .ok_or("tr.block_lv: its block premise")?;
        let (bkp2, bka2) = (lv_b[1].clone(), lv_b[2].clone());

        // the rest's claim from the block's end, for every locals and world
        // (the facts here: every path's in the block)
        let univ = |g: &Gen, x: &Term| g.mk("in", vec![x.clone(), g.mk("univ", vec![lit(1)])]);
        let hu_t = univ(self, &self.mk("pair", vec![wv.clone(), yv.clone()]));
        let hw_t = self.mk("and", vec![self.mk("in", vec![wv.clone(), self.mk("abi.World", vec![])]), univ(self, &wv)]);
        let hw = self.assume(&hw_t)?;
        let hu = self.assume(&hu_t)?;
        let hy = if self.app(&yt_t, "true", 0).is_some() { self.evp(&RP::Taut(vec![]), &yt_t, &[])? } else { self.assume(&yt_t)? };
        let hv = self.evp(&RP::Taut(vec![R::S(hw.clone())]), &univ(self, &wv), &[])?;
        let out = self.mk("ok", vec![self.mk("pair", vec![Term::bvar(1), yv.clone()]), self.mk("empty", vec![])]);
        let kb = kl.instantiate_params(&[out, Term::bvar(0)], &self.env.binders_fn());
        let jr = self.new_q(self.canon(&self.mk("mkprog", vec![kb])));
        let st_rest = St {
            a: j,
            fr: st.fr,
            regs: Vec::new(),
            rs: self.mk("empty", vec![]),
            ds: st.ds.clone(),
            w: wv.clone(),
            hvu: hv,
            hw,
            hsm: hsm_y,
            hst: hst_y,
            lp: st.lp,
            spec: Spec::Proc(jr),
            hyps: st.hyps.clone(),
            facts: st.facts.iter().cloned().chain([hy.clone(), hu.clone()]).collect(),
            lfx: st.lfx.iter().cloned().chain([hy.clone(), hu.clone()]).collect(),
            bconds: Vec::new(),
            spent: Vec::new(),
            splits: Vec::new(),
            no_join: Some(j),
            z: None,
            no_block: None,
        };
        self.trace(|| format!("block at {:x}: the rest from {:x}, for every world and locals", a, j));
        let hus = std::mem::replace(&mut self.hus, vec![hu]);
        let rest = self.prove_kept(st_rest);
        self.hus = hus;
        let rest = match rest {
            Ok(r) => r,
            Err(e) => return self.block_fallback(a, format!("the rest after it from {:x}: {}", j, e)),
        };
        let rest_c = self.close(rest, &[hu_t, yt_t, hw_t], &[Self::var_id(&yv), Self::var_id(&wv)])?;

        // the block's lemma: its program alone from here, its end a
        // breakpoint (in the identity wrapper, as a loop's iteration)
        let qb = self.mk("tr.biter", vec![al.clone(), kl.clone(), self.kw.clone()]);
        let jb = self.new_q(qb);
        let qv = self.var(&format!("bq{n}"));
        let wid = self.parse(&format!("mkprog(x1 x2. bind_rel(bq{n}, x1, x3 x4. x2 = ok(x3, x4), x3 x4. x2 = exc(x3, x4), x3. x2 = diverge(x3)))"))?;
        let wrap_id = self.abs(&wid, &[Self::var_id(&qv)]);
        let kw_id = self.mk("eq", vec![Term::bvar(0), self.mk("ok", vec![Term::bvar(2), Term::bvar(1)])]);
        let saved = LoopG {
            head: j,
            is_block: true,
            outer: self.lpg.clone().map(Box::new),
            hs: hs_lam,
            bkp: self.bkp.clone(),
            bka: self.bka.clone(),
            wrap: self.wrap.clone(),
            kw: self.kw.clone(),
            hu: st.hvu.clone(),
            fd: st.ds.clone(),
            yt: yt_lam,
            hy: st.hvu.clone(),
        };
        let mut st_blk = st.clone();
        st_blk.spec = Spec::Proc(jb);
        st_blk.no_block = Some(a);
        self.bkp = bkp2;
        self.bka = bka2;
        self.wrap = wrap_id;
        self.kw = kw_id;
        self.lpg = Some(saved.clone());
        self.trace(|| format!("block at {:x}: its lemma, to {:x}", a, j));
        let res = self.prove(st_blk);
        self.bkp = saved.bkp.clone();
        self.bka = saved.bka.clone();
        self.wrap = saved.wrap.clone();
        self.kw = saved.kw.clone();
        self.lpg = saved.outer.clone().map(|b| *b);
        let blk = match res {
            Ok(r) => r,
            Err(e) => return self.block_fallback(a, format!("its lemma to {:x}: {}", j, e)),
        };

        // composed: the claim here
        self.fr = st.fr;
        self.w = st.w.clone();
        self.hvu = Some(st.hvu.clone());
        self.set_lf(st)?;
        let r1 = mp(lr, vec![self.nobp(), s(&rest_c)]);
        let r2 = mp(r1, vec![t(&lit(a)), t(&st.hst), t(&st.rs), t(&st.w), s(&blk)]);
        let pf = self.run(&R::Expand(Box::new(r2), vec!["tr.bprog".into(), "tr.bp0".into()]), &[])?;
        self.trace(|| format!("block at {:x}: composed", a));
        Ok(Some(pf))
    }
}

/// whether BVar(k) (at t's top) occurs free in t
fn bvar_free(t: &Term, k: u32, bf: &dyn Fn(u32, usize) -> u32) -> bool {
    match t.node() {
        Node::BVar(i) => *i == k,
        Node::App(f, a) => a.iter().enumerate().any(|(i, x)| bvar_free(x, k + bf(*f, i), bf)),
        Node::Var(_, a) => a.iter().any(|x| bvar_free(x, k, bf)),
        _ => false,
    }
}
