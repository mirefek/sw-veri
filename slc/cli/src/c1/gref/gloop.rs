//! The CFG's loop with loops of its own (g.cut_loops, proofs/gimple_loop.core):
//! the loop heads cut points, the structured loop at each (a node of the
//! structured form), a trip's claim per head, the exits' claims.

use super::*;

/// A CFG's loops: the heads, each label's loop (its head; 0 outside), each
/// head's exits, the cut labels, a rank falling at every step but a back
/// edge
pub(super) struct Loops {
    pub heads: Vec<u128>,
    pub lp: BTreeMap<u128, u128>,
    pub exits: BTreeMap<u128, Vec<u128>>,
    pub cuts: BTreeSet<u128>,
    pub rank: BTreeMap<u128, u128>,
}

/// The loops of the label graph (each label's leaves; `cuts0` the
/// structuring's cut labels): a head's loop the labels reaching a back
/// edge to it without passing it; its exits (cut labels, outside every
/// loop); the cut labels the first, the heads, the exits and the
/// structuring's outside the loops
pub(super) fn loops_of(labels: &[u128], succ: &BTreeMap<u128, Vec<Option<u128>>>, entry: u128, cuts0: &BTreeSet<u128>) -> Result<Loops, String> {
    let next = |k: u128| -> Vec<u128> { succ.get(&k).into_iter().flatten().flatten().copied().collect() };
    // back edges: to a label on the walk's stack
    let mut back: BTreeSet<(u128, u128)> = BTreeSet::new();
    let mut state: BTreeMap<u128, u8> = BTreeMap::new();
    let mut stack: Vec<(u128, usize)> = vec![(entry, 0)];
    state.insert(entry, 1);
    while let Some((k, i)) = stack.pop() {
        let ns = next(k);
        if i < ns.len() {
            stack.push((k, i + 1));
            let s = ns[i];
            match state.get(&s).copied().unwrap_or(0) {
                1 => {
                    back.insert((k, s));
                }
                0 => {
                    state.insert(s, 1);
                    stack.push((s, 0));
                }
                _ => {}
            }
        } else {
            state.insert(k, 2);
        }
    }
    let mut preds: BTreeMap<u128, Vec<u128>> = BTreeMap::new();
    for &k in labels {
        for s in next(k) {
            preds.entry(s).or_default().push(k);
        }
    }
    let mut body: BTreeMap<u128, BTreeSet<u128>> = BTreeMap::new();
    for &(latch, h) in &back {
        let bs = body.entry(h).or_default();
        bs.insert(h);
        let mut work = vec![latch];
        while let Some(x) = work.pop() {
            if bs.insert(x) {
                work.extend(preds.get(&x).into_iter().flatten().copied());
            }
        }
    }
    let mut lp: BTreeMap<u128, u128> = BTreeMap::new();
    for (&h, bs) in &body {
        for &x in bs {
            if lp.insert(x, h).is_some_and(|o| o != h) {
                return Err(format!("label {}: in two loops (nested loops: not yet)", x));
            }
        }
    }
    let mut exits: BTreeMap<u128, Vec<u128>> = BTreeMap::new();
    for (&h, bs) in &body {
        let mut es: BTreeSet<u128> = BTreeSet::new();
        for &x in bs {
            es.extend(next(x).into_iter().filter(|s| !bs.contains(s)));
        }
        for &e in &es {
            if lp.contains_key(&e) {
                return Err(format!("loop {}: its exit {} inside a loop (nested loops: not yet)", h, e));
            }
        }
        exits.insert(h, es.into_iter().collect());
    }
    for &k in labels {
        for s in next(k) {
            if let Some(&h) = lp.get(&s) {
                if s != h && lp.get(&k) != Some(&h) {
                    return Err(format!("loop {}: entered at {} (from {}), not at its head", h, s, k));
                }
            }
        }
    }
    let heads: Vec<u128> = body.keys().copied().collect();
    let mut cuts: BTreeSet<u128> = BTreeSet::from([entry]);
    cuts.extend(heads.iter().copied());
    cuts.extend(exits.values().flatten().copied());
    cuts.extend(cuts0.iter().copied().filter(|c| !lp.contains_key(c)));
    // (a rank: the longest way on without the back edges)
    let mut rank: BTreeMap<u128, u128> = BTreeMap::new();
    for _ in 0..=labels.len() {
        for &k in labels {
            let r = next(k).into_iter().filter(|s| !back.contains(&(k, *s))).map(|s| rank.get(&s).copied().unwrap_or(0) + 1).max().unwrap_or(0);
            rank.insert(k, r);
        }
    }
    if labels.iter().any(|&k| next(k).into_iter().any(|s| !back.contains(&(k, s)) && rank[&s] >= rank[&k])) {
        return Err("the CFG's labels: no rank (an irreducible loop)".into());
    }
    Ok(Loops { heads, lp, exits, cuts, rank })
}

/// A structured loop at a head: its state's locals T (in the head point's
/// locals y), its body (`x y. ..`), trace (`x. ..`), rest (`x9 o. ..`)
pub(super) struct SLoop {
    pub y: Term,
    pub t: Term,
    pub bs: Term,
    pub trs: Term,
    pub ks: Term,
}

/// The loops' relations over the states (`l. ..`, `h l. ..`)
pub(super) struct LoopRels {
    pub pt: Term,
    pub hd: Term,
    pub xp: Term,
    pub lp: Term,
    pub m: Term,
    /// the labels' states (a disjunct per label), v (in univ(1) too)
    pub d: Term,
    pub v: Term,
}

impl<'e> Gen<'e> {
    /// `l. fst(snd(l)) = k1 || .. || false` over ks (lv the variable)
    fn label_in(&self, lv: &Term, ks: &[u128]) -> Term {
        let lab = self.mk("fst", vec![self.mk("snd", vec![lv.clone()])]);
        let mut t = self.mk("false", vec![]);
        for &k in ks.iter().rev() {
            t = self.mk("or", vec![self.mk("eq", vec![lab.clone(), lit(k)]), t]);
        }
        t
    }

    /// a table of the labels: `app(T, fst(snd(l)))`
    fn label_table(&self, lv: &Term, labels: &[u128], f: impl Fn(u128) -> u128) -> Term {
        let mut table = self.mk("empty", vec![]);
        for &k in labels {
            table = self.mk("fn_update", vec![table, lit(k), lit(f(k))]);
        }
        self.mk("app", vec![table, self.mk("fst", vec![self.mk("snd", vec![lv.clone()])])])
    }

    fn loop_rels(&mut self, lps: &Loops, labels: &[u128]) -> LoopRels {
        let lv = self.var("gl");
        let hv = self.var("gh");
        let yv = self.var("gly");
        let lid = Self::var_id(&lv);
        let cuts: Vec<u128> = lps.cuts.iter().copied().collect();
        let pt = self.abs(&self.label_in(&lv, &cuts), &[lid]);
        let hd = self.abs(&self.label_in(&lv, &lps.heads), &[lid]);
        let mut xp = self.mk("false", vec![]);
        for h in lps.heads.iter().rev() {
            let c = self.mk("and", vec![self.mk("eq", vec![hv.clone(), lit(*h)]), self.label_in(&lv, &lps.exits[h])]);
            xp = self.mk("or", vec![c, xp]);
        }
        let xp = self.abs(&xp, &[Self::var_id(&hv), lid]);
        let lp = self.abs(&self.label_table(&lv, labels, |k| lps.lp.get(&k).copied().unwrap_or(0)), &[lid]);
        let m = self.abs(&self.label_table(&lv, labels, |k| lps.rank[&k]), &[lid]);
        let mut d = self.mk("false", vec![]);
        for &kl in labels.iter().rev() {
            let e = self.mk("eq", vec![lv.clone(), self.mk("pair", vec![self.mk("fst", vec![lv.clone()]), self.mk("pair", vec![lit(kl), yv.clone()])])]);
            d = self.mk("or", vec![self.mk("ex", vec![self.abs(&e, &[Self::var_id(&yv)])]), d]);
        }
        let u = self.mk("in", vec![lv.clone(), self.mk("univ", vec![lit(1)])]);
        let v = self.abs(&self.mk("and", vec![u, d.clone()]), &[lid]);
        let d = self.abs(&d, &[lid]);
        LoopRels { pt, hd, xp, lp, m, d, v }
    }

    /// a premise `all l q. inv(l, q) -> H1 -> .. -> G(l, q)`: `l q. H1 -> .. -> G`
    fn claim_g(&self, prem: &Term) -> Result<Term, String> {
        let b1 = self.app(prem, "all", 1).ok_or("a premise over the points")?[0].clone();
        let b2 = self.app(&b1, "all", 1).ok_or("a premise over the points")?[0].clone();
        let (hs, g) = self.imps(&b2);
        if hs.is_empty() {
            return Err("a premise over the points: not inv -> ..".into());
        }
        let mut g = g;
        for h in hs[1..].iter().rev() {
            g = Term::app(self.env.builtins.imp, vec![h.clone(), g]);
        }
        Ok(g)
    }

    /// The CFG's loop with loops (g.cut_loops)
    #[allow(clippy::too_many_arguments)]
    pub(super) fn cfg_loops(&mut self, lo: &Term, l0: &Term, b: &Term, tr: &Term, kk: &Term, comps: &[Term], k_e: u128, labels: &[u128], succ: &BTreeMap<u128, Vec<Option<u128>>>, cuts0: &BTreeSet<u128>, q0: &Term, w: &Term) -> Result<Seq, String> {
        let lps = loops_of(labels, succ, k_e, cuts0)?;
        self.trace(|| format!("ref: loops at {:?}, exits {:?}, cut at {:?}", lps.heads, lps.exits, lps.cuts));
        let rels = self.loop_rels(&lps, labels);
        let fls = self.mk("false", vec![]);
        let cut = GCut { v: rels.d.clone(), labels: labels.to_vec(), succ: succ.clone(), vm: None, hv: BTreeMap::new(), hm: BTreeMap::new(), ways: BTreeMap::new() };
        self.gref = Some(GRef { m: comps.len(), points: Vec::new(), inv: fls.clone(), b: b.clone(), cur: k_e, cut: Some(cut), inv_var: None, hyps: Vec::new(), walked: Vec::new(), loop_heads: lps.heads.iter().copied().collect() });
        // the theorem at a free INV (and the structured loops' parts free
        // while the heads are found)
        let iv = self.env.new_var("ginv", 2);
        let inv_v = Term::var(iv, vec![Term::bvar(1), Term::bvar(0)]);
        {
            let g = self.gref.as_mut().unwrap();
            g.inv = inv_v.clone();
            g.inv_var = Some(iv);
        }
        let ph = |g: &mut Self, n: &str, k: u32| Term::var(g.env.new_var(n, k), (0..k).rev().map(Term::bvar).collect());
        let (hph, bsph, trsph, ksph) = (ph(self, "gH", 2), ph(self, "gbs", 3), ph(self, "gtrs", 1), ph(self, "gks", 3));
        let binds = |inv: Term, h: Term, bs: Term, trs: Term, ks: Term| {
            vec![
                ("b", b.clone()),
                ("tr", tr.clone()),
                ("k", kk.clone()),
                ("pt", rels.pt.clone()),
                ("hd", rels.hd.clone()),
                ("xp", rels.xp.clone()),
                ("lp", rels.lp.clone()),
                ("v", rels.v.clone()),
                ("m", rels.m.clone()),
                ("inv", inv),
                ("H", h),
                ("bs", bs),
                ("trs", trs),
                ("ks", ks),
            ]
        };
        let (_, stmt) = self.inst("g.cut_loops", &binds(inv_v.clone(), hph.clone(), bsph.clone(), trsph.clone(), ksph.clone()))?;
        let (prems, _) = self.imps(&stmt);
        let gs = self.claim_g(&prems[10])?;
        // the cut points: each found as a walk reaches it, each outside the
        // loops walked to its next cut points
        self.point_at(k_e, comps, q0)?;
        let mut walked: Vec<Option<Seq>> = Vec::new();
        let mut sl: BTreeMap<u128, SLoop> = BTreeMap::new();
        let mut i = 0;
        while i < self.gref.as_ref().unwrap().points.len() {
            let p = self.gref.as_ref().unwrap().points[i].clone();
            if lps.heads.contains(&p.label) {
                // a head: its structured loop; its exits' points
                if sl.contains_key(&p.label) {
                    return Err(format!("loop {}: reached at two structured loops (not yet)", p.label));
                }
                let x = self.sloop(&p, i)?;
                for &e in &lps.exits[&p.label] {
                    let tmpl = self.exit_tmpl(&x);
                    let g = self.gref.as_mut().unwrap();
                    if g.points.iter().any(|q| q.label == e) {
                        return Err(format!("loop {}: its exit {} a cut point already", p.label, e));
                    }
                    g.points.push(GPoint { label: e, shape: vec![Sh::Free; comps.len()], tmpl });
                }
                sl.insert(p.label, x);
                walked.push(None);
            } else {
                let prem = self.pt_prem(&gs, i)?.1;
                self.gref.as_mut().unwrap().cur = p.label;
                walked.push(Some(self.sub_walk_hd(&prem)?));
                self.drop_caches();
            }
            self.trace(|| format!("ref: phase: point {} (label {}) walked", i, p.label));
            i += 1;
        }
        let _ = (lo, l0, w);
        Err("loops: not yet".into())
    }

    /// The structured loop at head point i (`y. mkprog(x0 x1. ex x2.
    /// while_rel(pair(x0, T), x. true, BS, TRS, x2) && K)`): its parts
    fn sloop(&mut self, p: &GPoint, i: usize) -> Result<SLoop, String> {
        let yv = self.var("sy");
        let t = p.tmpl.instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
        let m = self.app(&t, "mkprog", 1).ok_or("a head's program")?[0].clone();
        let (a, k) = block(self, &m).ok_or("a head's program: not a loop")?;
        let wr = self.app(&a, "while_rel", 5).ok_or("a head's program: not a loop")?.to_vec();
        let st = self.app(&wr[0], "pair", 2).ok_or("a head's loop state")?.to_vec();
        let ctx = ["x0", "x1", "x2", "x3", "x4"];
        let tt = self.lam(&st[1], &ctx[..3], &[]).ok_or("a head's loop state reads the program")?;
        let bs = self.lam(&wr[2], &ctx, &["x3", "x4"]).ok_or("a head's loop body reads the program")?;
        let trs = self.lam(&wr[3], &ctx[..4], &["x3"]).ok_or("a head's loop trace reads the program")?;
        let ks = self.lam(&k, &ctx[..3], &["x2", "x1"]).ok_or("a head's loop rest reads the world")?;
        if self.app(&wr[1], "true", 0).is_none() {
            return Err("a head's loop: its condition not true".into());
        }
        self.trace(|| format!("ref: point {} (label {}) a loop, its state's locals {}", i, p.label, self.print(&tt)));
        Ok(SLoop { y: yv, t: tt, bs, trs, ks })
    }

    /// an exit's program: the loop's rest after a `break` from the state of
    /// world x0 and locals T (`y. mkprog(x0 x1. K(exc(pair(x0, T), brk), x1))`)
    fn exit_tmpl(&mut self, x: &SLoop) -> Term {
        let (w0, o0) = (self.var("ew"), self.var("eo"));
        let brk = self.mk("pair", vec![Term::bytes(b"brk"), self.mk("empty", vec![])]);
        let e = self.mk("exc", vec![self.mk("pair", vec![w0.clone(), x.t.clone()]), brk]);
        let body = x.ks.instantiate_params(&[e, o0.clone()], &self.env.binders_fn());
        let q = self.mk("mkprog", vec![self.abs(&body, &[Self::var_id(&w0), Self::var_id(&o0)])]);
        self.abs(&q, &[Self::var_id(&x.y)])
    }

    /// a point's premise `all w y. A -> g.ref(L, Q, S)`, A decided (a
    /// head's `!hd(..)` false: the claim vacuous)
    fn sub_walk_hd(&mut self, prem: &Term) -> Result<Seq, String> {
        let mut cur = prem.clone();
        let mut vs = Vec::new();
        for nm in ["pw", "py"] {
            let b = self.app(&cur, "all", 1).ok_or("a point's premise: not all")?[0].clone();
            let n = self.fresh(nm);
            let v = self.var(&n);
            cur = b.instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
            vs.push(Self::var_id(&v));
        }
        let (hs, g) = self.imps(&cur);
        let [a] = hs.as_slice() else { return Err("a point's premise: not A -> g.ref".into()) };
        let pf = match self.decide(a) {
            Some((true, _)) => {
                let x = self.app(&g, "g.ref", 3).ok_or("a point's premise: not g.ref")?.to_vec();
                let qj = self.new_q(x[1].clone());
                let saved = self.w.clone();
                let r = self.walk(&x[0], qj, &x[2]);
                self.w = saved;
                self.evp(&RP::Taut(vec![R::S(r?)]), &cur, &[])?
            }
            Some((false, na)) => self.evp(&RP::Taut(vec![R::S(na)]), &cur, &[])?,
            None => return Err(format!("a point's premise undecided: {}", self.print(a))),
        };
        if std::env::var("C1_TRACE").is_ok() {
            for h in pf.hyps() {
                eprintln!("c1 ref: point walk hypothesis {}", Printer::new(self.env).short(h));
            }
        }
        self.close(pf, &[], &vs)
    }
}
