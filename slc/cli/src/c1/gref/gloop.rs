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
        let cut = GCut { v: rels.d.clone(), labels: labels.to_vec(), succ: succ.clone(), vm: None, hv: BTreeMap::new(), hm: BTreeMap::new(), ways: BTreeMap::new(), nmode: true, ufacts: Vec::new() };
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
        // the labels' ways: each label's block walked alone, its leaves' states
        // in v and the labels' facts N (V, N free meanwhile)
        let (vv, nv) = (self.env.new_var("gv", 1), self.env.new_var("gn", 2));
        self.gref.as_mut().unwrap().cut.as_mut().unwrap().vm = Some((vv, nv));
        let mut ways: BTreeMap<u128, Seq> = BTreeMap::new();
        for &kl in labels {
            self.gref.as_mut().unwrap().cur = kl;
            ways.insert(kl, self.label_ways(kl)?);
            self.drop_caches();
        }
        // (V v, N the labels' facts as g.ways_split has them: each
        // hypothesis proven -- a state's label by its disjunct, the facts by
        // evaluation -- and each label's ways discharged)
        let (wsr, wst) = self.inst("g.ways_split", &[("b", b.clone()), ("v", rels.v.clone()), ("pt", rels.pt.clone()), ("hd", rels.hd.clone()), ("xp", rels.xp.clone()), ("lp", rels.lp.clone()), ("m", rels.m.clone())])?;
        let (wps, _) = self.imps(&wst);
        let n_l = (|| {
            let t0 = self.app(&wps[0], "all", 1)?[0].clone();
            let (_, c) = self.imps(&t0);
            let t1 = self.app(&c, "all", 1)?[0].clone();
            let (_, c2) = self.imps(&t1);
            Some(self.app(&c2, "and", 2)?[1].clone())
        })()
        .ok_or("g.ways_split's labels' facts")?;
        let (hvm, hnm) = {
            let c = self.gref.as_ref().unwrap().cut.as_ref().unwrap();
            (c.hv.clone(), c.hm.clone())
        };
        let at = |g: &mut Self, h: &Term| -> Result<Term, String> {
            let a = g.assume(h)?;
            let a = Seq::inst(g.env, &a, vv, &rels.v).map_err(|e| e.0)?;
            Ok(Seq::inst(g.env, &a, nv, &n_l).map_err(|e| e.0)?.concl().clone())
        };
        let mut hps: Vec<(Term, Seq)> = Vec::new();
        for (k2, h) in hvm {
            let hi = at(self, &h)?;
            let (w2, y2) = (self.var("vw"), self.var("vy"));
            let x = self.mk("pair", vec![w2.clone(), self.mk("pair", vec![lit(k2), y2.clone()])]);
            let d = self.v_at(&x)?;
            let body = self.inst_alls(&hi, &[w2.clone(), y2.clone()])?;
            let pf = self.evp(&RP::Taut(vec![R::S(d)]), &body, &[])?;
            hps.push((hi, self.close(pf, &[], &[Self::var_id(&w2), Self::var_id(&y2)])?));
        }
        for (_, h) in hnm {
            let hi = at(self, &h)?;
            let vs: Vec<Term> = ["nw", "ny", "nw2", "ny2"].iter().map(|n| self.var(n)).collect();
            let body = self.inst_alls(&hi, &vs)?;
            let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &body, &[])?;
            hps.push((hi, self.close(pf, &[], &vs.iter().map(Self::var_id).collect::<Vec<_>>())?));
        }
        let mut done: BTreeMap<u128, Seq> = BTreeMap::new();
        for (kl, pf) in ways {
            let s0 = Seq::inst(self.env, &pf, vv, &rels.v).map_err(|e| e.0)?;
            let mut s0 = Seq::inst(self.env, &s0, nv, &n_l).map_err(|e| e.0)?;
            for (hi, hp) in &hps {
                if s0.hyps().contains(hi) {
                    let d = s0.discharge(self.env, hi).map_err(|e| e.0)?;
                    s0 = Seq::mp(self.env, &d, hp).map_err(|e| e.0)?;
                }
            }
            if !s0.hyps().is_empty() {
                return Err(format!("label {}'s ways: {} hypotheses left", kl, s0.hyps().len()));
            }
            done.insert(kl, s0);
        }
        self.trace(|| "ref: phase: the ways".into());
        let pw = self.lab_all(&wps[0], |g, k, pk| g.evp(&RP::Taut(vec![R::S(done[&k].clone())]), pk, &[]))?;
        // the body's effect (the C1 bookkeeping's lemmas)
        let se = {
            let mut eff = super::super::eff::Eff::new(self.env, "gloop")?;
            eff.body_seff(b)?
        };
        let pse = self.evp(&RP::Defs(Box::new(RP::By(R::S(se))), vec!["letin".into()]), &wps[1], &[])?;
        let steps = self.run(&mp(wsr, vec![s(&pw), s(&pse)]), &[])?;
        self.trace(|| "ref: phase: the steps".into());
        let _ = (lo, l0, w, walked, sl, steps);
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

    /// `x in univ(1)`: a term known there (the walk's), a pair, a pair's
    /// part, a number, a word (its width's bits)
    pub(super) fn univ_of(&mut self, x: &Term) -> Result<Seq, String> {
        if let Some((_, pf)) = self.gref.as_ref().and_then(|g| g.cut.as_ref()).and_then(|c| c.ufacts.iter().find(|(u, _)| u == x)) {
            return Ok(pf.clone());
        }
        if let Some(pr) = self.app(x, "pair", 2).map(|p| p.to_vec()) {
            let (a, b) = (self.univ_of(&pr[0])?, self.univ_of(&pr[1])?);
            return self.run(&mp(f("g.pair_univ"), vec![t(&pr[0]), t(&pr[1]), s(&a), s(&b)]), &[]);
        }
        for (nm, lemma) in [("fst", "tr.fst_univ"), ("snd", "g.snd_univ")] {
            if let Some(a) = self.app(x, nm, 1).map(|a| a[0].clone()) {
                let u = self.univ_of(&a)?;
                return self.run(&mp(f(lemma), vec![t(&a), s(&u)]), &[]);
            }
        }
        if self.app(x, "empty", 0).is_some() {
            return self.run(&R::Inst("univ_empty".into(), vec![("u", lit(1))]), &[]);
        }
        let within = |g: &mut Self, set: Term, inr: R, setu: R| -> Result<Seq, String> {
            let i = g.run(&inr, &[])?;
            g.run(&mp(R::Inst("univ_trans".into(), vec![("u", lit(1)), ("a", x.clone()), ("b", set)]), vec![p(setu), s(&i)]), &[])
        };
        if nat(x).is_some() {
            let om = self.mk("omega", vec![]);
            let goal = self.mk("in", vec![x.clone(), om.clone()]);
            let io = self.evp(&RP::Simp(false, vec![], vec![], false), &goal, &[])?;
            return within(self, om, R::S(io), f("omega_univ"));
        }
        // (a word: in its width's bits)
        let typed = if let Some(name) = ["bits_add", "bits_sub", "bits_mul", "bits_neg", "bits_of_int", "bits_sext"].into_iter().find(|n| self.head_is(x, n)) {
            let Node::App(_, a) = x.node() else { unreachable!() };
            let lemma = match name {
                "bits_add" => "nf.add_in",
                "bits_sub" => "nf.sub_in",
                "bits_mul" => "nf.mul_in",
                "bits_neg" => "nf.neg_in",
                "bits_of_int" => "nf.of_int_in",
                _ => "nf.sext_in",
            };
            let n = if name == "bits_sext" { a[1].clone() } else { a[0].clone() };
            let mut args: Vec<RA> = a.iter().map(t).collect();
            args.push(simp0());
            Some((n, mp(f(lemma), args)))
        } else if let Some(name) = ["bits_and", "bits_or", "bits_xor"].into_iter().find(|n| self.head_is(x, n)) {
            let Node::App(_, a) = x.node() else { unreachable!() };
            Some((a[0].clone(), mp(R::Inst(format!("{}_in", name), vec![("n", a[0].clone()), ("x", a[1].clone()), ("y", a[2].clone())]), vec![simp0()])))
        } else {
            None
        };
        if let Some((n, r)) = typed {
            let bits = self.mk("bits", vec![n.clone()]);
            return within(self, bits, r, R::Inst("bits_univ".into(), vec![("n", n)]));
        }
        Err(format!("not known in univ(1): {}", self.print(x)))
    }

    /// `all x1 .. xn. B` at the terms ts: B
    fn inst_alls(&self, t: &Term, ts: &[Term]) -> Result<Term, String> {
        let mut cur = t.clone();
        for x in ts {
            let b = self.app(&cur, "all", 1).ok_or("not all")?[0].clone();
            cur = b.instantiate_params(std::slice::from_ref(x), &self.env.binders_fn());
        }
        Ok(cur)
    }

    /// `all l. v(l) -> G(l)` (v: in univ(1), of a label) from each label's
    /// claim `all w y. pair(w, pair(k, y)) in univ(1) -> G(pair(w, pair(k,
    /// y)))` (`per`, given it to prove), by g.lab_pt, g.lab_or, g.lab_univ
    fn lab_all(&mut self, prem: &Term, mut per: impl FnMut(&mut Self, u128, &Term) -> Result<Seq, String>) -> Result<Seq, String> {
        let body = self.app(prem, "all", 1).ok_or("a premise over the labels")?[0].clone();
        let (hs, gl) = self.imps(&body);
        if hs.len() != 1 {
            return Err("a premise over the labels: not v -> ..".into());
        }
        let u = self.mk("in", vec![Term::bvar(0), self.mk("univ", vec![lit(1)])]);
        let gp = Term::app(self.env.builtins.imp, vec![u, gl.clone()]);
        let (d, labels) = {
            let c = self.gref.as_ref().unwrap().cut.as_ref().unwrap();
            (c.v.clone(), c.labels.clone())
        };
        let mut disj = Vec::new();
        let mut cur = d.clone();
        while let Some(o) = self.app(&cur, "or", 2).map(|o| o.to_vec()) {
            disj.push((o[0].clone(), o[1].clone()));
            cur = o[1].clone();
        }
        if disj.len() != labels.len() {
            return Err("v's disjuncts not the labels".into());
        }
        let mut acc = self.run(&R::Inst("g.lab_none".into(), vec![("G", gp.clone())]), &[])?;
        for i in (0..labels.len()).rev() {
            let (r, st) = self.inst("g.lab_pt", &[("G", gp.clone()), ("k", lit(labels[i]))])?;
            let (ps, _) = self.imps(&st);
            self.gref.as_mut().unwrap().cur = labels[i];
            let pf = per(self, labels[i], &ps[0])?;
            let one = self.run(&mp(r, vec![s(&pf)]), &[])?;
            acc = self.run(&mp(R::Inst("g.lab_or".into(), vec![("G", gp.clone()), ("A", disj[i].0.clone()), ("B", disj[i].1.clone())]), vec![s(&one), s(&acc)]), &[])?;
        }
        let r = self.run(&mp(R::Inst("g.lab_univ".into(), vec![("G", gl), ("D", d)]), vec![s(&acc)]), &[])?;
        self.evp(&RP::Taut(vec![R::S(r)]), prem, &[])
    }

    /// a label's claim (lab_all's) by evaluation
    fn lab_simp(&mut self, pk: &Term) -> Result<Seq, String> {
        let (w, y) = (self.var("sw"), self.var("sy"));
        let body = self.inst_alls(pk, &[w.clone(), y.clone()])?;
        let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &body, &[])?;
        self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
    }

    fn head_is(&self, x: &Term, name: &str) -> bool {
        matches!(x.node(), Node::App(s, _) if self.env.syms[*s as usize].name == name)
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
