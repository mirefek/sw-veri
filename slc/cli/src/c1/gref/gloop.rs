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
    // (a label only the loop leads to, every way from it a return or on in
    // the loop: the loop's too -- a return from inside the structured loop,
    // not an exit to the code after it)
    loop {
        let mut grew = false;
        for bs in body.values_mut() {
            for &x in labels {
                if bs.contains(&x) {
                    continue;
                }
                let ps = preds.get(&x).cloned().unwrap_or_default();
                let only_in = !ps.is_empty() && ps.iter().all(|p| bs.contains(p));
                let returns = succ.get(&x).is_some_and(|ss| ss.iter().all(|s| s.is_none_or(|s| bs.contains(&s))));
                if only_in && returns {
                    bs.insert(x);
                    grew = true;
                }
            }
        }
        if !grew {
            break;
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
            // (another loop's head: a loop after the loop)
            if lp.get(&e).is_some_and(|&h2| h2 != e) {
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
        self.phase(|| format!("ref: loops at {:?}, exits {:?}, cut at {:?}", lps.heads, lps.exits, lps.cuts));
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
                    // (an exit that is the next loop's head: the rest at the
                    // break folded, the next loop then on top)
                    let tmpl = if lps.heads.contains(&e) { self.red_t(&tmpl, &mut Default::default()) } else { tmpl };
                    // (an exit already a cut point -- two ways meeting there:
                    // the same program from both, folded)
                    if let Some(q) = self.gref.as_ref().unwrap().points.iter().find(|q| q.label == e).cloned() {
                        let mut memo = Default::default();
                        let (a1, a2) = (self.red_t(&tmpl, &mut memo), self.red_t(&q.tmpl, &mut memo));
                        if a1 == a2 {
                            continue;
                        }
                        // (the two templates, functions of the locals)
                        let _ = std::fs::write(format!("{}/exit_new.txt", std::env::var("TMPDIR").unwrap_or("/tmp".into())), self.lambda(1, &a1));
                        let _ = std::fs::write(format!("{}/exit_old.txt", std::env::var("TMPDIR").unwrap_or("/tmp".into())), self.lambda(1, &a2));
                        return Err(format!("loop {}: its exit {} a cut point already, of another program", p.label, e));
                    }
                    let g = self.gref.as_mut().unwrap();
                    g.points.push(GPoint { label: e, shape: vec![Sh::Free; comps.len()], tmpl });
                }
                // (debugging: the trip of this head walked now, alone)
                if std::env::var("C1_REF_TRIP_EARLY").ok().and_then(|v| v.parse::<u128>().ok()) == Some(p.label) {
                    let (hv, xv, y2, x9v, ov) = (self.var("lh"), self.var("lx"), self.var("ly"), self.var("lx9"), self.var("lo"));
                    let ssx = self.mk("snd", vec![self.mk("snd", vec![xv.clone()])]);
                    let tx = x.t.subst_var(Self::var_id(&x.y), &ssx, &self.env.binders_fn());
                    let h1 = self.abs(&self.mk("pair", vec![self.mk("fst", vec![xv.clone()]), tx]), &[Self::var_id(&hv), Self::var_id(&xv)]);
                    let b1 = self.abs(&x.bs.instantiate_params(&[xv.clone(), y2.clone()], &self.env.binders_fn()), &[Self::var_id(&hv), Self::var_id(&xv), Self::var_id(&y2)]);
                    let k1 = self.abs(&x.ks.instantiate_params(&[x9v.clone(), ov.clone()], &self.env.binders_fn()), &[Self::var_id(&hv), Self::var_id(&x9v), Self::var_id(&ov)]);
                    let (h1_0, b1_0, k1_0) = (h1.clone(), b1.clone(), k1.clone());
                    let (_, st1) = self.inst("g.cut_loops", &binds(inv_v.clone(), h1, b1, x.trs.clone(), k1))?;
                    let pk1 = self.lab_prem(&self.imps(&st1).0[12], p.label)?;
                    if let Ok(d) = std::env::var("C1_DUMP") {
                        let yv = self.var("dy");
                        for q in &self.gref.as_ref().unwrap().points {
                            let tq = q.tmpl.instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
                            let _ = std::fs::write(format!("{}/point_{}.txt", d, q.label), self.print(&tq));
                        }
                    }
                    sl.insert(p.label, x);
                    let inv = self.points_inv();
                    let lab = p.label;
                    self.at_free_inv(iv, &inv_v, &inv, |g| g.trip_claim(&pk1, lab))?;
                    // (and its exits, at the points' INV so far)
                    let (h2, b2, k2) = (h1_0, b1_0, k1_0);
                    let (_, st2) = self.inst("g.cut_loops", &binds(inv.clone(), h2, b2, sl[&lab].trs.clone(), k2))?;
                    {
                        let g = self.gref.as_mut().unwrap();
                        g.inv = inv.clone();
                        g.inv_var = None;
                    }
                    for &e in &lps.exits[&lab] {
                        let pk2 = self.lab_prem(&self.imps(&st2).0[13], e)?;
                        self.exit_claim(&pk2, e).map_err(|x| format!("early exit {}: {}", e, x))?;
                        self.phase(|| format!("ref: phase: loop {}'s exit {} (C1_REF_TRIP_EARLY)", lab, e));
                    }
                    let ps2 = self.imps(&st2).0;
                    self.all_refute(&ps2[14]).map_err(|x| format!("early rest 14: {}", x))?;
                    self.phase(|| "ref: phase: rest 14 (C1_REF_TRIP_EARLY)".into());
                    self.all_simp(&ps2[16], 3).map_err(|x| format!("early rest 16: {}", x))?;
                    self.phase(|| "ref: phase: rest 16 (C1_REF_TRIP_EARLY)".into());
                    self.all_simp(&ps2[17], 2).map_err(|x| format!("early rest 17: {}", x))?;
                    self.phase(|| "ref: phase: rest 17 (C1_REF_TRIP_EARLY)".into());
                    return Err(format!("loop {}'s trip walked (C1_REF_TRIP_EARLY)", p.label));
                }
                sl.insert(p.label, x);
                walked.push(None);
            } else {
                let prem = self.pt_prem(&gs, i)?.1;
                self.gref.as_mut().unwrap().cur = p.label;
                walked.push(Some(self.sub_walk_hd(&prem)?));
                self.drop_caches();
            }
            self.phase(|| format!("ref: phase: point {} (label {}) walked", i, p.label));
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
            let pf = self.run(&mp(R::Inst("g.v_intro".into(), vec![("D", rels.d.clone()), ("x", x.clone())]), vec![s(&d)]), &[])?;
            let _ = body;
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
            // (the parameters in the universe: the refinement's own
            // hypotheses, discharged at the wrapper's arguments)
            let univ1 = self.mk("univ", vec![lit(1)]);
            let param_h = |g: &Self, h: &Term| g.params.iter().any(|p| *h == g.mk("in", vec![p.clone(), univ1.clone()]));
            if !s0.hyps().iter().all(|h| param_h(self, h)) {
                let hs: Vec<String> = s0.hyps().iter().map(|h| self.print(h)).collect();
                return Err(format!("label {}'s ways: {} hypotheses left: {}", kl, s0.hyps().len(), hs.join("; ")));
            }
            done.insert(kl, s0);
        }
        self.phase(|| "ref: phase: the ways".into());
        let pw = self.lab_all(&wps[0], |g, k, pk| g.evp(&RP::Taut(vec![R::S(done[&k].clone())]), pk, &[]))?;
        // the body's effect (the C1 bookkeeping's lemmas)
        let se = {
            let mut eff = super::super::eff::Eff::new(self.env, "gloop")?;
            eff.body_seff(b)?
        };
        let pse = self.evp(&RP::Defs(Box::new(RP::By(R::S(se))), vec!["letin".into()]), &wps[1], &[])?;
        let steps = self.run(&mp(wsr, vec![s(&pw), s(&pse)]), &[])?;
        self.phase(|| "ref: phase: the steps".into());
        // INV the points' disjunction: each hypothesis proven, each walk's
        // discharged
        if sl.is_empty() {
            return Err("no loop reached".into());
        }
        let inv = self.points_inv();
        {
            let g = self.gref.as_mut().unwrap();
            g.inv = inv.clone();
            g.inv_var = None;
        }
        let n = self.gref.as_ref().unwrap().points.len();
        let mut hps: Vec<(Term, Seq)> = Vec::new();
        for j in 0..n {
            let Some(Some(h)) = self.gref.as_ref().unwrap().hyps.get(j).cloned() else { continue };
            let a = self.assume(&h)?;
            let hj = Seq::inst(self.env, &a, iv, &inv).map_err(|e| e.0)?.concl().clone();
            hps.push((hj, self.hyp_proof(j, &inv)?));
        }
        let mut walked2: Vec<Option<Seq>> = Vec::new();
        for w0 in walked {
            let Some(w0) = w0 else {
                walked2.push(None);
                continue;
            };
            let mut s0 = Seq::inst(self.env, &w0, iv, &inv).map_err(|e| e.0)?;
            for (hj, pf) in &hps {
                if s0.hyps().contains(hj) {
                    let d = s0.discharge(self.env, hj).map_err(|e| e.0)?;
                    s0 = Seq::mp(self.env, &d, pf).map_err(|e| e.0)?;
                }
            }
            if !s0.hyps().is_empty() {
                return Err(format!("a cut point's walk: {} hypotheses left", s0.hyps().len()));
            }
            walked2.push(Some(s0));
        }
        // the structured loops: H a state's (its world, the loop's locals),
        // its body, trace, rest -- each a case on the head h (one loop: its
        // own), the trace the loops' one
        let (hv, xv, y2, x9v, ov) = (self.var("lh"), self.var("lx"), self.var("ly"), self.var("lx9"), self.var("lo"));
        let ssx = self.mk("snd", vec![self.mk("snd", vec![xv.clone()])]);
        let trs = sl.values().next().unwrap().trs.clone();
        if let Some((k, _)) = sl.iter().find(|(_, x)| x.trs != trs) {
            return Err(format!("loop {}: its trace not the other loops'", k));
        }
        let mut parts: Vec<(u128, Term, Term, Term)> = Vec::new();
        for (&k, x) in &sl {
            let tx = x.t.subst_var(Self::var_id(&x.y), &ssx, &self.env.binders_fn());
            let bs = x.bs.instantiate_params(&[xv.clone(), y2.clone()], &self.env.binders_fn());
            let ks = x.ks.instantiate_params(&[x9v.clone(), ov.clone()], &self.env.binders_fn());
            parts.push((k, tx, bs, ks));
        }
        let fx = self.mk("fst", vec![xv.clone()]);
        let lams = |g: &Self, tx: Term, bs: Term, ks: Term| {
            (
                g.abs(&g.mk("pair", vec![fx.clone(), tx]), &[Self::var_id(&hv), Self::var_id(&xv)]),
                g.abs(&bs, &[Self::var_id(&hv), Self::var_id(&xv), Self::var_id(&y2)]),
                g.abs(&ks, &[Self::var_id(&hv), Self::var_id(&x9v), Self::var_id(&ov)]),
            )
        };
        // (`ite(h = k1, T1, ite(h = k2, ..))`, the last loop's the rest)
        let (mut tc, mut bc, mut kc) = {
            let l = parts.last().unwrap();
            (l.1.clone(), l.2.clone(), l.3.clone())
        };
        for (k, tx, bs, ks) in parts.iter().rev().skip(1) {
            let c = self.mk("eq", vec![hv.clone(), lit(*k)]);
            tc = self.mk("ite", vec![c.clone(), tx.clone(), tc]);
            bc = self.mk("ite", vec![c.clone(), bs.clone(), bc]);
            kc = self.mk("ite", vec![c, ks.clone(), kc]);
        }
        let case_ks: Vec<u128> = parts.iter().map(|p| p.0).collect();
        let (h_l, bs_l, ks_l) = lams(self, tc, bc, kc);
        let (rr, stmt) = self.inst("g.cut_loops", &binds(inv.clone(), h_l, bs_l, trs.clone(), ks_l))?;
        let (prems, _) = self.imps(&stmt);
        // (each loop's own premises, when more: the cases proven there and
        // bridged by evaluation)
        let multi = sl.len() > 1;
        let mut own: BTreeMap<u128, Vec<Term>> = BTreeMap::new();
        if multi {
            for (k, tx, bs, ks) in &parts {
                let (h1, b1, k1) = lams(self, tx.clone(), bs.clone(), ks.clone());
                let (_, st1) = self.inst("g.cut_loops", &binds(inv.clone(), h1, b1, trs.clone(), k1))?;
                own.insert(*k, self.imps(&st1).0);
            }
        }
        let owner: BTreeMap<u128, u128> = lps.exits.iter().flat_map(|(h, es)| es.iter().map(move |e| (*e, *h))).collect();
        if owner.len() != lps.exits.values().map(|es| es.len()).sum::<usize>() {
            return Err("an exit of two loops (not yet)".into());
        }
        let mut pfs: Vec<Seq> = Vec::new();
        for i in [0, 1] {
            pfs.push(self.evp(&RP::Taut(vec![R::S(steps.clone())]), &prems[i], &[])?);
        }
        self.phase(|| "ref: phase: the rank".into());
        pfs.push(self.lab_all(&prems[2], |g, _, pk| g.lab_simp(pk))?);
        let mt = self.app(&rels.m, "app", 2).ok_or("the rank's table")?[0].clone();
        let ml = self.run(&R::Inst("g.ml_label".into(), vec![("v", rels.v.clone()), ("t", mt)]), &[])?;
        pfs.push(self.evp(&RP::Taut(vec![R::S(ml)]), &prems[3], &[])?);
        self.phase(|| "ref: phase: the heads".into());
        pfs.push(self.lab_all(&prems[4], |g, _, pk| g.lab_simp(pk))?);
        for i in [5, 6] {
            pfs.push(self.evp(&RP::Taut(vec![R::S(steps.clone())]), &prems[i], &[])?);
        }
        pfs.push(self.all_simp(&prems[7], 2)?);
        self.phase(|| "ref: phase: the points' states".into());
        let (rels_pt, rels_d) = (rels.pt.clone(), rels.d.clone());
        pfs.push(self.pts_all(&prems[8], |g, i, pk| {
            let (w, y) = (g.var("vw"), g.var("vy"));
            let st = g.point_state(i, &w, &y);
            let d = g.v_at(&st)?;
            let ptt = rels_pt.instantiate_params(std::slice::from_ref(&st), &g.env.binders_fn());
            let pp = g.evp(&RP::Simp(false, vec![], vec![], false), &ptt, &[])?;
            let pf = g.run(&mp(R::Inst("g.vpt_intro".into(), vec![("D", rels_d.clone()), ("P", rels_pt.clone()), ("x", st.clone())]), vec![s(&d), s(&pp)]), &[])?;
            let _ = pk;
            g.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
        })?);
        pfs.push(self.pts_all(&prems[9], |g, _, pk| g.lab_simp(pk))?);
        self.phase(|| "ref: phase: the points' walks".into());
        pfs.push(self.pts_all(&prems[10], |g, i, pk| match &walked2[i] {
            Some(s0) => g.evp(&RP::Taut(vec![R::S(s0.clone())]), pk, &[]),
            None => g.sub_walk_hd(pk),
        })?);
        self.phase(|| "ref: phase: the heads' programs".into());
        pfs.push(self.pts_all(&prems[11], |g, i, pk| {
            let k = g.gref.as_ref().unwrap().points[i].label;
            if !sl.contains_key(&k) {
                return g.vacuous(pk, 2, 0);
            }
            if !multi {
                return g.head_prog(i, pk);
            }
            let pk1 = g.pt_prem(&g.claim_g(&own[&k][11])?, i)?.1;
            let p1 = g.head_prog(i, &pk1)?;
            let (w, y) = (g.var("uw"), g.var("uy"));
            let body = g.inst_alls(pk, &[w.clone(), y.clone()])?;
            let p1 = g.run(&mp(R::S(p1), vec![t(&w), t(&y)]), &[])?;
            let conds = g.decided_conds(&body, &case_ks)?;
            let pf = g.uncase(&body, &p1, &conds)?;
            g.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
        })?);
        self.phase(|| "ref: phase: the trips".into());
        pfs.push(self.lab_all(&prems[12], |g, k, pk| {
            if !sl.contains_key(&k) {
                return g.vacuous(pk, 2, 1);
            }
            if !multi {
                return g.trip_claim(pk, k);
            }
            // (the loop's own trip, walked at the free INV; then at the cases)
            let pk1 = g.lab_prem(&own[&k][12], k)?;
            let p1 = g.at_free_inv(iv, &inv_v, &inv, |g| g.trip_claim(&pk1, k))?;
            g.phase(|| format!("ref: phase: loop {}'s trip walked", k));
            g.case_at(pk, &p1, k, &case_ks)
        })?);
        self.phase(|| "ref: phase: the exits".into());
        pfs.push(self.lab_all(&prems[13], |g, k, pk| {
            let Some(&h) = owner.get(&k) else { return g.vacuous(pk, 2, 1) };
            if !multi {
                return g.exit_claim(pk, k);
            }
            let pk1 = g.lab_prem(&own[&h][13], k)?;
            let p1 = g.exit_claim(&pk1, k).map_err(|e| format!("exit {} of loop {}, its own claim: {}", k, h, e))?;
            g.case_at(pk, &p1, h, &case_ks).map_err(|e| format!("exit {} of loop {}, at the cases: {}", k, h, e))
        })?);
        self.phase(|| "ref: phase: the rests".into());
        if multi {
            let (mut r14, mut r16, mut r17) = (Vec::new(), Vec::new(), Vec::new());
            for k in &case_ks {
                let ps = &own[k];
                r14.push(self.all_refute(&ps[14])?);
                r16.push(self.all_simp(&ps[16], 3)?);
                r17.push(self.all_simp(&ps[17], 2)?);
            }
            pfs.push(self.case_split(&prems[14], &r14, &case_ks, 3)?);
            pfs.push(self.all_refute(&prems[15])?);
            pfs.push(self.case_split(&prems[16], &r16, &case_ks, 3)?);
            pfs.push(self.case_split(&prems[17], &r17, &case_ks, 2)?);
        } else {
            for i in [14, 15] {
                pfs.push(self.all_refute(&prems[i])?);
            }
            pfs.push(self.all_simp(&prems[16], 3)?);
            pfs.push(self.all_simp(&prems[17], 2)?);
        }
        pfs.push(self.univ_hu(&prems[18])?);
        pfs.push(self.univ_htu(&prems[19])?);
        let main = self.run(&mp(rr, pfs.iter().map(s).collect()), &[])?;
        self.phase(|| "ref: phase: done".into());
        // at the loop's start: its point, its state in univ(1) (its world the
        // outcome's, its locals the walk's choices)
        let i0 = self.inv_at(l0, q0)?;
        let (rv, ov) = (self.var("lr"), self.var("lo"));
        let fl0 = self.mk("fst", vec![l0.clone()]);
        let hu_t = self.mk("in", vec![self.mk("pair", vec![fl0.clone(), ov.clone()]), self.mk("univ", vec![lit(1)])]);
        let hu = self.assume(&hu_t)?;
        let fu = self.run(&mp(f("g.univ_fst"), vec![t(&fl0), t(&ov), s(&hu)]), &[])?;
        let l0p = self.app(l0, "pair", 2).ok_or("the loop's start not a pair")?.to_vec();
        let wu_t = self.mk("in", vec![l0p[0].clone(), self.mk("univ", vec![lit(1)])]);
        let wu = self.evp(&RP::Simp(false, vec![R::S(fu)], vec![], false), &wu_t, &[])?;
        self.gref.as_mut().unwrap().cut.as_mut().unwrap().ufacts = vec![(l0p[0].clone(), wu)];
        let ul0 = self.univ_of(l0)?;
        let c1 = self.run(&mp(R::S(main), vec![t(l0), t(q0), t(&rv), t(&ov), s(&i0), s(&ul0)]), &[])?;
        let target = c1.concl().clone();
        let c1 = self.close(c1, &[hu_t], &[])?;
        let c1 = self.evp(&RP::Taut(vec![R::S(c1)]), &target, &[])?;
        let c1 = self.close(c1, &[], &[Self::var_id(&rv), Self::var_id(&ov)])?;
        let c2 = self.run(&mp(R::Inst("g.ref_cfg".into(), vec![("l", l0.clone()), ("q", q0.clone()), ("b", b.clone()), ("tr", tr.clone()), ("k", kk.clone())]), vec![s(&c1)]), &[])?;
        self.gref = None;
        if l0p[0] != *w {
            return Err(format!("the loop's start world {}: not the walk's", self.print(&l0p[0])));
        }
        let fe = R::Inst("fst_pair".into(), vec![("a", l0p[0].clone()), ("b", l0p[1].clone())]);
        self.run(&mp(R::Inst("g.ref_ws".into(), vec![("l", lo.clone()), ("q", q0.clone()), ("a", fl0), ("b", w.clone())]), vec![p(fe), s(&c2)]), &[])
    }

    /// The structured loop at head point i (`y. mkprog(x0 x1. ex x2.
    /// while_rel(pair(x0, T), x. true, BS, TRS, x2) && K)`): its parts
    fn sloop(&mut self, p: &GPoint, i: usize) -> Result<SLoop, String> {
        let yv = self.var("sy");
        let t = p.tmpl.instantiate_params(std::slice::from_ref(&yv), &self.env.binders_fn());
        let m = self.app(&t, "mkprog", 1).ok_or("a head's program")?[0].clone();
        let (a, k) = block(self, &m).ok_or_else(|| format!("a head's program: not a loop: {}", self.print(&t)))?;
        // (the loop first in a block -- `ex x2. ((ex x3. while_rel(.., x3)
        // && C) && K)`: the loop at x3, its rest `ex z. C(x9, z) && K(z, o)`,
        // the head's program by g.ex_reassoc)
        let nested = if self.app(&a, "while_rel", 5).is_none() { block(self, &a).filter(|(w, _)| self.app(w, "while_rel", 5).is_some()) } else { None };
        let (wr, ctx, tt, bs, trs, ks): (Vec<Term>, Vec<&str>, Term, Term, Term, Term) = if let Some((w, c)) = nested {
            let wr = self.app(&w, "while_rel", 5).unwrap().to_vec();
            let st = self.app(&wr[0], "pair", 2).ok_or("a head's loop state")?.to_vec();
            let ctx = vec!["x0", "x1", "x2", "x3", "x4", "x5"];
            let tt = self.lam(&st[1], &ctx[..4], &[]).ok_or("a head's loop state reads the program")?;
            let bs = self.lam(&wr[2], &ctx, &["x4", "x5"]).ok_or("a head's loop body reads the program")?;
            let trs = self.lam(&wr[3], &ctx[..5], &["x4"]).ok_or("a head's loop trace reads the program")?;
            // (C over the loop's outcome x3 and the block's x2; K over x2 and o)
            let cl = self.lam(&c, &ctx[..4], &["x3", "x2"]).ok_or("a head's loop's block rest reads the world")?;
            let kl = self.lam(&k, &ctx[..3], &["x2", "x1"]).ok_or("a head's loop rest reads the world")?;
            // (in `x9 o. ex z. ..`: x9 BVar(2), o BVar(1), z BVar(0))
            let ci = cl.instantiate_params(&[Term::bvar(2), Term::bvar(0)], &self.env.binders_fn());
            let ki = kl.instantiate_params(&[Term::bvar(0), Term::bvar(1)], &self.env.binders_fn());
            let ks = self.mk("ex", vec![self.mk("and", vec![ci, ki])]);
            (wr, ctx, tt, bs, trs, ks)
        } else {
            let wr = self.app(&a, "while_rel", 5).ok_or_else(|| format!("a head's program: not a loop: {}", self.print(&t)))?.to_vec();
            let st = self.app(&wr[0], "pair", 2).ok_or("a head's loop state")?.to_vec();
            let ctx = vec!["x0", "x1", "x2", "x3", "x4"];
            let tt = self.lam(&st[1], &ctx[..3], &[]).ok_or("a head's loop state reads the program")?;
            let bs = self.lam(&wr[2], &ctx, &["x3", "x4"]).ok_or("a head's loop body reads the program")?;
            let trs = self.lam(&wr[3], &ctx[..4], &["x3"]).ok_or("a head's loop trace reads the program")?;
            let ks = self.lam(&k, &ctx[..3], &["x2", "x1"]).ok_or("a head's loop rest reads the world")?;
            (wr, ctx, tt, bs, trs, ks)
        };
        let _ = &ctx;
        if self.app(&wr[1], "true", 0).is_none() {
            return Err("a head's loop: its condition not true".into());
        }
        self.trace(|| format!("ref: point {} (label {}) a loop, its state's locals {}", i, p.label, self.print(&tt)));
        Ok(SLoop { y: yv, t: tt, bs, trs, ks })
    }

    /// t with its decided parts folded: an outcome's tag and parts
    /// (`fst(exc(..))` 1, `out_state(exc(s, v))` s), a pair's projections, an
    /// equation of literals, `ite` on a decided condition, the boolean
    /// constants. A template's form, not a fact: wherever it stands for t
    /// the claim is bridged by evaluation (`simp`).
    pub(super) fn red_t(&self, t: &Term, memo: &mut std::collections::HashMap<Term, Term>) -> Term {
        if let Some(r) = memo.get(t) {
            return r.clone();
        }
        let r = match t.node() {
            Node::App(f, a) if !a.is_empty() => {
                let a2: Vec<Term> = a.iter().map(|x| self.red_t(x, memo)).collect();
                let t2 = t.with_args(a2.clone());
                let name = self.env.syms[*f as usize].name.clone();
                let tagged = |x: &Term| -> Option<(u128, Vec<Term>)> {
                    let Node::App(g, b) = x.node() else { return None };
                    let k = match (self.env.syms[*g as usize].name.as_str(), b.len()) {
                        ("ok", 2) => 0,
                        ("exc", 2) => 1,
                        ("diverge", 1) => 2,
                        _ => return None,
                    };
                    Some((k, b.to_vec()))
                };
                let tt = self.mk("true", vec![]);
                let ff = self.mk("false", vec![]);
                let is = |x: &Term, n: &str| matches!(x.node(), Node::App(g, b) if b.is_empty() && self.env.syms[*g as usize].name == n);
                match (name.as_str(), a2.len()) {
                    ("fst", 1) => match tagged(&a2[0]) {
                        Some((k, _)) => lit(k),
                        None => self.app(&a2[0], "pair", 2).map(|p| p[0].clone()).unwrap_or(t2),
                    },
                    ("snd", 1) => self.app(&a2[0], "pair", 2).map(|p| p[1].clone()).unwrap_or(t2),
                    ("out_state", 1) => match tagged(&a2[0]) {
                        Some((k, b)) if k < 2 => b[0].clone(),
                        _ => t2,
                    },
                    ("out_value", 1) => match tagged(&a2[0]) {
                        Some((k, b)) if k < 2 => b[1].clone(),
                        _ => t2,
                    },
                    ("eq", 2) => match (a2[0].node(), a2[1].node()) {
                        (Node::Nat(x), Node::Nat(y)) => if x == y { tt } else { ff },
                        (Node::Bytes(x), Node::Bytes(y)) => if x == y { tt } else { ff },
                        _ => t2,
                    },
                    ("and", 2) => {
                        if is(&a2[0], "false") || is(&a2[1], "false") {
                            ff
                        } else if is(&a2[0], "true") {
                            a2[1].clone()
                        } else if is(&a2[1], "true") {
                            a2[0].clone()
                        } else {
                            t2
                        }
                    }
                    ("or", 2) => {
                        if is(&a2[0], "true") || is(&a2[1], "true") {
                            tt
                        } else if is(&a2[0], "false") {
                            a2[1].clone()
                        } else if is(&a2[1], "false") {
                            a2[0].clone()
                        } else {
                            t2
                        }
                    }
                    ("not", 1) => {
                        if is(&a2[0], "true") {
                            ff
                        } else if is(&a2[0], "false") {
                            tt
                        } else {
                            t2
                        }
                    }
                    ("ite", 3) => {
                        if is(&a2[0], "true") {
                            a2[1].clone()
                        } else if is(&a2[0], "false") {
                            a2[2].clone()
                        } else {
                            t2
                        }
                    }
                    // (a witness not mentioned: the body alone)
                    ("ex", 1) if !self.occurs_bv(&a2[0], 0) => self.lower_bv(&a2[0], 0),
                    // (a witness given: `ex x. x = v && K(x)` is K(v) -- a
                    // block that only passes its outcome on, as an `if`'s end)
                    ("ex", 1) if self.one_point(&a2[0]).is_some() => {
                        let (v, k) = self.one_point(&a2[0]).unwrap();
                        let k2 = self.subst_bv(&k, 0, &v);
                        self.red_t(&k2, memo)
                    }
                    _ => t2,
                }
            }
            _ => t.clone(),
        };
        memo.insert(t.clone(), r.clone());
        r
    }

    /// an existential's body `x = v && K` (x bound variable 0, not in v):
    /// v outside the binder, K
    fn one_point(&self, b: &Term) -> Option<(Term, Term)> {
        let x = self.app(b, "and", 2)?;
        let e = self.app(&x[0], "eq", 2)?;
        (matches!(e[0].node(), Node::BVar(0)) && !self.occurs_bv(&e[1], 0)).then(|| (self.lower_bv(&e[1], 0), x[1].clone()))
    }

    /// t with bound variable `d` (at this depth) v (a term outside the
    /// binder: its loose variables raised by the depth), those above d one
    /// lower
    fn subst_bv(&self, t: &Term, d: u32, v: &Term) -> Term {
        match t.node() {
            Node::BVar(i) if *i == d => self.shift_bv(v, 0, d),
            Node::BVar(i) if *i > d => Term::bvar(i - 1),
            Node::App(f, a) => t.with_args(a.iter().enumerate().map(|(i, x)| self.subst_bv(x, d + self.env.syms[*f as usize].binders[i], v)).collect()),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.subst_bv(x, d, v)).collect()),
            _ => t.clone(),
        }
    }

    /// t's bound variables from `c` up raised by k
    fn shift_bv(&self, t: &Term, c: u32, k: u32) -> Term {
        if k == 0 {
            return t.clone();
        }
        match t.node() {
            Node::BVar(i) if *i >= c => Term::bvar(i + k),
            Node::App(f, a) => t.with_args(a.iter().enumerate().map(|(i, x)| self.shift_bv(x, c + self.env.syms[*f as usize].binders[i], k)).collect()),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.shift_bv(x, c, k)).collect()),
            _ => t.clone(),
        }
    }

    /// bound variable `d` (at this depth) occurs in t
    fn occurs_bv(&self, t: &Term, d: u32) -> bool {
        match t.node() {
            Node::BVar(i) => *i == d,
            Node::App(f, a) => a.iter().enumerate().any(|(i, x)| self.occurs_bv(x, d + self.env.syms[*f as usize].binders[i])),
            Node::Var(_, a) => a.iter().any(|x| self.occurs_bv(x, d)),
            _ => false,
        }
    }

    /// t with bound variable `d` (not occurring) removed: those above it
    /// one lower
    fn lower_bv(&self, t: &Term, d: u32) -> Term {
        match t.node() {
            Node::BVar(i) if *i > d => Term::bvar(i - 1),
            Node::App(f, a) => t.with_args(a.iter().enumerate().map(|(i, x)| self.lower_bv(x, d + self.env.syms[*f as usize].binders[i])).collect()),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.lower_bv(x, d)).collect()),
            _ => t.clone(),
        }
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
        // (a value's name: its value)
        if let Node::Var(v, a) = x.node() {
            if a.is_empty() {
                if let Some(e) = self.vexp.get(v).cloned() {
                    return self.univ_of(&e);
                }
            }
        }
        // (a parameter of the procedures: by hypothesis -- the refinement's
        // premise, discharged at the wrapper's arguments)
        if self.params.contains(x) {
            let h = self.mk("in", vec![x.clone(), self.mk("univ", vec![lit(1)])]);
            return self.assume(&h);
        }
        // (a choice of the walk: in its domain, a word's bits)
        if let Some((_, fact)) = self.gtyped.iter().find(|(v, _)| v == x).cloned() {
            if let Some(n) = self.app(fact.concl(), "in", 2).and_then(|i| self.app(&i[1], "bits", 1).map(|b| b[0].clone())) {
                let set = self.mk("bits", vec![n.clone()]);
                let i = fact;
                return self.run(&mp(R::Inst("univ_trans".into(), vec![("u", lit(1)), ("a", x.clone()), ("b", set)]), vec![p(R::Inst("bits_univ".into(), vec![("n", n)])), s(&i)]), &[]);
            }
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
        // (a case: each branch)
        if let Some(c) = self.app(x, "ite", 3).map(|c| c.to_vec()) {
            let (a, b) = (self.univ_of(&c[1])?, self.univ_of(&c[2])?);
            let un = self.mk("univ", vec![lit(1)]);
            return self.run(&mp(R::Inst("ite_in".into(), vec![("c", c[0].clone()), ("a", c[1].clone()), ("b", c[2].clone()), ("t", un)]), vec![s(&a), s(&b)]), &[]);
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
        let typed = if let Some(name) = ["bits_add", "bits_sub", "bits_mul", "bits_neg", "bits_of_int", "bits_sext", "bits_shl", "bits_sar"].into_iter().find(|n| self.head_is(x, n)) {
            let Node::App(_, a) = x.node() else { unreachable!() };
            let lemma = match name {
                "bits_add" => "nf.add_in",
                "bits_sub" => "nf.sub_in",
                "bits_mul" => "nf.mul_in",
                "bits_neg" => "nf.neg_in",
                "bits_of_int" => "nf.of_int_in",
                "bits_shl" => "nf.shl_in",
                "bits_sar" => "nf.sar_in",
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
    /// a premise over the labels `all l. v(l) -> G(l)`: G, and `U -> G`
    fn lab_g(&self, prem: &Term) -> Result<(Term, Term), String> {
        let body = self.app(prem, "all", 1).ok_or("a premise over the labels")?[0].clone();
        let (hs, gl) = self.imps(&body);
        if hs.is_empty() {
            return Err("a premise over the labels: not v -> ..".into());
        }
        let mut gl = gl;
        for h in hs[1..].iter().rev() {
            gl = Term::app(self.env.builtins.imp, vec![h.clone(), gl]);
        }
        let u = self.mk("in", vec![Term::bvar(0), self.mk("univ", vec![lit(1)])]);
        let gp = Term::app(self.env.builtins.imp, vec![u, gl.clone()]);
        Ok((gl, gp))
    }

    /// `f`'s proof walked at the free INV (as the points' walks: a walk's
    /// claims at the cut points hypotheses, not INV's large disjunction),
    /// then at INV `inv`, the hypotheses proven (hyp_proof)
    fn at_free_inv(&mut self, iv: VarId, inv_v: &Term, inv: &Term, f: impl FnOnce(&mut Self) -> Result<Seq, String>) -> Result<Seq, String> {
        {
            let g = self.gref.as_mut().unwrap();
            g.inv = inv_v.clone();
            g.inv_var = Some(iv);
        }
        let r = f(self);
        {
            let g = self.gref.as_mut().unwrap();
            g.inv = inv.clone();
            g.inv_var = None;
        }
        let mut s0 = Seq::inst(self.env, &r?, iv, inv).map_err(|e| e.0)?;
        let n = self.gref.as_ref().unwrap().points.len();
        for j in 0..n {
            let Some(Some(h)) = self.gref.as_ref().unwrap().hyps.get(j).cloned() else { continue };
            let a = self.assume(&h)?;
            let hj = Seq::inst(self.env, &a, iv, inv).map_err(|e| e.0)?.concl().clone();
            if s0.hyps().contains(&hj) {
                let pf = self.hyp_proof(j, inv)?;
                let d = s0.discharge(self.env, &hj).map_err(|e| e.0)?;
                s0 = Seq::mp(self.env, &d, &pf).map_err(|e| e.0)?;
            }
        }
        if !s0.hyps().is_empty() {
            return Err(format!("a walk at the free INV: {} hypotheses left", s0.hyps().len()));
        }
        Ok(s0)
    }

    /// lab_all's claim at label k
    fn lab_prem(&mut self, prem: &Term, k: u128) -> Result<Term, String> {
        let (_, gp) = self.lab_g(prem)?;
        let (_, st) = self.inst("g.lab_pt", &[("G", gp), ("k", lit(k))])?;
        Ok(self.imps(&st).0[0].clone())
    }

    /// a label's claim over the loops' cases `all w y. U -> all h. A(h) ->
    /// G(h)` from the loop at h0's own (`ps`, its G'): at h0, G from G' by
    /// evaluation (the cases decided); at any h, h = h0 from A(h)
    /// (evaluation, g.at_eq)
    fn case_at(&mut self, pc: &Term, ps: &Seq, h0: u128, ks: &[u128]) -> Result<Seq, String> {
        let (w, y, h, zv) = (self.var("cw"), self.var("cy"), self.var("ch"), self.var("cz"));
        let body = self.inst_alls(pc, &[w.clone(), y.clone()])?;
        let (hu, c) = self.imps(&body);
        let plam = self.app(&c, "all", 1).ok_or("a case claim: not all h")?[0].clone();
        let ph0 = plam.instantiate_params(&[lit(h0)], &self.env.binders_fn());
        let (ha0, g0) = self.imps(&ph0);
        let simp = |rs: Vec<R>| RP::Simp(false, rs, vec![], false);
        let a0 = self.evp(&simp(vec![]), &ha0[0], &[])?;
        let mut args = vec![t(&w), t(&y)];
        for u in &hu {
            args.push(s(&self.assume(u)?));
        }
        args.push(t(&lit(h0)));
        args.push(s(&a0));
        let g1 = self.run(&mp(R::S(ps.clone()), args), &[])?;
        let conds = self.decided_conds(&g0, ks)?;
        let gb = self.uncase(&g0, &g1, &conds).map_err(|e| format!("its cases taken: {}", e))?;
        let ph = plam.instantiate_params(std::slice::from_ref(&h), &self.env.binders_fn());
        let (ha, g) = self.imps(&ph);
        let aa = self.assume(&ha[0])?;
        let eq_t = self.mk("eq", vec![h.clone(), lit(h0)]);
        let eq = self.evp(&simp(vec![R::S(aa)]), &eq_t, &[])?;
        let pz = self.abs(&self.replace_t(&g, &h, &zv), &[Self::var_id(&zv)]);
        let at = self.run(&mp(R::Inst("g.at_eq".into(), vec![("P", pz), ("a", h.clone()), ("b", lit(h0))]), vec![s(&eq), s(&gb)]), &[])?;
        let at = self.evp(&RP::Taut(vec![R::S(at)]), &g, &[]).map_err(|e| format!("at h: {}", e))?;
        let at = self.close(at, &[ha[0].clone()], &[Self::var_id(&h)])?;
        let pf = self.evp(&RP::Taut(vec![R::S(at)]), &c, &[]).map_err(|e| format!("all h: {}", e))?;
        let pf = self.close(pf, &hu, &[])?;
        let pf = self.evp(&RP::Taut(vec![R::S(pf)]), &body, &[]).map_err(|e| format!("the claim: {}", e))?;
        self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
    }

    /// the loops' cases in t (`ite(X = k, ..)`, k a loop's) whose X is a
    /// label (`fst(snd(pair(w, pair(k2, ..))))`, a literal): each decided,
    /// its proof (of `X = k` or `!(X = k)`, by evaluation of that alone)
    fn decided_conds(&mut self, t: &Term, ks: &[u128]) -> Result<Vec<(Term, bool, Seq)>, String> {
        let mut cs: Vec<Term> = Vec::new();
        self.case_conds(t, ks, &mut cs, &mut Default::default());
        let mut out = Vec::new();
        for c in cs {
            let e = self.app(&c, "eq", 2).unwrap().to_vec();
            let x = self.red_t(&e[0], &mut Default::default());
            let (Some(a), Some(b)) = (nat(&x), nat(&e[1])) else { continue };
            let yes = a == b;
            let goal = if yes { c.clone() } else { self.mk("not", vec![c.clone()]) };
            let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &goal, &[])?;
            out.push((c, yes, pf));
        }
        Ok(out)
    }

    /// (the closed conditions `X = k` of t's `ite`s, k among ks, in order)
    fn case_conds(&self, t: &Term, ks: &[u128], out: &mut Vec<Term>, seen: &mut std::collections::HashSet<Term>) {
        if !seen.insert(t.clone()) {
            return;
        }
        if let Some(a) = self.app(t, "ite", 3) {
            if let Some(e) = self.app(&a[0], "eq", 2) {
                if nat(&e[1]).is_some_and(|k| ks.contains(&k)) && self.env.loose_depth_m(&a[0]) == 0 && !out.contains(&a[0]) {
                    out.push(a[0].clone());
                }
            }
        }
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => a.iter().for_each(|x| self.case_conds(x, ks, out, seen)),
            _ => {}
        }
    }

    /// the claim `goal` over the loops' cases from `own` (the claim with
    /// each case taken, each condition decided in `conds`): `goal = own` by
    /// rewriting `refl(goal)`'s right side under binders with g.ite_y /
    /// g.ite_n at each decided condition
    fn uncase(&mut self, goal0: &Term, own: &Seq, conds: &[(Term, bool, Seq)]) -> Result<Seq, String> {
        let goal = self.expand(goal0);
        // (`v = goal` assumed, v fresh: its right side rewritten -- every
        // instance, again for those inside a rewritten one -- then v the
        // goal, the assumption refl)
        let vv = self.var("uv");
        let veq = self.mk("eq", vec![vv.clone(), goal.clone()]);
        let mut e = self.assume(&veq)?;
        for (c, yes, pf) in conds {
            let lemma = if *yes { "g.ite_y" } else { "g.ite_n" };
            let eqs = self.run(&mp(R::Inst(lemma.into(), vec![("c", c.clone())]), vec![s(pf)]), &[])?;
            let api = self.api.take().expect("the proving context");
            let mut r = Ok(());
            while Seq::instance_count(self.env, &api.lg, &eqs, e.concl(), true) > 0 {
                match Seq::rewrite_under(self.env, &api.lg, &eqs, &e, &[]) {
                    Ok(x) => e = x,
                    Err(x) => {
                        r = Err(x.0);
                        break;
                    }
                }
            }
            self.api = Some(api);
            r?;
        }
        let e = e.discharge(self.env, &veq).map_err(|e| e.0)?;
        let e = Seq::inst(self.env, &e, Self::var_id(&vv), &goal).map_err(|e| e.0)?;
        let rf = Seq::refl(self.env, &goal).map_err(|e| e.0)?;
        let e = Seq::mp(self.env, &e, &rf).map_err(|e| e.0)?;
        let rhs = self.app(e.concl(), "eq", 2).unwrap()[1].clone();
        let oc = self.expand(own.concl());
        if rhs != oc {
            if let Ok(d) = std::env::var("C1_DUMP") {
                let _ = std::fs::write(format!("{}/uncase_rhs.txt", d), self.print(&rhs));
                let _ = std::fs::write(format!("{}/uncase_own.txt", d), self.print(&oc));
            }
            return Err("uncase: the claim with its cases taken not the loop's own".into());
        }
        let es = Seq::sym(self.env, &e).map_err(|e| e.0)?;
        // (taut only where the forms differ: a claim over the labels' many
        // atoms is not a truth table's)
        let own = if *own.concl() == oc { own.clone() } else { self.evp(&RP::Taut(vec![R::S(own.clone())]), &oc, &[])? };
        let r = Seq::rewrite(self.env, &es, &own).map_err(|e| e.0)?;
        if r.concl() == goal0 {
            return Ok(r);
        }
        self.evp(&RP::Taut(vec![R::S(r)]), goal0, &[])
    }

    /// `all h v2 .. vn. B` over the loops' cases from each loop's own (`own`,
    /// in the order of ks): at h = k1 the first, at !(h = k1) && h = k2 the
    /// second, .., the last the rest; joined by taut
    fn case_split(&mut self, prem: &Term, own: &[Seq], ks: &[u128], n: usize) -> Result<Seq, String> {
        let vs: Vec<Term> = (0..n).map(|i| self.var(&format!("cv{i}"))).collect();
        let body = self.inst_alls(prem, &vs)?;
        // (case i: under !(h = k1) .. and h = ki -- the last under the
        // negations alone)
        let mut parts: Vec<Seq> = Vec::new();
        for (i, o) in own.iter().enumerate() {
            let oi = self.run(&mp(R::S(o.clone()), vs.iter().map(t).collect()), &[])?;
            let mut conds = Vec::new();
            for (j, k) in ks.iter().enumerate().take((i + 1).min(ks.len() - 1)) {
                let c = self.mk("eq", vec![vs[0].clone(), lit(*k)]);
                let h = if j == i { c.clone() } else { self.mk("not", vec![c.clone()]) };
                conds.push((c, j == i, self.assume(&h)?));
            }
            parts.push(self.uncase(&body, &oi, &conds)?);
        }
        // (joined from the last: case i's c_i and the rest's !c_i by g.cases,
        // the claim whole)
        let mut acc = parts.pop().ok_or("no loop's case")?;
        for (i, p) in parts.into_iter().enumerate().rev() {
            let c = self.mk("eq", vec![vs[0].clone(), lit(ks[i])]);
            let nc = self.mk("not", vec![c.clone()]);
            let pc = self.close(p, &[c.clone()], &[])?;
            let pn = self.close(acc, &[nc], &[])?;
            acc = self.run(&mp(R::Inst("g.cases".into(), vec![("c", c), ("G", body.clone())]), vec![s(&pc), s(&pn)]), &[])?;
        }
        self.close(acc, &[], &vs.iter().map(Self::var_id).collect::<Vec<_>>())
    }

    fn lab_all(&mut self, prem: &Term, mut per: impl FnMut(&mut Self, u128, &Term) -> Result<Seq, String>) -> Result<Seq, String> {
        let (gl, gp) = self.lab_g(prem)?;
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
        let mut acc = self.run(&R::Inst("tr.cfg_kk_nil".into(), vec![("P", gp.clone())]), &[])?;
        for i in (0..labels.len()).rev() {
            let (r, st) = self.inst("g.lab_pt", &[("G", gp.clone()), ("k", lit(labels[i]))])?;
            let (ps, _) = self.imps(&st);
            self.gref.as_mut().unwrap().cur = labels[i];
            let pf = per(self, labels[i], &ps[0])?;
            let one = self.run(&mp(r, vec![s(&pf)]), &[])?;
            acc = self.run(&mp(R::Inst("g.lab_or".into(), vec![("G", gp.clone()), ("A", disj[i].0.clone()), ("B", disj[i].1.clone())]), vec![s(&one), s(&acc)]), &[])?;
            // (the label's terms not kept by the caches)
            self.drop_caches();
        }
        let r = self.run(&mp(R::Inst("g.lab_univ".into(), vec![("G", gl), ("D", d)]), vec![s(&acc)]), &[])?;
        self.evp(&RP::Taut(vec![R::S(r)]), prem, &[])
    }

    /// `all l q. inv(l, q) -> .. -> G(l, q)` from each point's claim (`per`,
    /// given point i and its premise `all w y. G(pair(w, pair(k, sh(y))),
    /// u(y))`), by g.inv_or
    fn pts_all(&mut self, prem: &Term, mut per: impl FnMut(&mut Self, usize, &Term) -> Result<Seq, String>) -> Result<Seq, String> {
        let gl = self.claim_g(prem)?;
        let inv = self.gref.as_ref().unwrap().inv.clone();
        let mut disj = Vec::new();
        let mut cur = inv.clone();
        while let Some(o) = self.app(&cur, "or", 2).map(|o| o.to_vec()) {
            disj.push((o[0].clone(), o[1].clone()));
            cur = o[1].clone();
        }
        let n = self.gref.as_ref().unwrap().points.len();
        if disj.len() != n {
            return Err("inv's disjuncts not the points".into());
        }
        let mut acc = self.run(&R::Inst("g.inv_none".into(), vec![("G", gl.clone())]), &[])?;
        for i in (0..n).rev() {
            let (r, prem_i) = self.pt_prem(&gl, i)?;
            self.gref.as_mut().unwrap().cur = self.gref.as_ref().unwrap().points[i].label;
            let pf = per(self, i, &prem_i)?;
            let pt = self.run(&mp(r, vec![s(&pf)]), &[])?;
            acc = self.run(&mp(R::Inst("g.inv_or".into(), vec![("G", gl.clone()), ("A", disj[i].0.clone()), ("B", disj[i].1.clone())]), vec![s(&pt), s(&acc)]), &[])?;
            self.drop_caches();
        }
        self.evp(&RP::Taut(vec![R::S(acc)]), prem, &[])
    }

    /// point i's state at world w, locals y
    fn point_state(&self, i: usize, w: &Term, y: &Term) -> Term {
        let g = self.gref.as_ref().unwrap();
        let p = &g.points[i];
        self.mk("pair", vec![w.clone(), self.mk("pair", vec![lit(p.label), self.shape_t(p, y, g.m)])])
    }

    /// a claim `all v1 .. vn. A -> ..` (k = 0) or `all v1 .. vn. U -> all
    /// h. A(h) -> ..` (k = 1) whose A fails (by evaluation)
    fn vacuous(&mut self, pk: &Term, n: usize, k: usize) -> Result<Seq, String> {
        let vs: Vec<Term> = (0..n).map(|i| self.var(&format!("vv{i}"))).collect();
        let body = self.inst_alls(pk, &vs)?;
        let (hs, c) = self.imps(&body);
        let simp = RP::Simp(false, vec![], vec![], false);
        let pf = if k == 0 {
            let neg = self.evp(&simp, &self.mk("not", vec![hs[0].clone()]), &[])?;
            self.evp(&RP::Taut(vec![R::S(neg)]), &body, &[])?
        } else {
            let hv = self.var("vh");
            let ch = self.inst_alls(&c, std::slice::from_ref(&hv))?;
            let (hs2, _) = self.imps(&ch);
            let neg = self.evp(&simp, &self.mk("not", vec![hs2[0].clone()]), &[])?;
            let pc = self.evp(&RP::Taut(vec![R::S(neg)]), &ch, &[])?;
            let pc = self.close(pc, &[], &[Self::var_id(&hv)])?;
            self.evp(&RP::Taut(vec![R::S(pc)]), &body, &[])?
        };
        self.close(pf, &[], &vs.iter().map(Self::var_id).collect::<Vec<_>>())
    }

    /// `all v1 .. vn. B` by evaluation
    fn all_simp(&mut self, prem: &Term, n: usize) -> Result<Seq, String> {
        let vs: Vec<Term> = (0..n).map(|i| self.var(&format!("av{i}"))).collect();
        let body = self.inst_alls(prem, &vs)?;
        let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &body, &[])?;
        self.close(pf, &[], &vs.iter().map(Self::var_id).collect::<Vec<_>>())
    }

    /// `all .. . !A && !B`: each refuted (a rest never marked 4 or 5)
    fn all_refute(&mut self, prem: &Term) -> Result<Seq, String> {
        let mut vs = Vec::new();
        let mut body = prem.clone();
        while let Some(b) = self.app(&body, "all", 1).map(|b| b[0].clone()) {
            let v = self.var(&format!("rv{}", vs.len()));
            body = b.instantiate_params(std::slice::from_ref(&v), &self.env.binders_fn());
            vs.push(v);
        }
        let c = self.app(&body, "and", 2).ok_or("not !A && !B")?.to_vec();
        let mut fs = Vec::new();
        for x in &c {
            let a = self.app(x, "not", 1).ok_or("not !A && !B")?[0].clone();
            fs.push(R::S(self.refute(&a)?.ok_or_else(|| format!("a rest marked: not refuted: {}", self.print(&a)))?));
        }
        let pf = self.evp(&RP::Taut(fs), &body, &[])?;
        self.close(pf, &[], &vs.iter().map(Self::var_id).collect::<Vec<_>>())
    }

    /// `all h x. v(x) -> fst(x) in univ(1) && H(h, x) in univ(1)`
    fn univ_hu(&mut self, prem: &Term) -> Result<Seq, String> {
        let (h, x) = (self.var("uh"), self.var("ux"));
        let body = self.inst_alls(prem, &[h.clone(), x.clone()])?;
        let (hs, c) = self.imps(&body);
        let hv = self.assume(&hs[0])?;
        let xu_t = self.mk("in", vec![x.clone(), self.mk("univ", vec![lit(1)])]);
        let xu = self.v_univ(&x, &hv)?;
        let _ = xu_t;
        self.gref.as_mut().unwrap().cut.as_mut().unwrap().ufacts = vec![(x.clone(), xu)];
        let mut fs = Vec::new();
        for part in self.app(&c, "and", 2).ok_or("hu: not a conjunction")?.to_vec() {
            let e = self.app(&part, "in", 2).ok_or("hu: not in")?[0].clone();
            fs.push(R::S(self.univ_of(&e)?));
        }
        let pf = self.evp(&RP::Taut(fs), &c, &[])?;
        self.close(pf, &[hs[0].clone()], &[Self::var_id(&h), Self::var_id(&x)])
    }

    /// `all x. v(x) -> tr(x) in univ(1)` (tr.tr_univ)
    fn univ_htu(&mut self, prem: &Term) -> Result<Seq, String> {
        let x = self.var("tx");
        let body = self.inst_alls(prem, std::slice::from_ref(&x))?;
        let (hs, c) = self.imps(&body);
        let hv = self.assume(&hs[0])?;
        let xu_t = self.mk("in", vec![x.clone(), self.mk("univ", vec![lit(1)])]);
        let xu = self.v_univ(&x, &hv)?;
        let _ = xu_t;
        let tu =self.run(&mp(f("tr.tr_univ"), vec![t(&x), s(&xu)]), &[])?;
        let pf = self.evp(&RP::Taut(vec![R::S(tu)]), &c, &[])?;
        self.close(pf, &[hs[0].clone()], &[Self::var_id(&x)])
    }

    /// `x in univ(1)` from v(x) (g.v_univ)
    fn v_univ(&mut self, x: &Term, hv: &Seq) -> Result<Seq, String> {
        let d = self.gref.as_ref().unwrap().cut.as_ref().unwrap().v.clone();
        self.run(&mp(R::Inst("g.v_univ".into(), vec![("D", d), ("x", x.clone())]), vec![s(hv)]), &[])
    }

    /// a head point's program the structured loop (hq): `all w y. hd(st)
    /// -> all o. E -> U -> runs(u(y), fst(st), o)`, E u(y)'s relation there
    fn head_prog(&mut self, _i: usize, pk: &Term) -> Result<Seq, String> {
        let (w, y, o) = (self.var("qw"), self.var("qy"), self.var("qo"));
        let body = self.inst_alls(pk, &[w.clone(), y.clone()])?;
        let (_, c) = self.imps(&body);
        let co = self.inst_alls(&c, std::slice::from_ref(&o))?;
        let (hs, g) = self.imps(&co);
        let r = self.app(&g, "runs", 3).ok_or("hq: not runs")?.to_vec();
        let rl = self.app(&r[0], "mkprog", 1).ok_or("hq: not a program")?[0].clone();
        let (ae, au) = (self.assume(&hs[0])?, self.assume(&hs[1])?);
        // (the relation there: E at the locals y, not snd(snd(st)))
        let goal_r = rl.instantiate_params(&[r[1].clone(), o.clone()], &self.env.binders_fn());
        let st = self.app(&r[1], "fst", 1).ok_or("hq: not at fst(st)")?[0].clone();
        let ss = self.mk("snd", vec![self.mk("snd", vec![st.clone()])]);
        let er = match self.at_eq_y(&goal_r, &y, &ss, ae.clone(), &st) {
            Ok(e) => e,
            // (the loop first in a block: its rest re-associated)
            Err(e0) => {
                let ae2 = self.reassoc(&ae).map_err(|e| format!("{} (and re-associated: {})", e0, e))?;
                self.at_eq_y(&goal_r, &y, &ss, ae2, &st)?
            }
        };
        let pf = self.run(&mp(R::Inst("tr.runs_intro".into(), vec![("r", rl)]), vec![t(&r[1]), t(&o), s(&au), s(&er)]), &[])?;
        let pf = self.close(pf, &hs, &[Self::var_id(&o)])?;
        let pf = self.evp(&RP::Taut(vec![R::S(pf)]), &body, &[])?;
        self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
    }

    /// `ex z. ((ex x. W(x) && C(x, z)) && K(z))` from `ex x. W(x) && (ex
    /// z. C(x, z) && K(z))` (g.ex_reassoc)
    fn reassoc(&mut self, ae: &Seq) -> Result<Seq, String> {
        let b = self.app(ae.concl(), "ex", 1).ok_or("not ex x. W && ..")?[0].clone();
        let x = self.app(&b, "and", 2).ok_or("not ex x. W && ..")?.to_vec();
        let r = self.app(&x[1], "ex", 1).ok_or("not ex x. W && (ex z. ..)")?[0].clone();
        let y = self.app(&r, "and", 2).ok_or("not ex x. W && (ex z. C && K)")?.to_vec();
        if self.occurs_bv(&y[1], 1) {
            return Err("K reads the loop's outcome".into());
        }
        let k1 = self.lower_bv(&y[1], 1);
        self.run(&mp(R::Inst("g.ex_reassoc".into(), vec![("W", x[0].clone()), ("C", y[0].clone()), ("K", k1)]), vec![s(ae)]), &[])
    }

    /// a head's trips (hb at its label): `all w y. U -> all h. hd(st) &&
    /// fst(snd(st)) = h -> all o. TRIP(h, st, o) -> U2 -> C(h, st, o)` --
    /// at h the head's label, the CFG's trip walked with the structured
    /// body (`mkprog(x0 x1. C)`); at any h equal to it (g.at_eq)
    fn trip_claim(&mut self, pk: &Term, h0: u128) -> Result<Seq, String> {
        let (w, y, o) = (self.var("bw"), self.var("by"), self.var("bo"));
        let body = self.inst_alls(pk, &[w.clone(), y.clone()])?;
        let (_, c) = self.imps(&body);
        let plam = self.app(&c, "all", 1).ok_or("hb: not all h")?[0].clone();
        let ph0 = plam.instantiate_params(&[lit(h0)], &self.env.binders_fn());
        let (_, c3) = self.imps(&ph0);
        let co = self.inst_alls(&c3, std::slice::from_ref(&o))?;
        let (hs, concl) = self.imps(&co);
        let ob = self.app(&c3, "all", 1).ok_or("hb: not all o")?[0].clone();
        let (hsb, _) = self.imps(&ob);
        let lo = hsb[0].clone();
        let q = self.mk("mkprog", vec![self.abs(&concl, &[Self::var_id(&w), Self::var_id(&o)])]);
        let qj = self.new_q(q);
        let saved = self.w.clone();
        let r = self.walk(&lo, qj, &w);
        self.w = saved;
        let gr = self.run(&R::Expand(Box::new(R::S(r?)), vec!["g.ref".into()]), &[])?;
        let (tj, uu) = (self.assume(&hs[0])?, self.assume(&hs[1])?);
        let uw_t = self.mk("in", vec![self.mk("pair", vec![w.clone(), o.clone()]), self.mk("univ", vec![lit(1)])]);
        let uw = self.evp(&RP::Simp(false, vec![R::S(uu)], vec![], false), &uw_t, &[])?;
        let rr = self.run(&mp(R::S(gr), vec![t(&o), s(&tj), s(&uw)]), &[])?;
        let ce = self.run(&R::Apply(Box::new(f("g.runs_elim")), vec![s(&rr)]), &[])?;
        let pf = self.evp(&RP::Taut(vec![R::S(ce)]), &concl, &[])?;
        let pf = self.close(pf, &hs, &[Self::var_id(&o)])?;
        let p0 = self.evp(&RP::Taut(vec![R::S(pf)]), &ph0, &[])?;
        // (at h: h the head's label)
        let hv = self.var("bh");
        let ph = plam.instantiate_params(std::slice::from_ref(&hv), &self.env.binders_fn());
        let (hs5, _) = self.imps(&ph);
        let ah = self.assume(&hs5[0])?;
        let eq_t = self.mk("eq", vec![hv.clone(), lit(h0)]);
        let eq = self.evp(&RP::Simp(false, vec![R::S(ah)], vec![], false), &eq_t, &[])?;
        let at = self.run(&mp(R::Inst("g.at_eq".into(), vec![("P", plam), ("a", hv.clone()), ("b", lit(h0))]), vec![s(&eq), s(&p0)]), &[])?;
        let at = self.close(at, &[hs5[0].clone()], &[])?;
        let at = self.evp(&RP::Taut(vec![R::S(at)]), &ph, &[])?;
        let at = self.close(at, &[], &[Self::var_id(&hv)])?;
        let pf = self.evp(&RP::Taut(vec![R::S(at)]), &body, &[])?;
        self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
    }

    /// an exit's claim (hxk at its label): `all w y. U -> all h. xp(h, st)
    /// -> all o. (all q. inv(st, q) -> U2 -> runs(q, ..)) -> U2 -> ks(h,
    /// exc(H(h, st), brk), o)` -- by the exit point's program
    fn exit_claim(&mut self, pk: &Term, e: u128) -> Result<Seq, String> {
        let ie = self.gref.as_ref().unwrap().points.iter().position(|p| p.label == e).ok_or("an exit not a point")?;
        let (w, y, h, o) = (self.var("xw"), self.var("xy"), self.var("xh"), self.var("xo"));
        let body = self.inst_alls(pk, &[w.clone(), y.clone()])?;
        let (_, c) = self.imps(&body);
        let ch = self.inst_alls(&c, std::slice::from_ref(&h))?;
        let (_, c2) = self.imps(&ch);
        let co = self.inst_alls(&c2, std::slice::from_ref(&o))?;
        let (hs, goal) = self.imps(&co);
        let st = self.point_state(ie, &w, &y);
        let tm = self.gref.as_ref().unwrap().points[ie].tmpl.clone();
        let q = tm.instantiate_params(std::slice::from_ref(&y), &self.env.binders_fn());
        let iq = self.inv_at_pt(&st, &q, ie)?;
        let (hj, u2) = (self.assume(&hs[0])?, self.assume(&hs[1])?);
        let rr = self.run(&mp(R::S(hj), vec![t(&q), s(&iq), s(&u2)]), &[])?;
        let ce = self.run(&R::Apply(Box::new(f("g.runs_elim")), vec![s(&rr)]), &[])?;
        // (the rest at the locals snd(snd(st)), the program's at y)
        let ss = self.mk("snd", vec![self.mk("snd", vec![st.clone()])]);
        let ce_t = ce.concl().clone();
        let kv = self.var("ek");
        let ps = self.replace_t(&ce_t, &st, &kv);
        let ps = self.replace_t(&ps, &y, &ss);
        let ps = self.replace_t(&ps, &kv, &st);
        let pf = self.at_eq_y(&ps, &ss, &y, ce, &st)?;
        if ps != goal && std::env::var("C1_DUMP").is_ok() {
            let d = std::env::var("C1_DUMP").unwrap();
            let _ = std::fs::write(format!("{}/exit_ps.txt", d), self.print(&ps));
            let _ = std::fs::write(format!("{}/exit_goal.txt", d), self.print(&goal));
        }
        // (the exit point's program folded at the break -- an exit reached
        // before as a cut point: its first part from the rest's, g.ex_mono)
        // (or, the exit inside more blocks than the point's program -- a
        // loop in nested `if`s: their ends pass the outcome on --, the rest
        // by evaluation from the program)
        let pf = if ps != goal { self.ex_mono(pf, &goal)? } else { pf };
        let pf = self.evp(&RP::Taut(vec![R::S(pf)]), &goal, &[])?;
        let pf = self.close(pf, &hs, &[Self::var_id(&o)])?;
        let pf = self.evp(&RP::Taut(vec![R::S(pf)]), &ch, &[])?;
        let pf = self.close(pf, &[], &[Self::var_id(&h)])?;
        let pf = self.evp(&RP::Taut(vec![R::S(pf)]), &body, &[])?;
        self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
    }

    /// `ex x. B(x) && K(x)` (goal) from `ex x. A(x) && K(x)` (fact): A(x) ->
    /// B(x) by evaluation of B alone at A's x (g.ex_mono)
    fn ex_mono(&mut self, fact: Seq, goal: &Term) -> Result<Seq, String> {
        let parts = |g: &Self, t: &Term| -> Option<(Term, Term)> {
            let b = g.app(t, "ex", 1)?[0].clone();
            let c = g.app(&b, "and", 2)?;
            Some((c[0].clone(), c[1].clone()))
        };
        let (a, k1) = parts(self, fact.concl()).ok_or("an exit's program: not ex x. A && K")?;
        let (b, k2) = parts(self, goal).ok_or("an exit's rest: not ex x. B && K")?;
        // (the rest one block end further: `ex y. P(x, y) && K(y)`, P passing
        // the outcome on -- g.ex_pass)
        if k1 != k2 {
            let pass = (|| {
                let e = self.app(&k2, "ex", 1)?[0].clone();
                let c = self.app(&e, "and", 2)?;
                (c[1] == self.shift_bv(&k1, 1, 1)).then(|| c[0].clone())
            })();
            let Some(pp) = pass else { return Err("an exit's program and rest: their rests differ".into()) };
            let (xv, yv) = (self.var("mx"), self.var("my"));
            let (ax, bx, kx, pxy, pxx) = {
                let bf = self.env.binders_fn();
                (
                    a.instantiate_params(std::slice::from_ref(&xv), &bf),
                    b.instantiate_params(std::slice::from_ref(&xv), &bf),
                    k1.instantiate_params(std::slice::from_ref(&xv), &bf),
                    pp.instantiate_params(&[xv.clone(), yv.clone()], &bf),
                    pp.instantiate_params(&[xv.clone(), xv.clone()], &bf),
                )
            };
            let ha = self.assume(&ax)?;
            let pb = self.evp(&RP::Simp(false, vec![R::S(ha.clone())], vec![], false), &bx, &[])?;
            let pp2 = self.evp(&RP::Simp(false, vec![R::S(ha)], vec![], false), &pxx, &[])?;
            let prem = self.close(pb, &[ax.clone()], &[Self::var_id(&xv)])?;
            let prem2 = self.close(pp2, &[ax.clone()], &[Self::var_id(&xv)])?;
            let (ix, iy) = (Self::var_id(&xv), Self::var_id(&yv));
            let (al, bl, kl, pl) = (self.abs(&ax, &[ix]), self.abs(&bx, &[ix]), self.abs(&kx, &[ix]), self.abs(&pxy, &[ix, iy]));
            let r = self.run(&mp(R::Inst("g.ex_pass".into(), vec![("A", al), ("B", bl), ("P", pl), ("K", kl)]), vec![s(&prem), s(&prem2), s(&fact)]), &[])?;
            return self.evp(&RP::Taut(vec![R::S(r)]), goal, &[]);
        }
        let xv = self.var("mx");
        let (ax, bx, kx) = {
            let bf = self.env.binders_fn();
            (a.instantiate_params(std::slice::from_ref(&xv), &bf), b.instantiate_params(std::slice::from_ref(&xv), &bf), k1.instantiate_params(std::slice::from_ref(&xv), &bf))
        };
        let ha = self.assume(&ax)?;
        let pb = self.evp(&RP::Simp(false, vec![R::S(ha)], vec![], false), &bx, &[])?;
        let prem = self.close(pb, &[ax.clone()], &[Self::var_id(&xv)])?;
        let id = Self::var_id(&xv);
        let (al, bl, kl) = (self.abs(&ax, &[id]), self.abs(&bx, &[id]), self.abs(&kx, &[id]));
        let r = self.run(&mp(R::Inst("g.ex_mono".into(), vec![("A", al), ("B", bl), ("K", kl)]), vec![s(&prem), s(&fact)]), &[])?;
        self.evp(&RP::Taut(vec![R::S(r)]), goal, &[])
    }

    /// `goal` (P(a), a a variable or term written there) from `fact` (P(b)),
    /// a = b by evaluation (g.at_eq; P the goal over a)
    fn at_eq_y(&mut self, goal: &Term, a: &Term, b: &Term, fact: Seq, keep: &Term) -> Result<Seq, String> {
        // (`keep`, a's other occurrences: as they are)
        let (zv, kv) = (self.var("az"), self.var("ak"));
        let pz = if self.replace_t(a, keep, &kv) != *a {
            // (a holds `keep`: a first)
            self.replace_t(goal, a, &zv)
        } else {
            let pz = self.replace_t(goal, keep, &kv);
            let pz = self.replace_t(&pz, a, &zv);
            self.replace_t(&pz, &kv, keep)
        };
        let plam = self.abs(&pz, &[Self::var_id(&zv)]);
        let eq_t = self.mk("eq", vec![a.clone(), b.clone()]);
        let eq = self.evp(&RP::Simp(false, vec![], vec![], false), &eq_t, &[])?;
        let pb = plam.instantiate_params(std::slice::from_ref(b), &self.env.binders_fn());
        let fb = self.evp(&RP::Taut(vec![R::S(fact)]), &pb, &[])?;
        let r = self.run(&mp(R::Inst("g.at_eq".into(), vec![("P", plam), ("a", a.clone()), ("b", b.clone())]), vec![s(&eq), s(&fb)]), &[])?;
        self.evp(&RP::Taut(vec![R::S(r)]), goal, &[])
    }

    /// a label's claim (lab_all's) by evaluation
    fn lab_simp(&mut self, pk: &Term) -> Result<Seq, String> {
        let (w, y) = (self.var("sw"), self.var("sy"));
        let body = self.inst_alls(pk, &[w.clone(), y.clone()])?;
        let pf = self.evp(&RP::Simp(false, vec![], vec![], false), &body, &[])?;
        self.close(pf, &[], &[Self::var_id(&w), Self::var_id(&y)])
    }

    /// `x in int`: a signed word (g.sint_int), a number
    pub(super) fn int_of(&mut self, x: &Term) -> Result<Seq, String> {
        let goal = self.mk("in", vec![x.clone(), self.mk("int", vec![])]);
        if let Some(a) = self.app(x, "sint", 2).map(|a| a.to_vec()) {
            let r = self.run(&mp(R::Inst("g.sint_int".into(), vec![("n", a[0].clone()), ("a", a[1].clone())]), vec![simp0()]), &[])?;
            return self.evp(&RP::Taut(vec![R::S(r)]), &goal, &[]);
        }
        if nat(x).is_some() {
            return self.evp(&RP::Simp(false, vec![], vec![], false), &goal, &[]);
        }
        Err(format!("not known an integer: {}", self.print(x)))
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
