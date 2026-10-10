//! Joins: where the paths of a branch meet again, the point claim is
//! proven once and used on each path that arrives, so a function's proof
//! grows with its code rather than with its paths.
//!
//! A join point is an address with two predecessors or more. A path
//! arriving there (after the spec's reductions) with no claim it is an
//! instance of is recorded, and walks on as before. The next path arriving
//! from the other side of a branch is generalized against it:
//! - the two states anti-unified -- the spec's rest, the homes' values, the
//!   world: where they differ, a variable (one per pair of terms), where
//!   they agree, the term itself;
//! - no registers (`tr.pt_rs` drops them on use);
//! - the facts of the branch's time kept, and of those both paths assumed
//!   after it the ones alike under the variables: premises;
//! - a home's whole value a variable: a word of its size, a premise.
//! The claim `all ys. W(ys) a world -> premises -> tr.lv(.. at the join ..)`
//! is proven by walking on from the point, then used, by matching, for this
//! path and any later one it fits. Nothing is trusted here: a claim the
//! walk cannot prove, or a path it does not fit, only loses the sharing.

use super::rec::*;
use super::*;

/// the claims made at one join point at most
const MAX_CLAIMS: usize = 8;

/// widening (a claim's every home value a variable, though the same in
/// both paths): off -- a home holds the code's form of a value, the spec
/// its own, and only where the paths differ do both get the variable
const WIDEN: bool = false;

/// a branch on the path: the other side's target, the facts and calls'
/// results then (their counts), the variables then (those made after are
/// the branch's own)
#[derive(Clone, PartialEq)]
pub(super) struct Split {
    other: u128,
    hyps: usize,
    facts: usize,
    mark: usize,
}

/// the spec at a point, expanded: a rest, or a result and the wrapper's rest
#[derive(Clone)]
enum SpecX {
    Proc(Term),
    Ret(Term, Term),
}

/// a path's state at a join point, expanded
#[derive(Clone)]
pub(super) struct Arrival {
    a: u128,
    fr: u128,
    ds: Term,
    lp: Option<usize>,
    splits: Vec<Split>,
    homes: Vec<(u128, u128, Term)>,
    w: Term,
    spec: SpecX,
    hyps: Vec<Term>,
    facts: Vec<Term>,
    /// a claim's (its terms patterns): a path generalized with it widens it
    pattern: bool,
}

/// a claim's premise: its world a world, a home's value a word, a fact
/// of the facts in scope, a call's result's
#[derive(Clone)]
enum Prem {
    World,
    Bits(VarId),
    Hyp,
    Fact,
}

/// a join's claim: at `a` (its frame, depth, loop), over the variables
/// `vars`, the patterns of the homes (in their map's order), the world,
/// the spec; the kept facts, the premises (a fact's or a call result's)
#[derive(Clone)]
pub(super) struct Join {
    a: u128,
    fr: u128,
    ds: Term,
    lp: Option<usize>,
    vars: Vec<VarId>,
    homes: Vec<(u128, u128, Term)>,
    w: Term,
    spec: SpecX,
    /// the claim's premises, in order (those its proof used)
    prems: Vec<(Prem, Term)>,
    claim: Seq,
    /// the claim's state as an arrival (its patterns; its facts the kept
    /// and the premises): what a path it does not fit is generalized with
    pattern: Arrival,
}

impl<'e> Gen<'e> {
    /// the split of a branch at st, the other side going to `other`
    pub(super) fn split(&self, st: &St, other: u128) -> Split {
        Split { other, hyps: st.hyps.len(), facts: st.facts.len(), mark: self.env.vars.len() }
    }

    /// the code's successors of the instruction at a
    fn succs(&self, a: u128) -> Vec<u128> {
        let Some(i) = self.insns.get(&a) else { return Vec::new() };
        let a2 = (a + i.len) % P64;
        match i.row {
            // ret
            122 => Vec::new(),
            // jmp rel8
            125 => match nat(&i.fields) {
                Some(r) => vec![(a2 + if r & 0x80 != 0 { r + 0xffff_ffff_ffff_ff00 } else { r }) % P64],
                None => Vec::new(),
            },
            // jcc rel8, rel32
            127 | 128 => match self.jcc(a) {
                Ok((_, _, a3, tt, _)) => vec![a3, tt],
                Err(_) => vec![a2],
            },
            _ => vec![a2],
        }
    }

    /// the number of a's predecessors in the code
    fn preds_of(&mut self, a: u128) -> usize {
        if self.preds.is_none() {
            let mut m: BTreeMap<u128, usize> = BTreeMap::new();
            for &x in self.insns.keys() {
                for y in self.succs(x) {
                    *m.entry(y).or_default() += 1;
                }
            }
            self.preds = Some(m);
        }
        self.preds.as_ref().and_then(|m| m.get(&a).copied()).unwrap_or(0)
    }

    /// The point claim at st by a join's claim: one st is an instance of,
    /// or one generalizing st and an earlier path's arrival here (none:
    /// not a join point, or the first path here)
    pub(super) fn join(&mut self, st: &St) -> Result<Option<Seq>, String> {
        if st.no_join == Some(st.a) || st.z.is_some() || self.preds_of(st.a) < 2 {
            return Ok(None);
        }
        let Some(arr) = self.arrival(st) else { return Ok(None) };
        for i in 0..self.joins.len() {
            if let Some(pf) = self.join_use(i, st)? {
                return Ok(Some(pf));
            }
        }
        // (enough claims here: the path on its own -- a bound on the work,
        // whatever the paths are like)
        if self.joins.iter().filter(|j| j.a == st.a).count() >= MAX_CLAIMS {
            return Ok(None);
        }
        // (the latest claim here, generalized with this path; or the latest
        // path here that left at another side of a branch)
        let mut bases = Vec::new();
        if let Some(j) = self.joins.iter().rev().find(|j| j.a == st.a) {
            bases.push(j.pattern.clone());
        }
        if let Some(a1) = self.arrivals.iter().rev().find(|x| x.a == st.a) {
            bases.push(a1.clone());
        }
        for a1 in bases {
            if let Some(i) = self.join_make(&a1, st, &arr)? {
                if let Some(pf) = self.join_use(i, st)? {
                    return Ok(Some(pf));
                }
                self.trace(|| format!("join at {:x}: its claim does not fit the path it was made from", st.a));
            }
        }
        self.arrivals.push(arr);
        Ok(None)
    }

    /// the homes' map term `hst`: its entries in order (key, bytes, value)
    fn home_entries(&self, hst: &Term) -> Option<Vec<(u128, u128, Term)>> {
        let mut out = Vec::new();
        let mut m = hst.clone();
        while let Some((parent, k, pv)) = upd_parts(self, &m) {
            let x = self.app(&pv, "pair", 2)?;
            out.push((nat(&k)?, nat(&x[0])?, x[1].clone()));
            m = parent;
        }
        self.app(&m, "empty", 0)?;
        out.reverse();
        Some(out)
    }

    fn arrival(&self, st: &St) -> Option<Arrival> {
        let homes = self.home_entries(&st.hst)?.into_iter().map(|(k, n, x)| (k, n, self.expand(&x))).collect();
        let spec = match &st.spec {
            Spec::Proc(i) => SpecX::Proc(self.expand(&self.qs[*i])),
            Spec::Ret(v, pr) => SpecX::Ret(self.expand(v), self.expand(pr)),
        };
        Some(Arrival {
            a: st.a,
            fr: st.fr,
            ds: self.expand(&st.ds),
            lp: st.lp,
            splits: st.splits.clone(),
            homes,
            w: self.expand(&st.w),
            spec,
            hyps: st.hyps.iter().map(|h| self.expand(&h.0)).collect(),
            facts: st.facts.iter().map(|f| self.expand(f.concl())).collect(),
            pattern: false,
        })
    }

    /// t1 and t2 anti-unified: their common term, a variable of `tab` for
    /// each pair of closed subterms where they differ (a new one unless
    /// `fixed`); none where they differ under a binder's variable
    fn au(&mut self, t1: &Term, t2: &Term, tab: &mut Vec<(Term, Term, Term)>, fixed: bool, name: &str) -> Option<Term> {
        // (a pair abstracted already -- or seeded: a value abstracted though
        // the same in both)
        if let Some((_, _, y)) = tab.iter().find(|(x1, x2, _)| x1 == t1 && x2 == t2) {
            return Some(y.clone());
        }
        if t1 == t2 {
            return Some(t1.clone());
        }
        match (t1.node(), t2.node()) {
            (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() && !a.is_empty() => {
                let mut xs = Vec::new();
                for (x, y) in a.iter().zip(b.iter()) {
                    xs.push(self.au(x, y, tab, fixed, name)?);
                }
                return Some(t1.with_args(xs));
            }
            (Node::Var(v, a), Node::Var(w, b)) if v == w && a.len() == b.len() && !a.is_empty() => {
                let mut xs = Vec::new();
                for (x, y) in a.iter().zip(b.iter()) {
                    xs.push(self.au(x, y, tab, fixed, name)?);
                }
                return Some(t1.with_args(xs));
            }
            _ => {}
        }
        let open = {
            let bf = self.env.binders_fn();
            t1.loose_depth(&bf) > 0 || t2.loose_depth(&bf) > 0
        };
        if open {
            return None;
        }
        if let Some((_, _, y)) = tab.iter().find(|(x1, x2, _)| x1 == t1 && x2 == t2) {
            return Some(y.clone());
        }
        if fixed {
            return None;
        }
        let y = self.var(&format!("{}{}", name, tab.len()));
        tab.push((t1.clone(), t2.clone(), y.clone()));
        Some(y)
    }

    /// whether t is an instance of the pattern pat (its variables `vars`),
    /// extending the substitution `sub`
    fn matches(&self, pat: &Term, t: &Term, vars: &[VarId], sub: &mut Vec<(VarId, Term)>) -> bool {
        if let Node::Var(v, a) = pat.node() {
            if a.is_empty() && vars.contains(v) {
                if let Some((_, x)) = sub.iter().find(|(u, _)| u == v) {
                    return x == t;
                }
                if t.loose_depth(&self.env.binders_fn()) > 0 {
                    return false;
                }
                sub.push((*v, t.clone()));
                return true;
            }
        }
        if pat == t {
            return true;
        }
        match (pat.node(), t.node()) {
            (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => a.iter().zip(b.iter()).all(|(x, y)| self.matches(x, y, vars, sub)),
            (Node::Var(v, a), Node::Var(w, b)) if v == w && a.len() == b.len() => a.iter().zip(b.iter()).all(|(x, y)| self.matches(x, y, vars, sub)),
            _ => false,
        }
    }

    /// A new join's claim, generalizing the arrival a1 (another path's) and
    /// st's (a2): its index
    fn join_make(&mut self, a1: &Arrival, st: &St, a2: &Arrival) -> Result<Option<usize>, String> {
        let a = st.a;
        if a1.fr != a2.fr || a1.ds != a2.ds || a1.lp != a2.lp {
            self.trace(|| format!("join at {:x}: the paths' frames differ", a));
            return Ok(None);
        }
        // the branch where the paths parted (a claim's pattern: its splits
        // those before its paths parted)
        // (the same branch taken the same way: its other side the same --
        // the facts' counts may differ, a claim's walk having its own)
        let common = a1.splits.len().min(a2.splits.len());
        let si = (0..common).find(|&i| a1.splits[i].other != a2.splits[i].other).unwrap_or(common);
        if si >= a2.splits.len() {
            self.trace(|| format!("join at {:x}: no branch where the paths parted", a));
            return Ok(None);
        }
        let mut sp = a2.splits[si].clone();
        // the facts kept: those both had before (the same, in order); the
        // others premises if alike
        let prefix = |x: &[Term], y: &[Term], cap: usize| x.iter().zip(y.iter()).take(cap).take_while(|(u, v)| u == v).count();
        sp.hyps = prefix(&a1.hyps, &a2.hyps, sp.hyps);
        sp.facts = prefix(&a1.facts, &a2.facts, sp.facts);
        // the states anti-unified
        let n = self.fresh("");
        let name = format!("j{n}_");
        let mut tab = Vec::new();
        // (widening: a claim generalized again -- the point reached from
        // more contexts -- has every home's value a variable, but a literal)
        if WIDEN && a1.pattern {
            for (k, nb, x1) in &a1.homes {
                let Some((_, _, x2)) = a2.homes.iter().find(|h| h.0 == *k && h.1 == *nb) else { continue };
                let literal = |x: &Term| matches!(x.node(), Node::Nat(_)) || matches!(x.node(), Node::App(_, args) if args.is_empty());
                if !literal(x1) && !literal(x2) && !tab.iter().any(|(u, v, _)| u == x1 && v == x2) {
                    let y = self.var(&format!("{}{}", name, tab.len()));
                    tab.push((x1.clone(), x2.clone(), y));
                }
            }
        }
        let spec = match (&a1.spec, &a2.spec) {
            (SpecX::Proc(q1), SpecX::Proc(q2)) => self.au(q1, q2, &mut tab, false, &name).map(SpecX::Proc),
            (SpecX::Ret(v1, p1), SpecX::Ret(v2, p2)) => match (self.au(v1, v2, &mut tab, false, &name), self.au(p1, p2, &mut tab, false, &name)) {
                (Some(v), Some(p)) => Some(SpecX::Ret(v, p)),
                _ => None,
            },
            _ => None,
        };
        let w = self.au(&a1.w, &a2.w, &mut tab, false, &name);
        // (the homes both paths have, by key: tr.pt_hs gives each its own)
        let mut common: Vec<(u128, u128, Term, Term)> = a2
            .homes
            .iter()
            .filter_map(|(k, nb, x2)| a1.homes.iter().find(|h| h.0 == *k && h.1 == *nb).map(|h| (*k, *nb, h.2.clone(), x2.clone())))
            .collect();
        common.sort_by_key(|h| h.0);
        let mut homes = Vec::new();
        for (k, nb, x1, x2) in &common {
            match self.au(x1, x2, &mut tab, false, &name) {
                Some(x) => homes.push((*k, *nb, x)),
                None => {
                    self.trace(|| format!("join at {:x}: the paths' homes differ under a binder", a));
                    return Ok(None);
                }
            }
        }
        let (Some(spec), Some(w)) = (spec, w) else {
            self.trace(|| {
                // (where: the first subterms that differ)
                fn diff(g: &Gen, x: &Term, y: &Term) -> (Term, Term) {
                    match (x.node(), y.node()) {
                        (Node::App(f, a), Node::App(h, b)) if f == h && a.len() == b.len() => match a.iter().zip(b.iter()).find(|(u, v)| u != v) {
                            Some((u, v)) => diff(g, u, v),
                            None => (x.clone(), y.clone()),
                        },
                        _ => (x.clone(), y.clone()),
                    }
                }
                let (d1, d2) = match (&a1.spec, &a2.spec) {
                    (SpecX::Proc(q1), SpecX::Proc(q2)) => diff(self, q1, q2),
                    _ => diff(self, &a1.w, &a2.w),
                };
                format!("join at {:x}: the paths' states differ under a binder: {} / {}", a, self.lambda(4, &d1), self.lambda(4, &d2))
            });
            return Ok(None);
        };
        let vars: Vec<VarId> = tab.iter().map(|x| Self::var_id(&x.2)).collect();
        // the premises: the facts both assumed after the branch, alike; and
        // those before it about a value abstracted (the others kept)
        let mut prem_h = Vec::new();
        let mut prem_hi = Vec::new();
        let mut kept_hi = Vec::new();
        // (a fact of the second path, its values the variables they are)
        fn abstract2(t: &Term, tab: &[(Term, Term, Term)]) -> Term {
            if let Some((_, _, y)) = tab.iter().find(|(_, x2, _)| x2 == t) {
                return y.clone();
            }
            match t.node() {
                Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => t.with_args(a.iter().map(|x| abstract2(x, tab)).collect()),
                _ => t.clone(),
            }
        }
        for i in 0..sp.hyps {
            let p = abstract2(&a2.hyps[i], &tab);
            if p != a2.hyps[i] {
                prem_h.push(p);
                prem_hi.push(i);
            } else {
                kept_hi.push(i);
            }
        }
        for (i, h2) in a2.hyps.iter().enumerate().skip(sp.hyps) {
            if let Some(p) = a1.hyps[sp.hyps.min(a1.hyps.len())..].iter().find_map(|h1| self.au(h1, h2, &mut tab, true, &name)) {
                prem_h.push(p);
                prem_hi.push(i);
            }
        }
        let mut prem_f = Vec::new();
        let mut kept_fi = Vec::new();
        for i in 0..sp.facts {
            let p = abstract2(&a2.facts[i], &tab);
            if p != a2.facts[i] {
                prem_f.push(p);
            } else {
                kept_fi.push(i);
            }
        }
        for f2 in a2.facts.iter().skip(sp.facts) {
            if let Some(p) = a1.facts[sp.facts.min(a1.facts.len())..].iter().find_map(|f1| self.au(f1, f2, &mut tab, true, &name)) {
                prem_f.push(p);
            }
        }
        // (the claim of the branch's scope: its variables older, or ours)
        let mut vs = Vec::new();
        match &spec {
            SpecX::Proc(q) => q.vars(&mut vs),
            SpecX::Ret(v, p) => {
                v.vars(&mut vs);
                p.vars(&mut vs);
            }
        }
        w.vars(&mut vs);
        for x in homes.iter().map(|h| &h.2).chain(prem_h.iter()).chain(prem_f.iter()) {
            x.vars(&mut vs);
        }
        if vs.iter().any(|v| (*v as usize) >= sp.mark && !vars.contains(v)) {
            self.trace(|| format!("join at {:x}: a value of a path's own not abstracted", a));
            return Ok(None);
        }
        // the generalized state: its world a world, its homes' whole values
        // words, the premises -- assumed
        let univ1 = self.mk("in", vec![w.clone(), self.mk("univ", vec![lit(1)])]);
        let hw_t = self.mk("and", vec![self.mk("in", vec![w.clone(), self.mk("abi.World", vec![])]), univ1.clone()]);
        let hw = self.assume(&hw_t)?;
        let hvu = self.evp(&RP::Taut(vec![R::S(hw.clone())]), &univ1, &[])?;
        let mut prems: Vec<(Prem, Term)> = vec![(Prem::World, hw_t)];
        let mut facts: Vec<Seq> = kept_fi.iter().map(|&i| st.facts[i].clone()).collect();
        let mut lfx = st.lfx.clone();
        for (_, nb, x) in &homes {
            if let Node::Var(v, a) = x.node() {
                if a.is_empty() && vars.contains(v) {
                    let b = self.mk("in", vec![x.clone(), self.mk("bits", vec![lit(8 * nb)])]);
                    let hb = self.assume(&b)?;
                    facts.push(hb.clone());
                    lfx.push(hb);
                    prems.push((Prem::Bits(*v), b));
                }
            }
        }
        // (only facts about the claim's state: a fact of this path's own --
        // a call's result not in the state -- would bind the claim to it)
        let in_state = |f: &Seq| {
            let mut fv = Vec::new();
            f.concl().vars(&mut fv);
            fv.iter().all(|v| vs.contains(v) || vars.contains(v))
        };
        facts.retain(|f| in_state(f));
        lfx.retain(|f| in_state(f));
        let mut hyps: Vec<(Term, Seq)> = kept_hi.iter().map(|&i| st.hyps[i].clone()).collect();
        for p in &prem_h {
            let pc = self.canon(p);
            hyps.push((pc, self.assume(p)?));
            prems.push((Prem::Hyp, p.clone()));
        }
        for p in &prem_f {
            facts.push(self.assume(p)?);
            prems.push((Prem::Fact, p.clone()));
        }
        let mut hst = self.mk("empty", vec![]);
        let mut hsm = BTreeMap::new();
        for (k, nb, x) in &homes {
            let xc = self.canon(x);
            hst = self.upd(&hst, *k, *nb, &xc);
            hsm.insert(*k, (*nb, xc));
        }
        let spec_st = match &spec {
            SpecX::Proc(q) => {
                let j = self.new_q(self.canon(q));
                Spec::Proc(j)
            }
            SpecX::Ret(v, p) => Spec::Ret(self.canon(v), self.canon(p)),
        };
        let stg = St {
            a,
            fr: st.fr,
            regs: Vec::new(),
            rs: self.mk("empty", vec![]),
            ds: st.ds.clone(),
            w: self.canon(&w),
            hvu,
            hw,
            hsm,
            hst,
            lp: st.lp,
            spec: spec_st,
            hyps,
            facts,
            lfx,
            // (its facts renumbered: a branch's condition here unspent)
            bconds: Vec::new(),
            spent: Vec::new(),
            splits: st.splits[..si].to_vec(),
            no_join: Some(a),
            z: None,
        };
        let _ = prem_hi;
        self.trace(|| format!("join at {:x}: its claim, over {} variables, {} premises", a, vars.len(), prems.len()));
        let pf = match self.prove_kept(stg) {
            Ok(pf) => pf,
            Err(e) => {
                self.trace(|| format!("join at {:x}: its claim not proven ({}), the paths on their own", a, e.replace('\n', " / ")));
                return Ok(None);
            }
        };
        // (the premises its proof used)
        let used: Vec<Term> = pf.hyps().to_vec();
        let prems: Vec<(Prem, Term)> = prems.into_iter().filter(|(_, t)| used.contains(&self.expand(t))).collect();
        let hs: Vec<Term> = prems.iter().map(|p| p.1.clone()).collect();
        let claim = match self.close(pf, &hs, &vars) {
            Ok(c) => c,
            Err(e) => {
                self.trace(|| format!("join at {:x}: its claim not closed ({})", a, e));
                return Ok(None);
            }
        };
        let kept: Vec<Term> = kept_hi.iter().map(|&i| a2.hyps[i].clone()).collect();
        let pattern = Arrival {
            a,
            fr: st.fr,
            ds: a2.ds.clone(),
            lp: st.lp,
            splits: st.splits[..si].to_vec(),
            homes: homes.clone(),
            w: w.clone(),
            spec: spec.clone(),
            hyps: kept.iter().chain(prems.iter().filter(|p| matches!(p.0, Prem::Hyp)).map(|p| &p.1)).cloned().collect(),
            facts: kept_fi.iter().map(|&i| a2.facts[i].clone()).chain(prems.iter().filter(|p| matches!(p.0, Prem::Fact)).map(|p| p.1.clone())).collect(),
            pattern: true,
        };
        self.joins.push(Join { a, fr: st.fr, ds: a2.ds.clone(), lp: st.lp, vars, homes, w, spec, prems, claim, pattern });
        Ok(Some(self.joins.len() - 1))
    }

    /// The point claim at st by the join `i`'s claim, if st is its instance
    fn join_use(&mut self, i: usize, st: &St) -> Result<Option<Seq>, String> {
        let j = self.joins[i].clone();
        if j.a != st.a || j.fr != st.fr || j.lp != st.lp {
            return Ok(None);
        }
        let Some(arr) = self.arrival(st) else { return Ok(None) };
        if arr.ds != j.ds {
            return Ok(None);
        }
        // the variables' values: st's state an instance of the claim's (its
        // homes among st's)
        let mut sub = Vec::new();
        let mut why = None;
        if !self.matches(&j.w, &arr.w, &j.vars, &mut sub) {
            why = Some("the world".to_string());
        }
        for (k, nb, px) in &j.homes {
            if why.is_none() && !arr.homes.iter().find(|h| h.0 == *k && h.1 == *nb).is_some_and(|h| self.matches(px, &h.2, &j.vars, &mut sub)) {
                why = Some(format!("the home {:x}", k));
            }
        }
        let spec_ok = why.is_some()
            || match (&j.spec, &arr.spec) {
                (SpecX::Proc(pq), SpecX::Proc(q)) => self.matches(pq, q, &j.vars, &mut sub),
                (SpecX::Ret(pv, pp), SpecX::Ret(v, p)) => self.matches(pv, v, &j.vars, &mut sub) && self.matches(pp, p, &j.vars, &mut sub),
                _ => false,
            };
        if !spec_ok {
            why = Some("the spec".into());
        }
        if why.is_none() && sub.len() != j.vars.len() {
            why = Some("a variable unbound".into());
        }
        // (the facts the claim kept: those its proof used, its sequent's
        // hypotheses -- in st's scope, below)
        if let Some(why) = why {
            self.trace(|| format!("join at {:x}: not an instance of claim {} ({})", st.a, i, why));
            return Ok(None);
        }
        // (the claim's own assumptions in st's scope: a claim made within
        // another's walk may rest on that one's)
        {
            let mut scope: Vec<&Term> = self.ambient.iter().collect();
            let lp = st.lp.map(|l| &self.loops[l]);
            let seqs = [&st.hw, &st.hvu].into_iter().chain(st.hyps.iter().map(|h| &h.1)).chain(st.facts.iter()).chain(st.lfx.iter());
            let seqs = seqs.chain(lp.into_iter().flat_map(|l| [&l.ih, &l.cc, &l.ci]));
            for q in seqs.chain(self.hl.iter()).chain(self.lf0.iter()).chain(self.hcall.iter().flatten()).chain(self.htyp.iter().flatten()).chain(self.hio.iter().flatten()) {
                scope.extend(q.hyps().iter());
            }
            if let Some(h) = j.claim.hyps().iter().find(|h| !scope.contains(h)) {
                self.trace(|| format!("join at {:x}: its claim rests on {}, not here", st.a, self.print(h)));
                return Ok(None);
            }
        }
        // the premises: its world, a home's word (by the facts about its
        // value), st's facts
        let mut args: Vec<RA> = j.vars.iter().map(|v| t(&sub.iter().find(|x| x.0 == *v).unwrap().1)).collect();
        for (kind, p) in &j.prems {
            let a = match kind {
                Prem::World => s(&st.hw),
                Prem::Bits(v) => {
                    let x = sub.iter().find(|s| s.0 == *v).map(|s| s.1.clone()).unwrap();
                    simp_lw(self.facts_about(&st.facts, &x))
                }
                Prem::Hyp | Prem::Fact => {
                    let pi = {
                        let bf = self.env.binders_fn();
                        sub.iter().fold(p.clone(), |x, (v, val)| x.subst_var(*v, val, &bf))
                    };
                    let found = match kind {
                        Prem::Hyp => arr.hyps.iter().position(|h| *h == pi).map(|k| st.hyps[k].1.clone()),
                        _ => arr.facts.iter().position(|f| *f == pi).map(|k| st.facts[k].clone()),
                    };
                    match found {
                        Some(q) => s(&q),
                        None => {
                            self.trace(|| format!("join at {:x}: not an instance of claim {} (a premise not here)", st.a, i));
                            return Ok(None);
                        }
                    }
                }
            };
            args.push(a);
        }
        let c0 = match self.run(&mp(R::S(j.claim.clone()), args), &[]) {
            Ok(c) => c,
            Err(e) => {
                self.trace(|| format!("join at {:x}: not an instance ({})", st.a, e.lines().next().unwrap_or("")));
                return Ok(None);
            }
        };
        self.trace(|| format!("join at {:x}: by its claim", st.a));
        // (st's homes: the claim's, and more -- tr.pt_hs, by tr.hsub_upd per
        // home of the claim's)
        let hs1 = c0.concl().clone();
        let hs1 = self.app(&hs1, "tr.lv", 13).map(|x| x[8].clone()).ok_or("join: the claim's homes")?;
        let empty = self.mk("empty", vec![]);
        let mut sub_pf = mpf("tr.hsub_empty", vec![t(&st.hst)]);
        let mut f = empty.clone();
        for (k, nb, x) in self.home_entries(&hs1).ok_or("join: the claim's homes")? {
            let v = self.mk("pair", vec![lit(nb), x.clone()]);
            sub_pf = mpf("tr.hsub_upd", vec![t(&st.hst), t(&f), t(&lit(k)), t(&v), p(sub_pf), simp_l(), simp_l()]);
            f = self.upd(&f, k, nb, &x);
        }
        let c0 = self.run(
            &mpf(
                "tr.pt_hs",
                vec![
                    t(&self.s.clone()),
                    t(&self.v.clone()),
                    t(&self.base.clone()),
                    t(&self.code.clone()),
                    t(&lit(st.fr)),
                    t(&lit(st.a)),
                    t(&hs1),
                    t(&st.hst),
                    t(&st.ds),
                    t(&empty),
                    t(&self.p(&st.spec)),
                    t(&st.w),
                    p(sub_pf),
                    s(&c0),
                ],
            ),
            &[],
        )?;
        let rs = mpf(
            "tr.pt_rs",
            vec![
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
                s(&c0),
            ],
        );
        self.run(&rs, &[]).map(Some)
    }
}
