//! The spec's side: its operations' and stores' rules, the reductions of
//! its rest.

use super::rec::*;
use super::*;

impl<'e> Gen<'e> {
    /// A rule's instance by its parameters' names (a sequent), its
    /// statement.
    pub(super) fn inst(&mut self, lemma: &str, args: &[(&'static str, Term)]) -> Result<(R, Term), String> {
        let r = R::Inst(lemma.to_string(), args.to_vec());
        let s = self.ev(&r, &[])?;
        let stmt = s.concl().clone();
        Ok((R::S(s), stmt))
    }

    /// a reduction lemma's instance: its `runs(q2, w, o) -> runs(q, w, o)`
    pub(super) fn qparts(&self, t: &Term) -> Option<(Term, Term)> {
        let mut t = t.clone();
        loop {
            if let Some(a) = self.app(&t, "all", 1) {
                t = a[0].clone();
                continue;
            }
            let Node::App(s, a) = t.node() else { return None };
            if *s != self.env.builtins.imp {
                return None;
            }
            if let (Some(x), Some(y)) = (self.app(&a[0], "runs", 3), self.app(&a[1], "runs", 3)) {
                let bf = self.env.binders_fn();
                if x[0].loose_depth(&bf) == 0 && y[0].loose_depth(&bf) == 0 {
                    return Some((y[0].clone(), x[0].clone()));
                }
            }
            t = a[1].clone();
        }
    }

    /// The reduction by `lemma` at `args` of the rest `qi`: the reduced
    /// rest (checked: the instance's rest is `qi`'s), the instance
    pub(super) fn by(&mut self, qi: usize, lemma: &str, args: &[(&'static str, Term)]) -> Result<(usize, R), String> {
        let (r, stmt) = self.inst(lemma, args)?;
        let (q, q2) = self.qparts(&stmt).ok_or_else(|| format!("{}: not a reduction", lemma))?;
        let (q, q2) = (self.canon(&q), self.canon(&q2));
        if q != self.canon(&self.qs[qi]) {
            return Err(format!("{} does not fit the rest:\n  {}\n  {}", lemma, self.print(&q), self.print(&self.qs[qi])));
        }
        let j = self.new_q(q2);
        Ok((j, r))
    }

    /// a guard's value: a literal comparison, a fact in scope
    fn guard(&self, g: &Term, hyps: &[(Term, Seq)]) -> Option<(bool, RA)> {
        let (v, facts) = self.guard_facts(g, hyps)?;
        // (the facts it was decided by: a branch condition among them spent)
        if v {
            self.picked.borrow_mut().extend(facts.iter().map(|f| f.concl().clone()));
        }
        // (the fact itself, or simp from the facts it rests on)
        if v && facts.len() == 1 && self.hyp_find(hyps, g).is_some() {
            return Some((v, s(&facts[0])));
        }
        Some((v, simpw(facts.into_iter().map(R::S).collect())))
    }

    /// a guard's value, and the facts in scope it rests on
    fn guard_facts(&self, g: &Term, hyps: &[(Term, Seq)]) -> Option<(bool, Vec<Seq>)> {
        if let Some(h) = self.hyp_find(hyps, g) {
            return Some((true, vec![h.1.clone()]));
        }
        if self.app(g, "true", 0).is_some() {
            return Some((true, vec![]));
        }
        let join = |mut x: Vec<Seq>, y: Vec<Seq>| {
            for f in y {
                if !x.iter().any(|z| z.concl() == f.concl()) {
                    x.push(f);
                }
            }
            x
        };
        if let Some(a) = self.app(g, "not", 1) {
            let (v, f) = self.guard_facts(&a[0], hyps)?;
            return Some((!v, f));
        }
        if let Some(a) = self.app(g, "and", 2) {
            let (x, f) = self.guard_facts(&a[0], hyps)?;
            let (y, f2) = self.guard_facts(&a[1], hyps)?;
            return Some((x && y, join(f, f2)));
        }
        if let Some(a) = self.app(g, "or", 2) {
            let (x, f) = self.guard_facts(&a[0], hyps)?;
            let (y, f2) = self.guard_facts(&a[1], hyps)?;
            return Some((x || y, join(f, f2)));
        }
        if let Some(a) = self.app(g, "eq", 2) {
            if a[0] == a[1] && g.loose_depth(&self.env.binders_fn()) == 0 {
                return Some((true, vec![]));
            }
            let v = match (a[0].node(), a[1].node()) {
                (Node::Nat(x), Node::Nat(y)) => x == y,
                (Node::Bytes(x), Node::Bytes(y)) => x == y,
                _ => return None,
            };
            return Some((v, vec![]));
        }
        None
    }

    /// the way to a disjunct whose guard holds
    fn pick(&self, t: &Term, hyps: &[(Term, Seq)]) -> Option<Vec<Pick>> {
        if let Some(a) = self.app(t, "and", 2) {
            if a[0].loose_depth(&self.env.binders_fn()) == 0 {
                if let Some((true, pf)) = self.guard(&a[0], hyps) {
                    return Some(vec![Pick::And(a[0].clone(), pf)]);
                }
            }
            return None;
        }
        if let Some(a) = self.app(t, "or", 2) {
            // (choosing an alternative: not by a branch condition spent)
            let spent = self.spent_now.borrow().clone();
            let usable: Vec<(Term, Seq)> = hyps.iter().filter(|h| !spent.contains(&self.expand(&h.0))).cloned().collect();
            if let Some(mut p) = self.pick(&a[0], &usable) {
                p.insert(0, Pick::L);
                return Some(p);
            }
            if let Some(mut p) = self.pick(&a[1], &usable) {
                p.insert(0, Pick::R);
                return Some(p);
            }
        }
        None
    }

    /// A projection of a constructed outcome (or pair) in the rest's body
    /// (of x0 only): its lemma, and its parts (at the body)
    fn redex(&self, t: &Term, depth: u32) -> Option<(&'static str, Term, Term, Term)> {
        let kinds: [(&str, &str, &'static str); 8] = [
            ("fst", "ok", "tr.qe_fst_ok"),
            ("fst", "exc", "tr.qe_fst_exc"),
            ("out_state", "ok", "tr.qe_os_ok"),
            ("out_value", "ok", "tr.qe_ov_ok"),
            ("out_state", "exc", "tr.qe_os_exc"),
            ("out_value", "exc", "tr.qe_ov_exc"),
            ("fst", "pair", "tr.qe_fst_pair"),
            ("snd", "pair", "tr.qe_snd_pair"),
        ];
        let lift = |x: &Term| self.remap(x, 0, &|j| (j == depth + 1).then_some(1));
        if let Node::App(_, a) = t.node() {
            for (f, c, lemma) in kinds {
                if let Some(x) = self.app(t, f, 1) {
                    if let Some(y) = self.app(&x[0], c, 2) {
                        if let (Some(s), Some(v), Some(r)) = (lift(&y[0]), lift(&y[1]), lift(t)) {
                            return Some((lemma, r, s, v));
                        }
                    }
                }
            }
            let Node::App(s, _) = t.node() else { unreachable!() };
            let bs = self.env.syms[*s as usize].binders.clone();
            for (x, k) in a.iter().zip(bs) {
                if let Some(r) = self.redex(x, depth + k) {
                    return Some(r);
                }
            }
        }
        None
    }

    /// An equation of a term (of x0 only) with itself in the rest's body:
    /// it, its side (at the body)
    fn refl_redex(&self, t: &Term, depth: u32) -> Option<(Term, Term)> {
        let lift = |x: &Term| self.remap(x, 0, &|j| (j == depth + 1).then_some(1));
        if let Some(e) = self.app(t, "eq", 2) {
            if e[0] == e[1] {
                if let (Some(r), Some(s)) = (lift(t), lift(&e[0])) {
                    return Some((r, s));
                }
            }
        }
        if let Node::App(s, a) = t.node() {
            let bs = self.env.syms[*s as usize].binders.clone();
            for (x, k) in a.iter().zip(bs) {
                if let Some(r) = self.refl_redex(x, depth + k) {
                    return Some(r);
                }
            }
        }
        None
    }

    /// `bits_of_int(n, x)` (closed) with x a whole n-bit field
    /// (`int_mod(int_div(b, int_pow(2, 0)), int_pow(2, n))`): it, n, b
    fn whole_field(&self, t: &Term) -> Option<(Term, u128, Term)> {
        if let Some(a) = self.app(t, "bits_of_int", 2) {
            if let Some(n) = nat(&a[0]) {
                if [8, 16, 32, 64].contains(&n) && t.loose_depth(&self.env.binders_fn()) == 0 {
                    let x = self.expand(&a[1]);
                    let field = (|| {
                        let m = self.app(&x, "int_mod", 2)?;
                        let d = self.app(&m[0], "int_div", 2)?;
                        let p0 = self.app(&d[1], "int_pow", 2)?;
                        let pn = self.app(&m[1], "int_pow", 2)?;
                        (nat(&p0[0])? == 2 && nat(&p0[1])? == 0 && nat(&pn[0])? == 2 && nat(&pn[1])? == n).then(|| d[0].clone())
                    })();
                    if let Some(b) = field {
                        return Some((t.clone(), n, b));
                    }
                }
            }
        }
        if let Node::App(_, a) = t.node() {
            for x in a.iter() {
                if let Some(r) = self.whole_field(x) {
                    return Some(r);
                }
            }
        }
        None
    }

    /// `t` (at depth d below the body) with `r` (at the body) abstracted:
    /// the body as a value of x0 x1 y
    fn abstract_(&self, t: &Term, r: &Term, depth: u32) -> Term {
        let bf = self.env.binders_fn();
        if *t == r.shift(depth, 0, &bf) {
            return Term::bvar(depth);
        }
        match t.node() {
            Node::BVar(i) if *i >= depth => Term::bvar(i + 1),
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.abstract_(x, r, depth)).collect()),
            Node::App(s, a) => {
                let bs = self.env.syms[*s as usize].binders.clone();
                t.with_args(a.iter().zip(bs).map(|(x, k)| self.abstract_(x, r, depth + k)).collect())
            }
        }
    }

    /// the signed type of n bits
    fn sty(&self, n: u128) -> Term {
        self.mk("fn_update", vec![self.mk("fn_update", vec![self.mk("empty", vec![]), Term::bytes(b"prec"), lit(n)]), Term::bytes(b"signed"), self.mk("true", vec![])])
    }

    /// the current world's set fact
    fn hv(&self) -> R {
        R::S(self.hvu.clone().expect("a point's world"))
    }

    /// the entry view's set fact
    fn hvu_w(&self) -> R {
        R::S(self.hvu0.clone().expect("the entry's world"))
    }

    /// An operation's rule `rule` at the current world: `ok` -- the
    /// operation's run to its value (the slot `HC` its definedness) -- and
    /// `ub` -- its raise when undefined (`HN`)
    fn ok_ub(&self, rule_ok: &str, rule_ub: &str, ts: &[Term], ok_tail: Vec<RA>, ub_mid: Vec<RA>) -> (RA, RA) {
        let w = self.w.clone();
        let mut oa = vec![t(&w)];
        oa.extend(ts.iter().map(t));
        oa.push(p(self.hv()));
        oa.extend(ok_tail);
        let mut ua = vec![t(&w)];
        ua.extend(ts.iter().map(t));
        ua.extend([t(&self.vw), t(&self.mk("empty", vec![])), p(self.hv()), p(self.hvu_w()), simp0()]);
        ua.extend(ub_mid);
        ua.push(p(R::Slot("HN")));
        (p(mpf(rule_ok, oa)), p(mpf(rule_ub, ua)))
    }

    /// An operation at the head: its definedness (none when literally
    /// defined), its value, its run's justification (`HC`), its raise's
    /// (`HN`).
    pub(super) fn op(&mut self, op: &Term) -> Result<(Option<Term>, Term, RA, Option<RA>), String> {
        let hc = || p(R::Slot("HC"));
        if let Some(x) = self.app(op, "gimple.sadd", 3) {
            if nat(&x[0]) == Some(32) {
                let (a, b) = (x[1].clone(), x[2].clone());
                let s32 = |g: &Gen, t: &Term| g.mk("sint", vec![lit(32), t.clone()]);
                let cond = self.mk("gimple.fits", vec![self.sty(32), self.mk("int_add", vec![s32(self, &a), s32(self, &b)])]);
                let r = self.mk("bits_add", vec![lit(32), a.clone(), b.clone()]);
                let (ok, ub) = self.ok_ub("tr.sadd32_ok", "tr.sadd32_ub", &[a, b], vec![simp_l(), simp_l(), hc()], vec![]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        if let Some(x) = self.app(op, "gimple.ssub", 3) {
            if nat(&x[0]) == Some(32) {
                let (a, b) = (x[1].clone(), x[2].clone());
                let s32 = |g: &Gen, t: &Term| g.mk("sint", vec![lit(32), t.clone()]);
                let cond = self.mk("gimple.fits", vec![self.sty(32), self.mk("int_sub", vec![s32(self, &a), s32(self, &b)])]);
                let la = self.lit_bits(&a);
                let r = self.mk("bits_sub", vec![lit(32), la.clone(), b.clone()]);
                let (ok, _) = if la != a {
                    self.ok_ub("tr.ssub32_ok_lit", "tr.ssub32_ub", &[la, b.clone()], vec![simp_l(), simp_l(), hc()], vec![])
                } else {
                    self.ok_ub("tr.ssub32_ok", "tr.ssub32_ub", &[a.clone(), b.clone()], vec![simp_l(), simp_l(), hc()], vec![])
                };
                let (_, ub) = self.ok_ub("tr.ssub32_ok", "tr.ssub32_ub", &[a, b], vec![], vec![]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
            // (of 64 bits: a pointer difference)
            if nat(&x[0]) == Some(64) {
                let (a, b) = (x[1].clone(), x[2].clone());
                let s64 = |g: &Gen, t: &Term| g.mk("sint", vec![lit(64), t.clone()]);
                let cond = self.mk("gimple.fits", vec![self.sty(64), self.mk("int_sub", vec![s64(self, &a), s64(self, &b)])]);
                let r = self.mk("bits_sub", vec![lit(64), a.clone(), b.clone()]);
                let (ok, ub) = self.ok_ub("tr.ssub64_ok", "tr.ssub64_ub", &[a, b], vec![simp_l(), simp_l(), hc()], vec![]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        if let Some(x) = self.app(op, "gimple.sneg", 2) {
            if nat(&x[0]) == Some(32) {
                let a = x[1].clone();
                let cond = self.mk("gimple.fits", vec![self.sty(32), self.mk("int_neg", vec![self.mk("sint", vec![lit(32), a.clone()])])]);
                let r = self.mk("bits_sub", vec![lit(32), lit(0), a.clone()]);
                let (ok, ub) = self.ok_ub("tr.sneg32_ok", "tr.sneg32_ub", &[a], vec![simp_l(), hc()], vec![]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        if let Some(x) = self.app(op, "gimple.padd", 2) {
            let (pp, d) = (x[0].clone(), x[1].clone());
            if let (Some(_), Some(dv)) = (self.eval_lit(&pp), self.eval_lit(&d)) {
                if dv < 1 << 63 {
                    let r = self.mk("int_add", vec![pp.clone(), d.clone()]);
                    let (ok, _) = self.ok_ub("tr.padd_ok", "tr.padd_ub", &[pp, d], vec![simp_l(), simp_l(), simp_l(), simp_l()], vec![]);
                    return Ok((None, r, ok, None));
                }
            }
            // a pointer's: p + d in 64 bits, when in the address range
            // (tr.padd_def, as it expands)
            let sum = self.mk("int_add", vec![pp.clone(), self.mk("gimple.sval", vec![self.sty(64), d.clone()])]);
            let cond = self.mk("and", vec![self.mk("int_le", vec![lit(0), sum.clone()]), self.mk("int_lt", vec![sum, lit(P64)])]);
            let r = self.mk("bits_add", vec![lit(64), pp.clone(), d.clone()]);
            let (ok, ub) = self.ok_ub("tr.padd_okb", "tr.padd_ub", &[pp, d], vec![simp_l(), simp_l(), hc()], vec![simp_l(), simp_l()]);
            return Ok((Some(cond), r, ok, Some(ub)));
        }
        if let Some(x) = self.app(op, "gimple.elem", 3) {
            if nat(&x[2]) == Some(1) {
                let pp = x[0].clone();
                let ix = self.expand(&x[1]);
                let (i, kind) = match self.app(&ix, "bits_sext", 3) {
                    Some(y) if nat(&y[0]) == Some(32) && nat(&y[1]) == Some(64) => (self.canon(&y[2]), "sx"),
                    _ => (x[1].clone(), "u"),
                };
                // (the definedness, as tr.elem_sx_def / tr.elem_u_def expand)
                let cond = if kind == "sx" {
                    let s = self.mk("sint", vec![lit(32), i.clone()]);
                    let sum = self.mk("int_add", vec![pp.clone(), s]);
                    self.mk("and", vec![self.mk("int_le", vec![lit(0), sum.clone()]), self.mk("int_lt", vec![sum, lit(P64)])])
                } else {
                    self.mk("int_lt", vec![self.mk("int_add", vec![pp.clone(), i.clone()]), lit(P64)])
                };
                let r = self.mk("bits_add", vec![lit(64), pp.clone(), x[1].clone()]);
                let (ok, ub) = self.ok_ub(&format!("tr.elem1_{}_ok", kind), &format!("tr.elem1_{}_ub", kind), &[pp, i], vec![simp_l(), simp_l(), hc()], vec![simp_l(), simp_l()]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        if let Some(x) = self.app(op, "gimple.ld8", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.ld8_cond(&a);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(1)])]);
                let (ok, _) = self.ok_ub("g.ld8_ok", "g.ld8_ub", &[a.clone()], vec![simp_l(), taut(vec![R::Slot("HC")]), taut(vec![R::Slot("HC")])], vec![]);
                // (g.ld8_ub: its condition before the address's range)
                let w = self.w.clone();
                let ub = p(mpf(
                    "g.ld8_ub",
                    vec![t(&w), t(&a), t(&self.vw), t(&self.mk("empty", vec![])), p(self.hv()), p(self.hvu_w()), simp0(), p(R::Slot("HN")), simp_l()],
                ));
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        // a byte load at a static's field: p + off, both literals (the
        // address computed)
        if let Some(x) = self.app(op, "gimple.ld8", 2) {
            if let (Some(pv), Some(ov)) = (self.eval_lit(&x[0]), self.eval_lit(&x[1])) {
                let (pp, off, a) = (x[0].clone(), x[1].clone(), lit((pv + ov) % P64));
                let cond = self.mem_defined(&self.w.clone(), &pp, &off, 1, false);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(1)])]);
                let w = self.w.clone();
                let ok = p(mpf("tr.ld8_at_ok", vec![t(&w), t(&pp), t(&off), t(&a), p(self.hv()), simp_l(), simp_l(), simp_l(), hc()]));
                let (_, ub) = self.ok_ub("g.ld8_at_ok", "g.ld8_at_ub", &[pp, off], vec![], vec![simp_l(), simp_l()]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        // a 2-byte load
        if let Some(x) = self.app(op, "gimple.ld16", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.mem_defined(&self.w.clone(), &a, &lit(0), 2, false);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(16), self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(2)])]);
                let (ok, ub) = self.ok_ub("g.ld16_ok", "g.ld16_ub", &[a], vec![simp_l(), hc()], vec![simp_l()]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        // a 4-byte load
        if let Some(x) = self.app(op, "gimple.ld32", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.mem_defined(&self.w.clone(), &a, &lit(0), 4, false);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(32), self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(4)])]);
                let (ok, ub) = self.ok_ub("g.ld32_ok", "g.ld32_ub", &[a], vec![simp_l(), hc()], vec![simp_l()]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        // an array's 2-byte element at a sign-extended 32-bit index
        if let Some(x) = self.app(op, "gimple.elem", 3) {
            let ix = self.expand(&x[1]);
            if let (Some(2), Some(y)) = (nat(&x[2]), self.app(&ix, "bits_sext", 3)) {
                if nat(&y[0]) == Some(32) && nat(&y[1]) == Some(64) {
                    let (pp, i) = (x[0].clone(), self.canon(&y[2]));
                    let cond = self.mk("tr.elem2_sx_def", vec![pp.clone(), i.clone()]);
                    let sx = self.mk("bits_sext", vec![lit(32), lit(64), i.clone()]);
                    let r = self.mk("bits_add", vec![lit(64), pp.clone(), self.mk("bits_add", vec![lit(64), sx.clone(), sx])]);
                    let (ok, ub) = self.ok_ub("tr.elem2_sx_ok", "tr.elem2_sx_ub", &[pp, i], vec![simp_l(), simp_l(), hc()], vec![simp_l(), simp_l()]);
                    return Ok((Some(cond), r, ok, Some(ub)));
                }
            }
        }
        // a 64-bit field load at p + off (off a literal)
        if let Some(x) = self.app(op, "gimple.ld64", 2) {
            if nat(&x[1]).is_some() {
                let (pp, off) = (x[0].clone(), x[1].clone());
                let cond = self.mem_defined(&self.w.clone(), &pp, &off, 8, false);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(64), self.mk("gimple.bytes_at", vec![vm, self.mk("bits_add", vec![lit(64), pp.clone(), off.clone()]), lit(8)])]);
                let (ok, ub) = self.ok_ub("tr.ld64_ok", "tr.ld64_ub", &[pp, off], vec![simp_l(), simp_l(), hc()], vec![simp_l(), simp_l()]);
                return Ok((Some(cond), r, ok, Some(ub)));
            }
        }
        // a bitfield load: n bytes at p + off, bits pos.., k of them
        if let Some(x) = self.app(op, "gimple.ldbf", 5) {
            let x = x.to_vec();
            let cond = self.mem_defined_t(&self.w.clone(), &x[0], &x[1], &x[2], false);
            let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
            let by = self.mk("gimple.bytes_at", vec![vm, self.mk("bits_add", vec![lit(64), x[0].clone(), x[1].clone()]), x[2].clone()]);
            let r = self.mk(
                "int_mod",
                vec![self.mk("int_div", vec![by, self.mk("int_pow", vec![lit(2), x[3].clone()])]), self.mk("int_pow", vec![lit(2), x[4].clone()])],
            );
            let (ok, ub) = self.ok_ub("tr.ldbf_ok", "g.ldbf_ub", &x, vec![simp_l(), simp_l(), hc()], vec![simp_l(), simp_l()]);
            return Ok((Some(cond), r, ok, Some(ub)));
        }
        // a signed 32-bit product by an immediate (tr.imul_by(k), proven per
        // immediate)
        if let Some(x) = self.app(op, "gimple.smul", 3) {
            if let (Some(32), Some(k)) = (nat(&x[0]), nat(&x[2])) {
                if k < 1 << 31 {
                    let a = x[1].clone();
                    let ib = self.imul_fact(k)?;
                    let cond = self.mk("gimple.fits", vec![self.sty(32), self.mk("int_mul", vec![self.mk("sint", vec![lit(32), a.clone()]), self.mk("sint", vec![lit(32), lit(k)])])]);
                    let r = self.mk("bits_mul", vec![lit(32), a.clone(), lit(k)]);
                    let (ok, ub) = self.ok_ub("tr.smul32_ok", "tr.smul32_ub", &[a, lit(k)], vec![simp_l(), simp_l(), s(&ib), hc()], vec![]);
                    return Ok((Some(cond), r, ok, Some(ub)));
                }
            }
        }
        // a call of a one-operation helper (a field's accessor): its
        // operation's definedness, its value through the helper's result
        if let Node::App(f, args) = op.node() {
            if let SymKind::Defined { params, body } = &self.env.syms[*f as usize].kind {
                let fname = self.env.syms[*f as usize].name.clone();
                let mut b = body.clone();
                for (pa, x) in params.clone().iter().zip(args.iter()) {
                    b = b.subst_var(*pa, x, &self.env.binders_fn());
                }
                let parts = (|| -> Option<(Term, Term)> {
                    let m = self.app(&b, "mkprog", 1)?;
                    let br = self.app(&m[0], "bind_rel", 5)?;
                    matches!(br[1].node(), Node::BVar(1)).then_some(())?;
                    // x1 = ok(x2, f(x3)), the standard handlers
                    let e = self.app(&br[2], "eq", 2)?;
                    let o = self.app(&e[1], "ok", 2)?;
                    (matches!(e[0].node(), Node::BVar(2)) && matches!(o[0].node(), Node::BVar(1))).then_some(())?;
                    let fl = self.lam(&o[1], &["x0", "x1", "x2", "x3"], &["x3"])?;
                    Some((br[0].clone(), fl))
                })();
                if let Some((op2, fl)) = parts {
                    let (cond, r2, ok2, ub2) = self.op(&op2)?;
                    let r = fl.instantiate_params(&[r2.clone()], &self.env.binders_fn());
                    let (okl, _) = self.inst("tr.call1_ok", &[("op", op2.clone()), ("r", r2.clone()), ("f", fl.clone())])?;
                    let w = self.w.clone();
                    let ok = RA::P(RP::Defs(Box::new(RP::Mp(okl, vec![t(&w), p(self.hv()), simp_l(), ok2])), vec![fname.clone()]));
                    let ub = match (cond.is_some(), ub2) {
                        (true, Some(ub2)) => {
                            let (ubl, _) = self.inst("tr.call1_ub", &[("op", op2.clone()), ("s2", self.vw.clone()), ("e", self.mk("empty", vec![])), ("f", fl.clone())])?;
                            Some(RA::P(RP::Defs(Box::new(RP::Mp(ubl, vec![t(&w), p(self.hv()), p(self.hvu_w()), simp0(), ub2])), vec![fname])))
                        }
                        _ => None,
                    };
                    return Ok((cond, r, ok, ub));
                }
            }
        }
        Err(format!("no rule for the operation {}", self.print(op)))
    }

    /// `g.mem_defined(w, p, off, n, write)`
    pub(super) fn mem_defined(&self, w: &Term, pp: &Term, off: &Term, n: u128, write: bool) -> Term {
        self.mem_defined_t(w, pp, off, &lit(n), write)
    }

    pub(super) fn mem_defined_t(&self, w: &Term, pp: &Term, off: &Term, n: &Term, write: bool) -> Term {
        self.mk("g.mem_defined", vec![w.clone(), pp.clone(), off.clone(), n.clone(), self.mk(if write { "true" } else { "false" }, vec![])])
    }

    /// A store at the head: `gimple.st8(p, off, v)` (16, 32, 64, bytes),
    /// or a helper's call whose body is one (`mkprog(x0 x1. bind_rel(st8(..),
    /// x0, x2 x3. x1 = ok(x2, empty), ..))`)
    pub(super) fn store_op(&mut self, op: &Term) -> Result<Option<StoreOp>, String> {
        let is_store = |g: &Gen, t: &Term| {
            g.app(t, "gimple.st8", 3).is_some() || g.app(t, "gimple.st16", 3).is_some() || g.app(t, "gimple.st32", 3).is_some() || g.app(t, "gimple.st64", 3).is_some() || g.app(t, "gimple.st_bytes", 3).is_some()
        };
        let (inner, helper) = if is_store(self, op) {
            (op.clone(), None)
        } else {
            let Node::App(f, args) = op.node() else { return Ok(None) };
            let SymKind::Defined { params, body } = &self.env.syms[*f as usize].kind else { return Ok(None) };
            let fname = self.env.syms[*f as usize].name.clone();
            let mut b = body.clone();
            for (pa, x) in params.clone().iter().zip(args.iter()) {
                b = b.subst_var(*pa, x, &self.env.binders_fn());
            }
            let inner = (|| {
                let m = self.app(&b, "mkprog", 1)?;
                let br = self.app(&m[0], "bind_rel", 5)?;
                matches!(br[1].node(), Node::BVar(1)).then_some(())?;
                is_store(self, &br[0]).then_some(())?;
                let e = self.app(&br[2], "eq", 2)?;
                let o = self.app(&e[1], "ok", 2)?;
                (matches!(e[0].node(), Node::BVar(2)) && matches!(o[0].node(), Node::BVar(1)) && self.app(&o[1], "empty", 0).is_some()).then_some(())?;
                Some(br[0].clone())
            })();
            let Some(inner) = inner else { return Ok(None) };
            (inner, Some(fname))
        };
        // (constant bytes: all zero, else not covered)
        let mut data = None;
        let (n, x) = match (self.app(&inner, "gimple.st8", 3), self.app(&inner, "gimple.st32", 3), self.app(&inner, "gimple.st_bytes", 3)) {
            (Some(x), _, _) => (1, x.to_vec()),
            (_, Some(x), _) => (4, x.to_vec()),
            (_, _, Some(x)) => {
                let items = self.list_items(&x[2]).ok_or("st_bytes of a list that is not a literal")?;
                if items.is_empty() || items.iter().any(|t| nat(t) != Some(0)) {
                    return Err(format!("st_bytes of {}: only zeros covered", self.print(&x[2])));
                }
                data = Some(x[2].clone());
                (items.len() as u128, vec![x[0].clone(), x[1].clone(), lit(0)])
            }
            _ if self.app(&inner, "gimple.st16", 3).is_some() => (2, self.app(&inner, "gimple.st16", 3).unwrap().to_vec()),
            _ => (8, self.app(&inner, "gimple.st64", 3).unwrap().to_vec()),
        };
        let (pp, off, v) = (x[0].clone(), x[1].clone(), x[2].clone());
        let addr = match (self.eval_lit(&pp), self.eval_lit(&off)) {
            (Some(pv), Some(ov)) => lit((pv + ov) % P64),
            // (a 64-bit field: at p + off, as the machine's [b + d])
            _ if (n == 8 || data.is_some()) && nat(&off).is_some() => self.mk("bits_add", vec![lit(64), pp.clone(), off.clone()]),
            _ if nat(&off) == Some(0) => pp.clone(),
            _ => return Err(format!("a store at {} + {}: not covered yet", self.print(&pp), self.print(&off))),
        };
        let w = self.w.clone();
        let cond = self.mem_defined(&w, &pp, &off, n, true);
        let empty = self.mk("empty", vec![]);
        let inner_ub = match &data {
            Some(d) => mpf(
                "g.stz_ub",
                vec![t(&w), t(&pp), t(&off), t(d), t(&self.vw), t(&empty), t(&lit(n)), p(self.hv()), p(self.hvu_w()), simp0(), simp_l(), simp_l(), arith(vec![]), p(R::Slot("HN"))],
            ),
            None => mpf(
                &format!("g.st{}_at_ub", 8 * n),
                vec![t(&w), t(&pp), t(&off), t(&v), t(&self.vw), t(&empty), p(self.hv()), p(self.hvu_w()), simp0(), simp_l(), simp_l(), p(R::Slot("HN"))],
            ),
        };
        let ub = match &helper {
            None => p(inner_ub),
            Some(fname) => {
                let (ubl, _) = self.inst("tr.call1_ub", &[("op", inner.clone()), ("s2", self.vw.clone()), ("e", empty.clone()), ("f", empty.clone())])?;
                RA::P(RP::Defs(Box::new(RP::Mp(ubl, vec![t(&w), p(self.hv()), p(self.hvu_w()), simp0(), p(inner_ub)])), vec![fname.clone()]))
            }
        };
        Ok(Some(StoreOp { n, cond, p: pp, off, v, addr, inner, helper, ub, data }))
    }

    /// `l in list_type(omega) && tr.zeros(l)` for a list literal of zeros
    /// (left-nested, as GIMPLE's): tr.zeros_one, then tr.zeros_snoc
    pub(super) fn zeros_proof(&self, l: &Term) -> Result<R, String> {
        if self.app(l, "seq_one", 1).is_some() {
            return Ok(f("tr.zeros_one"));
        }
        let x = self.app(l, "seq_concat", 2).filter(|x| self.app(&x[1], "seq_one", 1).is_some()).ok_or("a list of zeros not left-nested")?;
        Ok(R::Apply(Box::new(f("tr.zeros_snoc")), vec![p(self.zeros_proof(&x[0])?)]))
    }

    /// `[b + d]` (b a register, no index): b's number, b, d
    pub(super) fn base_disp(&self, t: &Term) -> Option<(u128, Term, Term)> {
        let m = self.memop(t)?;
        let (bk, b) = self.tag(m.get("base")?)?;
        (bk == 2 && nat(m.get("seg")?)? == 0 && self.app(m.get("index")?, "none", 0).is_some() && nat(m.get("scale")?)? == 1).then_some(())?;
        Some((nat(&b)?, b, m["disp"].clone()))
    }

    /// the fact in scope that the spec's n-byte load at p + d is defined
    pub(super) fn mem_hyp(&mut self, st: &St, pp: &Term, d: &Term, n: u128) -> Result<Seq, String> {
        let cond = self.mem_defined(&st.w, pp, d, n, false);
        self.hyp_find(&st.hyps, &cond).map(|h| h.1.clone()).ok_or_else(|| {
            let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
            format!("{:x}: a load of {} bytes at {} + {} the spec does not make (the facts: {})", st.a, n, self.print(pp), self.print(d), facts.join(", "))
        })
    }

    /// the fact in scope that the spec's byte load (or store) at the static
    /// address a is defined (its address p + off, literals)
    pub(super) fn static_hyp(&self, st: &St, a: u128, write: bool) -> Result<Seq, String> {
        fn usable<'t>(g: &Gen, t: &'t Term, out: &mut Vec<&'t Term>) {
            if g.app(t, "gimple.usable", 5).is_some() {
                out.push(t);
                return;
            }
            if let Node::App(_, xs) = t.node() {
                for x in xs.iter() {
                    usable(g, x, out);
                }
            }
        }
        for (h, pf) in &st.hyps {
            let mut us = Vec::new();
            usable(self, h, &mut us);
            for u in us {
                let x = self.app(u, "gimple.usable", 5).unwrap();
                let wr = self.app(&x[4], "true", 0).is_some();
                if x[0] == self.mk("app", vec![st.w.clone(), Term::bytes(b"vm")]) && nat(&x[3]) == Some(1) && wr == write {
                    let at = self.app(&x[2], "int_add", 2).and_then(|s| Some((self.eval_lit(&s[0])? + self.eval_lit(&s[1])?) % P64)).or_else(|| self.eval_lit(&x[2]));
                    if at == Some(a) {
                        return Ok(pf.clone());
                    }
                }
            }
        }
        Err(format!("{:x}: an access at the static {:x} the spec does not make", st.a, a))
    }

    /// a byte load's definedness at a
    pub(super) fn ld8_cond(&self, a: &Term) -> Term {
        let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
        let nz = self.mk("not", vec![self.mk("eq", vec![a.clone(), lit(0)])]);
        let ob = self.mk("app", vec![self.w.clone(), Term::bytes(b"objs")]);
        let us = self.mk("gimple.usable", vec![vm, ob, a.clone(), lit(1), self.mk("false", vec![])]);
        self.mk("and", vec![nz, us])
    }

    /// the items of a list literal (`seq_one`s concatenated)
    pub(super) fn list_items(&self, t: &Term) -> Option<Vec<Term>> {
        if self.app(t, "empty", 0).is_some() {
            return Some(Vec::new());
        }
        if let Some(x) = self.app(t, "seq_one", 1) {
            return Some(vec![x[0].clone()]);
        }
        let x = self.app(t, "seq_concat", 2)?;
        let mut a = self.list_items(&x[0])?;
        a.extend(self.list_items(&x[1])?);
        Some(a)
    }

    /// One reduction of the rest `qi` (None: the head waits for the machine).
    pub(super) fn reduce(&mut self, qi: usize, hyps: &[(Term, Seq)]) -> Result<Option<Red>, String> {
        let q = self.qs[qi].clone();
        let w = self.w.clone();
        // a procedure's definition: its body (`all o. runs(B, W, o) ->
        // runs(P(..), W, o)`, the definition unfolded)
        if let Node::App(fs, args) = q.node() {
            if self.name(&q) != Some("mkprog") {
                if let SymKind::Defined { params, body } = &self.env.syms[*fs as usize].kind {
                    let fname = self.env.syms[*fs as usize].name.clone();
                    let mut b = body.clone();
                    for (pa, x) in params.clone().iter().zip(args.iter()) {
                        b = b.subst_var(*pa, x, &self.env.binders_fn());
                    }
                    let b = self.canon(&b);
                    let j = self.new_q(b.clone());
                    // (all o. runs(b, w, o) -> runs(q, w, o): fix o, assume
                    // runs(b, w, o), the definition unfolded)
                    let o = self.var("o");
                    let h = self.mk("runs", vec![b, w.clone(), o.clone()]);
                    let hs = self.assume(&h)?;
                    let goal = self.mk("runs", vec![q.clone(), w.clone(), o.clone()]);
                    let u = self.evp(&RP::Defs(Box::new(RP::By(R::S(hs))), vec![fname]), &goal, &[])?;
                    let u = self.close(u, &[h], &[Self::var_id(&o)])?;
                    return Ok(Some(Red::Q(j, R::S(u))));
                }
            }
        }
        let body = self.app(&q, "mkprog", 1).ok_or_else(|| format!("the spec's rest is not a program: {}", self.print(&q)))?[0].clone();
        // a whole field's value: the bytes themselves
        if let Some((r, n, bytes)) = self.whole_field(&body) {
            let b = self.abstract_(&body, &r, 0);
            let e2 = self.mk("bits_of_int", vec![lit(n), bytes.clone()]);
            let (j, inst) = self.by(qi, "tr.qe_eq", &[("b", b), ("e", r), ("e2", e2)])?;
            return Ok(Some(Red::Q(j, mp(inst, vec![p(mpf(&format!("tr.bits_field0_{}", n), vec![t(&bytes)])), t(&w)]))));
        }
        // a projection of a constructed outcome
        if let Some((lemma, r, st, vv)) = self.redex(&body, 0) {
            let b = self.abstract_(&body, &r, 0);
            let st = self.lam(&st, &["x0", "x1"], &["x0"]).ok_or("redex")?;
            let vv = self.lam(&vv, &["x0", "x1"], &["x0"]).ok_or("redex")?;
            let (j, inst) = self.by(qi, lemma, &[("b", b), ("st", st), ("vv", vv)])?;
            return Ok(Some(Red::Q(j, mp(inst, vec![t(&w)]))));
        }
        // not a block: the result, a raise, or into the block form
        let Some(ex) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else {
            if let Some(x) = self.app(&body, "eq", 2) {
                if let Some(o) = self.app(&x[1], "ok", 2) {
                    if matches!(x[0].node(), Node::BVar(0)) && matches!(o[0].node(), Node::BVar(1)) && o[1].loose_depth(&self.env.binders_fn()) == 0 {
                        let val = self.value(&o[1]);
                        return Ok(Some(Red::Ret(val)));
                    }
                }
            }
            let (j, inst) = self.by(qi, "tr.qs_intro", &[("a", body.clone())])?;
            return Ok(Some(Red::Q(j, mp(inst, vec![t(&w)]))));
        };
        let (a, k) = (ex[0].clone(), ex[1].clone());
        let ctx = ["x0", "x1", "x8"];
        let kl = self.lam(&k, &ctx, &["x8", "x1"]).ok_or("a block's rest reads the world")?;
        // a let
        if let Some(x) = self.app(&a, "letin", 2) {
            if x[0].loose_depth(&self.env.binders_fn()) > 0 {
                return Err(format!("a let of the state: {}", self.lambda(3, &x[0])));
            }
            let e = self.value(&x[0]);
            let al = self.lam(&x[1], &["x0", "x1", "x8", "x"], &["x0", "x8", "x"]).ok_or("a let's body reads the outcome")?;
            let (j, inst) = self.by(qi, "tr.qs_let", &[("e", e), ("a", al), ("k", kl)])?;
            return Ok(Some(Red::Q(j, mp(inst, vec![t(&w)]))));
        }
        // a choice: a placeholder witness
        if let Some(x) = self.app(&a, "any_rel", 2) {
            let d = self.lam(&x[0], &["x0", "x1", "x8", "x"], &["x"]).ok_or("a choice whose domain reads the state")?;
            let ok = self.app(&d, "in", 2).map_or(false, |m| matches!(m[0].node(), Node::BVar(0)) && self.app(&m[1], "bits", 1).is_some());
            if !ok {
                return Err(format!("a choice from {}", self.lambda(1, &d)));
            }
            let zn = format!("Z{}", self.zs.len());
            let z = self.var(&zn);
            let zv = Self::var_id(&z);
            self.zs.push(zv);
            // (its witness: 0 -- no machine value is one)
            self.push_val(zv, lit(0));
            let al = self.lam(&x[1], &["x0", "x1", "x8", "x"], &["x0", "x8", "x"]).ok_or("a choice's body reads the outcome")?;
            let (j, inst) = self.by(qi, "tr.qs_any", &[("c", z), ("d", d), ("a", al), ("k", kl)])?;
            return Ok(Some(Red::Q(j, mp(inst, vec![simp0(), t(&w)]))));
        }
        // an operation
        if let Some(x) = self.app(&a, "bind_rel", 5) {
            if matches!(x[1].node(), Node::BVar(2)) && x[0].loose_depth(&self.env.binders_fn()) == 0 {
                let c5 = ["x0", "x1", "x8", "x9", "x10"];
                let al = self.lam(&x[2], &c5, &["x9", "x10", "x8"]).ok_or("an operation's continuation reads the world before it")?;
                let xl = self.lam(&x[3], &c5, &["x9", "x10", "x8"]).ok_or("an operation's handler reads the world before it")?;
                let dl = self.lam(&x[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("an operation's handler reads the world before it")?;
                let empty = self.mk("empty", vec![]);
                // a store: its definedness split here, the store itself at
                // the machine's
                if let Some(so) = self.store_op(&x[0])? {
                    if self.hyp_find(hyps, &so.cond).is_some() {
                        return Ok(None);
                    }
                    let ra = vec![("op", x[0].clone()), ("s2", self.vw.clone()), ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone()), ("e", empty)];
                    let (u, rinst) = self.by(qi, "tr.qs_raise", &ra)?;
                    let ubr = mp(rinst, vec![t(&w), so.ub]);
                    return Ok(Some(Red::Guard { cond: so.cond, ub: (u, ubr) }));
                }
                // a call: the machine's call makes it
                for (name, one) in [("gimple.call1", true), ("gimple.call", false)] {
                    if let Some(c) = self.app(&x[0], name, 2) {
                        let items = self.list_items(&c[1]).ok_or("a call's arguments: not a list literal")?;
                        return Ok(Some(Red::Call { g: c[0].clone(), args: items, list: c[1].clone(), one, a: al, xx: xl, dd: dl, k: kl }));
                    }
                }
                let (cond, r, okf, ubf) = self.op(&x[0])?;
                let r = self.value(&r);
                let args = |r2: (&'static str, Term)| vec![("op", x[0].clone()), r2, ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone())];
                let (j, inst) = self.by(qi, "tr.qs_op", &args(("r", r.clone())))?;
                let okr = mp(inst, vec![t(&w), okf]);
                let Some(cond) = cond else { return Ok(Some(Red::Q(j, okr))) };
                let mut ra = args(("s2", self.vw.clone()));
                ra.push(("e", empty));
                let (u, rinst) = self.by(qi, "tr.qs_raise", &ra)?;
                let ubr = mp(rinst, vec![t(&w), ubf.ok_or("an operation's raise")?]);
                return Ok(Some(Red::Split { cond, ok: (j, okr), ub: (u, ubr) }));
            }
        }
        // a block at the head
        if let Some(e) = self.app(&a, "ex", 1) {
            if let Some(y) = self.app(&e[0], "and", 2) {
                let c4 = ["x0", "x1", "x8", "x9"];
                let a1 = self.lam(&y[0], &c4, &["x0", "x9"]).ok_or("a block's head reads the outer outcome")?;
                let k1 = self.lam(&y[1], &c4, &["x9", "x8"]).ok_or("a block's rest reads the world")?;
                let (j, inst) = self.by(qi, "tr.qs_assoc", &[("a", a1), ("k1", k1), ("k2", kl)])?;
                return Ok(Some(Red::Q(j, mp(inst, vec![t(&w)]))));
            }
        }
        // the head done: x8 = v
        if let Some(x) = self.app(&a, "eq", 2) {
            if matches!(x[0].node(), Node::BVar(0)) {
                if let Some(v) = self.lam(&x[1], &ctx, &["x0"]) {
                    let (j, inst) = self.by(qi, "tr.qs_ret", &[("v", v), ("k", kl)])?;
                    return Ok(Some(Red::Q(j, mp(inst, vec![t(&w)]))));
                }
            }
        }
        // a disjunct whose guard holds
        if let Some(path) = self.pick(&a, hyps) {
            let first = path.into_iter().next().unwrap();
            let c2 = ["x0", "x8"];
            return Ok(Some(match first {
                Pick::L | Pick::R => {
                    let x = self.app(&a, "or", 2).unwrap().to_vec();
                    let l = self.lam(&x[0], &ctx, &c2).ok_or("a disjunct reads the outcome")?;
                    let r = self.lam(&x[1], &ctx, &c2).ok_or("a disjunct reads the outcome")?;
                    let lemma = if matches!(first, Pick::L) { "tr.qs_orl" } else { "tr.qs_orr" };
                    let (j, inst) = self.by(qi, lemma, &[("a", l), ("b", r), ("k", kl)])?;
                    Red::Q(j, mp(inst, vec![t(&w)]))
                }
                Pick::And(g, pf) => {
                    let x = self.app(&a, "and", 2).unwrap().to_vec();
                    let l = self.lam(&x[1], &ctx, &c2).ok_or("a guarded head reads the outcome")?;
                    let (j, inst) = self.by(qi, "tr.qs_and", &[("c", g), ("a", l), ("k", kl)])?;
                    Red::Q(j, mp(inst, vec![pf, t(&w)]))
                }
            }));
        }
        // (nothing else: an equation of a term with itself, of the world --
        // true)
        if let Some((r, s)) = self.refl_redex(&body, 0) {
            let b = self.abstract_(&body, &r, 0);
            let st = self.lam(&s, &["x0", "x1"], &["x0"]).ok_or("refl")?;
            let (j, inst) = self.by(qi, "tr.qe_refl", &[("b", b), ("st", st)])?;
            return Ok(Some(Red::Q(j, mp(inst, vec![t(&w)]))));
        }
        Ok(None)
    }
}
