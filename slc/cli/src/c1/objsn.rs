//! The frame's stack objects, several of any sizes (readable GIMPLE's
//! `alloc_objs(sizes)`), allocated where the machine makes no step
//! (proofs/translate_objsn.core, tr.alloc_lv): at the first point with a
//! home at or below them all, the frame within a page of the entry's rsp
//! (their bytes accessible); their bytes the machine's there. Then the
//! homes apart from them by their ranges (tr.hfree_objs), the frame
//! reaching them (tr.ofr_objs).

use super::rec::*;
use super::*;

/// The objects allocated: the callers' objects v0, the offsets' and sizes'
/// literal lists, the lowest home's offset, their count, `tr.vobjs`'s
/// proof (assumed), their ranges (offset, bytes), each one's elements
/// (`app(cs, k) = c`, `app(sizes, k) = pair(..)`)
#[derive(Clone)]
pub(super) struct ObjsN {
    pub v0: Term,
    pub cs: Term,
    pub sizes: Term,
    pub ch: u128,
    pub n: u128,
    pub hvo: Seq,
    pub ranges: Vec<(u128, u128)>,
    pub ats: Vec<[Seq; 2]>,
}

impl<'e> Gen<'e> {
    /// `app(l, k) = x` for a literal list l (the kernel's `list_at`)
    fn list_at_seq(&mut self, l: &Term, k: u128) -> Result<Seq, String> {
        let t = self.mk("app", vec![l.clone(), lit(k)]);
        let api = self.api.take().expect("the proving context");
        let r = Seq::list_at(self.env, &api.lg, &[], &t);
        self.api = Some(api);
        r.map_err(|e| format!("list_at {}: {}", self.print(&t), e.0))
    }

    /// `all k. k in omega -> int_lt(k, n) -> P(k)` (pl: P's body, k its
    /// bound variable 0), each instance by `inst` (tr.all_lt0,
    /// tr.all_lt_snoc)
    fn all_lt_r(n: u128, pl: &Term, inst: impl Fn(u128) -> RA) -> R {
        let mut prev = R::Inst("tr.all_lt0".into(), vec![("P", pl.clone())]);
        for i in 0..n {
            prev = mp(R::Inst("tr.all_lt_snoc".into(), vec![("n", lit(i)), ("m", lit(i + 1)), ("P", pl.clone())]), vec![simp0(), simp0(), p(prev), inst(i)]);
        }
        prev
    }

    /// a closed fact about the objects ks: simp from their elements
    fn objs_inst(ats: &[[Seq; 2]], ks: &[u128]) -> RA {
        let fs = ks.iter().flat_map(|&k| ats[k as usize].iter().map(|x| R::S(x.clone()))).collect();
        defs(RP::Simp(false, fs, vec![], false), &["tr.hrange"])
    }

    /// `tr.fobjs(cs, sizes, ch, n)`: each object's facts, the pairs'
    fn fobjs_pf(&mut self, cs: &Term, sizes: &Term, ch: u128, n: u128, ats: &[[Seq; 2]]) -> Result<Seq, String> {
        let pl = self.mk("tr.fok", vec![cs.clone(), sizes.clone(), lit(ch), Term::bvar(0)]);
        let oks = Self::all_lt_r(n, &pl, |k| Self::objs_inst(ats, &[k]));
        // (the pairs: for each k, each j below it)
        let omega = self.mk("omega", vec![]);
        let kn = self.fresh("KO");
        let kv = self.var(&kn);
        let jn = self.fresh("JO");
        let jv = self.var(&jn);
        let dj = self.mk("tr.fdisj", vec![cs.clone(), sizes.clone(), jv.clone(), kv.clone()]);
        let body = self.mk("imp", vec![self.mk("in", vec![jv.clone(), omega]), self.mk("imp", vec![self.mk("int_lt", vec![jv.clone(), kv.clone()]), dj])]);
        let inner = self.mk("all", vec![self.abs(&body, &[Self::var_id(&jv)])]);
        let inner = self.abs(&inner, &[Self::var_id(&kv)]);
        let pjs: Vec<Term> = (0..n).map(|k| self.mk("tr.fdisj", vec![cs.clone(), sizes.clone(), Term::bvar(0), lit(k)])).collect();
        let pairs = Self::all_lt_r(n, &inner, |k| p(Self::all_lt_r(k, &pjs[k as usize], |j| Self::objs_inst(ats, &[j, k]))));
        let goal = self.mk("tr.fobjs", vec![cs.clone(), sizes.clone(), lit(ch), lit(n)]);
        let mut ls = Vec::new();
        for l in [cs, sizes] {
            let e = self.mk("eq", vec![self.mk("seq_len", vec![l.clone()]), lit(n)]);
            ls.push(R::S(self.evp(&RP::Simp(false, vec![], vec![], false), &e, &[])?));
        }
        let om = self.mk("in", vec![lit(n), self.mk("omega", vec![])]);
        ls.push(R::S(self.evp(&RP::Simp(false, vec![], vec![], false), &om, &[])?));
        ls.extend([oks, pairs]);
        self.evp(&RP::Defs(Box::new(RP::Taut(ls)), vec!["tr.fobjs".into()]), &goal, &[])
    }

    /// The frame's objects allocated at st (`Red::Alloc`, the rest qi, the
    /// spec's op `alloc_objs(sizes)` and its continuation): tr.alloc_lv --
    /// the reduction for any memory B of their bytes (tr.allocn_run), the
    /// claim on from st's address with them (tr.vobjs assumed). None: not
    /// at this point (no home low enough yet), or one object of the old
    /// kind (tr.astore_r's).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn allocn_at(&mut self, st: &St, qi: usize, op: &Term, al: &Term, xl: &Term, dl: &Term, kl: &Term) -> Result<Option<Seq>, String> {
        // (one object too: allocated where the machine makes no step, before
        // a loop or call reaches it -- the old kind, at its first store, a
        // fallback: alloc_at)
        if self.objk.is_empty() || self.objs_n.is_some() || self.hvo.is_some() {
            return Ok(None);
        }
        let sizes = self.app(op, "gimple.alloc_objs", 1).ok_or("not alloc_objs")?[0].clone();
        let items = self.list_items(&sizes).ok_or("alloc_objs of a list that is not a literal")?;
        if items.len() != self.objk.len() {
            return Err(format!("{:x}: alloc_objs of {} objects, the location map's {}", st.a, items.len(), self.objk.len()));
        }
        let mut ranges = Vec::new();
        for (it, &c) in items.iter().zip(&self.objk) {
            let pr = self.app(it, "pair", 2).ok_or("an object's size: not a pair")?.to_vec();
            ranges.push((c, nat(&pr[0]).ok_or("an object's size: not a literal")?));
        }
        let minc = *self.objk.iter().min().unwrap();
        // (a home at or below them, within a page of the entry's rsp)
        let Some(ch) = st.hsm.iter().find(|(c, (n, _))| **c <= minc && *n > 0 && P64 - **c <= 4096).map(|x| *x.0) else { return Ok(None) };
        let a = st.a;
        let n = items.len() as u128;
        self.trace(|| format!("at {:x}: the {} stack objects allocated (the home at {:x} below them)", a, n, P64 - ch));
        // the offsets' list, the sizes', the addresses
        let mut cs = self.mk("seq_one", vec![lit(self.objk[0])]);
        for &c in &self.objk[1..] {
            cs = self.mk("seq_concat", vec![cs, self.mk("seq_one", vec![lit(c)])]);
        }
        let s0 = self.s.clone();
        let l = self.mk("tr.hal", vec![s0.clone(), cs.clone()]);
        let mut ats = Vec::new();
        for k in 0..n {
            ats.push([self.list_at_seq(&cs, k)?, self.list_at_seq(&sizes, k)?]);
        }
        let hf = self.fobjs_pf(&cs, &sizes, ch, n, &ats)?;
        let sal = self.sal16()?;
        let (w, v0) = (st.w.clone(), self.v.clone());
        // (a memory B of their bytes: typed, the world's elsewhere)
        let fresh_b = |g: &mut Self| -> Result<(Term, Term, Term, Seq, Seq), String> {
            let bn = g.fresh("BO");
            let b = g.var(&bn);
            let ht = g.parse(&format!("{} in fn_space(bits(64), bits(8))", bn))?;
            let hout_t = g.parse(&format!(
                "all z. z in bits(64) -> !tr.oin({}, {}, z) -> app({}, z) = app(app(app({}, \"vm\"), \"bytes\"), z)",
                g.print(&l),
                g.print(&sizes),
                bn,
                g.print(&w)
            ))?;
            let hts = g.assume(&ht)?;
            let hos = g.assume(&hout_t)?;
            Ok((b, ht, hout_t, hts, hos))
        };
        // the reduction, for every such B whose objects fit (alloc_objs's run)
        let (b1, ht1, ho1, hts1, hos1) = fresh_b(self)?;
        let fit_t = self.mk("gimple.objs_fit", vec![self.mk("app", vec![w.clone(), Term::bytes(b"vm")]), self.mk("app", vec![w.clone(), Term::bytes(b"objs")]), sizes.clone(), l.clone()]);
        let hfit = self.assume(&fit_t)?;
        let w2 = self.mk("tr.wobjs", vec![w.clone(), b1.clone(), l.clone(), sizes.clone()]);
        let hl = self.run(&mpf("tr.hal_typed", vec![t(&s0), t(&cs), simp0()]), &[])?;
        let okr = self.run(
            &mpf(
                "tr.allocn_run",
                vec![t(&w), t(&l), t(&sizes), t(&b1), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), taut(vec![R::S(hl.clone())]), taut(vec![R::S(hl.clone())]), s(&hfit), s(&hts1), s(&hos1)],
            ),
            &[],
        )?;
        let (j, inst) = self.by(qi, "tr.qs_opw", &[("op", op.clone()), ("r", l.clone()), ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone())])?;
        let qred = mp(inst, vec![t(&w), t(&w2), s(&st.hvu), s(&okr)]);
        let wredw = R::Inst("tr.wredw".into(), vec![("w", w.clone()), ("w2", w2.clone()), ("q", self.qs[qi].clone()), ("q2", self.qs[j].clone()), ("kw", self.kw3())]);
        let red = self.run(&mp(wredw, vec![s(&st.hvu), p(qred)]), &[])?;
        let red = self.close(red, &[ht1, ho1, fit_t], &[Self::var_id(&b1)])?;
        // the claim on from here, for every such B, with the objects
        let (b2, ht2, ho2, hts2, _hos2) = fresh_b(self)?;
        let w3 = self.mk("tr.wobjs", vec![w.clone(), b2.clone(), l.clone(), sizes.clone()]);
        let hw3 = self.run(&mpf("tr.world_allocn", vec![t(&w), t(&l), t(&sizes), t(&b2), taut(vec![R::S(st.hw.clone())]), s(&st.hvu), s(&hts2)]), &[])?;
        let w3u = self.mk("in", vec![w3.clone(), self.mk("univ", vec![lit(1)])]);
        let hv3 = self.evp(&RP::Taut(vec![R::S(hw3.clone())]), &w3u, &[])?;
        let v2 = self.mk("tr.objsv", vec![v0.clone(), l.clone(), sizes.clone()]);
        let hvo_t = self.mk("tr.vobjs", vec![s0.clone(), v2.clone(), v0.clone(), cs.clone(), sizes.clone(), lit(ch), lit(n)]);
        let hvo = self.assume(&hvo_t)?;
        let mut st2 = st.clone();
        // (each object's address, for simp(L): `app(L, k)` its normal
        // form -- the frame's address)
        let lf0 = self.lf.clone();
        for k in 0..n {
            let ak = self.mk("app", vec![l.clone(), lit(k)]);
            if let (_, Some(e)) = self.norm(&ak)? {
                st2.lfx.push(e.clone());
                self.lf.push(e);
            }
        }
        st2.w = w3;
        st2.hvu = hv3;
        st2.hw = hw3;
        st2.spec = Spec::Proc(j);
        self.v = v2;
        self.objs_n = Some(ObjsN { v0: v0.clone(), cs: cs.clone(), sizes: sizes.clone(), ch, n, hvo, ranges, ats });
        let rest = self.prove_kept(st2);
        self.lf = lf0;
        self.v = v0.clone();
        self.objs_n = None;
        let rest = self.close(rest?, &[ht2, ho2, hvo_t], &[Self::var_id(&b2)])?;
        // the rule
        let p0 = self.p(&st.spec);
        let p2 = self.wrap_of(&self.qs[j].clone());
        let inst = R::Inst("tr.alloc_lv".into(), vec![("bkp", self.bkp.clone()), ("bka", self.bka.clone())]);
        let args = vec![
            t(&s0),
            t(&v0),
            t(&self.base.clone()),
            t(&self.code.clone()),
            t(&lit(st.fr)),
            t(&lit(a)),
            t(&st.hst),
            t(&st.ds),
            t(&st.rs),
            t(&p0),
            t(&p2),
            t(&w),
            t(&cs),
            t(&sizes),
            t(&lit(ch)),
            t(&lit(n)),
            p(self.hva_r()),
            s(&sal),
            s(&hf),
            simp_l(),
            simp_l(),
            simp0(),
            s(&red),
            s(&rest),
        ];
        self.run(&mp(inst, args), &[]).map(Some)
    }

    /// `tr.hfree(s, c, nn, v)` with the objects allocated: apart from each
    /// by the ranges (tr.hfree_objs)
    pub(super) fn hfree_objs_pf(&self, c: u128, nn: u128) -> R {
        let o = self.objs_n.as_ref().expect("the objects allocated");
        let k = Term::bvar(0);
        let pl = self.mk(
            "or",
            vec![
                self.mk("int_le", vec![self.mk("int_add", vec![lit(c), lit(nn)]), self.mk("app", vec![o.cs.clone(), k.clone()])]),
                self.mk("int_le", vec![self.mk("int_add", vec![self.mk("app", vec![o.cs.clone(), k.clone()]), self.mk("fst", vec![self.mk("app", vec![o.sizes.clone(), k.clone()])])]), lit(c)]),
            ],
        );
        let dj = Self::all_lt_r(o.n, &pl, |kk| Self::objs_inst(&o.ats, &[kk]));
        let hr = defs(RP::Simp(false, vec![], vec![], false), &["tr.hrange"]);
        mpf("tr.hfree_objs", vec![t(&self.s), t(&o.v0), t(&o.cs), t(&o.sizes), t(&lit(o.ch)), t(&lit(o.n)), t(&lit(c)), t(&lit(nn)), s(&o.hvo), hr, p(dj)])
    }

    /// `tr.ofr(s, fr, v)` with the objects allocated (tr.ofr_objs)
    pub(super) fn ofr_objs_pf(&self, fr: &Term) -> R {
        let o = self.objs_n.as_ref().expect("the objects allocated");
        mpf("tr.ofr_objs", vec![t(&self.s), t(fr), t(&o.v0), t(&o.cs), t(&o.sizes), t(&lit(o.ch)), t(&lit(o.n)), s(&o.hvo), simp0()])
    }

    /// the object a frame offset is a byte of (with the objects allocated)
    pub(super) fn obj_byte(&self, c: u128) -> bool {
        self.objs_n.as_ref().is_some_and(|o| o.ranges.iter().any(|&(c0, n)| c0 <= c && c < c0 + n))
    }
}
