//! The engine's entry: a function's C1 theorems (`PREFIX.body`,
//! `.implements`, `.implements_abi`, and as a callee `.io`, `.typed`,
//! `.eff_*`), proven in the environment that holds its decode facts
//! (`FN.at_ADDR`), the program text (`text.code`, `FN.in_text`), its spec
//! and the rules.

use super::rec::*;
use super::*;
use sl_proof::api::Api;
use std::collections::BTreeSet;

/// the decode fact's statement: its address and instruction
fn decode_fact(env: &Env, name: &str, t: &Term) -> Option<(u128, Insn)> {
    let app = |t: &Term, n: &str| -> Option<Vec<Term>> {
        match t.node() {
            Node::App(s, a) if env.syms[*s as usize].name == n => Some(a.to_vec()),
            _ => None,
        }
    };
    let imp = |t: &Term| -> Option<(Term, Term)> {
        match t.node() {
            Node::App(s, a) if *s == env.builtins.imp => Some((a[0].clone(), a[1].clone())),
            _ => None,
        }
    };
    let t = app(t, "all")?[0].clone();
    let t = app(&t, "all")?[0].clone();
    let i1 = imp(&t)?;
    let i2 = imp(&i1.1)?;
    let i3 = imp(&i2.1)?;
    let ca = app(&i2.0, "abi.code_at")?;
    let rip = app(&i3.0, "eq")?;
    let ex = app(&app(&i3.1, "runs")?[0], "x86_64_linux.exec_body")?;
    let tg = app(&ex[1], "tag")?;
    Some((nat(&rip[1])?, Insn { name: name.to_string(), len: nat(&ex[0])?, row: nat(&tg[0])?, fields: tg[1].clone(), base: ca[1].clone(), code: ca[2].clone() }))
}

/// The C1 theorems of the function `fname` (its decode facts `fname.at_*`)
/// against the spec `spec_name` (a `_fun` wrapper), named `prefix.*`.
pub fn c1(env: &mut Env, fname: &str, spec_name: &str, prefix: &str, hints: &[String]) -> Result<Vec<(String, Seq)>, String> {
    let _rep = super::prof::Rep(fname.to_string());
    let _p = super::prof::g("c1");
    // the decode facts
    let mut insns: BTreeMap<u128, Insn> = BTreeMap::new();
    let pre = format!("{}.at_", fname);
    let found: Vec<(String, Term)> = env.theorems.iter().map(|(n, t)| (n.clone(), t.prop().clone())).chain(env.claims.iter().cloned()).filter(|(n, _)| n.starts_with(&pre)).collect();
    for (name, t) in found {
        let (a, insn) = decode_fact(env, &name, &t).ok_or_else(|| format!("{}: not a decode fact", name))?;
        insns.insert(a, insn);
    }
    let (&entry, first) = insns.iter().next().ok_or_else(|| format!("no decode facts `{}*`", pre))?;
    let (base_t, code_t) = (first.base.clone(), first.code.clone());
    if nat(&base_t) != Some(entry) {
        return Err(format!("the first decode fact is at {:x}, not the base", entry));
    }
    // the spec: fn_build(D, x0. mkprog(x1 x2. !ord_le(n, seq_len(x0)) || bind_rel(PROC, x1, KW, EXC, DIV)))
    // (n arguments), or fn_build(D, x0. mkprog(x1 x2. bind_rel(PROC, x1, KW, EXC, DIV))) (none)
    let ssym = *env.sym_by_name.get(spec_name).ok_or_else(|| format!("no spec `{}`", spec_name))?;
    let SymKind::Defined { body: sbody, params: sparams } = env.syms[ssym as usize].kind.clone() else { return Err(format!("`{}` is not a definition", spec_name)) };
    // (each callee's code: decoded)
    let mut targets: BTreeSet<u128> = BTreeSet::new();
    for (&a, i) in &insns {
        if i.row == 120 {
            let off = nat(&i.fields).ok_or_else(|| format!("{:x}: the call's displacement", a))?;
            let a2 = (a + i.len) % P64;
            targets.insert((a2 + if off >= 1 << 31 { off + (P64 - (1 << 32)) } else { off }) % P64);
        }
    }
    for &f in &targets {
        let suffix = format!(".at_{:x}", f);
        if !env.theorems.iter().any(|(n, _)| n.ends_with(&suffix)) && !env.claims.iter().any(|(n, _)| n.ends_with(&suffix)) {
            return Err(format!("no decode fact of the callee at {:x}", f));
        }
    }
    // (the hints: proven facts)
    let hint_seqs: Vec<Seq> = hints.iter().map(|h| sl_kernel::ext::facts::seq_of(env, h).ok_or_else(|| format!("no fact `{}` (a hint)", h))).collect::<Result<_, _>>()?;
    let mut g = Gen::new(env, insns, base_t, code_t, prefix, fname, hint_seqs)?;
    g.top(fname, spec_name, ssym, sbody, sparams, entry)
}

impl<'e> Gen<'e> {
    /// A generator over env: the decode facts (none for a refinement of
    /// two GIMPLE forms, gref.rs), the program's base and code, the
    /// theorems' prefix, the function's name, the hints
    pub(super) fn new(env: &'e mut Env, insns: BTreeMap<u128, Insn>, base: Term, code: Term, prefix: &str, fname: &str, hints: Vec<Seq>) -> Result<Gen<'e>, String> {
        let api = Api::new(env, Vec::new()).map_err(|e| e.0)?;
        let empty = Term::app(env.sym_by_name["empty"], vec![]);
        let no_bk = Term::app(env.sym_by_name["false"], vec![]);
        Ok(Gen {
            env,
            api: Some(api),
            names: Vec::new(),
            vals: Vec::new(),
            vexp: Default::default(),
            exp_memo: Default::default(),
            canon_memo: Default::default(),
            no_redex: Default::default(),
            no_refl: Default::default(),
            no_field: Default::default(),
            nf_memo: Default::default(),
            join_why: Default::default(),
            pdoms: None,
            block_fb: Vec::new(),
            val_of: Default::default(),
            zs: Vec::new(),
            qs: Vec::new(),
            insns,
            imuls: BTreeSet::new(),
            fields: BTreeSet::new(),
            facts_made: Vec::new(),
            rbytes: 4,
            scratch: BTreeSet::new(),
            base,
            code,
            prefix: prefix.to_string(),
            kw: Term::bvar(0),
            wrap: Term::bvar(0),
            fd: 0,
            fr: 0,
            w: empty.clone(),
            hvu: None,
            vw: empty.clone(),
            s: empty.clone(),
            v: empty.clone(),
            hw0: None,
            hvu0: None,
            hl: None,
            hcall: Vec::new(),
            htyp: Vec::new(),
            hio: Vec::new(),
            cinfo: Vec::new(),
            statics_t: Term::bvar(0),
            gs: Vec::new(),
            n: 0,
            loops: Vec::new(),
            nval: 0,
            visits: BTreeMap::new(),
            fname: fname.to_string(),
            lf: Vec::new(),
            hints,
            lf0: None,
            callees: Vec::new(),
            lbase: empty.clone(),
            lcode: empty,
            steps: 0,
            stmts: Vec::new(),
            stmt_fail: BTreeMap::new(),
            hus: Vec::new(),
            vmark0: 0,
            locmap: Vec::new(),
            loop_claims: Vec::new(),
            picked: Default::default(),
            spent_now: Default::default(),
            preds: None,
            ambient: Vec::new(),
            bkp: no_bk.clone(),
            bka: no_bk,
            lpg: None,
            cfg_meta: None,
            cfg_start: 0,
            cfg: None,
            gref: None,
            raw_lets: false,
            grefs: std::collections::HashMap::new(),
        })
    }
}

impl<'e> Gen<'e> {
    #[allow(clippy::too_many_arguments)]
    fn top(&mut self, fname: &str, spec_name: &str, ssym: u32, sbody: Term, sparams: Vec<VarId>, entry: u128) -> Result<Vec<(String, Seq)>, String> {
        let p = self.prefix.clone();
        // the locals' homes, if the location map has them
        let pname = spec_name.strip_suffix("_fun").unwrap_or(spec_name);
        // (the CFG's layer `M_cfg`: the location map of M's functions)
        let lname = match pname.split_once('.') {
            Some((m, f)) => format!("loc.{}.{}", m.strip_suffix("_cfg").unwrap_or(m), f),
            None => format!("loc.{pname}"),
        };
        if let Some(&ls) = self.env.sym_by_name.get(&lname) {
            if let SymKind::Defined { body, .. } = &self.env.syms[ls as usize].kind {
                let mut cur = body.clone();
                while let Some(x) = self.app(&cur, "pair", 2).map(|x| x.to_vec()) {
                    if let Some(e) = self.pairs(&x[0], 4) {
                        if let (Some(k), Some(key), Some(lo), Some(hi)) = (nat(&e[0]), nat(&e[1]), nat(&e[2]), nat(&e[3])) {
                            self.locmap.push((k as usize, key, entry + lo, entry + hi));
                        }
                    }
                    cur = x[1].clone();
                }
            }
        }
        // the readable CFG's guide (cfg.rs): each block's live locals, the
        // locals' widths
        let meta = |g: &Gen, nm: &str| -> Option<Vec<Term>> {
            let &sy = g.env.sym_by_name.get(&format!("{pname}_cfg_{nm}"))?;
            let SymKind::Defined { body, .. } = &g.env.syms[sy as usize].kind else { return None };
            g.list_items(body)
        };
        if let (Some(live), Some(ws)) = (meta(self, "live"), meta(self, "widths")) {
            let live: Option<Vec<(u128, u128)>> = live.iter().map(|x| self.app(x, "pair", 2).and_then(|p| Some((nat(&p[0])?, nat(&p[1])?)))).collect();
            let ws: Option<Vec<u64>> = ws.iter().map(|x| nat(x).map(|v| v as u64)).collect();
            if let (Some(live), Some(ws)) = (live, ws) {
                self.cfg_meta = Some((live, ws));
                self.cfg_start = self.cfg_body_start(entry);
            }
        }
        // the fixed variables: the program's statics, the callees, the
        // arguments, the view's objects, its memory, the entry's machine
        let statics = self.var("statics");
        let mut sbody = sbody;
        let mut gs = Vec::new();
        for (i, pa) in sparams.iter().enumerate() {
            let gv = self.var(&format!("G{}", i));
            sbody = sbody.subst_var(*pa, &gv, &self.env.binders_fn());
            gs.push(gv);
        }
        let spec_app = self.mk(spec_name, gs.clone());
        self.statics_t = statics.clone();
        self.gs = gs.clone();
        self.hcall = vec![None; gs.len()];
        self.htyp = vec![None; gs.len()];
        self.hio = vec![None; gs.len()];
        self.cinfo = vec![None; gs.len()];
        let args_t = self.var("args");
        let vv = self.var("v");
        let mem = self.var("mem");
        let s = self.var("s");
        self.s = s.clone();
        // (V: v; W: the entry's view)
        let vvar = self.var("V");
        self.push_val(Self::var_id(&vvar), vv.clone());
        self.v = vvar;
        let view = self.mk("abi.view", vec![s.clone(), vv.clone(), mem.clone()]);
        let w = self.var("W");
        self.push_val(Self::var_id(&w), view.clone());
        self.w = w.clone();
        self.vw = w.clone();
        let q_t = self.var("q");
        // the program text (every contract's code): FN.in_text's
        let lc = self.mk("text.code", vec![]);
        let in_text = self.env.theorems.iter().find(|(n, _)| n == &format!("{}.in_text", fname)).map(|(_, t)| t.prop().clone()).ok_or_else(|| format!("no program text with {} (slc steps --text)", fname))?;
        let lb = (|| {
            let t = self.app(&in_text, "all", 1)?[0].clone();
            let t = self.app(&t, "all", 1)?[0].clone();
            let Node::App(i, a) = t.node() else { return None };
            (*i == self.env.builtins.imp).then_some(())?;
            Some(self.app(&a[0], "abi.loaded", 4)?[1].clone())
        })()
        .ok_or("FN.in_text: not abi.loaded(..) -> ..")?;
        self.lbase = lb.clone();
        self.lcode = lc.clone();
        // the wrapper: PROC(x0); KW(x3, x4, x2); the wrapper's rest
        let parts = (|| -> Option<(u128, Term, Term, Term)> {
            let fb = self.app(&sbody, "fn_build", 2)?;
            let mp = self.app(&fb[1], "mkprog", 1)?;
            let (nargs, br) = match self.app(&mp[0], "or", 2) {
                Some(or) => {
                    let guard = self.app(&or[0], "not", 1)?;
                    let le = self.app(&guard[0], "ord_le", 2)?;
                    let n = nat(&le[0])?;
                    (1..=6).contains(&n).then_some(())?;
                    (n, self.app(&or[1], "bind_rel", 5)?.to_vec())
                }
                None => (0, self.app(&mp[0], "bind_rel", 5)?.to_vec()),
            };
            matches!(br[1].node(), Node::BVar(1)).then_some(())?;
            let proc = self.lam(&br[0], &["x0", "x1", "x2"], &["x0"])?;
            let kw = self.lam(&br[2], &["x0", "x1", "x2", "x3", "x4"], &["x3", "x4", "x2"])?;
            let bs = self.env.syms[self.env.sym_by_name["bind_rel"] as usize].binders.clone();
            let rest: Vec<Term> = br[1..].iter().zip(&bs[1..]).map(|(x, &k)| self.remap(x, k, &|i| (i < 2).then_some(i))).collect::<Option<_>>()?;
            let mut wa = vec![q_t.clone()];
            wa.extend(rest);
            let wrap = self.mk("mkprog", vec![self.mk("bind_rel", wa)]);
            Some((nargs, proc, kw, wrap))
        })();
        let (nargs, proc, kw, wrap) = parts.ok_or_else(|| format!("`{}`: not a procedure's spec", spec_name))?;
        let guarded = nargs > 0;
        self.kw = kw.clone();
        self.wrap = self.abs(&wrap, &[Self::var_id(&q_t)]);
        // (the result's width: the wrapper's gimple.result(N, ..))
        fn result_bits(g: &Gen, t: &Term) -> Option<u128> {
            if let Some(a) = g.app(t, "gimple.result", 2) {
                return nat(&a[0]);
            }
            match t.node() {
                Node::App(_, a) => a.iter().find_map(|x| result_bits(g, x)),
                _ => None,
            }
        }
        // (no `gimple.result`: a void function, no result bytes)
        self.rbytes = result_bits(self, &kw).unwrap_or(0) / 8;
        // the frame: `sub rsp, k` at the entry (or none); fd, the deepest byte
        // below the entry's rsp the function's stack accesses reach
        let k0 = (|| {
            let i = &self.insns[&entry];
            let x = (i.row == 60).then(|| self.pairs(&i.fields, 5)).flatten()?;
            let (tg, r) = self.tag(&x[2])?;
            (nat(&x[0])? == 8 && nat(&x[1])? == 5 && tg == 0 && nat(&r)? == 4).then_some(())?;
            nat(&x[4])
        })()
        .unwrap_or(0);
        fn rsp_disps(g: &Gen, t: &Term, out: &mut Vec<u128>) {
            if let Some(d) = g.rsp_mem(t).and_then(|d| nat(&d)) {
                out.push(d);
                return;
            }
            if let Node::App(_, a) = t.node() {
                for x in a.iter() {
                    rsp_disps(g, x, out);
                }
            }
        }
        let mut fd = k0;
        for i in self.insns.values() {
            let mut ds = Vec::new();
            rsp_disps(self, &i.fields, &mut ds);
            for d in ds {
                let c = (d + P64 - k0) % P64;
                if c >= P64 / 2 {
                    fd = fd.max(P64 - c);
                }
            }
        }
        if fd > 65536 {
            return Err(format!("a frame of {} bytes: beyond tr.FMAX", fd));
        }
        self.fd = fd;
        // the entry's facts (assumed; discharged at the end)
        let univ1 = |g: &Gen, x: &Term| g.mk("in", vec![x.clone(), g.mk("univ", vec![lit(1)])]);
        let h_a = self.mk("in", vec![args_t.clone(), self.mk("abi.ARGS", vec![])]);
        let h_vo = self.mk("in", vec![vv.clone(), self.mk("set_type", vec![self.mk("omega", vec![])])]);
        let h_mv = self.mk("in", vec![mem.clone(), self.mk("x86_64_linux.Vm", vec![])]);
        let h_m = self.mk("in", vec![s.clone(), self.mk("x86_64_linux.Machine", vec![])]);
        let h_g = self.mk("ord_le", vec![lit(nargs), self.mk("seq_len", vec![args_t.clone()])]);
        let h_l = self.mk("abi.loaded", vec![self.mk("app", vec![s.clone(), Term::bytes(b"vm")]), lb.clone(), lc.clone(), statics.clone()]);
        let h_vu = univ1(self, &view);
        let mut inner_h = vec![h_a.clone(), h_vo.clone(), h_mv.clone(), h_m.clone()];
        if guarded {
            inner_h.push(h_g.clone());
        }
        inner_h.push(h_l.clone());
        inner_h.push(h_vu.clone());
        let mut hseqs = Vec::new();
        for h in &inner_h {
            hseqs.push(self.assume(h)?);
        }
        // (in scope everywhere: a join's claim may rest on them)
        self.ambient = inner_h.iter().map(|h| self.expand(h)).collect();
        let (s_hvo, s_hmv, s_hm, s_hl, s_hvu) = (hseqs[1].clone(), hseqs[2].clone(), hseqs[3].clone(), self.assume(&h_l)?, self.assume(&h_vu)?);
        self.hl = Some(s_hl);
        // the literal facts: a map's keys, the scratch registers
        let lf0 = self.literal_facts()?;
        self.lf0 = Some(lf0);
        // the world: a world
        let wt = self.run(&R::Apply(Box::new(f("abi.world_typed")), vec![s_(&s_hm), s_(&s_hvo), s_(&s_hmv), s_(&s_hvu)]), &[])?;
        let hw_t = self.mk("and", vec![self.mk("in", vec![w.clone(), self.mk("abi.World", vec![])]), univ1(self, &w)]);
        let hw = self.evp(&RP::Taut(vec![R::S(wt), R::S(s_hvu.clone())]), &hw_t, &[])?;
        self.hw0 = Some(hw.clone());
        self.hvu0 = Some(s_hvu.clone());
        // the entry: the arguments in their registers (64 bits each)
        let q0raw = proc.instantiate_params(&[args_t.clone()], &self.env.binders_fn());
        let q0 = self.canon(&q0raw);
        let i0 = self.new_q(q0);
        let argregs = [7u128, 6, 2, 1, 8, 9];
        let mut st0 = St {
            a: entry,
            fr: 0,
            regs: Vec::new(),
            rs: self.mk("empty", vec![]),
            ds: lit(fd),
            w: w.clone(),
            hvu: s_hvu.clone(),
            hw,
            hsm: BTreeMap::new(),
            hst: self.mk("empty", vec![]),
            lp: None,
            spec: Spec::Proc(i0),
            hyps: Vec::new(),
            facts: Vec::new(),
            lfx: Vec::new(),
            bconds: Vec::new(),
            spent: Vec::new(),
            splits: Vec::new(),
            no_join: None,
            no_block: None,
            z: None,
        };
        let x0 = self.var("x0");
        let mut rs_lam = self.mk("empty", vec![]);
        for i in 0..nargs {
            let r = argregs[i as usize];
            let v = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![args_t.clone(), lit(i)])]);
            st0 = self.set_reg(&st0, entry, r, 8, v);
            let vx = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![x0.clone(), lit(i)])]);
            rs_lam = self.upd(&rs_lam, r, 8, &vx);
        }
        let rs_args = st0.rs.clone();
        // the proof
        self.vmark0 = self.env.vars.len();
        let pt = self.prove_pt(st0)?;
        // (the callees' premises, as their calls had them)
        let mut cprem = Vec::new();
        let mut cns = Vec::new();
        for (i, ci) in self.cinfo.iter().enumerate() {
            let (_, n, _, hs) = ci.clone().ok_or_else(|| format!("the spec's parameter G{} is not called", i))?;
            cprem.extend(hs);
            cns.push(n);
        }
        let mut out = Vec::new();
        for (n, sq) in std::mem::take(&mut self.facts_made) {
            out.push((n, sq));
        }
        let vs_inner = [Self::var_id(&args_t), Self::var_id(&vv), Self::var_id(&mem), Self::var_id(&s)];
        let body_in = self.close(pt, &inner_h, &vs_inner)?;
        let mut gvs = vec![Self::var_id(&statics)];
        gvs.extend(gs.iter().map(Self::var_id));
        let body = self.close(body_in.clone(), &cprem, &gvs)?;
        out.push((format!("{p}.body"), body));
        // the contract (`tr.implements_at`): the entry's rule, the body
        let b = self.base.clone();
        let c = self.code.clone();
        let fcode = format!("{}.in_text", fname);
        let vm = self.var("vm");
        let hsub_h = self.mk("abi.loaded", vec![vm.clone(), lb.clone(), lc.clone(), statics.clone()]);
        let hh = self.assume(&hsub_h)?;
        let l = self.run(&mpf(&fcode, vec![t(&vm), t(&statics), s_(&hh)]), &[])?;
        let le = self.ev(&R::Expand(Box::new(R::S(l)), vec!["abi.loaded".into()]), &[])?;
        let code_at = self.mk("abi.code_at", vec![vm.clone(), b.clone(), c.clone()]);
        let hs0 = self.evp(&RP::Taut(vec![R::S(le)]), &code_at, &[])?;
        let hsub = self.close(hs0, &[hsub_h], &[Self::var_id(&vm)])?;
        let ql = self.abs(&q0raw, &[Self::var_id(&args_t)]);
        let kwl = self.kw.clone();
        let m0 = if guarded {
            // (the arguments' registers at the entry: the map's entries one by one)
            let (a2, s2) = (self.var("args2"), self.var("s2"));
            let ha2 = self.mk("in", vec![a2.clone(), self.mk("abi.ARGS", vec![])]);
            let hs2 = self.mk("in", vec![s2.clone(), self.mk("x86_64_linux.Machine", vec![])]);
            let he2 = self.mk("abi.entry_ok", vec![s2.clone(), a2.clone()]);
            let hg2 = self.mk("ord_le", vec![lit(nargs), self.mk("seq_len", vec![a2.clone()])]);
            let (sa, ss, se, sg) = (self.assume(&ha2)?, self.assume(&hs2)?, self.assume(&he2)?, self.assume(&hg2)?);
            let ln = self.evp(&RP::Simp(false, vec![R::S(sa)], vec![], false), &self.mk("in", vec![self.mk("seq_len", vec![a2.clone()]), self.mk("omega", vec![])]), &[])?;
            let mut r = self.run(&mpf("tr.regs_empty", vec![t(&s2)]), &[])?;
            let mut prev = self.mk("empty", vec![]);
            for i in 0..nargs {
                let reg = argregs[i as usize];
                let lt = self.mk("int_lt", vec![lit(i), self.mk("seq_len", vec![a2.clone()])]);
                let lt_s = self.evp(&RP::Arith(vec![R::S(ln.clone()), R::Expand(Box::new(R::S(sg.clone())), vec!["ord_le".into()])]), &lt, &[])?;
                let ai = self.run(
                    &R::Apply(
                        Box::new(f("tr.arg_reg")),
                        vec![t(&s2), t(&a2), t(&lit(i)), t(&lit(reg)), s_(&ss), s_(&se), simp0(), s_(&lt_s), simpw(vec![f("tr.argregs")]), simp0()],
                    ),
                    &[],
                )?;
                let ai = self.ev(&R::S(ai), &[])?;
                let vx = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![a2.clone(), lit(i)])]);
                r = self.run(&R::Apply(Box::new(f("tr.regs_add")), vec![t(&s2), t(&prev), t(&lit(reg)), t(&lit(8)), t(&vx), s_(&r), simpw(vec![R::S(ai.clone())]), simpw(vec![R::S(ai)])]), &[])?;
                prev = self.upd(&prev, reg, 8, &vx);
            }
            let hregs = self.close(r, &[ha2, hs2, he2, hg2], &[Self::var_id(&a2), Self::var_id(&s2)])?;
            let rsl = self.abs(&rs_lam, &[Self::var_id(&x0)]);
            let inst = R::Inst(
                "tr.entry_n".into(),
                vec![("lb", lb.clone()), ("lc", lc.clone()), ("base", b.clone()), ("code", c.clone()), ("statics", statics.clone()), ("f", b.clone()), ("n", lit(nargs)), ("fd", lit(fd)), ("rs", rsl), ("q", ql), ("kw", kwl)],
            );
            self.run(&mp(inst, vec![simp0(), s_(&hsub), s_(&hregs), s_(&body_in)]), &[])?
        } else {
            let inst = R::Inst(
                "tr.entry0".into(),
                vec![("lb", lb.clone()), ("lc", lc.clone()), ("base", b.clone()), ("code", c.clone()), ("statics", statics.clone()), ("f", b.clone()), ("fd", lit(fd)), ("q", q0raw.clone()), ("kw", kwl)],
            );
            self.run(&mp(inst, vec![simp0(), s_(&hsub), s_(&body_in)]), &[])?
        };
        let _ = rs_args;
        // m: all args objs mem s o. .. -> tr.matches_t(spec, args, objs, mem, s, o), the spec unfolded
        let m_goal = self.parse(&format!(
            "all args objs mem s o. args in abi.ARGS -> objs in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> s in univ(1) -> \
             abi.loaded(app(s, \"vm\"), {lbp}, {lcp}, statics) -> app(s, \"rip\") = {bp} -> abi.entry_ok(s, args) -> tr.objs_ok(s, objs) -> abi.view_ok(s, objs, mem) -> tr.run_d(s, s, o) -> \
             tr.matches_t({sp}, args, objs, mem, s, o)",
            lbp = self.print(&lb),
            lcp = self.print(&lc),
            bp = self.print(&b),
            sp = self.print(&spec_app)
        ))?;
        let m = self.evp(&RP::Defs(Box::new(RP::By(R::S(m0))), vec![spec_name.to_string()]), &m_goal, &[])?;
        let imp_goal = self.mk("tr.implements_at", vec![b.clone(), spec_app.clone(), lb.clone(), lc.clone(), statics.clone()]);
        let imp_in = self.evp(&RP::Defs(Box::new(RP::By(R::S(m))), vec!["tr.implements_at".into()]), &imp_goal, &[])?;
        let imp = self.close(imp_in.clone(), &cprem, &gvs)?;
        out.push((format!("{p}.implements"), imp));
        // the ABI's contract, from the bridge's: given the spec diverges
        // only where it raises (C1 matches a divergence without its trace)
        let dr_t = self.mk("tr.div_raises", vec![spec_app.clone()]);
        let dr = self.assume(&dr_t)?;
        let abi_in = self.run(&R::Apply(Box::new(f("tr.implements_abi")), vec![s_(&dr), s_(&imp_in)]), &[])?;
        let mut aprem = cprem.clone();
        aprem.push(dr_t);
        let abi = self.close(abi_in, &aprem, &gvs)?;
        out.push((format!("{p}.implements_abi"), abi));
        if !self.block_fb.is_empty() {
            let at: Vec<String> = self.block_fb.iter().map(|a| format!("{:x}", a)).collect();
            eprintln!("{}: {} block(s) by the join claims, not as blocks (their ends not the spec's): {}", p, at.len(), at.join(", "));
        }
        // as a callee: tr.callee_io from the spec's structure
        let mut eff = super::eff::Eff::new(self.env, &p)?;
        match eff.callee_io(ssym, &cns) {
            Ok(()) => out.extend(std::mem::take(&mut eff.out)),
            Err(e) => eprintln!("{}: no tr.callee_io yet: {}", p, e),
        }
        Ok(out)
    }

    /// `L`: a map's keys (`tr.dom_upd`, `tr.dom_keep`), the scratch
    /// registers (`tr.scratch_reg`)
    fn literal_facts(&mut self) -> Result<Seq, String> {
        let mut fs = vec![R::F("tr.dom_upd".into()), R::F("tr.dom_keep".into())];
        let mut parts = Vec::new();
        for r in 0..16u128 {
            let g = self.mk("tr.scratch_reg", vec![lit(r)]);
            if let Ok(sc) = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![], vec![], false)), vec!["tr.scratch_reg".into()]), &g, &[]) {
                fs.push(R::S(sc));
                parts.push(g);
            }
        }
        let mut goal = self.parse("(all f k v. k in dom(fn_update(f, k, v))) && (all f k j v. k in dom(f) -> !(k = j) -> k in dom(fn_update(f, j, v)))")?;
        for g in parts {
            goal = self.mk("and", vec![goal, g]);
        }
        self.evp(&RP::Taut(fs), &goal, &[])
    }

    /// `tr.imul_by(c)`: the signed 32-bit product by c is the word product
    pub(super) fn imul_fact(&mut self, c: u128) -> Result<Seq, String> {
        let name = format!("{}.imul_{}", self.prefix, c);
        if let Some((_, s)) = self.facts_made.iter().find(|x| x.0 == name) {
            return Ok(s.clone());
        }
        let y = self.var("y");
        let hy_t = self.mk("in", vec![y.clone(), self.mk("bits", vec![lit(32)])]);
        let hy = self.assume(&hy_t)?;
        let ct = lit(c);
        let goal = self.parse(&format!("bits_add(32, int_mul(sint(32, {y}), sint(32, {c})), 0) = bits_mul(32, {y}, {c})", y = self.print(&y)))?;
        let goal1 = self.parse(&format!("bits_add(32, int_mul(sint(32, {y}), {c}), 0) = bits_mul(32, {y}, {c})", y = self.print(&y)))?;
        let defs3 = vec!["bits_add".to_string(), "bits_mul".into(), "sint".into()];
        let lt = self.mk("int_lt", vec![y.clone(), lit(2147483648)]);
        let hl = self.assume(&lt)?;
        let e1 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hy.clone()), R::S(hl)], vec![], false)), defs3.clone()), &goal1, &[])?;
        let c1 = self.close(e1, &[lt.clone()], &[])?;
        let nlt = self.mk("not", vec![lt]);
        let hl2 = self.assume(&nlt)?;
        let eg = self.parse(&format!("int_mod(int_mul(int_sub({y}, 4294967296), {c}), 4294967296) = int_mod(int_mul({y}, {c}), 4294967296)", y = self.print(&y)))?;
        let e = self.evp(&RP::Arith(vec![R::S(hy.clone())]), &eg, &[])?;
        let e2 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hy.clone()), R::S(hl2), R::S(e)], vec![], false)), defs3), &goal1, &[])?;
        let c2 = self.close(e2, &[nlt], &[])?;
        let e3 = self.evp(&RP::Taut(vec![R::S(c1), R::S(c2)]), &goal1, &[])?;
        let g0 = self.evp(&RP::Simp(false, vec![R::S(e3)], vec![], false), &goal, &[])?;
        let gall = self.close(g0, &[hy_t], &[Self::var_id(&y)])?;
        let stmt = self.mk("tr.imul_by", vec![ct]);
        let r = self.evp(&RP::Defs(Box::new(RP::By(R::S(gall))), vec!["tr.imul_by".into()]), &stmt, &[])?;
        self.facts_made.push((name, r.clone()));
        self.imuls.insert(c);
        Ok(r)
    }

    /// `tr.field16(pos, kb, kk)`: a 16-bit word's field pos.., kb bits of it,
    /// as the machine masks it
    pub(super) fn field_fact(&mut self, pos: u128, kb: u128, kk: u128) -> Result<Seq, String> {
        let name = format!("{}.field16_{}_{}_{}", self.prefix, pos, kb, kk);
        if let Some((_, s)) = self.facts_made.iter().find(|x| x.0 == name) {
            return Ok(s.clone());
        }
        let x = self.var("x");
        let xs = self.print(&x);
        let hx_t = self.mk("in", vec![x.clone(), self.mk("bits", vec![lit(16)])]);
        let hx = self.assume(&hx_t)?;
        let d = 1u128 << pos;
        let rb = 16 - pos;
        let dd = self.parse(&format!("int_div({xs}, {d}) in bits({rb})"))?;
        let d1 = self.evp(&RP::Arith(vec![R::S(hx.clone())]), &dd, &[])?;
        let dd16 = self.parse(&format!("int_div({xs}, {d}) in bits(16)"))?;
        let d2 = self.evp(&RP::Arith(vec![R::S(hx.clone())]), &dd16, &[])?;
        let x16 = format!("bits_of_int(16, {xs})");
        let goal = self.parse(&format!(
            "bits_and(32, bits_slice(bits_set_slice(64, {x16}, 15, 0, bits_shr(16, bits_slice({x16}, 15, 0), {pos})), 31, 0), {kk}) = bits_of_int({kb}, int_mod(int_div({xs}, int_pow(2, {pos})), int_pow(2, {kb})))"
        ))?;
        let g0 = self.evp(&RP::Defs(Box::new(RP::Simp(false, vec![R::S(hx), R::S(d1), R::S(d2)], vec![], false)), vec!["bits_shr".into(), "bits_of_int".into(), "pow2".into()]), &goal, &[])?;
        let gall = self.close(g0, &[hx_t], &[Self::var_id(&x)])?;
        let stmt = self.mk("tr.field16", vec![lit(pos), lit(kb), lit(kk)]);
        let r = self.evp(&RP::Defs(Box::new(RP::By(R::S(gall))), vec!["tr.field16".into()]), &stmt, &[])?;
        self.facts_made.push((name, r.clone()));
        self.fields.insert((pos, kb, kk));
        Ok(r)
    }
}

/// a proven fact as an argument
fn s_(x: &Seq) -> RA {
    RA::P(RP::By(R::S(x.clone())))
}
