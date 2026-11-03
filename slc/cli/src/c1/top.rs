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
pub fn c1(env: &mut Env, fname: &str, spec_name: &str, prefix: &str, stop: Option<(u128, bool)>, mode: u8, hints: &[String]) -> Result<Vec<(String, Seq)>, String> {
    let startup = mode > 0;
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
    if let Some((t, k)) = stop {
        // (the breakpoints zb. zb.rip = t; the relation zb pb wb. k && tr.at_t(zb, pb, wb)
        // -- the startup mode's tr.at_tm(false, zb, pb, wb))
        g.stop = stop;
        g.startup = startup;
        if mode == 2 {
            g.bmode = Some(g.var("B"));
        }
        g.bkp = g.mk("eq", vec![g.mk("app", vec![Term::bvar(0), Term::bytes(b"rip")]), lit(t)]);
        let kt = g.mk(if k { "true" } else { "false" }, vec![]);
        let at = if startup {
            g.mk("tr.at_tm", vec![g.bm(), Term::bvar(2), Term::bvar(1), Term::bvar(0)])
        } else {
            g.mk("tr.at_t", vec![Term::bvar(2), Term::bvar(1), Term::bvar(0)])
        };
        g.bka = g.mk("and", vec![kt, at]);
    } else if startup {
        // (the startup mode without a stop: no breakpoints, the runs
        // tr.run_d -- the contract tr.impl_d)
        if mode == 2 {
            return Err("`both` needs a stop".into());
        }
        g.startup = true;
    }
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
            nf_bits: false,
            nf_bits_memo: Default::default(),
            val_of: Default::default(),
            zs: Vec::new(),
            qs: Vec::new(),
            insns,
            imuls: BTreeSet::new(),
            fields: BTreeSet::new(),
            facts_made: Vec::new(),
            rbytes: 4,
            scratch: BTreeSet::new(),
            fk_ff: None,
            base,
            code,
            prefix: prefix.to_string(),
            kw: Term::bvar(0),
            wrap: Term::bvar(0),
            fd: 0,
            fr: 0,
            w: empty.clone(),
            hvu: None,
            hww: None,
            vw: empty.clone(),
            s: empty.clone(),
            v: empty.clone(),
            hw0: None,
            hvu0: None,
            hl: None,
            ent_m: None,
            ent_al: None,
            sargs: None,
            hcall: Vec::new(),
            htyp: Vec::new(),
            hio: Vec::new(),
            cinfo: Vec::new(),
            statics_t: Term::bvar(0),
            gs: Vec::new(),
            n: 0,
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
            hus: Vec::new(),
            vmark0: 0,
            locmap: Vec::new(),
            picked: Default::default(),
            spent_now: Default::default(),
            ambient: Vec::new(),
            bkp: no_bk.clone(),
            bka: no_bk,
            stop: None,
            startup: false,
            bmode: None,
            lpg: None,
            cfg_meta: None,
            cfg_start: 0,
            cfg_regs: Vec::new(),
            cfg: None,
            gref: None,
            raw_lets: false,
            params: Vec::new(),
            grefs: std::collections::HashMap::new(),
            gtyped: Vec::new(),
            hva: None,
            last_home: std::cell::Cell::new((0, 0)),
            reroot: None,
            objk: Vec::new(),
            hvo: None,
            objw: None,
            objs_n: None,
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
        // (the stack objects' keys, in their order)
        if let Some(&ls) = self.env.sym_by_name.get(&lname.replacen("loc.", "loc_objs.", 1)) {
            if let SymKind::Defined { body, .. } = &self.env.syms[ls as usize].kind {
                let mut cur = body.clone();
                while let Some(x) = self.app(&cur, "pair", 2).map(|x| x.to_vec()) {
                    self.objk.extend(nat(&x[0]));
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
        // (the locals in registers, a hand-written CFG's)
        if let Some(rg) = meta(self, "regs") {
            let rg: Option<Vec<(usize, u128)>> = rg.iter().map(|x| self.app(x, "pair", 2).and_then(|p| Some((nat(&p[0])? as usize, nat(&p[1])?)))).collect();
            self.cfg_regs = rg.ok_or("the CFG's registers: not a list of pairs of literals")?;
        }
        // (no guide: a function of a return alone, walked straight -- C1 is
        // against the readable CFG, its branches and loops only there)
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
        // (V: the claim's objects, the callers' v with the run's C bytes --
        // the main mode's, all but the canary; W: the entry's view)
        let vvar = self.var("V");
        let fs = self.mk("app", vec![s.clone(), Term::bytes(b"fs_base")]);
        // (the startup mode's: all bytes the C world's, tr.cbm(false, ..);
        // its world tr.vw(false, ..))
        let vobjs = if self.startup {
            self.mk("abi.wob", vec![vv.clone(), self.mk("tr.cbm", vec![self.bm(), fs])])
        } else {
            self.mk("abi.wob", vec![vv.clone(), self.mk("abi.cbytes0", vec![fs])])
        };
        self.push_val(Self::var_id(&vvar), vobjs);
        self.v = vvar;
        let view = if self.startup {
            self.mk("tr.vw", vec![self.bm(), s.clone(), vv.clone(), mem.clone()])
        } else {
            self.mk("abi.view", vec![s.clone(), vv.clone(), mem.clone()])
        };
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
        let parts = (|| -> Option<(u128, Term, Term, Term, Option<Term>)> {
            let fb = self.app(&sbody, "fn_build", 2)?;
            let mp = self.app(&fb[1], "mkprog", 1)?;
            let (nargs, br, bl) = match self.app(&mp[0], "or", 2) {
                Some(or) => {
                    let guard = self.app(&or[0], "not", 1)?;
                    let le = self.app(&guard[0], "ord_le", 2)?;
                    let n = nat(&le[0])?;
                    (n >= 1).then_some(())?;
                    // (beyond six arguments, B: x0 x1 x2. the guard's other side)
                    let bl = if n > 6 { Some(self.lam(&or[1], &["x0", "x1", "x2"], &["x0", "x1", "x2"])?) } else { None };
                    (n, self.app(&or[1], "bind_rel", 5)?.to_vec(), bl)
                }
                None => (0, self.app(&mp[0], "bind_rel", 5)?.to_vec(), None),
            };
            matches!(br[1].node(), Node::BVar(1)).then_some(())?;
            let proc = self.lam(&br[0], &["x0", "x1", "x2"], &["x0"])?;
            let kw = self.lam(&br[2], &["x0", "x1", "x2", "x3", "x4"], &["x3", "x4", "x2"])?;
            let bs = self.env.syms[self.env.sym_by_name["bind_rel"] as usize].binders.clone();
            let rest: Vec<Term> = br[1..].iter().zip(&bs[1..]).map(|(x, &k)| self.remap(x, k, &|i| (i < 2).then_some(i))).collect::<Option<_>>()?;
            let mut wa = vec![q_t.clone()];
            wa.extend(rest);
            let wrap = self.mk("mkprog", vec![self.mk("bind_rel", wa)]);
            Some((nargs, proc, kw, wrap, bl))
        })();
        // (more than the procedure's call -- the canary read before it, the
        // objects released after: a function of no arguments, its spec's
        // program P itself at the entry (tr.entry0p), the procedure's call
        // in it the walk's wrapper, Spec::Plain until there)
        let plain: Option<Term> = match &parts {
            Some(_) => None,
            None => (|| {
                let fb = self.app(&sbody, "fn_build", 2)?;
                let mp = self.app(&fb[1], "mkprog", 1)?;
                (self.app(&mp[0], "or", 2).is_none() && fb[1].loose_depth(&self.env.binders_fn()) == 0).then_some(())?;
                let &ps = self.env.sym_by_name.get(pname)?;
                self.reroot = Some(ps);
                Some(fb[1].clone())
            })(),
        };
        // (the same for a function of n <= 6 arguments: past the guard any
        // program B of them, `mkprog(x1 x2. !ord_le(n, seq_len(x0)) || B)`
        // (tr.entry_np) -- its program at args, and B as x0 x1 x2. B)
        let plain_g: Option<(u128, Term, Term)> = match (&parts, &plain) {
            (None, None) => (|| {
                let fb = self.app(&sbody, "fn_build", 2)?;
                let mp = self.app(&fb[1], "mkprog", 1)?;
                let or = self.app(&mp[0], "or", 2)?;
                let guard = self.app(&or[0], "not", 1)?;
                let le = self.app(&guard[0], "ord_le", 2)?;
                let n = nat(&le[0])?;
                (1..=6).contains(&n).then_some(())?;
                let prog = self.lam(&self.mk("mkprog", vec![or[1].clone()]), &["x0"], &["x0"])?;
                let bl = self.lam(&or[1], &["x0", "x1", "x2"], &["x0", "x1", "x2"])?;
                let &ps = self.env.sym_by_name.get(pname)?;
                self.reroot = Some(ps);
                Some((n, prog, bl))
            })(),
            _ => None,
        };
        let (nargs, proc, kw, wrap, bl) = match (parts, &plain, &plain_g) {
            (Some(x), _, _) => x,
            (None, Some(_), _) => (0, Term::bvar(0), Term::bvar(0), Term::bvar(0), None),
            (None, None, Some((n, _, _))) => (*n, Term::bvar(0), Term::bvar(0), Term::bvar(0), None),
            (None, None, None) => return Err(format!("`{}`: not a procedure's spec", spec_name)),
        };
        // (a plain spec at the entry: its program; with arguments, at args)
        let plain = plain.or_else(|| plain_g.as_ref().map(|(_, prog, _)| prog.instantiate_params(&[args_t.clone()], &self.env.binders_fn())));
        let guarded = nargs > 0;
        // (beyond six arguments: the rest on the stack, the list stk; the
        // spec's arguments seq_concat(args, stk))
        let nregs = nargs.min(6);
        let nstk = nargs.saturating_sub(6);
        let stk = self.var("stk");
        let cat = |g: &Gen, l: &Term| if nstk > 0 { g.mk("seq_concat", vec![l.clone(), stk.clone()]) } else { l.clone() };
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
        self.rbytes = result_bits(self, if plain.is_some() { &sbody } else { &kw }).unwrap_or(0) / 8;
        // the frame: the pushes at the entry, then `sub rsp, k` (or none);
        // fd, the deepest byte below the entry's rsp the function's stack
        // accesses reach
        let (mut pa, mut np) = (entry, 0u128);
        while let Some(i) = self.insns.get(&pa).filter(|i| i.row == 114) {
            np += 1;
            pa = (pa + i.len) % P64;
        }
        let k0 = 8 * np
            + (|| {
                let i = self.insns.get(&pa)?;
                let x = matches!(i.row, 59 | 60).then(|| self.pairs(&i.fields, 5)).flatten()?;
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
        // (gcc's frame pointer pushed past the entry -- after a test: its
        // word too)
        let pushes = self.insns.values().filter(|i| i.row == 114 && nat(&i.fields) == Some(5)).count() as u128;
        let mut fd = k0.max(8 * pushes);
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
        let h_g = self.mk("ord_le", vec![lit(nregs), self.mk("seq_len", vec![args_t.clone()])]);
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
        // (and the thread pointer a word: the canary's load, ld64(fs_base, 40))
        let fs_t = self.mk("in", vec![self.mk("app", vec![s.clone(), Term::bytes(b"fs_base")]), self.mk("bits", vec![lit(64)])]);
        let fsf = self.evp(&RP::Simp(false, vec![R::Expand(Box::new(R::S(s_hm.clone())), vec!["x86_64_linux.Machine".into()])], vec![], false), &fs_t, &[])?;
        let lf_t = self.mk("and", vec![lf0.concl().clone(), fs_t]);
        let lf0 = self.evp(&RP::Taut(vec![R::S(lf0), R::S(fsf)]), &lf_t, &[])?;
        self.lf0 = Some(lf0);
        // the world: a world
        // (the startup mode's: tr.vw_typed)
        let wt = if self.startup {
            self.run(&R::Apply(Box::new(f("tr.vw_typed")), vec![t(&self.bm()), t(&s), t(&vv), t(&mem), s_(&s_hm), s_(&s_hvo), s_(&s_hmv), s_(&s_hvu)]), &[])?
        } else {
            self.run(&R::Apply(Box::new(f("abi.world_typed")), vec![s_(&s_hm), s_(&s_hvo), s_(&s_hmv), s_(&s_hvu)]), &[])?
        };
        let hw_t = self.mk("and", vec![self.mk("in", vec![w.clone(), self.mk("abi.World", vec![])]), univ1(self, &w)]);
        let hw = self.evp(&RP::Taut(vec![R::S(wt), R::S(s_hvu.clone())]), &hw_t, &[])?;
        self.hw0 = Some(hw.clone());
        self.hvu0 = Some(s_hvu.clone());
        // the entry: the arguments in their registers (64 bits each)
        let q0raw = match &plain {
            Some(pp) => pp.clone(),
            None => proc.instantiate_params(&[cat(self, &args_t)], &self.env.binders_fn()),
        };
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
            spec: if plain.is_some() { Spec::Plain(i0) } else { Spec::Proc(i0) },
            hyps: Vec::new(),
            facts: Vec::new(),
            lfx: Vec::new(),
            bconds: Vec::new(),
            spent: Vec::new(),
            splits: Vec::new(),
            no_join: None,
            no_block: None,
            z: None,
            fk: None,
        };
        let x0 = self.var("x0");
        let mut rs_lam = self.mk("empty", vec![]);
        // (the callee-saved registers: their entry values, to be restored;
        // a scratch register the code pushes too -- crti's `push rax`)
        for r in self.entry_held() {
            let v = self.gpr(&s, r);
            st0 = self.set_reg(&st0, entry, r, 8, v.clone());
            rs_lam = self.upd(&rs_lam, r, 8, &v);
        }
        for i in 0..nregs {
            let r = argregs[i as usize];
            let v = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![cat(self, &args_t), lit(i)])]);
            st0 = self.set_reg(&st0, entry, r, 8, v);
            let vx = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![cat(self, &x0), lit(i)])]);
            rs_lam = self.upd(&rs_lam, r, 8, &vx);
        }
        let rs_args = st0.rs.clone();
        // the proof (the entry's condition: assumed if an aligned call or a
        // system call needs the ABI's alignment)
        self.ent_m = Some((s_hm.clone(), args_t.clone()));
        self.ent_al = None;
        // (stack arguments: stk typed, long enough; the entry's condition
        // the ABI's with the arguments on the stack, assumed; each
        // argument's facts for its load)
        let lty = self.mk("list_type", vec![self.mk("bits", vec![lit(64)])]);
        let hstk_t = self.mk("in", vec![stk.clone(), lty.clone()]);
        let lstk = self.mk("seq_len", vec![stk.clone()]);
        let hle_t = self.mk("int_le", vec![lit(nargs), self.mk("int_add", vec![lit(6), lstk.clone()])]);
        // (the startup mode's entry with stack arguments: its E, any alignment)
        let mut stk_et: Option<Term> = None;
        if nstk > 0 && self.startup && self.stop.is_none() {
            return Err("stack arguments in the startup mode never stopping: not supported".into());
        }
        if nstk > 0 {
            let (hstk, hle) = (self.assume(&hstk_t)?, self.assume(&hle_t)?);
            let largs = self.mk("seq_len", vec![args_t.clone()]);
            // (the startup mode's entry: tr.eok(false, true, ..), any
            // alignment -- GCC calls a static leaf misaligned)
            let eo_t = if self.startup {
                self.mk("tr.eok", vec![self.bm(), self.mk("true", vec![]), s.clone(), args_t.clone()])
            } else {
                self.mk("abi.entry_ok", vec![s.clone(), args_t.clone()])
            };
            let sa_t = self.mk("abi.stack_args", vec![s.clone(), stk.clone()]);
            let h6_t = self.mk("eq", vec![largs.clone(), lit(6)]);
            let so_t = self.mk("tr.sargs_off", vec![s.clone(), vv.clone(), lstk.clone()]);
            let e_t = self.mk("and", vec![self.mk("and", vec![self.mk("and", vec![eo_t.clone(), sa_t.clone()]), h6_t.clone()]), so_t.clone()]);
            let he = self.assume(&e_t)?;
            let [eo, hsa, h6, hso] = [&eo_t, &sa_t, &h6_t, &so_t].map(|g| self.evp(&RP::Taut(vec![R::S(he.clone())]), g, &[]));
            let (eo, hsa, h6, hso) = (eo?, hsa?, h6?, hso?);
            if self.startup {
                stk_et = Some(e_t);
            } else {
                let st = self.run(&R::Apply(Box::new(f("abi.entry_stack")), vec![s_(&s_hm), s_(&eo)]), &[])?;
                let goal = self.mk("eq", vec![self.mk("int_mod", vec![self.mk("bits_add", vec![lit(64), self.gpr(&s, 4), lit(8)]), lit(16)]), lit(0)]);
                let sal = self.evp(&RP::Taut(vec![R::S(st)]), &goal, &[])?;
                self.ent_al = Some((e_t, sal));
            }
            let hal = self.evp(&RP::Simp(false, vec![R::S(hseqs[0].clone())], vec![], false), &self.mk("in", vec![args_t.clone(), lty.clone()]), &[])?;
            let ln = self.evp(&RP::Simp(false, vec![R::S(hstk.clone())], vec![], false), &self.mk("in", vec![lstk.clone(), self.mk("omega", vec![])]), &[])?;
            let mut sargs = Vec::new();
            for j in 0..nstk {
                let i = 6 + j;
                let xj = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![cat(self, &args_t), lit(i)])]);
                let lt = self.evp(&RP::Arith(vec![R::S(hle.clone()), R::S(ln.clone())]), &self.mk("int_lt", vec![lit(j), lstk.clone()]), &[])?;
                let le6 = self.evp(&RP::Arith(vec![R::S(h6.clone())]), &self.mk("int_le", vec![largs.clone(), lit(i)]), &[])?;
                let ut = self.evp(&RP::Arith(vec![R::S(h6.clone()), R::S(hle.clone())]), &self.mk("int_lt", vec![lit(i), self.mk("int_add", vec![largs.clone(), lstk.clone()])]), &[])?;
                let ca = self.run(&mpf("tr.concat_at_r", vec![t(&args_t), t(&stk), t(&lit(i)), s_(&hal), s_(&hstk), simp0(), s_(&le6), s_(&ut)]), &[])?;
                let xs = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![stk.clone(), lit(j)])]);
                let hx = self.evp(&RP::Simp(false, vec![R::S(ca), R::S(h6.clone())], vec![], false), &self.mk("eq", vec![xj.clone(), xs]), &[])?;
                sargs.push((xj, lt, hx));
            }
            self.sargs = Some(SArgs { stk: stk.clone(), hsa, hso, hstk, args: sargs });
        } else {
            self.sargs = None;
        }
        self.vmark0 = self.env.var_bound() as usize;
        // (the callers' objects at or above sp, tr.vabove: the homes apart from them)
        let vab_t = self.mk("tr.vabove", vec![s.clone(), self.v.clone()]);
        self.hva = Some(self.assume(&vab_t)?);
        let pt = self.prove_pt(st0)?;
        let (aligned, e_t) = match self.ent_al.take() {
            Some(_) if stk_et.is_some() => return Err("stack arguments in the startup mode, the body needing the ABI's alignment: not supported".into()),
            None if stk_et.is_some() => (false, stk_et.clone().unwrap()),
            Some((et, _)) => (true, et),
            None if self.startup => (false, self.mk("tr.eok", vec![self.bm(), self.mk("true", vec![]), s.clone(), args_t.clone()])),
            None => (false, self.mk("tr.entry_ok_u", vec![s.clone(), args_t.clone()])),
        };
        self.ent_m = None;
        let _ = self.assume(&e_t)?;
        inner_h.push(e_t.clone());
        // (the callers' objects at or above sp: assumed for the walk)
        inner_h.push(vab_t);
        // (E of the entry, its arguments and the callers' stack objects)
        let e_lam = self.abs(&e_t, &[Self::var_id(&s), Self::var_id(&args_t), Self::var_id(&vv)]);
        let h_e = if nstk > 0 && self.startup {
            super::rec::p(R::Inst("tr.eok_e_s".into(), vec![("b", self.bm()), ("u", self.mk("true", vec![])), ("stk", stk.clone())]))
        } else if nstk > 0 {
            super::rec::p(R::Inst("tr.entry_e_s".into(), vec![("stk", stk.clone())]))
        } else if self.startup {
            // (E -> tr.eok(false, true, ..): the startup mode's entry, any alignment's)
            super::rec::p(R::Inst(if aligned { "tr.eok_e_of" } else { "tr.eok_e_id" }.into(), vec![("b", self.bm())]))
        } else {
            super::rec::p(f(if aligned { "tr.entry_e_of" } else { "tr.entry_e_id" }))
        };
        let sargs = self.sargs.take();
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
        // (either mode: the contracts for every b)
        if let Some(bv) = &self.bmode {
            gvs.push(Self::var_id(bv));
        }
        gvs.extend(gs.iter().map(Self::var_id));
        // (with stack arguments: for any stk long enough)
        let body_s = if sargs.is_some() { self.close(body_in.clone(), &[hstk_t.clone(), hle_t.clone()], &[Self::var_id(&stk)])? } else { body_in.clone() };
        let body = self.close(body_s, &cprem, &gvs)?;
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
            let he2 = if self.startup {
                self.mk("tr.eok", vec![self.bm(), self.mk("true", vec![]), s2.clone(), a2.clone()])
            } else {
                self.mk("tr.entry_ok_u", vec![s2.clone(), a2.clone()])
            };
            let hg2 = self.mk("ord_le", vec![lit(nregs), self.mk("seq_len", vec![a2.clone()])]);
            let (sa, ss, se, sg) = (self.assume(&ha2)?, self.assume(&hs2)?, self.assume(&he2)?, self.assume(&hg2)?);
            let ln = self.evp(&RP::Simp(false, vec![R::S(sa.clone())], vec![], false), &self.mk("in", vec![self.mk("seq_len", vec![a2.clone()]), self.mk("omega", vec![])]), &[])?;
            // (with stack arguments, a2's elements in seq_concat(a2, stk))
            let hal = match &sargs {
                Some(_) => Some(self.evp(&RP::Simp(false, vec![R::S(sa)], vec![], false), &self.mk("in", vec![a2.clone(), lty.clone()]), &[])?),
                None => None,
            };
            let (mut r, mut prev) = self.cs_entry_regs(&s2, &ss)?;
            for i in 0..nregs {
                let reg = argregs[i as usize];
                let lt = self.mk("int_lt", vec![lit(i), self.mk("seq_len", vec![a2.clone()])]);
                let lt_s = self.evp(&RP::Arith(vec![R::S(ln.clone()), R::Expand(Box::new(R::S(sg.clone())), vec!["ord_le".into()])]), &lt, &[])?;
                // (the startup mode's entry: tr.arg_reg_m)
                let mut aargs = vec![t(&s2), t(&a2), t(&lit(i)), t(&lit(reg)), s_(&ss), s_(&se), simp0(), s_(&lt_s), simpw(vec![f("tr.argregs")]), simp0()];
                if self.startup {
                    aargs.splice(0..0, [t(&self.bm()), t(&self.mk("true", vec![]))]);
                }
                let ai = self.run(&R::Apply(Box::new(f(if self.startup { "tr.arg_reg_m" } else { "tr.arg_reg" })), aargs), &[])?;
                let ai = self.ev(&R::S(ai), &[])?;
                let vx = self.mk("bits_of_int", vec![lit(64), self.mk("app", vec![cat(self, &a2), lit(i)])]);
                let mut ws = vec![R::S(ai)];
                if let (Some(sq), Some(hal)) = (&sargs, &hal) {
                    let cl = self.run(&mpf("tr.concat_at_l", vec![t(&a2), t(&stk), t(&lit(i)), s_(hal), s_(&sq.hstk), simp0(), s_(&lt_s)]), &[])?;
                    ws.push(R::S(cl));
                }
                r = self.run(&R::Apply(Box::new(f("tr.regs_add")), vec![t(&s2), t(&prev), t(&lit(reg)), t(&lit(8)), t(&vx), s_(&r), simpw(ws.clone()), simpw(ws)]), &[])?;
                prev = self.upd(&prev, reg, 8, &vx);
            }
            let hregs = self.close(r, &[ha2, hs2, he2, hg2], &[Self::var_id(&a2), Self::var_id(&s2)])?;
            let rsl = self.abs(&rs_lam, &[Self::var_id(&x0), Self::var_id(&s)]);
            if let Some(sq) = &sargs {
                // (the spec's procedure on x0 itself, q; on x0 with stk, q2)
                let qx = proc.instantiate_params(&[x0.clone()], &self.env.binders_fn());
                let qx = self.abs(&qx, &[Self::var_id(&x0)]);
                // (the startup mode's, stopping at t: tr.entry_nskm, b false)
                if let (true, Some((tt, k))) = (self.startup, self.stop) {
                    let inst = R::Inst(
                        "tr.entry_nskm".into(),
                        vec![
                            ("b", self.bm()),
                            ("lb", lb.clone()),
                            ("lc", lc.clone()),
                            ("base", b.clone()),
                            ("code", c.clone()),
                            ("statics", statics.clone()),
                            ("f", b.clone()),
                            ("n", lit(nargs)),
                            ("fd", lit(fd)),
                            ("t", lit(tt)),
                            ("k", self.mk(if k { "true" } else { "false" }, vec![])),
                            ("rs", rsl),
                            ("q", qx),
                            ("q2", ql),
                            ("kw", kwl),
                            ("E", e_lam.clone()),
                            ("stk", stk.clone()),
                        ],
                    );
                    let hle = self.assume(&hle_t)?;
                    self.run(&mp(inst, vec![simp0(), s_(&hsub), h_e, s_(&hregs), s_(&body_in), simp0(), simp0(), simp0(), s_(&sq.hstk), simp0(), s_(&hle)]), &[])?
                } else {
                if self.startup {
                    return Err("stack arguments in the startup mode without a stop: not yet".into());
                }
                let inst = R::Inst(
                    "tr.entry_ns".into(),
                    vec![
                        ("lb", lb.clone()),
                        ("lc", lc.clone()),
                        ("base", b.clone()),
                        ("code", c.clone()),
                        ("statics", statics.clone()),
                        ("f", b.clone()),
                        ("n", lit(nargs)),
                        ("fd", lit(fd)),
                        ("rs", rsl),
                        ("q", qx),
                        ("q2", ql),
                        ("kw", kwl),
                        ("E", e_lam.clone()),
                        ("stk", stk.clone()),
                    ],
                );
                let hle = self.assume(&hle_t)?;
                self.run(&mp(inst, vec![simp0(), s_(&hsub), h_e, s_(&hregs), s_(&body_in), simp0(), simp0(), s_(&sq.hstk), simp0(), s_(&hle)]), &[])?
                }
            } else if let (Some((_, _, bl3)), Some((tt, k))) = (&plain_g, self.stop) {
                // (stopping at t, past the guard any program P of the
                // arguments: tr.entry_nkpm, tr.entry_gkpm -- the mode b)
                let kt = self.mk(if k { "true" } else { "false" }, vec![]);
                let bt = self.mk(if self.startup { "false" } else { "true" }, vec![]);
                let nk_binds = vec![
                    ("b", bt.clone()),
                    ("lb", lb.clone()),
                    ("lc", lc.clone()),
                    ("base", b.clone()),
                    ("code", c.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("fd", lit(fd)),
                    ("rs", rsl),
                    ("P", bl3.clone()),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                ];
                let hpro = self.run(&mp(R::Inst("tr.entry_nkpm".into(), nk_binds), vec![simp0(), s_(&hsub), h_e.clone(), s_(&hregs), s_(&body_in), simp0()]), &[])?;
                let run_l = self.mk("tr.run_s", vec![Term::bvar(1), lit(tt), Term::bvar(1), Term::bvar(0)]);
                let match_l = self.match_k(&kt);
                let gk_binds = vec![
                    ("b", bt),
                    ("base", lb.clone()),
                    ("code", lc.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("P", bl3.clone()),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                    ("RUN", run_l),
                    ("MATCH", match_l),
                ];
                let (fin, ub) = self.fin_ub(tt, &b, &kt);
                self.run(&mp(R::Inst("tr.entry_gkpm".into(), gk_binds), vec![super::rec::p(fin), ub, h_e, s_(&hpro)]), &[])?
            } else if let Some((_, _, bl3)) = &plain_g {
                // (past the guard any program of the arguments)
                if self.startup {
                    return Err("a spec past its guard any program, in the startup mode without a stop: not yet".into());
                }
                let inst = R::Inst(
                    "tr.entry_np".into(),
                    vec![
                        ("lb", lb.clone()),
                        ("lc", lc.clone()),
                        ("base", b.clone()),
                        ("code", c.clone()),
                        ("statics", statics.clone()),
                        ("f", b.clone()),
                        ("n", lit(nargs)),
                        ("fd", lit(fd)),
                        ("rs", rsl),
                        ("B", bl3.clone()),
                        ("E", e_lam.clone()),
                    ],
                );
                self.run(&mp(inst, vec![simp0(), s_(&hsub), h_e, s_(&hregs), s_(&body_in)]), &[])?
            } else if let Some((tt, k)) = self.stop {
                // (stopping at t: the claim at the entry with its breakpoints,
                // tr.entry_nk; the contract with the stop, tr.entry_gk by
                // tr.fin_k, tr.ub_k)
                let kt = self.mk(if k { "true" } else { "false" }, vec![]);
                // (the startup mode's: tr.entry_nkm, tr.entry_gkm, tr.fin_km, tr.ub_km with b false)
                let sm = self.startup;
                let mut nk_binds = vec![
                    ("lb", lb.clone()),
                    ("lc", lc.clone()),
                    ("base", b.clone()),
                    ("code", c.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("fd", lit(fd)),
                    ("rs", rsl),
                    ("q", ql.clone()),
                    ("kw", kwl.clone()),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                ];
                if sm {
                    nk_binds.insert(0, ("b", self.bm()));
                }
                let inst = R::Inst(if sm { "tr.entry_nkm" } else { "tr.entry_nk" }.into(), nk_binds);
                let hpro = self.run(&mp(inst, vec![simp0(), s_(&hsub), h_e.clone(), s_(&hregs), s_(&body_in), simp0()]), &[])?;
                let run_l = self.mk("tr.run_s", vec![Term::bvar(1), lit(tt), Term::bvar(1), Term::bvar(0)]);
                let match_l = self.match_k(&kt);
                let mut gk_binds = vec![
                    ("base", lb.clone()),
                    ("code", lc.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("q", ql),
                    ("kw", kwl),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                    ("RUN", run_l),
                    ("MATCH", match_l),
                ];
                if sm {
                    gk_binds.insert(0, ("b", self.bm()));
                }
                let gk = R::Inst(if sm { "tr.entry_gkm" } else { "tr.entry_gk" }.into(), gk_binds);
                let (fin, ub) = self.fin_ub(tt, &b, &kt);
                self.run(&mp(gk, vec![super::rec::p(fin), ub, h_e, s_(&hpro)]), &[])?
            } else if self.startup {
                // (the startup mode without a stop: tr.entry_nkm, tr.entry_gkm
                // with no breakpoints, the runs tr.run_d -- tr.fin_dm, tr.ub_km)
                let nk_binds = vec![
                    ("b", self.bm()),
                    ("lb", lb.clone()),
                    ("lc", lc.clone()),
                    ("base", b.clone()),
                    ("code", c.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("fd", lit(fd)),
                    ("rs", rsl),
                    ("q", ql.clone()),
                    ("kw", kwl.clone()),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                ];
                let hpro = self.run(&mp(R::Inst("tr.entry_nkm".into(), nk_binds), vec![simp0(), s_(&hsub), h_e.clone(), s_(&hregs), s_(&body_in), simp0()]), &[])?;
                let run_l = self.mk("tr.run_d", vec![Term::bvar(1), Term::bvar(1), Term::bvar(0)]);
                let kf = self.mk("false", vec![]);
                let match_l = self.match_k(&kf);
                let gk_binds = vec![
                    ("b", self.bm()),
                    ("base", lb.clone()),
                    ("code", lc.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("q", ql),
                    ("kw", kwl),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                    ("RUN", run_l),
                    ("MATCH", match_l),
                ];
                let (fin, ub) = self.fin_ub_d(&b);
                self.run(&mp(R::Inst("tr.entry_gkm".into(), gk_binds), vec![super::rec::p(fin), ub, h_e, s_(&hpro)]), &[])?
            } else {
            let inst = R::Inst(
                "tr.entry_n".into(),
                vec![
                    ("lb", lb.clone()),
                    ("lc", lc.clone()),
                    ("base", b.clone()),
                    ("code", c.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("n", lit(nargs)),
                    ("fd", lit(fd)),
                    ("rs", rsl),
                    ("q", ql),
                    ("kw", kwl),
                    ("E", e_lam.clone()),
                ],
            );
            self.run(&mp(inst, vec![simp0(), s_(&hsub), h_e, s_(&hregs), s_(&body_in)]), &[])?
            }
        } else {
            // (the callee-saved registers' entries)
            let s2 = self.var("s2");
            let hs2 = self.mk("in", vec![s2.clone(), self.mk("x86_64_linux.Machine", vec![])]);
            let ss = self.assume(&hs2)?;
            let (r, _) = self.cs_entry_regs(&s2, &ss)?;
            let hregs = self.close(r, &[hs2], &[Self::var_id(&s2)])?;
            let rsl = self.abs(&rs_lam, &[Self::var_id(&s)]);
            // (stopping at t: tr.entry0k, by tr.fin_k)
            if let (Some((tt, k)), None) = (self.stop, &plain) {
                let kt = self.mk(if k { "true" } else { "false" }, vec![]);
                let run_l = self.mk("tr.run_s", vec![Term::bvar(1), lit(tt), Term::bvar(1), Term::bvar(0)]);
                let match_l = self.match_k(&kt);
                let sm = self.startup;
                let mut binds = vec![
                    ("lb", lb.clone()),
                    ("lc", lc.clone()),
                    ("base", b.clone()),
                    ("code", c.clone()),
                    ("statics", statics.clone()),
                    ("f", b.clone()),
                    ("fd", lit(fd)),
                    ("rs", rsl),
                    ("q", q0raw.clone()),
                    ("kw", kwl),
                    ("E", e_lam.clone()),
                    ("B", self.bkp.clone()),
                    ("A", self.bka.clone()),
                    ("RUN", run_l),
                    ("MATCH", match_l),
                ];
                if sm {
                    binds.insert(0, ("b", self.bm()));
                }
                let inst = R::Inst(if sm { "tr.entry0km" } else { "tr.entry0k" }.into(), binds);
                let (fin, _) = self.fin_ub(tt, &b, &kt);
                self.run(&mp(inst, vec![super::rec::p(fin), simp0(), simp0(), s_(&hsub), h_e, s_(&hregs), s_(&body_in)]), &[])?
            } else {
            if self.startup {
                return Err("a function of no arguments in the startup mode without a stop: not yet".into());
            }
            let inst = match &plain {
                Some(pp) => R::Inst(
                    "tr.entry0p".into(),
                    vec![
                        ("lb", lb.clone()),
                        ("lc", lc.clone()),
                        ("base", b.clone()),
                        ("code", c.clone()),
                        ("statics", statics.clone()),
                        ("f", b.clone()),
                        ("fd", lit(fd)),
                        ("rs", rsl),
                        ("P", pp.clone()),
                        ("E", e_lam.clone()),
                    ],
                ),
                None => R::Inst(
                    "tr.entry0".into(),
                    vec![
                        ("lb", lb.clone()),
                        ("lc", lc.clone()),
                        ("base", b.clone()),
                        ("code", c.clone()),
                        ("statics", statics.clone()),
                        ("f", b.clone()),
                        ("fd", lit(fd)),
                        ("rs", rsl),
                        ("q", q0raw.clone()),
                        ("kw", kwl),
                        ("E", e_lam.clone()),
                    ],
                ),
            };
            self.run(&mp(inst, vec![simp0(), s_(&hsub), h_e, s_(&hregs), s_(&body_in)]), &[])?
            }
        };
        let _ = rs_args;
        // (stack arguments: for any stk long enough, tr.implements_at_s)
        if let (Some(_), Some(bl)) = (&sargs, &bl) {
            let h = self.close(m0, &[hstk_t.clone(), hle_t.clone()], &[Self::var_id(&stk)])?;
            // (the startup mode's, stopping at t: tr.impl_m_s(false, u, ..) by
            // tr.impl_m_s_intro, u for any alignment)
            if let (true, Some((tt, k))) = (self.startup, self.stop) {
                let (ff, kt) = (self.bm(), self.mk(if k { "true" } else { "false" }, vec![]));
                let ut = self.mk(if aligned { "false" } else { "true" }, vec![]);
                let inst = R::Inst(
                    "tr.impl_m_s_intro".into(),
                    vec![
                        ("b", ff.clone()),
                        ("u", ut.clone()),
                        ("f", b.clone()),
                        ("t", lit(tt)),
                        ("k", kt.clone()),
                        ("base", lb.clone()),
                        ("code", lc.clone()),
                        ("statics", statics.clone()),
                        ("n", lit(nargs)),
                        ("B", bl.clone()),
                    ],
                );
                let i0 = self.run(&mp(inst, vec![simp0(), simp0(), s_(&h)]), &[])?;
                let goal = self.mk("tr.impl_m_s", vec![ff, ut, b.clone(), spec_app.clone(), lit(tt), kt, lb.clone(), lc.clone(), statics.clone()]);
                let imp_in = self.evp(&RP::Defs(Box::new(RP::By(R::S(i0))), vec![spec_name.to_string()]), &goal, &[])?;
                let imp = self.close(imp_in, &cprem, &gvs)?;
                out.push((format!("{p}.impl_m_s"), imp));
                self.callee_effects(&p, ssym, &cns, &mut out)?;
                return Ok(out);
            }
            let inst = R::Inst(
                "tr.implements_s_intro".into(),
                vec![("f", b.clone()), ("base", lb.clone()), ("code", lc.clone()), ("statics", statics.clone()), ("n", lit(nargs)), ("B", bl.clone())],
            );
            let i0 = self.run(&mp(inst, vec![simp0(), simp0(), s_(&h)]), &[])?;
            let goal = self.mk("tr.implements_at_s", vec![b.clone(), spec_app.clone(), lb.clone(), lc.clone(), statics.clone()]);
            let imp_in = self.evp(&RP::Defs(Box::new(RP::By(R::S(i0))), vec![spec_name.to_string()]), &goal, &[])?;
            let imp = self.close(imp_in, &cprem, &gvs)?;
            out.push((format!("{p}.implements_s"), imp));
            self.callee_effects(&p, ssym, &cns, &mut out)?;
            return Ok(out);
        }
        // (the ABI's entry, or any alignment's)
        let ent = if aligned { "abi.entry_ok" } else { "tr.entry_ok_u" };
        // (stopping at t: the contract with the stop, k; never stopping, the
        // contract too)
        // (the startup mode's contract: tr.impl_m(false, u, ..), u for any alignment)
        if let (Some((tt, k)), true) = (self.stop, self.startup) {
            let kp = if k { "true" } else { "false" };
            let up = if aligned { "false" } else { "true" };
            let m_goal = self.parse(&format!(
                "all args objs mem s o. args in abi.ARGS -> objs in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> s in univ(1) -> \
                 abi.loaded(app(s, \"vm\"), {lbp}, {lcp}, statics) -> app(s, \"rip\") = {bp} -> tr.eok({mb}, {up}, s, args) -> tr.objs_ok(s, objs) -> tr.vok({mb}, s, objs, mem) -> tr.run_s(s, {tt}, s, o) -> \
                 tr.mtv({mb}, s, abi.wob(objs, tr.cbm({mb}, app(s, \"fs_base\"))), app({sp}, args), tr.vw({mb}, s, objs, mem), o, {kp})",
                lbp = self.print(&lb),
                lcp = self.print(&lc),
                bp = self.print(&b),
                sp = self.print(&spec_app),
                mb = self.print(&self.bm())
            ))?;
            let m = self.evp(&RP::Defs(Box::new(RP::By(R::S(m0))), vec![spec_name.to_string()]), &m_goal, &[])?;
            let (ff, kt, ut) = (self.bm(), self.mk(kp, vec![]), self.mk(up, vec![]));
            let imp_goal = self.mk("tr.impl_m", vec![ff, ut, b.clone(), spec_app.clone(), lit(tt), kt, lb.clone(), lc.clone(), statics.clone()]);
            let imps = self.evp(&RP::Defs(Box::new(RP::By(R::S(m))), vec!["tr.impl_m".into()]), &imp_goal, &[])?;
            out.push((format!("{p}.impl_m"), self.close(imps, &cprem, &gvs)?));
            self.callee_effects(&p, ssym, &cns, &mut out)?;
            return Ok(out);
        }
        // (... without a stop: tr.impl_d(false, u, ..))
        if self.startup && self.stop.is_none() {
            let up = if aligned { "false" } else { "true" };
            let m_goal = self.parse(&format!(
                "all args objs mem s o. args in abi.ARGS -> objs in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> s in univ(1) -> \
                 abi.loaded(app(s, \"vm\"), {lbp}, {lcp}, statics) -> app(s, \"rip\") = {bp} -> tr.eok({mb}, {up}, s, args) -> tr.objs_ok(s, objs) -> tr.vok({mb}, s, objs, mem) -> tr.run_d(s, s, o) -> \
                 tr.mtv({mb}, s, abi.wob(objs, tr.cbm({mb}, app(s, \"fs_base\"))), app({sp}, args), tr.vw({mb}, s, objs, mem), o, false)",
                lbp = self.print(&lb),
                lcp = self.print(&lc),
                bp = self.print(&b),
                sp = self.print(&spec_app),
                mb = self.print(&self.bm())
            ))?;
            let m = self.evp(&RP::Defs(Box::new(RP::By(R::S(m0))), vec![spec_name.to_string()]), &m_goal, &[])?;
            let (ff, ut) = (self.bm(), self.mk(up, vec![]));
            let imp_goal = self.mk("tr.impl_d", vec![ff, ut, b.clone(), spec_app.clone(), lb.clone(), lc.clone(), statics.clone()]);
            let imps = self.evp(&RP::Defs(Box::new(RP::By(R::S(m))), vec!["tr.impl_d".into()]), &imp_goal, &[])?;
            out.push((format!("{p}.impl_d"), self.close(imps, &cprem, &gvs)?));
            self.callee_effects(&p, ssym, &cns, &mut out)?;
            return Ok(out);
        }
        if let Some((tt, k)) = self.stop {
            let kp = if k { "true" } else { "false" };
            let m_goal = self.parse(&format!(
                "all args objs mem s o. args in abi.ARGS -> objs in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> s in univ(1) -> \
                 abi.loaded(app(s, \"vm\"), {lbp}, {lcp}, statics) -> app(s, \"rip\") = {bp} -> {ent}(s, args) -> tr.objs_ok(s, objs) -> abi.view_ok(s, objs, mem) -> tr.run_s(s, {tt}, s, o) -> \
                 tr.matches_tk({sp}, args, objs, mem, s, o, {kp})",
                lbp = self.print(&lb),
                lcp = self.print(&lc),
                bp = self.print(&b),
                sp = self.print(&spec_app)
            ))?;
            let m = self.evp(&RP::Defs(Box::new(RP::By(R::S(m0))), vec![spec_name.to_string()]), &m_goal, &[])?;
            let kt = self.mk(kp, vec![]);
            let gname = if aligned { "tr.implements_stop" } else { "tr.implements_stop_u" };
            let imp_goal = self.mk(gname, vec![b.clone(), spec_app.clone(), lit(tt), kt, lb.clone(), lc.clone(), statics.clone()]);
            let imps = self.evp(&RP::Defs(Box::new(RP::By(R::S(m))), vec![gname.into()]), &imp_goal, &[])?;
            out.push((format!("{p}.{}", gname.trim_start_matches("tr.")), self.close(imps.clone(), &cprem, &gvs)?));
            if k {
                self.callee_effects(&p, ssym, &cns, &mut out)?;
                return Ok(out);
            }
            // (never stopping: the contract)
            let imp_in = if aligned {
                self.run(&R::Apply(Box::new(f("tr.implements_ns_at")), vec![s_(&imps)]), &[])?
            } else {
                let impu_in = self.run(&R::Apply(Box::new(f("tr.implements_ns_at_u")), vec![s_(&imps)]), &[])?;
                out.push((format!("{p}.implements_u"), self.close(impu_in.clone(), &cprem, &gvs)?));
                self.run(&R::Apply(Box::new(f("tr.implements_u")), vec![s_(&impu_in)]), &[])?
            };
            let imp = self.close(imp_in.clone(), &cprem, &gvs)?;
            out.push((format!("{p}.implements"), imp));
            let dr_t = self.mk("tr.div_raises", vec![spec_app.clone()]);
            let dr = self.assume(&dr_t)?;
            let abi_in = self.run(&R::Apply(Box::new(f("tr.implements_abi")), vec![s_(&dr), s_(&imp_in)]), &[])?;
            let mut aprem = cprem.clone();
            aprem.push(dr_t);
            let abi = self.close(abi_in, &aprem, &gvs)?;
            out.push((format!("{p}.implements_abi"), abi));
            self.callee_effects(&p, ssym, &cns, &mut out)?;
            return Ok(out);
        }
        // m: all args objs mem s o. .. -> tr.matches_t(spec, args, objs, mem, s, o), the spec unfolded
        let m_goal = self.parse(&format!(
            "all args objs mem s o. args in abi.ARGS -> objs in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> s in univ(1) -> \
             abi.loaded(app(s, \"vm\"), {lbp}, {lcp}, statics) -> app(s, \"rip\") = {bp} -> {ent}(s, args) -> tr.objs_ok(s, objs) -> abi.view_ok(s, objs, mem) -> tr.run_d(s, s, o) -> \
             tr.matches_t({sp}, args, objs, mem, s, o)",
            lbp = self.print(&lb),
            lcp = self.print(&lc),
            bp = self.print(&b),
            sp = self.print(&spec_app)
        ))?;
        let m = self.evp(&RP::Defs(Box::new(RP::By(R::S(m0))), vec![spec_name.to_string()]), &m_goal, &[])?;
        let imp_in = if aligned {
            let imp_goal = self.mk("tr.implements_at", vec![b.clone(), spec_app.clone(), lb.clone(), lc.clone(), statics.clone()]);
            self.evp(&RP::Defs(Box::new(RP::By(R::S(m))), vec!["tr.implements_at".into()]), &imp_goal, &[])?
        } else {
            // (for any entry, so for the ABI's)
            let impu_goal = self.mk("tr.implements_at_u", vec![b.clone(), spec_app.clone(), lb.clone(), lc.clone(), statics.clone()]);
            let impu_in = self.evp(&RP::Defs(Box::new(RP::By(R::S(m))), vec!["tr.implements_at_u".into()]), &impu_goal, &[])?;
            let impu = self.close(impu_in.clone(), &cprem, &gvs)?;
            out.push((format!("{p}.implements_u"), impu));
            self.run(&R::Apply(Box::new(f("tr.implements_u")), vec![s_(&impu_in)]), &[])?
        };
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
        self.callee_effects(&p, ssym, &cns, &mut out)?;
        Ok(out)
    }

    /// as a callee: tr.callee_io (tr.callee_io_s) from the spec's structure
    fn callee_effects(&mut self, p: &str, ssym: sl_kernel::SymId, cns: &[usize], out: &mut Vec<(String, Seq)>) -> Result<(), String> {
        let mut eff = super::eff::Eff::new(self.env, p)?;
        match eff.callee_io(ssym, cns) {
            Ok(()) => out.extend(std::mem::take(&mut eff.out)),
            Err(e) => eprintln!("{}: no tr.callee_io yet: {}", p, e),
        }
        Ok(())
    }

    /// the stop form's match of the spec at the entry (tr.entry_gk's MATCH,
    /// of spec args v mem s o): tr.matches_tk -- the startup mode's
    /// tr.mtv(false, ..) of the claim's objects and world
    fn match_k(&self, kt: &Term) -> Term {
        if !self.startup {
            return self.mk("tr.matches_tk", vec![Term::bvar(5), Term::bvar(4), Term::bvar(3), Term::bvar(2), Term::bvar(1), Term::bvar(0), kt.clone()]);
        }
        let ff = self.bm();
        let fs = self.mk("app", vec![Term::bvar(1), Term::bytes(b"fs_base")]);
        let vo = self.mk("abi.wob", vec![Term::bvar(3), self.mk("tr.cbm", vec![ff.clone(), fs])]);
        let p = self.mk("app", vec![Term::bvar(5), Term::bvar(4)]);
        let w = self.mk("tr.vw", vec![ff.clone(), Term::bvar(1), Term::bvar(3), Term::bvar(2)]);
        self.mk("tr.mtv", vec![ff, Term::bvar(1), vo, p, w, Term::bvar(0), kt.clone()])
    }

    /// tr.entry_gk's premises: the claim at the entry f matching (tr.fin_k),
    /// the spec undefined matching (tr.ub_k) -- the startup mode's tr.fin_km,
    /// tr.ub_km
    fn fin_ub_d(&self, f: &Term) -> (R, RA) {
        let ff = self.bm();
        let kf = self.mk("false", vec![]);
        (mpf("tr.fin_dm", vec![t(&ff), t(f)]), p(R::Inst("tr.ub_km".into(), vec![("b", ff), ("k", kf)])))
    }

    fn fin_ub(&self, tt: u128, f: &Term, kt: &Term) -> (R, RA) {
        if self.startup {
            let ff = self.bm();
            (mpf("tr.fin_km", vec![t(&ff), t(&lit(tt)), t(f), t(kt), simp0()]), p(R::Inst("tr.ub_km".into(), vec![("b", ff), ("k", kt.clone())])))
        } else {
            (mpf("tr.fin_k", vec![t(&lit(tt)), t(f), t(kt), simp0()]), p(R::Inst("tr.ub_k".into(), vec![("k", kt.clone())])))
        }
    }

    /// the registers held at the entry at their values there: the
    /// callee-saved ones, and those others the code pushes (no argument's,
    /// not rsp)
    pub(super) fn entry_held(&self) -> Vec<u128> {
        let mut rs = CS_REGS.to_vec();
        for i in self.insns.values() {
            if let (114, Some(g)) = (i.row, nat(&i.fields)) {
                if !rs.contains(&g) && ![4u128, 7, 6, 2, 1, 8, 9].contains(&g) {
                    rs.push(g);
                }
            }
        }
        rs
    }

    /// `tr.regs(m, rs)`, rs the registers entry_held at their values on m
    /// (hm: m a machine); and rs
    fn cs_entry_regs(&mut self, m: &Term, hm: &Seq) -> Result<(Seq, Term), String> {
        let mut r = self.run(&mpf("tr.regs_empty", vec![t(m)]), &[])?;
        let mut prev = self.mk("empty", vec![]);
        for g in self.entry_held() {
            let v = self.gpr(m, g);
            let ty = R::Apply(Box::new(f("x86i.reg_typed")), vec![t(m), t(&lit(g)), s_(hm), simp0()]);
            r = self.run(&R::Apply(Box::new(f("tr.regs_add")), vec![t(m), t(&prev), t(&lit(g)), t(&lit(8)), t(&v), s_(&r), simp0(), simpw(vec![ty])]), &[])?;
            prev = self.upd(&prev, g, 8, &v);
        }
        Ok((r, prev))
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
