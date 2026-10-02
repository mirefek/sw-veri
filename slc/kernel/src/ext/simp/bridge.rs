//! The bridge from readable GIMPLE to machine code (part of the trusted
//! `simp` extension; proof-plan section 6.3), for code without loops:
//! `bridge(h, {app(spec, args)}, ..)` with `h: runs(abi.run_to_return(), S,
//! O)` states `abi.matches(spec, args, S, O)` (proofs/abi_bridge.core):
//! the machine's outcome O is the spec's raising, a return matching the
//! spec's ok outcome, or (not here: no loops) a divergence -- the spec run
//! on a view v of S's memory (S's but for scratch bytes).
//!
//! v: the memory after the prologue -- the machine run (symex) up to its
//! first access other than at the entry's rsp, a branch or the return: the
//! code's spills of the arguments to the stack, as its reads see them. It
//! is a witness only: shown a scratch view matching S's memory (by simp,
//! from the library's lemmas: `abi.slot_matches`, `abi.slot_view`, ..).
//!
//! The spec runs from the view `abi.view(v, S)` by spec_run's machinery:
//! its ok branches (conditions Ck, outcome ok(Wk, (r0, r1))) and D, the
//! condition whose failure makes it raise from any world. For each branch,
//! the machine runs by symex under Ck and D -- with the argument
//! registers holding args where D gives the arity, the premises its steps
//! need that the facts do not give (a memory access) shown by simp from the
//! premises (the access lemmas: `g.read_at`, `abi.slot_at`, ..) and Ck --
//! and for each of its paths (conditions Cp, final state Sp) the return
//! case of `abi.matches_at` holds at the witnesses Sp and Wk (its open
//! values those the machine returns in rax:rdx), conjunct by conjunct, by
//! simp. Last, D implies one of the Ck (coverage). Then O matches: if D
//! fails, the spec raises (from the view, its exception any); if D holds,
//! some Ck holds, the machine's run is one of that branch's paths, which
//! matches. No reasoning about what the function computes: each side's
//! own conditions and effects are compared.

use super::*;
use crate::env::KResult;

impl Logic {
    /// `abi.matches(spec, args, S, O)` (see the module).
    pub fn bridge(&self, env: &Env, p: &Term, premises: &[Term]) -> KResult<Term> {
        let kerr = |m: String| crate::env::KernelError(format!("bridge: {}", m));
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| kerr(format!("needs `{}`", n)));
        let t0 = std::time::Instant::now();
        let dbg = std::env::var("BRIDGE_DEBUG").is_ok();
        let lap = |what: &str| {
            if dbg {
                eprintln!("bridge: {:8.3}s {}", t0.elapsed().as_secs_f64(), what)
            }
        };
        let (runs, rtr, app, matches, matches_at, fn_update, empty, badd, ok, pair, exc) = (
            sym("runs")?,
            sym("abi.run_to_return")?,
            sym("app")?,
            sym("abi.matches")?,
            sym("abi.matches_at")?,
            sym("fn_update")?,
            sym("empty")?,
            sym("bits_add")?,
            sym("ok")?,
            sym("pair")?,
            sym("exc")?,
        );
        let pr = crate::syntax::Printer::new(env);
        let short = |t: &Term| pr.term(t).chars().take(600).collect::<String>();
        // the run, the spec and its arguments
        let Some((s, o)) = premises.iter().find_map(|t| match t.node() {
            Node::App(r, a) if *r == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, x) if *g == rtr && x.is_empty()) => Some((a[1].clone(), a[2].clone())),
            _ => None,
        }) else {
            return Err(kerr("no premise `runs(abi.run_to_return(), S, O)`".into()));
        };
        let Node::App(ap, fa) = p.node() else { return Err(kerr("the spec is not `app(spec, args)`".into())) };
        if *ap != app || fa.len() != 2 {
            return Err(kerr("the spec is not `app(spec, args)`".into()));
        }
        let (spec, args) = (fa[0].clone(), fa[1].clone());
        let field = |t: &Term, k: &[u8]| Term::app(app, vec![t.clone(), Term::bytes(k)]);
        let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
        // the view of the memory v: abi.view(v, S)
        let rsp = Term::app(app, vec![field(&s, b"gpr"), nat(4)]);
        let view = |v: &Term| {
            let mut w = Term::app(empty, vec![]);
            for (k, x) in [
                (&b"vm"[..], v.clone()),
                (&b"os"[..], field(&s, b"os")),
                (&b"fs_base"[..], field(&s, b"fs_base")),
                (&b"cpu"[..], field(&s, b"cpu")),
                (&b"sp"[..], Term::app(badd, vec![nat(64), rsp.clone(), nat(8)])),
            ] {
                w = Term::app(fn_update, vec![w, Term::bytes(k), x]);
            }
            w
        };
        let sp = Simp::new(env, self);
        let in_ = sp.s.in_.unwrap();
        let u1 = Term::app(sp.s.univ.unwrap(), vec![nat(1)]);
        let is_run = |t: &Term| matches!(t.node(), Node::App(r, a) if *r == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, _) if *g == rtr));
        let compound = |l: &Term| match l.node() {
            Node::App(c, _) => *c == env.builtins.imp || is(*c, sp.s.or) || is(*c, sp.s.and),
            _ => false,
        };
        // (the instructions' lemmas: symex's, not simp's)
        let step = sym("x86_64_linux.step")?;
        let is_step = |t: &Term| {
            let mut st = vec![t.clone()];
            while let Some(u) = st.pop() {
                if let Node::App(g, xs) = u.node() {
                    if *g == step {
                        return true;
                    }
                    st.extend(xs.iter().cloned());
                }
            }
            false
        };
        // (the premises but the run and the instructions: for simp, which
        // would unfold the run)
        let mut no_run: Vec<Term> = premises.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
        // (with the entry's typing literals: rsp a word, the memory a Vm --
        // for the lemmas' premises)
        sp.set_nats(&no_run);
        for t in [
            Term::app(in_, vec![rsp.clone(), Term::app(sym("bits")?, vec![nat(64)])]),
            Term::app(in_, vec![field(&s, b"vm"), Term::app(sym("x86_64_linux.Vm")?, vec![])]),
        ] {
            if sp.typed(&no_run, &t) {
                no_run.push(t);
            }
        }
        let with_run = |facts: &[Term], s2: &Term| -> Vec<Term> {
            facts.iter().map(|t| if is_run(t) { Term::app(runs, vec![Term::app(rtr, vec![]), s2.clone(), o.clone()]) } else { t.clone() }).collect()
        };
        // the prologue: the machine from S with the argument registers
        // holding args (all six: v is a witness only, its obligations shown
        // below -- where a register is no argument, its store is scratch)
        let vm0 = field(&s, b"vm");
        if std::env::var("BRIDGE_SPEC_ONLY").is_ok() {
            let conj = |cs: &[Term]| cs.iter().cloned().reduce(|a, b| Term::app(sp.s.and.unwrap(), vec![a, b])).unwrap_or_else(|| sp.tt());
            let out = self.spec_run_cut(env, p, &view(&vm0), premises)?;
            for (c, o) in &out.branches {
                eprintln!("branch: {} => {}", short(&conj(c)), short(o));
            }
            if let Some(cut) = &out.cut {
                eprintln!("cut: l0 = {}; pre = {}", short(&cut.l0), short(&conj(&cut.pre)));
                for (e, vs, bs) in &cut.exits {
                    eprintln!("  exit {} ({} params): {} branches", short(e), vs.len(), bs.len());
                    for (c, o) in bs {
                        eprintln!("    {} => {}", short(&conj(c)), short(o));
                    }
                }
                let it = self.spec_iter(env, cut, premises, self.bridge_fresh(env, premises, &out.statement))?;
                eprintln!("iteration from {}:", short(&it.lv));
                for (c, o, on) in &it.branches {
                    eprintln!("  {} => {} {}", short(&conj(c)), short(o), if *on { "(on)" } else { "(out)" });
                }
            }
            return Err(kerr("BRIDGE_SPEC_ONLY".into()));
        }
        let v = {
            let mut gpr = field(&s, b"gpr");
            let mut facts = premises.to_vec();
            for (i, r) in [7u64, 6, 2, 1, 8, 9].iter().enumerate() {
                let arg = Term::app(app, vec![args.clone(), nat(i as u64)]);
                facts.push(Term::app(in_, vec![arg.clone(), Term::app(sym("bits")?, vec![nat(64)])]));
                gpr = Term::app(fn_update, vec![gpr, nat(*r), arg]);
            }
            let s2 = Term::app(fn_update, vec![s.clone(), Term::bytes(b"gpr"), gpr]);
            let facts = with_run(&facts, &s2);
            *self.symex_simp.borrow_mut() = facts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
            *self.symex_prologue.borrow_mut() = Some(None);
            let r = self.symex(env, &[], &facts);
            self.symex_simp.borrow_mut().clear();
            let end = self.symex_prologue.borrow_mut().take().flatten();
            lap("the prologue");
            match (r, end) {
                (Ok(_), Some(st)) => sp.term(&field(&st, b"vm")),
                (r, _) => {
                    if let (Err(e), true) = (&r, std::env::var("BRIDGE_DEBUG").is_ok()) {
                        eprintln!("bridge: the prologue: {}", e.0);
                    }
                    vm0.clone()
                }
            }
        };
        // v a scratch view of S's memory, matching it
        let spv = Term::app(badd, vec![nat(64), rsp.clone(), nat(8)]);
        let (vm_t, sv, wm, store_le) = (sym("x86_64_linux.Vm")?, sym("abi.scratch_view")?, sym("abi.world_matches")?, sym("x86_64_linux.store_le")?);
        // (one store at a time: v = fn_update(y, "bytes", B), B a chain of
        // stores on app(y, "bytes"), each layer from the one below)
        let mut layers: Vec<Term> = Vec::new();
        if let Node::App(fu, fa) = v.node() {
            if *fu == fn_update && fa.len() == 3 && fa[1] == Term::bytes(b"bytes") {
                let mut b = fa[2].clone();
                loop {
                    layers.push(Term::app(fn_update, vec![fa[0].clone(), fa[1].clone(), b.clone()]));
                    match b.node() {
                        Node::App(st, sa) if *st == store_le && sa.len() == 4 => b = sa[0].clone(),
                        _ => break,
                    }
                }
                if b != field(&fa[0], b"bytes") {
                    layers.clear();
                } else {
                    layers.push(Term::app(fn_update, vec![fa[0].clone(), fa[1].clone(), b]));
                }
                layers.reverse();
            }
        }
        let mut obl: Vec<Term> = Vec::new();
        for l in layers.iter().chain(std::iter::once(&v)) {
            obl.push(Term::app(sv, vec![l.clone(), vm0.clone(), spv.clone()]));
            obl.push(Term::app(wm, vec![vm0.clone(), vm0.clone(), l.clone(), spv.clone()]));
        }
        obl.push(Term::app(in_, vec![v.clone(), Term::app(vm_t, vec![])]));
        obl.push(Term::app(in_, vec![v.clone(), u1.clone()]));
        let mut known = no_run.clone();
        for c in obl {
            if known.contains(&c) {
                continue;
            }
            if let Err(e) = self.simp_prove_loops(env, &known, &c, &[]) {
                return Err(kerr(format!("the memory after the prologue is not shown a view of the entry's: {}: {}", short(&c), e.0)));
            }
            known.push(c);
        }
        lap("the view's obligations");
        let w = view(&v);
        // the spec's branches
        let out = self.spec_run_out(env, p, &w, &[], premises)?;
        lap("the spec on the view");
        if dbg {
            if let Some(d) = &out.ub {
                eprintln!("bridge: D = {}", pr.term(d));
            }
        }
        let and = sp.s.and.unwrap();
        let conj = |cs: &[Term]| cs.iter().cloned().reduce(|a, b| Term::app(and, vec![a, b])).unwrap_or_else(|| sp.tt());
        let bf = env.binders_fn();
        // (the statement of the spec's branches, a premise for the checks)
        let mut base: Vec<Term> = no_run.clone();
        base.push(out.statement.clone());
        let goal_of = |m1: &Term| -> Option<Term> {
            let o1 = Term::app(ok, vec![m1.clone(), Term::app(empty, vec![])]);
            sp.unfold(matches_at, &[spec.clone(), args.clone(), s.clone(), v.clone(), o1])
        };
        // the facts of every branch: D (a branch is taken only where the
        // spec is defined; elsewhere it raises), the view in the universe
        // (D's chains end in its negation; shown below), the arguments in
        // their registers (where D gives the arity)
        let mut dfacts = premises.to_vec();
        dfacts.extend(out.ub.iter().cloned());
        dfacts.push(Term::app(in_, vec![w.clone(), u1.clone()]));
        let (s2, dfacts) = self.bridge_couple(env, &sp, &dfacts, &s, &args)?;
        lap("the arguments");
        let mut covers: Vec<Term> = Vec::new();
        for (bi, (conds, outcome)) in out.branches.iter().enumerate() {
            // ok(Wk, (r0, r1)): a branch to match; a raise from the view
            // exc(W, e): the raise case, whatever the machine does; others
            // (a raise elsewhere) are covered by D or not at all
            let Node::App(okk, oa) = outcome.node() else { continue };
            // (its parameters' typing dropped from the coverage: inhabited)
            let core: Vec<Term> = conds.iter().filter(|c| !Self::bridge_param_typing(&sp, c, out.first)).cloned().collect();
            if *okk == exc && oa.len() == 2 && oa[0] == w {
                // (e: an open value -- empty, then -- or a term in univ(1))
                let e0 = match oa[1].node() {
                    Node::Var(x, xa) if xa.is_empty() && *x >= out.first => Term::app(empty, vec![]),
                    _ => oa[1].clone(),
                };
                let sub = |t: &Term| match oa[1].node() {
                    Node::Var(x, xa) if xa.is_empty() && *x >= out.first => t.subst_var(*x, &e0, &bf),
                    _ => t.clone(),
                };
                let mut ps = dfacts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect::<Vec<_>>();
                ps.push(out.statement.clone());
                ps.extend(core.iter().cloned());
                let mut obl: Vec<Term> = conds.iter().map(sub).filter(|c| !core.contains(c)).collect();
                obl.push(Term::app(in_, vec![e0.clone(), u1.clone()]));
                obl.push(Term::app(runs, vec![p.clone(), w.clone(), Term::app(exc, vec![w.clone(), e0.clone()])]));
                for c in obl {
                    if let Err(e) = self.simp_prove_loops(env, &ps, &c, &[]) {
                        return Err(kerr(format!("branch {} of the spec ({}), a raise: not shown: {}: {}", bi + 1, short(&conj(conds)), short(&c), e.0)));
                    }
                    ps.push(c);
                }
                covers.push(conj(&core));
                lap(&format!("branch {}: a raise", bi + 1));
                continue;
            }
            if *okk != ok || oa.len() != 2 || !matches!(oa[1].node(), Node::App(pp, _) if *pp == pair) {
                continue;
            }
            covers.push(conj(&core));
            if dbg {
                for c in conds {
                    eprintln!("bridge: branch {} condition: {}", bi + 1, pr.term(c));
                }
            }
            // the machine under Ck (and the facts of every branch); the
            // arguments in their registers again where Ck gives more (a
            // nonzero argument: `abi.arg0`)
            let mut facts = dfacts.clone();
            facts.extend(conds.iter().cloned());
            let s2 = if s2 == s {
                let (s3, f3) = self.bridge_couple(env, &sp, &facts, &s, &args)?;
                facts = f3;
                lap(&format!("branch {}: the arguments", bi + 1));
                s3
            } else {
                s2.clone()
            };
            // (Ck's reads of memory also as the machine's: sums of bytes)
            let words = super::spec::Words::new(&sp, self, true, &facts);
            // (twice: the second with the first's forms in the context)
            for _ in 0..2 {
                let ctx = facts.clone();
                sp.set_nats(&ctx);
                words.memo.borrow_mut().clear();
                for c in conds {
                    let c2 = sp.prop(&words.word(&ctx, c), Pol::Other);
                    if !facts.contains(&c2) {
                        facts.push(c2);
                    }
                }
            }
            let facts = with_run(&facts, &s2);
            if dbg {
                let ty: Vec<String> = facts.iter().map(|t| pr.term(t)).filter(|x| x.starts_with("app(args")).collect();
                eprintln!("bridge: branch {} argument facts: {:?}", bi + 1, ty);
            }
            // (for simp on a step's premise: not the run itself, nor the
            // instructions' lemmas)
            *self.symex_simp.borrow_mut() = facts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
            let r = self.symex(env, &[], &facts);
            self.symex_simp.borrow_mut().clear();
            lap(&format!("branch {}: the machine", bi + 1));
            let r = r.map_err(|e| kerr(format!("branch {} of the spec ({}): the machine: {}", bi + 1, short(&conj(conds)), e.0)))?;
            // its paths: `ex vs. Cp.. && O = ok(Sp, empty)`
            let mut ds = Vec::new();
            sp.disjuncts(&r, &mut ds);
            let mut fresh = self.bridge_fresh(env, premises, &r);
            for (pi, d) in ds.iter().enumerate() {
                let mut body = d.clone();
                while let Node::App(q, b) = body.node() {
                    if *q != self.ex {
                        break;
                    }
                    body = inst_k(env, &b[0], &[Term::var(fresh, vec![])]);
                    fresh += 1;
                }
                let mut cs = Vec::new();
                sp.conjuncts(&body, &mut cs);
                let mut m1 = None;
                let mut pconds = Vec::new();
                for c in cs {
                    match c.node() {
                        Node::App(e, ab) if *e == env.builtins.eq && ab[0] == o => match ab[1].node() {
                            Node::App(k, kb) if *k == ok => m1 = Some(kb[0].clone()),
                            _ => return Err(kerr(format!("a machine path ends other than by a return: {}", short(&c)))),
                        },
                        _ => pconds.push(c),
                    }
                }
                let Some(m1) = m1 else { return Err(kerr("a machine path without its outcome".into())) };
                let Some(goal) = goal_of(&m1) else { return Err(kerr("`abi.matches_at` is not a definition".into())) };
                let fail = |what: &str, e: String| {
                    kerr(format!("branch {} of the spec ({}), machine path {} ({}): {}: {}", bi + 1, short(&conj(conds)), pi + 1, short(&conj(&pconds)), what, e))
                };
                // the witnesses: m1, and the branch's world with its open
                // values (parameters) those the machine returns -- (rax, rdx)
                let mut ps: Vec<Term> = facts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
                ps.push(out.statement.clone());
                // (and in word forms: the machine's values compared)
                let stw = sp.prop(&words.word(&facts, &out.statement), Pol::Other);
                if stw != out.statement {
                    ps.push(stw);
                }
                ps.extend(pconds.iter().cloned());
                sp.set_nats(&ps);
                let reg = |r: u64| sp.term(&Term::app(app, vec![field(&m1, b"gpr"), nat(r)]));
                let (rax, rdx) = (reg(0), reg(2));
                let Node::App(_, pv) = oa[1].node() else { unreachable!() };
                let mut sigma: Vec<(crate::term::VarId, Term)> = Vec::new();
                for (x, m) in [(&pv[0], &rax), (&pv[1], &rdx)] {
                    if let Node::Var(v, va) = x.node() {
                        if va.is_empty() && *v >= out.first && !sigma.iter().any(|(u, _)| u == v) {
                            sigma.push((*v, m.clone()));
                        }
                    }
                }
                let sub = |t: &Term| sigma.iter().fold(t.clone(), |t, (v, m)| t.subst_var(*v, m, &bf));
                let w2 = sub(&oa[0]);
                // (the branch's conditions at the witnesses: shown, as is
                // the spec's run there)
                let mut obl: Vec<Term> = conds.iter().map(sub).filter(|c| !facts.contains(c)).collect();
                // the return case of abi.matches_at at (m1, w2), conjunct by conjunct
                let mut gds = Vec::new();
                sp.disjuncts(&goal, &mut gds);
                let case = gds.iter().find_map(|d| {
                    let Node::App(q, b) = d.node() else { return None };
                    if *q != self.ex {
                        return None;
                    }
                    let b1 = inst_k(env, &b[0], &[m1.clone()]);
                    match b1.node() {
                        Node::App(q2, b2) if *q2 == self.ex => Some(inst_k(env, &b2[0], &[w2.clone()])),
                        _ => None,
                    }
                });
                let Some(case) = case else { return Err(kerr("`abi.matches_at` has no return case `ex m1 w2. ..`".into())) };
                sp.conjuncts(&case, &mut obl);
                let mut shown = ps.clone();
                for c in obl {
                    let c = sp.prop(&c, Pol::Other);
                    if sp.is_true(&c) || shown.contains(&c) {
                        continue;
                    }
                    // (first from the lemmas and literals only: the compound
                    // facts split simp's paths)
                    let lean: Vec<Term> = shown.iter().filter(|t| !compound(t)).cloned().collect();
                    if self.simp_prove_loops(env, &lean, &c, &[]).is_ok() {
                        shown.push(c.clone());
                        lap(&format!("branch {}, path {}: {}", bi + 1, pi + 1, short(&c).chars().take(60).collect::<String>()));
                        continue;
                    }
                    if let Err(e) = self.simp_prove_loops(env, &shown, &c, &[]) {
                        // (or with its reads of memory as sums of bytes)
                        sp.set_nats(&shown);
                        let c2 = sp.prop(&words.word(&shown, &c), Pol::Other);
                        if dbg {
                            eprintln!("bridge: in word forms: {}", pr.term(&c2));
                        }
                        if c2 == c || self.simp_prove_loops(env, &shown, &c2, &[]).is_err() {
                            return Err(fail(&format!("its return does not match, at {}", short(&c)), e.0));
                        }
                    }
                    shown.push(c.clone());
                    lap(&format!("branch {}, path {}: {}", bi + 1, pi + 1, short(&c).chars().take(60).collect::<String>()));
                }
            }
        }
        // the view in the universe (for the raise from it: D's failure; and
        // the branches' conditions)
        let wu = Term::app(in_, vec![w.clone(), u1.clone()]);
        if self.simp_prove_loops(env, &no_run, &wu, &[]).is_err() {
            return Err(kerr("the view is not shown in univ(1)".into()));
        }
        base.push(wu);
        // coverage: D (or always, without undefined behaviour) implies a branch
        let any = covers.into_iter().reduce(|a, b| sp.or(a, b)).unwrap_or_else(|| sp.ff());
        let cover = match &out.ub {
            Some(d) => Term::app(env.builtins.imp, vec![d.clone(), any]),
            None => any,
        };
        if let Err(e) = self.simp_prove_loops(env, &base, &cover, &[]) {
            return Err(kerr(format!("the spec's branches do not cover its defined cases: {}", e.0)));
        }
        lap("coverage");
        Ok(Term::app(matches, vec![spec, args, s, o]))
    }

    /// The entry state S with the argument registers holding args where the
    /// facts show it (the entry's `all x. .. -> reg(x) = app(args, x)`, the
    /// arity `ord_le(i+1, seq_len(args))` from D): S' (shown = S), and the
    /// facts with the equations and the arguments' typing.
    fn bridge_couple(&self, env: &Env, sp: &Simp, facts: &[Term], s: &Term, args: &Term) -> KResult<(Term, Vec<Term>)> {
        let kerr = |m: String| crate::env::KernelError(format!("bridge: {}", m));
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| kerr(format!("needs `{}`", n)));
        let (runs, rtr, app, fn_update) = (sym("runs")?, sym("abi.run_to_return")?, sym("app")?, sym("fn_update")?);
        let field = |t: &Term, k: &[u8]| Term::app(app, vec![t.clone(), Term::bytes(k)]);
        let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
        let mut facts = facts.to_vec();
        // (the entry's `all x. .. -> reg(x) = app(args, x)`, at 0..5)
        let mut entry_cs = Vec::new();
        for t in facts.clone().iter() {
            sp.conjuncts(t, &mut entry_cs);
        }
        for c in &entry_cs {
            let Node::App(q, qa) = c.node() else { continue };
            if *q != self.all || qa.len() != 1 {
                continue;
            }
            for i in 0..6u64 {
                let inst = sp.prop(&inst_k(env, &qa[0], &[nat(i)]), Pol::Other);
                let arg = Term::app(app, vec![args.clone(), nat(i)]);
                let mut mentions = false;
                let mut st = vec![inst.clone()];
                while let Some(t) = st.pop() {
                    if t == arg {
                        mentions = true;
                        break;
                    }
                    if let Node::App(_, xs) = t.node() {
                        st.extend(xs.iter().cloned());
                    }
                }
                if mentions && !facts.contains(&inst) {
                    facts.push(inst);
                }
            }
        }
        let is_run = |t: &Term| matches!(t.node(), Node::App(r, a) if *r == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, _) if *g == rtr));
        let step = sym("x86_64_linux.step")?;
        let is_step = |t: &Term| {
            let mut st = vec![t.clone()];
            while let Some(u) = st.pop() {
                if let Node::App(g, xs) = u.node() {
                    if *g == step {
                        return true;
                    }
                    st.extend(xs.iter().cloned());
                }
            }
            false
        };
        let no_run: Vec<Term> = facts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
        // (the lemmas and literals: the compound facts split simp's paths --
        // D, needed for the arity only)
        let compound = |l: &Term| match l.node() {
            Node::App(c, _) => *c == env.builtins.imp || is(*c, sp.s.or) || is(*c, sp.s.and),
            _ => false,
        };
        let lean: Vec<Term> = no_run.iter().filter(|t| !compound(t)).cloned().collect();
        let mut gpr = field(s, b"gpr");
        for (i, r) in [7u64, 6, 2, 1, 8, 9].iter().enumerate() {
            let reg = Term::app(app, vec![field(s, b"gpr"), nat(*r)]);
            let arg = Term::app(app, vec![args.clone(), nat(i as u64)]);
            let e = Term::app(env.builtins.eq, vec![reg.clone(), arg.clone()]);
            // (the arity first: the spec's own guard `ord_le(i+1, seq_len(args))`)
            let guard = Term::app(sym("ord_le")?, vec![nat(i as u64 + 1), Term::app(sym("seq_len")?, vec![args.clone()])]);
            let mut with_guard = lean.clone();
            let arity = self.simp_prove_loops(env, &lean, &guard, &[]).is_ok() || self.simp_prove_loops(env, &no_run, &guard, &[]).is_ok();
            if arity {
                with_guard.push(guard);
            }
            // (or by a lemma from other facts: `abi.arg0`, a nonzero
            // argument passed)
            let coupled = self.simp_prove_loops(env, &with_guard, &e, &[]).is_ok();
            if !coupled && !arity {
                // (fewer arguments: none further)
                break;
            }
            if coupled {
                // (the register's typing, and reg = arg: the argument's)
                let bits64 = Term::app(sym("bits")?, vec![nat(64)]);
                sp.set_nats(&no_run);
                let rty = Term::app(sp.s.in_.unwrap(), vec![reg, bits64.clone()]);
                let aty = Term::app(sp.s.in_.unwrap(), vec![arg.clone(), bits64]);
                if sp.typed(&no_run, &rty) || self.simp_prove_loops(env, &lean, &rty, &[]).is_ok() {
                    facts.push(aty);
                }
                facts.push(e);
                gpr = Term::app(fn_update, vec![gpr, nat(*r), arg]);
            }
        }
        let s2 = if gpr == field(s, b"gpr") { s.clone() } else { Term::app(fn_update, vec![s.clone(), Term::bytes(b"gpr"), gpr]) };
        let same = Term::app(env.builtins.eq, vec![s2.clone(), s.clone()]);
        let no_run2: Vec<Term> = facts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
        if self.simp_prove_loops(env, &no_run2, &same, &[]).is_err() {
            let pr = crate::syntax::Printer::new(env);
            return Err(kerr(format!("the entry state with the arguments in their registers is not shown to be it: {}", pr.term(&same).chars().take(600).collect::<String>())));
        }
        Ok((s2, facts))
    }

    /// `x in S` for a parameter x of the spec's branch (a value it leaves
    /// open) of a universe or words
    fn bridge_param_typing(sp: &Simp, c: &Term, first: u32) -> bool {
        match c.node() {
            Node::App(i, ab) if is(*i, sp.s.in_) && ab.len() == 2 => {
                matches!(ab[0].node(), Node::Var(v, va) if va.is_empty() && *v >= first)
                    && matches!(ab[1].node(), Node::App(u, _) if is(*u, sp.s.univ) || Some(*u) == sp.env.sym_by_name.get("bits").copied())
            }
            _ => false,
        }
    }

    fn bridge_fresh(&self, env: &Env, premises: &[Term], r: &Term) -> u32 {
        let mut fresh = env.vars.len() as u32 + 5_000_000;
        for t in premises.iter().chain([r]) {
            fresh = fresh.max(max_var(t) + 1);
        }
        fresh
    }
}
