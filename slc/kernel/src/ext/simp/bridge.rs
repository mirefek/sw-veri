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
use super::bridge_loop::LoopCx;

impl Logic {
    /// `abi.matches(spec, args, S, O)` (see the module).
    pub fn bridge(&self, env: &Env, p: &Term, inv: Option<&Term>, premises: &[Term]) -> KResult<Term> {
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
        let out = self.spec_run_cut(env, p, &w, premises)?;
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
        // (a loop: the machine's head, the first address a path is at twice,
        // from the way to the spec's loop; the branches without the loop
        // stop there -- reaching it, they do not match)
        let head: Option<u128> = match &out.cut {
            Some(cut) => {
                let mut facts = dfacts.clone();
                facts.extend(cut.pre.iter().cloned());
                let facts = with_run(&facts, &s2);
                *self.symex_simp.borrow_mut() = facts.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect();
                *self.symex_head.borrow_mut() = Some(None);
                let r = self.symex(env, &[], &facts);
                self.symex_simp.borrow_mut().clear();
                let h = self.symex_head.borrow_mut().take().flatten();
                match (r, h) {
                    (Ok(_), Some(h)) => Some(h),
                    (Err(e), _) => return Err(kerr(format!("the machine's way to the loop: {}", e.0))),
                    _ => return Err(kerr("the spec loops, the machine's way there does not".into())),
                }
            }
            None if inv.is_some() => return Err(kerr("an invariant for a program without a loop".into())),
            None => None,
        };
        let wm_sym = sym("abi.world_matches")?;
        let stops: Vec<Term> = head.iter().map(|h| Term::nat(crate::nat::Nat::from_u128(*h))).collect();
        lap("the loop's head");
        let mut covers: Vec<Term> = Vec::new();
        // (the spec's statement by branches: `all ps. C.. -> runs(p, w, O)`)
        let mut stmt_parts: Vec<Term> = Vec::new();
        sp.conjuncts(&out.statement, &mut stmt_parts);
        let spec_run_of = |t: &Term| matches!(t.node(), Node::App(r, a) if *r == runs && a.len() == 3) && !is_run(t);
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
            let r = self.symex(env, &stops, &facts);
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
                let Some(m1) = m1 else {
                    // (a path to the loop's head the branch's conditions rule
                    // out: not taken -- its conditions contradict them)
                    // (on the lemmas and literals: the compound facts would
                    // split simp's paths)
                    let mut ps: Vec<Term> = facts.iter().filter(|t| !is_run(t) && !is_step(t) && !compound(t)).cloned().collect();
                    sp.set_nats(&ps);
                    for c in &pconds {
                        ps.push(c.clone());
                        ps.push(sp.prop(&words.word(&facts, c), Pol::Other));
                    }
                    if self.simp_prove_loops(env, &ps, &sp.ff(), &[]).is_ok() {
                        continue;
                    }
                    return Err(kerr(format!("branch {} of the spec ({}): a machine path ({}) reaches the loop's head, the spec's branch does not", bi + 1, short(&conj(conds)), short(&conj(&pconds)))));
                };
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
                    // (the memories' match: their bytes' agreement first, by layers)
                    if let Node::App(g, ga) = c.node() {
                        if *g == wm_sym && ga.len() == 4 {
                            let bytes = |t: &Term| sp.term(&field(t, b"bytes"));
                            if let Ok(k) = self.bridge_agree(env, &shown, &s, &bytes(&ga[1]), &bytes(&ga[2])) {
                                shown = k;
                            }
                        }
                    }
                    // (the spec's run: the branch's statement `all ps. C.. ->
                    // runs(p, w, O)` at the witnesses, its C's shown)
                    if spec_run_of(&c) {
                        let h = conds.iter().rev().fold(c.clone(), |t, ci| Term::app(env.builtins.imp, vec![sub(ci), t]));
                        let held = |ci: &Term| {
                            let ci = sp.prop(&sub(ci), Pol::Other);
                            sp.is_true(&ci) || shown.contains(&ci) || sp.typed(&shown, &ci) || self.symex_decide(&sp, &shown, &ci) == Some(true)
                        };
                        // (h an instance of a part: its binders matched)
                        let instance = |part: &Term| {
                            let mut fresh = super::max_var(part).max(super::max_var(&h)) + 1;
                            let (mut b, mut vs) = (part.clone(), Vec::new());
                            while let Node::App(q, a) = b.node() {
                                if *q != self.all {
                                    break;
                                }
                                vs.push(fresh);
                                b = inst_k(env, &a[0], &[Term::var(fresh, vec![])]);
                                fresh += 1;
                            }
                            super::pmatch(&b, &h, &vs, &mut Vec::new())
                        };
                        if conds.iter().all(held) && stmt_parts.iter().any(instance) {
                            shown.push(c.clone());
                            lap(&format!("branch {}, path {}: {} (the branch's statement)", bi + 1, pi + 1, short(&c).chars().take(60).collect::<String>()));
                            continue;
                        }
                        // (or an instance up to values: where h and the part
                        // differ -- the machine's value, the spec's -- equal)
                        fn diff(pat: &Term, t: &Term, pvars: &[crate::term::VarId], binds: &mut Vec<(crate::term::VarId, Term)>, out: &mut Vec<(Term, Term)>) -> bool {
                            match (pat.node(), t.node()) {
                                (Node::Var(v, a), _) if a.is_empty() && pvars.contains(v) => match binds.iter().find(|(w, _)| w == v) {
                                    Some((_, b)) => b == t,
                                    None => {
                                        binds.push((*v, t.clone()));
                                        true
                                    }
                                },
                                (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => a.iter().zip(b.iter()).all(|(x, y)| diff(x, y, pvars, binds, out)),
                                _ if pat == t => true,
                                _ => {
                                    let mut vs = Vec::new();
                                    pat.vars(&mut vs);
                                    if vs.iter().any(|v| pvars.contains(v)) {
                                        return false;
                                    }
                                    out.push((t.clone(), pat.clone()));
                                    true
                                }
                            }
                        }
                        let up_to = |part: &Term| -> Option<Vec<(Term, Term)>> {
                            let mut fresh = super::max_var(part).max(super::max_var(&h)) + 1;
                            let (mut b, mut vs) = (part.clone(), Vec::new());
                            while let Node::App(q, a) = b.node() {
                                if *q != self.all {
                                    break;
                                }
                                vs.push(fresh);
                                b = inst_k(env, &a[0], &[Term::var(fresh, vec![])]);
                                fresh += 1;
                            }
                            let mut out = Vec::new();
                            (diff(&b, &h, &vs, &mut Vec::new(), &mut out) && !out.is_empty() && out.len() <= 4 && out.iter().all(|(x, y)| x.loose_depth(&bf) == 0 && y.loose_depth(&bf) == 0)).then_some(out)
                        };
                        if conds.iter().all(held) {
                            let lean: Vec<Term> = shown.iter().filter(|t| !compound(t)).cloned().collect();
                            let equal = |(x, y): &(Term, Term)| {
                                let e = sp.prop(&Term::app(env.builtins.eq, vec![x.clone(), y.clone()]), Pol::Other);
                                sp.is_true(&e) || shown.contains(&e) || self.simp_prove_loops(env, &lean, &e, &[]).is_ok() || {
                                    sp.set_nats(&shown);
                                    let e2 = sp.prop(&words.word(&shown, &e), Pol::Other);
                                    sp.is_true(&e2) || e2 != e && self.simp_prove_loops(env, &lean, &e2, &[]).is_ok()
                                }
                            };
                            if stmt_parts.iter().filter_map(up_to).any(|ds| ds.iter().all(equal)) {
                                shown.push(c.clone());
                                lap(&format!("branch {}, path {}: {} (the branch's statement, values equal)", bi + 1, pi + 1, short(&c).chars().take(60).collect::<String>()));
                                continue;
                            }
                        }
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
        // the loop: from the way there, segment by segment (bridge_loop)
        if let (Some(cut), Some(h)) = (&out.cut, head) {
            covers.push(conj(&cut.pre.iter().filter(|c| !Self::bridge_param_typing(&sp, c, out.first)).cloned().collect::<Vec<_>>()));
            let cx = LoopCx { s: s.clone(), o: o.clone(), spec: spec.clone(), args: args.clone(), v: v.clone(), w: w.clone(), dfacts: dfacts.clone(), s2: s2.clone(), head: h };
            self.bridge_loop(env, p, inv, premises, &out, cut, &cx)?;
            lap("the loop");
        }
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
            // (from the compound facts only if one mentions the guard: else
            // they only make simp search)
            let mentions = |t: &Term| {
                let mut st = vec![t.clone()];
                while let Some(u) = st.pop() {
                    if u == guard {
                        return true;
                    }
                    if let Node::App(_, xs) = u.node() {
                        st.extend(xs.iter().cloned());
                    }
                }
                false
            };
            let arity = self.simp_prove_loops(env, &lean, &guard, &[]).is_ok()
                || no_run.iter().any(|t| compound(t) && mentions(t)) && self.simp_prove_loops(env, &no_run, &guard, &[]).is_ok();
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
    pub(super) fn bridge_param_typing(sp: &Simp, c: &Term, first: u32) -> bool {
        match c.node() {
            Node::App(i, ab) if is(*i, sp.s.in_) && ab.len() == 2 => {
                matches!(ab[0].node(), Node::Var(v, va) if va.is_empty() && *v >= first)
                    && matches!(ab[1].node(), Node::App(u, _) if is(*u, sp.s.univ) || Some(*u) == sp.env.sym_by_name.get("bits").copied())
            }
            _ => false,
        }
    }

    /// `abi.agree(vm0, sp, b1, b2)`, the machine's bytes b1 and the world's
    /// b2 agreeing outside the scratch area: store by store from the outside
    /// -- a store to the frame below the return address (scratch), the same
    /// byte stored on both sides -- down to bytes that agree (a fact) or are
    /// the same, each step shown by simp from the one below
    /// (`abi.agree_slot`, `abi.agree_st1`; in word forms where needed).
    /// The facts with the agreements shown.
    pub(super) fn bridge_agree(&self, env: &Env, facts: &[Term], s: &Term, b1: &Term, b2: &Term) -> Result<Vec<Term>, String> {
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| format!("needs `{}`", n));
        let (app, badd, agree, store_le) = (sym("app")?, sym("bits_add")?, sym("abi.agree")?, sym("x86_64_linux.store_le")?);
        let sp = Simp::new(env, self);
        let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
        let rsp0 = Term::app(app, vec![Term::app(app, vec![s.clone(), Term::bytes(b"gpr")]), nat(4)]);
        let spv = Term::app(badd, vec![nat(64), rsp0.clone(), nat(8)]);
        let vm0 = Term::app(app, vec![s.clone(), Term::bytes(b"vm")]);
        let words = super::spec::Words::new(&sp, self, true, facts);
        sp.set_nats(facts);
        let norm = |t: &Term| sp.term(&words.word(facts, &sp.term(t)));
        let slot = |a: &Term| match norm(a).node() {
            Node::App(g, ga) if *g == badd && ga.len() == 3 && ga[1] == rsp0 => matches!(ga[2].node(), Node::Nat(c) if *c >= crate::nat::Nat::pow2(63)),
            _ => false,
        };
        // (each layer with the instance of its lemma: abi.agree_refl at
        // (old, sp, b), abi.agree_slot at (old, b1, b2, rsp, c, n, x),
        // abi.agree_st1b at (old, sp, b1, b2, a1, a2, x, y))
        let mut goals: Vec<(Term, Vec<Term>)> = Vec::new();
        let (mut x, mut y) = (sp.term(b1), sp.term(b2));
        loop {
            let g = Term::app(agree, vec![vm0.clone(), spv.clone(), x.clone(), y.clone()]);
            if x == y {
                goals.push((g, vec![vm0.clone(), spv.clone(), x.clone()]));
                break;
            }
            match (x.node(), y.node()) {
                (Node::App(st, sa), _) if *st == store_le && sa.len() == 4 && slot(&sa[1]) => {
                    let c = match norm(&sa[1]).node() {
                        Node::App(_, ga) => ga[2].clone(),
                        _ => unreachable!(),
                    };
                    goals.push((g, vec![vm0.clone(), sa[0].clone(), y.clone(), rsp0.clone(), c, sa[2].clone(), sa[3].clone()]));
                    x = sa[0].clone();
                }
                (Node::App(st, sa), Node::App(fu, fa)) if *st == store_le && sa.len() == 4 && is(*fu, sp.s.fn_update) && fa.len() == 3 && norm(&sa[1]) == norm(&fa[1]) => {
                    goals.push((g, vec![vm0.clone(), spv.clone(), sa[0].clone(), fa[0].clone(), sa[1].clone(), fa[1].clone(), sa[3].clone(), fa[2].clone()]));
                    let (nx, ny) = (sa[0].clone(), fa[0].clone());
                    x = nx;
                    y = ny;
                }
                _ => {
                    goals.push((g, Vec::new()));
                    break;
                }
            }
        }
        let compound = |l: &Term| match l.node() {
            Node::App(c, _) => *c == env.builtins.imp || is(*c, sp.s.or) || is(*c, sp.s.and),
            _ => false,
        };
        let mut known = facts.to_vec();
        for (g, inst) in goals.into_iter().rev() {
            let g = sp.prop(&g, Pol::Other);
            if sp.is_true(&g) || known.contains(&g) {
                continue;
            }
            // (its lemma at the instance, its hypotheses shown)
            if !inst.is_empty() && self.bridge_apply(env, &sp, &known, &g, &inst) {
                known.push(g);
                continue;
            }
            // (the lemmas and literals, conjunctions split)
            let mut lean: Vec<Term> = Vec::new();
            let mut st: Vec<Term> = known.clone();
            while let Some(t) = st.pop() {
                match t.node() {
                    Node::App(c, _) if is(*c, sp.s.and) => sp.conjuncts(&t, &mut st),
                    _ if compound(&t) => {}
                    _ => {
                        if !lean.contains(&t) {
                            lean.push(t)
                        }
                    }
                }
            }
            let ok = self.simp_prove_loops(env, &lean, &g, &[]).is_ok() || {
                sp.set_nats(&known);
                let g2 = sp.prop(&words.word(&known, &g), Pol::Other);
                g2 != g && self.simp_prove_loops(env, &lean, &g2, &[]).is_ok()
            } || self.simp_prove_loops(env, &known, &g, &[]).is_ok();
            if !ok {
                let pr = crate::syntax::Printer::new(env);
                sp.set_nats(&known);
                let g2 = sp.prop(&words.word(&known, &g), Pol::Other);
                let left = if std::env::var("BRIDGE_DEBUG").is_ok() { let l2: Vec<Term> = lean.clone(); self.simp_prove_loops(env, &l2, &g2, &[]).err().map(|e| e.0).unwrap_or_default() } else { String::new() };
                return Err(format!("the bytes agree outside the frame: {} not shown (in word forms {}) {}", pr.term(&g).chars().take(600).collect::<String>(), pr.term(&g2).chars().take(600).collect::<String>(), left));
            }
            known.push(g);
        }
        Ok(known)
    }

    /// The goal by a premise `all x1 .. xk. H.. -> C` at the given k terms:
    /// C there is the goal, each H there shown (a fact, typing, or simp on
    /// the facts' lemmas and literals, in word forms too).
    pub(super) fn bridge_apply(&self, env: &Env, sp: &Simp, facts: &[Term], goal: &Term, inst: &[Term]) -> bool {
        let k = inst.len();
        let target = sp.prop(goal, Pol::Other);
        let compound = |l: &Term| match l.node() {
            Node::App(c, _) => *c == env.builtins.imp || is(*c, sp.s.or),
            _ => false,
        };
        let mut lean: Vec<Term> = Vec::new();
        let mut st: Vec<Term> = facts.to_vec();
        while let Some(t) = st.pop() {
            match t.node() {
                Node::App(c, _) if is(*c, sp.s.and) => sp.conjuncts(&t, &mut st),
                _ if compound(&t) => {}
                _ => {
                    if !lean.contains(&t) {
                        lean.push(t)
                    }
                }
            }
        }
        for l in facts {
            // (exactly k binders)
            let mut body = l.clone();
            let mut n = 0;
            while let Node::App(q, b) = body.node() {
                if *q != self.all {
                    break;
                }
                body = b[0].clone();
                n += 1;
            }
            if n != k {
                continue;
            }
            let mut t = l.clone();
            for x in inst {
                let Node::App(_, b) = t.node() else { break };
                t = inst_k(env, &b[0], &[x.clone()]);
            }
            let mut hyps = Vec::new();
            while let Node::App(i, ab) = t.node() {
                if *i != env.builtins.imp {
                    break;
                }
                hyps.push(ab[0].clone());
                t = ab[1].clone();
            }
            let words = super::spec::Words::new(sp, self, true, facts);
            if sp.prop(&t, Pol::Other) != target {
                // (or in word forms: a generic state's registers read)
                sp.set_nats(facts);
                let a = sp.prop(&words.word(facts, &t), Pol::Other);
                let b = sp.prop(&words.word(facts, &target), Pol::Other);
                if a != b {
                    continue;
                }
            }
            let ok = hyps.iter().all(|h| {
                let h = sp.prop(h, Pol::Other);
                if sp.is_true(&h) || facts.contains(&h) || sp.typed(facts, &h) || self.simp_prove_loops(env, &lean, &h, &[]).is_ok() {
                    return true;
                }
                sp.set_nats(facts);
                let h2 = sp.prop(&words.word(facts, &h), Pol::Other);
                h2 != h && (sp.is_true(&h2) || self.simp_prove_loops(env, &lean, &h2, &[]).is_ok())
            });
            if ok {
                return true;
            }
        }
        false
    }

    pub(super) fn bridge_fresh(&self, env: &Env, premises: &[Term], r: &Term) -> u32 {
        let mut fresh = env.vars.len() as u32 + 5_000_000;
        for t in premises.iter().chain([r]) {
            fresh = fresh.max(max_var(t) + 1);
        }
        fresh
    }
}
