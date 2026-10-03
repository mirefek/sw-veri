//! Symbolic execution of machine code (part of the trusted `simp`
//! extension; proof-plan section 6.1): `symex(h, facts..)` with
//! `h: runs(abi.run_to_return(), M, O)` runs the machine from M, an
//! instruction at a time, until it returns, and states the outcome:
//!
//!   O = ok(S1, empty) || .. (one disjunct per path, its conditions and
//!   the open values it chose existential)
//!
//! `run_to_return` steps while not (rip = the return address read at M's
//! rsp and rsp = M's rsp + 8): a while loop unrolled an iteration at a
//! time, which rests on the open lemma `while_unroll` (core/loop.core),
//! recorded like `simp`'s unrolling. Each step applies the instruction's
//! outcome lemma from the facts (`F.ok_A` of `slc steps`: `all m o.
//! runs(x86_64_linux.step(), m, o) -> .. -> app(m, "rip") = A -> .. ->
//! alternatives`), instantiated with the current state: its premises are
//! shown from the facts (typing, accesses, the code in place), its
//! alternatives are decided or become paths. Only the current state, the
//! path's conditions and the code fact are kept, so a step costs the same
//! however long the run; memory is the entry memory and its stores, read
//! and ordered by `simp`'s term rules (with the facts' `x86.apart`).
//!
//! Loops (proofs/abi_loop.core): the run may also be `abi.run_from(M0, S,
//! O)`, the same loop from a state S (its exit still M0's return), and
//! `symex(h, .., {H})` stops a path that reaches the address H after a step
//! (a loop's head): its disjunct is `ex o2. abi.run_from(M0, S1, o2) &&
//! fst(o2) = fst(O) && (!(fst(O) = 2) -> o2 = O)` -- the run on from S1,
//! of O's kind, O itself unless it diverges (as `while_unroll` gives). The
//! definition of `abi.run_from` is checked against `run_to_return`'s.

use super::*;
use crate::env::KResult;
use crate::ext::seq::abstract_term;
use crate::term::VarId;

/// The definition of `abi.run_to_return` that symex implements (layers/
/// abi.sl): sp = rsp + 8, ret = the 8 bytes at rsp, then `step` while not
/// (rip = ret and rsp = sp); its outcome the state at the exit. Checked at
/// each use: another definition is refused, not run.
const RUN_TO_RETURN: &str = r#"mkprog(x0 x1. letin(bits_add(64, app(app(x0, "gpr"), 4), 8), x2. letin(x86_64_linux.le(app(app(x0, "vm"), "bytes"), app(app(x0, "gpr"), 4), 8), x3. ex x4. while_rel(pair(x0, empty), x5. true, x5 x6. (!(app(fst(x5), "rip") = x3 && app(app(fst(x5), "gpr"), 4) = x2) && bind_rel(x86_64_linux.step, fst(x5), x7 x8. x6 = ok(pair(x7, empty), empty), x7 x8. x6 = exc(pair(x7, empty), pair("raise", x8)), x7. x6 = diverge(x7))) || (!!(app(fst(x5), "rip") = x3 && app(app(fst(x5), "gpr"), 4) = x2) && x6 = exc(pair(fst(x5), empty), pair("brk", empty))), x5. fn_update(empty, "os.events", app(app(fst(x5), "os"), "events")), x4) && (((fst(x4) = 0 || (fst(x4) = 1 && fst(out_value(x4)) = "brk")) && x1 = ok(fst(out_state(x4)), empty)) || ((((fst(x4) = 1 && fst(out_value(x4)) = "ret") && x1 = ok(fst(out_state(x4)), snd(out_value(x4)))) || ((fst(x4) = 1 && fst(out_value(x4)) = "raise") && x1 = exc(fst(out_state(x4)), snd(out_value(x4))))) || (fst(x4) = 2 && x1 = diverge(snd(x4))))))))"#;

/// steps of all paths
const MAX_STEPS: usize = 200_000;
const MAX_PATHS: usize = 4096;

/// An instruction's outcome lemma: its address, its premises and its
/// conclusion under the binders `m` (BVar 1) and `o` (BVar 0).
struct Lemma {
    hyps: Vec<Term>,
    concl: Term,
}

#[derive(Clone)]
struct XPath {
    state: Term,
    conds: Vec<Term>,
    code: Vec<Term>,
    vars: Vec<VarId>,
    /// it has taken a step (a stop applies only then)
    moved: bool,
    /// the addresses it has been at (the head-finding mode)
    seen: Vec<u128>,
}

impl Logic {
    /// The outcome of the run `h` (a premise `runs(abi.run_to_return(), M,
    /// O)`) by symbolic execution with the other premises: the instructions'
    /// outcome lemmas and the facts their premises need.
    pub fn symex(&self, env: &Env, stops: &[Term], premises: &[Term]) -> KResult<Term> {
        let err = |m: String| Err(crate::env::KernelError(format!("symex: {}", m)));
        let sym = |n: &str| env.sym_by_name.get(n).copied();
        let (Some(runs), Some(rtr), Some(step), Some(app), Some(ok), Some(empty), Some(le), Some(badd), Some(code_at)) = (
            sym("runs"),
            sym("abi.run_to_return"),
            sym("x86_64_linux.step"),
            sym("app"),
            sym("ok"),
            sym("empty"),
            sym("x86_64_linux.le"),
            sym("bits_add"),
            sym("abi.code_at"),
        ) else {
            return err("needs the x86 model and the ABI layer".into());
        };
        // (the loop it runs must be the one it implements)
        match &env.syms[rtr as usize].kind {
            SymKind::Defined { params, body } if params.is_empty() && crate::syntax::Printer::new(env).term(body) == RUN_TO_RETURN => {}
            _ => return err("`abi.run_to_return` is not the definition symex implements (layers/abi.sl changed?)".into()),
        }
        // (`abi.run_from`, proofs/abi_loop.core: the same loop from another
        // state, its exit as at the entry m0)
        let run_from = sym("abi.run_from").filter(|rf| match (&env.syms[*rf as usize].kind, &env.syms[rtr as usize].kind) {
            (SymKind::Defined { params, body }, SymKind::Defined { body: rbody, .. }) if params.len() == 3 => {
                let [m0, s, o] = [params[0], params[1], params[2]].map(|v| Term::var(v, vec![]));
                expected_run_from(env, rbody, &m0, &s, &o).is_some_and(|e| e == *body)
            }
            _ => false,
        });
        let imp = env.builtins.imp;
        let eq = env.builtins.eq;
        // the run (entry, start, outcome), the instructions' lemmas (by
        // address), the other facts
        let mut run: Option<(Term, Term, Term)> = None;
        let mut lemmas: Vec<(u128, Lemma)> = Vec::new();
        let mut facts: Vec<Term> = Vec::new();
        for p in premises {
            if let Node::App(r, a) = p.node() {
                if *r == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, x) if *g == rtr && x.is_empty()) && run.is_none() {
                    run = Some((a[1].clone(), a[1].clone(), a[2].clone()));
                    continue;
                }
                if Some(*r) == run_from && a.len() == 3 && run.is_none() {
                    run = Some((a[0].clone(), a[1].clone(), a[2].clone()));
                    continue;
                }
            }
            if let Some((addr, l)) = self.step_lemma(p, runs, step, app, eq, imp) {
                lemmas.push((addr, l));
                continue;
            }
            facts.push(p.clone());
        }
        let Some((m0, s0, o0)) = run else { return err("no premise `runs(abi.run_to_return(), M, O)` or `abi.run_from(M, S, O)`".into()) };
        // the stop addresses (numerals)
        let mut stop_at = Vec::new();
        for t in stops {
            match t.node() {
                Node::Nat(v) if v.to_u128().is_some() => stop_at.push(v.to_u128().unwrap()),
                _ => return err(format!("a stop address is a numeral, not {}", crate::syntax::Printer::new(env).term(t))),
            }
        }
        if !stop_at.is_empty() && run_from.is_none() {
            return err("stopping at a loop's head needs `abi.run_from` (proofs/abi_loop.core)".into());
        }
        // (premises `all xs. f(xs) = rhs` unfold f, as in simp)
        *self.simp_rewrites.borrow_mut() = self.rewrite_rules(env, premises);
        let r = self.symex_run(env, &facts, &lemmas, (&m0, &s0, &o0), (&stop_at, run_from), [app, ok, empty, le, badd, code_at, eq]);
        self.simp_rewrites.borrow_mut().clear();
        if r.is_ok() {
            self.simp_used.borrow_mut().push("while_unroll".into());
        }
        r
    }

    /// `all m o. runs(x86_64_linux.step(), m, o) -> .. -> app(m, "rip") = A
    /// -> .. -> C`: (A, its premises and C under the two binders).
    fn step_lemma(&self, p: &Term, runs: SymId, step: SymId, app: SymId, eq: SymId, imp: SymId) -> Option<(u128, Lemma)> {
        let Node::App(a1, b1) = p.node() else { return None };
        if *a1 != self.all {
            return None;
        }
        let Node::App(a2, b2) = b1[0].node() else { return None };
        if *a2 != self.all {
            return None;
        }
        let mut hyps = Vec::new();
        let mut t = b2[0].clone();
        while let Node::App(i, ab) = t.node() {
            if *i != imp {
                break;
            }
            hyps.push(ab[0].clone());
            t = ab[1].clone();
        }
        // the first premise: a step of the machine from m to o
        let first = hyps.first()?;
        let is_step = matches!(first.node(), Node::App(r, a) if *r == runs && a.len() == 3
            && matches!(a[0].node(), Node::App(s, x) if *s == step && x.is_empty())
            && matches!(a[1].node(), Node::BVar(1)) && matches!(a[2].node(), Node::BVar(0)));
        if !is_step {
            return None;
        }
        let rip = Term::app(app, vec![Term::bvar(1), Term::bytes(b"rip")]);
        let addr = hyps.iter().find_map(|h| match h.node() {
            Node::App(e, a) if *e == eq && a[0] == rip => match a[1].node() {
                Node::Nat(v) => v.to_u128(),
                _ => None,
            },
            _ => None,
        })?;
        Some((addr, Lemma { hyps: hyps[1..].to_vec(), concl: t }))
    }

    #[allow(clippy::too_many_arguments)]
    fn symex_run(&self, env: &Env, facts: &[Term], lemmas: &[(u128, Lemma)], run: (&Term, &Term, &Term), stops: (&[u128], Option<SymId>), syms: [SymId; 7]) -> KResult<Term> {
        let (m0, s0, o0) = run;
        let (stop_at, run_from) = stops;
        let [app, ok, empty, le, badd, code_at, eq] = syms;
        let prologue = self.symex_prologue.borrow().is_some();
        let head_mode = self.symex_head.borrow().is_some();
        // (at the bridge: premises and conditions also in the word forms)
        let bridge = !self.symex_simp.borrow().is_empty();
        let err = |m: String| Err(crate::env::KernelError(format!("symex: {}", m)));
        let sp = Simp::new(env, self);
        let pr = crate::syntax::Printer::new(env);
        let short = |t: &Term| pr.term(t).chars().take(400).collect::<String>();
        // the facts, as literals
        let mut lits = Vec::new();
        for f in facts {
            sp.conjuncts(&self.simp_fact(env, f), &mut lits);
            // (a word's typing also as given: the word forms read it)
            if matches!(f.node(), Node::App(i, ab) if is(*i, sp.s.in_) && ab.len() == 2 && matches!(ab[1].node(), Node::App(b, _) if env.syms[*b as usize].name == "bits")) && !lits.contains(f) {
                lits.push(f.clone());
            }
        }
        if std::env::var("SYMEX_DEBUG").is_ok() {
            eprintln!("symex: facts with typing: {:?}", facts.iter().map(|f| short(f)).filter(|x| x.ends_with("in bits(64)") && x.len() < 60).collect::<Vec<_>>());
            eprintln!("symex: lits with typing: {:?}", lits.iter().map(|f| short(f)).filter(|x| x.ends_with("in bits(64)") && x.len() < 60).collect::<Vec<_>>());
        }
        // (M normalized: an entry state with the argument registers set)
        sp.set_nats(&lits);
        let m0 = &sp.term(m0);
        let (codes, lits): (Vec<Term>, Vec<Term>) = lits.into_iter().partition(|l| matches!(l.node(), Node::App(c, _) if *c == code_at));
        // the return: rip at the address M's rsp points to, rsp past it
        let gpr = |s: &Term, r: u64| Term::app(app, vec![Term::app(app, vec![s.clone(), Term::bytes(b"gpr")]), Term::nat(crate::nat::Nat::from_u64(r))]);
        let field = |s: &Term, k: &[u8]| Term::app(app, vec![s.clone(), Term::bytes(k)]);
        // (the entry registers' typing, where the facts give it: for arith)
        let mut lits = lits;
        if let (Some(in_), Some(bits)) = (sp.s.in_, env.sym_by_name.get("bits")) {
            for r in 0..16 {
                let t = Term::app(in_, vec![sp.term(&gpr(m0, r)), Term::app(*bits, vec![Term::nat(crate::nat::Nat::from_u64(64))])]);
                sp.set_nats(&lits);
                if !lits.contains(&t) && sp.typed(&lits, &t) {
                    lits.push(t);
                }
            }
        }
        let ret = sp.term(&Term::app(le, vec![field(&field(m0, b"vm"), b"bytes"), gpr(m0, 4), Term::nat(crate::nat::Nat::from_u64(8))]));
        let sp_end = sp.term(&Term::app(badd, vec![Term::nat(crate::nat::Nat::from_u64(64)), gpr(m0, 4), Term::nat(crate::nat::Nat::from_u64(8))]));
        let mut fresh = env.vars.len() as u32 + 3_000_000;
        for t in facts.iter().chain([m0, s0, o0]) {
            fresh = fresh.max(max_var(t) + 1);
        }
        let mut work = vec![XPath { state: s0.clone(), conds: Vec::new(), code: codes, vars: Vec::new(), moved: false, seen: Vec::new() }];
        let mut done: Vec<XPath> = Vec::new();
        // (paths at a stop address, after a step at least)
        let mut stopped: Vec<XPath> = Vec::new();
        let mut steps = 0usize;
        // (time in: the word forms, premises shown, conditions decided, the return decided)
        let mut prof = [0f64; 4];
        let words = super::spec::Words::new(&sp, self, true, &self.symex_simp.borrow());
        let mut words_conds: Vec<Term> = Vec::new();
        // (at the bridge: the literals also in the word forms -- as the
        // conditions and premises are compared)
        if bridge {
            sp.set_nats(&lits);
            let base = lits.clone();
            for l in &base {
                if l.loose_depth(&env.binders_fn()) == 0 && !matches!(l.node(), Node::App(q, _) if *q == self.all) {
                    let l2 = sp.prop(&words.word(&base, l), Pol::Other);
                    if !lits.contains(&l2) && !sp.is_true(&l2) {
                        lits.push(l2);
                    }
                }
            }
            words.memo.borrow_mut().clear();
        }
        while let Some(mut p) = work.pop() {
            loop {
                steps += 1;
                if steps > MAX_STEPS {
                    return err(format!("more than {} steps", MAX_STEPS));
                }
                let ctx: Vec<Term> = lits.iter().chain(&p.conds).chain(&p.code).cloned().collect();
                sp.set_nats(&ctx);
                let s = sp.term(&p.state);
                p.state = s.clone();
                // (premises and conditions in the word forms the path bounds,
                // as the spec computes them: where the two are compared --
                // remembered while the path's conditions stay)
                if words_conds != p.conds {
                    words.memo.borrow_mut().clear();
                    words_conds = p.conds.clone();
                }
                // returned?
                // (rip and rsp as the path's equalities give them: a state at a
                // loop's head, its registers known by the coupling)
                let back = Term::app(sp.s.and.unwrap(), vec![Term::app(eq, vec![self.symex_value(&sp, &ctx, &field(&s, b"rip")), ret.clone()]), Term::app(eq, vec![{
                    let r = self.symex_value(&sp, &ctx, &gpr(&s, 4));
                    ctx.iter().find_map(|l| match l.node() {
                        Node::App(e, ab) if *e == eq && ab.len() == 2 && ab[0] == r => Some(ab[1].clone()),
                        _ => None,
                    }).unwrap_or(r)
                }, sp_end.clone()])]);
                let tq = std::time::Instant::now();
                let mut back_d = self.symex_decide(&sp, &ctx, &back);
                // (at the bridge: also in the word forms, the coupling's values read)
                if back_d.is_none() && bridge {
                    sp.set_nats(&ctx);
                    let b2 = sp.prop(&words.word(&ctx, &back), Pol::Other);
                    back_d = if sp.is_false(&b2) { Some(false) } else if sp.is_true(&b2) { Some(true) } else { self.symex_decide(&sp, &ctx, &b2) };
                }
                prof[3] += tq.elapsed().as_secs_f64();
                match back_d {
                    Some(true) if prologue => return self.prologue_end(&s, &sp),
                    Some(true) => {
                        done.push(p);
                        break;
                    }
                    Some(false) => {}
                    None => {
                        let rel: Vec<String> = ctx.iter().map(|l| short(l)).filter(|x| x.contains("\"gpr\"), 4)") && x.len() < 200).collect();
                        sp.set_nats(&ctx);
                        let b2 = sp.prop(&words.word(&ctx, &back), Pol::Other);
                        return err(format!("whether the function has returned is not decided at the state {} ({}; in word forms {}); about rsp: {:?}", short(&s), short(&sp.prop(&back, Pol::Other)), short(&b2), rel));
                    }
                }
                // the instruction at rip
                let rip = self.symex_value(&sp, &ctx, &field(&s, b"rip"));
                let Some(addr) = (match rip.node() {
                    Node::Nat(v) => v.to_u128(),
                    _ => None,
                }) else {
                    return err(format!("rip is not known: {}", short(&rip)));
                };
                // (the head-finding mode: the first address a path is at twice)
                if head_mode {
                    if p.seen.contains(&addr) {
                        *self.symex_head.borrow_mut() = Some(Some(addr));
                        return Ok(sp.tt());
                    }
                    p.seen.push(addr);
                }
                // a stop: the run from here
                if p.moved && stop_at.contains(&addr) {
                    stopped.push(p);
                    break;
                }
                let Some((_, lem)) = lemmas.iter().find(|(a, _)| *a == addr) else {
                    return err(format!("no outcome lemma for the instruction at {:#x} (pass its `F.ok_{:x}`)", addr, addr));
                };
                let o = Term::var(fresh, vec![]);
                fresh += 1;
                let inst = |t: &Term| inst_k(env, t, &[s.clone(), o.clone()]);
                // (the prologue: up to an access other than at the entry's rsp)
                if prologue {
                    let rsp0 = sp.term(&gpr(m0, 4));
                    if lem.hyps.iter().any(|h| self.data_access(env, &sp.prop(&inst(h), Pol::Other), &rsp0)) {
                        return self.prologue_end(&s, &sp);
                    }
                }
                // (finding the head: exploring only, nothing shown)
                let mut dead_path = false;
                for h in lem.hyps.iter().filter(|_| !head_mode) {
                    // (as stated; at the bridge, else in the word forms)
                    let h0 = sp.prop(&inst(h), Pol::Other);
                    let tq = std::time::Instant::now();
                    let mut shown = self.symex_shows(env, &sp, &ctx, &h0);
                    prof[1] += tq.elapsed().as_secs_f64();
                    let mut h = h0.clone();
                    if !shown && bridge {
                        let tq = std::time::Instant::now();
                        h = sp.prop(&words.word(&ctx, &h0), Pol::Other);
                        prof[0] += tq.elapsed().as_secs_f64();
                        let tq = std::time::Instant::now();
                        shown = h != h0 && self.symex_shows(env, &sp, &ctx, &h);
                        if std::env::var("SYMEX_DEBUG").is_ok() {
                            let ty = ctx.iter().filter(|l| short(l).contains("in bits(64)")).map(|l| short(l)).collect::<Vec<_>>();
                            eprintln!("symex: word form ({}): {}\n  typings: {:?}", if shown { "shown" } else { "not shown" }, short(&h), ty);
                        }
                        prof[1] += tq.elapsed().as_secs_f64();
                    }
                    if !shown {
                        // (at the bridge: a path its conditions rule out --
                        // they contradict the facts -- is not taken)
                        if bridge {
                            // (not a variable's definition `x = t`: simp would put t
                            // for x, the conditions' arithmetic lost in it)
                            let defn = |l: &Term| matches!(l.node(), Node::App(e, ab) if *e == eq && ab.len() == 2 && matches!(ab[0].node(), Node::Var(_, a) if a.is_empty()));
                            // (the literals about the conditions' variables only)
                            let mut cvs = Vec::new();
                            for c in &p.conds {
                                c.vars(&mut cvs);
                            }
                            let near_c = |l: &Term| { let mut lv = Vec::new(); l.vars(&mut lv); lv.iter().any(|v| cvs.contains(v)) };
                            let mut ps: Vec<Term> = ctx.iter().filter(|l| near_c(l) && !defn(l) && !matches!(l.node(), Node::App(q, _) if *q == self.all || *q == env.builtins.imp || is(*q, sp.s.or))).cloned().collect();
                            sp.set_nats(&ctx);
                            for c in &p.conds {
                                ps.push(sp.prop(&words.word(&ctx, c), Pol::Other));
                            }
                            crate::ext::arith::BRANCH.store(true, std::sync::atomic::Ordering::Relaxed);
                            let dead = self.simp_prove_loops(env, &ps, &sp.ff(), &[]);
                            crate::ext::arith::BRANCH.store(false, std::sync::atomic::Ordering::Relaxed);
                            match dead {
                                Ok(()) => {
                                    dead_path = true;
                                    break;
                                }
                                Err(e) if std::env::var("SYMEX_DEBUG").is_ok_and(|v| v == "3") => {
                                    eprintln!("symex: the path is not ruled out: {}", e.0);
                                }
                                Err(_) => {}
                            }
                        }
                        return err(format!("at {:#x}: cannot show the premise {}", addr, short(&h)));
                    }
                }
                if dead_path {
                    break;
                }
                // its alternatives: decided, or paths
                let mut alts = Vec::new();
                sp.disjuncts(&inst(&lem.concl), &mut alts);
                let mut next: Vec<XPath> = Vec::new();
                for alt in alts {
                    let mut q = XPath { state: s.clone(), conds: p.conds.clone(), code: Vec::new(), vars: p.vars.clone(), moved: true, seen: p.seen.clone() };
                    // (values the model leaves open: fresh, existential in the result)
                    let mut body = alt;
                    while let Node::App(x, b) = body.node() {
                        if *x != self.ex {
                            break;
                        }
                        let v = Term::var(fresh, vec![]);
                        q.vars.push(fresh);
                        fresh += 1;
                        body = inst_k(env, &b[0], &[v]);
                    }
                    let mut cs = Vec::new();
                    sp.conjuncts(&body, &mut cs);
                    let mut out: Option<Term> = None;
                    let mut fault: Option<Term> = None;
                    let mut dead = false;
                    for c in cs {
                        match c.node() {
                            Node::App(e, ab) if *e == eq && ab[0] == o => {
                                if let Node::App(k, kb) = ab[1].node() {
                                    if *k == ok {
                                        out = Some(kb[0].clone());
                                        continue;
                                    }
                                }
                                // (an outcome other than ok -- a fault --
                                // cannot be left out unless its conditions
                                // fail: checked below)
                                fault = Some(c.clone());
                            }
                            Node::App(k, _) if *k == code_at => q.code.push(sp.prop(&c, Pol::Other)),
                            _ => match { let tq = std::time::Instant::now(); let mut d = self.symex_decide(&sp, &ctx, &c); if d.is_none() && bridge { sp.set_nats(&ctx); let c2 = sp.prop(&words.word(&ctx, &c), Pol::Other); d = if sp.is_true(&c2) { Some(true) } else if sp.is_false(&c2) { Some(false) } else { self.symex_decide(&sp, &ctx, &c2) }; if d.is_none() && std::env::var("SYMEX_DEBUG").is_ok_and(|v| v == "3") { eprintln!("symex: at {:#x} undecided: {}\n  as {}", addr, short(&c), pr.term(&c2)); for l in ctx.iter().filter(|l| short(l).contains("int_lt(31")) { eprintln!("  ctx: {}", short(l)); } } } prof[2] += tq.elapsed().as_secs_f64(); d } {
                                Some(true) => {}
                                Some(false) => dead = true,
                                None => q.conds.push(if bridge { sp.prop(&words.word(&ctx, &sp.prop(&c, Pol::Other)), Pol::Other) } else { sp.prop(&c, Pol::Other) }),
                            },
                        }
                        if dead {
                            break;
                        }
                    }
                    if dead {
                        continue;
                    }
                    if let Some(f) = fault {
                        return err(format!("at {:#x}: the outcome lemma allows {}; only `ok` outcomes are followed", addr, short(&f)));
                    }
                    let Some(n) = out else { return err(format!("at {:#x}: an alternative without an outcome", addr)) };
                    q.state = n;
                    next.push(q);
                }
                match next.len() {
                    0 => return err(format!("at {:#x}: no alternative of the outcome lemma holds", addr)),
                    n if n > 1 && prologue => return self.prologue_end(&s, &sp),
                    1 => p = next.pop().unwrap(),
                    _ => {
                        p = next.pop().unwrap();
                        work.extend(next);
                        if work.len() + done.len() > MAX_PATHS {
                            return err(format!("more than {} paths", MAX_PATHS));
                        }
                    }
                }
            }
        }
        if std::env::var("SYMEX_DEBUG").is_ok() {
            eprintln!("symex: {} steps; words {:.3}s, premises {:.3}s, conditions {:.3}s, returns {:.3}s", steps, prof[0], prof[1], prof[2], prof[3]);
        }
        // O = ok(S, empty) per path, its conditions, its open values existential
        let bf = env.binders_fn();
        let mut result: Option<Term> = None;
        // (a stopped path: `ex o2. abi.run_from(m0, S, o2) && fst(o2) =
        // fst(O) && (!(fst(O) = 2) -> o2 = O)` -- the run on from S, with O's
        // outcome; a divergence's trace may differ, as in `while_unroll`)
        let n_done = done.len();
        let paths: Vec<(bool, XPath)> = done.into_iter().map(|p| (false, p)).chain(stopped.into_iter().map(|p| (true, p))).collect();
        if paths.len() > n_done && std::env::var("SYMEX_DEBUG").is_ok() {
            eprintln!("symex: {} paths returned, {} stopped", n_done, paths.len() - n_done);
        }
        for (stop, p) in paths.into_iter().rev() {
            let mut body = if stop {
                let fst = |t: &Term| Term::app(sp.s.fst.unwrap(), vec![t.clone()]);
                let o2 = Term::bvar(0);
                let o0s = o0.shift(1, 0, &bf);
                let st = p.state.shift(1, 0, &bf);
                let m0s = m0.shift(1, 0, &bf);
                let two = Term::nat(crate::nat::Nat::from_u64(2));
                let rf = Term::app(run_from.unwrap(), vec![m0s, st, o2.clone()]);
                let same = Term::app(eq, vec![fst(&o2), fst(&o0s)]);
                let div = Term::app(sp.s.not.unwrap(), vec![Term::app(eq, vec![fst(&o0s), two])]);
                let eqo = Term::app(env.builtins.imp, vec![div, Term::app(eq, vec![o2, o0s])]);
                let and = sp.s.and.unwrap();
                Term::app(self.ex, vec![Term::app(and, vec![rf, Term::app(and, vec![same, eqo])])])
            } else {
                Term::app(eq, vec![o0.clone(), Term::app(ok, vec![p.state.clone(), Term::app(empty, vec![])])])
            };
            // (an open value overwritten later: its choice dropped, it is
            // only `v = false || v = true` of a value nothing else mentions)
            let conds: Vec<&Term> = p
                .conds
                .iter()
                .enumerate()
                .filter(|(i, c)| {
                    let mut vs = Vec::new();
                    c.vars(&mut vs);
                    let mut ds = Vec::new();
                    sp.disjuncts(c, &mut ds);
                    let choice = sp.const_choice(&ds) && vs.iter().all(|v| p.vars.contains(v));
                    let used = vs.iter().any(|v| has_var(&p.state, *v) || p.conds.iter().enumerate().any(|(j, d)| j != *i && has_var(d, *v)));
                    !(choice && !used)
                })
                .map(|(_, c)| c)
                .collect();
            for c in conds.into_iter().rev() {
                body = Term::app(sp.s.and.unwrap(), vec![c.clone(), body]);
            }
            // (a stopped path: also the code where its state is, for a
            // loop's next iteration)
            if stop {
                for c in p.code.iter().rev() {
                    body = Term::app(sp.s.and.unwrap(), vec![c.clone(), body]);
                }
            }
            for v in p.vars.iter().rev() {
                if has_var(&body, *v) {
                    body = Term::app(self.ex, vec![abstract_term(&body, &Term::var(*v, vec![]), 0, &bf)]);
                }
            }
            result = Some(match result {
                None => body,
                Some(r) => Term::app(sp.s.or.unwrap(), vec![body, r]),
            });
        }
        result.ok_or_else(|| crate::env::KernelError("symex: no path returns".into()))
    }

    /// A term's value: as simp computes it, or the value an equation of the
    /// context gives it (`app(m, "rip") = A`).
    fn symex_value(&self, sp: &Simp, ctx: &[Term], t: &Term) -> Term {
        let v = sp.term(t);
        if matches!(v.node(), Node::Nat(_)) {
            return v;
        }
        for l in ctx {
            if let Node::App(e, ab) = l.node() {
                if *e == sp.s.eq && ab[0] == v && matches!(ab[1].node(), Node::Nat(_)) {
                    return ab[1].clone();
                }
            }
        }
        v
    }

    /// A condition decided in the context: by simp, a literal (or its
    /// negation), or taut / arith from the literals about it.
    /// The prologue's end at the state s: kept for the bridge (the run's
    /// statement is not made: `true`)
    fn prologue_end(&self, s: &Term, sp: &Simp) -> KResult<Term> {
        *self.symex_prologue.borrow_mut() = Some(Some(s.clone()));
        Ok(sp.tt())
    }

    /// t accesses memory (`x86_64_linux.can_access(vm, A, k)`) at an A
    /// not computed from the entry's rsp
    fn data_access(&self, env: &Env, t: &Term, rsp0: &Term) -> bool {
        let mentions = |t: &Term| {
            let mut st = vec![t.clone()];
            while let Some(u) = st.pop() {
                if u == *rsp0 {
                    return true;
                }
                if let Node::App(_, xs) = u.node() {
                    st.extend(xs.iter().cloned());
                }
            }
            false
        };
        let mut st = vec![t.clone()];
        while let Some(u) = st.pop() {
            if let Node::App(g, xs) = u.node() {
                if xs.len() == 3 && env.syms[*g as usize].name == "x86_64_linux.can_access" && !mentions(&xs[1]) {
                    return true;
                }
                st.extend(xs.iter().cloned());
            }
        }
        false
    }

    pub(super) fn symex_decide(&self, sp: &Simp, ctx: &[Term], c: &Term) -> Option<bool> {
        let c = sp.prop(c, Pol::Other);
        if sp.is_true(&c) {
            return Some(true);
        }
        if sp.is_false(&c) {
            return Some(false);
        }
        let not = |t: &Term| Term::app(sp.s.not.unwrap(), vec![t.clone()]);
        let near = relevant(ctx, &c);
        let env = sp.env;
        if ctx.contains(&c) || self.tautology(env, &near, &c).is_ok() || self.arith(env, &near, &c).is_ok() {
            return Some(true);
        }
        let nc = sp.prop(&not(&c), Pol::Other);
        if ctx.contains(&nc) || self.tautology(env, &near, &nc).is_ok() || self.arith(env, &near, &nc).is_ok() {
            return Some(false);
        }
        None
    }

    /// A premise of an instruction's lemma shown from the context: simp,
    /// typing, a literal or an instance of one, a fact `A -> h` with A
    /// shown, taut / arith.
    fn symex_shows(&self, env: &Env, sp: &Simp, ctx: &[Term], h: &Term) -> bool {
        if sp.is_true(h) || ctx.contains(h) || sp.typed(ctx, h) || sp.instance_of_all(ctx, h) {
            return true;
        }
        for l in ctx {
            if let Node::App(i, ab) = l.node() {
                if *i == env.builtins.imp && (ab[1] == *h || sp.instance_of_all(&ab[1..], h)) && self.symex_decide(sp, ctx, &ab[0]) == Some(true) {
                    return true;
                }
            }
        }
        let near = relevant(ctx, h);
        if self.tautology(env, &near, h).is_ok() || self.arith(env, &near, h).is_ok() {
            return true;
        }
        // (by simp, from the premises the bridge gives -- with the path's
        // literals: the state is the same)
        let extra = self.symex_simp.borrow().clone();
        if !extra.is_empty() {
            // (the registers' typing symex adds left out: simp has it from
            // the machine's, and as literals it would bind a lemma's word
            // variables to registers)
            let reg_typing = |l: &Term| match l.node() {
                Node::App(i, ab) if is(*i, sp.s.in_) && ab.len() == 2 => matches!(ab[0].node(), Node::App(a, x) if is(*a, sp.s.app) && x.len() == 2
                    && matches!(x[0].node(), Node::App(a2, y) if is(*a2, sp.s.app) && y.len() == 2 && matches!(y[1].node(), Node::Bytes(b) if &b[..] == b"gpr"))),
                _ => false,
            };
            // (the lemmas and literals: compound facts -- D's implications,
            // a branch's alternatives -- would only split simp's paths; an
            // implication whose antecedent the path decides gives its
            // consequent, a conjunction its conjuncts)
            let mut ps: Vec<Term> = Vec::new();
            let mut st: Vec<Term> = extra.into_iter().chain(ctx.iter().filter(|l| !reg_typing(l)).cloned()).collect();
            while let Some(l) = st.pop() {
                match l.node() {
                    Node::App(c, ab) if *c == env.builtins.imp => {
                        if self.symex_decide(sp, ctx, &ab[0]) == Some(true) {
                            st.push(ab[1].clone());
                        }
                    }
                    Node::App(c, _) if is(*c, sp.s.and) => sp.conjuncts(&l, &mut st),
                    Node::App(c, _) if is(*c, sp.s.or) => {}
                    _ => {
                        if !ps.contains(&l) {
                            ps.push(l);
                        }
                    }
                }
            }
            let t0 = std::time::Instant::now();
            let r = self.simp_prove_loops(env, &ps, h, &[]);
            if std::env::var("SYMEX_DEBUG").is_ok() {
                let pr = crate::syntax::Printer::new(env);
                eprintln!("symex: premise by simp ({:.3}s, {}): {}", t0.elapsed().as_secs_f64(), if r.is_ok() { "ok" } else { "failed" }, pr.term(h).chars().take(200).collect::<String>());
            }
            if let (Err(e), true) = (&r, std::env::var("SYMEX_DEBUG").is_ok_and(|v| v == "2")) {
                eprintln!("symex: premise by simp failed: {}", e.0);
            }
            return r.is_ok();
        }
        false
    }
}

/// What `abi.run_from(m0, s, o)` must be: `run_to_return`'s relation at
/// (m0, o) -- `mkprog(x0 x1. letin(sp, x2. letin(ret, x3. ex x4.
/// while_rel(pair(x0, empty), ..) && ..)))` with its lets taken -- with the
/// loop started at `pair(s, empty)` instead of `pair(m0, empty)`.
fn expected_run_from(env: &Env, rbody: &Term, m0: &Term, s: &Term, o: &Term) -> Option<Term> {
    let sym = |n: &str| env.sym_by_name.get(n).copied();
    let (mkprog, letin, pair, empty) = (sym("mkprog")?, sym("letin")?, sym("pair")?, sym("empty")?);
    let Node::App(mk, rel) = rbody.node() else { return None };
    if *mk != mkprog || rel.len() != 1 {
        return None;
    }
    let mut t = inst_k(env, &rel[0], &[m0.clone(), o.clone()]);
    for _ in 0..2 {
        let Node::App(l, la) = t.node() else { return None };
        if *l != letin || la.len() != 2 {
            return None;
        }
        t = inst_k(env, &la[1], &[la[0].clone()]);
    }
    let e = Term::app(empty, vec![]);
    let start = Term::app(pair, vec![m0.clone(), e.clone()]);
    let body = abstract_term(&t, &start, 0, &env.binders_fn());
    Some(inst_k(env, &body, &[Term::app(pair, vec![s.clone(), e])]))
}
