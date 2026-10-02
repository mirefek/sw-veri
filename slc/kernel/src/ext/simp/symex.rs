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
}

impl Logic {
    /// The outcome of the run `h` (a premise `runs(abi.run_to_return(), M,
    /// O)`) by symbolic execution with the other premises: the instructions'
    /// outcome lemmas and the facts their premises need.
    pub fn symex(&self, env: &Env, premises: &[Term]) -> KResult<Term> {
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
        let imp = env.builtins.imp;
        let eq = env.builtins.eq;
        // the run, the instructions' lemmas (by address), the other facts
        let mut run: Option<(Term, Term)> = None;
        let mut lemmas: Vec<(u128, Lemma)> = Vec::new();
        let mut facts: Vec<Term> = Vec::new();
        for p in premises {
            if let Node::App(r, a) = p.node() {
                if *r == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, x) if *g == rtr && x.is_empty()) && run.is_none() {
                    run = Some((a[1].clone(), a[2].clone()));
                    continue;
                }
            }
            if let Some((addr, l)) = self.step_lemma(p, runs, step, app, eq, imp) {
                lemmas.push((addr, l));
                continue;
            }
            facts.push(p.clone());
        }
        let Some((m0, o0)) = run else { return err("no premise `runs(abi.run_to_return(), M, O)`".into()) };
        // (premises `all xs. f(xs) = rhs` unfold f, as in simp)
        *self.simp_rewrites.borrow_mut() = self.rewrite_rules(env, premises);
        let r = self.symex_run(env, &facts, &lemmas, &m0, &o0, [app, ok, empty, le, badd, code_at, eq]);
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
    fn symex_run(&self, env: &Env, facts: &[Term], lemmas: &[(u128, Lemma)], m0: &Term, o0: &Term, syms: [SymId; 7]) -> KResult<Term> {
        let [app, ok, empty, le, badd, code_at, eq] = syms;
        let err = |m: String| Err(crate::env::KernelError(format!("symex: {}", m)));
        let sp = Simp::new(env, self);
        let pr = crate::syntax::Printer::new(env);
        let short = |t: &Term| pr.term(t).chars().take(400).collect::<String>();
        // the facts, as literals
        let mut lits = Vec::new();
        for f in facts {
            sp.conjuncts(&self.simp_fact(env, f), &mut lits);
        }
        let (codes, lits): (Vec<Term>, Vec<Term>) = lits.into_iter().partition(|l| matches!(l.node(), Node::App(c, _) if *c == code_at));
        // the return: rip at the address M's rsp points to, rsp past it
        let gpr = |s: &Term, r: u64| Term::app(app, vec![Term::app(app, vec![s.clone(), Term::bytes(b"gpr")]), Term::nat(crate::nat::Nat::from_u64(r))]);
        let field = |s: &Term, k: &[u8]| Term::app(app, vec![s.clone(), Term::bytes(k)]);
        // (the entry registers' typing, where the facts give it: for arith)
        let mut lits = lits;
        if let (Some(in_), Some(bits)) = (sp.s.in_, env.sym_by_name.get("bits")) {
            for r in 0..16 {
                let t = Term::app(in_, vec![gpr(m0, r), Term::app(*bits, vec![Term::nat(crate::nat::Nat::from_u64(64))])]);
                sp.set_nats(&lits);
                if !lits.contains(&t) && sp.typed(&lits, &t) {
                    lits.push(t);
                }
            }
        }
        let ret = Term::app(le, vec![field(&field(m0, b"vm"), b"bytes"), gpr(m0, 4), Term::nat(crate::nat::Nat::from_u64(8))]);
        let sp_end = Term::app(badd, vec![Term::nat(crate::nat::Nat::from_u64(64)), gpr(m0, 4), Term::nat(crate::nat::Nat::from_u64(8))]);
        let mut fresh = env.vars.len() as u32 + 3_000_000;
        for t in facts.iter().chain([m0, o0]) {
            fresh = fresh.max(max_var(t) + 1);
        }
        let mut work = vec![XPath { state: m0.clone(), conds: Vec::new(), code: codes, vars: Vec::new() }];
        let mut done: Vec<XPath> = Vec::new();
        let mut steps = 0usize;
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
                // returned?
                let back = Term::app(sp.s.and.unwrap(), vec![Term::app(eq, vec![field(&s, b"rip"), ret.clone()]), Term::app(eq, vec![gpr(&s, 4), sp_end.clone()])]);
                match self.symex_decide(&sp, &ctx, &back) {
                    Some(true) => {
                        done.push(p);
                        break;
                    }
                    Some(false) => {}
                    None => return err(format!("whether the function has returned is not decided at the state {}", short(&s))),
                }
                // the instruction at rip
                let rip = self.symex_value(&sp, &ctx, &field(&s, b"rip"));
                let Some(addr) = (match rip.node() {
                    Node::Nat(v) => v.to_u128(),
                    _ => None,
                }) else {
                    return err(format!("rip is not known: {}", short(&rip)));
                };
                let Some((_, lem)) = lemmas.iter().find(|(a, _)| *a == addr) else {
                    return err(format!("no outcome lemma for the instruction at {:#x} (pass its `F.ok_{:x}`)", addr, addr));
                };
                let o = Term::var(fresh, vec![]);
                fresh += 1;
                let inst = |t: &Term| inst_k(env, t, &[s.clone(), o.clone()]);
                for h in &lem.hyps {
                    let h = sp.prop(&inst(h), Pol::Other);
                    if !self.symex_shows(env, &sp, &ctx, &h) {
                        return err(format!("at {:#x}: cannot show the premise {}", addr, short(&h)));
                    }
                }
                // its alternatives: decided, or paths
                let mut alts = Vec::new();
                sp.disjuncts(&inst(&lem.concl), &mut alts);
                let mut next: Vec<XPath> = Vec::new();
                for alt in alts {
                    let mut q = XPath { state: s.clone(), conds: p.conds.clone(), code: Vec::new(), vars: p.vars.clone() };
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
                            _ => match self.symex_decide(&sp, &ctx, &c) {
                                Some(true) => {}
                                Some(false) => dead = true,
                                None => q.conds.push(sp.prop(&c, Pol::Other)),
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
        // O = ok(S, empty) per path, its conditions, its open values existential
        let bf = env.binders_fn();
        let mut result: Option<Term> = None;
        for p in done.into_iter().rev() {
            let mut body = Term::app(eq, vec![o0.clone(), Term::app(ok, vec![p.state.clone(), Term::app(empty, vec![])])]);
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
    fn symex_decide(&self, sp: &Simp, ctx: &[Term], c: &Term) -> Option<bool> {
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
        self.tautology(env, &near, h).is_ok() || self.arith(env, &near, h).is_ok()
    }
}
