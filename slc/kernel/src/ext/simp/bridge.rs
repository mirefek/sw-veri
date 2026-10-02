//! The bridge from readable GIMPLE to machine code (part of the trusted
//! `simp` extension; proof-plan section 6.3), for code without loops:
//! `bridge(h, {app(spec, args)}, ..)` with `h: runs(abi.run_to_return(), S,
//! O)` states `abi.matches(spec, args, S, O)` (proofs/abi_bridge.core):
//! the machine's outcome O is the spec's raising, a return matching the
//! spec's ok outcome, or (not here: no loops) a divergence.
//!
//! The spec runs from the view of S's memory (`abi.view(app(S, "vm"), S)`)
//! by spec_run's machinery: its ok branches (conditions Ck, outcome
//! ok(Wk, (r0, r1))) and D, the condition whose failure makes it raise
//! from any world. For each branch, the machine runs by symex under Ck --
//! the premises its steps need that the facts do not give (a memory
//! access) shown by simp, from the premises (the library's access lemmas:
//! `g.usable_read`, `abi.slot_access`, ..) and Ck -- and for each of its
//! paths (conditions Cp, final state Sp) simp shows `abi.matches(spec,
//! args, S, ok(Sp, empty))` from the branch's run, Ck and Cp. Last, D
//! implies one of the Ck (coverage). Then O matches: if D fails, the spec
//! raises (from the view, its exception any); if D holds, some Ck holds,
//! the machine's run is one of that branch's paths, which matches.
//! No reasoning about what the function computes: each side's own
//! conditions and effects are compared.

use super::*;
use crate::env::KResult;

impl Logic {
    /// `abi.matches(spec, args, S, O)` (see the module).
    pub fn bridge(&self, env: &Env, p: &Term, premises: &[Term]) -> KResult<Term> {
        let kerr = |m: String| crate::env::KernelError(format!("bridge: {}", m));
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| kerr(format!("needs `{}`", n)));
        let (runs, rtr, app, matches, fn_update, empty, badd, ok, pair) =
            (sym("runs")?, sym("abi.run_to_return")?, sym("app")?, sym("abi.matches")?, sym("fn_update")?, sym("empty")?, sym("bits_add")?, sym("ok")?, sym("pair")?);
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
        // the view of S's memory: abi.view(app(S, "vm"), S)
        let field = |t: &Term, k: &[u8]| Term::app(app, vec![t.clone(), Term::bytes(k)]);
        let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
        let rsp = Term::app(app, vec![field(&s, b"gpr"), nat(4)]);
        let mut w = Term::app(empty, vec![]);
        for (k, v) in [
            (&b"vm"[..], field(&s, b"vm")),
            (&b"os"[..], field(&s, b"os")),
            (&b"fs_base"[..], field(&s, b"fs_base")),
            (&b"cpu"[..], field(&s, b"cpu")),
            (&b"sp"[..], Term::app(badd, vec![nat(64), rsp, nat(8)])),
        ] {
            w = Term::app(fn_update, vec![w, Term::bytes(k), v]);
        }
        // the spec's branches
        let out = self.spec_run_out(env, p, &w, &[], premises)?;
        let sp = Simp::new(env, self);
        let and = sp.s.and.unwrap();
        let conj = |cs: &[Term]| cs.iter().cloned().reduce(|a, b| Term::app(and, vec![a, b])).unwrap_or_else(|| sp.tt());
        let bf = env.binders_fn();
        // (the statement of the spec's branches, a premise for the checks)
        let mut base: Vec<Term> = premises.to_vec();
        base.push(out.statement.clone());
        let goal_of = |m1: &Term| -> Option<Term> {
            let o1 = Term::app(ok, vec![m1.clone(), Term::app(empty, vec![])]);
            sp.unfold(matches, &[spec.clone(), args.clone(), s.clone(), o1])
        };
        let mut covers: Vec<Term> = Vec::new();
        for (bi, (conds, outcome)) in out.branches.iter().enumerate() {
            // ok(Wk, (r0, r1)): a branch to match; others (a raise not merged)
            // are covered by D or not at all
            let Node::App(okk, oa) = outcome.node() else { continue };
            if *okk != ok || oa.len() != 2 || !matches!(oa[1].node(), Node::App(pp, _) if *pp == pair) {
                continue;
            }
            // (its parameters' typing dropped from the coverage: inhabited)
            let core: Vec<Term> = conds.iter().filter(|c| !Self::bridge_param_typing(&sp, c, out.first)).cloned().collect();
            covers.push(conj(&core));
            // the machine under Ck -- and D (a branch is taken only where the
            // spec is defined, D; elsewhere it raises), and the coupling of
            // the arguments: the argument registers hold args (the ABI's
            // entry, shown by simp where D gives the arity)
            let mut facts = premises.to_vec();
            facts.extend(conds.iter().cloned());
            if let Some(d) = &out.ub {
                facts.push(d.clone());
            }
            for (i, r) in [7u64, 6, 2, 1, 8, 9].iter().enumerate() {
                let reg = Term::app(app, vec![field(&s, b"gpr"), nat(*r)]);
                let arg = Term::app(app, vec![args.clone(), nat(i as u64)]);
                let e = Term::app(env.builtins.eq, vec![reg, arg]);
                let ps: Vec<Term> = facts.iter().filter(|t| !matches!(t.node(), Node::App(r2, a) if *r2 == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, _) if *g == rtr))).cloned().collect();
                if self.simp_prove_loops(env, &ps, &e, &[]).is_ok() {
                    facts.push(e);
                }
            }
            // (for simp on a step's premise: not the run itself)
            let is_run = |t: &Term| matches!(t.node(), Node::App(r, a) if *r == runs && a.len() == 3 && matches!(a[0].node(), Node::App(g, _) if *g == rtr));
            *self.symex_simp.borrow_mut() = facts.iter().filter(|t| !is_run(t)).cloned().collect();
            let r = self.symex(env, &[], &facts);
            self.symex_simp.borrow_mut().clear();
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
                let Some(goal) = goal_of(&m1) else { return Err(kerr("`abi.matches` is not a definition".into())) };
                let mut ps = facts.clone();
                ps.push(out.statement.clone());
                ps.extend(pconds.iter().cloned());
                if let Err(e) = self.simp_prove_loops(env, &ps, &goal, &[]) {
                    return Err(kerr(format!(
                        "branch {} of the spec ({}), machine path {} ({}): its return does not match: {}",
                        bi + 1,
                        short(&conj(conds)),
                        pi + 1,
                        short(&conj(&pconds)),
                        e.0
                    )));
                }
            }
        }
        let _ = &bf;
        // coverage: D (or always, without undefined behaviour) implies a branch
        let any = covers.into_iter().reduce(|a, b| sp.or(a, b)).unwrap_or_else(|| sp.ff());
        let cover = match &out.ub {
            Some(d) => Term::app(env.builtins.imp, vec![d.clone(), any]),
            None => any,
        };
        if let Err(e) = self.simp_prove_loops(env, &base, &cover, &[]) {
            return Err(kerr(format!("the spec's branches do not cover its defined cases: {}", e.0)));
        }
        // (the raise from the view: D's failure, the view in the universe)
        if out.ub.is_some() {
            let in_ = sp.s.in_.unwrap();
            let u1 = Term::app(sp.s.univ.unwrap(), vec![nat(1)]);
            if self.simp_prove_loops(env, premises, &Term::app(in_, vec![w.clone(), u1]), &[]).is_err() {
                return Err(kerr("the view of the entry is not shown in univ(1)".into()));
            }
        }
        Ok(Term::app(matches, vec![spec, args, s, o]))
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
