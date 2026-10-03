//! The bridge at a loop (proof-plan 6.3, milestone 3): the spec's loop cut
//! at its head (spec_run's cut mode), the machine's head the first address
//! a path is at twice. The way there, one iteration and the ways out are
//! segments, each machine path matched with the spec's branch, as for code
//! without loops; at the head, both sides generalized -- a machine state M
//! and a spec state L, fresh -- related by the coupling only: M at the head
//! with the ABI's registers, the thread's state and the memory's pages as
//! at entry, its bytes agreeing with L's world's outside the scratch area
//! (`abi.agree`), the spec's locals in their homes in the frame (found at
//! the first arrival: the stores of their values), the return address and
//! the code in place; and the invariant, if given, of L (a fact of the
//! spec, shown on it). Nothing about what the loop computes.
//!
//! The checks: the way to the loop arrives coupled; from any coupled pair
//! each of the iteration's branches either goes on -- the machine at the
//! head again, coupled -- or leaves, the machine then returning as the
//! program after the loop does from that way out (`while_rel(l0, .., r)`
//! a hypothesis: the spec's cut statement gives the program's outcome), or
//! raises (undefined behaviour: the program raises from the view, its world
//! chosen); the iteration's branches cover the coupled pairs, each way
//! out's branches cover it; the coupled states have the same trace. The
//! loop rule `abi.loop_sim` (an open lemma) makes these the whole loop:
//! the machine's outcome the spec's, or both diverging with the same trace.

use super::spec::{CutOut, SpecOut, Words};
use super::*;
use crate::env::KResult;
use crate::term::VarId;

/// What the bridge passes on at a loop.
pub(super) struct LoopCx {
    pub s: Term,
    pub o: Term,
    pub spec: Term,
    pub args: Term,
    pub v: Term,
    pub w: Term,
    pub dfacts: Vec<Term>,
    pub s2: Term,
    pub head: u128,
}

/// A machine path's end: a return (the final state) or the head (its state).
enum End {
    Ret(Term),
    Head(Term),
}

impl Logic {
    pub(super) fn bridge_loop(&self, env: &Env, _p: &Term, inv: Option<&Term>, premises: &[Term], out: &SpecOut, cut: &CutOut, cx: &LoopCx) -> KResult<()> {
        let kerr = |m: String| crate::env::KernelError(format!("bridge: the loop: {}", m));
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| kerr(format!("needs `{}`", n)));
        let (runs, rtr, run_from, app, empty, badd, ok, exc, pair, le, code_at, wr, agree, fst_s, snd_s, step) = (
            sym("runs")?,
            sym("abi.run_to_return")?,
            sym("abi.run_from")?,
            sym("app")?,
            sym("empty")?,
            sym("bits_add")?,
            sym("ok")?,
            sym("exc")?,
            sym("pair")?,
            sym("x86_64_linux.le")?,
            sym("abi.code_at")?,
            sym("while_rel")?,
            sym("abi.agree")?,
            sym("fst")?,
            sym("snd")?,
            sym("x86_64_linux.step")?,
        );
        let (machine_set, world, bits, fn_space, univ, store_le) =
            (sym("x86_64_linux.Machine")?, sym("abi.World")?, sym("bits")?, sym("fn_space")?, sym("univ")?, sym("x86_64_linux.store_le")?);
        let sp = Simp::new(env, self);
        let pr = crate::syntax::Printer::new(env);
        let short = |t: &Term| pr.term(t).chars().take(600).collect::<String>();
        let dbg = std::env::var("BRIDGE_DEBUG").is_ok();
        let t0 = std::time::Instant::now();
        let lap = |what: &str| {
            if dbg {
                eprintln!("bridge: loop {:8.3}s {}", t0.elapsed().as_secs_f64(), what)
            }
        };
        let in_ = sp.s.in_.unwrap();
        let eq = env.builtins.eq;
        let and = sp.s.and.unwrap();
        let conj = |cs: &[Term]| cs.iter().cloned().reduce(|a, b| Term::app(and, vec![a, b])).unwrap_or_else(|| sp.tt());
        let nat = |k: u64| Term::nat(crate::nat::Nat::from_u64(k));
        let fld = |t: &Term, k: &str| Term::app(app, vec![t.clone(), Term::bytes(k.as_bytes())]);
        let reg = |m: &Term, r: u64| Term::app(app, vec![fld(m, "gpr"), nat(r)]);
        let bf = env.binders_fn();
        let s = &cx.s;
        let rsp0 = reg(s, 4);
        let spv = Term::app(badd, vec![nat(64), rsp0.clone(), nat(8)]);
        let vm0 = fld(s, "vm");
        let hterm = Term::nat(crate::nat::Nat::from_u128(cx.head));
        let is_run = |t: &Term| match t.node() {
            Node::App(r, a) if *r == runs && a.len() == 3 => matches!(a[0].node(), Node::App(g, _) if *g == rtr),
            Node::App(r, a) => *r == run_from && a.len() == 3,
            _ => false,
        };
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
        // (t mentions the symbol f)
        let mentions = |t: &Term, f: SymId| {
            let mut st = vec![t.clone()];
            while let Some(u) = st.pop() {
                if let Node::App(g, xs) = u.node() {
                    if *g == f {
                        return true;
                    }
                    st.extend(xs.iter().cloned());
                }
            }
            false
        };
        // the lemmas and literals of facts (conjunctions split; implications
        // and alternatives left out: they split simp's paths), without the
        // spec's runs if `machine` (facts about states)
        let lean_of = |fs: &[Term], machine: bool| -> Vec<Term> {
            let mut out = Vec::new();
            let mut st: Vec<Term> = fs.to_vec();
            while let Some(t) = st.pop() {
                match t.node() {
                    Node::App(c, _) if is(*c, sp.s.and) => sp.conjuncts(&t, &mut st),
                    Node::App(c, _) if *c == env.builtins.imp || is(*c, sp.s.or) => {}
                    _ if machine && (mentions(&t, runs) || mentions(&t, wr)) => {}
                    _ => {
                        if !out.contains(&t) {
                            out.push(t)
                        }
                    }
                }
            }
            out
        };
        let plain = |fs: &[Term]| -> Vec<Term> { fs.iter().filter(|t| !is_run(t) && !is_step(t)).cloned().collect() };
        let fresh = std::cell::Cell::new(self.bridge_fresh(env, premises, &out.statement) + 1_000_000);
        let var = || {
            let v = fresh.get();
            fresh.set(v + 1);
            (v, Term::var(v, vec![]))
        };
        let u1 = Term::app(univ, vec![nat(1)]);
        let w0 = sp.term(&Term::app(fst_s, vec![cut.l0.clone()]));
        // (the code where the machine is: the premises' `code_at(vm0, ..)`)
        let codes: Vec<Term> = premises
            .iter()
            .filter_map(|t| match t.node() {
                Node::App(c, a) if *c == code_at && a.len() == 3 && a[0] == vm0 => Some(a[1..].to_vec()),
                _ => None,
            })
            .map(|a| Term::app(code_at, vec![Term::var(u32::MAX, vec![]), a[0].clone(), a[1].clone()]))
            .collect();
        // the spec's locals: snd(l0)'s leaves, with their paths
        fn leaves(t: &Term, pair: SymId, path: &mut Vec<bool>, out: &mut Vec<(Vec<bool>, Term)>) {
            match t.node() {
                Node::App(p, x) if *p == pair && x.len() == 2 => {
                    path.push(false);
                    leaves(&x[0], pair, path, out);
                    path.pop();
                    path.push(true);
                    leaves(&x[1], pair, path, out);
                    path.pop();
                }
                _ => out.push((path.clone(), t.clone())),
            }
        }
        let l0_locals = sp.term(&Term::app(snd_s, vec![cut.l0.clone()]));
        let mut locs0: Vec<(Vec<bool>, Term)> = Vec::new();
        leaves(&l0_locals, pair, &mut Vec::new(), &mut locs0);
        let local_of = |l: &Term, path: &[bool]| -> Term {
            let mut t = Term::app(snd_s, vec![l.clone()]);
            for b in path {
                t = Term::app(if *b { snd_s } else { fst_s }, vec![t]);
            }
            t
        };
        let mk_runfrom = |m: &Term, o: &Term| Term::app(run_from, vec![s.clone(), m.clone(), o.clone()]);
        // a machine run under the facts (its run among them): its paths
        let machine = |facts: &[Term], stops: &[Term], o: &Term| -> Result<Vec<(Vec<Term>, End)>, String> {
            *self.symex_simp.borrow_mut() = plain(facts);
            let r = self.symex(env, stops, facts);
            self.symex_simp.borrow_mut().clear();
            let r = r.map_err(|e| e.0)?;
            let mut ds = Vec::new();
            sp.disjuncts(&r, &mut ds);
            let mut paths = Vec::new();
            for d in ds {
                let mut body = d.clone();
                while let Node::App(q, b) = body.node() {
                    if *q != self.ex {
                        break;
                    }
                    let (_, x) = var();
                    body = inst_k(env, &b[0], &[x]);
                }
                let mut cs = Vec::new();
                sp.conjuncts(&body, &mut cs);
                let mut end = None;
                let mut conds = Vec::new();
                for c in cs {
                    match c.node() {
                        Node::App(e, ab) if *e == eq && ab[0] == *o => match ab[1].node() {
                            Node::App(k, kb) if *k == ok => end = Some(End::Ret(kb[0].clone())),
                            _ => return Err(format!("a machine path ends other than by a return: {}", short(&c))),
                        },
                        Node::App(q, b) if *q == self.ex => {
                            // (the stop: `ex o2. abi.run_from(m0, S, o2) && ..`)
                            let mut st = vec![b[0].clone()];
                            let mut found = None;
                            while let Some(u) = st.pop() {
                                if let Node::App(g, ga) = u.node() {
                                    if *g == run_from && ga.len() == 3 && ga[1].loose_depth(&bf) == 0 {
                                        found = Some(ga[1].clone());
                                        break;
                                    }
                                    st.extend(ga.iter().cloned());
                                }
                            }
                            match found {
                                Some(m2) => end = Some(End::Head(m2)),
                                None => conds.push(c.clone()),
                            }
                        }
                        _ => conds.push(c.clone()),
                    }
                }
                let Some(end) = end else { return Err("a machine path without its end".into()) };
                paths.push((conds, end));
            }
            Ok(paths)
        };
        // simp, first on the lemmas and literals
        let prove = |facts: &[Term], goal: &Term| -> Result<(), String> {
            let lean: Vec<Term> = lean_of(facts, false);
            if self.simp_prove_loops(env, &lean, goal, &[]).is_ok() {
                return Ok(());
            }
            self.simp_prove_loops(env, facts, goal, &[]).map_err(|e| e.0)
        };
        // the agreement of bytes b1 (the machine's) and b2 (the world's):
        // store by store from the outside -- a store to the slot (scratch),
        // the same byte on both sides -- to agreeing bytes, each step shown
        // by simp from the one below (abi.agree_slot, abi.agree_st1)
        let words_for = |facts: &[Term]| Words::new(&sp, self, true, facts);
        let prove_agree = |facts: &[Term], b1: &Term, b2: &Term| -> Result<(), String> { self.bridge_agree(env, facts, s, b1, b2).map(|_| ()) };
        // the homes of the locals: at the first arrival, the frame's stores
        // of their values
        let homes_of = |m0: &Term, facts: &[Term]| -> Result<Vec<(Vec<bool>, Term, u64)>, String> {
            let words = words_for(facts);
            sp.set_nats(facts);
            let norm = |t: &Term| sp.term(&words.word(facts, &sp.term(t)));
            let mut stores: Vec<(Term, u64, Term)> = Vec::new();
            let mut b = sp.term(&fld(&fld(m0, "vm"), "bytes"));
            while let Node::App(st, sa) = b.node() {
                if *st != store_le || sa.len() != 4 {
                    break;
                }
                let a = norm(&sa[1]);
                if let (Node::App(g, ga), Node::Nat(n)) = (a.node(), sa[2].node()) {
                    if *g == badd && ga.len() == 3 && ga[1] == rsp0 && matches!(ga[2].node(), Node::Nat(_)) && !stores.iter().any(|(x, _, _)| *x == a) {
                        stores.push((a.clone(), n.to_u64().unwrap_or(0), norm(&sa[3])));
                    }
                }
                b = sa[0].clone();
            }
            let mut homes = Vec::new();
            for (path, val) in &locs0 {
                let val = norm(val);
                let at: Vec<&(Term, u64, Term)> = stores.iter().filter(|(_, n, x)| *x == val && *n > 0).collect();
                match at.as_slice() {
                    [(a, n, _)] => homes.push((path.clone(), a.clone(), *n)),
                    [] => return Err(format!("no home in the frame for the spec's local {} (= {})", homes.len(), short(&val))),
                    _ => return Err(format!("more homes than one for the spec's local {} (= {}): give it one", homes.len(), short(&val))),
                }
            }
            Ok(homes)
        };
        // the coupling of a machine state m at the head and a spec state l
        let coupling = |m: &Term, l: &Term, homes: &[(Vec<bool>, Term, u64)]| -> Vec<Term> {
            let e = |a: Term, b: Term| Term::app(eq, vec![a, b]);
            let wv = Term::app(fst_s, vec![l.clone()]);
            let bm = fld(&fld(m, "vm"), "bytes");
            let bw = fld(&fld(&wv, "vm"), "bytes");
            let mut cs = vec![Term::app(in_, vec![m.clone(), Term::app(machine_set, vec![])]), e(fld(m, "rip"), hterm.clone())];
            // (its parts' typing, for simp: a machine state's)
            cs.push(Term::app(in_, vec![m.clone(), u1.clone()]));
            cs.push(Term::app(in_, vec![fld(m, "gpr"), Term::app(fn_space, vec![Term::app(sym("x86_64_linux.Reg").unwrap(), vec![]), Term::app(bits, vec![nat(64)])])]));
            cs.push(Term::app(in_, vec![fld(m, "vm"), Term::app(sym("x86_64_linux.Vm").unwrap(), vec![])]));
            cs.push(Term::app(in_, vec![fld(m, "flags"), Term::app(sym("x86_64_linux.Flags").unwrap(), vec![])]));
            for k in ["os", "fs_base", "gs_base", "cpu"] {
                cs.push(e(fld(m, k), fld(s, k)));
            }
            for k in ["pages", "stack_top", "stack_limit", "brk_start", "brk"] {
                cs.push(e(fld(&fld(m, "vm"), k), fld(&vm0, k)));
            }
            cs.push(e(reg(m, 4), rsp0.clone()));
            cs.push(Term::app(in_, vec![rsp0.clone(), Term::app(bits, vec![nat(64)])]));
            for r in [3u64, 5, 12, 13, 14, 15] {
                cs.push(e(reg(m, r), reg(s, r)));
            }
            cs.push(sp.not(Term::app(app, vec![fld(m, "flags"), Term::bytes(b"df")])));
            for c in &codes {
                cs.push(c.subst_var(u32::MAX, &fld(m, "vm"), &bf));
            }
            cs.push(e(Term::app(le, vec![bm.clone(), rsp0.clone(), nat(8)]), Term::app(le, vec![fld(&vm0, "bytes"), rsp0.clone(), nat(8)])));
            cs.push(Term::app(in_, vec![wv.clone(), u1.clone()]));
            cs.push(Term::app(in_, vec![wv.clone(), Term::app(world, vec![])]));
            for k in ["os", "fs_base", "cpu", "sp"] {
                cs.push(e(fld(&wv, k), fld(&w0, k)));
            }
            for k in ["pages", "stack_top", "stack_limit", "brk_start", "brk"] {
                cs.push(e(fld(&fld(&wv, "vm"), k), fld(&fld(&w0, "vm"), k)));
            }
            cs.push(Term::app(agree, vec![vm0.clone(), spv.clone(), bm.clone(), bw]));
            for (path, a, n) in homes {
                let x = local_of(l, path);
                cs.push(e(Term::app(le, vec![bm.clone(), a.clone(), nat(*n)]), x.clone()));
                cs.push(Term::app(in_, vec![x, Term::app(bits, vec![nat(8 * n)])]));
            }
            if let Some(i) = inv {
                cs.push(inst_k(env, i, &[l.clone()]));
            }
            cs.into_iter().map(|c| sp.prop(&c, Pol::Other)).collect()
        };
        // the coupling shown at (m, l): each fact by simp, the agreement by layers
        let show_coupling = |facts: &[Term], m: &Term, l: &Term, homes: &[(Vec<bool>, Term, u64)], what: &str| -> Result<(), String> {
            let mut known = facts.to_vec();
            sp.set_nats(&known);
            let words = words_for(&known);
            for c in coupling(m, l, homes) {
                if sp.is_true(&c) || known.contains(&c) {
                    continue;
                }
                if let Node::App(g, ga) = c.node() {
                    if *g == agree {
                        prove_agree(&known, &ga[2], &ga[3]).map_err(|e| format!("{}: {}", what, e))?;
                        known.push(c);
                        continue;
                    }
                }
                // (on the lemmas and literals: the coupling's facts are
                // about states, not the spec's alternatives)
                let lean: Vec<Term> = lean_of(&known, true);
                if let Err(e) = self.simp_prove_loops(env, &lean, &c, &[]) {
                    sp.set_nats(&known);
                    let c2 = sp.prop(&words.word(&known, &c), Pol::Other);
                    if c2 == c || self.simp_prove_loops(env, &lean, &c2, &[]).is_err() {
                        return Err(format!("{}: the coupling at {}: {}", what, short(&c), e.0));
                    }
                }
                known.push(c);
            }
            Ok(())
        };
        // a machine path the spec's conditions rule out (its conditions
        // contradict them; on the lemmas and literals)
        let infeasible = |facts: &[Term], pconds: &[Term]| -> bool {
            let mut ps: Vec<Term> = lean_of(&plain(facts), false);
            sp.set_nats(&ps);
            let words = words_for(facts);
            for c in pconds {
                ps.push(c.clone());
                ps.push(sp.prop(&words.word(facts, c), Pol::Other));
            }
            self.simp_prove_loops(env, &ps, &sp.ff(), &[]).is_ok()
        };
        // a return matched with the program's outcome O (`ok(W2, (r0, r1))`)
        // under ps: abi.matches_at's return case at (m1, W2), its open
        // values the machine's rax:rdx
        let match_ret = |ps: &[Term], m1: &Term, outcome: &Term, conds: &[Term], first: u32| -> Result<(), String> {
            let Node::App(okk, oa) = outcome.node() else { return Err(format!("the program's outcome {}", short(outcome))) };
            if *okk != ok || oa.len() != 2 {
                return Err(format!("the machine returns, the program's outcome is {}", short(outcome)));
            }
            let Node::App(pp, pv) = oa[1].node() else { return Err(format!("the program's value {}", short(&oa[1]))) };
            if *pp != pair || pv.len() != 2 {
                return Err(format!("the program's value {}", short(&oa[1])));
            }
            sp.set_nats(ps);
            let words = words_for(ps);
            let rv = |r: u64| sp.term(&reg(m1, r));
            let (rax, rdx) = (rv(0), rv(2));
            let mut sigma: Vec<(VarId, Term)> = Vec::new();
            for (x, m) in [(&pv[0], &rax), (&pv[1], &rdx)] {
                if let Node::Var(v, va) = x.node() {
                    if va.is_empty() && *v >= first && !sigma.iter().any(|(u, _)| u == v) {
                        sigma.push((*v, m.clone()));
                    }
                }
            }
            let sub = |t: &Term| sigma.iter().fold(t.clone(), |t, (v, m)| t.subst_var(*v, m, &bf));
            let w2 = sub(&oa[0]);
            let o1 = Term::app(ok, vec![m1.clone(), Term::app(empty, vec![])]);
            let Some(goal) = sp.unfold(sym("abi.matches_at").map_err(|e| e.0)?, &[cx.spec.clone(), cx.args.clone(), s.clone(), cx.v.clone(), o1]) else {
                return Err("`abi.matches_at` is not a definition".into());
            };
            let mut gds = Vec::new();
            sp.disjuncts(&goal, &mut gds);
            let case = gds.iter().find_map(|d| {
                let Node::App(q, b) = d.node() else { return None };
                if *q != self.ex {
                    return None;
                }
                match inst_k(env, &b[0], &[m1.clone()]).node() {
                    Node::App(q2, b2) if *q2 == self.ex => Some(inst_k(env, &b2[0], &[w2.clone()])),
                    _ => None,
                }
            });
            let Some(case) = case else { return Err("`abi.matches_at` has no return case".into()) };
            // (the branch's conditions at the open values: shown -- then the
            // run is the cut statement's, at them, with the loop's exit a
            // hypothesis; the return case without it)
            let mut obl: Vec<Term> = conds.iter().map(sub).collect();
            let mut cs = Vec::new();
            sp.conjuncts(&case, &mut cs);
            obl.extend(cs.into_iter().filter(|c| !matches!(c.node(), Node::App(r, _) if *r == runs)));
            let mut shown = ps.to_vec();
            for c in obl {
                let c = sp.prop(&c, Pol::Other);
                if sp.is_true(&c) || shown.contains(&c) {
                    continue;
                }
                // (a fact about the states: on the machine's facts only;
                // the spec's run: on all)
                let res = if mentions(&c, runs) {
                    prove(&shown, &c)
                } else {
                    let lean = lean_of(&shown, true);
                    self.simp_prove_loops(env, &lean, &c, &[]).map_err(|e| e.0).or_else(|e| {
                        sp.set_nats(&shown);
                        let c2 = sp.prop(&words.word(&shown, &c), Pol::Other);
                        if c2 != c && self.simp_prove_loops(env, &lean, &c2, &[]).is_ok() { Ok(()) } else { Err(e) }
                    })
                };
                if let Err(e) = res {
                    let c2 = sp.prop(&words.word(&shown, &c), Pol::Other);
                    if c2 == c || prove(&shown, &c2).is_err() {
                        return Err(format!("its return does not match, at {}: {}", short(&c), e));
                    }
                }
                shown.push(c);
            }
            Ok(())
        };
        let loop_of = |r: &Term| Term::app(wr, vec![cut.l0.clone(), cut.cond.clone(), cut.body.clone(), cut.trace.clone(), r.clone()]);
        // (an outcome from the view's world: the raise case of matches_at)
        let raise_from_view = |o: &Term| matches!(o.node(), Node::App(x, xa) if *x == exc && xa.len() == 2 && xa[0] == cx.w);
        let base: Vec<Term> = plain(&cx.dfacts).into_iter().chain([out.statement.clone()]).collect();

        // 1. the way to the loop: under its conditions, the machine to the head
        let mut efacts = cx.dfacts.clone();
        efacts.extend(cut.pre.iter().cloned());
        let words = words_for(&efacts);
        sp.set_nats(&efacts);
        for c in cut.pre.clone() {
            let c2 = sp.prop(&words.word(&efacts.clone(), &c), Pol::Other);
            if !efacts.contains(&c2) {
                efacts.push(c2);
            }
        }
        let efacts_run: Vec<Term> = efacts.iter().map(|t| if is_run(t) { Term::app(runs, vec![Term::app(rtr, vec![]), cx.s2.clone(), cx.o.clone()]) } else { t.clone() }).collect();
        let stops = vec![hterm.clone()];
        let paths = machine(&efacts_run, &stops, &cx.o).map_err(|e| kerr(format!("the way to the loop: the machine: {}", e)))?;
        lap("the way to the loop");
        let mut homes: Option<Vec<(Vec<bool>, Term, u64)>> = None;
        for (pi, (pconds, end)) in paths.iter().enumerate() {
            let End::Head(m0) = end else {
                if infeasible(&efacts, pconds) {
                    continue;
                }
                return Err(kerr(format!("the way to the loop: machine path {} ({}) returns, the spec loops", pi + 1, short(&conj(pconds)))));
            };
            let mut facts = plain(&efacts);
            facts.extend(pconds.iter().cloned());
            if homes.is_none() {
                homes = Some(homes_of(m0, &facts).map_err(|e| kerr(format!("the way to the loop: {}", e)))?);
            }
            show_coupling(&facts, m0, &cut.l0, homes.as_ref().unwrap(), &format!("the way to the loop, machine path {}", pi + 1)).map_err(kerr)?;
        }
        let homes = homes.ok_or_else(|| kerr("the way to the loop: no machine path".into()))?;
        lap("the coupling at the first arrival");

        // 2. the iteration, from a coupled pair (M, L) -- fresh
        let (_, mv) = var();
        let (_, wvv) = var();
        fn shaped(t: &Term, pair: SymId, var: &dyn Fn() -> (VarId, Term)) -> Term {
            match t.node() {
                Node::App(p, x) if *p == pair && x.len() == 2 => Term::app(pair, vec![shaped(&x[0], pair, var), shaped(&x[1], pair, var)]),
                _ => var().1,
            }
        }
        let lv = Term::app(pair, vec![wvv.clone(), shaped(&l0_locals, pair, &var)]);
        let cpl = coupling(&mv, &lv, &homes);
        let mut ifacts: Vec<Term> = premises.iter().filter(|t| !is_run(t)).cloned().collect();
        ifacts.extend(cpl.iter().cloned());
        let it = self.spec_iter(env, cut, &lv, &ifacts, fresh.get())?;
        fresh.set(fresh.get().max(it.first + 1_000_000));
        lap("the spec's iteration");
        // (the trace: the coupled states' events)
        let tr_goal = Term::app(
            eq,
            vec![inst_k(env, &cut.trace, &[lv.clone()]), Term::app(sp.s.fn_update.unwrap(), vec![Term::app(empty, vec![]), Term::bytes(b"os.events"), fld(&fld(&mv, "os"), "events")])],
        );
        prove(&ifacts, &tr_goal).map_err(|e| kerr(format!("the coupled states' traces: {}", e)))?;
        let (_, ov) = var();
        let mut icovers: Vec<Term> = Vec::new();
        for (bi, (conds, o_b, on)) in it.branches.iter().enumerate() {
            let label = |what: String| kerr(format!("the iteration's branch {} ({}): {}", bi + 1, short(&conj(conds)), what));
            let core: Vec<Term> = conds.iter().filter(|c| !Self::bridge_param_typing(&sp, c, it.first)).cloned().collect();
            icovers.push(conj(&core));
            let mut facts = ifacts.clone();
            facts.extend(conds.iter().cloned());
            let words = words_for(&facts);
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
            let run = mk_runfrom(&mv, &ov);
            if *on {
                // goes on: the machine at the head again, coupled
                let Node::App(_, oa) = o_b.node() else { unreachable!() };
                let l2 = oa[0].clone();
                let mut mf = facts.clone();
                mf.push(run.clone());
                let paths = machine(&mf, &stops, &ov).map_err(|e| label(format!("the machine: {}", e)))?;
                for (pi, (pconds, end)) in paths.iter().enumerate() {
                    let End::Head(m2) = end else {
                        if infeasible(&facts, pconds) {
                            continue;
                        }
                        return Err(label(format!("machine path {} ({}) returns, the spec goes on", pi + 1, short(&conj(pconds)))));
                    };
                    let mut f2 = plain(&facts);
                    f2.extend(pconds.iter().cloned());
                    show_coupling(&f2, m2, &l2, &homes, &format!("machine path {}", pi + 1)).map_err(label)?;
                }
                lap(&format!("iteration branch {}: on", bi + 1));
                continue;
            }
            // leaves by r: the exit it is (its parameters matched), the
            // program after the loop from there
            let Some((k, sigma0)) = cut.exits.iter().enumerate().find_map(|(k, (e, vs, _))| {
                let mut b = Vec::new();
                super::pmatch(e, o_b, vs, &mut b).then_some((k, b))
            }) else {
                return Err(label(format!("the loop leaves by {}, no way out of the cut", short(o_b))));
            };
            // (a raise of undefined behaviour: its world and value open --
            // chosen, the view's and empty)
            let free = |t: &Term| matches!(t.node(), Node::Var(v, va) if va.is_empty() && *v >= it.first);
            let mut sigma = sigma0.clone();
            let mut r = o_b.clone();
            if k == 3 {
                if let Node::App(_, ra) = o_b.node() {
                    if let (Node::App(_, sa), Node::App(_, pa)) = (ra[0].node(), ra[1].node()) {
                        let mut ch: Vec<(VarId, Term)> = Vec::new();
                        if free(&sa[0]) {
                            if let Node::Var(x, _) = sa[0].node() {
                                ch.push((*x, cx.w.clone()));
                            }
                        }
                        if free(&pa[1]) {
                            if let Node::Var(x, _) = pa[1].node() {
                                ch.push((*x, Term::app(empty, vec![])));
                            }
                        }
                        let csub = |t: &Term| ch.iter().fold(t.clone(), |t, (v, x)| t.subst_var(*v, x, &bf));
                        r = csub(&r);
                        sigma = sigma.into_iter().map(|(v, t)| (v, csub(&t))).collect();
                        for c in conds {
                            let c = sp.prop(&csub(c), Pol::Other);
                            if !facts.contains(&c) {
                                facts.push(c);
                            }
                        }
                    }
                }
            }
            let sub = |t: &Term| sigma.iter().fold(t.clone(), |t, (v, x)| t.subst_var(*v, x, &bf));
            let mut lfacts = facts.clone();
            lfacts.push(loop_of(&r));
            let mut ecovers: Vec<Term> = Vec::new();
            for (ci, (cconds, co)) in cut.exits[k].2.iter().enumerate() {
                let cconds: Vec<Term> = cconds.iter().map(|c| sp.prop(&sub(c), Pol::Other)).filter(|c| !cut.pre.contains(c)).collect();
                let co = sp.term(&sub(co));
                let ccore: Vec<Term> = cconds.iter().filter(|c| !Self::bridge_param_typing(&sp, c, out.first)).cloned().collect();
                ecovers.push(conj(&ccore));
                let clabel = |what: String| label(format!("way out {} ({}): {}", ci + 1, short(&conj(&cconds)), what));
                let mut cf = lfacts.clone();
                cf.extend(cconds.iter().cloned());
                if raise_from_view(&co) || matches!(co.node(), Node::App(x, _) if *x == exc) {
                    // the program raises: from the view (anything) -- its
                    // world and value open (undefined behaviour): the view's
                    // and empty; the branch's conditions there shown, the
                    // cut statement's instance giving the raise
                    let mut ch: Vec<(VarId, Term)> = Vec::new();
                    if let Node::App(_, xa) = co.node() {
                        for (t, val) in [(&xa[0], cx.w.clone()), (&xa[1], Term::app(empty, vec![]))] {
                            if let Node::Var(v, va) = t.node() {
                                if va.is_empty() && *v >= out.first {
                                    ch.push((*v, val));
                                }
                            }
                        }
                    }
                    let csub = |t: &Term| ch.iter().fold(t.clone(), |t, (v, x)| t.subst_var(*v, x, &bf));
                    let co2 = sp.term(&csub(&co));
                    if !raise_from_view(&co2) {
                        return Err(clabel(format!("the program raises from another world: {}", short(&co2))));
                    }
                    let mut known = plain(&cf);
                    for c in cconds.iter().filter(|c| ch.iter().any(|(v, _)| has_var(c, *v))) {
                        let c = sp.prop(&csub(c), Pol::Other);
                        if sp.is_true(&c) || known.contains(&c) {
                            continue;
                        }
                        prove(&known, &c).map_err(|e| clabel(format!("the raise's condition {}: {}", short(&c), e)))?;
                        known.push(c);
                    }
                    continue;
                }
                if matches!(co.node(), Node::App(x, _) if is(*x, sp.s.diverge)) {
                    return Err(clabel("the program diverges past the loop (not supported yet)".into()));
                }
                // the machine from M under these conditions, to its return
                let mut mf = cf.clone();
                mf.push(run.clone());
                let paths = machine(&mf, &stops, &ov).map_err(|e| clabel(format!("the machine: {}", e)))?;
                for (pi, (pconds, end)) in paths.iter().enumerate() {
                    let End::Ret(m1) = end else {
                        if infeasible(&cf, pconds) {
                            continue;
                        }
                        return Err(clabel(format!("machine path {} ({}) reaches the head, the spec leaves", pi + 1, short(&conj(pconds)))));
                    };
                    let mut ps = plain(&cf);
                    ps.push(out.statement.clone());
                    let words = words_for(&cf);
                    let stw = sp.prop(&words.word(&cf, &out.statement), Pol::Other);
                    if stw != out.statement {
                        ps.push(stw);
                    }
                    ps.extend(pconds.iter().cloned());
                    // (the world's bytes, the machine's: by layers)
                    if let Node::App(_, oa) = co.node() {
                        let mut f3 = ps.clone();
                        prove_agree(&f3, &sp.term(&fld(&fld(m1, "vm"), "bytes")), &sp.term(&fld(&fld(&oa[0], "vm"), "bytes"))).map_err(|e| clabel(format!("machine path {}: {}", pi + 1, e)))?;
                        f3.push(sp.prop(&Term::app(agree, vec![vm0.clone(), spv.clone(), sp.term(&fld(&fld(m1, "vm"), "bytes")), sp.term(&fld(&fld(&oa[0], "vm"), "bytes"))]), Pol::Other));
                        ps = f3;
                    }
                    match_ret(&ps, m1, &co, &cconds, out.first).map_err(|e| clabel(format!("machine path {}: {}", pi + 1, e)))?;
                }
            }
            // (the ways out cover this one)
            let any = ecovers.into_iter().reduce(|a, b| sp.or(a, b)).unwrap_or_else(|| sp.ff());
            prove(&plain(&lfacts).into_iter().chain([out.statement.clone()]).collect::<Vec<_>>(), &any).map_err(|e| label(format!("the program after the loop: its branches do not cover the way out: {}", e)))?;
            lap(&format!("iteration branch {}: out", bi + 1));
        }
        // the iteration's branches cover the coupled pairs
        let any = icovers.into_iter().reduce(|a, b| sp.or(a, b)).unwrap_or_else(|| sp.ff());
        prove(&ifacts, &any).map_err(|e| kerr(format!("the iteration's branches do not cover the coupled states: {}", e)))?;
        let _ = (base, eq);
        // the loop rule
        let mut u = self.simp_used.borrow_mut();
        if !u.iter().any(|m| m == "abi.loop_sim") {
            u.push("abi.loop_sim".into());
        }
        Ok(())
    }
}
