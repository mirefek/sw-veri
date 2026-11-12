//! `run_steps(STOP, STEP)` (in `by`): a program's run on concrete data, one
//! step at a time, each step its own fact. The goal is `ex x. C(.., m0, x)`;
//! the lemmas say
//!
//!   STOP: `all .. m. A1(m) -> .. -> C(.., m, m)`              (the run ends)
//!   STEP: `all .. m m1 v x. N1(m) -> .. -> runs(P, m, ok(m1, v)) ->
//!          C(.., m1, x) -> C(.., m, x)`                       (a step first)
//!
//! From m0: STOP's premises evaluated at the current state; if they hold,
//! the run ends there, else STEP's side premises are evaluated, the step's
//! outcome is found by evaluation (a witness, no theorem) and `runs(P, m,
//! ok(m1, v))` is kernel-checked by evaluation -- its loops the step's own,
//! not the run's. The facts are then joined from the end: STOP at the last
//! state, STEP back to m0, the goal by its witness.

use super::*;
use std::collections::HashMap;

/// the steps a run may take (each one evaluated)
const MAX_STEPS: usize = 100_000;

/// A lemma opened: its variables (fresh, in binder order), premises,
/// conclusion.
struct Opened {
    vars: Vec<VarId>,
    prems: Vec<Term>,
    concl: Term,
}

fn open(env: &mut Env, lg: &Logic, s: &Seq, tag: &str) -> KResult<Opened> {
    let mut s = s.clone();
    let mut vars = Vec::new();
    while matches!(s.concl().node(), Node::App(a, _) if *a == lg.all) {
        let v = env.new_var(&format!("rs_{}{}", tag, vars.len()), 0);
        s = Seq::all_elim(env, lg, &s, &Term::var(v, vec![]))?;
        vars.push(v);
    }
    let mut prems = Vec::new();
    let mut c = s.concl().clone();
    while let Node::App(i, a) = c.node() {
        if *i != lg.imp {
            break;
        }
        prems.push(a[0].clone());
        c = a[1].clone();
    }
    Ok(Opened { vars, prems, concl: c })
}

/// p matches t, the variables `vs` of p bound in `sub`
fn pmatch(p: &Term, t: &Term, vs: &[VarId], sub: &mut HashMap<VarId, Term>) -> bool {
    if let Node::Var(v, a) = p.node() {
        if a.is_empty() && vs.contains(v) {
            return match sub.get(v) {
                Some(x) => x == t,
                None => {
                    sub.insert(*v, t.clone());
                    true
                }
            };
        }
    }
    match (p.node(), t.node()) {
        (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => a.iter().zip(b).all(|(x, y)| pmatch(x, y, vs, sub)),
        _ => p == t,
    }
}

fn subst(env: &Env, t: &Term, sub: &HashMap<VarId, Term>) -> Term {
    let bf = env.binders_fn();
    sub.iter().fold(t.clone(), |t, (v, x)| t.subst_var(*v, x, &bf))
}

/// the lemma `s` at the values of its variables (in order), its premises
/// discharged by `ps` (in order)
fn instance(env: &Env, lg: &Logic, s: &Seq, vals: &[Term], ps: &[&Seq]) -> KResult<Seq> {
    let mut r = s.clone();
    for v in vals {
        r = Seq::all_elim(env, lg, &r, v)?;
    }
    for p in ps {
        r = Seq::mp(env, &r, p)?;
    }
    Ok(r)
}

/// one step taken: the next state, the step's value, the side premises'
/// proofs, the run's proof
struct Taken {
    m1: Term,
    v: Term,
    side: Vec<Seq>,
    run: Seq,
}

impl State {
    pub(crate) fn run_steps(&self, env: &mut Env, lg: &Logic, goal: &Term, args: &[Arg]) -> KResult<Seq> {
        let name = |a: &Arg| match a {
            Arg::Proof(PE::Ref(n)) => Ok(n.clone()),
            _ => err("run_steps(STOP, STEP): two lemmas' names"),
        };
        let [a_stop, a_step, more @ ..] = args else { return err("run_steps(STOP, STEP, L..): lemmas' names") };
        let (stop, step) = (self.fact(env, &name(a_stop)?)?, self.fact(env, &name(a_step)?)?);
        // (L..: premises of every evaluation -- a loop's outcome by its
        // lemma, `all xs. A -> runs(Q, S, O)`)
        let extra: Vec<Seq> = more.iter().map(|a| self.fact(env, &name(a)?)).collect::<KResult<_>>()?;
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| KernelError(format!("run_steps: no `{}`", n)));
        let (runs, okc) = (sym("runs")?, sym("ok")?);
        // the goal: ex x. C(.., m0, x)
        let body = match goal.node() {
            Node::App(e, a) if *e == lg.ex => a[0].clone(),
            _ => return err(format!("run_steps: the goal is not `ex x. ..`: `{}`", Printer::new(env).short(goal))),
        };
        let xv = env.new_var("rs_x", 0);
        let bx = env.instantiate_params_m(&body, &[Term::var(xv, vec![])]);
        // STEP opened: its run premise `runs(P, m, ok(m1, v))`, its
        // continuation C(.., m1, x), the rest side premises
        let st = open(env, lg, &step, "s")?;
        let var_of = |t: &Term| match t.node() {
            Node::Var(v, a) if a.is_empty() && st.vars.contains(v) => Some(*v),
            _ => None,
        };
        let mut run_ix = None;
        for (i, q) in st.prems.iter().enumerate() {
            if let Node::App(r, a) = q.node() {
                if *r == runs && a.len() == 3 {
                    if let Node::App(o, b) = a[2].node() {
                        if *o == okc && var_of(&a[1]).is_some() && var_of(&b[0]).is_some() && var_of(&b[1]).is_some() {
                            run_ix = Some((i, var_of(&a[1]).unwrap(), var_of(&b[0]).unwrap(), var_of(&b[1]).unwrap(), a[0].clone()));
                        }
                    }
                }
            }
        }
        let Some((run_ix, vm, vm1, vv, prog)) = run_ix else { return err("run_steps: STEP has no premise `runs(P, m, ok(m1, v))`") };
        // the goal's instance of STEP's conclusion: the state m0, the end x,
        // the other variables (not the step's own)
        let mut sub = HashMap::new();
        if !pmatch(&st.concl, &bx, &st.vars, &mut sub) {
            let p = Printer::new(env);
            return err(format!("run_steps: the goal `{}` is not STEP's conclusion `{}`", p.short(&bx), p.short(&st.concl)));
        }
        let Some(m0) = sub.remove(&vm) else { return err("run_steps: STEP's conclusion has no state") };
        let vx = st.vars.iter().copied().find(|v| sub.get(v).is_some_and(|t| matches!(t.node(), Node::Var(w, _) if *w == xv)));
        let Some(vx) = vx else { return err("run_steps: the goal's witness is not STEP's end") };
        sub.remove(&vx);
        let fixed = sub; // (the other variables: the goal's)
        let cont_ix = st.prems.iter().position(|q| q.has_var(vm1) && q.has_var(vx)).ok_or_else(|| KernelError("run_steps: STEP has no continuation premise".into()))?;
        let prog = subst(env, &prog, &fixed);
        let sp = open(env, lg, &stop, "t")?;
        // STOP at state m (its conclusion STEP's with x = m): its proof, if
        // its premises evaluate true
        let envm = env;
        let env: &Env = &*envm;
        // (the evaluations share memos: the states share most of their parts)
        let known: Vec<Term> = extra.iter().map(|s| s.concl().clone()).collect();
        let xs: Vec<&Seq> = extra.iter().collect();
        let mut ses = lg.eval_session(env, &known);
        let try_stop = |ses: &mut sl_kernel::ext::simp::EvalSession, m: &Term| -> Option<Seq> {
            let mut at = fixed.clone();
            at.insert(vm, m.clone());
            at.insert(vx, m.clone());
            let target = subst(env, &st.concl, &at);
            let mut s2 = HashMap::new();
            if !pmatch(&sp.concl, &target, &sp.vars, &mut s2) || sp.vars.iter().any(|v| !s2.contains_key(v)) {
                return None;
            }
            let ps: Vec<Seq> = sp.prems.iter().map(|q| Seq::eval_goal_in(env, ses, &xs, &subst(env, q, &s2))).collect::<KResult<_>>().ok()?;
            let vals: Vec<Term> = sp.vars.iter().map(|v| s2[v].clone()).collect();
            instance(env, lg, &stop, &vals, &ps.iter().collect::<Vec<_>>()).ok()
        };
        let trace = std::env::var("RUN_STEPS_TRACE").is_ok();
        let t0 = std::time::Instant::now();
        // forward: the states
        let mut states = vec![m0];
        let mut taken: Vec<Taken> = Vec::new();
        let mut tm = [0f64; 4];
        let base = loop {
            let m = states.last().unwrap().clone();
            let t1 = std::time::Instant::now();
            if let Some(b) = try_stop(&mut ses, &m) {
                break b;
            }
            tm[0] += t1.elapsed().as_secs_f64();
            let k = taken.len();
            if k >= MAX_STEPS {
                return err(format!("run_steps: no stop within {} steps", MAX_STEPS));
            }
            let t1 = std::time::Instant::now();
            let mut at = fixed.clone();
            at.insert(vm, m.clone());
            let mut side = Vec::new();
            for (i, q) in st.prems.iter().enumerate() {
                if i == run_ix || i == cont_ix {
                    continue;
                }
                let q = subst(env, q, &at);
                side.push(Seq::eval_goal_in(env, &mut ses, &xs, &q).map_err(|e| KernelError(format!("run_steps: step {}: STEP's premise `{}`: {}", k, Printer::new(env).short(&q), e.0)))?);
            }
            let t2 = std::time::Instant::now();
            tm[1] += (t2 - t1).as_secs_f64();
            let outs = ses.outcomes(&prog, &m).map_err(|e| KernelError(format!("run_steps: step {}: {}", k, e.0)))?;
            let t3 = std::time::Instant::now();
            tm[2] += (t3 - t2).as_secs_f64();
            let o = outs
                .iter()
                .find(|o| matches!(o.node(), Node::App(c, _) if *c == okc))
                .cloned()
                .ok_or_else(|| KernelError(format!("run_steps: step {}: no normal outcome ({} outcomes)", k, outs.len())))?;
            let Node::App(_, ob) = o.node() else { unreachable!() };
            let (m1, v) = (ob[0].clone(), ob[1].clone());
            let rg = Term::app(runs, vec![prog.clone(), m.clone(), o.clone()]);
            let run = Seq::eval_goal_in(env, &mut ses, &xs, &rg).map_err(|e| KernelError(format!("run_steps: step {}: the step's run: {}", k, e.0)))?;
            tm[3] += t3.elapsed().as_secs_f64();
            if trace {
                let rss = std::fs::read_to_string("/proc/self/statm").ok().and_then(|s| s.split_whitespace().nth(1).and_then(|x| x.parse::<u64>().ok())).unwrap_or(0) * 4096 >> 20;
                eprintln!("run_steps: step {} ({:.2} s; stop {:.2}, side {:.2}, outcomes {:.2}, check {:.2}; {} MB)", k, t0.elapsed().as_secs_f64(), tm[0], tm[1], tm[2], tm[3], rss);
            }
            taken.push(Taken { m1: m1.clone(), v, side, run });
            states.push(m1);
        };
        // backward: STEP from each state, the end fixed
        let mf = states.last().unwrap().clone();
        let mut fact = base;
        for (k, t) in taken.iter().enumerate().rev() {
            let mut at = fixed.clone();
            at.insert(vm, states[k].clone());
            at.insert(vm1, t.m1.clone());
            at.insert(vv, t.v.clone());
            at.insert(vx, mf.clone());
            let vals: Vec<Term> = st.vars.iter().map(|v| at.get(v).cloned().ok_or_else(|| KernelError("run_steps: a STEP variable not determined".into()))).collect::<KResult<_>>()?;
            let mut side = t.side.iter();
            let ps: Vec<&Seq> = (0..st.prems.len())
                .map(|i| if i == run_ix { &t.run } else if i == cont_ix { &fact } else { side.next().unwrap() })
                .collect();
            fact = instance(env, lg, &step, &vals, &ps)?;
        }
        if trace {
            eprintln!("run_steps: {} steps, {:.2} s", taken.len(), t0.elapsed().as_secs_f64());
        }
        let r = Seq::ex_intro(env, lg, &fact, &mf, &body)?;
        drop(ses);
        self.check(envm, r, goal)
    }
}
