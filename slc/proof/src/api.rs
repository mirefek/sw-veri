//! The proof checker's rules as functions on sequents and terms, for
//! programs that prove (the C1 engine): no proof text. The same semantics
//! as the language's rules (`mp`, instantiation by name, `apply`, the goal
//! rules `simp`, `taut`, `arith`, `defs`, `mem`), each result a sequent
//! made by the kernel's rules.

use super::*;

/// `k in dom(fn_update(.. fn_update(f, j, v) ..))`, k and the keys passed
/// literals: by `tr.dom_upd` at the update at k, `tr.dom_keep` past the
/// others (their keys distinct literals, by evaluation); None if not of
/// that form
fn dom_member(env: &Env, lg: &Logic, goal: &Term) -> Option<Seq> {
    let g = |n: &str| env.sym_by_name.get(n).copied();
    let (dom, fn_update) = (g("dom")?, g("fn_update")?);
    let Node::App(i, a) = goal.node() else { return None };
    if *i != lg.in_ || a.len() != 2 {
        return None;
    }
    let k = &a[0];
    let lit = |t: &Term| matches!(t.node(), Node::Nat(_) | Node::Bytes(_));
    if !lit(k) {
        return None;
    }
    let Node::App(d, m) = a[1].node() else { return None };
    if *d != dom || m.len() != 1 {
        return None;
    }
    // the updates from the outside in, to the one at k
    let mut chain = Vec::new();
    let mut cur = m[0].clone();
    loop {
        let Node::App(u, b) = cur.node() else { return None };
        if *u != fn_update || b.len() != 3 || !lit(&b[1]) {
            return None;
        }
        let (f, j, v) = (b[0].clone(), b[1].clone(), b[2].clone());
        chain.push((f.clone(), j.clone(), v));
        if j == *k {
            break;
        }
        cur = f;
    }
    let upd = facts::seq_of(env, "tr.dom_upd")?;
    let keep = facts::seq_of(env, "tr.dom_keep")?;
    let (f, j, v) = chain.pop()?;
    let inst = |s: &Seq, ts: &[&Term]| ts.iter().try_fold(s.clone(), |s, t| Seq::all_elim(env, lg, &s, t)).ok();
    let mut s = inst(&upd, &[&f, &j, &v])?;
    while let Some((f, j, v)) = chain.pop() {
        let ne = Term::app(g("not")?, vec![Term::app(env.builtins.eq, vec![k.clone(), j.clone()])]);
        let hne = Seq::eval_goal(env, lg, &[], &ne).ok()?;
        let h = inst(&keep, &[&f, k, &j, &v])?;
        s = Seq::mp(env, &Seq::mp(env, &h, &s).ok()?, &hne).ok()?;
    }
    (s.concl() == goal).then_some(s)
}

/// `app(fn_update(.. fn_update(f, k, v) ..), k) = v`, k and the keys passed
/// literals: by `app_update_other` past the other keys (distinct literals,
/// by evaluation) and `app_update_same` at k; None if not of that form or
/// the value read is not the goal's right side
fn map_lookup(api: &Api, env: &mut Env, goal: &Term) -> Option<Seq> {
    let lg = &api.lg;
    let g = |n: &str| env.sym_by_name.get(n).copied();
    let (app, fn_update, not) = (g("app")?, g("fn_update")?, g("not")?);
    let Node::App(e, a) = goal.node() else { return None };
    if *e != env.builtins.eq || a.len() != 2 {
        return None;
    }
    let Node::App(ap, b) = a[0].node() else { return None };
    if *ap != app || b.len() != 2 {
        return None;
    }
    let k = &b[1];
    let lit = |t: &Term| matches!(t.node(), Node::Nat(_) | Node::Bytes(_));
    if !lit(k) {
        return None;
    }
    let (k, top) = (k.clone(), b[0].clone());
    let other = facts::seq_of(env, "app_update_other")?;
    let same = facts::seq_of(env, "app_update_same")?;
    // app(m, k) = .. step by step, from the outside in
    let mut acc: Option<Seq> = None;
    let mut cur = top;
    loop {
        let Node::App(u, c) = cur.node() else { return None };
        if *u != fn_update || c.len() != 3 || !lit(&c[1]) {
            return None;
        }
        let (f, j, v) = (c[0].clone(), c[1].clone(), c[2].clone());
        let step = if j == k {
            api.inst(env, same.clone(), &[("f", f.clone()), ("k", j.clone()), ("v", v)]).ok()?
        } else {
            let ne = Term::app(not, vec![Term::app(env.builtins.eq, vec![k.clone(), j.clone()])]);
            let hne = Seq::eval_goal(env, lg, &[], &ne).ok()?;
            let h = api.inst(env, other.clone(), &[("f", f.clone()), ("k", j.clone()), ("v", v), ("x", k.clone())]).ok()?;
            Seq::mp(env, &h, &hne).ok()?
        };
        acc = Some(match acc {
            None => step,
            Some(s) => Seq::trans(env, &s, &step).ok()?,
        });
        if j == k {
            break;
        }
        cur = f;
    }
    acc.filter(|s| s.concl() == goal)
}

/// A justification of a goal (a premise, when it is one).
pub enum G {
    /// a proof of it (fitted: its free variables matched, implicit unfolding)
    By(Seq),
    /// `simp(facts, keep(..))` (`unroll`: loops unrolled)
    Simp(Vec<Seq>, Vec<SymId>, bool),
    Taut(Vec<Seq>),
    Arith(Vec<Seq>),
    Mem(Vec<Seq>),
    /// `bitwise([{n},] facts)`: a word equation bit by bit (n its width)
    Bitwise(Vec<Seq>, Option<Term>),
    /// `defs(g, D..)`: g proves it with the definitions unfolded
    Defs(Box<G>, Vec<SymId>),
    /// `apply(f, ..)` against it
    Apply(Seq, Vec<A>),
    /// `mp(f, ..)` (its result fitted to it)
    Mp(Seq, Vec<A>),
    /// `divergence([GU, GS])`: a spec function diverges nowhere it does not
    /// also raise (the lemmas GU, GS by name: a ghost family's)
    Divergence(Vec<String>),
}

/// An argument of `mp` / `apply`: a term for the leading `all`, or a
/// justification of the leading premise.
pub enum A {
    T(Term),
    G(G),
}

/// A proving context: the variables fixed (not instantiated by matching).
pub struct Api {
    st: State,
    pub lg: Logic,
    /// (`G::Simp` without loops or kept definitions, from facts without
    /// hypotheses: the goal and the facts' statements -> the theorem, made
    /// once. A variable id is never reused, so a theorem kept stays about
    /// the same variables.)
    simp_memo: std::cell::RefCell<std::collections::HashMap<(Term, Vec<Term>), Seq>>,
}

impl Api {
    pub fn new(env: &Env, fixed: Vec<(String, VarId)>) -> KResult<Api> {
        Ok(Api { st: State::new(fixed, Vec::new(), None), lg: Logic::new(env)?, simp_memo: Default::default() })
    }

    /// a fixed variable more (a `fix`)
    pub fn fix(&mut self, name: &str, v: VarId) {
        self.st.scope.push((name.to_string(), v));
    }

    /// a theorem, axiom or open lemma by name
    pub fn fact(&self, env: &Env, name: &str) -> KResult<Seq> {
        facts::seq_of(env, name).ok_or_else(|| KernelError(format!("unknown fact `{}`", name)))
    }

    /// `goal` by `g`
    pub fn by(&self, env: &mut Env, goal: &Term, g: G) -> KResult<Seq> {
        let lg = &self.lg;
        match g {
            G::By(s) => self.st.check(env, s, goal),
            G::Simp(facts, keep, unroll) => {
                let memo = !unroll && keep.is_empty() && facts.iter().all(|f| f.hyps().is_empty());
                let key = memo.then(|| (goal.clone(), facts.iter().map(|f| f.concl().clone()).collect::<Vec<_>>()));
                if let Some(s) = key.as_ref().and_then(|k| self.simp_memo.borrow().get(k).cloned()) {
                    return Ok(s);
                }
                // (a literal key of a map built by updates at literal keys: by
                // the updates, no search)
                if let Some(s) = dom_member(env, lg, goal).or_else(|| map_lookup(self, env, goal)) {
                    return Ok(s);
                }
                let loops = if unroll { vec![LoopHint { inv: Term::app(env.builtins.eq, vec![Term::bvar(0), Term::bvar(0)]), var: None, unroll: true }] } else { Vec::new() };
                let refs: Vec<&Seq> = facts.iter().collect();
                let s = Seq::simp_goal(env, lg, &refs, goal, &loops, &keep)?;
                if let Some(k) = key {
                    self.simp_memo.borrow_mut().insert(k, s.clone());
                }
                Ok(s)
            }
            G::Taut(mut ps) => {
                let syms = sym_facts(env, &ps, goal)?;
                ps.extend(syms);
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::taut(env, lg, &refs, goal)
            }
            G::Arith(ps) => {
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::arith(env, lg, &refs, goal)
            }
            G::Bitwise(ps, width) => self.st.bitwise_goal(env, lg, goal, &ps, width),
            G::Mem(ps) => {
                let ps = split_conj(env, ps)?;
                self.st.mem_goal(env, lg, goal, &ps)
            }
            G::Defs(inner, syms) => {
                let unfolded = unfold_all(env, goal, &syms);
                let s = self.by(env, &unfolded, *inner)?;
                Seq::conv(env, &s, goal, &syms)
            }
            G::Apply(f, args) => {
                let s = self.apply(env, f, args, Some(goal))?;
                self.st.check(env, s, goal)
            }
            G::Mp(f, args) => {
                let s = self.mp(env, f, args)?;
                self.st.check(env, s, goal)
            }
            G::Divergence(names) => {
                let args: Vec<Arg> = names.into_iter().map(|n| Arg::Proof(PE::Ref(n))).collect();
                self.st.divergence(env, lg, goal, &args)
            }
        }
    }

    /// `mp(f, a1, ..)`: a term instantiates the leading `all`, a
    /// justification proves the leading premise
    pub fn mp(&self, env: &mut Env, f: Seq, args: Vec<A>) -> KResult<Seq> {
        let lg = &self.lg;
        let mut s = f;
        for a in args {
            match a {
                A::T(t) => {
                    let _p = sl_kernel::prof::g("mp all_elim");
                    s = head_to(env, s, |t| matches!(t.node(), Node::App(e, _) if *e == lg.all))?;
                    s = Seq::all_elim(env, lg, &s, &t)?;
                }
                A::G(G::By(x)) => {
                    let _p = sl_kernel::prof::g("mp premise");
                    s = mp_u(env, &s, &x)?
                }
                A::G(g) => {
                    let kind = match &g {
                        G::Simp(..) => "mp by simp",
                        G::Taut(..) => "mp by taut",
                        G::Arith(..) => "mp by arith",
                        G::Defs(..) => "mp by defs",
                        G::Apply(..) | G::Mp(..) => "mp by mp",
                        _ => "mp by other",
                    };
                    let (prem, _) = imp_parts(env, s.concl())?;
                    let x = {
                        let _p = sl_kernel::prof::g(kind);
                        self.by(env, &prem, g)?
                    };
                    let _p = sl_kernel::prof::g("mp premise");
                    s = mp_u(env, &s, &x)?;
                }
            }
        }
        Ok(s)
    }

    /// a theorem's schematic variables instantiated by name, simultaneously
    /// (as `name[x := t, ..]`); names of leading `all` binders after them
    pub fn inst(&self, env: &mut Env, s: Seq, binds: &[(&str, Term)]) -> KResult<Seq> {
        let mut s = s;
        let mut vs = Vec::new();
        {
            let _p = sl_kernel::prof::g("inst vars");
            s.concl().vars(&mut vs);
            for h in s.hyps() {
                h.vars(&mut vs);
            }
        }
        let mut staged = Vec::new();
        let mut bound: Vec<(&str, Term)> = Vec::new();
        // (simultaneously: through fresh variables, unless no value has a
        // variable instantiated -- then one after the other is the same)
        let targets: Vec<VarId> = vs.iter().copied().filter(|v| binds.iter().any(|(n, _)| env.var(*v).name == *n)).collect();
        let direct = binds.iter().all(|(_, value)| !targets.iter().any(|w| value.has_var(*w)));
        for (vname, value) in binds {
            let cands: Vec<VarId> = vs.iter().copied().filter(|v| env.var(*v).name == *vname).collect();
            let v = match cands.as_slice() {
                [v] => *v,
                [] => {
                    bound.push((vname, value.clone()));
                    continue;
                }
                _ => return err(format!("several variables named `{}`", vname)),
            };
            if direct {
                s = Seq::inst(env, &s, v, value)?;
                continue;
            }
            let k = env.var(v).arity;
            let tmp = env.new_var(&format!("{}'", vname), k);
            let tmp_term = Term::var(tmp, (0..k).rev().map(Term::bvar).collect());
            s = Seq::inst(env, &s, v, &tmp_term)?;
            staged.push((tmp, value.clone()));
        }
        for (tmp, value) in staged {
            s = Seq::inst(env, &s, tmp, &value)?;
        }
        if !bound.is_empty() {
            s = self.inst_bound_terms(env, s, &bound)?;
        }
        Ok(s)
    }

    /// the variable v instantiated by value (a variable found before)
    pub fn inst_var(&self, env: &mut Env, s: Seq, v: VarId, value: &Term) -> KResult<Seq> {
        Seq::inst(env, &s, v, value)
    }

    /// leading `all` binders instantiated by name (the ones before kept
    /// general)
    fn inst_bound_terms(&self, env: &mut Env, mut s: Seq, bound: &[(&str, Term)]) -> KResult<Seq> {
        let lg = &self.lg;
        let mut names = Vec::new();
        let mut t = s.concl().clone();
        while let Node::App(a, x) = t.node() {
            if *a != lg.all {
                break;
            }
            names.push(t.binder_name().map(|n| n.to_string()));
            t = x[0].clone();
        }
        let mut last = 0;
        for (n, _) in bound {
            match names.iter().position(|m| m.as_deref() == Some(*n)) {
                Some(i) => last = last.max(i + 1),
                None => return err(format!("no variable `{}` to instantiate", n)),
            }
        }
        let mut general = Vec::new();
        for name in names.iter().take(last) {
            let value = match bound.iter().find(|(n, _)| Some(*n) == name.as_deref()) {
                Some((_, v)) => v.clone(),
                None => {
                    let v = env.new_var(name.as_deref().unwrap_or("x"), 0);
                    general.push(v);
                    Term::var(v, vec![])
                }
            };
            s = Seq::all_elim(env, lg, &s, &value)?;
        }
        for v in general.into_iter().rev() {
            s = Seq::gen(env, lg, &s, v)?;
        }
        Ok(s)
    }

    /// `apply(f, a1, ..)`: f's variables (schematic ones, then its leading
    /// `all`s) from the terms in order, the rest by matching f's premises
    /// with the proofs (and its conclusion with the goal); the justifications
    /// then prove their premises, instantiated
    pub fn apply(&self, env: &mut Env, f: Seq, args: Vec<A>, goal: Option<&Term>) -> KResult<Seq> {
        let lg = &self.lg;
        let mut s = f;
        let mut terms = Vec::new();
        let mut proofs: Vec<Option<Seq>> = Vec::new();
        let mut goal_args: Vec<(usize, G)> = Vec::new();
        for a in args {
            match a {
                A::T(t) => terms.push(t),
                A::G(G::By(x)) => proofs.push(Some(x)),
                A::G(g) => {
                    goal_args.push((proofs.len(), g));
                    proofs.push(None);
                }
            }
        }
        let mut pvars = self.st.free_vars(&s);
        let mut terms = terms.into_iter();
        while let Node::App(a, _) = s.concl().node() {
            if *a != lg.all {
                break;
            }
            let t = match terms.next() {
                Some(t) => t,
                None => {
                    let v = env.new_var("x?", 0);
                    pvars.push(v);
                    Term::var(v, vec![])
                }
            };
            s = Seq::all_elim(env, lg, &s, &t)?;
        }
        if terms.next().is_some() {
            return err("apply: more terms than leading `all`s");
        }
        let mut binds: Vec<(VarId, Term)> = Vec::new();
        if let Some(g) = goal {
            let mut c = s.concl().clone();
            for _ in 0..proofs.len() {
                match imp_parts(env, &c) {
                    Ok((_, b)) => c = b,
                    Err(_) => break,
                }
            }
            let mut b = Vec::new();
            if pmatch(env, &c, g, &pvars, &mut b) {
                binds = b;
            }
        }
        let mut c = s.concl().clone();
        let and = env.sym_by_name.get("and").copied();
        for (i, p) in proofs.iter_mut().enumerate() {
            let (a, b) = imp_parts(env, &c).map_err(|_| KernelError(format!("apply: no premise for the proof number {}", i + 1)))?;
            c = b;
            let Some(p) = p else { continue };
            let a = {
                let bf = env.binders_fn();
                binds.iter().fold(a, |t, (v, x)| t.subst_var(*v, x, &bf))
            };
            if !pmatch(env, &a, p.concl(), &pvars, &mut binds) {
                let mut cs = Vec::new();
                conjuncts(p.concl(), and, &mut cs);
                let hit = cs.iter().find(|x| {
                    let mut b = binds.clone();
                    pmatch(env, &a, x, &pvars, &mut b)
                });
                match hit {
                    Some(x) => {
                        pmatch(env, &a, x, &pvars, &mut binds);
                        let x = x.clone();
                        *p = Seq::taut(env, lg, &[&*p], &x)?;
                    }
                    None => {
                        let pp = Printer::new(env);
                        let bf = env.binders_fn();
                        let a2 = binds.iter().fold(a.clone(), |t, (v, x)| t.subst_var(*v, x, &bf));
                        return err(format!("apply: the proof number {} does not match the premise `{}`\n  {}", i + 1, pp.short(&a2), pp.mismatch(&a2, p.concl())));
                    }
                }
            }
        }
        for v in &pvars {
            match binds.iter().find(|(w, _)| w == v) {
                Some((_, t)) => s = Seq::inst(env, &s, *v, t)?,
                None => {
                    let mut vs = Vec::new();
                    s.concl().vars(&mut vs);
                    if vs.contains(v) && env.var(*v).arity == 0 {
                        return err(format!("apply: `{}` is not determined", env.var(*v).name));
                    }
                }
            }
        }
        // the justifications, on their premises as instantiated
        let mut c = s.concl().clone();
        let mut prems = Vec::new();
        for _ in 0..proofs.len() {
            let (a, b) = imp_parts(env, &c)?;
            prems.push(a);
            c = b;
        }
        for (i, g) in goal_args {
            proofs[i] = Some(self.by(env, &prems[i], g)?);
        }
        for p in proofs {
            s = mp_u(env, &s, &p.unwrap())?;
        }
        Ok(s)
    }

    /// `expand(s, D..)`: s with the definitions unfolded
    pub fn expand(&self, env: &mut Env, s: Seq, syms: &[SymId]) -> KResult<Seq> {
        let goal = unfold_all(env, s.concl(), syms);
        Seq::conv(env, &s, &goal, syms)
    }

    /// `s` as a proof of `goal` (fitted, implicit unfolding)
    pub fn check(&self, env: &mut Env, s: Seq, goal: &Term) -> KResult<Seq> {
        self.st.check(env, s, goal)
    }
}
