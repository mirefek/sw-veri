//! The proof checker's rules as functions on sequents and terms, for
//! programs that prove (the C1 engine): no proof text. The same semantics
//! as the language's rules (`mp`, instantiation by name, `apply`, the goal
//! rules `simp`, `taut`, `arith`, `defs`, `mem`), each result a sequent
//! made by the kernel's rules.

use super::*;

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
}

impl Api {
    pub fn new(env: &Env, fixed: Vec<(String, VarId)>) -> KResult<Api> {
        Ok(Api { st: State::new(fixed, Vec::new(), None), lg: Logic::new(env)? })
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
                let loops = if unroll { vec![LoopHint { inv: Term::app(env.builtins.eq, vec![Term::bvar(0), Term::bvar(0)]), var: None, unroll: true }] } else { Vec::new() };
                let refs: Vec<&Seq> = facts.iter().collect();
                Seq::simp_goal(env, lg, &refs, goal, &loops, &keep)
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
        s.concl().vars(&mut vs);
        for h in s.hyps() {
            h.vars(&mut vs);
        }
        let mut staged = Vec::new();
        let mut bound: Vec<(&str, Term)> = Vec::new();
        for (vname, value) in binds {
            let cands: Vec<VarId> = vs.iter().copied().filter(|v| env.vars[*v as usize].name == *vname).collect();
            let v = match cands.as_slice() {
                [v] => *v,
                [] => {
                    bound.push((vname, value.clone()));
                    continue;
                }
                _ => return err(format!("several variables named `{}`", vname)),
            };
            let k = env.vars[v as usize].arity;
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
                    if vs.contains(v) && env.vars[*v as usize].arity == 0 {
                        return err(format!("apply: `{}` is not determined", env.vars[*v as usize].name));
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
