//! Natural deduction: sequents `hyps ⊢ concl` and the derived rules on them.
//!
//! Trusted extension. A sequent `h1, .., hn ⊢ c` stands for the kernel
//! statement `h1 -> .. -> hn -> c`; the rules below are the standard ones,
//! derivable from the kernel's (modus ponens, instantiation) and the
//! prelude's axioms by the deduction theorem (from `imp_weaken` and
//! `imp_chain`). Each rule notes its derivation.

use super::prop::Logic;
use crate::env::{Env, KResult, KernelError, SymKind, Thm};
use crate::syntax::Printer;
use crate::term::{Node, SymId, Term, VarId};

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

/// `hyps ⊢ concl`, resting on the open lemmas `open` (see `ext::facts`; a
/// sequent with open lemmas never becomes a `Thm`). Private fields: only
/// the rules below build sequents.
#[derive(Clone, Debug)]
pub struct Seq {
    hyps: Vec<Term>,
    concl: Term,
    open: Vec<String>,
}

fn union<T: Clone + PartialEq>(a: &[T], b: &[T]) -> Vec<T> {
    let mut v = a.to_vec();
    for h in b {
        if !v.contains(h) {
            v.push(h.clone());
        }
    }
    v
}

/// Replaces every occurrence of the closed term `pat` in `t` by the bound
/// variable of a new binder around `t` (so the result has one loose
/// variable, `BVar(0)` at the top).
pub(crate) fn abstract_term(t: &Term, pat: &Term, depth: u32, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
    if t == pat {
        return Term::bvar(depth);
    }
    match t.node() {
        Node::App(s, args) => t.with_args(args.iter().enumerate().map(|(i, a)| abstract_term(a, pat, depth + binders(*s, i), binders)).collect()),
        Node::Var(_, args) => t.with_args(args.iter().map(|a| abstract_term(a, pat, depth, binders)).collect()),
        // bound variables of `t` itself: those below `depth` are bound inside
        // `t`, the new binder is outside them all
        _ => t.clone(),
    }
}

/// `abstract_term` at the chosen occurrences of `pat` only (numbered from
/// 1 in `count`, outer before inner, left to right; all if `occ` is empty).
fn abstract_at(t: &Term, pat: &Term, depth: u32, binders: &dyn Fn(SymId, usize) -> u32, occ: &[usize], count: &mut usize) -> Term {
    if t == pat {
        *count += 1;
        if occ.is_empty() || occ.contains(count) {
            return Term::bvar(depth);
        }
        return t.clone();
    }
    match t.node() {
        Node::App(s, args) => t.with_args(args.iter().enumerate().map(|(i, a)| abstract_at(a, pat, depth + binders(*s, i), binders, occ, count)).collect()),
        Node::Var(_, args) => t.with_args(args.iter().map(|a| abstract_at(a, pat, depth, binders, occ, count)).collect()),
        _ => t.clone(),
    }
}

/// bound variable `i` (counted at `depth` 0) occurs loose in `t`
fn bvar_free_at(t: &Term, i: u32, depth: u32, bf: &dyn Fn(SymId, usize) -> u32) -> bool {
    match t.node() {
        Node::BVar(j) => *j == i + depth,
        Node::App(s, a) => a.iter().enumerate().any(|(k, x)| bvar_free_at(x, i, depth + bf(*s, k), bf)),
        Node::Var(_, a) => a.iter().any(|x| bvar_free_at(x, i, depth, bf)),
        _ => false,
    }
}

/// `t` with its loose bound variables from `k` on lowered by `k` (None if one
/// below `k` occurs: bound inside the matched part)
fn lower(t: &Term, k: u32, depth: u32, bf: &dyn Fn(SymId, usize) -> u32) -> Option<Term> {
    if k == 0 {
        return Some(t.clone());
    }
    Some(match t.node() {
        Node::BVar(i) if *i >= depth + k => Term::bvar(i - k),
        Node::BVar(i) if *i >= depth => return None,
        Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
        Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(j, x)| lower(x, k, depth + bf(*s, j), bf)).collect::<Option<_>>()?),
        Node::Var(_, a) => t.with_args(a.iter().map(|x| lower(x, k, depth, bf)).collect::<Option<_>>()?),
    })
}

/// matches the pattern `p` (its loose bound variables from `pd` on the n
/// pattern variables, `as_[j]` for `BVar(pd + j)`) against `t`
fn match_pat(p: &Term, t: &Term, pd: u32, n: u32, as_: &mut Vec<Option<Term>>, bf: &dyn Fn(SymId, usize) -> u32) -> bool {
    match (p.node(), t.node()) {
        (Node::BVar(i), _) if *i >= pd && *i < pd + n => {
            // (the value: t at the match site, no variable bound inside)
            let Some(v) = lower(t, pd, 0, bf) else { return false };
            let j = (i - pd) as usize;
            match &as_[j] {
                Some(w) => *w == v,
                None => {
                    as_[j] = Some(v);
                    true
                }
            }
        }
        (Node::BVar(i), Node::BVar(j)) if *i < pd => i == j,
        (Node::BVar(i), Node::BVar(j)) => *j == *i - n,
        (Node::App(s1, a1), Node::App(s2, a2)) if s1 == s2 && a1.len() == a2.len() => {
            a1.iter().zip(a2.iter()).enumerate().all(|(k, (x, y))| match_pat(x, y, pd + bf(*s1, k), n, as_, bf))
        }
        (Node::Var(v1, a1), Node::Var(v2, a2)) if v1 == v2 && a1.len() == a2.len() => a1.iter().zip(a2.iter()).all(|(x, y)| match_pat(x, y, pd, n, as_, bf)),
        (Node::Nat(_), _) | (Node::Bytes(_), _) => p == t,
        _ => false,
    }
}

/// `t` (at binder depth `d` of the whole statement) with the instances of
/// `l` (n pattern variables) replaced by those of `r`: all, or the chosen
/// ones (`count` numbers them; outer before inner, left to right)
#[allow(clippy::too_many_arguments)]
fn rewrite_pat(env: &Env, t: &Term, l: &Term, r: &Term, n: u32, d: u32, occ: &[usize], count: &mut usize) -> Term {
    let bf = env.binders_fn();
    let mut as_ = vec![None; n as usize];
    if match_pat(l, t, 0, n, &mut as_, &bf) && as_.iter().all(|x| x.is_some()) {
        *count += 1;
        if occ.is_empty() || occ.contains(count) {
            // (r's BVar(j) is pattern variable j: instantiate_params takes
            // them outermost first)
            let args: Vec<Term> = as_.into_iter().rev().map(|x| x.unwrap()).collect();
            let rr = r.instantiate_params(&args, &bf);
            return match t.label() {
                Some(lb) => rr.with_label(Some(lb.into())),
                None => rr,
            };
        }
    }
    match t.node() {
        Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| rewrite_pat(env, x, l, r, n, d + bf(*s, i), occ, count)).collect()),
        Node::Var(_, a) => t.with_args(a.iter().map(|x| rewrite_pat(env, x, l, r, n, d, occ, count)).collect()),
        _ => t.clone(),
    }
}

impl Seq {
    pub fn hyps(&self) -> &[Term] {
        &self.hyps
    }

    pub fn concl(&self) -> &Term {
        &self.concl
    }

    /// The open lemmas this sequent rests on (empty: none).
    pub fn open(&self) -> &[String] {
        &self.open
    }

    pub fn show(&self, env: &Env) -> String {
        let p = Printer::new(env);
        let hs: Vec<String> = self.hyps.iter().map(|h| p.term(h)).collect();
        format!("{} ⊢ {}", hs.join(", "), p.term(&self.concl))
    }

    /// `⊢ φ` from a theorem.
    pub fn of_thm(t: &Thm) -> Seq {
        Seq { hyps: Vec::new(), concl: t.prop().clone(), open: Vec::new() }
    }

    /// `⊢ φ` resting on the open lemma `name` (`φ` its statement).
    pub fn open_lemma(env: &Env, name: &str) -> KResult<Seq> {
        match env.open.lemmas.iter().find(|(n, _)| n == name) {
            Some((_, t)) => Ok(Seq { hyps: Vec::new(), concl: t.clone(), open: vec![name.to_string()] }),
            None => err(format!("no open lemma `{}`", name)),
        }
    }

    /// The same sequent with its conclusion as written in `t` (equal to it:
    /// only the metadata, labels and binder names, are `t`'s).
    pub(crate) fn restated(self, t: &Term) -> Seq {
        assert!(self.concl == *t, "restated: a different statement");
        Seq { concl: t.clone(), ..self }
    }

    /// `⊢ φ` resting on `open`: a cached conditional theorem (`ext::cache`).
    pub(crate) fn cached(concl: Term, open: Vec<String>) -> Seq {
        Seq { hyps: Vec::new(), concl, open }
    }

    /// A theorem, once no hypotheses and no open lemmas are left.
    pub fn into_thm(self, env: &Env) -> KResult<Thm> {
        if !self.hyps.is_empty() {
            return err(format!("hypotheses left: {}", self.show(env)));
        }
        if !self.open.is_empty() {
            return err(format!("rests on open lemmas: {}", self.open.join(", ")));
        }
        Ok(Thm::by_extension(self.concl))
    }

    /// `a ⊢ a` (`a -> a`: from `imp_chain` and `imp_weaken`).
    pub fn assume(env: &Env, a: Term) -> KResult<Seq> {
        env.check_wf(&a, 0)?;
        Ok(Seq { hyps: vec![a.clone()], concl: a, open: Vec::new() })
    }

    /// From `Γ ⊢ φ`: `Γ \ {a} ⊢ a -> φ` (the deduction theorem; if `a` is not
    /// among `Γ`, `imp_weaken`).
    pub fn discharge(&self, env: &Env, a: &Term) -> KResult<Seq> {
        env.check_wf(a, 0)?;
        Ok(Seq {
            hyps: self.hyps.iter().filter(|h| *h != a).cloned().collect(),
            concl: env.mk_imp(a.clone(), self.concl.clone()),
            open: self.open.clone(),
        })
    }

    /// From `Γ ⊢ a -> b` and `Δ ⊢ a`: `Γ, Δ ⊢ b` (modus ponens under
    /// hypotheses: `imp_chain`).
    pub fn mp(env: &Env, imp: &Seq, a: &Seq) -> KResult<Seq> {
        match imp.concl.node() {
            Node::App(s, args) if *s == env.builtins.imp && args[0] == a.concl => {
                Ok(Seq { hyps: union(&imp.hyps, &a.hyps), concl: args[1].clone(), open: union(&imp.open, &a.open) })
            }
            Node::App(s, args) if *s == env.builtins.imp => {
                let p = Printer::new(env);
                err(format!("modus ponens: the fact does not match the premise `{}`\n  {}", p.short(&args[0]), p.mismatch(&args[0], &a.concl)))
            }
            _ => err(format!("modus ponens: not an implication: `{}`", Printer::new(env).short(&imp.concl))),
        }
    }

    /// Instantiates schematic variable `v` everywhere (the kernel's rule,
    /// applied to the whole implication).
    pub fn inst(env: &Env, s: &Seq, v: VarId, value: &Term) -> KResult<Seq> {
        let arity = env.vars.get(v as usize).ok_or_else(|| KernelError("unknown variable".into()))?.arity;
        env.check_wf(value, arity)?;
        let b = env.binders_fn();
        Ok(Seq {
            hyps: s.hyps.iter().map(|h| h.subst_var(v, value, &b)).collect(),
            concl: s.concl.subst_var(v, value, &b),
            open: s.open.clone(),
        })
    }

    /// From `Γ ⊢ φ(v)`, `v` a first-order variable not in `Γ`: `Γ ⊢ all x. φ(x)`.
    /// Derivation: `all x. φ(x)` is `!(ex x. !φ(x))`; from `ex x. !φ(x)`,
    /// `choose_spec` gives `!φ(c)` for `c = choose(x. !φ(x))`, and
    /// instantiating `v` by `c` gives `φ(c)`: a contradiction.
    pub fn gen(env: &Env, lg: &Logic, s: &Seq, v: VarId) -> KResult<Seq> {
        if env.vars.get(v as usize).map(|x| x.arity) != Some(0) {
            return err("generalization over a variable with parameters");
        }
        for h in &s.hyps {
            let mut vs = Vec::new();
            h.vars(&mut vs);
            if vs.contains(&v) {
                return err(format!("cannot generalize over `{}`: it occurs in a hypothesis", env.vars[v as usize].name));
            }
        }
        let body = abstract_term(&s.concl, &Term::var(v, vec![]), 0, &env.binders_fn());
        Ok(Seq { hyps: s.hyps.clone(), concl: Term::app(lg.all, vec![body]), open: s.open.clone() })
    }

    /// From `Γ ⊢ all x. φ(x)`: `Γ ⊢ φ(t)`. Derivation: from `!φ(t)`,
    /// `ex_intro` gives `ex x. !φ(x)`, contradicting the premise; so `!!φ(t)`,
    /// and `!!a -> a` holds for any `a` (`dne_any` in core/logic.core).
    pub fn all_elim(env: &Env, lg: &Logic, s: &Seq, t: &Term) -> KResult<Seq> {
        env.check_wf(t, 0)?;
        let body = match s.concl.node() {
            Node::App(a, args) if *a == lg.all => &args[0],
            _ => return err(format!("not a universal statement: {}", Printer::new(env).term(&s.concl))),
        };
        let inst = body.instantiate_params(std::slice::from_ref(t), &env.binders_fn());
        Ok(Seq { hyps: s.hyps.clone(), concl: inst, open: s.open.clone() })
    }

    /// From `Γ ⊢ φ(w)`: `Γ ⊢ ex x. φ(x)`, for `body` = φ with one loose
    /// variable (the axiom `ex_intro`).
    pub fn ex_intro(env: &Env, lg: &Logic, s: &Seq, w: &Term, body: &Term) -> KResult<Seq> {
        env.check_wf(w, 0)?;
        env.check_wf(body, 1)?;
        let inst = body.instantiate_params(std::slice::from_ref(w), &env.binders_fn());
        if inst != s.concl {
            let p = Printer::new(env);
            return err(format!("ex_intro: the fact is not the instance `{}`\n  {}", p.short(&inst), p.mismatch(&inst, &s.concl)));
        }
        Ok(Seq { hyps: s.hyps.clone(), concl: Term::app(lg.ex, vec![body.clone()]), open: s.open.clone() })
    }

    /// From `Γ ⊢ ex x. φ(x)`: `Γ ⊢ φ(choose(x. φ(x)))` (the axiom
    /// `choose_spec`).
    pub fn witness(env: &Env, lg: &Logic, s: &Seq) -> KResult<Seq> {
        let body = match s.concl.node() {
            Node::App(e, args) if *e == lg.ex => args[0].clone(),
            _ => return err(format!("not an existential statement: {}", Printer::new(env).term(&s.concl))),
        };
        let c = Term::app(lg.choose, vec![body.clone()]);
        Ok(Seq { hyps: s.hyps.clone(), concl: body.instantiate_params(&[c], &env.binders_fn()), open: s.open.clone() })
    }

    /// `⊢ t = t` (the axiom `eq_refl`).
    pub fn refl(env: &Env, t: &Term) -> KResult<Seq> {
        env.check_wf(t, 0)?;
        Ok(Seq { hyps: Vec::new(), concl: env.mk_eq(t.clone(), t.clone()), open: Vec::new() })
    }

    fn eq_sides(env: &Env, s: &Seq) -> KResult<(Term, Term)> {
        match s.concl.node() {
            Node::App(e, a) if *e == env.builtins.eq => Ok((a[0].clone(), a[1].clone())),
            _ => err(format!("not an equation: {}", Printer::new(env).term(&s.concl))),
        }
    }

    /// From `Γ ⊢ a = b`: `Γ ⊢ b = a` (`eq_subst` with `x. x = a`, `eq_refl`).
    pub fn sym(env: &Env, s: &Seq) -> KResult<Seq> {
        let (a, b) = Self::eq_sides(env, s)?;
        Ok(Seq { hyps: s.hyps.clone(), concl: env.mk_eq(b, a), open: s.open.clone() })
    }

    /// From `Γ ⊢ a = b` and `Δ ⊢ b = c`: `Γ, Δ ⊢ a = c` (`eq_subst` with
    /// `x. a = x`).
    pub fn trans(env: &Env, s1: &Seq, s2: &Seq) -> KResult<Seq> {
        let (a, b) = Self::eq_sides(env, s1)?;
        let (b2, c) = Self::eq_sides(env, s2)?;
        if b != b2 {
            let p = Printer::new(env);
            return err(format!("trans: the middle terms differ\n  {}", p.mismatch(&b, &b2)));
        }
        Ok(Seq { hyps: union(&s1.hyps, &s2.hyps), concl: env.mk_eq(a, c), open: union(&s1.open, &s2.open) })
    }

    /// From `Γ ⊢ a = b` and `Δ ⊢ φ(a)`: `Γ, Δ ⊢ φ(b)`, where `body` is φ with
    /// one loose variable (the axiom `eq_subst`).
    pub fn subst(env: &Env, eq: &Seq, body: &Term, s: &Seq) -> KResult<Seq> {
        let (a, b) = Self::eq_sides(env, eq)?;
        env.check_wf(body, 1)?;
        let bf = env.binders_fn();
        if body.instantiate_params(std::slice::from_ref(&a), &bf) != s.concl {
            return err("subst: the statement is not the predicate at the equation's left side");
        }
        Ok(Seq { hyps: union(&eq.hyps, &s.hyps), concl: body.instantiate_params(&[b], &bf), open: union(&eq.open, &s.open) })
    }

    /// From `Γ ⊢ a = b` and `Δ ⊢ φ`: `Γ, Δ ⊢ φ` with every occurrence of `a`
    /// replaced by `b` (`subst` with φ abstracted over `a`).
    pub fn rewrite(env: &Env, eq: &Seq, s: &Seq) -> KResult<Seq> {
        let (a, _) = Self::eq_sides(env, eq)?;
        let body = abstract_term(&s.concl, &a, 0, &env.binders_fn());
        if body == s.concl {
            return err(format!("rewrite: `{}` does not occur", Printer::new(env).term(&a)));
        }
        Self::subst(env, eq, &body, s)
    }

    /// `rewrite` at the chosen occurrences of `a` (numbered from 1, left to
    /// right, outer before inner) only (`subst` with φ abstracted there).
    pub fn rewrite_at(env: &Env, eq: &Seq, s: &Seq, occ: &[usize]) -> KResult<Seq> {
        let (a, _) = Self::eq_sides(env, eq)?;
        let mut n = 0;
        let body = abstract_at(&s.concl, &a, 0, &env.binders_fn(), occ, &mut n);
        if let Some(k) = occ.iter().find(|k| **k == 0 || **k > n) {
            return err(format!("rewrite: no occurrence {} of `{}` ({} in all)", k, Printer::new(env).short(&a), n));
        }
        Self::subst(env, eq, &body, s)
    }

    /// From `Γ ⊢ all x1 .. xn. l = r` and `Δ ⊢ φ`: `Γ, Δ ⊢ φ'`, φ with each
    /// instance `l[t1 .. tn]` (or the chosen ones, numbered as in
    /// `rewrite_at`) replaced by `r[t1 .. tn]` -- also under binders, where
    /// the ts may mention the bound variables. Derivation: an instance with
    /// closed ts is `all_elim` and `eq_subst`; under a binder, the two sides
    /// are equal for every value of the bound variables, so the binder's
    /// terms are equal by its extensionality (`ex`/`all`: propositional;
    /// `choose`: `choose_ext`; `set_select`, `set_image`: `set_ext`; a
    /// defined binder unfolds to these), and `eq_subst` replaces the whole
    /// binder term (`eq_congr` through the context).
    pub fn rewrite_under(env: &Env, lg: &Logic, eq: &Seq, s: &Seq, occ: &[usize]) -> KResult<Seq> {
        // (the pattern: the equation under its n leading `all`s)
        let mut n = 0u32;
        let mut b = eq.concl.clone();
        while let Node::App(q, a) = b.node() {
            if *q != lg.all {
                break;
            }
            b = a[0].clone();
            n += 1;
        }
        let (l, r) = match b.node() {
            Node::App(e, a) if *e == env.builtins.eq => (a[0].clone(), a[1].clone()),
            _ => return err(format!("rewrite: not an equation under `all`s: {}", Printer::new(env).short(&eq.concl))),
        };
        // every variable of r bound by matching l
        let bf = env.binders_fn();
        for i in 0..n {
            if !bvar_free_at(&l, i, 0, &bf) {
                return err("rewrite: a variable of the equation is not in its left side");
            }
        }
        let mut count = 0;
        let concl = rewrite_pat(env, &s.concl, &l, &r, n, 0, occ, &mut count);
        if count == 0 {
            return err(format!("rewrite: no instance of the left side of `{}`", Printer::new(env).short(&eq.concl)));
        }
        if let Some(k) = occ.iter().find(|k| **k == 0 || **k > count) {
            return err(format!("rewrite: no instance {} of the left side of `{}` ({} in all)", k, Printer::new(env).short(&eq.concl), count));
        }
        env.check_wf(&concl, 0)?;
        Ok(Seq { hyps: union(&eq.hyps, &s.hyps), concl, open: union(&eq.open, &s.open) })
    }

    /// The defining equation of a defined symbol, `⊢ c(params) = body`
    /// (returned by the kernel's `define`).
    pub fn def_eq(env: &Env, sym: SymId) -> KResult<Seq> {
        match env.defs.iter().find(|(s, _)| *s == sym) {
            Some((_, t)) => Ok(Seq::of_thm(t)),
            None => err(format!("`{}` is not a defined symbol", env.syms[sym as usize].name)),
        }
    }

    /// From `Γ ⊢ φ`: `Γ ⊢ ψ`, where φ and ψ are the same after unfolding
    /// every occurrence of the defined symbols `syms` (repeatedly, also in
    /// the unfolded bodies). Derivation: each occurrence `c(args)` is
    /// replaced using the instance `c(args) = body[args]` of the defining
    /// equation (`eq_subst`); an occurrence under binders is replaced for
    /// every value of the bound variables, by congruence, which holds for
    /// every primitive binder of the prelude: `ex` (witness and
    /// `ex_intro`), `choose` (`choose_ext`), `set_select` and `set_image`
    /// (`set_ext` with `set_select_def`, `set_image_def`); defined binders
    /// unfold to these. An argument mentioning variables bound around the
    /// occurrence (`letin(v, x. z = x)` under `ex z`) is the equation's
    /// instance at those variables' values: in the body, the argument's
    /// parameters take the call's arguments, its other bound variables are
    /// shifted past the body's binders.
    pub fn conv(env: &Env, s: &Seq, goal: &Term, syms: &[SymId]) -> KResult<Seq> {
        env.check_wf(goal, 0)?;
        let (uf, ug) = (unfold_all(env, &s.concl, syms), unfold_all(env, goal, syms));
        if uf != ug {
            let p = Printer::new(env);
            return err(format!("the fact and the goal `{}` differ after unfolding\n  {}", p.short(goal), p.mismatch(&ug, &uf)));
        }
        Ok(Seq { hyps: s.hyps.clone(), concl: goal.clone(), open: s.open.clone() })
    }

    /// `⊢ is_prop(t)` for a term known syntactically to be a proposition
    /// (see `Logic::prop_valued`).
    pub fn prop(env: &Env, lg: &Logic, t: &Term) -> KResult<Seq> {
        env.check_wf(t, 0)?;
        if !lg.prop_valued(env, t) {
            return err(format!("not syntactically a proposition: {}", Printer::new(env).term(t)));
        }
        Ok(Seq { hyps: Vec::new(), concl: Term::app(lg.is_prop, vec![t.clone()]), open: Vec::new() })
    }

    /// From premises `Γi ⊢ pi`: `⋃Γi ⊢ goal`, if `p1 -> .. -> goal` is a
    /// propositional tautology (see `Logic::tautology`).
    pub fn taut(env: &Env, lg: &Logic, premises: &[&Seq], goal: &Term) -> KResult<Seq> {
        env.check_wf(goal, 0)?;
        let mut hyps = Vec::new();
        let mut open = Vec::new();
        for p in premises {
            hyps = union(&hyps, &p.hyps);
            open = union(&open, &p.open);
        }
        let ps: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        lg.tautology(env, &ps, goal)?;
        Ok(Seq { hyps, concl: goal.clone(), open })
    }

    /// From premises `Γi ⊢ pi`: `⋃Γi ⊢ goal`, if `p1 -> .. -> goal` holds by
    /// propositional logic and linear arithmetic over the naturals (see
    /// `ext::arith`).
    pub fn arith(env: &Env, lg: &Logic, premises: &[&Seq], goal: &Term) -> KResult<Seq> {
        env.check_wf(goal, 0)?;
        let mut hyps = Vec::new();
        let mut open = Vec::new();
        for p in premises {
            hyps = union(&hyps, &p.hyps);
            open = union(&open, &p.open);
        }
        let ps: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        lg.arith(env, &ps, goal)?;
        Ok(Seq { hyps, concl: goal.clone(), open })
    }

    /// From premises (list memberships among them): `⋃Γi ⊢ A = B` for list
    /// expressions with the same pieces (see `ext::list`).
    pub fn lists(env: &Env, lg: &Logic, premises: &[&Seq], goal: &Term) -> KResult<Seq> {
        env.check_wf(goal, 0)?;
        let (hyps, open) = Self::gather(premises);
        let ps: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        lg.list_eq(env, &ps, goal)?;
        Ok(Seq { hyps, concl: goal.clone(), open })
    }

    /// `⋃Γi ⊢ app(L, i) = e`: the element at i of a list expression, the
    /// bounds of i shown by `arith` from the premises (see `ext::list`).
    pub fn list_at(env: &Env, lg: &Logic, premises: &[&Seq], t: &Term) -> KResult<Seq> {
        env.check_wf(t, 0)?;
        let (hyps, open) = Self::gather(premises);
        let ps: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        let concl = lg.list_at(env, &ps, t)?;
        Ok(Seq { hyps, concl, open })
    }

    /// `⋃Γi ⊢ bytes_at(M, b, m) = r`: a memory read through M's writes,
    /// their places decided by `arith` from the premises (see `ext::mem`).
    pub fn mem_read(env: &Env, lg: &Logic, premises: &[&Seq], t: &Term) -> KResult<Seq> {
        env.check_wf(t, 0)?;
        let (hyps, open) = Self::gather(premises);
        let ps: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        let concl = lg.mem_read(env, &ps, t)?;
        Ok(Seq { hyps, concl, open })
    }

    /// List extensionality (see `Logic::list_ext`).
    pub fn list_ext(env: &Env, lg: &Logic, ha: &Seq, hb: &Seq, hlen: &Seq, hel: &Seq) -> KResult<Seq> {
        let (hyps, open) = Self::gather(&[ha, hb, hlen, hel]);
        let concl = lg.list_ext(env, &ha.concl, &hb.concl, &hlen.concl, &hel.concl)?;
        Ok(Seq { hyps, concl, open })
    }

    /// From `Γ ⊢ φ`: `Γ ⊢ φ'`, φ simplified (see `ext::simp`; φ implies φ').
    pub fn simp(env: &Env, lg: &Logic, s: &Seq) -> Seq {
        Seq { hyps: s.hyps.clone(), concl: lg.simp_fact(env, &s.concl), open: s.open.clone() }
    }

    /// From premises: `⋃Γi ⊢ goal`, when the simplified premises imply the
    /// simplified goal (equivalent to the goal) by propositional logic, or
    /// else by linear arithmetic.
    /// `simp`: the goal from the premises, with loop hints, keeping the
    /// programs `keep` folded.
    pub fn simp_goal(env: &Env, lg: &Logic, premises: &[&Seq], goal: &Term, loops: &[super::simp::LoopHint], keep: &[SymId]) -> KResult<Seq> {
        env.check_wf(goal, 0)?;
        for h in loops {
            env.check_wf(&h.inv, 2)?;
            if let Some(m) = &h.var {
                env.check_wf(m, 1)?;
            }
        }
        let (hyps, mut open) = Self::gather(premises);
        let ps: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        *lg.simp_keep.borrow_mut() = keep.to_vec();
        lg.simp_used.borrow_mut().clear();
        lg.simp_goal_loops.set(loops.iter().any(|h| h.unroll));
        let r = lg.simp_prove_loops(env, &ps, goal, loops);
        lg.simp_goal_loops.set(false);
        lg.simp_keep.borrow_mut().clear();
        let used = std::mem::take(&mut *lg.simp_used.borrow_mut());
        r?;
        // the library facts the step relied on: proven, or open lemmas this
        // sequent rests on (never silently assumed)
        for name in used {
            // (its statement the one simp relies on: `ext::pinned`)
            if !super::pinned::thm_ok(env, &name) {
                return err(format!("simp relies on `{}` (core/loop.core) with its statement there; this one differs", name));
            }
            if env.theorems.iter().any(|(n, _)| *n == name) {
                continue;
            }
            if env.open.lemmas.iter().any(|(n, _)| *n == name) {
                if !open.contains(&name) {
                    open.push(name);
                }
                continue;
            }
            return err(format!("simp relies on `{}` (core/loop.core): load it", name));
        }
        Ok(Seq { hyps, concl: goal.clone(), open })
    }

    fn gather(premises: &[&Seq]) -> (Vec<Term>, Vec<String>) {
        let mut hyps = Vec::new();
        let mut open = Vec::new();
        for p in premises {
            hyps = union(&hyps, &p.hyps);
            open = union(&open, &p.open);
        }
        (hyps, open)
    }

    /// A recursion equation of `nat_rec` for `t` (see `Logic::nat_rec_eq`);
    /// `m_nat` proves `m in omega` for the step case.
    /// `Γ ⊢ goal`, evaluated to true on concrete data (`Logic::eval_truth`)
    /// with the premises `lhs = value` as known values.
    pub fn eval_goal(env: &Env, lg: &Logic, premises: &[&Seq], goal: &Term) -> KResult<Seq> {
        env.check_wf(goal, 0)?;
        let known: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        let used = lg.eval_truth(env, goal, &known)?;
        let used: Vec<&Seq> = used.iter().map(|&i| premises[i]).collect();
        let (hyps, open) = Self::gather(&used);
        Ok(Seq { hyps, concl: goal.clone(), open })
    }

    /// `Γ ⊢ all x. x in set <-> x = c1 || .. || x = cn`, the members of
    /// `set` evaluated on concrete data (`Logic::eval_members`), using the
    /// premises `lhs = value` as known values (Γ: the used premises').
    pub fn members(env: &Env, lg: &Logic, set: &Term, premises: &[&Seq]) -> KResult<Seq> {
        env.check_wf(set, 0)?;
        let known: Vec<Term> = premises.iter().map(|p| p.concl.clone()).collect();
        let (concl, used) = lg.eval_members(env, set, &known)?;
        env.check_wf(&concl, 0)?;
        let used: Vec<&Seq> = used.iter().map(|&i| premises[i]).collect();
        let (hyps, open) = Self::gather(&used);
        Ok(Seq { hyps, concl, open })
    }

    pub fn nat_rec_eq(env: &Env, lg: &Logic, t: &Term, m_nat: Option<&Seq>) -> KResult<Seq> {
        env.check_wf(t, 0)?;
        let concl = lg.nat_rec_eq(env, t, m_nat.map(|s| &s.concl))?;
        Ok(match m_nat {
            Some(s) => Seq { hyps: s.hyps.clone(), concl, open: s.open.clone() },
            None => Seq { hyps: Vec::new(), concl, open: Vec::new() },
        })
    }

    /// A kernel theorem about literals or bytes, as a sequent.
    pub fn kernel(t: KResult<Thm>) -> KResult<Seq> {
        Ok(Seq::of_thm(&t?))
    }
}

/// `t` with every occurrence of the defined symbols `syms` unfolded,
/// repeatedly (definitions are not recursive, so this terminates).
pub fn unfold_all(env: &Env, t: &Term, syms: &[SymId]) -> Term {
    let mut unbounded = usize::MAX;
    unfold_all_in(env, t, syms, &mut unbounded).unwrap()
}

/// `unfold_all`, unless it visits more than `budget` subterms (unfolding
/// can grow a term exponentially: arithmetic's definitions).
pub fn unfold_all_bounded(env: &Env, t: &Term, syms: &[SymId], budget: usize) -> Option<Term> {
    let mut budget = budget;
    unfold_all_in(env, t, syms, &mut budget)
}

fn unfold_all_in(env: &Env, t: &Term, syms: &[SymId], budget: &mut usize) -> Option<Term> {
    *budget = budget.checked_sub(1)?;
    match t.node() {
        Node::App(s, args) => {
            let args: Vec<Term> = args.iter().map(|a| unfold_all_in(env, a, syms, budget)).collect::<Option<Vec<_>>>()?;
            if syms.contains(s) {
                if let SymKind::Defined { params, body } = &env.syms[*s as usize].kind {
                    let bf = env.binders_fn();
                    // an argument with bound variables of the context (the
                    // occurrence is under binders): placed under the body's
                    // binders shifted
                    let open = |p: &VarId, a: &Term| a.loose_depth(&bf) > env.vars[*p as usize].arity;
                    // the kernel's instantiation of the defining equation
                    let mut b = body.clone();
                    for (p, a) in params.iter().zip(&args) {
                        b = if open(p, a) { subst_open(env, &b, *p, a, 0) } else { b.subst_var(*p, a, &bf) };
                    }
                    // (the occurrence's label, if any, on the unfolded body)
                    let r = unfold_all_in(env, &b, syms, budget)?;
                    return Some(match t.label() {
                        Some(l) => r.with_label(Some(l.into())),
                        None => r,
                    });
                }
            }
            Some(t.with_args(args))
        }
        Node::Var(_, args) => Some(t.with_args(args.iter().map(|a| unfold_all_in(env, a, syms, budget)).collect::<Option<Vec<_>>>()?)),
        _ => Some(t.clone()),
    }
}

/// `t` with the chosen occurrences of the defined symbol `sym` (numbered from
/// 1 in `count`, outer before inner, left to right; all if `occ` is empty)
/// unfolded once (their bodies not unfolded further). For `Seq::conv`.
pub fn unfold_at(env: &Env, t: &Term, sym: SymId, occ: &[usize], count: &mut usize) -> Term {
    match t.node() {
        Node::App(s, args) if *s == sym => {
            *count += 1;
            if occ.is_empty() || occ.contains(count) {
                if let SymKind::Defined { params, body } = &env.syms[*s as usize].kind {
                    let bf = env.binders_fn();
                    let open = |p: &VarId, a: &Term| a.loose_depth(&bf) > env.vars[*p as usize].arity;
                    if !params.iter().zip(args.iter()).any(|(p, a)| open(p, a) && env.vars[*p as usize].arity > 0) {
                        let mut b = body.clone();
                        for (p, a) in params.iter().zip(args.iter()) {
                            b = if open(p, a) { subst_open(env, &b, *p, a, 0) } else { b.subst_var(*p, a, &bf) };
                        }
                        return match t.label() {
                            Some(l) => b.with_label(Some(l.into())),
                            None => b,
                        };
                    }
                }
            }
            t.with_args(args.iter().map(|a| unfold_at(env, a, sym, occ, count)).collect())
        }
        Node::App(_, args) | Node::Var(_, args) => t.with_args(args.iter().map(|a| unfold_at(env, a, sym, occ, count)).collect()),
        _ => t.clone(),
    }
}

/// `t` with the variable `v` (k parameters) replaced by `a`, a term with
/// bound variables of the context: at binder depth `d` in `t`, an
/// occurrence `v(x1, .., xk)` becomes `a` with its parameters the xi and
/// its context's variables shifted by d.
fn subst_open(env: &Env, t: &Term, v: VarId, a: &Term, d: u32) -> Term {
    let bf = env.binders_fn();
    match t.node() {
        Node::Var(w, xs) if *w == v => {
            let xs: Vec<Term> = xs.iter().map(|x| subst_open(env, x, v, a, d)).collect();
            let r = open_inst(env, a, &xs, d, 0);
            match t.label() {
                Some(l) => r.with_label(Some(l.into())),
                None => r,
            }
        }
        Node::Var(_, xs) => t.with_args(xs.iter().map(|x| subst_open(env, x, v, a, d)).collect()),
        Node::App(s, xs) => t.with_args(xs.iter().enumerate().map(|(i, x)| subst_open(env, x, v, a, d + bf(*s, i))).collect()),
        _ => t.clone(),
    }
}

/// `a` (at depth `dd` within it) with its parameters (the k loose bound
/// variables below its context's: parameter j is BVar(k - 1 - j)) the
/// terms `xs` (at the site, depth d in the body) and its context's bound
/// variables lowered by k and shifted by d.
fn open_inst(env: &Env, a: &Term, xs: &[Term], d: u32, dd: u32) -> Term {
    let bf = env.binders_fn();
    let k = xs.len() as u32;
    match a.node() {
        Node::BVar(i) if *i < dd => a.clone(),
        Node::BVar(i) => {
            let j = i - dd;
            if j < k {
                xs[(k - 1 - j) as usize].shift(dd, 0, &bf).labelled_as(a)
            } else {
                Term::bvar(j - k + d + dd)
            }
        }
        Node::App(s, ys) => a.with_args(ys.iter().enumerate().map(|(i, y)| open_inst(env, y, xs, d, dd + bf(*s, i))).collect()),
        Node::Var(_, ys) => a.with_args(ys.iter().map(|y| open_inst(env, y, xs, d, dd)).collect()),
        _ => a.clone(),
    }
}

/// The symbol `name`, if it is a defined one.
pub fn defined_sym(env: &Env, name: &str) -> KResult<SymId> {
    match env.sym_by_name.get(name) {
        Some(&s) if matches!(env.syms[s as usize].kind, SymKind::Defined { .. }) => Ok(s),
        Some(_) => err(format!("`{}` is not a defined symbol", name)),
        None => err(format!("unknown symbol `{}`", name)),
    }
}
