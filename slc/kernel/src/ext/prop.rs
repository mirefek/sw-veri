//! Propositions: which terms are known to be propositions (`is_prop`), and
//! propositional tautologies.
//!
//! Trusted extension. Relies on the prelude's axioms `imp_prop`, `eq_prop`,
//! `ex_prop`, `in_prop` and the definitions of `false`, `not`, `true`, `and`,
//! `or`, `iff`, `is_prop` (checked by name when used; see `Logic::new`).

use crate::env::{Env, KResult, KernelError, SymKind};
use crate::term::{Node, SymId, Term};

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

/// The prelude symbols the extensions reason about.
pub struct Logic {
    pub imp: SymId,
    pub eq: SymId,
    pub false_: SymId,
    pub ex: SymId,
    pub all: SymId,
    pub choose: SymId,
    pub in_: SymId,
    pub is_prop: SymId,
    /// programs `simp` keeps folded (`runs(P, ..)` not unfolded), for the
    /// duration of one `simp` step
    pub simp_keep: std::cell::RefCell<Vec<SymId>>,
}

impl Logic {
    /// Finds the prelude's logical symbols and checks that the axioms the
    /// extensions rely on are present.
    pub fn new(env: &Env) -> KResult<Logic> {
        let sym = |n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| KernelError(format!("extensions need `{}` (the prelude)", n)));
        for a in ["imp_prop", "eq_prop", "ex_prop", "in_prop", "ex_intro", "choose_spec", "eq_refl", "eq_subst", "false_elim"] {
            if !env.axioms.iter().any(|(n, _)| n == a) {
                return err(format!("extensions need the prelude axiom `{}`", a));
            }
        }
        Ok(Logic {
            imp: env.builtins.imp,
            eq: env.builtins.eq,
            false_: sym("false")?,
            ex: sym("ex")?,
            all: sym("all")?,
            choose: sym("choose")?,
            in_: sym("in")?,
            is_prop: sym("is_prop")?,
            simp_keep: Default::default(),
        })
    }

    /// `t` is syntactically a proposition: its head is `false`, `->`, `=`,
    /// `ex`, `in`, or a defined symbol whose body is (recursively).
    ///
    /// Soundness: `is_prop(false)` from `eq_refl`; `->`, `=`, `ex`, `in` by the
    /// axioms `imp_prop`, `eq_prop`, `ex_prop`, `in_prop`; a defined symbol
    /// by rewriting with its defining equation (`eq_subst`).
    pub fn prop_valued(&self, env: &Env, t: &Term) -> bool {
        match t.node() {
            Node::App(s, _) => self.sym_prop_valued(env, *s, 0),
            _ => false,
        }
    }

    fn sym_prop_valued(&self, env: &Env, s: SymId, depth: u32) -> bool {
        if [self.imp, self.eq, self.false_, self.ex, self.in_].contains(&s) {
            return true;
        }
        if depth > 64 {
            return false;
        }
        match &env.syms[s as usize].kind {
            SymKind::Defined { body, .. } => match body.node() {
                Node::App(h, _) => self.sym_prop_valued(env, *h, depth + 1),
                _ => false,
            },
            _ => false,
        }
    }

    /// `premises -> goal` is a classical propositional tautology.
    /// Connectives: `->`, `false`, and defined symbols whose bodies are built
    /// from connectives and their parameters only (`not`, `true`, `and`,
    /// `or`, `iff`); anything else is an atom.
    ///
    /// Soundness: for propositions (each `false` or `true`), `->` behaves as
    /// the truth table says (the axioms `imp_weaken`, `imp_chain`, `false_elim`
    /// and `imp_prop`), so a formula true in every row is provable by cases
    /// on its atoms. An atom `a` need not be a proposition: `true -> a` is one
    /// (`imp_prop`), and `a` and `true -> a` are interderivable (`imp_weaken`,
    /// and modus ponens with `true`), so they can be exchanged in a formula
    /// built from `->` and `false` (the proof of `dne_any` in
    /// core/logic.core does this for `!!a -> a`, following ji-trust's
    /// `not_not_impl`).
    pub fn tautology(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        if premises.contains(goal) {
            return Ok(());
        }
        // only the premises connected to the goal by shared atoms (the others
        // can be dropped: a weaker implication, still a tautology if shown)
        let mut premises: Vec<&Term> = premises.iter().collect();
        if premises.len() > 8 {
            let atoms_of = |t: &Term| -> KResult<Vec<Term>> {
                let mut a = Vec::new();
                self.prop_tree(env, t, &mut a, 0)?;
                Ok(a)
            };
            let mut near = atoms_of(goal)?;
            let mut rest: Vec<(&Term, Vec<Term>)> = premises.iter().map(|p| Ok((*p, atoms_of(p)?))).collect::<KResult<_>>()?;
            let mut kept = Vec::new();
            loop {
                let (hit, miss): (Vec<_>, Vec<_>) = rest.into_iter().partition(|(_, a)| a.is_empty() || a.iter().any(|x| near.contains(x)));
                rest = miss;
                if hit.is_empty() {
                    break;
                }
                for (p, a) in hit {
                    near.extend(a);
                    kept.push(p);
                }
            }
            premises = kept;
        }
        let mut f = goal.clone();
        for p in premises.iter().rev() {
            f = Term::app(self.imp, vec![(*p).clone(), f]);
        }
        let mut atoms: Vec<Term> = Vec::new();
        let tree = self.prop_tree(env, &f, &mut atoms, 0)?;
        match tree.falsifying_rows(atoms.len(), 20) {
            None => err("too many atoms for a truth table"),
            Some(rows) if rows.is_empty() => Ok(()),
            Some(_) => err("not a tautology"),
        }
    }

    /// The propositional structure of `t` over atoms.
    pub(crate) fn prop_tree(&self, env: &Env, t: &Term, atoms: &mut Vec<Term>, depth: u32) -> KResult<PTree> {
        if depth > 1000 {
            return err("formula too deep");
        }
        if let Node::App(s, args) = t.node() {
            if *s == self.imp {
                let a = self.prop_tree(env, &args[0], atoms, depth + 1)?;
                let b = self.prop_tree(env, &args[1], atoms, depth + 1)?;
                return Ok(PTree::Imp(Box::new(a), Box::new(b)));
            }
            if *s == self.false_ {
                return Ok(PTree::False);
            }
            if let Some(expanded) = self.connective(env, *s, args) {
                return self.prop_tree(env, &expanded, atoms, depth + 1);
            }
        }
        let i = match atoms.iter().position(|a| a == t) {
            Some(i) => i,
            None => {
                atoms.push(t.clone());
                atoms.len() - 1
            }
        };
        Ok(PTree::Atom(i))
    }

    /// A defined symbol whose body uses only `->`, `false`, other such
    /// symbols and its (non-binding) parameters: its expansion.
    fn connective(&self, env: &Env, s: SymId, args: &[Term]) -> Option<Term> {
        let SymKind::Defined { params, body } = &env.syms[s as usize].kind else { return None };
        if env.syms[s as usize].binders.iter().any(|&b| b > 0) || !self.is_connective_body(env, body, params, 0) {
            return None;
        }
        let mut t = body.clone();
        for (p, a) in params.iter().zip(args) {
            t = t.subst_var(*p, a, &env.binders_fn());
        }
        Some(t)
    }

    fn is_connective_body(&self, env: &Env, t: &Term, params: &[u32], depth: u32) -> bool {
        if depth > 64 {
            return false;
        }
        match t.node() {
            Node::Var(v, a) => a.is_empty() && params.contains(v),
            Node::App(s, a) if *s == self.imp => a.iter().all(|x| self.is_connective_body(env, x, params, depth + 1)),
            Node::App(s, a) if *s == self.false_ => a.is_empty(),
            Node::App(s, a) => match &env.syms[*s as usize].kind {
                SymKind::Defined { params: ps, body } if env.syms[*s as usize].binders.iter().all(|&b| b == 0) => {
                    self.is_connective_body(env, body, ps, depth + 1) && a.iter().all(|x| self.is_connective_body(env, x, params, depth + 1))
                }
                _ => false,
            },
            _ => false,
        }
    }
}

pub(crate) enum PTree {
    Atom(usize),
    False,
    Imp(Box<PTree>, Box<PTree>),
}

impl PTree {
    /// The rows (assignments to the atoms, as bits) that make the tree
    /// false. A row falsifies `p1 -> .. -> pk -> g` only if every pi is
    /// true and g false, so atomic pi (and negated ones, `a -> false`), and
    /// the atoms of g's own chain, have forced values; only the other atoms
    /// are enumerated (at most `max_free` of them, else None).
    pub(crate) fn falsifying_rows(&self, n_atoms: usize, max_free: usize) -> Option<Vec<u64>> {
        if n_atoms > 63 {
            return None;
        }
        let (mut mask, mut val) = (0u64, 0u64);
        let mut conflict = false;
        let mut force = |i: usize, b: bool, mask: &mut u64, val: &mut u64| {
            let bit = 1u64 << i;
            if *mask & bit != 0 {
                if (*val & bit != 0) != b {
                    conflict = true;
                }
            } else {
                *mask |= bit;
                if b {
                    *val |= bit;
                }
            }
        };
        // walk the chain: `t` must be false
        let mut t = self;
        loop {
            match t {
                PTree::Imp(p, rest) => {
                    // p must be true
                    match &**p {
                        PTree::Atom(i) => force(*i, true, &mut mask, &mut val),
                        PTree::Imp(a, f) if matches!(**f, PTree::False) => {
                            if let PTree::Atom(i) = **a {
                                force(i, false, &mut mask, &mut val);
                            }
                        }
                        _ => {}
                    }
                    t = rest;
                }
                PTree::Atom(i) => {
                    force(*i, false, &mut mask, &mut val);
                    break;
                }
                PTree::False => break,
            }
        }
        if conflict {
            return Some(Vec::new());
        }
        let free: Vec<usize> = (0..n_atoms).filter(|i| mask >> i & 1 == 0).collect();
        if free.len() > max_free {
            return None;
        }
        let mut rows = Vec::new();
        for k in 0u64..(1 << free.len()) {
            let mut row = val;
            for (j, i) in free.iter().enumerate() {
                if k >> j & 1 == 1 {
                    row |= 1 << i;
                }
            }
            if !self.eval(row) {
                rows.push(row);
            }
        }
        Some(rows)
    }

    pub(crate) fn eval(&self, row: u64) -> bool {
        match self {
            PTree::Atom(i) => row >> i & 1 == 1,
            PTree::False => false,
            PTree::Imp(a, b) => !a.eval(row) || b.eval(row),
        }
    }
}
