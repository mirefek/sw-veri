//! `rsimp`: Lean-like simplification -- rewriting with equations, left to
//! right, until none applies.
//!
//! The rules: the facts given (`rsimp(e1, .., D1, ..)`), then the registered
//! ones (`simp NAME` declarations; not with `only`). A fact may be an
//! equation `l = r`, an equivalence `a <-> b` (rewriting a to b), a
//! negation `!p` (p to `false`) or another proposition p (p to `true`);
//! under leading `all`s (its variables matched) and premises `H -> ..`
//! (each instance's premises shown: `is_prop(t)` of a syntactic
//! proposition, a fact of the context, or simp itself proving it `true`).
//! A definition D among the arguments is unfolded (its defining equation).
//!
//! Strategy: innermost first, the rules in order; an instance at a closed
//! subterm, each a kernel `rewrite` of the closed equation (every occurrence);
//! unconditional equations also under binders (`rewrite_under`). No
//! search: rules apply as found, never undone.
//!
//! Untrusted: every step is a kernel rule (`rewrite`, `rewrite_under`,
//! `inst`, `mp`, `conv`) or one of core/logic.core's theorems (`iff_eq`,
//! `eq_true`, `eq_false`, `true_i`).

use super::*;
use sl_kernel::Nat;

/// rewrites before giving up (a rule set that loops)
const LIMIT: usize = 2000;
/// nesting of simp proving a rule's premise
const DEPTH: usize = 2;

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Eq,
    Iff,
    True,
    False,
}

#[derive(Clone)]
pub(crate) struct Rule {
    name: String,
    /// the fact, its leading `all`s eliminated with the pattern variables
    seq: Seq,
    pvars: Vec<VarId>,
    prems: usize,
    kind: Kind,
    lhs: Term,
    /// `all xs. l = r` (unconditional, first-order): for `rewrite_under`
    general: Option<Seq>,
}

pub(crate) struct Rules {
    rules: Vec<Rule>,
    defs: Vec<SymId>,
    /// the facts given, for premises
    given: Vec<Seq>,
    /// (rule, term, depth) found not to apply, and premises tried: each
    /// tried once per rsimp call (a rewrite elsewhere does not change them)
    failed: std::cell::RefCell<std::collections::HashSet<(usize, Term, usize)>>,
    premises: std::cell::RefCell<std::collections::HashMap<(Term, usize), Option<Seq>>>,
}

impl Rules {
    /// The rules for another call: what failed and the premises tried
    /// forgotten (the facts may have grown since).
    pub(crate) fn reset(&self) {
        self.failed.borrow_mut().clear();
        self.premises.borrow_mut().clear();
    }
}

/// `name`'s instance at `ts` (its schematic variables in the order they
/// appear)
fn lemma(env: &Env, name: &str, ts: &[Term]) -> KResult<Seq> {
    let mut s = facts::seq_of(env, name).ok_or_else(|| KernelError(format!("rsimp: `{}` (core/logic.core) is not loaded", name)))?;
    let mut vs = Vec::new();
    s.concl().vars(&mut vs);
    for (v, t) in vs.iter().zip(ts) {
        s = Seq::inst(env, &s, *v, t)?;
    }
    Ok(s)
}

/// the value of an arithmetic term over numerals (natural results)
fn ground(env: &Env, t: &Term) -> Option<Nat> {
    match t.node() {
        Node::Nat(n) => Some(n.clone()),
        Node::App(s, a) => {
            let name = env.syms[*s as usize].name.as_str();
            match (name, a.len()) {
                ("pow2", 1) => {
                    let k = ground(env, &a[0])?.to_u64()?;
                    (k <= 4096).then(|| Nat::pow2(k))
                }
                ("int_add", 2) => Some(ground(env, &a[0])?.add(&ground(env, &a[1])?)),
                ("int_sub", 2) => ground(env, &a[0])?.sub(&ground(env, &a[1])?),
                ("int_mul", 2) => Some(ground(env, &a[0])?.mul(&ground(env, &a[1])?)),
                ("int_div", 2) => Some(ground(env, &a[0])?.divmod(&ground(env, &a[1])?)?.0),
                ("int_mod", 2) => Some(ground(env, &a[0])?.divmod(&ground(env, &a[1])?)?.1),
                _ => None,
            }
        }
        _ => None,
    }
}

/// a comparison of arithmetic terms over numerals, decided
fn ground_cmp(env: &Env, t: &Term) -> Option<bool> {
    let Node::App(s, a) = t.node() else { return None };
    if a.len() != 2 {
        return None;
    }
    let name = env.syms[*s as usize].name.as_str();
    if !["int_lt", "int_le"].contains(&name) {
        return None;
    }
    let (x, y) = (ground(env, &a[0])?, ground(env, &a[1])?);
    Some(match name {
        "int_lt" => y.sub(&x).is_some_and(|d| !d.is_zero()),
        _ => y.sub(&x).is_some(),
    })
}

/// a comparison or a membership in `omega` / `bits(n)` / `int` (closed)
fn arith_goal(env: &Env, t: &Term) -> bool {
    let name = |s: &SymId| env.syms[*s as usize].name.as_str();
    arith_atom(env, t) && matches!(t.node(), Node::App(s, _) if ["int_lt", "int_le", "in"].contains(&name(s)))
}

/// the terms an arithmetic proposition is about: its subterms that are
/// not arithmetic operations, comparisons or numerals
fn arith_leaves(env: &Env, t: &Term, out: &mut Vec<Term>) {
    let ops = ["int_lt", "int_le", "int_add", "int_sub", "int_mul", "int_div", "int_mod", "in", "not", "ne", "omega", "bits", "int", "pow2", "int_pow", "bits_add", "bits_sub", "bits_of_int"];
    match t.node() {
        Node::App(s, a) if ops.contains(&env.syms[*s as usize].name.as_str()) || *s == env.builtins.eq => a.iter().for_each(|x| arith_leaves(env, x, out)),
        Node::Nat(_) | Node::Bytes(_) | Node::BVar(_) => {}
        _ => {
            if !out.contains(t) {
                out.push(t.clone());
            }
        }
    }
}

fn occurs(x: &Term, t: &Term) -> bool {
    t == x
        || match t.node() {
            Node::App(_, a) | Node::Var(_, a) => a.iter().any(|y| occurs(x, y)),
            _ => false,
        }
}

/// at most `n` nodes
fn small_term(t: &Term, n: usize) -> bool {
    fn go(t: &Term, left: &mut usize) -> bool {
        if *left == 0 {
            return false;
        }
        *left -= 1;
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => a.iter().all(|x| go(x, left)),
            _ => true,
        }
    }
    go(t, &mut n.clone())
}

/// a comparison, a membership in `omega` / `bits(n)` / `int`, an
/// equation, or a negation of one: what arith reads (closed)
fn arith_atom(env: &Env, t: &Term) -> bool {
    if t.loose_depth(&env.binders_fn()) > 0 {
        return false;
    }
    let name = |s: &SymId| env.syms[*s as usize].name.as_str();
    match t.node() {
        Node::App(s, a) if name(s) == "not" => arith_atom(env, &a[0]),
        Node::App(s, _) if ["int_lt", "int_le", "ne"].contains(&name(s)) || *s == env.builtins.eq => true,
        Node::App(s, a) if name(s) == "in" => matches!(a[1].node(), Node::App(k, _) if ["omega", "bits", "int"].contains(&name(k))),
        _ => false,
    }
}

/// distinct numeric or string literals
fn lit_ne(a: &Term, b: &Term) -> bool {
    matches!((a.node(), b.node()), (Node::Nat(x), Node::Nat(y)) if x != y) || matches!((a.node(), b.node()), (Node::Bytes(x), Node::Bytes(y)) if x != y)
}

fn eq_parts(env: &Env, t: &Term) -> Option<(Term, Term)> {
    match t.node() {
        Node::App(e, a) if *e == env.builtins.eq => Some((a[0].clone(), a[1].clone())),
        _ => None,
    }
}

impl State {
    /// The rules of `rsimp(args)`.
    pub(crate) fn rsimp_rules(&self, env: &mut Env, lg: &Logic, args: &[Arg]) -> KResult<Rules> {
        let mut rs = Rules { rules: Vec::new(), defs: Vec::new(), given: Vec::new(), failed: Default::default(), premises: Default::default() };
        let mut only = false;
        for a in args {
            match a {
                Arg::Proof(PE::Ref(n)) if n == "only" => only = true,
                Arg::Proof(PE::Ref(n)) if self.fact(env, n).is_err() && defined_sym(env, n).is_ok() => rs.defs.push(defined_sym(env, n)?),
                Arg::Proof(p) => {
                    let s = self.eval(env, lg, p)?;
                    let name = match p {
                        PE::Ref(n) => n.clone(),
                        _ => "a given fact".into(),
                    };
                    rs.given.push(s.clone());
                    match self.rule(env, lg, &name, s) {
                        Some(r) => rs.rules.push(r),
                        None => return err(format!("rsimp: `{}` is no rewrite rule", name)),
                    }
                }
                _ => return err("rsimp takes facts and definitions"),
            }
        }
        if !only {
            for n in env.simp_set.clone() {
                if let Some(s) = facts::seq_of(env, &n) {
                    if let Some(r) = self.rule(env, lg, &n, s) {
                        rs.rules.push(r);
                    }
                }
            }
        }
        Ok(rs)
    }

    /// `s` as a rewrite rule
    fn rule(&self, env: &mut Env, lg: &Logic, name: &str, s: Seq) -> Option<Rule> {
        let mut pvars = self.free_vars(&s);
        let mut s = s;
        while let Node::App(q, _) = s.concl().node() {
            if *q != lg.all {
                break;
            }
            let v = env.new_var(s.concl().binder_name().unwrap_or("x"), 0);
            s = Seq::all_elim(env, lg, &s, &Term::var(v, vec![])).ok()?;
            pvars.push(v);
        }
        let (mut c, mut prems) = (s.concl().clone(), 0);
        while let Ok((_, b)) = imp_parts(env, &c) {
            c = b;
            prems += 1;
        }
        let iff = env.sym_by_name.get("iff").copied();
        let not = env.sym_by_name.get("not").copied();
        let (kind, lhs) = match c.node() {
            Node::App(e, a) if *e == env.builtins.eq => (Kind::Eq, a[0].clone()),
            Node::App(e, a) if Some(*e) == iff => (Kind::Iff, a[0].clone()),
            Node::App(e, a) if Some(*e) == not => (Kind::False, a[0].clone()),
            _ => (Kind::True, c.clone()),
        };
        // (not a rule: a pattern matching anything)
        if matches!(lhs.node(), Node::Var(v, _) if pvars.contains(v)) {
            return None;
        }
        let general = if kind == Kind::Eq && prems == 0 && !pvars.is_empty() && pvars.iter().all(|v| env.vars[*v as usize].arity == 0) {
            let mut g = Some(s.clone());
            for v in pvars.iter().rev() {
                g = g.and_then(|g| Seq::gen(env, lg, &g, *v).ok());
            }
            g
        } else {
            None
        };
        Some(Rule { name: name.to_string(), seq: s, pvars, prems, kind, lhs, general })
    }

    /// `rule` at the closed term `t`: the equation `t = t'` (t' different)
    fn rule_at(&self, env: &mut Env, lg: &Logic, i: usize, rule: &Rule, t: &Term, rs: &Rules, depth: usize) -> KResult<Option<Seq>> {
        let mut binds = Vec::new();
        if !pmatch_at(env, &rule.lhs, t, &rule.pvars, &mut binds, 0, false) {
            return Ok(None);
        }
        // (matched before, its premises not shown: not again)
        let key = (i, t.clone(), depth);
        if rule.prems > 0 && rs.failed.borrow().contains(&key) {
            return Ok(None);
        }
        let r = self.rule_inst(env, lg, rule, t, binds, rs, depth)?;
        if r.is_none() && rule.prems > 0 {
            rs.failed.borrow_mut().insert(key);
        }
        Ok(r)
    }

    fn rule_inst(&self, env: &mut Env, lg: &Logic, rule: &Rule, t: &Term, binds: Vec<(VarId, Term)>, rs: &Rules, depth: usize) -> KResult<Option<Seq>> {
        let mut s = rule.seq.clone();
        for (v, x) in &binds {
            s = Seq::inst(env, &s, *v, x)?;
        }
        // (a variable not bound by the match: the rule does not apply)
        let mut vs = Vec::new();
        s.concl().vars(&mut vs);
        if rule.pvars.iter().any(|v| vs.contains(v)) {
            return Ok(None);
        }
        for _ in 0..rule.prems {
            let (h, _) = imp_parts(env, s.concl())?;
            match self.premise(env, lg, &h, rs, depth)? {
                Some(p) => s = Seq::mp(env, &s, &p)?,
                None => return Ok(None),
            }
        }
        let prop = |env: &Env, t: &Term| self.premise_known(env, lg, &Term::app(lg.is_prop, vec![t.clone()]), rs);
        let e = match rule.kind {
            Kind::Eq => s,
            Kind::Iff => {
                let (a, b) = match s.concl().node() {
                    Node::App(_, x) => (x[0].clone(), x[1].clone()),
                    _ => unreachable!(),
                };
                let (Some(pa), Some(pb)) = (prop(env, &a), prop(env, &b)) else { return Ok(None) };
                let l = lemma(env, "iff_eq", &[a, b])?;
                Seq::mp(env, &Seq::mp(env, &Seq::mp(env, &l, &pa)?, &pb)?, &s)?
            }
            Kind::True => {
                let a = s.concl().clone();
                let Some(pa) = prop(env, &a) else { return Ok(None) };
                Seq::mp(env, &Seq::mp(env, &lemma(env, "eq_true", &[a])?, &pa)?, &s)?
            }
            Kind::False => {
                let a = rule.lhs.clone();
                let a = match s.concl().node() {
                    Node::App(_, x) => x[0].clone(),
                    _ => a,
                };
                let Some(pa) = prop(env, &a) else { return Ok(None) };
                Seq::mp(env, &Seq::mp(env, &lemma(env, "eq_false", &[a])?, &pa)?, &s)?
            }
        };
        match eq_parts(env, e.concl()) {
            Some((l, r)) if l == *t && r != l => {
                // (RSIMP_TRACE: each rewrite and its rule)
                if std::env::var("RSIMP_TRACE").is_ok() {
                    let pp = Printer::new(env);
                    eprintln!("rsimp {}: {}  ~>  {}", rule.name, pp.short(&l), pp.short(&r));
                }
                Ok(Some(e))
            }
            _ => Ok(None),
        }
    }

    /// a premise from what is known: `is_prop` of a syntactic proposition,
    /// a fact given or of the context
    fn premise_known(&self, env: &Env, lg: &Logic, h: &Term, rs: &Rules) -> Option<Seq> {
        if let Node::App(p, a) = h.node() {
            if *p == lg.is_prop {
                if let Ok(s) = Seq::prop(env, lg, &a[0]) {
                    return Some(s);
                }
            }
        }
        rs.given.iter().chain(self.facts.iter().rev().map(|(_, s)| s)).find(|s| s.concl() == h).cloned()
    }

    /// a rule's premise: known, or simp shows it (not too deeply nested)
    fn premise(&self, env: &mut Env, lg: &Logic, h: &Term, rs: &Rules, depth: usize) -> KResult<Option<Seq>> {
        let key = (h.clone(), depth);
        if let Some(r) = rs.premises.borrow().get(&key) {
            return Ok(r.clone());
        }
        let t0 = std::time::Instant::now();
        let r = self.premise_(env, lg, h, rs, depth)?;
        if std::env::var("RSIMP_TRACE").is_ok() {
            eprintln!("rsimp premise {} ({:.3}s, depth {}): {}", if r.is_some() { "shown" } else { "not shown" }, t0.elapsed().as_secs_f64(), depth, Printer::new(env).short(h));
        }
        rs.premises.borrow_mut().insert(key, r.clone());
        Ok(r)
    }

    fn premise_(&self, env: &mut Env, lg: &Logic, h: &Term, rs: &Rules, depth: usize) -> KResult<Option<Seq>> {
        if let Some(s) = self.premise_known(env, lg, h, rs) {
            return Ok(Some(s));
        }
        if depth < DEPTH {
            if let Ok(s) = self.rsimp_close(env, lg, h, rs, depth + 1) {
                return Ok(Some(s));
            }
        }
        // (a comparison or a range: without variables, decided; else arith,
        // from the small arithmetic facts about its terms)
        if arith_goal(env, h) {
            let mut vs = Vec::new();
            h.vars(&mut vs);
            if vs.is_empty() {
                if let Ok(s) = Seq::simp_goal(env, lg, &[], h, &[], &[]) {
                    return Ok(Some(s));
                }
            }
            let mut leaves = Vec::new();
            arith_leaves(env, h, &mut leaves);
            let known: Vec<&Seq> = rs
                .given
                .iter()
                .chain(self.facts.iter().map(|(_, s)| s))
                .filter(|s| arith_atom(env, s.concl()) && small_term(s.concl(), 64) && leaves.iter().any(|l| occurs(l, s.concl())))
                .collect();
            if let Ok(s) = Seq::arith(env, lg, &known, h) {
                return Ok(Some(s));
            }
        }
        Ok(None)
    }

    /// the first rewrite in `t` (innermost first): `u = u'` for a closed
    /// subterm u
    fn site(&self, env: &mut Env, lg: &Logic, t: &Term, rs: &Rules, depth: usize) -> KResult<Option<Seq>> {
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => {
                for x in a.iter() {
                    if let Some(e) = self.site(env, lg, x, rs, depth)? {
                        return Ok(Some(e));
                    }
                }
            }
            Node::BVar(_) => return Ok(None),
            _ => {}
        }
        if t.loose_depth(&env.binders_fn()) > 0 {
            return Ok(None);
        }
        for (i, r) in rs.rules.iter().enumerate() {
            if let Some(e) = self.rule_at(env, lg, i, r, t, rs, depth)? {
                return Ok(Some(e));
            }
        }
        // (arithmetic on numerals: evaluated -- a value, or a comparison
        // decided -- and shown by arith)
        if !matches!(t.node(), Node::Nat(_)) {
            if let Some(v) = ground(env, t) {
                let eq = Term::app(env.builtins.eq, vec![t.clone(), Term::nat(v)]);
                return Ok(Some(Seq::arith(env, lg, &[], &eq).or_else(|_| Seq::simp_goal(env, lg, &[], &eq, &[], &[]))?));
            }
            if let Some(b) = ground_cmp(env, t) {
                let pa = Seq::prop(env, lg, t)?;
                return Ok(Some(if b {
                    let h = Seq::arith(env, lg, &[], t)?;
                    Seq::mp(env, &Seq::mp(env, &lemma(env, "eq_true", &[t.clone()])?, &pa)?, &h)?
                } else {
                    let not = env.sym_by_name["not"];
                    let h = Seq::arith(env, lg, &[], &Term::app(not, vec![t.clone()]))?;
                    Seq::mp(env, &Seq::mp(env, &lemma(env, "eq_false", &[t.clone()])?, &pa)?, &h)?
                }));
            }
        }
        // (distinct literals are unequal)
        if let Some((a, b)) = eq_parts(env, t) {
            if lit_ne(&a, &b) {
                let not = env.sym_by_name["not"];
                let ne = Seq::simp_goal(env, lg, &[], &Term::app(not, vec![t.clone()]), &[], &[])?;
                let pa = Seq::prop(env, lg, t)?;
                return Ok(Some(Seq::mp(env, &Seq::mp(env, &lemma(env, "eq_false", &[t.clone()])?, &pa)?, &ne)?));
            }
        }
        Ok(None)
    }

    /// `s` with the part `focus` picks of its conclusion simplified
    fn normalize(&self, env: &mut Env, lg: &Logic, mut s: Seq, focus: &dyn Fn(&Term) -> Term, rs: &Rules, depth: usize) -> KResult<Seq> {
        for _ in 0..LIMIT {
            if !rs.defs.is_empty() {
                let u = unfold_all(env, s.concl(), &rs.defs);
                if &u != s.concl() {
                    s = Seq::conv(env, &s, &u, &rs.defs)?;
                }
            }
            let t = focus(s.concl());
            if let Some(e) = self.site(env, lg, &t, rs, depth)? {
                s = Seq::rewrite(env, &e, &s)?;
                continue;
            }
            // (under binders: the unconditional equations)
            let mut moved = false;
            for r in rs.rules.iter().filter_map(|r| r.general.as_ref()) {
                if let Ok(s2) = Seq::rewrite_under(env, lg, r, &s, &[]) {
                    if s2.concl() != s.concl() {
                        s = s2;
                        moved = true;
                        break;
                    }
                }
            }
            if !moved {
                return Ok(s);
            }
        }
        err(format!("rsimp: more than {} rewrites (do the rules loop?)", LIMIT))
    }

    /// `goal = N`, N its normal form
    pub(crate) fn rsimp_eq(&self, env: &mut Env, lg: &Logic, goal: &Term, rs: &Rules, depth: usize) -> KResult<Seq> {
        let v = env.new_var("_simp", 0);
        let e0 = Term::app(env.builtins.eq, vec![Term::var(v, vec![]), goal.clone()]);
        let s = Seq::assume(env, e0.clone())?;
        let rhs = |t: &Term| match t.node() {
            Node::App(_, a) => a[1].clone(),
            _ => t.clone(),
        };
        let s = self.normalize(env, lg, s, &rhs, rs, depth)?;
        let s = Seq::inst(env, &s.discharge(env, &e0)?, v, goal)?;
        Seq::mp(env, &s, &Seq::refl(env, goal)?)
    }

    /// `goal`, by simplifying it to `true` (or to a known fact, or `a = a`)
    pub(crate) fn rsimp_close(&self, env: &mut Env, lg: &Logic, goal: &Term, rs: &Rules, depth: usize) -> KResult<Seq> {
        let e = self.rsimp_eq(env, lg, goal, rs, depth)?;
        let n = eq_parts(env, e.concl()).unwrap().1;
        let pn = match self.closes(env, lg, &n, rs) {
            Some(p) => p,
            None => {
                let pp = Printer::new(env);
                return err(format!("rsimp: the goal simplifies to `{}`", pp.short(&n)));
            }
        };
        Seq::rewrite(env, &Seq::sym(env, &e)?, &pn)
    }

    /// a proof of the simplified goal n, if it is trivial
    pub(crate) fn closes(&self, env: &Env, lg: &Logic, n: &Term, rs: &Rules) -> Option<Seq> {
        if env.sym_by_name.get("true").is_some_and(|t| matches!(n.node(), Node::App(s, a) if s == t && a.is_empty())) {
            return facts::seq_of(env, "true_i");
        }
        if let Some((a, b)) = eq_parts(env, n) {
            if a == b {
                return Seq::refl(env, &a).ok();
            }
        }
        self.premise_known(env, lg, n, rs)
    }

    /// the fact `s` simplified
    pub(crate) fn rsimp_fact(&self, env: &mut Env, lg: &Logic, s: Seq, rs: &Rules) -> KResult<Seq> {
        self.normalize(env, lg, s, &|t: &Term| t.clone(), rs, 0)
    }
}
