//! `mem_read` / `mem`: memory reads through writes, and predicates the
//! bytes do not matter to.
//!
//! A read is unfolded by the registered views (`mem_view NAME`: equations
//! such as `rd64(vm, a) = bits_of_int(64, bytes_at(vm, a, 8))` and
//! `wr64(vm, a, v) = fn_update(vm, "bytes", store_le(..))`), each
//! `bytes_at` of a written memory resolved by the kernel's `mem_read` (the
//! writes' places decided by `arith` from the facts given), and the value
//! cleaned (a word's own value back from its digits). A predicate of a
//! written memory is unfolded the same way and rewritten by the registered
//! frames (`mem_frame NAME`: `P(fn_update(vm, "bytes", X), ..) = P(vm,
//! ..)`), then closed by the facts. A read that does not resolve (a write
//! not placed, bytes of an unknown memory) stays as it is: the goal may
//! not need it (a read in a value written), else its reason is reported.
//!
//! Untrusted: views and frames are proven facts applied by rsimp's
//! rewriting; the reads are the kernel's `mem_read`; the clean-up is
//! `arith`.

use super::*;
use rsimp::Rules;
use std::rc::Rc;

/// a proof's memory-rule state: the rule sets built (0: views, 1: views
/// and frames, 2: step's), the facts' unfolding equations (by the views)
#[derive(Default)]
pub(crate) struct MemCache {
    pub(crate) rules: std::collections::HashMap<u8, Rc<Rules>>,
    unfold: std::collections::HashMap<Term, Seq>,
    /// a premise simplified by step's own rules (`mem_discharge`)
    premise_eq: std::collections::HashMap<(Term, bool), Seq>,
    /// `mem` goals not shown from these facts (the facts' hash)
    mem_failed: std::collections::HashSet<(Term, u64)>,
    /// the reads left unresolved (why), for a failing goal's message
    skipped: Vec<String>,
    /// the values read a step left unresolved (why), for its message
    pub(crate) value_failed: Vec<String>,
}

impl State {
    /// the views (and the frames) as rsimp rules, alone
    fn mem_rules(&self, env: &mut Env, lg: &Logic, frames: bool) -> KResult<Rc<Rules>> {
        let k = frames as u8;
        if let Some(r) = self.mem_cache.borrow().rules.get(&k) {
            r.reset();
            return Ok(r.clone());
        }
        let mut names: Vec<String> = env.mem_views.clone();
        if frames {
            names.extend(env.mem_frames.clone());
        }
        let mut args: Vec<Arg> = names.into_iter().map(|n| Arg::Proof(PE::Ref(n))).collect();
        args.push(Arg::Proof(PE::Ref("only".into())));
        let r = Rc::new(self.rsimp_rules(env, lg, &args)?);
        self.mem_cache.borrow_mut().rules.insert(k, r.clone());
        Ok(r)
    }

    /// `t = u`, t unfolded by the views (remembered)
    pub(crate) fn mem_unfold_eq(&self, env: &mut Env, lg: &Logic, t: &Term) -> KResult<Seq> {
        if let Some(e) = self.mem_cache.borrow().unfold.get(t) {
            return Ok(e.clone());
        }
        let rs = self.mem_rules(env, lg, false)?;
        let e = self.rsimp_eq(env, lg, t, &rs, 0)?;
        self.mem_cache.borrow_mut().unfold.insert(t.clone(), e.clone());
        Ok(e)
    }

    /// a fact unfolded by the views
    pub(crate) fn mem_unfold(&self, env: &mut Env, lg: &Logic, f: &Seq) -> Seq {
        let Ok(e) = self.mem_unfold_eq(env, lg, f.concl()) else { return f.clone() };
        if rhs_of(env, e.concl()) == *f.concl() {
            return f.clone();
        }
        Seq::rewrite(env, &e, f).unwrap_or_else(|_| f.clone())
    }

    /// `t = r`: t's reads resolved through their memories' writes (see the
    /// module docs); r is t if nothing applies. Lenient (a `mem` goal): a
    /// read that does not resolve left as it is; else an error
    pub(crate) fn mem_read_eq(&self, env: &mut Env, lg: &Logic, t: &Term, facts: &[Seq], frames: bool, lenient: bool) -> KResult<Seq> {
        let rs = self.mem_rules(env, lg, frames)?;
        let mut e = self.rsimp_eq(env, lg, t, &rs, 0)?;
        // (the facts in the same terms: unfolded too)
        let mut all: Vec<Seq> = Vec::new();
        for f in facts {
            all.push(self.mem_unfold(env, lg, f));
        }
        let facts = &all[..];
        let refs: Vec<&Seq> = facts.iter().collect();
        let g = |n: &str| env.sym_by_name.get(n).copied();
        let (bytes_at, fn_update, store_le, app) = (g("gimple.bytes_at"), g("fn_update"), g("x86_64_linux.store_le"), g("app"));
        // (a memory's bytes X with no write on them -- not a store, not
        // another memory's bytes: the read is already of them)
        let bare = |m: &Term| match m.node() {
            Node::App(h, b) if Some(*h) == fn_update && b.len() == 3 && matches!(b[1].node(), Node::Bytes(k) if &**k == b"bytes") => match b[2].node() {
                Node::App(s, c) => !(Some(*s) == store_le || (Some(*s) == app && c.len() == 2)),
                _ => true,
            },
            _ => false,
        };
        // each read of a written memory, through its writes (those that do
        // not resolve left as they are)
        let mut left: Vec<Term> = Vec::new();
        for _ in 0..1000 {
            let rhs = rhs_of(env, e.concl());
            let Some(u) = find(env, &rhs, &|x: &Term| match x.node() {
                Node::App(f, a) if Some(*f) == bytes_at && a.len() == 3 => {
                    !left.contains(x) && matches!(a[0].node(), Node::App(h, _) if Some(*h) == fn_update) && !bare(&a[0])
                }
                _ => false,
            }) else {
                break;
            };
            let r = match Seq::mem_read(env, lg, &refs, &u) {
                Ok(r) => r,
                Err(e) if !lenient => return Err(e),
                Err(KernelError(why)) => {
                    let mut c = self.mem_cache.borrow_mut();
                    if !c.skipped.contains(&why) {
                        c.skipped.push(why);
                    }
                    left.push(u);
                    continue;
                }
            };
            e = rewrite_rhs(env, &r, &e)?;
            // (cleaned at once: the value may be another read's address)
            e = self.mem_clean(env, lg, e, facts)?;
        }
        self.mem_clean(env, lg, e, facts)
    }

    /// a read's value cleaned: `bits_of_int(8n, v mod 256^n)` to v (or to
    /// `bits_of_int(8n, v)`), the digits of 0 to 0
    fn mem_clean(&self, env: &mut Env, lg: &Logic, mut e: Seq, facts: &[Seq]) -> KResult<Seq> {
        let g = |n: &str| env.sym_by_name.get(n).copied();
        let (boi, imod, idiv, ipow) = (g("bits_of_int"), g("int_mod"), g("int_div"), g("int_pow"));
        let nat_of = |t: &Term| match t.node() {
            Node::Nat(n) => n.to_u128(),
            _ => None,
        };
        let mut done: Vec<Term> = Vec::new();
        for _ in 0..1000 {
            let rhs = rhs_of(env, e.concl());
            // bits_of_int(K, int_mod(v, int_pow(256, n))), K = 8n
            let word = find(env, &rhs, &|x: &Term| {
                !done.contains(x)
                    && matches!(x.node(), Node::App(f, a) if Some(*f) == boi && a.len() == 2
                        && matches!(a[1].node(), Node::App(m, b) if Some(*m) == imod && b.len() == 2
                            && matches!(b[1].node(), Node::App(p, c) if Some(*p) == ipow && c.len() == 2 && nat_of(&c[0]) == Some(256)
                                && nat_of(&a[0]).is_some_and(|k| Some(k) == nat_of(&c[1]).map(|n| 8 * n)))))
            });
            // int_mod(int_div(0, int_pow(256, d)), int_pow(256, m))
            let zero = find(env, &rhs, &|x: &Term| {
                !done.contains(x)
                    && matches!(x.node(), Node::App(m, a) if Some(*m) == imod && a.len() == 2
                        && matches!(a[0].node(), Node::App(d, b) if Some(*d) == idiv && b.len() == 2 && nat_of(&b[0]) == Some(0)))
            });
            let Some((w, cands, extra)) = (match (word, zero) {
                (Some(w), _) => {
                    let Node::App(_, a) = w.node() else { unreachable!() };
                    let Node::App(_, b) = a[1].node() else { unreachable!() };
                    let v = b[0].clone();
                    let k = a[0].clone();
                    let cands = vec![v.clone(), Term::app(boi.unwrap(), vec![k, v])];
                    Some((w, cands, Vec::new()))
                }
                (None, Some(z)) => {
                    // (256^d > 0: pow256_pos, d a natural)
                    let Node::App(_, a) = z.node() else { unreachable!() };
                    let Node::App(_, b) = a[0].node() else { unreachable!() };
                    let mut extra = Vec::new();
                    if let Node::App(_, c) = b[1].node() {
                        let d = c[1].clone();
                        let omega = Term::app(g("omega").unwrap(), vec![]);
                        let d_nat = Term::app(lg.in_, vec![d.clone(), omega]);
                        let refs: Vec<&Seq> = facts.iter().collect();
                        if let (Ok(hd), Some(pp)) = (rel_arith(env, lg, &refs, &d_nat), facts::seq_of(env, "pow256_pos")) {
                            if let Ok(p) = Seq::all_elim(env, lg, &pp, &d).and_then(|p| Seq::mp(env, &p, &hd)) {
                                extra.push(p);
                            }
                        }
                    }
                    Some((z, vec![Term::nat(sl_kernel::Nat::from_u128(0))], extra))
                }
                _ => None,
            }) else {
                break;
            };
            done.push(w.clone());
            let mut ps: Vec<Seq> = facts.to_vec();
            ps.extend(extra);
            let refs: Vec<&Seq> = ps.iter().collect();
            for c in cands {
                let goal = Term::app(env.builtins.eq, vec![w.clone(), c]);
                if let Ok(p) = rel_arith(env, lg, &refs, &goal) {
                    e = rewrite_rhs(env, &p, &e)?;
                    break;
                }
            }
        }
        Ok(e)
    }

    /// `mem(p..)`: the goal -- an equation of reads (both sides resolved,
    /// then equal, or equal by `arith`), or a predicate of written memories
    /// (views and frames to the facts' memories, then by the facts)
    pub(crate) fn mem_goal(&self, env: &mut Env, lg: &Logic, goal: &Term, facts: &[Seq]) -> KResult<Seq> {
        self.mem_cache.borrow_mut().skipped.clear();
        self.mem_goal_1(env, lg, goal, facts).map_err(|KernelError(m)| {
            let sk = &self.mem_cache.borrow().skipped;
            if sk.is_empty() {
                KernelError(m)
            } else {
                KernelError(format!("{m}\n  reads left unresolved:\n    {}", sk.join("\n    ")))
            }
        })
    }

    fn mem_goal_1(&self, env: &mut Env, lg: &Logic, goal: &Term, facts: &[Seq]) -> KResult<Seq> {
        let refs: Vec<&Seq> = facts.iter().collect();
        if let Some((l, r)) = eq_sides(env, goal) {
            let el = self.mem_read_eq(env, lg, &l, facts, false, true)?;
            let er = self.mem_read_eq(env, lg, &r, facts, false, true)?;
            let (l2, r2) = (rhs_of(env, el.concl()), rhs_of(env, er.concl()));
            let mid = if l2 == r2 {
                Seq::refl(env, &l2)?
            } else {
                let g2 = Term::app(env.builtins.eq, vec![l2.clone(), r2.clone()]);
                rel_arith(env, lg, &refs, &g2).map_err(|_| {
                    let p = Printer::new(env);
                    KernelError(format!("mem: the sides resolve to `{}` and `{}`, not shown equal", p.short(&l2), p.short(&r2)))
                })?
            };
            // l = l2 = r2 = r
            let s = Seq::trans(env, &el, &mid)?;
            return Seq::trans(env, &s, &Seq::sym(env, &er)?);
        }
        let e = self.mem_read_eq(env, lg, goal, facts, true, true)?;
        let g2 = rhs_of(env, e.concl());
        let mut p = facts.iter().find(|f| f.concl() == &g2).cloned();
        // (a fact of the same normal form)
        if p.is_none() {
            for f in facts {
                if matches!(f.concl().node(), Node::App(h, _) if Some(*h) == head_sym(&g2)) {
                    if let Ok(ef) = self.mem_read_eq(env, lg, f.concl(), facts, true, true) {
                        if rhs_of(env, ef.concl()) == g2 {
                            p = Some(Seq::rewrite(env, &ef, f)?);
                            break;
                        }
                    }
                }
            }
        }
        let p = match p {
            Some(f) => f,
            None => Seq::taut(env, lg, &refs, &g2).or_else(|_| rel_arith(env, lg, &refs, &g2)).map_err(|_| {
                KernelError(format!("mem: the goal resolves to `{}`, not shown by the facts", Printer::new(env).short(&g2)))
            })?,
        };
        Seq::rewrite(env, &Seq::sym(env, &e)?, &p)
    }
}

/// e: `t = rhs` rewritten by r: `u = v` in rhs only (t may be u itself, a
/// read resolved)
fn rewrite_rhs(env: &Env, r: &Seq, e: &Seq) -> KResult<Seq> {
    fn count(t: &Term, pat: &Term) -> usize {
        if t == pat {
            return 1;
        }
        match t.node() {
            Node::App(_, a) | Node::Var(_, a) => a.iter().map(|x| count(x, pat)).sum(),
            _ => 0,
        }
    }
    let (u, _) = eq_sides(env, r.concl()).ok_or_else(|| KernelError("mem: not an equation".into()))?;
    let (l, rr) = eq_sides(env, e.concl()).ok_or_else(|| KernelError("mem: not an equation".into()))?;
    let (cl, cr) = (count(&l, &u), count(&rr, &u));
    if cl == 0 || cr == 0 {
        return Seq::rewrite(env, r, e);
    }
    let occ: Vec<usize> = (cl + 1..=cl + cr).collect();
    Seq::rewrite_at(env, r, e, &occ)
}

/// `goal` by arith from the facts mentioning its terms
/// (`Logic::arith_relevant`: the narrow choice, else the wide one)
pub(crate) fn rel_arith(env: &Env, lg: &Logic, facts: &[&Seq], goal: &Term) -> KResult<Seq> {
    let cs: Vec<Term> = facts.iter().map(|f| f.concl().clone()).collect();
    let narrow: Vec<&Seq> = lg.arith_relevant(env, &cs, goal, false).into_iter().map(|i| facts[i]).collect();
    Seq::arith(env, lg, &narrow, goal).or_else(|e| {
        let wide: Vec<&Seq> = lg.arith_relevant(env, &cs, goal, true).into_iter().map(|i| facts[i]).collect();
        if wide.len() == narrow.len() {
            return Err(e);
        }
        Seq::arith(env, lg, &wide, goal).map_err(|_| e)
    })
}

/// whether t mentions the symbol f
fn mentions(t: &Term, f: Option<SymId>) -> bool {
    match t.node() {
        Node::App(g, a) => Some(*g) == f || a.iter().any(|x| mentions(x, f)),
        _ => false,
    }
}

/// t's proper subterms, closed, outermost first, each once
fn subterms(t: &Term, out: &mut Vec<Term>) {
    if let Node::App(_, a) = t.node() {
        for x in a.iter() {
            if !out.contains(x) && !matches!(x.node(), Node::BVar(_)) {
                out.push(x.clone());
            }
        }
        for x in a.iter() {
            subterms(x, out);
        }
    }
}

fn head_sym(t: &Term) -> Option<SymId> {
    match t.node() {
        Node::App(h, _) => Some(*h),
        _ => None,
    }
}

/// the right side of an equation
pub(crate) fn rhs(env: &Env, t: &Term) -> Term {
    rhs_of(env, t)
}

/// the right side of an equation
fn rhs_of(env: &Env, t: &Term) -> Term {
    eq_sides(env, t).map(|(_, r)| r).unwrap_or_else(|| t.clone())
}

/// a literal's signed value `gimple.sval(T, n)` occurs in t
fn sval_lit(env: &Env, t: &Term) -> bool {
    match t.node() {
        Node::App(f, a) => {
            (a.len() == 2 && matches!(a[1].node(), Node::Nat(_)) && env.sym_by_name.get("gimple.sval") == Some(f)) || a.iter().any(|x| sval_lit(env, x))
        }
        Node::Var(_, a) => a.iter().any(|x| sval_lit(env, x)),
        _ => false,
    }
}

fn eq_sides(env: &Env, t: &Term) -> Option<(Term, Term)> {
    match t.node() {
        Node::App(f, a) if *f == env.builtins.eq && a.len() == 2 => Some((a[0].clone(), a[1].clone())),
        _ => None,
    }
}

/// a closed subterm with property p, innermost first
fn find(env: &Env, t: &Term, p: &dyn Fn(&Term) -> bool) -> Option<Term> {
    if let Node::App(_, a) = t.node() {
        for x in a.iter() {
            if let Some(r) = find(env, x, p) {
                return Some(r);
            }
        }
    }
    (p(t) && t.loose_depth(&env.binders_fn()) == 0).then(|| t.clone())
}

impl State {
    /// an operation's lemma (`all xs. H1 -> .. -> g.det(P, S, O)`) at the
    /// operation p from the state s: its variables by matching P, S; its
    /// premises discharged (`mem_discharge`)
    pub(crate) fn mem_lemma_inst(&self, env: &mut Env, lg: &Logic, lemma: &Seq, p: &Term, s: &Term, using: &[Seq]) -> KResult<Seq> {
        let det = env.sym_by_name.get("g.det").copied();
        let (inst, concl) = open_lemma(env, lg, lemma)?;
        let (pp, sp) = match concl.node() {
            Node::App(f, a) if Some(*f) == det && a.len() == 3 => (a[0].clone(), a[1].clone()),
            _ => return err("step: a `with` lemma not concluding `g.det(P, S, O)`"),
        };
        let mut binds = Vec::new();
        if !pmatch(env, &pp, p, &inst.1, &mut binds) || !pmatch(env, &sp, s, &inst.1, &mut binds) {
            let pr = Printer::new(env);
            return err(format!("step: the lemma's operation `{}` does not match `{}`", pr.short(&pp), pr.short(p)));
        }
        let mut l = inst.0;
        for (v, t) in &binds {
            l = Seq::inst(env, &l, *v, t)?;
        }
        if let Some(v) = inst.1.iter().find(|v| !binds.iter().any(|(w, _)| w == *v)) {
            return err(format!("step: the lemma's `{}` not determined by the operation", env.var(*v).name));
        }
        self.mem_discharge_all(env, lg, l, using, 0)
    }

    /// a value read `v = v'`: v's record fields simplified, then its reads
    /// resolved when that leaves no read (a value written), else v's
    /// memories past their writes when the reads resolve the same (a value
    /// the writes do not touch); None if neither
    pub(crate) fn mem_value(&self, env: &mut Env, lg: &Logic, v: &Term, using: &[Seq]) -> Option<Seq> {
        let srs = self.step_rules(env, lg).ok()?;
        let es = self.rsimp_eq(env, lg, v, &srs, 0).ok()?;
        let vs = rhs_of(env, es.concl());
        let er = match self.mem_read_eq(env, lg, &vs, using, false, false) {
            Ok(er) => er,
            Err(KernelError(why)) => {
                let mut c = self.mem_cache.borrow_mut();
                if !c.value_failed.contains(&why) {
                    c.value_failed.push(why);
                }
                return None;
            }
        };
        let r = rhs_of(env, er.concl());
        let bytes_at = env.sym_by_name.get("gimple.bytes_at").copied();
        if r == vs {
            return None;
        }
        if !mentions(&r, bytes_at) {
            return Seq::trans(env, &es, &er).ok();
        }
        // v's memories past their writes, or (a value written) a term of v
        let Node::App(f, a) = vs.node() else { return None };
        let mut a0 = Vec::new();
        for x in a.iter() {
            a0.push(self.mem_strip(env, lg, x));
        }
        let e = Seq::trans(env, &es, &er).ok()?;
        let v0 = Term::app(*f, a0);
        if v0 != vs {
            if let Ok(e0) = self.mem_read_eq(env, lg, &v0, using, false, false) {
                if rhs_of(env, e0.concl()) == r {
                    return Seq::trans(env, &e, &Seq::sym(env, &e0).ok()?).ok();
                }
            }
        }
        // (a term of v unfolding to r: no write in it, so no read to resolve)
        let fn_update = env.sym_by_name.get("fn_update").copied();
        let mut subs = Vec::new();
        subterms(&vs, &mut subs);
        for c in subs {
            if matches!(c.node(), Node::Nat(_) | Node::Bytes(_)) {
                continue;
            }
            let Ok(ec) = self.mem_unfold_eq(env, lg, &c) else { continue };
            let u = rhs_of(env, ec.concl());
            if u == r && !mentions(&u, fn_update) {
                return Seq::trans(env, &e, &Seq::sym(env, &ec).ok()?).ok();
            }
        }
        None
    }

    /// x past its writes: while x = f(y, ..) is by the views an update of
    /// y, y
    fn mem_strip(&self, env: &mut Env, lg: &Logic, x: &Term) -> Term {
        let fn_update = env.sym_by_name.get("fn_update").copied();
        let Ok(rs) = self.mem_rules(env, lg, false) else { return x.clone() };
        let mut x = x.clone();
        loop {
            let Node::App(_, a) = x.node() else { return x };
            let Some(y) = a.first().cloned() else { return x };
            let nx = self.rsimp_eq(env, lg, &x, &rs, 0).map(|e| rhs_of(env, e.concl()));
            let ny = self.rsimp_eq(env, lg, &y, &rs, 0).map(|e| rhs_of(env, e.concl()));
            match (nx, ny) {
                (Ok(nx), Ok(ny)) if matches!(nx.node(), Node::App(u, b) if Some(*u) == fn_update && b.len() == 3 && b[0] == ny) => x = y,
                _ => return x,
            }
        }
    }

    /// `s`'s premises discharged in order
    fn mem_discharge_all(&self, env: &mut Env, lg: &Logic, mut s: Seq, using: &[Seq], depth: usize) -> KResult<Seq> {
        while let Node::App(i, a) = s.concl().node() {
            if *i != env.builtins.imp {
                break;
            }
            let h = a[0].clone();
            let p = self.mem_discharge(env, lg, &h, using, depth)?;
            s = Seq::mp(env, &s, &p)?;
        }
        Ok(s)
    }

    /// h with its literals' signed values `gimple.sval(T, n)` written as
    /// the literals (`premise_rules`): `h = h'`, if any
    fn lit_form(&self, env: &mut Env, lg: &Logic, h: &Term) -> KResult<Option<Seq>> {
        if !sval_lit(env, h) || facts::seq_of(env, "g.sval64_lit").is_none() {
            return Ok(None);
        }
        let cached = self.mem_cache.borrow().premise_eq.get(&(h.clone(), true)).cloned();
        let e = match cached {
            Some(e) => e,
            None => {
                let srs = self.premise_rules(env, lg)?;
                let e = self.rsimp_eq(env, lg, h, &srs, 0)?;
                self.mem_cache.borrow_mut().premise_eq.insert((h.clone(), true), e.clone());
                e
            }
        };
        Ok(if &rhs_of(env, e.concl()) == h { None } else { Some(e) })
    }

    /// a premise h: a fact given (also as h with its literal offsets'
    /// signed values written as the literals, as facts state them), by a
    /// closure fact (backward), by `mem`, or by arith / taut from the facts
    /// given
    pub(crate) fn mem_discharge(&self, env: &mut Env, lg: &Logic, h: &Term, using: &[Seq], depth: usize) -> KResult<Seq> {
        if let Some(f) = using.iter().find(|f| f.concl() == h) {
            return Ok(f.clone());
        }
        let lit = self.lit_form(env, lg, h)?;
        if let Some(e) = &lit {
            let h2 = rhs_of(env, e.concl());
            if let Some(f) = using.iter().find(|f| f.concl() == &h2) {
                return Seq::rewrite(env, &Seq::sym(env, e)?, f);
            }
        }
        // a conjunction (`g.mem_defined`: not null, in range, usable): each part
        if let Node::App(c, a) = h.node() {
            if env.sym_by_name.get("and") == Some(c) && a.len() == 2 {
                if let (Ok(l), Ok(r)) = (self.mem_discharge(env, lg, &a[0], using, depth), self.mem_discharge(env, lg, &a[1], using, depth)) {
                    if let Ok(p) = Seq::taut(env, lg, &[&l, &r], h) {
                        return Ok(p);
                    }
                }
            }
        }
        // (its record fields first; else as written -- the facts' terms may
        // be the unsimplified ones)
        let cached = self.mem_cache.borrow().premise_eq.get(&(h.clone(), false)).cloned();
        let e = match cached {
            Some(e) => e,
            None => {
                let srs = self.step_rules(env, lg)?;
                let e = self.rsimp_eq(env, lg, h, &srs, 0)?;
                self.mem_cache.borrow_mut().premise_eq.insert((h.clone(), false), e.clone());
                e
            }
        };
        let h2 = rhs_of(env, e.concl());
        if &h2 != h {
            if let Ok(p) = self.mem_discharge(env, lg, &h2, using, depth) {
                return Seq::rewrite(env, &Seq::sym(env, &e)?, &p);
            }
        }
        if depth < 40 {
            for name in env.mem_closures.clone() {
                let Some(l) = facts::seq_of(env, &name) else { continue };
                let (inst, concl) = open_lemma(env, lg, &l)?;
                // (a conjunct of its conclusion)
                for (k, part) in conj_parts(env, &concl).iter().enumerate() {
                    let mut binds = Vec::new();
                    if !pmatch(env, part, h, &inst.1, &mut binds) || inst.1.iter().any(|v| !binds.iter().any(|(w, _)| w == v)) {
                        continue;
                    }
                    let mut s = inst.0.clone();
                    for (v, t) in &binds {
                        s = Seq::inst(env, &s, *v, t)?;
                    }
                    let Ok(s) = self.mem_discharge_all(env, lg, s, using, depth + 1) else { continue };
                    if let Ok(c) = conj_get(env, &s, k + 1) {
                        if c.concl() == h {
                            return Ok(c);
                        }
                    }
                }
            }
        }
        // (arith and taut first: cheap, and most premises are bounds and
        // memberships; mem, normalizing the facts, after -- a failure
        // remembered for the same facts)
        let refs: Vec<&Seq> = using.iter().collect();
        if let Ok(p) = rel_arith(env, lg, &refs, h).or_else(|_| Seq::taut(env, lg, &refs, h)) {
            return Ok(p);
        }
        if let Some(e) = &lit {
            let h2 = rhs_of(env, e.concl());
            if let Ok(p) = rel_arith(env, lg, &refs, &h2) {
                return Seq::rewrite(env, &Seq::sym(env, e)?, &p);
            }
        }
        let fkey = {
            use std::hash::{Hash, Hasher};
            let mut st = std::collections::hash_map::DefaultHasher::new();
            for f in using {
                f.concl().hash(&mut st);
            }
            (h.clone(), st.finish())
        };
        let not_shown = |env: &Env| KernelError(format!("step: the premise `{}` not discharged (a `using` fact, a closure, mem, arith)", Printer::new(env).short(h)));
        if self.mem_cache.borrow().mem_failed.contains(&fkey) {
            return Err(not_shown(env));
        }
        match self.mem_goal(env, lg, h, using) {
            Ok(p) => Ok(p),
            Err(_) => {
                self.mem_cache.borrow_mut().mem_failed.insert(fkey);
                Err(not_shown(env))
            }
        }
    }
}

/// a lemma's parameters and leading `all`s as fresh variables (bits.rs's
/// opener): (the instance, its variables), its conclusion after the premises
fn open_lemma(env: &mut Env, lg: &Logic, l: &Seq) -> KResult<((Seq, Vec<VarId>), Term)> {
    let (s, vs, c) = super::bits::open_rule(env, lg, l)?;
    Ok(((s, vs), c))
}
