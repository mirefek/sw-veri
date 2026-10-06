//! `slc translate`: the certificate of a function's C1 by statement patterns
//! (docs/bridge-pattern-design.md). Not trusted: it writes a proof that
//! `slc kernel-check` checks, with proofs/translate.core's rules.
//!
//! It walks the function's decode facts (`FN.at_ADDR`, build/leaf_steps.core)
//! from the entry, alongside the spec's procedure (`SPEC_fun`):
//! - the spec's rest is reduced at its head, by one lemma instance per step:
//!   a definition's body, a let, a choice (a placeholder witness, which no
//!   machine value can match: a value the machine has can never be chosen
//!   arbitrarily), an operation (split on its definedness: undefined, the
//!   spec raises, which closes the case), a disjunct by its guard (a literal
//!   fact or the machine's branch condition), a block's end, a projection
//!   of a constructed outcome;
//! - each instruction is the instance of the rule for its pattern; a
//!   conditional branch splits the proof on its condition.
//! The rests are computed through the lemmas' own statements, so they are
//! the kernel's. Nothing is searched: an instruction without a rule, a spec
//! head without a reduction, a machine value the spec does not have, stop it
//! with an error naming the address.

use crate::commands::CResult;
use sl_kernel::syntax::{self, Printer};
use sl_kernel::{Env, Nat, Node, SymKind, Term, VarId};
use std::collections::{BTreeMap, BTreeSet, HashMap};

const USAGE: &str = "usage: slc translate FN SPEC PREFIX -o OUT.core FILE.core...";
const P64: u128 = 1 << 64;

/// A decode fact: at its address, `len` bytes decode to `tag(row, fields)`.
struct Insn {
    name: String,
    len: u128,
    row: u128,
    fields: Term,
    base: Term,
    code: Term,
}

/// The spec's side at a point: the procedure's rest, or (after its result)
/// the wrapper's rest, named, with the value returned.
#[derive(Clone)]
enum Spec {
    Proc(usize),
    Ret(Term, String),
}

/// A path's state at an address.
#[derive(Clone)]
struct St {
    a: u128,
    /// the registers written: register, bytes, value
    regs: Vec<(u128, u128, Term)>,
    /// their map's name
    rs: String,
    spec: Spec,
    /// the facts in scope: a branch's condition (or its negation), a
    /// defined operation's condition, by name
    hyps: Vec<(Term, String)>,
}

/// A proof of a point claim: `have` lines, then its expression.
struct Pf {
    lines: Vec<String>,
    expr: String,
}

/// A reduction of the spec's rest.
enum Red {
    /// to the rest `.0`, by the proof `.1` of `all o. runs(q2, W, o) ->
    /// runs(q, W, o)`, after the lines `.2`
    Q(usize, String, Vec<String>),
    /// the procedure's result
    Ret(Term),
    /// an operation defined under `cond`: ok to `ok.0` by `ok.1` (`{HC}` the
    /// condition's proof), raising to `ub.0` by `ub.1` (`{HN}` its negation's)
    Split { cond: Term, ok: (usize, String), ub: (usize, String) },
}

/// One step towards a disjunct whose guard holds.
enum Pick {
    L,
    R,
    And(Term, String),
}

struct Gen<'e> {
    env: &'e mut Env,
    /// the placeholders: values (`T`), choices (`Z`), the world `W`, ...
    names: Vec<(String, VarId)>,
    vals: Vec<(VarId, Term)>,
    zs: Vec<VarId>,
    qs: Vec<(String, Term)>,
    /// lets: the register maps, the wrapper's rests
    lets: Vec<(String, String)>,
    lemmas: HashMap<String, (Vec<VarId>, Term)>,
    insns: BTreeMap<u128, Insn>,
    hs: BTreeMap<u128, (u128, Term)>,
    imuls: BTreeSet<u128>,
    /// the per-immediate facts the rules take: an and's narrowing, a
    /// field's shift and mask
    narrows: BTreeSet<u128>,
    fields: BTreeSet<(u128, u128, u128)>,
    /// the result's bytes (the wrapper's gimple.result width)
    rbytes: u128,
    scratch: BTreeSet<u128>,
    base: String,
    code: String,
    prefix: String,
    kw: Term,
    w: Term,
    n: usize,
}

fn nat(t: &Term) -> Option<u128> {
    match t.node() {
        Node::Nat(n) => n.to_u128(),
        _ => None,
    }
}

fn lit(v: u128) -> Term {
    Term::nat(Nat::from_u128(v))
}

fn indent(lines: Vec<String>) -> Vec<String> {
    lines.into_iter().map(|l| format!("  {}", l)).collect()
}

impl<'e> Gen<'e> {
    fn name(&self, t: &Term) -> Option<&str> {
        match t.node() {
            Node::App(s, _) => Some(&self.env.syms[*s as usize].name),
            _ => None,
        }
    }

    /// `t` as `NAME(args)`
    fn app<'t>(&self, t: &'t Term, name: &str, n: usize) -> Option<&'t [Term]> {
        match t.node() {
            Node::App(s, a) if self.env.syms[*s as usize].name == name && a.len() == n => Some(a),
            _ => None,
        }
    }

    fn mk(&self, name: &str, args: Vec<Term>) -> Term {
        Term::app(self.env.sym_by_name[name], args)
    }

    fn print(&self, t: &Term) -> String {
        Printer::new(self.env).term(t)
    }

    fn lambda(&self, k: usize, t: &Term) -> String {
        Printer::new(self.env).lambda(k, t)
    }

    fn fresh(&mut self, p: &str) -> String {
        self.n += 1;
        format!("{}{}", p, self.n)
    }

    fn var(&mut self, name: &str) -> Term {
        let v = self.env.new_var(name, 0);
        self.names.push((name.to_string(), v));
        Term::var(v, vec![])
    }

    /// `pair(a, pair(b, .. rest))` as its n components (the last the rest)
    fn pairs(&self, t: &Term, n: usize) -> Option<Vec<Term>> {
        let mut out = Vec::new();
        let mut t = t.clone();
        for _ in 1..n {
            let a = self.app(&t, "pair", 2)?;
            out.push(a[0].clone());
            t = a[1].clone();
        }
        out.push(t);
        Some(out)
    }

    /// `tag(k, x)` with the literal k
    fn tag(&self, t: &Term) -> Option<(u128, Term)> {
        let a = self.app(t, "tag", 2)?;
        Some((nat(&a[0])?, a[1].clone()))
    }

    /// a record `fn_update(.. empty, "f", v)`: its fields
    fn record(&self, t: &Term) -> Option<BTreeMap<String, Term>> {
        let mut out = BTreeMap::new();
        let mut r = t.clone();
        while let Some(a) = self.app(&r, "fn_update", 3) {
            let Node::Bytes(b) = a[1].node() else { return None };
            out.entry(String::from_utf8(b.to_vec()).ok()?).or_insert(a[2].clone());
            r = a[0].clone();
        }
        self.app(&r, "empty", 0)?;
        Some(out)
    }

    /// a memory operand `tag(2, {seg, base, index, scale, disp})`
    fn memop(&self, t: &Term) -> Option<BTreeMap<String, Term>> {
        let (k, r) = self.tag(t)?;
        if k != 2 {
            return None;
        }
        self.record(&r)
    }

    /// `[rsp + d]`: the displacement
    fn rsp_mem(&self, t: &Term) -> Option<Term> {
        let m = self.memop(t)?;
        let base = self.tag(m.get("base")?)?;
        (nat(m.get("seg")?)? == 0 && base.0 == 2 && nat(&base.1)? == 4 && self.app(m.get("index")?, "none", 0).is_some() && nat(m.get("scale")?)? == 1)
            .then(|| m["disp"].clone())
    }

    /// The bound variables of `t` (at `depth`) renumbered by `f`; None if
    /// one has no image.
    fn remap(&self, t: &Term, depth: u32, f: &dyn Fn(u32) -> Option<u32>) -> Option<Term> {
        Some(match t.node() {
            Node::BVar(i) if *i >= depth => Term::bvar(f(i - depth)? + depth),
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.remap(x, depth, f)).collect::<Option<_>>()?),
            Node::App(s, a) => {
                let bs = &self.env.syms[*s as usize].binders;
                t.with_args(a.iter().zip(bs).map(|(x, &k)| self.remap(x, depth + k, f)).collect::<Option<_>>()?)
            }
        })
    }

    /// `t` under the binders `ctx` (outermost first) as a value of the
    /// parameters `params`; None if it uses a binder that is not one
    fn lam(&self, t: &Term, ctx: &[&str], params: &[&str]) -> Option<Term> {
        let (c, p) = (ctx.len() as u32, params.len() as u32);
        self.remap(t, 0, &|i| {
            if i >= c {
                return None;
            }
            let name = ctx[(c - 1 - i) as usize];
            params.iter().position(|q| *q == name).map(|j| p - 1 - j as u32)
        })
    }

    /// `t` with its names expanded
    fn expand(&self, t: &Term) -> Term {
        match t.node() {
            Node::Var(v, a) if a.is_empty() => match self.vals.iter().find(|x| x.0 == *v) {
                Some((_, e)) => self.expand(e),
                None => t.clone(),
            },
            Node::App(_, a) => t.with_args(a.iter().map(|x| self.expand(x)).collect()),
            _ => t.clone(),
        }
    }

    /// `t` with each subterm that is a named value replaced by its name
    /// (compared expanded: a value named before its parts were)
    fn canon(&self, t: &Term) -> Term {
        let known: Vec<(VarId, Term)> = self.vals.iter().map(|(v, e)| (*v, self.expand(e))).collect();
        self.canon_in(&self.expand(t), &known)
    }

    fn canon_in(&self, t: &Term, known: &[(VarId, Term)]) -> Term {
        let t2 = match t.node() {
            Node::App(_, a) => t.with_args(a.iter().map(|x| self.canon_in(x, known)).collect()),
            _ => t.clone(),
        };
        match known.iter().find(|(_, e)| e == t) {
            Some((v, _)) => Term::var(*v, vec![]),
            None => t2,
        }
    }

    /// A value's name (a new one for a new value); literals, constants and
    /// names stand for themselves.
    fn value(&mut self, t: &Term) -> Term {
        let t = self.canon(t);
        match t.node() {
            Node::Nat(_) | Node::Var(..) => return t,
            Node::App(_, a) if a.is_empty() => return t,
            _ => {}
        }
        let name = format!("T{}", self.vals.len());
        let v = self.env.new_var(&name, 0);
        self.names.push((name, v));
        self.vals.push((v, t));
        Term::var(v, vec![])
    }

    /// a literal's value (a constant defined as one, a sum of them)
    fn eval_lit(&self, t: &Term) -> Option<u128> {
        if let Some(n) = nat(t) {
            return Some(n);
        }
        if let Node::Var(v, _) = t.node() {
            return self.vals.iter().find(|x| x.0 == *v).and_then(|x| self.eval_lit(&x.1));
        }
        if let Some(a) = self.app(t, "int_add", 2) {
            return Some(self.eval_lit(&a[0])? + self.eval_lit(&a[1])?);
        }
        let Node::App(s, a) = t.node() else { return None };
        match &self.env.syms[*s as usize].kind {
            SymKind::Defined { params, body } if params.is_empty() && a.is_empty() => nat(body),
            _ => None,
        }
    }

    fn new_q(&mut self, t: Term) -> usize {
        self.qs.push((format!("Q{}", self.qs.len()), t));
        self.qs.len() - 1
    }

    fn reg(&self, st: &St, r: u128) -> Option<(u128, Term)> {
        st.regs.iter().rev().find(|x| x.0 == r).map(|x| (x.1, x.2.clone()))
    }

    fn need_reg(&self, st: &St, r: u128, n: u128) -> Result<Term, String> {
        match self.reg(st, r) {
            Some((m, v)) if m == n => Ok(v),
            Some((m, _)) => Err(format!("{:x}: register {} holds {} bytes, not {}", st.a, r, m, n)),
            None => Err(format!("{:x}: register {} holds no value of the procedure", st.a, r)),
        }
    }

    /// the state after writing v (n bytes) to r, at a
    fn set_reg(&mut self, st: &St, a: u128, r: u128, n: u128, v: Term) -> St {
        let name = self.fresh("R");
        self.lets.push((name.clone(), format!("fn_update({}, {}, pair({}, {}))", st.rs, r, n, self.print(&v))));
        let mut st2 = st.clone();
        st2.regs.push((r, n, v));
        st2.rs = name;
        st2.a = a;
        st2
    }

    /// the point claim's spec argument
    fn p(&self, spec: &Spec) -> String {
        match spec {
            Spec::Proc(i) => format!("WRAP({})", self.qs[*i].0),
            Spec::Ret(_, n) => n.clone(),
        }
    }

    fn pt(&self, st: &St, a: u128) -> String {
        format!("tr.pt(s, V, {}, {}, {}, HS, {}, {}, W)", self.base, self.code, a, st.rs, self.p(&st.spec))
    }

    // ------------------------------------------------------------------
    //  The spec's reductions

    /// A lemma's statement at an instance, and the instance's text.
    fn inst(&self, lemma: &str, args: &[(&str, Term)]) -> Result<(String, Term), String> {
        let (ps, stmt) = self.lemmas.get(lemma).ok_or_else(|| format!("no lemma `{}` (load proofs/translate.core)", lemma))?;
        let mut t = stmt.clone();
        let mut parts = Vec::new();
        for v in ps {
            let info = &self.env.vars[*v as usize];
            let val = &args.iter().find(|x| x.0 == info.name).ok_or_else(|| format!("{}: no value for `{}`", lemma, info.name))?.1;
            t = t.subst_var(*v, val, &self.env.binders_fn());
            parts.push(format!("{} := {}", info.name, self.lambda(info.arity as usize, val)));
        }
        Ok((format!("{}[{}]", lemma, parts.join(", ")), t))
    }

    /// a reduction lemma's instance: its `runs(q2, w, o) -> runs(q, w, o)`
    fn qparts(&self, t: &Term) -> Option<(Term, Term)> {
        let mut t = t.clone();
        loop {
            if let Some(a) = self.app(&t, "all", 1) {
                t = a[0].clone();
                continue;
            }
            let Node::App(s, a) = t.node() else { return None };
            if *s != self.env.builtins.imp {
                return None;
            }
            if let (Some(x), Some(y)) = (self.app(&a[0], "runs", 3), self.app(&a[1], "runs", 3)) {
                let bf = self.env.binders_fn();
                if x[0].loose_depth(&bf) == 0 && y[0].loose_depth(&bf) == 0 {
                    return Some((y[0].clone(), x[0].clone()));
                }
            }
            t = a[1].clone();
        }
    }

    /// The reduction by `lemma` at `args` of the rest `qi`: the reduced
    /// rest (checked: the instance's rest is `qi`'s)
    fn by(&mut self, qi: usize, lemma: &str, args: &[(&str, Term)]) -> Result<(usize, String), String> {
        let (text, stmt) = self.inst(lemma, args)?;
        let (q, q2) = self.qparts(&stmt).ok_or_else(|| format!("{}: not a reduction", lemma))?;
        // (as the kernel reads them: the names are lets)
        let (q, q2) = (self.canon(&q), self.canon(&q2));
        if q != self.canon(&self.qs[qi].1) {
            return Err(format!("{} does not fit {}:\n  {}\n  {}", lemma, self.qs[qi].0, self.print(&q), self.print(&self.qs[qi].1)));
        }
        let j = self.new_q(q2);
        Ok((j, text))
    }

    /// a guard's value: a literal comparison, a fact in scope
    fn guard(&self, g: &Term, hyps: &[(Term, String)]) -> Option<(bool, String)> {
        if let Some(h) = hyps.iter().find(|h| h.0 == *g) {
            return Some((true, h.1.clone()));
        }
        if let Some(a) = self.app(g, "not", 1) {
            if hyps.iter().any(|h| h.0 == a[0]) {
                return Some((false, String::new()));
            }
            let (v, _) = self.guard(&a[0], hyps)?;
            return Some((!v, "simp()".into()));
        }
        if let Some(a) = self.app(g, "and", 2) {
            let (x, _) = self.guard(&a[0], hyps)?;
            let (y, _) = self.guard(&a[1], hyps)?;
            return Some((x && y, "simp()".into()));
        }
        if let Some(a) = self.app(g, "eq", 2) {
            let v = match (a[0].node(), a[1].node()) {
                (Node::Nat(x), Node::Nat(y)) => x == y,
                (Node::Bytes(x), Node::Bytes(y)) => x == y,
                _ => return None,
            };
            return Some((v, "simp()".into()));
        }
        None
    }

    /// the way to a disjunct whose guard holds
    fn pick(&self, t: &Term, hyps: &[(Term, String)]) -> Option<Vec<Pick>> {
        if let Some(a) = self.app(t, "and", 2) {
            if a[0].loose_depth(&self.env.binders_fn()) == 0 {
                if let Some((true, pf)) = self.guard(&a[0], hyps) {
                    return Some(vec![Pick::And(a[0].clone(), pf)]);
                }
            }
            return None;
        }
        if let Some(a) = self.app(t, "or", 2) {
            if let Some(mut p) = self.pick(&a[0], hyps) {
                p.insert(0, Pick::L);
                return Some(p);
            }
            if let Some(mut p) = self.pick(&a[1], hyps) {
                p.insert(0, Pick::R);
                return Some(p);
            }
        }
        None
    }

    /// A projection of a constructed outcome (or pair) in the rest's body
    /// (of x0 only): its lemma, and its parts (at the body)
    fn redex(&self, t: &Term, depth: u32) -> Option<(&'static str, Term, Term, Term)> {
        let kinds: [(&str, &str, &'static str); 8] = [
            ("fst", "ok", "tr.qe_fst_ok"),
            ("fst", "exc", "tr.qe_fst_exc"),
            ("out_state", "ok", "tr.qe_os_ok"),
            ("out_value", "ok", "tr.qe_ov_ok"),
            ("out_state", "exc", "tr.qe_os_exc"),
            ("out_value", "exc", "tr.qe_ov_exc"),
            ("fst", "pair", "tr.qe_fst_pair"),
            ("snd", "pair", "tr.qe_snd_pair"),
        ];
        // (of x0 only: its loose variables at depth d are x0's, d + 1)
        let lift = |x: &Term| self.remap(x, 0, &|j| (j == depth + 1).then_some(1));
        if let Node::App(_, a) = t.node() {
            for (f, c, lemma) in kinds {
                if let Some(x) = self.app(t, f, 1) {
                    if let Some(y) = self.app(&x[0], c, 2) {
                        if let (Some(s), Some(v), Some(r)) = (lift(&y[0]), lift(&y[1]), lift(t)) {
                            return Some((lemma, r, s, v));
                        }
                    }
                }
            }
            let Node::App(s, _) = t.node() else { unreachable!() };
            let bs = self.env.syms[*s as usize].binders.clone();
            for (x, k) in a.iter().zip(bs) {
                if let Some(r) = self.redex(x, depth + k) {
                    return Some(r);
                }
            }
        }
        None
    }

    /// `bits_of_int(n, x)` (closed) with x a whole n-bit field
    /// (`int_mod(int_div(b, int_pow(2, 0)), int_pow(2, n))`): it, n, b
    fn whole_field(&self, t: &Term) -> Option<(Term, u128, Term)> {
        if let Some(a) = self.app(t, "bits_of_int", 2) {
            if let Some(n) = nat(&a[0]) {
                if [8, 16, 32, 64].contains(&n) && t.loose_depth(&self.env.binders_fn()) == 0 {
                    let x = self.expand(&a[1]);
                    let field = (|| {
                        let m = self.app(&x, "int_mod", 2)?;
                        let d = self.app(&m[0], "int_div", 2)?;
                        let p0 = self.app(&d[1], "int_pow", 2)?;
                        let pn = self.app(&m[1], "int_pow", 2)?;
                        (nat(&p0[0])? == 2 && nat(&p0[1])? == 0 && nat(&pn[0])? == 2 && nat(&pn[1])? == n).then(|| d[0].clone())
                    })();
                    if let Some(b) = field {
                        return Some((t.clone(), n, b));
                    }
                }
            }
        }
        if let Node::App(_, a) = t.node() {
            for x in a.iter() {
                if let Some(r) = self.whole_field(x) {
                    return Some(r);
                }
            }
        }
        None
    }

    /// `t` (at depth d below the body) with `r` (at the body) abstracted:
    /// the body as a value of x0 x1 y
    fn abstract_(&self, t: &Term, r: &Term, depth: u32) -> Term {
        let bf = self.env.binders_fn();
        if *t == r.shift(depth, 0, &bf) {
            return Term::bvar(depth);
        }
        match t.node() {
            Node::BVar(i) if *i >= depth => Term::bvar(i + 1),
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.abstract_(x, r, depth)).collect()),
            Node::App(s, a) => {
                let bs = self.env.syms[*s as usize].binders.clone();
                t.with_args(a.iter().zip(bs).map(|(x, k)| self.abstract_(x, r, depth + k)).collect())
            }
        }
    }

    /// An operation at the head: (its definedness, its value, the ok
    /// fact's text, the raise fact's text); no definedness when literally
    /// defined.
    fn op(&mut self, op: &Term) -> Result<(Option<Term>, Term, String, String), String> {
        let w = self.print(&self.w.clone());
        let pr = |g: &Gen, t: &Term| g.print(t);
        if let Some(x) = self.app(op, "gimple.sadd", 3) {
            if nat(&x[0]) == Some(32) {
                let (a, b) = (x[1].clone(), x[2].clone());
                let s32 = |g: &Gen, t: &Term| g.mk("sint", vec![lit(32), t.clone()]);
                let ty = self.mk("fn_update", vec![self.mk("fn_update", vec![self.mk("empty", vec![]), Term::bytes(b"prec"), lit(32)]), Term::bytes(b"signed"), self.mk("true", vec![])]);
                let cond = self.mk("gimple.fits", vec![ty, self.mk("int_add", vec![s32(self, &a), s32(self, &b)])]);
                let r = self.mk("bits_add", vec![lit(32), a.clone(), b.clone()]);
                let ok = format!("mp(tr.sadd32_ok, {{{w}}}, {{{}}}, {{{}}}, hvu, simp(L), simp(L), {{HC}})", pr(self, &a), pr(self, &b));
                let ub = format!("mp(tr.sadd32_ub, {{{w}}}, {{{}}}, {{{}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), {{HN}})", pr(self, &a), pr(self, &b));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        if let Some(x) = self.app(op, "gimple.padd", 2) {
            let (p, d) = (x[0].clone(), x[1].clone());
            if let (Some(_), Some(dv)) = (self.eval_lit(&p), self.eval_lit(&d)) {
                if dv < 1 << 63 {
                    let r = self.mk("int_add", vec![p.clone(), d.clone()]);
                    let ok = format!("mp(tr.padd_ok, {{{w}}}, {{{}}}, {{{}}}, hvu, simp(L), simp(L), simp(L), simp(L))", pr(self, &p), pr(self, &d));
                    return Ok((None, r, ok, String::new()));
                }
            }
            // a pointer's: p + d in 64 bits, when in the address range
            // (tr.padd_def, as it expands)
            let ty = self.mk("fn_update", vec![self.mk("fn_update", vec![self.mk("empty", vec![]), Term::bytes(b"prec"), lit(64)]), Term::bytes(b"signed"), self.mk("true", vec![])]);
            let sum = self.mk("int_add", vec![p.clone(), self.mk("gimple.sval", vec![ty, d.clone()])]);
            let cond = self.mk("and", vec![self.mk("int_le", vec![lit(0), sum.clone()]), self.mk("int_lt", vec![sum, lit(P64)])]);
            let r = self.mk("bits_add", vec![lit(64), p.clone(), d.clone()]);
            let ok = format!("mp(tr.padd_okb, {{{w}}}, {{{}}}, {{{}}}, hvu, simp(L), simp(L), {{HC}})", pr(self, &p), pr(self, &d));
            let ub = format!("mp(tr.padd_ub, {{{w}}}, {{{}}}, {{{}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), simp(L), simp(L), {{HN}})", pr(self, &p), pr(self, &d));
            return Ok((Some(cond), r, ok, ub));
        }
        if let Some(x) = self.app(op, "gimple.elem", 3) {
            if nat(&x[2]) == Some(1) {
                let p = x[0].clone();
                let ix = self.expand(&x[1]);
                let (i, kind) = match self.app(&ix, "bits_sext", 3) {
                    Some(y) if nat(&y[0]) == Some(32) && nat(&y[1]) == Some(64) => (self.canon(&y[2]), "sx"),
                    _ => (x[1].clone(), "u"),
                };
                // (the definedness, as tr.elem_sx_def / tr.elem_u_def expand)
                let cond = if kind == "sx" {
                    let s = self.mk("sint", vec![lit(32), i.clone()]);
                    let sum = self.mk("int_add", vec![p.clone(), s]);
                    self.mk("and", vec![self.mk("int_le", vec![lit(0), sum.clone()]), self.mk("int_lt", vec![sum, lit(P64)])])
                } else {
                    self.mk("int_lt", vec![self.mk("int_add", vec![p.clone(), i.clone()]), lit(P64)])
                };
                let r = self.mk("bits_add", vec![lit(64), p.clone(), x[1].clone()]);
                let ok = format!("mp(tr.elem1_{}_ok, {{{w}}}, {{{}}}, {{{}}}, hvu, simp(L), simp(L), {{HC}})", kind, pr(self, &p), pr(self, &i));
                let ub = format!("mp(tr.elem1_{}_ub, {{{w}}}, {{{}}}, {{{}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), simp(L), simp(L), {{HN}})", kind, pr(self, &p), pr(self, &i));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        if let Some(x) = self.app(op, "gimple.ld8", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.ld8_cond(&a);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(1)])]);
                let ok = format!("mp(g.ld8_ok, {{{w}}}, {{{}}}, hvu, simp(L), taut({{HC}}), taut({{HC}}))", pr(self, &a));
                let ub = format!("mp(g.ld8_ub, {{{w}}}, {{{}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), {{HN}}, simp(L))", pr(self, &a));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        // a 2-byte load
        if let Some(x) = self.app(op, "gimple.ld16", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.parse(&format!("g.mem_defined(app({w}, \"vm\"), {}, 0, 2, false)", pr(self, &a)))?;
                let r = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({w}, \"vm\"), {}, 2))", pr(self, &a)))?;
                let ok = format!("mp(g.ld16_ok, {{{w}}}, {{{}}}, hvu, simp(L), {{HC}})", pr(self, &a));
                let ub = format!("mp(g.ld16_ub, {{{w}}}, {{{}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), simp(L), {{HN}})", pr(self, &a));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        // an array's 2-byte element at a sign-extended 32-bit index
        if let Some(x) = self.app(op, "gimple.elem", 3) {
            let ix = self.expand(&x[1]);
            if let (Some(2), Some(y)) = (nat(&x[2]), self.app(&ix, "bits_sext", 3)) {
                if nat(&y[0]) == Some(32) && nat(&y[1]) == Some(64) {
                    let (p, i) = (pr(self, &x[0]), pr(self, &self.canon(&y[2])));
                    let cond = self.parse(&format!("tr.elem2_sx_def({}, {})", p, i))?;
                    let r = self.parse(&format!("bits_add(64, {p}, bits_add(64, bits_sext(32, 64, {i}), bits_sext(32, 64, {i})))"))?;
                    let ok = format!("mp(tr.elem2_sx_ok, {{{w}}}, {{{p}}}, {{{i}}}, hvu, simp(L), simp(L), {{HC}})");
                    let ub = format!("mp(tr.elem2_sx_ub, {{{w}}}, {{{p}}}, {{{i}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), simp(L), simp(L), {{HN}})");
                    return Ok((Some(cond), r, ok, ub));
                }
            }
        }
        // a bitfield load: n bytes at p + off, bits pos.., k of them
        if let Some(x) = self.app(op, "gimple.ldbf", 5) {
            let t: Vec<String> = x.iter().map(|y| pr(self, y)).collect();
            let (p, off, n, pos, k) = (&t[0], &t[1], &t[2], &t[3], &t[4]);
            let cond = self.parse(&format!("g.mem_defined(app({w}, \"vm\"), {p}, {off}, {n}, false)"))?;
            let r = self.parse(&format!("int_mod(int_div(gimple.bytes_at(app({w}, \"vm\"), bits_add(64, {p}, {off}), {n}), int_pow(2, {pos})), int_pow(2, {k}))"))?;
            let ok = format!("mp(tr.ldbf_ok, {{{w}}}, {{{p}}}, {{{off}}}, {{{n}}}, {{{pos}}}, {{{k}}}, hvu, simp(L), simp(L), {{HC}})");
            let ub = format!("mp(g.ldbf_ub, {{{w}}}, {{{p}}}, {{{off}}}, {{{n}}}, {{{pos}}}, {{{k}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), simp(L), simp(L), {{HN}})");
            return Ok((Some(cond), r, ok, ub));
        }
        // a signed 32-bit product by an immediate (tr.imul_by(k), proven per
        // immediate)
        if let Some(x) = self.app(op, "gimple.smul", 3) {
            if let (Some(32), Some(k)) = (nat(&x[0]), nat(&x[2])) {
                if k < 1 << 31 {
                    self.imuls.insert(k);
                    let a = pr(self, &x[1]);
                    let cond = self.parse(&format!("tr.s32_fits(int_mul(sint(32, {a}), sint(32, {k})))"))?;
                    let r = self.parse(&format!("bits_mul(32, {a}, {k})"))?;
                    let ok = format!("mp(tr.smul32_ok, {{{w}}}, {{{a}}}, {{{k}}}, hvu, simp(L), simp(L), {}.imul_{k}, {{HC}})", self.prefix);
                    let ub = format!("mp(tr.smul32_ub, {{{w}}}, {{{a}}}, {{{k}}}, {{{w}}}, {{empty}}, hvu, hvu, simp(), {{HN}})");
                    return Ok((Some(cond), r, ok, ub));
                }
            }
        }
        // a call of a one-operation helper (a field's accessor): its
        // operation's definedness, its value through the helper's result
        if let Node::App(f, args) = op.node() {
            if let SymKind::Defined { params, body } = &self.env.syms[*f as usize].kind {
                let fname = self.env.syms[*f as usize].name.clone();
                let mut b = body.clone();
                for (p, x) in params.clone().iter().zip(args.iter()) {
                    b = b.subst_var(*p, x, &self.env.binders_fn());
                }
                let parts = (|| -> Option<(Term, Term)> {
                    let m = self.app(&b, "mkprog", 1)?;
                    let br = self.app(&m[0], "bind_rel", 5)?;
                    matches!(br[1].node(), Node::BVar(1)).then_some(())?;
                    // x1 = ok(x2, f(x3)), the standard handlers
                    let e = self.app(&br[2], "eq", 2)?;
                    let o = self.app(&e[1], "ok", 2)?;
                    (matches!(e[0].node(), Node::BVar(2)) && matches!(o[0].node(), Node::BVar(1))).then_some(())?;
                    let fl = self.lam(&o[1], &["x0", "x1", "x2", "x3"], &["x3"])?;
                    Some((br[0].clone(), fl))
                })();
                if let Some((op2, fl)) = parts {
                    let (cond, r2, ok2, ub2) = self.op(&op2)?;
                    let r = fl.instantiate_params(&[r2.clone()], &self.env.binders_fn());
                    let (okl, _) = self.inst("tr.call1_ok", &[("op", op2.clone()), ("r", r2.clone()), ("f", fl.clone())])?;
                    let ok = format!("defs(mp({okl}, {{{w}}}, hvu, simp(L), {ok2}), {fname})");
                    let ub = match cond {
                        Some(_) => {
                            let (ubl, _) = self.inst("tr.call1_ub", &[("op", op2.clone()), ("s2", self.w.clone()), ("e", self.mk("empty", vec![])), ("f", fl.clone())])?;
                            format!("defs(mp({ubl}, {{{w}}}, hvu, hvu, simp(), {ub2}), {fname})")
                        }
                        None => String::new(),
                    };
                    return Ok((cond, r, ok, ub));
                }
            }
        }
        Err(format!("no rule for the operation {}", self.print(op)))
    }

    /// a term from text, the placeholders by their names
    fn parse(&mut self, text: &str) -> Result<Term, String> {
        let names = self.names.clone();
        syntax::parse_term(self.env, text, &names).map_err(|e| format!("{}: {}", text, e.0))
    }

    /// `[b + d]` (b a register, no index): b's number, b, d
    fn base_disp(&self, t: &Term) -> Option<(u128, Term, Term)> {
        let m = self.memop(t)?;
        let (bk, b) = self.tag(m.get("base")?)?;
        (bk == 2 && nat(m.get("seg")?)? == 0 && self.app(m.get("index")?, "none", 0).is_some() && nat(m.get("scale")?)? == 1).then_some(())?;
        Some((nat(&b)?, b, m["disp"].clone()))
    }

    /// the fact in scope that the spec's n-byte load at p + d is defined
    fn mem_hyp(&mut self, st: &St, p: &Term, d: &Term, n: u128) -> Result<String, String> {
        let cond = self.parse(&format!("g.mem_defined(app(W, \"vm\"), {}, {}, {}, false)", self.print(p), self.print(d), n))?;
        st.hyps.iter().find(|h| h.0 == cond).map(|h| h.1.clone()).ok_or_else(|| {
            let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
            format!("{:x}: a load of {} bytes at {} + {} the spec does not make (the facts: {})", st.a, n, self.print(p), self.print(d), facts.join(", "))
        })
    }

    /// a byte load's definedness at a
    fn ld8_cond(&self, a: &Term) -> Term {
        let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
        let nz = self.mk("not", vec![self.mk("eq", vec![a.clone(), lit(0)])]);
        let us = self.mk("gimple.usable", vec![vm, a.clone(), lit(1), self.mk("false", vec![])]);
        self.mk("and", vec![nz, us])
    }

    /// One reduction of the rest `qi` (None: the head waits for the machine).
    fn reduce(&mut self, qi: usize, hyps: &[(Term, String)]) -> Result<Option<Red>, String> {
        let q = self.qs[qi].1.clone();
        let w = self.print(&self.w.clone());
        // a procedure's definition: its body
        if let Node::App(f, args) = q.node() {
            if self.name(&q) != Some("mkprog") {
                if let SymKind::Defined { params, body } = &self.env.syms[*f as usize].kind {
                    let fname = self.env.syms[*f as usize].name.clone();
                    let mut b = body.clone();
                    for (p, x) in params.clone().iter().zip(args.iter()) {
                        b = b.subst_var(*p, x, &self.env.binders_fn());
                    }
                    let b = self.canon(&b);
                    let j = self.new_q(b);
                    let u = self.fresh("u");
                    let pre = vec![
                        format!("have {}: all o. runs({}, W, o) -> runs({}, W, o) proof", u, self.qs[j].0, self.qs[qi].0),
                        "  fix o".into(),
                        format!("  assume h: runs({}, W, o)", self.qs[j].0),
                        format!("  show by defs(h, {})", fname),
                        "qed".into(),
                    ];
                    return Ok(Some(Red::Q(j, u, pre)));
                }
            }
        }
        let body = self.app(&q, "mkprog", 1).ok_or_else(|| format!("the spec's rest is not a program: {}", self.print(&q)))?[0].clone();
        // a whole field's value: the bytes themselves
        if let Some((r, n, bytes)) = self.whole_field(&body) {
            let b = self.abstract_(&body, &r, 0);
            let e2 = self.mk("bits_of_int", vec![lit(n), bytes.clone()]);
            let (j, text) = self.by(qi, "tr.qe_eq", &[("b", b), ("e", r), ("e2", e2)])?;
            return Ok(Some(Red::Q(j, format!("mp({}, mp(tr.bits_field0_{}, {{{}}}), {{{w}}})", text, n, self.print(&bytes)), vec![])));
        }
        // a projection of a constructed outcome
        if let Some((lemma, r, st, vv)) = self.redex(&body, 0) {
            let b = self.abstract_(&body, &r, 0);
            let st = self.lam(&st, &["x0", "x1"], &["x0"]).ok_or("redex")?;
            let vv = self.lam(&vv, &["x0", "x1"], &["x0"]).ok_or("redex")?;
            let (j, text) = self.by(qi, lemma, &[("b", b), ("st", st), ("vv", vv)])?;
            return Ok(Some(Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])));
        }
        // not a block: the result, a raise, or into the block form
        let Some(ex) = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())) else {
            if let Some(x) = self.app(&body, "eq", 2) {
                if let Some(o) = self.app(&x[1], "ok", 2) {
                    if matches!(x[0].node(), Node::BVar(0)) && matches!(o[0].node(), Node::BVar(1)) && o[1].loose_depth(&self.env.binders_fn()) == 0 {
                        let val = self.value(&o[1]);
                        return Ok(Some(Red::Ret(val)));
                    }
                }
            }
            let (j, text) = self.by(qi, "tr.qs_intro", &[("a", body.clone())])?;
            return Ok(Some(Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])));
        };
        let (a, k) = (ex[0].clone(), ex[1].clone());
        let ctx = ["x0", "x1", "x8"];
        let kl = self.lam(&k, &ctx, &["x8", "x1"]).ok_or("a block's rest reads the world")?;
        // a let
        if let Some(x) = self.app(&a, "letin", 2) {
            if x[0].loose_depth(&self.env.binders_fn()) > 0 {
                return Err(format!("a let of the state: {}", self.lambda(3, &x[0])));
            }
            let e = self.value(&x[0]);
            let al = self.lam(&x[1], &["x0", "x1", "x8", "x"], &["x0", "x8", "x"]).ok_or("a let's body reads the outcome")?;
            let (j, text) = self.by(qi, "tr.qs_let", &[("e", e), ("a", al), ("k", kl)])?;
            return Ok(Some(Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])));
        }
        // a choice: a placeholder witness
        if let Some(x) = self.app(&a, "any_rel", 2) {
            let d = self.lam(&x[0], &["x0", "x1", "x8", "x"], &["x"]).ok_or("a choice whose domain reads the state")?;
            let ok = self.app(&d, "in", 2).map_or(false, |m| matches!(m[0].node(), Node::BVar(0)) && self.app(&m[1], "bits", 1).is_some());
            if !ok {
                return Err(format!("a choice from {}", self.lambda(1, &d)));
            }
            let zn = format!("Z{}", self.zs.len());
            let z = self.var(&zn);
            if let Node::Var(v, _) = z.node() {
                self.zs.push(*v);
            }
            let al = self.lam(&x[1], &["x0", "x1", "x8", "x"], &["x0", "x8", "x"]).ok_or("a choice's body reads the outcome")?;
            let (j, text) = self.by(qi, "tr.qs_any", &[("c", z), ("d", d), ("a", al), ("k", kl)])?;
            return Ok(Some(Red::Q(j, format!("mp({}, simp(), {{{w}}})", text), vec![])));
        }
        // an operation
        if let Some(x) = self.app(&a, "bind_rel", 5) {
            if matches!(x[1].node(), Node::BVar(2)) && x[0].loose_depth(&self.env.binders_fn()) == 0 {
                let c5 = ["x0", "x1", "x8", "x9", "x10"];
                let al = self.lam(&x[2], &c5, &["x9", "x10", "x8"]).ok_or("an operation's continuation reads the world before it")?;
                let xl = self.lam(&x[3], &c5, &["x9", "x10", "x8"]).ok_or("an operation's handler reads the world before it")?;
                let dl = self.lam(&x[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("an operation's handler reads the world before it")?;
                let (cond, r, okf, ubf) = self.op(&x[0])?;
                let r = self.value(&r);
                let args = |r2: (&'static str, Term)| vec![("op", x[0].clone()), r2, ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone())];
                let (j, text) = self.by(qi, "tr.qs_op", &args(("r", r.clone())))?;
                let okr = format!("mp({}, {{{w}}}, {})", text, okf);
                let Some(cond) = cond else { return Ok(Some(Red::Q(j, okr, vec![]))) };
                let mut ra = args(("s2", self.w.clone()));
                ra.push(("e", self.mk("empty", vec![])));
                let (u, rtext) = self.by(qi, "tr.qs_raise", &ra)?;
                let ubr = format!("mp({}, {{{w}}}, {})", rtext, ubf);
                return Ok(Some(Red::Split { cond, ok: (j, okr), ub: (u, ubr) }));
            }
        }
        // a block at the head
        if let Some(e) = self.app(&a, "ex", 1) {
            if let Some(y) = self.app(&e[0], "and", 2) {
                let c4 = ["x0", "x1", "x8", "x9"];
                let a1 = self.lam(&y[0], &c4, &["x0", "x9"]).ok_or("a block's head reads the outer outcome")?;
                let k1 = self.lam(&y[1], &c4, &["x9", "x8"]).ok_or("a block's rest reads the world")?;
                let (j, text) = self.by(qi, "tr.qs_assoc", &[("a", a1), ("k1", k1), ("k2", kl)])?;
                return Ok(Some(Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])));
            }
        }
        // the head done: x8 = v
        if let Some(x) = self.app(&a, "eq", 2) {
            if matches!(x[0].node(), Node::BVar(0)) {
                if let Some(v) = self.lam(&x[1], &ctx, &["x0"]) {
                    let (j, text) = self.by(qi, "tr.qs_ret", &[("v", v), ("k", kl)])?;
                    return Ok(Some(Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])));
                }
            }
        }
        // a disjunct whose guard holds
        if let Some(path) = self.pick(&a, hyps) {
            let first = path.into_iter().next().unwrap();
            let c2 = ["x0", "x8"];
            return Ok(Some(match first {
                Pick::L | Pick::R => {
                    let x = self.app(&a, "or", 2).unwrap().to_vec();
                    let l = self.lam(&x[0], &ctx, &c2).ok_or("a disjunct reads the outcome")?;
                    let r = self.lam(&x[1], &ctx, &c2).ok_or("a disjunct reads the outcome")?;
                    let lemma = if matches!(first, Pick::L) { "tr.qs_orl" } else { "tr.qs_orr" };
                    let (j, text) = self.by(qi, lemma, &[("a", l), ("b", r), ("k", kl)])?;
                    Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])
                }
                Pick::And(g, pf) => {
                    let x = self.app(&a, "and", 2).unwrap().to_vec();
                    let l = self.lam(&x[1], &ctx, &c2).ok_or("a guarded head reads the outcome")?;
                    let (j, text) = self.by(qi, "tr.qs_and", &[("c", g), ("a", l), ("k", kl)])?;
                    Red::Q(j, format!("mp({}, {}, {{{w}}})", text, pf), vec![])
                }
            }));
        }
        Ok(None)
    }

    // ------------------------------------------------------------------
    //  The proof

    fn wred(&self, st: &St, qi: usize, j: usize) -> String {
        format!(
            "tr.wred[s := s, v := V, base := {}, code := {}, a := {}, hs := HS, rs := {}, w := W, q := {}, q2 := {}, kw := x0 x1 x2. KW(x0, x1, x2)]",
            self.base, self.code, st.a, st.rs, self.qs[qi].0, self.qs[j].0
        )
    }

    /// A proof that the rest `qi` raises from W (`x1 = exc(W, empty)` at its
    /// end): the reductions to it, backwards.
    fn raise_chain(&mut self, qi: usize) -> Result<Pf, String> {
        let mut cur = qi;
        let mut steps: Vec<String> = Vec::new();
        let mut lines = Vec::new();
        let exc_end = |g: &Gen, q: &Term| {
            g.app(q, "mkprog", 1).and_then(|b| g.app(&b[0], "eq", 2).map(|x| x.to_vec())).map_or(false, |x| {
                matches!(x[0].node(), Node::BVar(0)) && g.app(&x[1], "exc", 2).map_or(false, |e| e[0] == g.w && g.app(&e[1], "empty", 0).is_some())
            })
        };
        while !exc_end(self, &self.qs[cur].1.clone()) {
            match self.reduce(cur, &[])? {
                Some(Red::Q(j, r, pre)) => {
                    lines.extend(pre);
                    steps.push(r);
                    cur = j;
                }
                _ => return Err(format!("a raise that does not reach the result: {}", self.print(&self.qs[cur].1))),
            }
        }
        let mut name = self.fresh("r");
        lines.push(format!("have {} := mp(tr.q_exc_runs, {{W}}, {{W}}, {{empty}}, hvu, hvu, simp())", name));
        for r in steps.into_iter().rev() {
            let n2 = self.fresh("r");
            lines.push(format!("have {} := mp({}, {{exc(W, empty)}}, {})", n2, r, name));
            name = n2;
        }
        Ok(Pf { lines, expr: name })
    }

    /// The proof of the point claim at `st`.
    fn prove(&mut self, st: St) -> Result<Pf, String> {
        if let Spec::Proc(qi) = st.spec {
            match self.reduce(qi, &st.hyps)? {
                Some(Red::Q(j, r, pre)) => {
                    let mut st2 = st.clone();
                    st2.spec = Spec::Proc(j);
                    let rest = self.prove(st2)?;
                    let pn = self.fresh("p");
                    let mut lines = pre;
                    lines.extend(rest.lines);
                    lines.push(format!("have {} := {}", pn, rest.expr));
                    return Ok(Pf { lines, expr: format!("mp({}, {}, {})", self.wred(&st, qi, j), r, pn) });
                }
                Some(Red::Ret(val)) => {
                    let pr = self.fresh("PR");
                    let body = self.kw.instantiate_params(&[Term::bvar(1), val.clone(), Term::bvar(0)], &self.env.binders_fn());
                    let text = self.print(&self.mk("mkprog", vec![body]));
                    self.lets.push((pr.clone(), text));
                    let mut st2 = st.clone();
                    st2.spec = Spec::Ret(val.clone(), pr);
                    let rest = self.prove(st2)?;
                    let pn = self.fresh("p");
                    let mut lines = rest.lines;
                    lines.push(format!("have {} := {}", pn, rest.expr));
                    let expr = format!(
                        "mp(tr.wret[s := s, v := V, base := {}, code := {}, a := {}, hs := HS, rs := {}, w := W, val := {}, kw := x0 x1 x2. KW(x0, x1, x2)], simp(hvu), {})",
                        self.base, self.code, st.a, st.rs, self.print(&val), pn
                    );
                    return Ok(Pf { lines, expr });
                }
                Some(Red::Split { cond, ok, ub }) => {
                    let (hn, hc, un, dn, pn) = (self.fresh("hn"), self.fresh("hc"), self.fresh("u"), self.fresh("d"), self.fresh("p"));
                    let ct = self.print(&cond);
                    // undefined: the spec raises
                    let chain = self.raise_chain(ub.0)?;
                    let mut lines = vec![format!("have {}: !({}) -> runs({}, W, exc(W, empty)) proof", un, ct, self.qs[qi].0), format!("  assume {}: !({})", hn, ct)];
                    let mut body = chain.lines;
                    body.push(format!("show := mp({}, {{exc(W, empty)}}, {})", ub.1.replace("{HN}", &hn), chain.expr));
                    lines.extend(indent(body));
                    lines.push("qed".into());
                    // defined: on with the condition
                    let mut st2 = st.clone();
                    st2.spec = Spec::Proc(ok.0);
                    st2.hyps.push((cond.clone(), hc.clone()));
                    let rest = self.prove(st2)?;
                    lines.push(format!("have {}: {} -> {} proof", dn, ct, self.pt(&st, st.a)));
                    let mut body = vec![format!("assume {}: {}", hc, ct)];
                    body.extend(rest.lines);
                    body.push(format!("have {} := {}", pn, rest.expr));
                    body.push(format!("show := mp({}, {}, {})", self.wred(&st, qi, ok.0), ok.1.replace("{HC}", &hc), pn));
                    lines.extend(indent(body));
                    lines.push("qed".into());
                    let expr = format!(
                        "mp(tr.wsplit[s := s, v := V, base := {}, code := {}, a := {}, hs := HS, rs := {}, w := W, q := {}, kw := x0 x1 x2. KW(x0, x1, x2), c := {}], hvu, {}, {})",
                        self.base, self.code, st.a, st.rs, self.qs[qi].0, ct, un, dn
                    );
                    return Ok(Pf { lines, expr });
                }
                None => {}
            }
        }
        self.insn(st)
    }

    /// a linear step: the rule's text with `{NEXT}`, the state after
    fn then(&mut self, text: String, st2: St) -> Result<Pf, String> {
        let rest = self.prove(st2)?;
        let pn = self.fresh("p");
        let mut lines = rest.lines;
        lines.push(format!("have {} := {}", pn, rest.expr));
        Ok(Pf { lines, expr: text.replace("{NEXT}", &pn) })
    }

    /// a branch on c: on to a3 when c, to t when not
    fn branch(&mut self, st: &St, c: Term, a3: u128, t: u128, text: String) -> Result<Pf, String> {
        let ct = self.print(&c);
        let nc = self.mk("not", vec![c.clone()]);
        let mut lines = Vec::new();
        let mut names = Vec::new();
        for (cond, to, neg) in [(c.clone(), a3, false), (nc, t, true)] {
            let (bn, hn) = (self.fresh("b"), self.fresh("h"));
            let mut st2 = st.clone();
            st2.a = to;
            st2.hyps.push((cond, hn.clone()));
            let rest = self.prove(st2.clone())?;
            let cs = if neg { format!("!({})", ct) } else { ct.clone() };
            lines.push(format!("have {}: {} -> {} proof", bn, cs, self.pt(&st2, to)));
            let mut body = vec![format!("assume {}: {}", hn, cs)];
            body.extend(rest.lines);
            body.push(format!("show := {}", rest.expr));
            lines.extend(indent(body));
            lines.push("qed".into());
            names.push(bn);
        }
        Ok(Pf { lines, expr: text.replace("{T}", &names[0]).replace("{F}", &names[1]) })
    }

    /// the instance's common head: `{s}, {V}, {base}, {code}, {a}, {a2}, {len}`
    fn head(&self, rule: &str, a: u128, insn: &Insn) -> String {
        format!("mp(tr.{}, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}", rule, self.base, self.code, a, (a + insn.len) % P64, insn.len)
    }

    /// the instance's tail: the coupling's maps, the decode fact, n literal
    /// facts, the extra premises, the next point
    fn tail(&self, st: &St, insn: &Insn, n: usize, extra: &[String]) -> String {
        let mut t = format!(", {{HS}}, {{{}}}, {{{}}}, {{W}}, {}", st.rs, self.p(&st.spec), insn.name);
        for _ in 0..n {
            t.push_str(", simp(L)");
        }
        for e in extra {
            t.push_str(", ");
            t.push_str(e);
        }
        t.push_str(", {NEXT})");
        t
    }

    fn terms(&self, ts: &[&Term]) -> String {
        ts.iter().map(|t| format!(", {{{}}}", self.print(t))).collect()
    }

    /// The instruction at st's address.
    fn insn(&mut self, st: St) -> Result<Pf, String> {
        let a = st.a;
        let insn = self.insns.remove(&a).ok_or_else(|| format!("no decode fact at {:x}", a))?;
        let r = self.insn_at(&st, &insn);
        self.insns.insert(a, insn);
        r
    }

    fn insn_at(&mut self, st: &St, insn: &Insn) -> Result<Pf, String> {
        let a = st.a;
        let a2 = (a + insn.len) % P64;
        let fs = self.print(&insn.fields);
        let bad = |what: &str| format!("{:x}: {} (row {}): {}", a, what, insn.row, fs);
        let reg = |g: &Term| nat(g).ok_or_else(|| bad("a register that is not a literal"));
        let f = insn.fields.clone();
        let home = |hs: &BTreeMap<u128, (u128, Term)>, d: &Term| -> Result<Term, String> {
            let d = nat(d).ok_or_else(|| bad("a displacement that is not a literal"))?;
            match hs.get(&d) {
                Some((4, x)) => Ok(x.clone()),
                _ => Err(format!("{:x}: no 4-byte home at rsp{:+}", a, d as i128 - if d >= P64 / 2 { P64 as i128 } else { 0 })),
            }
        };
        match insn.row {
            // mov r32/r64, [rsp + d]: the home's value
            76 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // mov r64, [b + d] (b holding a pointer): the spec's field load
                if self.rsp_mem(&x[2]).is_none() && nat(&x[0]) == Some(8) {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let hc = self.mem_hyp(st, &bp, &d, 8)?;
                    let t = self.head("load64_bd", a, insn) + &self.terms(&[&x[1], &b, &d, &x[4], &bp]) + &self.tail(st, insn, 6, &[hc]);
                    let v = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app(W, \"vm\"), bits_add(64, {}, {}), 8))", self.print(&bp), self.print(&d)))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, v);
                    return self.then(t, st2);
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let v = match (n, self.hs.get(&dn)) {
                    (4, _) => home(&self.hs, &d)?,
                    (8, Some((8, x))) => x.clone(),
                    _ => return Err(bad("no home of the load's width")),
                };
                let rule = if n == 8 { "load64_home" } else { "load32_home" };
                let t = self.head(rule, a, insn) + &self.terms(&[&x[1], &d, &x[3], &x[4], &v]) + &self.tail(st, insn, 7, &[]);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, n, v);
                self.then(t, st2)
            }
            // neg r32
            64 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if nat(&x[1]) != Some(3) || k != 0 {
                    return Err(bad("not neg r32"));
                }
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, 4)?;
                let t = self.head("neg32", a, insn) + &self.terms(&[&g, &x[3], &u]) + &self.tail(st, insn, 4, &[]);
                let r = self.mk("bits_sub", vec![lit(32), lit(0), u]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(t, st2)
            }
            // and r32, [rsp + d]
            48 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&self.hs, &d)?;
                let u = self.need_reg(st, g, 4)?;
                let t = self.head("and32_home", a, insn) + &self.terms(&[&x[1], &d, &x[3], &x[4], &v, &u]) + &self.tail(st, insn, 9, &[]);
                let r = self.mk("bits_and", vec![lit(32), v, u]);
                let r = self.value(&r);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(t, st2)
            }
            // imul r32, r32, imm
            89 => {
                let x = self.pairs(&f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let (k, h) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 {
                    return Err(bad("imul of memory"));
                }
                let hn = reg(&h)?;
                let c = nat(&x[5]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                if c >= 1 << 31 {
                    return Err(bad("a negative immediate (no product lemma yet)"));
                }
                let u = self.need_reg(st, hn, 4)?;
                self.imuls.insert(c);
                let by = format!("{}.imul_{}", self.prefix, c);
                let t = self.head("imul32", a, insn) + &self.terms(&[&x[1], &h, &x[3], &x[4], &x[5], &u]) + &self.tail(st, insn, 4, &[by, "simp(L)".into(), "simp(L)".into()]);
                let r = self.mk("bits_mul", vec![lit(32), u, x[5].clone()]);
                let r = self.value(&r);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(t, st2)
            }
            // shr/shl r16/r32/r64, imm
            72 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let c = nat(&x[4]).ok_or_else(|| bad("a count that is not a literal"))?;
                let (size, op) = (nat(&x[0]).ok_or_else(|| bad("fields"))?, nat(&x[1]).ok_or_else(|| bad("fields"))?);
                if k != 0 || c == 0 || c >= 8 * size {
                    return Err(bad("not a register shift by 1..width-1"));
                }
                let gn = reg(&g)?;
                match (size, op) {
                    (4, 5) => {}
                    // shr r64, c
                    (8, 5) => {
                        let u = self.need_reg(st, gn, 8)?;
                        let t = self.head("shr64_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &u]) + &self.tail(st, insn, 7, &[]);
                        let r = self.mk("bits_shr", vec![lit(64), u, x[4].clone()]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(t, st2);
                    }
                    // shl r64, 12 of a word shifted down by 12: the field above
                    // its first byte, times 4096
                    (8, 4) if c == 12 => {
                        let (_, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                        let shape = (|| {
                            let s = self.expand(&u);
                            let sh = self.app(&s, "bits_shr", 3)?;
                            (nat(&sh[0])? == 64 && nat(&sh[2])? == 12).then_some(())?;
                            let y = self.app(&sh[1], "bits_of_int", 2)?;
                            (nat(&y[0])? == 64).then_some(())?;
                            let ba = self.app(&y[1], "gimple.bytes_at", 3)?;
                            (nat(&ba[2])? == 8).then_some(())?;
                            let ad = self.app(&ba[1], "bits_add", 3)?;
                            (nat(&ad[0])? == 64).then_some(())?;
                            Some((ad[1].clone(), nat(&ad[2])?))
                        })();
                        let (bp, off) = shape.ok_or_else(|| bad("shl 12 of a value not a word's field"))?;
                        let bp = self.canon(&bp);
                        let t = self.head("shl12_field", a, insn) + &self.terms(&[&g, &x[3], &bp, &lit(off), &lit(off + 1)]) + &self.tail(st, insn, 5, &[]);
                        let r = self.parse(&format!(
                            "bits_mul(64, bits_of_int(52, int_mod(int_div(gimple.bytes_at(app(W, \"vm\"), bits_add(64, {}, {}), 7), int_pow(2, 4)), int_pow(2, 52))), 4096)",
                            self.print(&bp),
                            off + 1
                        ))?;
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(t, st2);
                    }
                    // shr r16, c: the machine's value (a field rule reads it)
                    (2, 5) => {
                        let u = self.need_reg(st, gn, 2)?;
                        let t = self.head("shr16_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &u]) + &self.tail(st, insn, 7, &[]);
                        let r = self.parse(&format!("bits_set_slice(64, {u}, 15, 0, bits_shr(16, bits_slice({u}, 15, 0), {c}))", u = self.print(&u)))?;
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        return self.then(t, st2);
                    }
                    // shl r32, c: a product by 2^c
                    (4, 4) => {
                        let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                        let mk = 1u128 << c;
                        let t = self.head("shl32_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &lit(mk), &lit(n), &u]) + &self.tail(st, insn, 9, &[]);
                        let r = self.mk("bits_mul", vec![lit(32), u, lit(mk)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(t, st2);
                    }
                    _ => return Err(bad("no rule for the shift")),
                }
                let u = self.need_reg(st, gn, 4)?;
                let t = self.head("shr32", a, insn) + &self.terms(&[&g, &x[3], &x[4], &u]) + &self.tail(st, insn, 7, &[]);
                let r = self.mk("bits_shr", vec![lit(32), u, x[4].clone()]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(t, st2)
            }
            // mov r32, r32 (the store form: rm the destination)
            75 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let Some((0, h)) = self.tag(&x[2]) else { return Err(bad("a store (only the prologue's is matched)")) };
                let hn = reg(&h)?;
                let u = self.need_reg(st, g, 4)?;
                let t = self.head("mov32_rr", a, insn) + &self.terms(&[&x[1], &h, &x[3], &x[4], &u]) + &self.tail(st, insn, 5, &[]);
                self.scratch.insert(hn);
                let st2 = self.set_reg(st, a2, hn, 4, u);
                self.then(t, st2)
            }
            // mov r32, imm32
            111 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[0])?;
                nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let t = self.head("mov32_imm", a, insn) + &self.terms(&[&x[0], &x[1]]) + &self.tail(st, insn, 3, &[]);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, x[1].clone());
                self.then(t, st2)
            }
            // sub r32, imm8: GIMPLE's x + -k
            60 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if imm >= 128 { imm + 0xffff_ff00 } else { imm };
                let size = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                if k != 0 || (size != 4 && size != 8) {
                    return Err(bad("not r32/r64, imm8"));
                }
                let gn = reg(&g)?;
                // and r32, imm8 of a byte: in 8 bits; of a shifted word: the field
                if (size, nat(&x[1])) == (4, Some(4)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n == 1 {
                        self.narrows.insert(kk);
                        let t = self.head("and8_imm", a, insn)
                            + &self.terms(&[&g, &x[3], &x[4], &lit(kk), &u])
                            + &self.tail(st, insn, 4, &[format!("{}.narrow8_{}", self.prefix, kk), "simp(L)".into(), "simp(L)".into()]);
                        let r = self.mk("bits_and", vec![lit(8), u, lit(kk)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 1, r);
                        return self.then(t, st2);
                    }
                    if n == 8 {
                        // bits_set_slice(64, W, 15, 0, bits_shr(16, bits_slice(W, 15, 0), pos)), W the word at q
                        let shape = (|| {
                            let s = self.expand(&u);
                            let ss = self.app(&s, "bits_set_slice", 5)?;
                            let sh = self.app(&ss[4], "bits_shr", 3)?;
                            let w16 = self.app(&ss[1], "bits_of_int", 2)?;
                            (nat(&w16[0])? == 16).then_some(())?;
                            let ba = self.app(&w16[1], "gimple.bytes_at", 3)?;
                            (nat(&ba[2])? == 2).then_some(())?;
                            Some((ba[1].clone(), nat(&sh[2])?))
                        })();
                        let (q, pos) = shape.ok_or_else(|| bad("and of a 64-bit value not a shifted word"))?;
                        let kb = (0..16).find(|kb| (1u128 << kb) - 1 == kk).ok_or_else(|| bad("a field mask not 2^k - 1"))?;
                        self.fields.insert((pos, kb, kk));
                        let q = self.canon(&q);
                        let t = self.head("and_field16", a, insn)
                            + &self.terms(&[&g, &x[3], &x[4], &lit(kk), &q, &lit(pos), &lit(kb)])
                            + &self.tail(st, insn, 4, &[format!("{}.field16_{}_{}_{}", self.prefix, pos, kb, kk), "simp(L)".into(), "simp(L)".into(), "simp(L)".into()]);
                        let r = self.parse(&format!(
                            "bits_of_int({kb}, int_mod(int_div(gimple.bytes_at(app(W, \"vm\"), {}, 2), int_pow(2, {pos})), int_pow(2, {kb})))",
                            self.print(&q)
                        ))?;
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(t, st2);
                    }
                }
                let u = self.need_reg(st, gn, size)?;
                match (size, nat(&x[1])) {
                    // sub r64, imm8: GIMPLE's p + -k
                    (8, Some(5)) => {
                        let kk = if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm };
                        let t = self.head("sub64_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &lit(kk), &u]) + &self.tail(st, insn, 6, &[]);
                        let neg = self.mk("bits_neg", vec![lit(64), lit(kk)]);
                        let r = self.mk("bits_add", vec![lit(64), u, neg]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 8, r);
                        self.then(t, st2)
                    }
                    // and r32, imm8
                    (4, Some(4)) => {
                        let t = self.head("and32_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &lit(kk), &u]) + &self.tail(st, insn, 6, &[]);
                        let r = self.mk("bits_and", vec![lit(32), u, lit(kk)]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(t, st2)
                    }
                    (4, Some(5)) => {
                        let t = self.head("sub32_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &lit(kk), &u]) + &self.tail(st, insn, 6, &[]);
                        let neg = self.mk("bits_neg", vec![lit(32), lit(kk)]);
                        let r = self.mk("bits_add", vec![lit(32), u, neg]);
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        self.then(t, st2)
                    }
                    // cmp r32, imm8; ja t
                    (4, Some(7)) => {
                        let (j, jn, a3, tt, cc) = self.jcc(a2)?;
                        if cc != 7 {
                            return Err(bad("cmp not followed by ja"));
                        }
                        let c = self.mk("int_le", vec![u.clone(), lit(kk)]);
                        let text = format!(
                            "mp(tr.cmp32_ja, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                            self.base,
                            self.code,
                            a,
                            a2,
                            a3,
                            tt,
                            insn.len,
                            jn,
                            self.terms(&[&g, &x[3], &x[4], &lit(kk), &j, &u]),
                            st.rs,
                            self.p(&st.spec),
                            insn.name,
                            self.insns[&a2].name,
                            ", simp(L)".repeat(9)
                        );
                        self.branch(st, c, a3, tt, text)
                    }
                    _ => Err(bad("unknown operation")),
                }
            }
            // cmp al, imm8; jbe t
            23 => {
                let k = nat(&f).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let b = self.need_reg(st, 0, 1)?;
                let (j, jn, a3, tt, cc) = self.jcc(a2)?;
                if cc != 6 {
                    return Err(bad("cmp not followed by jbe"));
                }
                let c = self.mk("int_lt", vec![lit(k), b.clone()]);
                let text = format!(
                    "mp(tr.cmp8_jbe, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                    self.base,
                    self.code,
                    a,
                    a2,
                    a3,
                    tt,
                    insn.len,
                    jn,
                    self.terms(&[&f, &j, &b]),
                    st.rs,
                    self.p(&st.spec),
                    insn.name,
                    self.insns[&a2].name,
                    ", simp(L)".repeat(7)
                );
                self.branch(st, c, a3, tt, text)
            }
            // cdqe
            91 => {
                let u = self.need_reg(st, 0, 4)?;
                let t = self.head("cdqe", a, insn) + &self.terms(&[&u]) + &self.tail(st, insn, 3, &[]);
                let r = self.mk("bits_sext", vec![lit(32), lit(64), u]);
                let r = self.value(&r);
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(t, st2)
            }
            // lea r64, [rip + d]: a static's address (the spec's name for it)
            78 => {
                let x = self.pairs(&f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let m = self.record(&x[5]).ok_or_else(|| bad("fields"))?;
                // lea r64, [b + i]: iv + bv
                if let Some(idx) = m.get("index").and_then(|i| self.app(i, "some", 1)).map(|i| i[0].clone()) {
                    let (bk, b) = m.get("base").and_then(|b| self.tag(b)).ok_or_else(|| bad("fields"))?;
                    if bk != 2 || m.get("disp").and_then(nat) != Some(0) || m.get("scale").and_then(nat) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&idx)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let t = self.head("lea_bi", a, insn) + &self.terms(&[&x[1], &b, &idx, &x[2], &x[3], &x[4], &lit(nb), &bv, &iv]) + &self.tail(st, insn, 8, &[]);
                    let r = self.mk("bits_add", vec![lit(64), iv, bv]);
                    let r = self.value(&r);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, r);
                    return self.then(t, st2);
                }
                let d = m.get("disp").and_then(nat).ok_or_else(|| bad("not rip-relative"))?;
                if !m.get("base").map_or(false, |b| self.tag(b).map_or(false, |(k, _)| k == 1)) {
                    return Err(bad("not rip-relative"));
                }
                let addr = (a2 + d) % P64;
                let named = self.vals.iter().find(|(_, t)| self.eval_lit(t) == Some(addr)).map(|(v, _)| Term::var(*v, vec![]));
                let biga = match named {
                    Some(t) => t,
                    None => {
                        let q = match &st.spec {
                            Spec::Proc(i) => self.qs[*i].1.clone(),
                            Spec::Ret(v, _) => v.clone(),
                        };
                        let mut found = None;
                        self.statics(&q, addr, &mut found);
                        for (_, t) in &self.vals {
                            self.statics(t, addr, &mut found);
                        }
                        found.unwrap_or_else(|| lit(addr))
                    }
                };
                let t = self.head("lea_rip", a, insn) + &self.terms(&[&x[1], &lit(d), &x[2], &x[3], &x[4], &biga]) + &self.tail(st, insn, 4, &[]);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, biga);
                self.then(t, st2)
            }
            // movzx r32, byte [b + i]: the spec's byte load at i + b
            79 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // movzx r32, r8 (h holding the byte b)
                if let Some((0, h)) = self.tag(&x[2]) {
                    let hn = reg(&h)?;
                    if x[3] != x[2] || hn >= 4 {
                        return Err(bad("not movzx r32, r8"));
                    }
                    let (n, b) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    // (a value of more bytes, of 8 bits)
                    let t = if n == 1 {
                        self.head("movzx8_rr", a, insn) + &self.terms(&[&x[1], &h, &x[4], &b]) + &self.tail(st, insn, 6, &[])
                    } else {
                        self.head("movzx8_rrw", a, insn) + &self.terms(&[&x[1], &h, &x[4], &lit(n), &b]) + &self.tail(st, insn, 7, &[])
                    };
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, b);
                    return self.then(t, st2);
                }
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                // movzx r32, byte [b + d] (b holding a pointer): the spec's field load
                if self.app(&m["index"], "none", 0).is_some() && nat(&m["disp"]) != Some(0) {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let hc = self.mem_hyp(st, &bp, &d, 1)?;
                    let t = self.head("movzx8_bd", a, insn) + &self.terms(&[&x[1], &b, &d, &x[4], &bp]) + &self.tail(st, insn, 6, &[hc]);
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app(W, \"vm\"), bits_add(64, {}, {}), 1))", self.print(&bp), self.print(&d)))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, v);
                    return self.then(t, st2);
                }
                // movzx r32, byte [b] (b holding the pointer)
                if self.app(&m["index"], "none", 0).is_some() {
                    if bk != 2 || nat(&m["disp"]) != Some(0) || x[3] != x[2] {
                        return Err(bad("not [b]"));
                    }
                    let bn = reg(&b)?;
                    let bv = self.need_reg(st, bn, 8)?;
                    let cond = self.ld8_cond(&bv);
                    let hc = st.hyps.iter().find(|h| h.0 == cond).map(|h| h.1.clone()).ok_or_else(|| format!("{:x}: a byte load at {} the spec does not load", a, self.print(&bv)))?;
                    let t = self.head("movzx8_b", a, insn) + &self.terms(&[&x[1], &b, &x[4], &bv]) + &self.tail(st, insn, 5, &[format!("taut({})", hc)]);
                    let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                    let by = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, bv, lit(1)])]);
                    let by = self.value(&by);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, by);
                    return self.then(t, st2);
                }
                let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) || x[3] != x[2] {
                    return Err(bad("not [b + i]"));
                }
                let (bn, inn) = (reg(&b)?, reg(&i)?);
                let (nb, bv) = self.reg(st, bn).ok_or_else(|| format!("{:x}: register {} holds no value of the procedure", a, bn))?;
                let iv = self.need_reg(st, inn, 8)?;
                let ad = self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]);
                let ad = self.canon(&ad);
                let cond = self.ld8_cond(&ad);
                let hc = st.hyps.iter().find(|h| h.0 == cond).map(|h| h.1.clone()).ok_or_else(|| {
                    let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
                    let vals: Vec<String> = self.vals.iter().map(|(v, t)| format!("{} = {}", self.env.vars[*v as usize].name, self.print(t))).collect();
                    format!("{:x}: a byte load at {} the spec does not load (the facts: {}; the values: {})", a, self.print(&ad), facts.join(", "), vals.join(", "))
                })?;
                let t = self.head("movzx8_ld", a, insn) + &self.terms(&[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv]) + &self.tail(st, insn, 8, &[format!("taut({})", hc)]);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let by = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, ad, lit(1)])]);
                let by = self.value(&by);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 1, by);
                self.then(t, st2)
            }
            // movzx r32, word: from r16, [b + d], [b + i]
            80 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                if x[3] != x[2] || nat(&x[0]) != Some(4) {
                    return Err(bad("not movzx r32, word"));
                }
                if let Some((0, h)) = self.tag(&x[2]) {
                    let hn = reg(&h)?;
                    let (n, b) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                    let t = self.head("movzx16_rrw", a, insn) + &self.terms(&[&x[1], &h, &x[4], &lit(n), &b]) + &self.tail(st, insn, 6, &[]);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, b);
                    return self.then(t, st2);
                }
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                if self.app(&m["index"], "none", 0).is_some() {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let hc = self.mem_hyp(st, &bp, &d, 2)?;
                    let t = self.head("movzx16_bd", a, insn) + &self.terms(&[&x[1], &b, &d, &x[4], &bp]) + &self.tail(st, insn, 6, &[hc]);
                    let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app(W, \"vm\"), bits_add(64, {}, {}), 2))", self.print(&bp), self.print(&d)))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 2, v);
                    return self.then(t, st2);
                }
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                    return Err(bad("not [b + i]"));
                }
                let (bn, inn) = (reg(&b)?, reg(&i)?);
                let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                let iv = self.need_reg(st, inn, 8)?;
                let ad = self.canon(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]));
                let hc = self.mem_hyp(st, &ad, &lit(0), 2)?;
                let t = self.head("movzx16_ld", a, insn) + &self.terms(&[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv]) + &self.tail(st, insn, 8, &[hc]);
                let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app(W, \"vm\"), {}, 2))", self.print(&ad)))?;
                let v = self.value(&v);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 2, v);
                self.then(t, st2)
            }
            // and rax, imm32 (sign-extended): the spec's form of the immediate
            49 => {
                let x = self.pairs(&f, 2).ok_or_else(|| bad("fields"))?;
                let k = nat(&x[1]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                if nat(&x[0]) != Some(8) {
                    return Err(bad("not and rax, imm32"));
                }
                let u = self.need_reg(st, 0, 8)?;
                let kk64 = if k >= 1 << 31 { k + 0xffff_ffff_0000_0000 } else { k };
                // (a negative immediate as GIMPLE writes it: bits_neg(64, -k))
                let kk = if kk64 >= 1 << 63 { self.mk("bits_neg", vec![lit(64), lit(P64 - kk64)]) } else { lit(kk64) };
                let t = self.head("and64_imm", a, insn) + &self.terms(&[&x[1], &kk, &u]) + &self.tail(st, insn, 5, &[]);
                let r = self.mk("bits_and", vec![lit(64), u, kk]);
                let r = self.value(&r);
                self.scratch.insert(0);
                let st2 = self.set_reg(st, a2, 0, 8, r);
                self.then(t, st2)
            }
            // test r8, r8; jne t / test r64, r64; je t
            25 | 61 => {
                let (g, size) = if insn.row == 25 {
                    let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                    (x[0].clone(), 1)
                } else {
                    let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                    (x[1].clone(), 8)
                };
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, size)?;
                let (j, jn, a3, tt, cc) = self.jcc(a2)?;
                let (rule, want, nprem) = if size == 1 { ("test8_jne", 5, 8) } else { ("test64_je", 4, 7) };
                if cc != want {
                    return Err(bad("test not followed by the matched jump"));
                }
                let z = self.mk("eq", vec![u.clone(), lit(0)]);
                let c = if size == 1 { z } else { self.mk("not", vec![z]) };
                let text = format!(
                    "mp(tr.{}, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                    rule,
                    self.base,
                    self.code,
                    a,
                    a2,
                    a3,
                    tt,
                    insn.len,
                    jn,
                    self.terms(&[&g, &j, &u]),
                    st.rs,
                    self.p(&st.spec),
                    insn.name,
                    self.insns[&a2].name,
                    ", simp(L)".repeat(nprem)
                );
                self.branch(st, c, a3, tt, text)
            }
            // movsx r32, r8
            81 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let (k, h) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 || x[3] != x[2] {
                    return Err(bad("not movsx r32, r8"));
                }
                let hn = reg(&h)?;
                if hn >= 4 {
                    return Err(bad("a high byte register"));
                }
                let b = self.need_reg(st, hn, 1)?;
                let t = self.head("movsx8", a, insn) + &self.terms(&[&x[1], &h, &x[4], &b]) + &self.tail(st, insn, 6, &[]);
                let r = self.mk("bits_sext", vec![lit(8), lit(32), b]);
                let r = self.value(&r);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 4, r);
                self.then(t, st2)
            }
            // ret: eax the spec's result
            122 => {
                let Spec::Ret(val, pr) = &st.spec else {
                    return Err(format!("{:x}: ret before the procedure's result (the spec at {})", a, match &st.spec {
                        Spec::Proc(i) => self.print(&self.qs[*i].1),
                        _ => String::new(),
                    }));
                };
                let n = self.rbytes;
                let v = self.need_reg(st, 0, n)?;
                if &v != val {
                    return Err(format!("{:x}: rax holds {}, the spec returns {}", a, self.print(&v), self.print(val)));
                }
                let expr = format!(
                    "mp(tr.ret_insn, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{HS}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {{{}}}, {}, simp(L), simp(L), mp(tr.result{}, {{W}}, {{{}}}))",
                    self.base,
                    self.code,
                    a,
                    insn.len,
                    st.rs,
                    pr,
                    n,
                    self.print(val),
                    insn.name,
                    8 * n,
                    self.print(val)
                );
                Ok(Pf { lines: vec![], expr })
            }
            _ => Err(bad("no rule for the instruction")),
        }
    }

    /// the conditional jump at a2: its displacement field, decode fact's
    /// length, the fall-through, the target, the condition code
    fn jcc(&self, a2: u128) -> Result<(Term, u128, u128, u128, u128), String> {
        let j = self.insns.get(&a2).ok_or_else(|| format!("no decode fact at {:x}", a2))?;
        let x = (j.row == 127).then(|| self.pairs(&j.fields, 2)).flatten().ok_or_else(|| format!("{:x}: not a conditional jump", a2))?;
        let (cc, r) = (nat(&x[0]).ok_or("jcc")?, nat(&x[1]).ok_or("jcc")?);
        let a3 = (a2 + j.len) % P64;
        let r8 = r & 0xff;
        let t = (a3 + if r8 >= 128 { r8 + P64 - 256 } else { r8 }) % P64;
        Ok((x[1].clone(), j.len, a3, t, cc))
    }

    /// nullary defined constants of `t` whose value is `addr`
    fn statics(&self, t: &Term, addr: u128, found: &mut Option<Term>) {
        match t.node() {
            Node::App(s, a) => {
                if a.is_empty() {
                    if let SymKind::Defined { params, body } = &self.env.syms[*s as usize].kind {
                        if params.is_empty() && nat(body) == Some(addr) {
                            *found = Some(t.clone());
                        }
                    }
                }
                a.iter().for_each(|x| self.statics(x, addr, found));
            }
            Node::Var(_, a) => a.iter().for_each(|x| self.statics(x, addr, found)),
            _ => {}
        }
    }
}

/// The files' statements: a theorem becomes a claim (its statement); a
/// schematic one is returned as (name, parameters, statement), to be read
/// with its parameters -- the generator reads statements only, and checks
/// nothing.
fn statements(src: &str) -> (String, Vec<(String, String, String)>) {
    let code = |l: &str| l.split("//").next().unwrap_or("").trim().to_string();
    let mut out = String::new();
    let mut schem = Vec::new();
    let mut lines = src.split_inclusive('\n');
    while let Some(l) = lines.next() {
        let Some(rest) = l.strip_prefix("theorem ") else {
            out.push_str(l);
            continue;
        };
        let mut head = rest.to_string();
        loop {
            let Some(n) = lines.next() else { break };
            if code(n) == "proof" {
                break;
            }
            head.push_str(n);
        }
        let mut nest = 1;
        while nest > 0 {
            let Some(n) = lines.next() else { break };
            let t = code(n);
            if t == "qed" {
                nest -= 1;
            } else if t == "proof" || t.ends_with(" proof") {
                nest += 1;
            }
        }
        let i = head.find(|c: char| c == ':' || c == '(').unwrap_or(0);
        if head[i..].starts_with('(') {
            // NAME(params): statement (the parameters' parentheses balanced)
            let mut depth = 0;
            let mut end = i;
            for (k, c) in head[i..].char_indices() {
                match c {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = i + k;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let stmt = head[end + 1..].trim_start().strip_prefix(':').unwrap_or("").to_string();
            schem.push((head[..i].to_string(), head[i + 1..end].to_string(), stmt));
        } else {
            out.push_str("claim ");
            out.push_str(&head);
        }
    }
    (out, schem)
}

pub fn translate(args: &[String]) -> CResult {
    let mut out_path = None;
    let mut pos = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "-o" {
            out_path = it.next().cloned();
        } else {
            pos.push(a.clone());
        }
    }
    let (Some(out_path), true) = (out_path, pos.len() >= 4) else { return Err(USAGE.into()) };
    let (fname, spec_name, prefix) = (pos[0].clone(), pos[1].clone(), pos[2].clone());
    let mut env = Env::new();
    let mut schem = Vec::new();
    for (i, f) in pos[3..].iter().enumerate() {
        let src = std::fs::read_to_string(f).map_err(|e| format!("{}: {}", f, e))?;
        let (text, s) = statements(&src);
        syntax::load(&mut env, &text, i == 0).map_err(|e| format!("{}: {}", f, e))?;
        schem.extend(s);
    }
    // the schematic lemmas (the rules' statements)
    let mut lemmas = HashMap::new();
    for (name, ps, stmt) in schem {
        if !name.starts_with("tr.") {
            continue;
        }
        let mut scope = Vec::new();
        let mut vars = Vec::new();
        for p in ps.split(',') {
            let (bound, v) = match p.rsplit_once('.') {
                Some((b, v)) => (b.split_whitespace().count() as u32, v.trim()),
                None => (0, p.trim()),
            };
            let id = env.new_var(v, bound);
            scope.push((v.to_string(), id));
            vars.push(id);
        }
        let t = syntax::parse_term(&mut env, &stmt, &scope).map_err(|e| format!("{}: {}", name, e.0))?;
        lemmas.insert(name, (vars, t));
    }

    // the decode facts
    let mut insns: BTreeMap<u128, Insn> = BTreeMap::new();
    let pre = format!("{}.at_", fname);
    for (name, t) in env.claims.clone() {
        if !name.starts_with(&pre) {
            continue;
        }
        let g = Gen0(&env);
        let parsed = (|| -> Option<(u128, Insn)> {
            let t = &g.app(t.clone(), "all")?;
            let t = &g.app(t.clone(), "all")?;
            let i1 = g.imp(t)?;
            let i2 = g.imp(&i1.1)?;
            let i3 = g.imp(&i2.1)?;
            let ca = g.args(&i2.0, "abi.code_at")?;
            let rip = g.args(&i3.0, "eq")?;
            let ex = g.args(&g.args(&i3.1, "runs")?[0], "x86_64_linux.exec_body")?;
            let tg = g.args(&ex[1], "tag")?;
            Some((
                nat(&rip[1])?,
                Insn { name: name.clone(), len: nat(&ex[0])?, row: nat(&tg[0])?, fields: tg[1].clone(), base: ca[1].clone(), code: ca[2].clone() },
            ))
        })();
        let (a, insn) = parsed.ok_or_else(|| format!("{}: not a decode fact", name))?;
        insns.insert(a, insn);
    }
    let (&entry, first) = insns.iter().next().ok_or_else(|| format!("no decode facts `{}*`", pre))?;
    let (base_t, code_t) = (first.base.clone(), first.code.clone());
    if nat(&base_t) != Some(entry) {
        return Err(format!("the first decode fact is at {:x}, not the base", entry));
    }

    // the spec: fn_build(D, x0. mkprog(x1 x2. !ord_le(1, seq_len(x0)) || bind_rel(PROC, x1, KW, EXC, DIV)))
    let ssym = *env.sym_by_name.get(&spec_name).ok_or_else(|| format!("no spec `{}`", spec_name))?;
    let SymKind::Defined { body: sbody, .. } = env.syms[ssym as usize].kind.clone() else { return Err(format!("`{}` is not a definition", spec_name)) };
    let mut g = Gen {
        env: &mut env,
        names: Vec::new(),
        vals: Vec::new(),
        zs: Vec::new(),
        qs: Vec::new(),
        lets: Vec::new(),
        lemmas,
        insns,
        hs: BTreeMap::new(),
        imuls: BTreeSet::new(),
        narrows: BTreeSet::new(),
        fields: BTreeSet::new(),
        rbytes: 4,
        scratch: BTreeSet::new(),
        base: String::new(),
        code: String::new(),
        prefix: prefix.clone(),
        kw: Term::bvar(0),
        w: Term::bvar(0),
        n: 0,
    };
    let args_t = g.var("args");
    g.var("s");
    g.w = g.var("W");
    let q_t = g.var("q");
    g.base = g.print(&base_t);
    g.code = g.print(&code_t);
    let parts = (|| -> Option<(Term, Term, Term)> {
        let fb = g.app(&sbody, "fn_build", 2)?;
        let mp = g.app(&fb[1], "mkprog", 1)?;
        let or = g.app(&mp[0], "or", 2)?;
        let guard = g.app(&or[0], "not", 1)?;
        let le = g.app(&guard[0], "ord_le", 2)?;
        (nat(&le[0])? == 1).then_some(())?;
        let br = g.app(&or[1], "bind_rel", 5)?;
        matches!(br[1].node(), Node::BVar(1)).then_some(())?;
        // PROC(x0); KW(x3, x4, x2); the wrapper without x0
        let proc = g.lam(&br[0], &["x0", "x1", "x2"], &["x0"])?;
        let kw = g.lam(&br[2], &["x0", "x1", "x2", "x3", "x4"], &["x3", "x4", "x2"])?;
        let bs = g.env.syms[g.env.sym_by_name["bind_rel"] as usize].binders.clone();
        let rest: Vec<Term> = br[1..].iter().zip(&bs[1..]).map(|(x, &k)| g.remap(x, k, &|i| (i < 2).then_some(i))).collect::<Option<_>>()?;
        let mut wa = vec![q_t.clone()];
        wa.extend(rest);
        let wrap = g.mk("mkprog", vec![g.mk("bind_rel", wa)]);
        Some((proc, kw, wrap))
    })();
    let (proc, kw, wrap) = parts.ok_or_else(|| format!("`{}`: not a one-argument procedure's spec", spec_name))?;
    g.kw = kw.clone();
    // (the result's width: the wrapper's gimple.result(N, ..))
    fn result_bits(g: &Gen, t: &Term) -> Option<u128> {
        if let Some(a) = g.app(t, "gimple.result", 2) {
            return nat(&a[0]);
        }
        match t.node() {
            Node::App(_, a) => a.iter().find_map(|x| result_bits(g, x)),
            _ => None,
        }
    }
    g.rbytes = result_bits(&g, &kw).unwrap_or(32) / 8;

    // the entry: mov [rsp + d], edi / rdi (the argument's n bytes)
    let (e_len, e_name, ef) = {
        let e0 = &g.insns[&entry];
        (e0.len, e0.name.clone(), g.pairs(&e0.fields, 5).ok_or("the entry's fields")?)
    };
    let (d, n) = match (g.insns[&entry].row, nat(&ef[0]), nat(&ef[1]), g.rsp_mem(&ef[2])) {
        (75, Some(n), Some(7), Some(d)) if n == 4 || n == 8 => (d, n),
        _ => return Err(format!("the entry {:x} is not `mov [rsp + d], edi` or `rdi`", entry)),
    };
    let dn = nat(&d).ok_or("the entry's displacement")?;
    let a2 = (entry + e_len) % P64;
    let x = g.mk("bits_of_int", vec![lit(8 * n), g.mk("app", vec![args_t.clone(), lit(0)])]);
    // (the entry rule, the argument register's value stored)
    let (entry_rule, arg_reg) = if n == 8 { ("tr.entry1_64", "app(app(s, \"gpr\"), 7)".to_string()) } else { ("tr.entry1_32", "bits_slice(app(app(s, \"gpr\"), 7), 31, 0)".to_string()) };
    let q0raw = proc.instantiate_params(&[args_t.clone()], &g.env.binders_fn());
    let Node::Var(qv, _) = q_t.node() else { unreachable!() };
    let wrap_q0 = wrap.subst_var(*qv, &q0raw, &g.env.binders_fn());
    let xn = g.value(&x);
    g.hs.insert(dn, (n, xn.clone()));
    let q0 = g.canon(&q0raw);
    let i0 = g.new_q(q0);

    // the proof
    let st0 = St { a: a2, regs: Vec::new(), rs: "empty".into(), spec: Spec::Proc(i0), hyps: Vec::new() };
    let pf = g.prove(st0)?;

    // the text
    let mut o = String::new();
    o.push_str(&format!(
        "// {}'s C1 by translation (docs/bridge-pattern-design.md). Generated by\n//   slc translate {} {} {} -o OUT.core FILES (the spec's and the decode facts' files, proofs/translate.core)\n// Each step: a rule of proofs/translate.core with its instance -- a spec\n// reduction, or an instruction (its decode fact, build/leaf_steps.core;\n// literal facts, simp(L)) -- then the next point. Checked after\n// proofs/translate.core.\n\n",
        fname, fname, spec_name, prefix
    ));
    let view = format!("tr.view1(s, {}, {}, {})", dn, n, arg_reg);
    o.push_str(&format!("abbrev {p}.v(s) := {}\nabbrev {p}.w(s) := abi.view({p}.v(s), s)\n\n", view, p = prefix));
    for c in g.imuls.clone() {
        o.push_str(&format!(
            "theorem {p}.imul_{c}: tr.imul_by({c})\nproof\n  have g: all y. y in bits(32) -> bits_add(32, int_mul(sint(32, y), sint(32, {c})), 0) = bits_mul(32, y, {c}) proof\n    fix y\n    assume hy: y in bits(32)\n    have c1: int_lt(y, 2147483648) -> bits_add(32, int_mul(sint(32, y), {c}), 0) = bits_mul(32, y, {c}) proof\n      assume hl: int_lt(y, 2147483648)\n      show by defs(simp(hy, hl), bits_add, bits_mul, sint)\n    qed\n    have c2: !int_lt(y, 2147483648) -> bits_add(32, int_mul(sint(32, y), {c}), 0) = bits_mul(32, y, {c}) proof\n      assume hl: !int_lt(y, 2147483648)\n      have e: int_mod(int_mul(int_sub(y, 4294967296), {c}), 4294967296) = int_mod(int_mul(y, {c}), 4294967296) by arith(hy)\n      show by defs(simp(hy, hl, e), bits_add, bits_mul, sint)\n    qed\n    have e: bits_add(32, int_mul(sint(32, y), {c}), 0) = bits_mul(32, y, {c}) by taut(c1, c2)\n    show by simp(e)\n  qed\n  show by defs(g, tr.imul_by)\nqed\n\n",
            p = prefix,
            c = c
        ));
    }
    for kk in g.narrows.clone() {
        o.push_str(&format!(
            "theorem {p}.narrow8_{kk}: tr.narrow8({kk})\nproof\n  have g: all u. u in bits(8) -> bits_and(32, u, {kk}) = bits_and(8, u, {kk}) proof\n    fix u\n    assume h: u in bits(8)\n    show by simp(h)\n  qed\n  show by defs(g, tr.narrow8)\nqed\n\n",
            p = prefix
        ));
    }
    for (pos, kb, kk) in g.fields.clone() {
        let x16 = "bits_of_int(16, x)";
        o.push_str(&format!(
            "theorem {p}.field16_{pos}_{kb}_{kk}: tr.field16({pos}, {kb}, {kk})\nproof\n  have g: all x. x in bits(16) -> bits_and(32, bits_slice(bits_set_slice(64, {x16}, 15, 0, bits_shr(16, bits_slice({x16}, 15, 0), {pos})), 31, 0), {kk}) = bits_of_int({kb}, int_mod(int_div(x, int_pow(2, {pos})), int_pow(2, {kb}))) proof\n    fix x\n    assume hx: x in bits(16)\n    have d: int_div(x, {d}) in bits({rb}) by arith(hx)\n    have d16: int_div(x, {d}) in bits(16) by arith(hx)\n    show by defs(simp(hx, d, d16), bits_shr, bits_of_int, pow2)\n  qed\n  show by defs(g, tr.field16)\nqed\n\n",
            p = prefix,
            d = 1u128 << pos,
            rb = 16 - pos
        ));
    }
    let p = &prefix;
    o.push_str(&format!(
        "theorem {p}.body: all args s. args in abi.ARGS -> s in x86_64_linux.Machine -> ord_le(1, seq_len(args)) -> {p}.w(s) in univ(1) ->\n  tr.pt(s, {p}.v(s), {}, {}, {}, fn_update(empty, {}, pair({}, bits_of_int({}, app(args, 0)))), empty,\n    {}, {p}.w(s))\nproof\n",
        g.base,
        g.code,
        a2,
        dn,
        n,
        8 * n,
        g.print(&wrap_q0)
    ));
    o.push_str("  fix args\n  fix s\n  assume hA: args in abi.ARGS\n  assume hM: s in x86_64_linux.Machine\n  assume hg: ord_le(1, seq_len(args))\n");
    o.push_str(&format!("  assume hvu: {p}.w(s) in univ(1)\n"));
    let mut l = vec!["tr.dom_upd".to_string(), "tr.dom_keep".to_string()];
    let mut lt = vec!["(all f k v. k in dom(fn_update(f, k, v)))".to_string(), "(all f k j v. k in dom(f) -> !(k = j) -> k in dom(fn_update(f, j, v)))".to_string()];
    for r in &g.scratch {
        o.push_str(&format!("  have sc{r}: tr.scratch_reg({r}) by defs(simp(), tr.scratch_reg)\n"));
        l.push(format!("sc{}", r));
        lt.push(format!("tr.scratch_reg({})", r));
    }
    o.push_str(&format!("  // the literal facts: a map's keys, the registers written\n  have L: {} by taut({})\n", lt.join(" && "), l.join(", ")));
    let kwl = g.lambda(3, &g.kw);
    let kwb = kwl.split_once(". ").map(|x| x.1.to_string()).unwrap_or(kwl.clone());
    o.push_str(&format!("  // the wrapper: the procedure's rest q, its result returned\n  let KW(x0, x1, x2) := {}\n", kwb));
    o.push_str(&format!("  let WRAP(q) := {}\n", g.print(&wrap)));
    o.push_str(&format!("  let V := {p}.v(s)\n  let W := {p}.w(s)\n"));
    if !g.zs.is_empty() {
        o.push_str("  // the choices' witnesses (no machine value is one)\n");
        for z in &g.zs {
            o.push_str(&format!("  let {} := 0\n", g.env.vars[*z as usize].name));
        }
    }
    o.push_str("  // the values\n");
    for (v, t) in &g.vals {
        o.push_str(&format!("  let {} := {}\n", g.env.vars[*v as usize].name, g.print(t)));
    }
    o.push_str(&format!("  let HS := fn_update(empty, {}, pair({}, {}))\n", dn, n, g.print(&xn)));
    o.push_str("  // the spec's rest at each point\n");
    for (n, t) in &g.qs {
        o.push_str(&format!("  let {} := {}\n", n, g.print(t)));
    }
    o.push_str("  // the registers after each write; the wrapper after the result\n");
    for (n, t) in &g.lets {
        o.push_str(&format!("  let {} := {}\n", n, t));
    }
    o.push_str("  // the steps (each from the next point's claim)\n");
    for line in &pf.lines {
        o.push_str(&format!("  {}\n", line));
    }
    o.push_str(&format!("  show := {}\nqed\n\n", pf.expr));
    let ql = g.lambda(1, &proc);
    o.push_str(&format!(
        "theorem {p}.implements: all statics. abi.implements2_at(single(empty), {b}, {spec}(), {b}, {c}, statics)\nproof\n  fix statics\n  have m0 := mp({er}[base := {b}, code := {c}, statics := statics, f := {b}, len := {len}, d := {d}, z1 := {z1}, z2 := {z2}, a2 := {a2},\n    q := {ql}, kw := {kwl}],\n    simp(), {at0}, simp(), simp(), simp(), simp(), {p}.body)\n",
        er = entry_rule,
        b = g.base,
        c = g.code,
        spec = spec_name,
        len = e_len,
        d = dn,
        z1 = g.print(&ef[3]),
        z2 = g.print(&ef[4]),
        a2 = a2,
        at0 = e_name,
    ));
    o.push_str(&format!(
        "  have m: all args s o. args in abi.ARGS -> s in x86_64_linux.Machine -> abi.loaded(app(s, \"vm\"), {b}, {c}, statics) -> app(s, \"rip\") = {b} ->\n      abi.entry_ok(s, args) -> runs(abi.run_to_return(), s, o) -> abi.matches({spec}(), args, s, o) by defs(m0, {spec})\n  show := apply(abi.bridge_implements, m)\nqed\n",
        b = g.base,
        c = g.code,
        spec = spec_name
    ));
    std::fs::write(&out_path, o).map_err(|e| format!("{}: {}", out_path, e))?;
    println!("{}: {} spec rests, {} values, {} lines", out_path, g.qs.len(), g.vals.len(), pf.lines.len());
    Ok(())
}

/// statement access before the generator's state exists
struct Gen0<'e>(&'e Env);

impl Gen0<'_> {
    fn args(&self, t: &Term, name: &str) -> Option<Vec<Term>> {
        match t.node() {
            Node::App(s, a) if self.0.syms[*s as usize].name == name => Some(a.to_vec()),
            _ => None,
        }
    }
    fn app(&self, t: Term, name: &str) -> Option<Term> {
        self.args(&t, name).map(|a| a[0].clone())
    }
    fn imp(&self, t: &Term) -> Option<(Term, Term)> {
        match t.node() {
            Node::App(s, a) if *s == self.0.builtins.imp => Some((a[0].clone(), a[1].clone())),
            _ => None,
        }
    }
}
