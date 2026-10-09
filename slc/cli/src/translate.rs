//! `slc translate`: the certificate of a function's C1 by statement patterns
//! (docs/overview.md, C1). Not trusted: it writes a proof that
//! `slc kernel-check` checks, with proofs/translate.core's,
//! proofs/translate_frame.core's and proofs/translate_store_loop.core's
//! rules.
//!
//! The entry is the function's first instruction, its arguments in their
//! registers (tr.entry_n); the prologue (`sub rsp, k`, the arguments'
//! stores) is instructions as any. A home store names the homes it leaves
//! (a tr.hkeep chain over the map's entries).
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
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

const USAGE: &str = "usage: slc translate FN SPEC PREFIX -o OUT.core FILE.core...";
const P64: u128 = 1 << 64;

/// A decode fact: at its address, `len` bytes decode to `tag(row, fields)`.
#[derive(Clone)]
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
    /// the frame's size: rsp is the entry's minus fr (`tr.inv`)
    fr: u128,
    /// the registers written: register, bytes, value
    regs: Vec<(u128, u128, Term)>,
    /// their map's name
    rs: String,
    /// the frame's depth (`tr.pt`'s fd, the function's: its literal)
    ds: String,
    /// the spec's world (its placeholder), its name, the fact that it is a
    /// set (`hvu`) and a world (`hw`)
    w: Term,
    wn: String,
    hvu: String,
    hw: String,
    /// the homes: offset -> (bytes, value), and the map's text
    hsm: BTreeMap<u128, (u128, Term)>,
    hst: String,
    /// the loop whose body this is (an index into `loops`)
    lp: Option<usize>,
    spec: Spec,
    /// the facts in scope: a branch's condition (or its negation), a
    /// defined operation's condition, by name
    hyps: Vec<(Term, String)>,
    /// in a zero-initialization (`tr.ptz`): the zero xmm register, the
    /// address of the bytes still to be stored (a base, an offset), their
    /// count
    z: Option<(u128, Term, u128, u128)>,
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
    /// a store defined under `cond` (the rest kept: the machine's store
    /// makes it), raising as `Split`'s
    Guard { cond: Term, ub: (usize, String) },
    /// a call of `g` with one argument `ar` (the machine's `call` makes
    /// it): the block's continuation, handlers and rest
    /// (`one`: call1, the result's rax only)
    Call { g: Term, args: Vec<Term>, list: Term, one: bool, a: Term, xx: Term, dd: Term, k: Term },
}

/// A store of the spec: st8(p, off, v) or st32(p, off, v) (or a helper
/// whose body is one, named), its width, its definedness, its address
struct StoreOp {
    n: u128,
    cond: Term,
    p: Term,
    off: Term,
    v: Term,
    addr: Term,
    inner: Term,
    helper: Option<String>,
    ub: String,
    /// st_bytes of zeros: its list (the stored value 0, n its length)
    data: Option<Term>,
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
    /// the function's frame depth (`tr.frame`): its stack accesses reach
    /// fd bytes below the entry's rsp
    fd: u128,
    /// the current point's frame size, world, its name, its `in univ(1)`
    /// fact (set by `prove`)
    fr: u128,
    w: Term,
    wn: String,
    hvu: String,
    /// the spec's view at the entry (`W`): the state of its raises
    vw: Term,
    n: usize,
    /// the loops met: their heads and claims
    loops: Vec<Loop>,
    /// the values' count (their names); the rests and lets local to a
    /// loop's step (defined in its proof)
    nval: usize,
    scoped_q: BTreeSet<usize>,
    scoped_l: BTreeSet<usize>,
    /// the literal facts' name list for simp (`L`, and a loop step's)
    lf: String,
    /// the register maps' updates: a map's name -> its parent's, the
    /// register, the value pair
    rmaps: HashMap<String, (String, u128, String)>,
    /// the calls met: the callee (a spec parameter), its address, the
    /// call's number of arguments, whether a call enters it with the stack
    /// not aligned (its contract then for any entry: tr.implements_at_u)
    callees: Vec<(Term, u128, usize, bool)>,
    /// the contract's code: the function's own, or with its callees'
    lbase: String,
    lcode: String,
}

/// A loop of the spec met at a machine address (its head): the claim there,
/// for every world and local with the invariant, by induction on the variant
#[derive(Clone)]
struct Loop {
    head: u128,
    /// the induction hypothesis' name, the bound K of the counting loop,
    /// the home d of its counter
    ih: String,
    k: u128,
    d: u128,
    /// the rest at the head, the counter abstracted (a term of the counter's
    /// placeholder `li`)
    qh: Term,
    li: Term,
    /// in the step: the counter's fact (tr.count_inv expanded)
    ci: String,
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
        let name = format!("T{}", self.nval);
        self.nval += 1;
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

    /// an n-bit literal `bits_of_int(n, k)` as k (as the machine has it)
    fn lit_bits(&self, t: &Term) -> Term {
        if let Some(a) = self.app(t, "bits_of_int", 2) {
            if let (Some(n), Some(k)) = (nat(&a[0]), nat(&a[1])) {
                if n < 128 && k < 1 << n {
                    return a[1].clone();
                }
            }
        }
        t.clone()
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
        let pv = format!("pair({}, {})", n, self.print(&v));
        self.lets.push((name.clone(), format!("fn_update({}, {}, {})", st.rs, r, pv)));
        self.rmaps.insert(name.clone(), (st.rs.clone(), r, pv));
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
        format!("tr.pt(s, V, {}, {}, {}, {}, {}, {}, {}, {}, {})", self.base, self.code, st.fr, a, st.hst, st.ds, st.rs, self.p(&st.spec), st.wn)
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
        let (v, facts) = self.guard_facts(g, hyps)?;
        // (the fact itself, or simp from the facts it rests on)
        if v && facts.len() == 1 && hyps.iter().any(|h| h.0 == *g && h.1 == facts[0]) {
            return Some((v, facts[0].clone()));
        }
        Some((v, format!("simp({})", facts.join(", "))))
    }

    /// a guard's value, and the facts in scope it rests on
    fn guard_facts(&self, g: &Term, hyps: &[(Term, String)]) -> Option<(bool, Vec<String>)> {
        if let Some(h) = hyps.iter().find(|h| h.0 == *g) {
            return Some((true, vec![h.1.clone()]));
        }
        if self.app(g, "true", 0).is_some() {
            return Some((true, vec![]));
        }
        let join = |mut x: Vec<String>, y: Vec<String>| {
            for f in y {
                if !x.contains(&f) {
                    x.push(f);
                }
            }
            x
        };
        if let Some(a) = self.app(g, "not", 1) {
            let (v, f) = self.guard_facts(&a[0], hyps)?;
            return Some((!v, f));
        }
        if let Some(a) = self.app(g, "and", 2) {
            let (x, f) = self.guard_facts(&a[0], hyps)?;
            let (y, f2) = self.guard_facts(&a[1], hyps)?;
            return Some((x && y, join(f, f2)));
        }
        if let Some(a) = self.app(g, "or", 2) {
            let (x, f) = self.guard_facts(&a[0], hyps)?;
            let (y, f2) = self.guard_facts(&a[1], hyps)?;
            return Some((x || y, join(f, f2)));
        }
        if let Some(a) = self.app(g, "eq", 2) {
            if a[0] == a[1] && g.loose_depth(&self.env.binders_fn()) == 0 {
                return Some((true, vec![]));
            }
            let v = match (a[0].node(), a[1].node()) {
                (Node::Nat(x), Node::Nat(y)) => x == y,
                (Node::Bytes(x), Node::Bytes(y)) => x == y,
                _ => return None,
            };
            return Some((v, vec![]));
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

    /// An equation of a term (of x0 only) with itself in the rest's body:
    /// it, its side (at the body)
    fn refl_redex(&self, t: &Term, depth: u32) -> Option<(Term, Term)> {
        let lift = |x: &Term| self.remap(x, 0, &|j| (j == depth + 1).then_some(1));
        if let Some(e) = self.app(t, "eq", 2) {
            if e[0] == e[1] {
                if let (Some(r), Some(s)) = (lift(t), lift(&e[0])) {
                    return Some((r, s));
                }
            }
        }
        if let Node::App(s, a) = t.node() {
            let bs = self.env.syms[*s as usize].binders.clone();
            for (x, k) in a.iter().zip(bs) {
                if let Some(r) = self.refl_redex(x, depth + k) {
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
        let (c, r, ok, ub) = self.op_raw(op)?;
        Ok((c, r, self.lfacts(&ok), self.lfacts(&ub)))
    }

    /// a text's literal facts (`simp(L)`): in a loop's step, with its
    /// counter's facts
    /// `g in dom(rs)` for the register map named rs, by its updates: g's
    /// own (`tr.dom_upd`) under the later ones (`tr.dom_keep`) -- None for a
    /// register not in it
    fn dom_pf(&self, rs: &str, g: u128) -> Option<String> {
        let (parent, r, pv) = self.rmaps.get(rs)?;
        if *r == g {
            return Some(format!("all_elim(tr.dom_upd, {{{parent}}}, {{{g}}}, {{{pv}}})"));
        }
        let inner = self.dom_pf(parent, g)?;
        Some(format!("mp(all_elim(tr.dom_keep, {{{parent}}}, {{{g}}}, {{{r}}}, {{{pv}}}), {inner}, simp())"))
    }

    /// `!(g in dom(rs))` for a register not in the map named rs, by its
    /// updates (`tr.dom_out`) down to empty (`tr.dom_none`)
    fn dom_out_pf(&self, rs: &str, g: u128) -> Option<String> {
        if rs == "empty" {
            return Some(format!("all_elim(tr.dom_none, {{{g}}})"));
        }
        let (parent, r, pv) = self.rmaps.get(rs)?;
        if *r == g {
            return None;
        }
        let inner = self.dom_out_pf(parent, g)?;
        Some(format!("mp(all_elim(tr.dom_out, {{{parent}}}, {{{g}}}, {{{r}}}, {{{pv}}}), {inner}, simp())"))
    }

    /// the registers two updates or more below the top of the map rs: their
    /// `in dom` facts (simp(L) shows the others)
    fn deep_doms(&self, rs: &str) -> Vec<String> {
        let mut seen = Vec::new();
        let mut out = Vec::new();
        let (mut cur, mut depth) = (rs.to_string(), 0);
        while let Some((parent, r, _)) = self.rmaps.get(&cur) {
            if !seen.contains(r) {
                seen.push(*r);
                if depth >= 2 {
                    out.extend(self.dom_pf(rs, *r));
                }
            }
            cur = parent.clone();
            depth += 1;
        }
        out
    }

    fn lfacts(&self, t: &str) -> String {
        if self.lf == "L" {
            return t.to_string();
        }
        t.replace("simp(L)", &format!("simp({})", self.lf)).replace("simp(L, ", &format!("simp({}, ", self.lf))
    }

    fn op_raw(&mut self, op: &Term) -> Result<(Option<Term>, Term, String, String), String> {
        let w = self.print(&self.w.clone());
        let hv = self.hvu.clone();
        let pr = |g: &Gen, t: &Term| g.print(t);
        if let Some(x) = self.app(op, "gimple.sadd", 3) {
            if nat(&x[0]) == Some(32) {
                let (a, b) = (x[1].clone(), x[2].clone());
                let s32 = |g: &Gen, t: &Term| g.mk("sint", vec![lit(32), t.clone()]);
                let ty = self.mk("fn_update", vec![self.mk("fn_update", vec![self.mk("empty", vec![]), Term::bytes(b"prec"), lit(32)]), Term::bytes(b"signed"), self.mk("true", vec![])]);
                let cond = self.mk("gimple.fits", vec![ty, self.mk("int_add", vec![s32(self, &a), s32(self, &b)])]);
                let r = self.mk("bits_add", vec![lit(32), a.clone(), b.clone()]);
                let ok = format!("mp(tr.sadd32_ok, {{{w}}}, {{{}}}, {{{}}}, {hv}, simp(L), simp(L), {{HC}})", pr(self, &a), pr(self, &b));
                let ub = format!("mp(tr.sadd32_ub, {{{w}}}, {{{}}}, {{{}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), {{HN}})", pr(self, &a), pr(self, &b));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        if let Some(x) = self.app(op, "gimple.ssub", 3) {
            if nat(&x[0]) == Some(32) {
                let (a, b) = (x[1].clone(), x[2].clone());
                let s32 = |g: &Gen, t: &Term| g.mk("sint", vec![lit(32), t.clone()]);
                let ty = self.mk("fn_update", vec![self.mk("fn_update", vec![self.mk("empty", vec![]), Term::bytes(b"prec"), lit(32)]), Term::bytes(b"signed"), self.mk("true", vec![])]);
                let cond = self.mk("gimple.fits", vec![ty, self.mk("int_sub", vec![s32(self, &a), s32(self, &b)])]);
                let r = self.mk("bits_sub", vec![lit(32), self.lit_bits(&a), b.clone()]);
                let ok = if self.lit_bits(&a) != a {
                    format!("mp(tr.ssub32_ok_lit, {{{w}}}, {{{}}}, {{{}}}, {hv}, simp(L), simp(L), {{HC}})", pr(self, &self.lit_bits(&a)), pr(self, &b))
                } else {
                    format!("mp(tr.ssub32_ok, {{{w}}}, {{{}}}, {{{}}}, {hv}, simp(L), simp(L), {{HC}})", pr(self, &a), pr(self, &b))
                };
                let ub = format!("mp(tr.ssub32_ub, {{{w}}}, {{{}}}, {{{}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), {{HN}})", pr(self, &a), pr(self, &b));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        if let Some(x) = self.app(op, "gimple.padd", 2) {
            let (p, d) = (x[0].clone(), x[1].clone());
            if let (Some(_), Some(dv)) = (self.eval_lit(&p), self.eval_lit(&d)) {
                if dv < 1 << 63 {
                    let r = self.mk("int_add", vec![p.clone(), d.clone()]);
                    let ok = format!("mp(tr.padd_ok, {{{w}}}, {{{}}}, {{{}}}, {hv}, simp(L), simp(L), simp(L), simp(L))", pr(self, &p), pr(self, &d));
                    return Ok((None, r, ok, String::new()));
                }
            }
            // a pointer's: p + d in 64 bits, when in the address range
            // (tr.padd_def, as it expands)
            let ty = self.mk("fn_update", vec![self.mk("fn_update", vec![self.mk("empty", vec![]), Term::bytes(b"prec"), lit(64)]), Term::bytes(b"signed"), self.mk("true", vec![])]);
            let sum = self.mk("int_add", vec![p.clone(), self.mk("gimple.sval", vec![ty, d.clone()])]);
            let cond = self.mk("and", vec![self.mk("int_le", vec![lit(0), sum.clone()]), self.mk("int_lt", vec![sum, lit(P64)])]);
            let r = self.mk("bits_add", vec![lit(64), p.clone(), d.clone()]);
            let ok = format!("mp(tr.padd_okb, {{{w}}}, {{{}}}, {{{}}}, {hv}, simp(L), simp(L), {{HC}})", pr(self, &p), pr(self, &d));
            let ub = format!("mp(tr.padd_ub, {{{w}}}, {{{}}}, {{{}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})", pr(self, &p), pr(self, &d));
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
                let ok = format!("mp(tr.elem1_{}_ok, {{{w}}}, {{{}}}, {{{}}}, {hv}, simp(L), simp(L), {{HC}})", kind, pr(self, &p), pr(self, &i));
                let ub = format!("mp(tr.elem1_{}_ub, {{{w}}}, {{{}}}, {{{}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})", kind, pr(self, &p), pr(self, &i));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        if let Some(x) = self.app(op, "gimple.ld8", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.ld8_cond(&a);
                let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
                let r = self.mk("bits_of_int", vec![lit(8), self.mk("gimple.bytes_at", vec![vm, a.clone(), lit(1)])]);
                let ok = format!("mp(g.ld8_ok, {{{w}}}, {{{}}}, {hv}, simp(L), taut({{HC}}), taut({{HC}}))", pr(self, &a));
                let ub = format!("mp(g.ld8_ub, {{{w}}}, {{{}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), {{HN}}, simp(L))", pr(self, &a));
                return Ok((Some(cond), r, ok, ub));
            }
        }
        // a byte load at a static's field: p + off, both literals (the
        // address computed)
        if let Some(x) = self.app(op, "gimple.ld8", 2) {
            if let (Some(pv), Some(ov)) = (self.eval_lit(&x[0]), self.eval_lit(&x[1])) {
                let (p, off, a) = (pr(self, &x[0]), pr(self, &x[1]), (pv + ov) % P64);
                let cond = self.parse(&format!("g.mem_defined({w}, {p}, {off}, 1, false)"))?;
                let r = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({w}, \"vm\"), {a}, 1))"))?;
                let ok = format!("mp(tr.ld8_at_ok, {{{w}}}, {{{p}}}, {{{off}}}, {{{a}}}, {hv}, simp(L), simp(L), simp(L), {{HC}})");
                let ub = format!("mp(g.ld8_at_ub, {{{w}}}, {{{p}}}, {{{off}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})");
                return Ok((Some(cond), r, ok, ub));
            }
        }
        // a 2-byte load
        if let Some(x) = self.app(op, "gimple.ld16", 2) {
            if nat(&x[1]) == Some(0) {
                let a = x[0].clone();
                let cond = self.parse(&format!("g.mem_defined({w}, {}, 0, 2, false)", pr(self, &a)))?;
                let r = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({w}, \"vm\"), {}, 2))", pr(self, &a)))?;
                let ok = format!("mp(g.ld16_ok, {{{w}}}, {{{}}}, {hv}, simp(L), {{HC}})", pr(self, &a));
                let ub = format!("mp(g.ld16_ub, {{{w}}}, {{{}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), {{HN}})", pr(self, &a));
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
                    let ok = format!("mp(tr.elem2_sx_ok, {{{w}}}, {{{p}}}, {{{i}}}, {hv}, simp(L), simp(L), {{HC}})");
                    let ub = format!("mp(tr.elem2_sx_ub, {{{w}}}, {{{p}}}, {{{i}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})");
                    return Ok((Some(cond), r, ok, ub));
                }
            }
        }
        // a 64-bit field load at p + off (off a literal)
        if let Some(x) = self.app(op, "gimple.ld64", 2) {
            if nat(&x[1]).is_some() {
                let (p, off) = (pr(self, &x[0]), pr(self, &x[1]));
                let cond = self.parse(&format!("g.mem_defined({w}, {p}, {off}, 8, false)"))?;
                let r = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app({w}, \"vm\"), bits_add(64, {p}, {off}), 8))"))?;
                let ok = format!("mp(tr.ld64_ok, {{{w}}}, {{{p}}}, {{{off}}}, {hv}, simp(L), simp(L), {{HC}})");
                let ub = format!("mp(tr.ld64_ub, {{{w}}}, {{{p}}}, {{{off}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})");
                return Ok((Some(cond), r, ok, ub));
            }
        }
        // a bitfield load: n bytes at p + off, bits pos.., k of them
        if let Some(x) = self.app(op, "gimple.ldbf", 5) {
            let t: Vec<String> = x.iter().map(|y| pr(self, y)).collect();
            let (p, off, n, pos, k) = (&t[0], &t[1], &t[2], &t[3], &t[4]);
            let cond = self.parse(&format!("g.mem_defined({w}, {p}, {off}, {n}, false)"))?;
            let r = self.parse(&format!("int_mod(int_div(gimple.bytes_at(app({w}, \"vm\"), bits_add(64, {p}, {off}), {n}), int_pow(2, {pos})), int_pow(2, {k}))"))?;
            let ok = format!("mp(tr.ldbf_ok, {{{w}}}, {{{p}}}, {{{off}}}, {{{n}}}, {{{pos}}}, {{{k}}}, {hv}, simp(L), simp(L), {{HC}})");
            let ub = format!("mp(g.ldbf_ub, {{{w}}}, {{{p}}}, {{{off}}}, {{{n}}}, {{{pos}}}, {{{k}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})");
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
                    let ok = format!("mp(tr.smul32_ok, {{{w}}}, {{{a}}}, {{{k}}}, {hv}, simp(L), simp(L), {}.imul_{k}, {{HC}})", self.prefix);
                    let ub = format!("mp(tr.smul32_ub, {{{w}}}, {{{a}}}, {{{k}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), {{HN}})");
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
                    let ok = format!("defs(mp({okl}, {{{w}}}, {hv}, simp(L), {ok2}), {fname})");
                    let ub = match cond {
                        Some(_) => {
                            let (ubl, _) = self.inst("tr.call1_ub", &[("op", op2.clone()), ("s2", self.vw.clone()), ("e", self.mk("empty", vec![])), ("f", fl.clone())])?;
                            format!("defs(mp({ubl}, {{{w}}}, {hv}, hvu, simp(), {ub2}), {fname})")
                        }
                        None => String::new(),
                    };
                    return Ok((cond, r, ok, ub));
                }
            }
        }
        Err(format!("no rule for the operation {}", self.print(op)))
    }

    /// A store at the head: `gimple.st8(p, off, v)` or `gimple.st32(..)`,
    /// or a helper's call whose body is one (`mkprog(x0 x1. bind_rel(st8(..),
    /// x0, x2 x3. x1 = ok(x2, empty), ..))`)
    fn store_op(&mut self, op: &Term) -> Result<Option<StoreOp>, String> {
        let is_store = |g: &Gen, t: &Term| {
            g.app(t, "gimple.st8", 3).is_some() || g.app(t, "gimple.st32", 3).is_some() || g.app(t, "gimple.st64", 3).is_some() || g.app(t, "gimple.st_bytes", 3).is_some()
        };
        let (inner, helper) = if is_store(self, op) {
            (op.clone(), None)
        } else {
            let Node::App(f, args) = op.node() else { return Ok(None) };
            let SymKind::Defined { params, body } = &self.env.syms[*f as usize].kind else { return Ok(None) };
            let fname = self.env.syms[*f as usize].name.clone();
            let mut b = body.clone();
            for (p, x) in params.clone().iter().zip(args.iter()) {
                b = b.subst_var(*p, x, &self.env.binders_fn());
            }
            let inner = (|| {
                let m = self.app(&b, "mkprog", 1)?;
                let br = self.app(&m[0], "bind_rel", 5)?;
                matches!(br[1].node(), Node::BVar(1)).then_some(())?;
                is_store(self, &br[0]).then_some(())?;
                let e = self.app(&br[2], "eq", 2)?;
                let o = self.app(&e[1], "ok", 2)?;
                (matches!(e[0].node(), Node::BVar(2)) && matches!(o[0].node(), Node::BVar(1)) && self.app(&o[1], "empty", 0).is_some()).then_some(())?;
                Some(br[0].clone())
            })();
            let Some(inner) = inner else { return Ok(None) };
            (inner, Some(fname))
        };
        // (constant bytes: all zero, else not covered)
        let mut data = None;
        let (n, x) = match (self.app(&inner, "gimple.st8", 3), self.app(&inner, "gimple.st32", 3), self.app(&inner, "gimple.st_bytes", 3)) {
            (Some(x), _, _) => (1, x.to_vec()),
            (_, Some(x), _) => (4, x.to_vec()),
            (_, _, Some(x)) => {
                let items = self.list_items(&x[2]).ok_or("st_bytes of a list that is not a literal")?;
                if items.is_empty() || items.iter().any(|t| nat(t) != Some(0)) {
                    return Err(format!("st_bytes of {}: only zeros covered", self.print(&x[2])));
                }
                data = Some(x[2].clone());
                (items.len() as u128, vec![x[0].clone(), x[1].clone(), lit(0)])
            }
            _ => (8, self.app(&inner, "gimple.st64", 3).unwrap().to_vec()),
        };
        let (p, off, v) = (x[0].clone(), x[1].clone(), x[2].clone());
        let addr = match (self.eval_lit(&p), self.eval_lit(&off)) {
            (Some(pv), Some(ov)) => lit((pv + ov) % P64),
            // (a 64-bit field: at p + off, as the machine's [b + d])
            _ if (n == 8 || data.is_some()) && nat(&off).is_some() => self.mk("bits_add", vec![lit(64), p.clone(), off.clone()]),
            _ if nat(&off) == Some(0) => p.clone(),
            _ => return Err(format!("a store at {} + {}: not covered yet", self.print(&p), self.print(&off))),
        };
        let w = self.print(&self.w.clone());
        let hv = self.hvu.clone();
        let (ps, os, vs) = (self.print(&p), self.print(&off), self.print(&v));
        let cond = self.parse(&format!("g.mem_defined({w}, {ps}, {os}, {n}, true)"))?;
        let inner_ub = match &data {
            Some(d) => format!("mp(g.stz_ub, {{{w}}}, {{{ps}}}, {{{os}}}, {{{}}}, {{W}}, {{empty}}, {{{n}}}, {hv}, hvu, simp(), simp(L), simp(L), arith(), {{HN}})", self.print(d)),
            None => format!("mp(g.st{}_at_ub, {{{w}}}, {{{ps}}}, {{{os}}}, {{{vs}}}, {{W}}, {{empty}}, {hv}, hvu, simp(), simp(L), simp(L), {{HN}})", 8 * n),
        };
        let ub = match &helper {
            None => inner_ub,
            Some(fname) => {
                let (ubl, _) = self.inst("tr.call1_ub", &[("op", inner.clone()), ("s2", self.vw.clone()), ("e", self.mk("empty", vec![])), ("f", self.mk("empty", vec![]))])?;
                format!("defs(mp({ubl}, {{{w}}}, {hv}, hvu, simp(), {inner_ub}), {fname})")
            }
        };
        Ok(Some(StoreOp { n, cond, p, off, v, addr, inner, helper, ub, data }))
    }

    /// The spec's store at the head of `st`'s rest, the machine storing n
    /// bytes at `addr`: its definedness fact, the stored value, the world
    /// after (its lines: its definition, its facts), the state after, the
    /// reduction `tr.red(WRAP(q), w, WRAP(q2), w2)`'s proof, the address
    fn spec_store(&mut self, st: &St, addr: &Term, n: u128) -> Result<(String, Term, Vec<String>, St, String, Term), String> {
        let (hc, v, pre, st2, red, sa, _) = self.spec_store_x(st, Some(addr), Some(n))?;
        Ok((hc, v, pre, st2, red, sa))
    }

    /// the same, the machine's address and size not known yet (any): also
    /// the store
    fn spec_store_x(&mut self, st: &St, addr: Option<&Term>, n: Option<u128>) -> Result<(String, Term, Vec<String>, St, String, Term, StoreOp), String> {
        let Spec::Proc(qi) = st.spec else { return Err(format!("{:x}: a store after the procedure's result", st.a)) };
        let q = self.qs[qi].1.clone();
        let badm = format!("{:x}: a store the spec does not make here (its rest: {})", st.a, self.print(&q));
        let bad = || badm.clone();
        let body = self.app(&q, "mkprog", 1).ok_or_else(bad)?[0].clone();
        let ex = self.app(&body, "ex", 1).and_then(|e| self.app(&e[0], "and", 2).map(|x| x.to_vec())).ok_or_else(bad)?;
        let (a, k) = (ex[0].clone(), ex[1].clone());
        let x = self.app(&a, "bind_rel", 5).ok_or_else(bad)?.to_vec();
        let so = self.store_op(&x[0])?.ok_or_else(bad)?;
        let n = n.unwrap_or(so.n);
        if so.n != n {
            return Err(format!("{:x}: the machine stores {} bytes, the spec {}", st.a, n, so.n));
        }
        let hc = st.hyps.iter().find(|h| h.0 == so.cond).map(|h| h.1.clone()).ok_or_else(bad)?;
        if let Some(addr) = addr {
            if self.canon(&so.addr) != self.canon(addr) && !(self.eval_lit(&so.addr).is_some() && self.eval_lit(&so.addr) == self.eval_lit(addr)) {
                return Err(format!("{:x}: the machine stores at {}, the spec at {}", st.a, self.print(addr), self.print(&so.addr)));
            }
        }
        let ctx = ["x0", "x1", "x8"];
        let kl = self.lam(&k, &ctx, &["x8", "x1"]).ok_or("a block's rest reads the world")?;
        let c5 = ["x0", "x1", "x8", "x9", "x10"];
        let al = self.lam(&x[2], &c5, &["x9", "x10", "x8"]).ok_or("a store's continuation reads the world before it")?;
        let xl = self.lam(&x[3], &c5, &["x9", "x10", "x8"]).ok_or("a store's handler reads the world before it")?;
        let dl = self.lam(&x[4], &["x0", "x1", "x8", "x9"], &["x9", "x8"]).ok_or("a store's handler reads the world before it")?;
        // the world after it
        self.n += 1;
        let k2 = self.n;
        let (wn2, hw2, hv2) = (format!("W{}", k2), format!("hW{}", k2), format!("hvu{}", k2));
        let w2 = self.var(&wn2);
        let (wn, ap, vp) = (st.wn.clone(), self.print(&so.addr), self.print(&so.v));
        let w2t = format!("fn_update({wn}, \"vm\", fn_update(app({wn}, \"vm\"), \"bytes\", x86_64_linux.store_le(app(app({wn}, \"vm\"), \"bytes\"), {ap}, {n}, {vp})))");
        // (a value as any: the values read from it come after it)
        let w2term = self.parse(&w2t)?;
        let Node::Var(w2v, _) = w2.node() else { unreachable!() };
        self.vals.push((*w2v, w2term));
        let pre = vec![
            format!("have {hw2} := apply(tr.world_store, {{{wn}}}, {{{ap}}}, {{{n}}}, {{{vp}}}, taut({}), taut({}), simp(L))", st.hw, st.hw),
            format!("have {hv2}: {wn2} in univ(1) by taut({hw2})"),
        ];
        // the store's run: ok, to the world after
        let (ps, os) = (self.print(&so.p), self.print(&so.off));
        let st8ok = match &so.data {
            Some(d) => format!(
                "mp(tr.stz_at_ok, {{{wn}}}, {{{ps}}}, {{{os}}}, {{{}}}, {{{ap}}}, {{{n}}}, taut({}), {}, simp(L), simp(L), {}, simp(L), arith(), {hc})",
                self.print(d), st.hw, st.hvu, self.zeros_proof(d)?
            ),
            None => format!("mp(tr.st{}_at_ok, {{{wn}}}, {{{ps}}}, {{{os}}}, {{{vp}}}, {{{ap}}}, taut({}), {}, simp(L), simp(L), simp(L), simp(L), {hc})", 8 * n, st.hw, st.hvu),
        };
        let okp = match &so.helper {
            None => st8ok,
            Some(fname) => {
                let (okl, _) = self.inst("tr.call1w_ok", &[("op", so.inner.clone()), ("r", self.mk("empty", vec![]))])?;
                format!("defs(mp({okl}, {{{wn}}}, {{{wn2}}}, {}, {hv2}, {st8ok}), {fname})", st.hvu)
            }
        };
        let empty = self.mk("empty", vec![]);
        let (j, text) = self.by(qi, "tr.qs_opw", &[("op", x[0].clone()), ("r", empty), ("a", al), ("xx", xl), ("dd", dl), ("k", kl)])?;
        let qred = format!("mp({text}, {{{wn}}}, {{{wn2}}}, {}, {okp})", st.hvu);
        let red = format!(
            "mp(tr.wredw[w := {wn}, w2 := {wn2}, q := {}, q2 := {}, kw := x0 x1 x2. KW(x0, x1, x2)], {}, {qred})",
            self.qs[qi].0, self.qs[j].0, st.hvu
        );
        let mut st2 = st.clone();
        st2.w = w2;
        st2.wn = wn2;
        st2.hvu = hv2;
        st2.hw = hw2;
        st2.spec = Spec::Proc(j);
        let _ = &so.cond;
        Ok((hc, so.v.clone(), pre, st2, red, so.addr.clone(), so))
    }

    /// `l in list_type(omega) && tr.zeros(l)` for a list literal of zeros
    /// (left-nested, as GIMPLE's): tr.zeros_one, then tr.zeros_snoc
    fn zeros_proof(&self, l: &Term) -> Result<String, String> {
        if self.app(l, "seq_one", 1).is_some() {
            return Ok("tr.zeros_one".into());
        }
        let x = self.app(l, "seq_concat", 2).filter(|x| self.app(&x[1], "seq_one", 1).is_some()).ok_or("a list of zeros not left-nested")?;
        Ok(format!("apply(tr.zeros_snoc, {})", self.zeros_proof(&x[0])?))
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
        let wn = st.wn.clone();
        let cond = self.parse(&format!("g.mem_defined({wn}, {}, {}, {}, false)", self.print(p), self.print(d), n))?;
        st.hyps.iter().find(|h| h.0 == cond).map(|h| h.1.clone()).ok_or_else(|| {
            let facts: Vec<String> = st.hyps.iter().map(|h| self.print(&h.0)).collect();
            format!("{:x}: a load of {} bytes at {} + {} the spec does not make (the facts: {})", st.a, n, self.print(p), self.print(d), facts.join(", "))
        })
    }

    /// the fact in scope that the spec's byte load (or store) at the static
    /// address a is defined (its address p + off, literals)
    fn static_hyp(&self, st: &St, a: u128, write: bool) -> Result<String, String> {
        fn usable<'t>(g: &Gen, t: &'t Term, out: &mut Vec<&'t Term>) {
            if let Some(x) = g.app(t, "gimple.usable", 5) {
                out.push(t);
                let _ = x;
                return;
            }
            if let Node::App(_, xs) = t.node() {
                for x in xs.iter() {
                    usable(g, x, out);
                }
            }
        }
        for (h, name) in &st.hyps {
            let mut us = Vec::new();
            usable(self, h, &mut us);
            for u in us {
                let x = self.app(u, "gimple.usable", 5).unwrap();
                let wr = self.app(&x[4], "true", 0).is_some();
                if x[0] == self.mk("app", vec![st.w.clone(), Term::bytes(b"vm")]) && nat(&x[3]) == Some(1) && wr == write {
                    let at = self.app(&x[2], "int_add", 2).and_then(|s| Some((self.eval_lit(&s[0])? + self.eval_lit(&s[1])?) % P64)).or_else(|| self.eval_lit(&x[2]));
                    if at == Some(a) {
                        return Ok(name.clone());
                    }
                }
            }
        }
        Err(format!("{:x}: an access at the static {:x} the spec does not make", st.a, a))
    }

    /// a byte load's definedness at a
    fn ld8_cond(&self, a: &Term) -> Term {
        let vm = self.mk("app", vec![self.w.clone(), Term::bytes(b"vm")]);
        let nz = self.mk("not", vec![self.mk("eq", vec![a.clone(), lit(0)])]);
        let ob = self.mk("app", vec![self.w.clone(), Term::bytes(b"objs")]);
        let us = self.mk("gimple.usable", vec![vm, ob, a.clone(), lit(1), self.mk("false", vec![])]);
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
                        format!("have {}: all o. runs({}, {w}, o) -> runs({}, {w}, o) proof", u, self.qs[j].0, self.qs[qi].0),
                        "  fix o".into(),
                        format!("  assume h: runs({}, {w}, o)", self.qs[j].0),
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
                // a store: its definedness split here, the store itself at
                // the machine's
                if let Some(so) = self.store_op(&x[0])? {
                    if hyps.iter().any(|h| h.0 == so.cond) {
                        return Ok(None);
                    }
                    let mut ra = vec![("op", x[0].clone()), ("s2", self.vw.clone()), ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone())];
                    ra.push(("e", self.mk("empty", vec![])));
                    let (u, rtext) = self.by(qi, "tr.qs_raise", &ra)?;
                    let ubr = format!("mp({}, {{{w}}}, {})", rtext, so.ub);
                    return Ok(Some(Red::Guard { cond: so.cond, ub: (u, ubr) }));
                }
                // a call: the machine's call makes it
                for (name, one) in [("gimple.call1", true), ("gimple.call", false)] {
                    if let Some(c) = self.app(&x[0], name, 2) {
                        let items = self.list_items(&c[1]).ok_or("a call's arguments: not a list literal")?;
                        return Ok(Some(Red::Call { g: c[0].clone(), args: items, list: c[1].clone(), one, a: al, xx: xl, dd: dl, k: kl }));
                    }
                }
                let (cond, r, okf, ubf) = self.op(&x[0])?;
                let r = self.value(&r);
                let args = |r2: (&'static str, Term)| vec![("op", x[0].clone()), r2, ("a", al.clone()), ("xx", xl.clone()), ("dd", dl.clone()), ("k", kl.clone())];
                let (j, text) = self.by(qi, "tr.qs_op", &args(("r", r.clone())))?;
                let okr = format!("mp({}, {{{w}}}, {})", text, okf);
                let Some(cond) = cond else { return Ok(Some(Red::Q(j, okr, vec![]))) };
                let mut ra = args(("s2", self.vw.clone()));
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
        // (nothing else: an equation of a term with itself, of the world --
        // true)
        if let Some((r, s)) = self.refl_redex(&body, 0) {
            let b = self.abstract_(&body, &r, 0);
            let st = self.lam(&s, &["x0", "x1"], &["x0"]).ok_or("refl")?;
            let (j, text) = self.by(qi, "tr.qe_refl", &[("b", b), ("st", st)])?;
            return Ok(Some(Red::Q(j, format!("mp({}, {{{w}}})", text), vec![])));
        }
        Ok(None)
    }

    // ------------------------------------------------------------------
    //  The proof

    fn wred(&self, st: &St, qi: usize, j: usize) -> String {
        format!(
            "tr.wred[s := s, v := V, base := {}, code := {}, fr := {}, a := {}, hs := {}, ds := {}, rs := {}, w := {}, q := {}, q2 := {}, kw := x0 x1 x2. KW(x0, x1, x2)]",
            self.base, self.code, st.fr, st.a, st.hst, st.ds, st.rs, st.wn, self.qs[qi].0, self.qs[j].0
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
                matches!(x[0].node(), Node::BVar(0)) && g.app(&x[1], "exc", 2).map_or(false, |e| e[0] == g.vw && g.app(&e[1], "empty", 0).is_some())
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
        let (wn, hv) = (self.wn.clone(), self.hvu.clone());
        lines.push(format!("have {} := mp(tr.q_exc_runs, {{{wn}}}, {{W}}, {{empty}}, {hv}, hvu, simp())", name));
        for r in steps.into_iter().rev() {
            let n2 = self.fresh("r");
            lines.push(format!("have {} := mp({}, {{exc(W, empty)}}, {})", n2, r, name));
            name = n2;
        }
        Ok(Pf { lines, expr: name })
    }

    /// The proof of the point claim at `st`.
    fn prove(&mut self, st: St) -> Result<Pf, String> {
        self.fr = st.fr;
        self.w = st.w.clone();
        self.wn = st.wn.clone();
        self.hvu = st.hvu.clone();
        self.lf = match st.lp {
            Some(l) => format!("L, {}", self.loops[l].ci),
            None => "L".into(),
        };
        if let Some(pf) = self.loop_point(&st)? {
            return Ok(pf);
        }
        // (in a zero-initialization: the machine's stores only, the spec's made)
        if st.z.is_some() {
            return self.insn(st);
        }
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
                        "mp(tr.wret[s := s, v := V, base := {}, code := {}, fr := {}, a := {}, hs := {}, ds := {}, rs := {}, w := {}, val := {}, kw := x0 x1 x2. KW(x0, x1, x2)], simp({}), {})",
                        self.base, self.code, st.fr, st.a, st.hst, st.ds, st.rs, st.wn, self.print(&val), st.hvu, pn
                    );
                    return Ok(Pf { lines, expr });
                }
                Some(Red::Split { cond, ok, ub }) => {
                    let (hn, hc, un, dn, pn) = (self.fresh("hn"), self.fresh("hc"), self.fresh("u"), self.fresh("d"), self.fresh("p"));
                    let ct = self.print(&cond);
                    // undefined: the spec raises
                    let chain = self.raise_chain(ub.0)?;
                    let wn = st.wn.clone();
                    let mut lines = vec![format!("have {}: !({}) -> runs({}, {wn}, exc(W, empty)) proof", un, ct, self.qs[qi].0), format!("  assume {}: !({})", hn, ct)];
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
                        "mp(tr.wsplit[s := s, v := V, base := {}, code := {}, fr := {}, a := {}, hs := {}, ds := {}, rs := {}, w := {}, q := {}, kw := x0 x1 x2. KW(x0, x1, x2), c := {}], {{W}}, taut(hW), hvu, {}, {})",
                        self.base, self.code, st.fr, st.a, st.hst, st.ds, st.rs, st.wn, self.qs[qi].0, ct, un, dn
                    );
                    return Ok(Pf { lines, expr });
                }
                // (a call: at the machine's call; the instructions before it first)
                Some(Red::Call { g, args, list, one, a, xx, dd, k }) => {
                    if self.insns.get(&st.a).map(|i| i.row) == Some(120) {
                        return self.call_at(&st, qi, g, &args, list, one, a, xx, dd, k);
                    }
                }
                Some(Red::Guard { cond, ub }) => {
                    let (hn, hc, un, dn) = (self.fresh("hn"), self.fresh("hc"), self.fresh("u"), self.fresh("d"));
                    let ct = self.print(&cond);
                    // undefined: the spec raises
                    let chain = self.raise_chain(ub.0)?;
                    let wn = st.wn.clone();
                    let mut lines = vec![format!("have {}: !({}) -> runs({}, {wn}, exc(W, empty)) proof", un, ct, self.qs[qi].0), format!("  assume {}: !({})", hn, ct)];
                    let mut body = chain.lines;
                    body.push(format!("show := mp({}, {{exc(W, empty)}}, {})", ub.1.replace("{HN}", &hn), chain.expr));
                    lines.extend(indent(body));
                    lines.push("qed".into());
                    // defined: the same rest, with the condition
                    let mut st2 = st.clone();
                    st2.hyps.push((cond.clone(), hc.clone()));
                    let rest = self.prove(st2)?;
                    lines.push(format!("have {}: {} -> {} proof", dn, ct, self.pt(&st, st.a)));
                    let mut body = vec![format!("assume {}: {}", hc, ct)];
                    body.extend(rest.lines);
                    body.push(format!("show := {}", rest.expr));
                    lines.extend(indent(body));
                    lines.push("qed".into());
                    let expr = format!(
                        "mp(tr.wsplit[s := s, v := V, base := {}, code := {}, fr := {}, a := {}, hs := {}, ds := {}, rs := {}, w := {}, q := {}, kw := x0 x1 x2. KW(x0, x1, x2), c := {}], {{W}}, taut(hW), hvu, {}, {})",
                        self.base, self.code, st.fr, st.a, st.hst, st.ds, st.rs, st.wn, self.qs[qi].0, ct, un, dn
                    );
                    return Ok(Pf { lines, expr });
                }
                None => {}
            }
        }
        self.insn(st)
    }

    /// the items of a list literal (`seq_one`s concatenated)
    fn list_items(&self, t: &Term) -> Option<Vec<Term>> {
        if self.app(t, "empty", 0).is_some() {
            return Some(Vec::new());
        }
        if let Some(x) = self.app(t, "seq_one", 1) {
            return Some(vec![x[0].clone()]);
        }
        let x = self.app(t, "seq_concat", 2)?;
        let mut a = self.list_items(&x[0])?;
        a.extend(self.list_items(&x[1])?);
        Some(a)
    }

    /// `tr.hin(hs, fr)` for the homes' map text hs: one `tr.hin_upd` per
    /// entry, as the map is nested
    fn hin_proof(&self, hs: &str, fr: u128) -> Result<String, String> {
        if hs == "empty" {
            return Ok(format!("all_elim(tr.hin_empty, {{{fr}}})"));
        }
        let [h, c, x] = split_update(hs).ok_or_else(|| format!("homes' map `{}`: not an update", hs))?;
        let ph = self.hin_proof(&h, fr)?;
        Ok(format!("mp(all_elim(tr.hin_upd, {{{h}}}, {{{fr}}}, {{{c}}}, {{{x}}}), {ph}, simp())"))
    }

    /// A call (tr.call, tr.call1 for call1): the machine's `call rel32` at
    /// st's address from a frame of fr bytes, the spec's call of g with the
    /// arguments in their registers; the claim after it (at the return
    /// address, rax:rdx the result -- rax for call1 --, the homes kept, the
    /// frame from the push up) for every world and result, its definitions
    /// local to it
    #[allow(clippy::too_many_arguments)]
    fn call_at(&mut self, st: &St, qi: usize, g: Term, args: &[Term], list: Term, one: bool, al: Term, xl: Term, dl: Term, kl: Term) -> Result<Pf, String> {
        let a = st.a;
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        if insn.row != 120 {
            return Err(format!("{:x}: the spec calls, the machine does not", a));
        }
        if st.fr % 8 != 0 || st.fr < 8 || st.fr + 8 > 65536 {
            return Err(format!("{:x}: a call from a frame of {} bytes (a multiple of 8, at most 64 KiB expected)", a, st.fr));
        }
        let aligned = st.fr % 16 == 8;
        let nargs = args.len();
        if nargs > 6 {
            return Err(format!("{:x}: a call with {} arguments (at most 6 so far)", a, nargs));
        }
        let off = nat(&insn.fields).ok_or_else(|| format!("{:x}: the call's displacement", a))?;
        let a2 = (a + insn.len) % P64;
        let f = (a2 + if off >= 1 << 31 { off + (P64 - (1 << 32)) } else { off }) % P64;
        // the arguments: arg(n, X), X in its register
        const ARGREGS: [u128; 6] = [7, 6, 2, 1, 8, 9];
        let mut aps = Vec::new();
        for (i, ar) in args.iter().enumerate() {
            let ax = self.app(ar, "gimple.arg", 2).ok_or_else(|| format!("{:x}: argument {} not a register argument", a, i))?;
            let nb = nat(&ax[0]).ok_or_else(|| format!("{:x}: argument {}'s width", a, i))?;
            let x = ax[1].clone();
            let r = ARGREGS[i];
            let (k, v) = self.reg(st, r).ok_or_else(|| format!("{:x}: register {} holds no value at the call", a, r))?;
            if ![1, 2, 4, 8].contains(&k) || self.canon(&v) != self.canon(&x) {
                return Err(format!("{:x}: register {} holds {}, the spec passes {}", a, r, self.print(&v), self.print(&x)));
            }
            aps.push(format!("apply(tr.argv_reg, {{{}}}, {{{r}}}, {{{k}}}, {{{nb}}}, {{{}}}, simp(L), simp(L), simp())", st.rs, self.print(&x)));
        }
        let hreg = if nargs == 0 { format!("all_elim(tr.args0, {{{}}})", st.rs) } else { format!("apply(tr.args{nargs}, {})", aps.join(", ")) };
        let hin = self.hin_proof(&st.hst, st.fr)?;
        let gi = self.callees.iter().position(|c| c.0 == g && c.1 == f).unwrap_or_else(|| {
            self.callees.push((g.clone(), f, nargs, false));
            self.callees.len() - 1
        });
        self.callees[gi].3 |= !aligned;
        // (the callee's contract at this call: the ABI's if aligned, else the one for any entry)
        let hcon = if aligned { format!("defs(taut(hcall{gi}, (int_mod({}, 16) = 8 by simp())), tr.callee_contract)", st.fr) } else { format!("defs(taut(hcall{gi}), tr.callee_contract)") };
        let (gn, wn) = (self.print(&g), st.wn.clone());
        let hv = st.hvu.clone();
        // the continuation's raise and divergence: the function's
        let n = self.fresh("c");
        let (xv, ev, tv) = (self.var(&format!("XC{n}")), self.var(&format!("EC{n}")), self.var(&format!("TC{n}")));
        let x8 = Term::bvar(0);
        let mkq = |gg: &Gen, h: Term| -> Term {
            let kk = kl.instantiate_params(&[Term::bvar(0), Term::bvar(1)], &gg.env.binders_fn());
            gg.mk("mkprog", vec![gg.mk("ex", vec![gg.mk("and", vec![h, kk])])])
        };
        let qx = mkq(self, xl.instantiate_params(&[xv.clone(), ev.clone(), x8.clone()], &self.env.binders_fn()));
        let qd = mkq(self, dl.instantiate_params(&[tv.clone(), x8.clone()], &self.env.binders_fn()));
        let (xs, es, ts) = (self.print(&xv), self.print(&ev), self.print(&tv));
        let mut lines = vec![
            format!("have hk{n}: all {xs} {es}. {xs} in univ(1) -> {es} in univ(1) -> runs({}, {wn}, exc({xs}, {es})) proof", self.print(&qx)),
            format!("  fix {xs}"),
            format!("  fix {es}"),
            format!("  assume hx: {xs} in univ(1)"),
            format!("  assume he: {es} in univ(1)"),
            format!("  show by defs(simp(hx, he, {hv}), runs, mkprog)"),
            "qed".into(),
            format!("have hd{n}: all {ts}. {ts} in univ(1) -> runs({}, {wn}, diverge({ts})) proof", self.print(&qd)),
            format!("  fix {ts}"),
            format!("  assume ht: {ts} in univ(1)"),
            format!("  show by defs(simp(ht, {hv}), runs, mkprog)"),
            "qed".into(),
        ];
        // the claim after the call, for every world W4 and result R0 (:R1)
        let (wc, rc, rd) = (format!("WC{n}"), format!("RC{n}"), format!("RD{n}"));
        let (w4, r0, r1) = (self.var(&wc), self.var(&rc), self.var(&rd));
        let (nv0, nq0, nl0) = (self.vals.len(), self.qs.len(), self.lets.len());
        let res = if one { r0.clone() } else { self.mk("pair", vec![r0.clone(), r1.clone()]) };
        let ka = al.instantiate_params(&[Term::bvar(2), res, Term::bvar(0)], &self.env.binders_fn());
        let q2 = self.canon(&mkq(self, ka));
        let j = self.new_q(q2);
        let fd2 = st.fr + 8;
        let mut st0 = st.clone();
        st0.a = a2;
        st0.regs = Vec::new();
        st0.rs = "empty".into();
        st0.w = w4.clone();
        st0.wn = wc.clone();
        st0.hvu = format!("hvu{wc}");
        st0.hw = format!("hW{wc}");
        st0.ds = fd2.to_string();
        st0.spec = Spec::Proc(j);
        let mut st2 = self.set_reg(&st0, a2, 0, 8, r0.clone());
        if !one {
            st2 = self.set_reg(&st2, a2, 2, 8, r1.clone());
        }
        let rsp = if one { format!("fn_update(empty, 0, pair(8, {rc}))") } else { format!("fn_update(fn_update(empty, 0, pair(8, {rc})), 2, pair(8, {rd}))") };
        let pt2 = format!("tr.pt(s, V, {}, {}, {}, {}, {}, {fd2}, {rsp}, WRAP({}), {wc})", self.base, self.code, st.fr, a2, st.hst, self.print(&self.qs[j].1));
        let rest = self.prove(st2)?;
        // (the definitions after the call: in its proof)
        let mut local = Vec::new();
        let lvals: Vec<(VarId, Term)> = self.vals.drain(nv0..).collect();
        for (v, t) in lvals {
            local.push(format!("let {} := {}", self.env.vars[v as usize].name, self.print(&t)));
        }
        // (but those a nested call's proof already holds)
        for i in nq0..self.qs.len() {
            if self.scoped_q.insert(i) {
                local.push(format!("let {} := {}", self.qs[i].0, self.print(&self.qs[i].1)));
            }
        }
        for i in nl0..self.lets.len() {
            if self.scoped_l.insert(i) {
                local.push(format!("let {} := {}", self.lets[i].0, self.lets[i].1));
            }
        }
        let (rv, rh) = if one { (rc.clone(), format!("{rc} in bits(64) ->")) } else { (format!("{rc} {rd}"), format!("{rc} in bits(64) -> {rd} in bits(64) ->")) };
        lines.push(format!("have pc{n}: all {wc} {rv}. {wc} in abi.World && {wc} in univ(1) -> {rh} {pt2} proof"));
        let mut body = vec![
            format!("fix {wc}"),
            format!("fix {rc}"),
        ];
        if !one {
            body.push(format!("fix {rd}"));
        }
        body.push(format!("assume hW{wc}: {wc} in abi.World && {wc} in univ(1)"));
        body.push(format!("assume h{rc}: {rc} in bits(64)"));
        if !one {
            body.push(format!("assume h{rd}: {rd} in bits(64)"));
        }
        body.push(format!("have hvu{wc}: {wc} in univ(1) by taut(hW{wc})"));
        body.extend(local);
        body.extend(rest.lines);
        body.push(format!("show := {}", rest.expr));
        lines.extend(indent(body));
        lines.push("qed".into());
        let rule = format!(
            "{}[s := s, v := V, base := {}, code := {}, fr := {}, a := {}, a2 := {}, len := {}, off := {}, f := {}, g := {gn}, args := {}, n := {nargs}, cb := {}, cc := {}, st := statics, hs := {}, ds := {}, fd2 := {fd2}, rs := {}, w := {wn}, ka := {}, xx := {}, dd := {}, k := {}, kw := x0 x1 x2. KW(x0, x1, x2)]",
            if one { "tr.call1" } else { "tr.call" },
            self.base,
            self.code,
            st.fr,
            a,
            a2,
            insn.len,
            off,
            f,
            self.print(&list),
            self.lbase,
            self.lcode,
            st.hst,
            st.ds,
            st.rs,
            self.lambda(3, &al),
            self.lambda(3, &xl),
            self.lambda(2, &dl),
            self.lambda(2, &kl),
        );
        let _ = qi;
        let expr = format!(
            "mp({rule}, {}, simp(L), simp(L), simp(L), simp(L), {hcon}, hl, simp(), defs(simp(), tr.cfr), simp(), simp(), simp(), htyp{gi}, hio{gi}, {hreg}, {hin}, simp(), simp(), hk{n}, hd{n}, pc{n})",
            insn.name,
        );
        Ok(Pf { lines, expr })
    }

    /// a loop's head (the spec's loop there): its claim, by induction
    fn loop_point(&mut self, st: &St) -> Result<Option<Pf>, String> {
        let Spec::Proc(qi) = st.spec else { return Ok(None) };
        if self.loop_head(qi).is_none() || !self.is_loop_test(st.a) {
            return Ok(None);
        }
        if let Some(l) = st.lp {
            if self.loops[l].head == st.a {
                return self.loop_back(st, qi, l).map(Some);
            }
        }
        self.loop_start(st, qi).map(Some)
    }

    /// the machine's loop test at a: an instruction followed by a backward
    /// conditional jump
    fn is_loop_test(&self, a: u128) -> bool {
        let Some(i) = self.insns.get(&a) else { return false };
        matches!(self.jcc((a + i.len) % P64), Ok((_, _, _, tt, _)) if tt <= a)
    }

    /// A counting loop met at its head h (the machine's test `cmp dword [rsp
    /// + d], K; jle`, the counter in the home d): the claim at h for every
    /// world lw and counter li with the invariant, by induction on the
    /// variant (tr.wf2); here, at the counter's start value.
    fn loop_start(&mut self, st: &St, qi: usize) -> Result<Pf, String> {
        let h = st.a;
        let bad = |m: &str| format!("{:x}: a loop {}: not covered yet", h, m);
        // the machine's test: the counter's home, the bound
        let (d, kv) = {
            let i = &self.insns[&h];
            let x = (i.row == 60).then(|| self.pairs(&i.fields, 5)).flatten().ok_or_else(|| bad("whose test is not cmp dword [rsp + d], imm8"))?;
            let d = self.rsp_mem(&x[2]).and_then(|d| nat(&d)).ok_or_else(|| bad("whose test is not on a home"))?;
            let k = nat(&x[4]).filter(|k| *k < 128 && nat(&x[1]) == Some(7)).ok_or_else(|| bad("whose test is not cmp with a small immediate"))?;
            (self.hkey(d), k)
        };
        // the rest: ex x8. while_rel(pair(x0, I0), true, B, TR, x8) && K
        let q = self.qs[qi].1.clone();
        let body = self.app(&q, "mkprog", 1).unwrap()[0].clone();
        let y = self.app(&self.app(&body, "ex", 1).unwrap()[0], "and", 2).unwrap().to_vec();
        let ctx = ["x0", "x1", "x8"];
        let al = self.lam(&y[0], &ctx, &["x0", "x8"]).ok_or_else(|| bad("whose head reads the outcome"))?;
        let kl = self.lam(&y[1], &ctx, &["x8", "x1"]).ok_or_else(|| bad("whose rest reads the world"))?;
        let wr = self.app(&al, "while_rel", 5).ok_or_else(|| bad("not a while"))?.to_vec();
        let l0 = self.app(&wr[0], "pair", 2).ok_or_else(|| bad("whose state is not the world and one local"))?.to_vec();
        let i0 = l0[1].clone();
        let outer = {
            let bf = self.env.binders_fn();
            i0.loose_depth(&bf) > 0 || wr[2].loose_depth(&bf) > 2 || wr[3].loose_depth(&bf) > 1
        };
        if outer {
            return Err(bad("whose body reads the outer state"));
        }
        match st.hsm.get(&d) {
            Some((4, x)) if self.canon(x) == self.canon(&i0) => {}
            _ => return Err(bad("whose counter is not its home's value")),
        }
        if st.hsm.len() != 1 {
            return Err(bad("in a frame of other homes"));
        }
        let wn = st.wn.clone();
        // (at the counter's start: the guarded rest, the claim's at i0)
        let (j0, nodiv0) = self.by(qi, "tr.qs_nodiv", &[("a", al.clone()), ("k", kl.clone())])?;
        // the step's names; its rests and values (local to its proof)
        self.n += 1;
        let ln = self.n;
        let (lwn, lin) = (format!("lw{ln}"), format!("li{ln}"));
        let lw = self.var(&lwn);
        let li = self.var(&lin);
        let (nq0, nv0, nl0) = (self.qs.len(), self.vals.len(), self.lets.len());
        let l0li = wr[0].with_args(vec![l0[0].clone(), li.clone()]);
        let mut wa: Vec<Term> = wr.clone();
        wa[0] = l0li;
        let al_li = al.with_args(wa);
        let (_, stmt) = self.inst("tr.qs_nodiv", &[("a", al_li), ("k", kl.clone())])?;
        let (_, qh) = self.qparts(&stmt).ok_or("qs_nodiv")?;
        let qhc = self.canon(&qh);
        let jh = self.new_q(qhc);
        let l0f = self.mk("pair", vec![Term::bvar(0), li.clone()]);
        let (ju, unroll) = self.by(jh, "tr.qs_loop", &[("l0", l0f), ("b", wr[2].clone()), ("tr", wr[3].clone()), ("k", kl.clone())])?;
        let (cl, pi, mv) = (format!("CL{ln}"), format!("PI{ln}"), format!("MV{ln}"));
        let (hp, ih, cc, ci) = (format!("hp{ln}"), format!("ih{ln}"), format!("cc{ln}"), format!("ci{ln}"));
        let idx = self.loops.len();
        self.loops.push(Loop { head: h, ih: ih.clone(), k: kv, d, qh: self.qs[jh].1.clone(), li: li.clone(), ci: ci.clone() });
        let hst = format!("fn_update(empty, {}, pair(4, {}))", d, lin);
        let st_head = St {
            a: h,
            fr: st.fr,
            regs: Vec::new(),
            rs: "empty".into(),
            ds: self.fd.to_string(),
            w: lw.clone(),
            wn: lwn.clone(),
            hvu: format!("hvu{lwn}"),
            hw: format!("hW{lwn}"),
            hsm: [(d, (4, li.clone()))].into_iter().collect(),
            hst: hst.clone(),
            lp: Some(idx),
            spec: Spec::Proc(jh),
            hyps: st.hyps.clone(),
            z: None,
        };
        let mut st_body = st_head.clone();
        st_body.spec = Spec::Proc(ju);
        let body_pf = self.prove(st_body)?;
        // the step's local definitions: its values, rests, register maps
        let mut local = Vec::new();
        let lvals: Vec<(VarId, Term)> = self.vals.drain(nv0..).collect();
        for (v, t) in lvals {
            local.push(format!("let {} := {}", self.env.vars[v as usize].name, self.print(&t)));
        }
        for i in nq0..self.qs.len() {
            local.push(format!("let {} := {}", self.qs[i].0, self.print(&self.qs[i].1)));
            self.scoped_q.insert(i);
        }
        for i in nl0..self.lets.len() {
            local.push(format!("let {} := {}", self.lets[i].0, self.lets[i].1));
            self.scoped_l.insert(i);
        }
        // the claim, the invariant, the variant
        let (b, c, kvp) = (self.base.clone(), self.code.clone(), kv);
        let qhp = self.print(&self.qs[jh].1);
        let mut lines = vec![
            format!("let {cl}({lwn}, {lin}) := tr.pt(s, V, {b}, {c}, {}, {h}, {hst}, {}, empty, WRAP({qhp}), {lwn})", st.fr, self.fd),
            format!("let {pi}({lwn}, {lin}) := tr.count_inv({kvp}, {lin}) && {lwn} in abi.World && {lwn} in univ(1)"),
            format!("let {mv}({lwn}, {lin}) := tr.count_var({kvp}, {lin})"),
            format!("have nat{ln}: all {lwn} {lin}. {pi}({lwn}, {lin}) -> {mv}({lwn}, {lin}) in omega proof"),
            format!("  fix {lwn}"),
            format!("  fix {lin}"),
            format!("  assume h: {pi}({lwn}, {lin})"),
            format!("  have c: tr.count_inv({kvp}, {lin}) by taut(h)"),
            format!("  show := apply(tr.count_nat, {{{kvp}}}, {{{lin}}}, simp(), c)"),
            "qed".into(),
            format!("have step{ln}: all {lwn} {lin}. {pi}({lwn}, {lin}) -> (all x2 y2. {pi}(x2, y2) -> int_lt({mv}(x2, y2), {mv}({lwn}, {lin})) -> {cl}(x2, y2)) -> {cl}({lwn}, {lin}) proof"),
        ];
        let mut sb = vec![
            format!("fix {lwn}"),
            format!("fix {lin}"),
            format!("assume {hp}: {pi}({lwn}, {lin})"),
            format!("assume {ih}: all x2 y2. {pi}(x2, y2) -> int_lt({mv}(x2, y2), {mv}({lwn}, {lin})) -> {cl}(x2, y2)"),
            format!("have hW{lwn}: {lwn} in abi.World && {lwn} in univ(1) by taut({hp})"),
            format!("have hvu{lwn}: {lwn} in univ(1) by taut({hp})"),
            format!("have {cc}: tr.count_inv({kvp}, {lin}) by taut({hp})"),
            format!("have {ci} := expand({cc}, tr.count_inv)"),
        ];
        sb.extend(local);
        sb.extend(body_pf.lines);
        let pn = self.fresh("p");
        sb.push(format!("have {pn} := {}", body_pf.expr));
        sb.push(format!("show := mp({}, mp({unroll}, {{{lwn}}}), {pn})", self.wred(&st_head, jh, ju)));
        lines.extend(indent(sb));
        lines.push("qed".into());
        lines.push(format!("have loop{ln} := mp(tr.wf2[claim := x y. {cl}(x, y), p := x y. {pi}(x, y), mm := x y. {mv}(x, y)], nat{ln}, step{ln})"));
        let i0p = self.print(&i0);
        if nat(&i0) != Some(0) {
            return Err(bad("whose counter does not start at 0"));
        }
        lines.push(format!("have i0{ln} := apply(tr.count_init, {{{kvp}}}, simp())"));
        lines.push(format!("have c{ln} := mp(all_elim(loop{ln}, {{{wn}}}, {{{i0p}}}), taut(i0{ln}, {}))", st.hw));
        let fdl = self.fd;
        let rs = format!(
            "mp(tr.pt_rs, {{s}}, {{V}}, {{{b}}}, {{{c}}}, {{{}}}, {{{h}}}, {{{}}}, {{{fdl}}}, {{{}}}, {{WRAP({})}}, {{{wn}}}, c{ln})",
            st.fr, st.hst, st.rs, self.qs[j0].0
        );
        let expr = format!("mp({}, mp({nodiv0}, {{{wn}}}), {rs})", self.wred(st, qi, j0));
        Ok(Pf { lines, expr })
    }

    /// the loop's head again (its body's end): the claim there, by the
    /// induction hypothesis at the world and counter now
    fn loop_back(&mut self, st: &St, qi: usize, l: usize) -> Result<Pf, String> {
        let lp = self.loops[l].clone();
        let q = self.qs[qi].1.clone();
        let badm = format!("{:x}: back at the loop's head, the rest not the loop's: {}", st.a, self.print(&q));
        let bad = || badm.clone();
        // the rest: ex x8. (while_rel(pair(x0, T'), ..) && !(fst(x8) = 2)) && (ex x2. k(x8, x2) && x1 = x2)
        let body = self.app(&q, "mkprog", 1).ok_or_else(bad)?[0].clone();
        let y = self.app(&self.app(&body, "ex", 1).ok_or_else(bad)?[0], "and", 2).ok_or_else(bad)?.to_vec();
        let al = self.lam(&y[0], &["x0", "x1", "x8"], &["x0", "x8"]).ok_or_else(bad)?;
        let ek = self.app(&y[1], "ex", 1).ok_or_else(bad)?.to_vec();
        let ka = self.app(&ek[0], "and", 2).ok_or_else(bad)?.to_vec();
        let kl = self.lam(&ka[0], &["x0", "x1", "x8", "x2"], &["x8", "x2"]).ok_or_else(bad)?;
        let (j, settle) = self.by(qi, "tr.qs_settle", &[("a", al.clone()), ("k", kl)])?;
        // the counter now: T' = li + 1, at the home
        let g0 = self.app(&al, "and", 2).ok_or_else(bad)?[0].clone();
        let wr = self.app(&g0, "while_rel", 5).ok_or_else(bad)?.to_vec();
        let tp = self.app(&wr[0], "pair", 2).ok_or_else(bad)?[1].clone();
        let step = self.mk("bits_add", vec![lit(32), lp.li.clone(), lit(1)]);
        if self.expand(&tp) != self.expand(&step) {
            return Err(format!("{:x}: the counter at the loop's end {} is not {} + 1", st.a, self.print(&tp), self.print(&lp.li)));
        }
        match st.hsm.get(&lp.d) {
            Some((4, x)) if self.canon(x) == self.canon(&tp) && st.hsm.len() == 1 => {}
            _ => return Err(format!("{:x}: the counter's home not the counter at the loop's end", st.a)),
        }
        // (the rest now: the claim's at T')
        let Node::Var(liv, _) = lp.li.node() else { unreachable!() };
        let qh2 = self.canon(&lp.qh.subst_var(*liv, &tp, &self.env.binders_fn()));
        if self.canon(&self.qs[j].1) != qh2 {
            return Err(format!("{:x}: the rest at the loop's end not the claim's:\n  {}\n  {}", st.a, self.print(&self.qs[j].1), self.print(&qh2)));
        }
        // the invariant at (W', T'), the variant smaller: by the counter's step
        let k = lp.k;
        let g = self.mk("not", vec![self.mk("int_lt", vec![self.mk("sint", vec![lit(32), lit(k)]), self.mk("sint", vec![lit(32), lp.li.clone()])])]);
        let hg = st.hyps.iter().find(|h| h.0 == g).map(|h| h.1.clone()).ok_or_else(|| format!("{:x}: the loop's condition not in scope", st.a))?;
        let (lip, tpp, wn) = (self.print(&lp.li), self.print(&tp), st.wn.clone());
        let cc = lp.ci.replacen("ci", "cc", 1);
        let (csn, cn) = (self.fresh("cs"), self.fresh("c"));
        let lines = vec![
            format!("have {csn} := apply(tr.count_step, {{{k}}}, {{{lip}}}, simp(), {cc}, simp(), {hg})"),
            format!("have {cn} := mp(all_elim({}, {{{wn}}}, {{{tpp}}}), taut({csn}, {}), taut({csn}))", lp.ih, st.hw),
        ];
        let fdl = self.fd;
        let rs = format!(
            "mp(tr.pt_rs, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{fdl}}}, {{{}}}, {{WRAP({})}}, {{{wn}}}, {cn})",
            self.base, self.code, st.fr, st.a, st.hst, st.rs, self.qs[j].0
        );
        let expr = format!("mp({}, mp({settle}, {{{wn}}}), {rs})", self.wred(st, qi, j));
        Ok(Pf { lines, expr })
    }

    /// the rest `qi`'s head a loop: `ex x8. while_rel(l0, c, b, tr, x8) && k`
    /// (its parts: l0, b, tr, k, as the rest has them)
    fn loop_head(&self, qi: usize) -> Option<Vec<Term>> {
        let body = self.app(&self.qs[qi].1, "mkprog", 1)?[0].clone();
        let e = self.app(&body, "ex", 1)?;
        let y = self.app(&e[0], "and", 2)?;
        // (or guarded: while_rel(..) && !(fst(x8) = 2), at the body's end)
        let w0 = self.app(&y[0], "and", 2).map(|g| g[0].clone()).unwrap_or(y[0].clone());
        let wr = self.app(&w0, "while_rel", 5)?;
        Some(vec![wr[0].clone(), wr[2].clone(), wr[3].clone(), y[1].clone()])
    }

    /// a linear step: the rule's text with `{NEXT}`, the state after
    fn then(&mut self, text: String, st2: St) -> Result<Pf, String> {
        let rest = self.prove(st2)?;
        let pn = self.fresh("p");
        let mut lines = rest.lines;
        lines.push(format!("have {} := {}", pn, rest.expr));
        Ok(Pf { lines, expr: text.replace("{NEXT}", &pn) })
    }

    /// the same, after the lines `pre` (the next point's definitions)
    fn then_pre(&mut self, text: String, st2: St, pre: Vec<String>) -> Result<Pf, String> {
        let rest = self.prove(st2)?;
        let pn = self.fresh("p");
        let mut lines = pre;
        lines.extend(rest.lines);
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

    /// the instance's common head: `{s}, {V}, {base}, {code}, {fr}, {a}, {a2}, {len}`
    fn head(&self, rule: &str, a: u128, insn: &Insn) -> String {
        format!("mp(tr.{}, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}", rule, self.base, self.code, self.fr, a, (a + insn.len) % P64, insn.len)
    }

    /// a home's key: the offset from the entry's rsp of rsp + d in the frame
    fn hkey(&self, d: u128) -> u128 {
        (d + P64 - self.fr % P64) % P64
    }

    /// the instance's tail: the coupling's maps, the decode fact, n literal
    /// facts, the extra premises, the next point
    fn tail(&self, st: &St, insn: &Insn, n: usize, extra: &[String]) -> String {
        self.tail_ds(st, insn, n, extra, true)
    }

    /// the same for a rule reading memory: before the frame is written, no
    /// flag (the rule's claims at `ds` false)
    fn tailv(&self, st: &St, insn: &Insn, n: usize, extra: &[String]) -> Result<String, String> {
        Ok(self.tail_ds(st, insn, n, extra, true))
    }

    fn tail_ds(&self, st: &St, insn: &Insn, n: usize, extra: &[String], with_ds: bool) -> String {
        let ds = if with_ds { format!(", {{{}}}", st.ds) } else { String::new() };
        let mut t = format!(", {{HS}}{}, {{{}}}, {{{}}}, {{W}}, {}", ds, st.rs, self.p(&st.spec), insn.name);
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

    /// the same for a rule writing a home: the homes it leaves (hs2) after
    /// the map
    fn tail_h(&self, st: &St, insn: &Insn, hs2: &str, n: usize, extra: &[String]) -> String {
        let mut t = format!(", {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}", hs2, st.ds, st.rs, self.p(&st.spec), insn.name);
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
        let insn = self.insns.get(&a).cloned().ok_or_else(|| format!("no decode fact at {:x}", a))?;
        let r = self.insn_at(&st, &insn);
        // (the instance's homes and world: the point's)
        let mut pf = r?;
        self.lf = match st.lp {
            Some(l) => format!("L, {}", self.loops[l].ci),
            None => "L".into(),
        };
        // (registers and homes deep in their maps: their `in dom` facts, determined)
        for d in self.deep_doms(&st.rs).into_iter().chain(deep_hdoms(&st.hst)) {
            self.lf = format!("{}, {}", self.lf, d);
        }
        pf.expr = self.lfacts(&pf.expr.replace("{HS}", &format!("{{{}}}", st.hst)).replace("{W}", &format!("{{{}}}", st.wn)));
        Ok(pf)
    }

    fn insn_at(&mut self, st: &St, insn: &Insn) -> Result<Pf, String> {
        let a = st.a;
        let wn = st.wn.clone();
        let a2 = (a + insn.len) % P64;
        let fs = self.print(&insn.fields);
        let bad = |what: &str| format!("{:x}: {} (row {}): {}", a, what, insn.row, fs);
        let reg = |g: &Term| nat(g).ok_or_else(|| bad("a register that is not a literal"));
        let f = insn.fields.clone();
        let fr = self.fr;
        let home = |hs: &BTreeMap<u128, (u128, Term)>, d: &Term| -> Result<Term, String> {
            let d = nat(d).ok_or_else(|| bad("a displacement that is not a literal"))?;
            match hs.get(&((d + P64 - fr % P64) % P64)) {
                Some((4, x)) => Ok(x.clone()),
                _ => Err(format!("{:x}: no 4-byte home at rsp{:+}", a, d as i128 - if d >= P64 / 2 { P64 as i128 } else { 0 })),
            }
        };
        // (in a zero-initialization: its stores only)
        if st.z.is_some() && insn.row != 145 && insn.row != 150 {
            return Err(bad("in a zero-initialization: not a store of the zero register"));
        }
        match insn.row {
            // pxor x, x: a zero-initialization begun -- the spec's store of
            // zeros made at once (tr.ptz_red), the machine's by the stores of x
            135 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let xr = reg(&x[0])?;
                if self.tag(&x[1]).map(|(k, r)| (k, nat(&r))) != Some((0, Some(xr))) {
                    return Err(bad("pxor of two registers"));
                }
                let (hc, _, pre, st2, red, sa, so) = self.spec_store_x(st, None, None)?;
                if so.data.is_none() {
                    return Err(bad("pxor before a spec's store that is not of zeros"));
                }
                let o = nat(&so.off).ok_or_else(|| bad("a zero-initialization at an offset that is not a literal"))?;
                let t = self.head("pxor_z", a, insn) + &self.terms(&[&x[0], &x[2], &x[3], &sa]) + &self.tail(st, insn, 3, &[]);
                let rd = format!(
                    "mp(tr.ptz_red, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{a2}}}, {{HS}}, {{{}}}, {{{}}}, {{{xr}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, simp(L), simp(L), simp(L), simp(L), simp(L), {hc}, simp(), {red}, {{NEXT}})",
                    self.base, self.code, st.fr, st.ds, st.rs, self.print(&sa), so.n, self.print(&so.p), self.print(&so.off), self.p(&st.spec), self.p(&st2.spec), st2.wn
                );
                let mut st3 = st2;
                st3.a = a2;
                st3.z = Some((xr, so.p.clone(), o, so.n));
                return self.then_pre(t.replace("{NEXT}", &rd), st3, pre);
            }
            // movups / movq [b + d], x (x zero): the next c of the bytes
            145 | 150 => {
                let Some((xr, bz, o, k)) = st.z.clone() else { return Err(bad("a store of an xmm register outside a zero-initialization")) };
                let (c, nf) = if insn.row == 145 { (16u128, 4) } else { (8u128, 5) };
                let x = self.pairs(&f, nf).ok_or_else(|| bad("fields"))?;
                if reg(&x[0])? != xr {
                    return Err(bad("a store of an xmm register not zeroed"));
                }
                let (bn, b, d) = self.base_disp(&x[1]).ok_or_else(|| bad("not [b + d]"))?;
                let bv = self.need_reg(st, bn, 8)?;
                if self.canon(&bv) != self.canon(&bz) || nat(&d) != Some(o) || c > k {
                    return Err(format!("{:x}: the machine stores {} bytes at {} + {}, the zero-initialization's rest: {} bytes at {} + {}", a, c, self.print(&bv), self.print(&d), k, self.print(&bz), o));
                }
                let at = |g: &Gen, o: u128| g.mk("bits_add", vec![lit(64), bz.clone(), lit(o)]);
                let (aa, a2t) = (at(self, o), at(self, o + c));
                let mut ts: Vec<&Term> = vec![&x[0], &b, &d];
                ts.extend(x[2..].iter());
                let (kt, k2t) = (lit(k), lit(k - c));
                ts.extend([&bv, &aa, &kt, &a2t, &k2t]);
                let rule = if insn.row == 145 { "zst_ups" } else { "zst_q" };
                let mut t = self.head(rule, a, insn) + &self.terms(&ts) + &self.tail(st, insn, 11, &["arith()".into(), "arith()".into()]);
                let mut st2 = st.clone();
                st2.a = a2;
                if k == c {
                    // (all stored: the plain claim on)
                    let ex = format!(
                        "mp(tr.ptz_exit, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{a2}}}, {{HS}}, {{{}}}, {{{}}}, {{{xr}}}, {{{}}}, {{{}}}, {{W}}, simp(L), {{NEXT}})",
                        self.base, self.code, st.fr, st.ds, st.rs, self.print(&a2t), self.p(&st.spec)
                    );
                    t = t.replace("{NEXT}", &ex);
                    st2.z = None;
                } else {
                    st2.z = Some((xr, bz, o + c, k - c));
                }
                return self.then(t, st2);
            }
            // mov r32/r64, [rsp + d]: the home's value
            76 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                // mov r64, [b + d] (b holding a pointer): the spec's field load
                if self.rsp_mem(&x[2]).is_none() && nat(&x[0]) == Some(8) {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let hc = self.mem_hyp(st, &bp, &d, 8)?;
                    let t = self.head("load64_bd", a, insn) + &self.terms(&[&x[1], &b, &d, &x[4], &bp]) + &self.tailv(st, insn, 6, &[hc])?;
                    let v = self.parse(&format!("bits_of_int(64, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 8))", self.print(&bp), self.print(&d)))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 8, v);
                    return self.then(t, st2);
                }
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let c = lit(self.hkey(dn));
                let v = match (n, st.hsm.get(&self.hkey(dn))) {
                    (4, _) => home(&st.hsm, &d)?,
                    (8, Some((8, x))) => x.clone(),
                    _ => return Err(bad("no home of the load's width")),
                };
                let rule = if n == 8 { "load64_home" } else { "load32_home" };
                let t = self.head(rule, a, insn) + &self.terms(&[&x[1], &d, &c, &x[3], &x[4], &v]) + &self.tail(st, insn, 6, &[]);
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
                let v = home(&st.hsm, &d)?;
                let u = self.need_reg(st, g, 4)?;
                let c = lit(self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?));
                let t = self.head("and32_home", a, insn) + &self.terms(&[&x[1], &d, &c, &x[3], &x[4], &v, &u]) + &self.tail(st, insn, 8, &[]);
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
                            "bits_mul(64, bits_of_int(52, int_mod(int_div(gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 7), int_pow(2, 4)), int_pow(2, 52))), 4096)",
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
                // mov [rsp + d], r32 / r64: the home c := the register's low n bytes
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let n = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                    if n != 4 && n != 8 {
                        return Err(bad("a store to a home of other than 4 or 8 bytes"));
                    }
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let cn = self.hkey(dn);
                    let (ng, u) = self.reg(st, g).ok_or_else(|| bad("an empty register"))?;
                    // (the value: the register's; its low bytes, of a 64-bit word bits_of_int(64, y): y's)
                    let xv = if ng == n {
                        u.clone()
                    } else {
                        let y = self.app(&u, "bits_of_int", 2).filter(|y| nat(&y[0]) == Some(64)).map(|y| y[1].clone()).unwrap_or_else(|| u.clone());
                        self.mk("bits_of_int", vec![lit(8 * n), y])
                    };
                    let (_, hs2, hk) = self.hkeep(st, cn, n);
                    let t = self.head("store_home_r", a, insn)
                        + &self.terms(&[&x[0], &x[1], &d, &lit(cn), &x[3], &x[4], &lit(ng), &u, &xv])
                        + &self.tail_h(st, insn, &hs2, 9, &["defs(simp(), tr.hrange)".into(), "simp(L)".into(), "simp(L)".into(), "simp(L)".into(), hk]);
                    let st2 = self.set_home(st, a2, cn, n, xv);
                    return self.then(t, st2);
                }
                // mov [b + d], r64 (b holding a pointer): the spec's 8-byte field store
                if let (Some((bn, b, d)), Some(8)) = (self.base_disp(&x[2]).filter(|z| z.0 != 4), nat(&x[0])) {
                    let bv = self.need_reg(st, bn, 8)?;
                    let u = self.need_reg(st, g, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                    let (hc, v, pre, st2, red, _) = self.spec_store(st, &ad, 8)?;
                    if self.canon(&v) != self.canon(&u) {
                        return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&u), self.print(&v)));
                    }
                    let t = self.head("store64_bd", a, insn)
                        + &self.terms(&[&x[1], &b, &d, &x[3], &x[4], &bv, &u])
                        + &format!(", {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {}", st.ds, st.rs, self.p(&st.spec), self.p(&st2.spec), st2.wn, insn.name)
                        + &", simp(L)".repeat(10)
                        + &format!(", simp(L, {hc}), simp(), {red}, {{NEXT}})");
                    let mut st3 = st2;
                    st3.a = a2;
                    return self.then_pre(t, st3, pre);
                }
                let Some((0, h)) = self.tag(&x[2]) else { return Err(bad("a store to memory other than a home")) };
                let hn = reg(&h)?;
                // (mov r32, r32 / mov r64, r64)
                let n = if nat(&x[0]) == Some(8) { 8 } else { 4 };
                let u = self.need_reg(st, g, n)?;
                let t = self.head(if n == 8 { "mov64_rr" } else { "mov32_rr" }, a, insn) + &self.terms(&[&x[1], &h, &x[3], &x[4], &u]) + &self.tail(st, insn, 5, &[]);
                self.scratch.insert(hn);
                let st2 = self.set_reg(st, a2, hn, n, u);
                self.then(t, st2)
            }
            // shr r32 / dword [rsp + d], 1
            73 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                if nat(&x[0]) != Some(4) || nat(&x[1]) != Some(5) || x[2] != x[3] {
                    return Err(bad("not shr r/m32, 1"));
                }
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let u = home(&st.hsm, &d)?;
                    let cn = self.hkey(dn);
                    let (_, hs2, hk) = self.hkeep(st, cn, 4);
                    let t = self.head("shr32_1_home", a, insn) + &self.terms(&[&d, &lit(cn), &u]) + &self.tail_h(st, insn, &hs2, 6, &[hk]);
                    let r = self.mk("bits_shr", vec![lit(32), u, lit(1)]);
                    let r = self.value(&r);
                    let st2 = self.set_home(st, a2, cn, 4, r);
                    return self.then(t, st2);
                }
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not shr r/m32, 1")) };
                let gn = reg(&g)?;
                let u = self.need_reg(st, gn, 4)?;
                let t = self.head("shr32_1", a, insn) + &self.terms(&[&g, &u]) + &self.tail(st, insn, 4, &[]);
                let r = self.mk("bits_shr", vec![lit(32), u, lit(1)]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
                self.then(t, st2)
            }
            // or dword [rsp + d], r32
            38 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not or [rsp + d], r32"))?;
                let g = reg(&x[1])?;
                if nat(&x[0]) != Some(4) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not or dword [rsp + d], r32"));
                }
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let u = home(&st.hsm, &d)?;
                let v = self.need_reg(st, g, 4)?;
                let cn = self.hkey(dn);
                let (_, hs2, hk) = self.hkeep(st, cn, 4);
                let t = self.head("or32_home", a, insn) + &self.terms(&[&d, &lit(cn), &x[1], &v, &u]) + &self.tail_h(st, insn, &hs2, 9, &[hk]);
                let r = self.mk("bits_or", vec![lit(32), u, v]);
                let r = self.value(&r);
                let st2 = self.set_home(st, a2, cn, 4, r);
                self.then(t, st2)
            }
            // cmp [rsp + d], r64 (the home's word against g's); je / jne t
            56 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not cmp [rsp + d], r64"))?;
                if nat(&x[0]) != Some(8) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not cmp qword [rsp + d], r64"));
                }
                let g = reg(&x[1])?;
                let cn = self.hkey(nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?);
                let Some((8, xv)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                let u = self.need_reg(st, g, 8)?;
                let (j, jn, a3, tt, cc) = self.jcc(a2)?;
                let eq = self.mk("eq", vec![xv.clone(), u.clone()]);
                let (rule, c) = match cc {
                    4 => ("cmp64_hr_je", self.mk("not", vec![eq])),
                    5 => ("cmp64_hr_jne", eq),
                    _ => return Err(bad("cmp not followed by je or jne")),
                };
                let text = format!(
                    "mp(tr.{rule}, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                    self.base,
                    self.code,
                    self.fr,
                    a,
                    a2,
                    a3,
                    tt,
                    insn.len,
                    jn,
                    self.terms(&[&x[1], &d, &lit(cn), &j, &xv, &u]),
                    st.ds,
                    st.rs,
                    self.p(&st.spec),
                    insn.name,
                    self.insns[&a2].name,
                    ", simp(L)".repeat(13)
                );
                self.branch(st, c, a3, tt, text)
            }
            // sub r32, r32 (the source's low 32 bits)
            50 => {
                let x = self.pairs(&f, 5).ok_or_else(|| bad("fields"))?;
                let Some((0, g)) = self.tag(&x[2]) else { return Err(bad("not sub r32, r32")) };
                if nat(&x[0]) != Some(4) || x[3] != x[2] || self.tag(&x[4]) != Some((0, x[1].clone())) {
                    return Err(bad("not sub r32, r32"));
                }
                let (gn, hn) = (reg(&g)?, reg(&x[1])?);
                let u = self.need_reg(st, gn, 4)?;
                let (nh, xv) = self.reg(st, hn).ok_or_else(|| bad("an empty register"))?;
                let t = self.head("sub32_rr", a, insn) + &self.terms(&[&g, &x[1], &u, &lit(nh), &xv]) + &self.tail(st, insn, 7, &[]);
                let r = self.mk("bits_sub", vec![lit(32), u, self.mk("bits_of_int", vec![lit(32), xv.clone()])]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                let st2 = self.set_reg(st, a2, gn, 4, r);
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
                // add / cmp dword [rsp + d], imm8: the home d (u)
                if let Some(d) = self.rsp_mem(&x[2]) {
                    let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                    // cmp qword [rsp + d], imm8; je t: the home's word against the immediate
                    if nat(&x[0]) == Some(8) && x[3] == x[2] && nat(&x[1]) == Some(7) {
                        let kk = lit(if imm >= 128 { imm + 0xffff_ffff_ffff_ff00 } else { imm });
                        let cn = self.hkey(dn);
                        let Some((8, xv)) = st.hsm.get(&cn).cloned() else { return Err(bad("no 8-byte home there")) };
                        let (j, jn, a3, tt, cc) = self.jcc(a2)?;
                        if cc != 4 {
                            return Err(bad("cmp qword of a home not followed by je"));
                        }
                        let c = self.mk("not", vec![self.mk("eq", vec![xv.clone(), kk.clone()])]);
                        let text = format!(
                            "mp(tr.cmp64i_home_je, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                            self.base,
                            self.code,
                            self.fr,
                            a,
                            a2,
                            a3,
                            tt,
                            insn.len,
                            jn,
                            self.terms(&[&d, &lit(cn), &x[4], &kk, &j, &xv]),
                            st.ds,
                            st.rs,
                            self.p(&st.spec),
                            insn.name,
                            self.insns[&a2].name,
                            ", simp(L)".repeat(11)
                        );
                        return self.branch(st, c, a3, tt, text);
                    }
                    let kk = lit(if imm >= 128 { imm + 0xffff_ff00 } else { imm });
                    if nat(&x[0]) != Some(4) || x[3] != x[2] {
                        return Err(bad("not dword [rsp + d], imm8"));
                    }
                    let u = home(&st.hsm, &d)?;
                    let cn = self.hkey(dn);
                    let ck = lit(cn);
                    return match nat(&x[1]) {
                        Some(0) => {
                            let (_, hs2, hk) = self.hkeep(st, cn, 4);
                            let t = self.head("add32_home", a, insn) + &self.terms(&[&d, &ck, &x[4], &kk, &u]) + &self.tail_h(st, insn, &hs2, 8, &[hk]);
                            let r = self.mk("bits_add", vec![lit(32), u, kk]);
                            let r = self.value(&r);
                            let st2 = self.set_home(st, a2, cn, 4, r);
                            self.then(t, st2)
                        }
                        // cmp; jle t: on to a3 (the loop's leaving) when kk <s u
                        Some(7) => {
                            let (j, jn, a3, tt, cc) = self.jcc(a2)?;
                            if cc != 14 {
                                return Err(bad("cmp of a home not followed by jle"));
                            }
                            let c = self.mk("int_lt", vec![self.mk("sint", vec![lit(32), kk.clone()]), self.mk("sint", vec![lit(32), u.clone()])]);
                            let text = format!(
                                "mp(tr.cmp32_home_jle, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                                self.base,
                                self.code,
                                self.fr,
                                a,
                                a2,
                                a3,
                                tt,
                                insn.len,
                                jn,
                                self.terms(&[&d, &ck, &x[4], &kk, &j, &u]),
                                st.ds,
                                st.rs,
                                self.p(&st.spec),
                                insn.name,
                                self.insns[&a2].name,
                                ", simp(L)".repeat(10)
                            );
                            self.branch(st, c, a3, tt, text)
                        }
                        _ => Err(bad("an operation on a home other than add, cmp")),
                    };
                }
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let imm = nat(&x[4]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if imm >= 128 { imm + 0xffff_ff00 } else { imm };
                let size = nat(&x[0]).ok_or_else(|| bad("fields"))?;
                if k != 0 || (size != 4 && size != 8) {
                    return Err(bad("not r32/r64, imm8"));
                }
                let gn = reg(&g)?;
                // sub rsp, k: the frame grows (the prologue)
                if (size, nat(&x[1]), gn) == (8, Some(5), 4) {
                    if imm >= 128 || self.fr + imm > 65536 {
                        return Err(bad("sub rsp beyond the frame's bound"));
                    }
                    let fr2 = self.fr + imm;
                    let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                    let t = self.head("sub_rsp", a, insn) + &self.terms(&[&x[3], &x[4], &lit(fr2)]) + &self.tail(st, insn, 6, &[n4]);
                    let mut st2 = st.clone();
                    st2.a = a2;
                    st2.fr = fr2;
                    return self.then(t, st2);
                }
                // add rsp, k: the frame's end (k at most the frame)
                if (size, nat(&x[1]), gn) == (8, Some(0), 4) {
                    if imm >= 128 || imm > self.fr {
                        return Err(bad("add rsp beyond the frame"));
                    }
                    let fr2 = self.fr - imm;
                    let n4 = self.dom_out_pf(&st.rs, 4).ok_or_else(|| bad("rsp in the register map"))?;
                    let t = self.head("add_rsp", a, insn) + &self.terms(&[&x[3], &x[4], &lit(fr2)]) + &self.tail(st, insn, 6, &[n4]);
                    let mut st2 = st.clone();
                    st2.a = a2;
                    st2.fr = fr2;
                    return self.then(t, st2);
                }
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
                            "bits_of_int({kb}, int_mod(int_div(gimple.bytes_at(app({wn}, \"vm\"), {}, 2), int_pow(2, {pos})), int_pow(2, {kb})))",
                            self.print(&q)
                        ))?;
                        let r = self.value(&r);
                        self.scratch.insert(gn);
                        let st2 = self.set_reg(st, a2, gn, 4, r);
                        return self.then(t, st2);
                    }
                }
                // add r32, imm8 (g holding a value of at most 4 bytes): g := u + kk
                if (size, nat(&x[1])) == (4, Some(0)) {
                    let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                    if n > 4 {
                        return Err(bad("add r32 of a wider value"));
                    }
                    let t = self.head("add32_imm", a, insn) + &self.terms(&[&g, &x[3], &x[4], &lit(kk), &lit(n), &u]) + &self.tail(st, insn, 7, &[]);
                    let r = self.mk("bits_add", vec![lit(32), u, lit(kk)]);
                    let r = self.value(&r);
                    self.scratch.insert(gn);
                    let st2 = self.set_reg(st, a2, gn, 4, r);
                    return self.then(t, st2);
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
                            "mp(tr.cmp32_ja, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                            self.base,
                            self.code,
                            self.fr,
                            a,
                            a2,
                            a3,
                            tt,
                            insn.len,
                            jn,
                            self.terms(&[&g, &x[3], &x[4], &lit(kk), &j, &u]),
                            st.ds,
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
                // cmp al, imm8; jne t: on to a3 when al = k (k as GIMPLE writes
                // it: a negative byte bits_neg(8, -k))
                if cc == 5 {
                    let kk = if k >= 128 { self.mk("bits_neg", vec![lit(8), lit(256 - k)]) } else { lit(k) };
                    let c = self.mk("eq", vec![b.clone(), kk.clone()]);
                    let text = format!(
                        "mp(tr.cmp8_jne, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                        self.base,
                        self.code,
                        self.fr,
                        a,
                        a2,
                        a3,
                        tt,
                        insn.len,
                        jn,
                        self.terms(&[&f, &kk, &j, &b]),
                        st.ds,
                        st.rs,
                        self.p(&st.spec),
                        insn.name,
                        self.insns[&a2].name,
                        ", simp(L)".repeat(8)
                    );
                    return self.branch(st, c, a3, tt, text);
                }
                if cc != 6 {
                    return Err(bad("cmp not followed by jbe or jne"));
                }
                let c = self.mk("int_lt", vec![lit(k), b.clone()]);
                let text = format!(
                    "mp(tr.cmp8_jbe, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                    self.base,
                    self.code,
                    self.fr,
                    a,
                    a2,
                    a3,
                    tt,
                    insn.len,
                    jn,
                    self.terms(&[&f, &j, &b]),
                    st.ds,
                    st.rs,
                    self.p(&st.spec),
                    insn.name,
                    self.insns[&a2].name,
                    ", simp(L)".repeat(7)
                );
                self.branch(st, c, a3, tt, text)
            }
            // movsxd r64, r32: g := h's 32 bits sign-extended
            113 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (k, h) = self.tag(&x[1]).ok_or_else(|| bad("fields"))?;
                if k != 0 {
                    return Err(bad("not movsxd r64, r32"));
                }
                let (g, hn) = (reg(&x[0])?, reg(&h)?);
                let u = self.need_reg(st, hn, 4)?;
                let t = self.head("movsxd", a, insn) + &self.terms(&[&x[0], &h, &x[2], &x[3], &u]) + &self.tail(st, insn, 5, &[]);
                let r = self.mk("bits_sext", vec![lit(32), lit(64), u]);
                let r = self.value(&r);
                self.scratch.insert(g);
                let st2 = self.set_reg(st, a2, g, 8, r);
                self.then(t, st2)
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
                // lea r32, [b + d]: u + d, 32 bits
                if nat(&x[0]) == Some(4) {
                    let (bk, b) = m.get("base").and_then(|b| self.tag(b)).ok_or_else(|| bad("fields"))?;
                    let d = m.get("disp").and_then(nat).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    if bk != 2 || m.get("index").map_or(true, |i| self.app(i, "none", 0).is_none()) || m.get("scale").and_then(nat) != Some(1) {
                        return Err(bad("not lea r32, [b + d]"));
                    }
                    let bn = reg(&b)?;
                    let (nb, u) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let kk = lit(d % (1 << 32));
                    let t = self.head("lea32_bd", a, insn) + &self.terms(&[&x[1], &b, &lit(d), &x[2], &x[3], &x[4], &lit(nb), &u, &kk]) + &self.tail(st, insn, 7, &[]);
                    let r = self.mk("bits_add", vec![lit(32), u, kk]);
                    let r = self.value(&r);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 4, r);
                    return self.then(t, st2);
                }
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
                // movzx r32, byte [rip + d]: the spec's load of a static's byte
                if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = (a2 + d) % P64;
                    let hc = self.static_hyp(st, biga, false)?;
                    let t = self.head("movzx8_rip", a, insn) + &self.terms(&[&x[1], &lit(d), &x[4], &lit(biga)]) + &self.tailv(st, insn, 4, &[format!("simp(L, {})", hc)])?;
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({wn}, \"vm\"), {biga}, 1))"))?;
                    let v = self.value(&v);
                    self.scratch.insert(g);
                    let st2 = self.set_reg(st, a2, g, 1, v);
                    return self.then(t, st2);
                }
                // movzx r32, byte [b + d] (b holding a pointer): the spec's field load
                if self.app(&m["index"], "none", 0).is_some() && nat(&m["disp"]) != Some(0) {
                    let (bn, b, d) = self.base_disp(&x[2]).ok_or_else(|| bad("not [b + d]"))?;
                    let bp = self.need_reg(st, bn, 8)?;
                    let hc = self.mem_hyp(st, &bp, &d, 1)?;
                    let t = self.head("movzx8_bd", a, insn) + &self.terms(&[&x[1], &b, &d, &x[4], &bp]) + &self.tailv(st, insn, 6, &[hc])?;
                    let v = self.parse(&format!("bits_of_int(8, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 1))", self.print(&bp), self.print(&d)))?;
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
                    let t = self.head("movzx8_b", a, insn) + &self.terms(&[&x[1], &b, &x[4], &bv]) + &self.tailv(st, insn, 5, &[format!("taut({})", hc)])?;
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
                let t = self.head("movzx8_ld", a, insn) + &self.terms(&[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv]) + &self.tailv(st, insn, 8, &[format!("taut({})", hc)])?;
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
                    let t = self.head("movzx16_bd", a, insn) + &self.terms(&[&x[1], &b, &d, &x[4], &bp]) + &self.tailv(st, insn, 6, &[hc])?;
                    let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), bits_add(64, {}, {}), 2))", self.print(&bp), self.print(&d)))?;
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
                let t = self.head("movzx16_ld", a, insn) + &self.terms(&[&x[1], &b, &i, &x[4], &lit(nb), &bv, &iv]) + &self.tailv(st, insn, 8, &[hc])?;
                let v = self.parse(&format!("bits_of_int(16, gimple.bytes_at(app({wn}, \"vm\"), {}, 2))", self.print(&ad)))?;
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
            // test r8, r8; jne t / je t; test r64, r64; je t
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
                let (rule, nprem) = match (size, cc) {
                    (1, 5) => ("test8_jne", 8),
                    (1, 4) => ("test8_je", 8),
                    (8, 4) => ("test64_je", 7),
                    _ => return Err(bad("test not followed by the matched jump")),
                };
                // (the fall-through's condition: jne falls through on u = 0)
                let z = self.mk("eq", vec![u.clone(), lit(0)]);
                let c = if cc == 5 { z } else { self.mk("not", vec![z]) };
                let text = format!(
                    "mp(tr.{}, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}{}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, {}{}, {{T}}, {{F}})",
                    rule,
                    self.base,
                    self.code,
                    self.fr,
                    a,
                    a2,
                    a3,
                    tt,
                    insn.len,
                    jn,
                    self.terms(&[&g, &j, &u]),
                    st.ds,
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
                if st.fr != 0 {
                    return Err(format!("{:x}: ret with a frame of {} bytes", a, st.fr));
                }
                let Spec::Ret(val, pr) = &st.spec else {
                    return Err(format!("{:x}: ret before the procedure's result (the spec at {})", a, match &st.spec {
                        Spec::Proc(i) => self.print(&self.qs[*i].1),
                        _ => String::new(),
                    }));
                };
                // (no result: rax:rdx anything)
                if self.rbytes == 0 {
                    let expr = format!(
                        "mp(tr.ret_void, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, mp(tr.result_void, {{W}}))",
                        self.base, self.code, a, insn.len, st.ds, st.rs, pr, insn.name
                    );
                    return Ok(Pf { lines: vec![], expr });
                }
                let n = self.rbytes;
                let v = self.need_reg(st, 0, n)?;
                if &v != val {
                    return Err(format!("{:x}: rax holds {} = {}, the spec returns {} = {}", a, self.print(&v), self.print(&self.expand(&v)), self.print(val), self.print(&self.expand(val))));
                }
                let expr = format!(
                    "mp(tr.ret_insn, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {{{}}}, {}, simp(L), simp(L), mp(tr.result{}, {{W}}, {{{}}}))",
                    self.base,
                    self.code,
                    a,
                    insn.len,
                    st.ds,
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
            // mov byte [b + i], imm8 / mov byte [rip + d], imm8: the spec's store
            30 => {
                let x = self.pairs(&f, 3).ok_or_else(|| bad("fields"))?;
                let m = self.memop(&x[0]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let k = x[2].clone();
                if x[1] != x[0] {
                    return Err(bad("not mov byte [m], imm8"));
                }
                let (rule, terms, n, ad) = if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    ("store8i_rip", vec![lit(d), k.clone(), biga.clone()], 5, biga)
                } else {
                    let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                    if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&i)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]));
                    ("store8i_bi", vec![b.clone(), i.clone(), k.clone(), lit(nb), bv, iv], 9, ad)
                };
                let (hc, v, pre, st2, red, sa) = self.spec_store(st, &ad, 1)?;
                if self.eval_lit(&v) != nat(&k) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&k), self.print(&v)));
                }
                let _ = &sa;
                let tr: Vec<&Term> = terms.iter().collect();
                let t = self.head(rule, a, insn)
                    + &self.terms(&tr)
                    + &format!(", {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {}", st.ds, st.rs, self.p(&st.spec), self.p(&st2.spec), st2.wn, insn.name)
                    + &", simp(L)".repeat(n)
                    + &format!(", simp(L, {hc}), simp(), {red}, {{NEXT}})");
                let mut st3 = st2;
                st3.a = a2;
                self.then_pre(t, st3, pre)
            }
            // mov byte [rip + d] / [b + i], r8: the spec's store of the
            // register's low byte
            28 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let (gk, g) = self.tag(&x[3]).ok_or_else(|| bad("fields"))?;
                let gn = reg(&g)?;
                if gk != 0 || gn >= 4 {
                    return Err(bad("not mov byte [m], r8"));
                }
                let (n, u) = self.reg(st, gn).ok_or_else(|| bad("an empty register"))?;
                // (the address: a static's, or b + i; the rule's terms and
                // its literal facts' count)
                let (rule, terms, nlit, ad) = if bk == 1 {
                    let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                    let biga = lit((a2 + d) % P64);
                    ("store8_rip", vec![g.clone(), lit(d), x[0].clone(), x[1].clone(), lit(n), u.clone()], 8, biga)
                } else {
                    let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                    if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) {
                        return Err(bad("not [b + i]"));
                    }
                    let (bn, inn) = (reg(&b)?, reg(&i)?);
                    let (nb, bv) = self.reg(st, bn).ok_or_else(|| bad("an empty base register"))?;
                    let iv = self.need_reg(st, inn, 8)?;
                    let ad = self.canon(&self.mk("bits_add", vec![lit(64), iv.clone(), bv.clone()]));
                    ("store8_bi", vec![g.clone(), b.clone(), i.clone(), x[0].clone(), x[1].clone(), lit(nb), bv, iv, lit(n), u.clone()], 12, ad)
                };
                let (hc, v, pre, st2, red, sa) = self.spec_store(st, &ad, 1)?;
                // (the register's low byte: the spec's value, u + k against v + k)
                let (ue, ve) = (self.expand(&u), self.expand(&v));
                // (a constant: a literal, or bits_neg(n, k) -- 2^n - k)
                let konst = |t: &Term| -> Option<u128> {
                    self.eval_lit(t).or_else(|| {
                        let x = self.app(t, "bits_neg", 2)?;
                        let (n, k) = (nat(&x[0])?, self.eval_lit(&x[1])?);
                        (n < 64).then(|| ((1u128 << n) - k % (1u128 << n)) % (1u128 << n))
                    })
                };
                let low8 = (|| {
                    let x = self.app(&ue, "bits_add", 3)?;
                    let y = self.app(&ve, "bits_add", 3)?;
                    (nat(&x[0])? == 32 && nat(&y[0])? == 8 && self.canon(&x[1]) == self.canon(&y[1]) && konst(&x[2])? % 256 == konst(&y[2])? % 256)
                        .then(|| (x[1].clone(), x[2].clone(), y[2].clone()))
                })();
                let (bb, kk, kk2) = low8.ok_or_else(|| format!("{:x}: the stored byte {} = {} is not the spec's {} = {}", a, self.print(&u), self.print(&ue), self.print(&v), self.print(&ve)))?;
                let lp = if self.eval_lit(&kk).is_some() && self.eval_lit(&kk) == self.eval_lit(&kk2) {
                    format!("mp(tr.low8_add, {{{}}}, {{{}}}, simp(L), simp(L))", self.print(&bb), self.print(&kk))
                } else {
                    format!("mp(tr.low8_add_mod, {{{}}}, {{{}}}, {{{}}}, simp(L), simp(L), simp(L), simp(L))", self.print(&bb), self.print(&kk), self.print(&kk2))
                };
                let _ = &sa;
                let mut terms: Vec<&Term> = terms.iter().collect();
                terms.push(&v);
                if rule == "store8_rip" {
                    terms.push(&ad);
                }
                let t = self.head(rule, a, insn)
                    + &self.terms(&terms)
                    + &format!(", {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {}", st.ds, st.rs, self.p(&st.spec), self.p(&st2.spec), st2.wn, insn.name)
                    + &", simp(L)".repeat(nlit)
                    + &format!(", {lp}, simp(L, {hc}), simp(), {red}, {{NEXT}})");
                let mut st3 = st2;
                st3.a = a2;
                self.then_pre(t, st3, pre)
            }
            // nop
            109 => {
                let t = format!(
                    "mp(tr.nop, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, simp(L), {{NEXT}})",
                    self.base,
                    self.code,
                    self.fr,
                    a,
                    a2,
                    insn.len,
                    self.print(&f),
                    st.ds,
                    st.rs,
                    self.p(&st.spec),
                    insn.name
                );
                let mut st2 = st.clone();
                st2.a = a2;
                self.then(t, st2)
            }
            // jmp rel8
            125 => {
                let r = nat(&f).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let sx = if r & 0x80 != 0 { r + 0xffff_ffff_ffff_ff00 } else { r };
                let tt = (a2 + sx) % P64;
                let t = format!(
                    "mp(tr.jmp8, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {}, simp(L), simp(L), simp(L), {{NEXT}})",
                    self.base,
                    self.code,
                    self.fr,
                    a,
                    a2,
                    tt,
                    insn.len,
                    r,
                    st.ds,
                    st.rs,
                    self.p(&st.spec),
                    insn.name
                );
                let mut st2 = st.clone();
                st2.a = tt;
                self.then(t, st2)
            }
            // mov dword [rip + d], imm32: the spec's 4-byte store of k at a
            // static's address
            77 if self.pairs(&f, 4).and_then(|x| self.memop(&x[1])).and_then(|m| self.tag(&m["base"])).map_or(false, |b| b.0 == 1) => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let m = self.memop(&x[1]).ok_or_else(|| bad("fields"))?;
                if nat(&x[0]) != Some(4) || x[2] != x[1] {
                    return Err(bad("not mov dword [rip + d], imm32"));
                }
                let d = nat(&m["disp"]).ok_or_else(|| bad("a displacement that is not a literal"))?;
                let biga = lit((a2 + d) % P64);
                let k = x[3].clone();
                let (hc, v, pre, st2, red, sa) = self.spec_store(st, &biga, 4)?;
                if self.eval_lit(&v) != nat(&k) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, self.print(&k), self.print(&v)));
                }
                let _ = &sa;
                let t = self.head("store32i_rip", a, insn)
                    + &self.terms(&[&lit(d), &k, &biga])
                    + &format!(", {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {}", st.ds, st.rs, self.p(&st.spec), self.p(&st2.spec), st2.wn, insn.name)
                    + &", simp(L)".repeat(5)
                    + &format!(", simp(L, {hc}), simp(), {red}, {{NEXT}})");
                let mut st3 = st2;
                st3.a = a2;
                self.then_pre(t, st3, pre)
            }
            // mov qword [b + d], imm32 (b holding a pointer): the spec's 8-byte
            // field store of the immediate sign-extended
            77 if self.pairs(&f, 4).and_then(|x| self.base_disp(&x[1])).map_or(false, |z| z.0 != 4) => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let (bn, b, d) = self.base_disp(&x[1]).ok_or_else(|| bad("not [b + d]"))?;
                if nat(&x[0]) != Some(8) || x[2] != x[1] {
                    return Err(bad("not mov qword [b + d], imm32"));
                }
                let k = nat(&x[3]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                let kk = if k >= 1 << 31 { k + (P64 - (1 << 32)) } else { k };
                let bv = self.need_reg(st, bn, 8)?;
                let ad = self.canon(&self.mk("bits_add", vec![lit(64), bv.clone(), d.clone()]));
                let (hc, v, pre, st2, red, _) = self.spec_store(st, &ad, 8)?;
                if self.eval_lit(&v) != Some(kk) {
                    return Err(format!("{:x}: the machine stores {}, the spec {}", a, kk, self.print(&v)));
                }
                let t = self.head("store64i_bd", a, insn)
                    + &self.terms(&[&b, &d, &x[3], &lit(kk), &bv])
                    + &format!(", {{HS}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{W}}, {{{}}}, {}", st.ds, st.rs, self.p(&st.spec), self.p(&st2.spec), st2.wn, insn.name)
                    + &", simp(L)".repeat(9)
                    + &format!(", simp(L, {hc}), simp(), {red}, {{NEXT}})");
                let mut st3 = st2;
                st3.a = a2;
                self.then_pre(t, st3, pre)
            }
            // mov dword [rsp + d], imm32: the home d := k (the frame written)
            77 => {
                let x = self.pairs(&f, 4).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[1]).ok_or_else(|| bad("not a home"))?;
                let dn = nat(&d).ok_or_else(|| bad("a displacement that is not a literal"))?;
                if nat(&x[0]) != Some(4) || x[2] != x[1] {
                    return Err(bad("not mov dword [rsp + d], imm32"));
                }
                let cn = self.hkey(dn);
                let (_, hs2, hk) = self.hkeep(st, cn, 4);
                let k = x[3].clone();
                let t = self.head("store32i_home", a, insn)
                    + &self.terms(&[&d, &lit(cn), &k])
                    + &self.tail_h(st, insn, &hs2, 4, &["defs(simp(), tr.hrange)".into(), "simp(L)".into(), "simp(L)".into(), "simp(L)".into(), "simp(L)".into(), hk]);
                let st2 = self.set_home(st, a2, cn, 4, k);
                self.then(t, st2)
            }
            _ => Err(bad("no rule for the instruction")),
        }
    }

    /// a home map's text: its entries in their keys' order
    fn hs_text(&self, hsm: &BTreeMap<u128, (u128, Term)>) -> String {
        let mut t = "empty".to_string();
        for (c, (n, x)) in hsm {
            t = format!("fn_update({}, {}, pair({}, {}))", t, c, n, self.print(x));
        }
        t
    }

    /// a store of n bytes to the home c: the homes it leaves (apart from
    /// it), their map's text, and the `tr.hkeep` proof (`{HS}` the homes
    /// before) -- one `tr.hkeep_upd` per home left
    fn hkeep(&self, st: &St, c: u128, n: u128) -> (BTreeMap<u128, (u128, Term)>, String, String) {
        let mut kept = BTreeMap::new();
        let mut pf = format!("all_elim(tr.hkeep_empty, {{HS}}, {{{c}}}, {{{n}}})");
        for (&k, (nk, xk)) in &st.hsm {
            if k + nk <= c || c + n <= k {
                let f = self.hs_text(&kept);
                pf = format!(
                    "mp(tr.hkeep_upd, {{HS}}, {{{f}}}, {{{c}}}, {{{n}}}, {{{k}}}, {{{nk}}}, {{{}}}, {pf}, simp(L), simp(L), defs(simp(), tr.hdisj))",
                    self.print(xk)
                );
                kept.insert(k, (*nk, xk.clone()));
            }
        }
        let t = self.hs_text(&kept);
        (kept, t, pf)
    }

    /// after a write of n bytes x to the home c: the homes it left, and it
    fn set_home(&mut self, st: &St, a2: u128, c: u128, n: u128, x: Term) -> St {
        // (the rules' map after: the kept ones', then the stored home)
        let (mut kept, kt, _) = self.hkeep(st, c, n);
        let mut st2 = st.clone();
        st2.a = a2;
        st2.hst = format!("fn_update({}, {}, pair({}, {}))", kt, c, n, self.print(&x));
        kept.insert(c, (n, x));
        st2.hsm = kept;
        st2
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
    // (one argument), or fn_build(D, x0. mkprog(x1 x2. bind_rel(PROC, x1, KW, EXC, DIV))) (none)
    let ssym = *env.sym_by_name.get(&spec_name).ok_or_else(|| format!("no spec `{}`", spec_name))?;
    let SymKind::Defined { body: sbody, params: sparams } = env.syms[ssym as usize].kind.clone() else { return Err(format!("`{}` is not a definition", spec_name)) };
    // the callee (the calls' target): its code, loaded before the function's
    // own (the contract's code: both)
    let mut targets: BTreeSet<u128> = BTreeSet::new();
    for (&a, i) in &insns {
        if i.row == 120 {
            let off = nat(&i.fields).ok_or_else(|| format!("{:x}: the call's displacement", a))?;
            let a2 = (a + i.len) % P64;
            targets.insert((a2 + if off >= 1 << 31 { off + (P64 - (1 << 32)) } else { off }) % P64);
        }
    }
    if targets.len() > 1 {
        return Err("calls to several callees: not covered yet".into());
    }
    let callee = match targets.iter().next() {
        None => None,
        Some(&f) => {
            let suffix = format!(".at_{:x}", f);
            let (cname, t) = env.claims.iter().find(|(n, _)| n.ends_with(&suffix)).cloned().ok_or_else(|| format!("no decode fact of the callee at {:x}", f))?;
            let g0 = Gen0(&env);
            let cc = (|| {
                let t = &g0.app(t.clone(), "all")?;
                let t = &g0.app(t.clone(), "all")?;
                let i1 = g0.imp(t)?;
                let i2 = g0.imp(&i1.1)?;
                Some(g0.args(&i2.0, "abi.code_at")?[2].clone())
            })()
            .ok_or_else(|| format!("{}: not a decode fact", cname))?;
            Some((f, cc))
        }
    };
    let mut g = Gen {
        env: &mut env,
        names: Vec::new(),
        vals: Vec::new(),
        zs: Vec::new(),
        qs: Vec::new(),
        lets: Vec::new(),
        lemmas,
        insns,
        imuls: BTreeSet::new(),
        narrows: BTreeSet::new(),
        fields: BTreeSet::new(),
        rbytes: 4,
        scratch: BTreeSet::new(),
        base: String::new(),
        code: String::new(),
        prefix: prefix.clone(),
        kw: Term::bvar(0),
        fd: 0,
        fr: 0,
        w: Term::bvar(0),
        wn: "W".into(),
        hvu: "hvu".into(),
        vw: Term::bvar(0),
        n: 0,
        loops: Vec::new(),
        nval: 0,
        scoped_q: BTreeSet::new(),
        scoped_l: BTreeSet::new(),
        lf: "L".into(),
        rmaps: HashMap::new(),
        callees: Vec::new(),
        lbase: String::new(),
        lcode: String::new(),
    };
    let args_t = g.var("args");
    g.var("s");
    g.w = g.var("W");
    g.vw = g.w.clone();
    let q_t = g.var("q");
    g.base = g.print(&base_t);
    g.code = g.print(&code_t);
    // (the spec's parameters, the callees: G0, G1, ...)
    let mut sbody = sbody;
    let mut gnames = Vec::new();
    for (i, p) in sparams.iter().enumerate() {
        let gn = format!("G{}", i);
        let gv = g.var(&gn);
        sbody = sbody.subst_var(*p, &gv, &g.env.binders_fn());
        gnames.push(gn);
    }
    let spec_app = format!("{}({})", spec_name, gnames.join(", "));
    // (the contract's code: the program text, which holds the function's
    // and its callees' -- FN.in_text)
    let text_base = (|| -> Option<String> {
        let sym = *g.env.sym_by_name.get("text.code")?;
        let SymKind::Defined { .. } = &g.env.syms[sym as usize].kind else { return None };
        // (its base: the lowest function's, the first piece's address)
        g.env.claims.iter().find(|(n, _)| n == &format!("{}.in_text", fname)).and_then(|(_, t)| {
            let t = g.app(t, "all", 1)?;
            let t = g.app(&t[0], "all", 1)?;
            let (p, _) = Gen0(&*g.env).imp(&t[0])?;
            Some(g.print(&g.app(&p, "abi.loaded", 4)?[1]))
        })
    })()
    .ok_or_else(|| format!("no program text with {} (slc steps --text)", fname))?;
    g.lbase = text_base;
    g.lcode = "text.code".to_string();
    let callee_text = callee.as_ref().map(|(f, cc)| (*f, g.print(cc)));
    let parts = (|| -> Option<(u128, Term, Term, Term)> {
        let fb = g.app(&sbody, "fn_build", 2)?;
        let mp = g.app(&fb[1], "mkprog", 1)?;
        let (nargs, br) = match g.app(&mp[0], "or", 2) {
            Some(or) => {
                let guard = g.app(&or[0], "not", 1)?;
                let le = g.app(&guard[0], "ord_le", 2)?;
                let n = nat(&le[0])?;
                (1..=6).contains(&n).then_some(())?;
                (n, g.app(&or[1], "bind_rel", 5)?.to_vec())
            }
            None => (0, g.app(&mp[0], "bind_rel", 5)?.to_vec()),
        };
        matches!(br[1].node(), Node::BVar(1)).then_some(())?;
        // PROC(x0); KW(x3, x4, x2); the wrapper without x0
        let proc = g.lam(&br[0], &["x0", "x1", "x2"], &["x0"])?;
        let kw = g.lam(&br[2], &["x0", "x1", "x2", "x3", "x4"], &["x3", "x4", "x2"])?;
        let bs = g.env.syms[g.env.sym_by_name["bind_rel"] as usize].binders.clone();
        let rest: Vec<Term> = br[1..].iter().zip(&bs[1..]).map(|(x, &k)| g.remap(x, k, &|i| (i < 2).then_some(i))).collect::<Option<_>>()?;
        let mut wa = vec![q_t.clone()];
        wa.extend(rest);
        let wrap = g.mk("mkprog", vec![g.mk("bind_rel", wa)]);
        Some((nargs, proc, kw, wrap))
    })();
    let (nargs, proc, kw, wrap) = parts.ok_or_else(|| format!("`{}`: not a procedure's spec", spec_name))?;
    let guarded = nargs > 0;
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
    g.rbytes = result_bits(&g, &kw).unwrap_or(0) / 8;

    // the frame: `sub rsp, k` at the entry (or none); fd, the deepest byte
    // below the entry's rsp the function's stack accesses reach
    let k0 = (|| {
        let i = &g.insns[&entry];
        let x = (i.row == 60).then(|| g.pairs(&i.fields, 5)).flatten()?;
        let (t, r) = g.tag(&x[2])?;
        (nat(&x[0])? == 8 && nat(&x[1])? == 5 && t == 0 && nat(&r)? == 4).then_some(())?;
        nat(&x[4])
    })()
    .unwrap_or(0);
    fn rsp_disps(g: &Gen, t: &Term, out: &mut Vec<u128>) {
        if let Some(d) = g.rsp_mem(t).and_then(|d| nat(&d)) {
            out.push(d);
            return;
        }
        if let Node::App(_, a) = t.node() {
            for x in a.iter() {
                rsp_disps(g, x, out);
            }
        }
    }
    let mut fd = k0;
    for i in g.insns.values() {
        let mut ds = Vec::new();
        rsp_disps(&g, &i.fields, &mut ds);
        for d in ds {
            let c = (d + P64 - k0) % P64;
            if c >= P64 / 2 {
                fd = fd.max(P64 - c);
            }
        }
    }
    if fd > 65536 {
        return Err(format!("a frame of {} bytes: beyond tr.FMAX", fd));
    }
    g.fd = fd;

    // the entry: the arguments in their registers (64 bits each); the
    // prologue is instructions as any
    let q0raw = proc.instantiate_params(&[args_t.clone()], &g.env.binders_fn());
    let Node::Var(qv, _) = q_t.node() else { unreachable!() };
    let wrap_q0 = wrap.subst_var(*qv, &q0raw, &g.env.binders_fn());
    let q0 = g.canon(&q0raw);
    let i0 = g.new_q(q0);
    let argregs = [7u128, 6, 2, 1, 8, 9];
    let mut st0 = St {
        a: entry,
        fr: 0,
        regs: Vec::new(),
        rs: "empty".into(),
        ds: fd.to_string(),
        w: g.w.clone(),
        wn: "W".into(),
        hvu: "hvu".into(),
        hw: "hW".into(),
        hsm: BTreeMap::new(),
        hst: "empty".into(),
        lp: None,
        spec: Spec::Proc(i0),
        hyps: Vec::new(),
        z: None,
    };
    // (the registers' map, as a function of the arguments x0)
    let mut rs_maps = vec!["empty".to_string()];
    for i in 0..nargs {
        let r = argregs[i as usize];
        let v = g.mk("bits_of_int", vec![lit(64), g.mk("app", vec![args_t.clone(), lit(i)])]);
        st0 = g.set_reg(&st0, entry, r, 8, v);
        let prev = rs_maps.last().unwrap().clone();
        rs_maps.push(format!("fn_update({prev}, {r}, pair(8, bits_of_int(64, app(x0, {i}))))"));
    }
    let rs_lam = rs_maps.last().unwrap().clone();
    let at_args = |t: &str| t.replace("app(x0, ", "app(args, ");

    // the proof
    let pf = g.prove(st0)?;

    // the text
    let mut o = String::new();
    let after = if g.callees.is_empty() {
        "Checked after proofs/translate_effects.core\n// (its tr.callee_io: the spec's structure, by that file's lemmas).".to_string()
    } else {
        "A call: proofs/translate_call.core's\n// tr.call / tr.call1, the callee's contract a premise. Checked after proofs/translate_effects.core.".to_string()
    };
    o.push_str(&format!(
        "// {}'s C1 by translation (docs/overview.md, C1). Generated by\n//   slc translate {} {} {} -o OUT.core FILES (the spec's and the decode facts' files, the rules)\n// Each step: a rule of proofs/translate.core, proofs/translate_frame.core or\n// proofs/translate_store_loop.core with its instance -- a spec reduction, or an\n// instruction (its decode fact, build/leaf_steps.core; literal facts, simp(L))\n// -- then the next point. {}\n\n",
        fname, fname, spec_name, prefix, after
    ));
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
    // (the callee: its contract on the code with the function's, its spec
    // typed and keeping I/O and code -- premises)
    let (lb, lc) = (g.lbase.clone(), g.lcode.clone());
    let cn = g.callees.first().map(|c| c.2).unwrap_or(1);
    let cimp = if g.callees.first().is_some_and(|c| c.3) { "tr.implements_at_u" } else { "tr.implements_at" };
    let cprem = match &callee_text {
        Some((f, _)) => format!("{cimp}({f}, G0, {lb}, {lc}, statics) -> G0 in fn_space(abi.ARGS, powerset(univ(1))) -> tr.callee_io(G0, {cn}) -> "),
        None => String::new(),
    };
    let call = if callee_text.is_some() { "all G0. " } else { "" };
    if callee_text.is_some() && gnames.len() != 1 {
        return Err("a caller: one callee so far".into());
    }
    let (b, c) = (g.base.clone(), g.code.clone());
    let rs_args = at_args(&rs_lam);
    if guarded {
        o.push_str(&format!(
            "theorem {p}.body: all statics. {call}{cprem}all args v mem s. args in abi.ARGS -> v in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> ord_le({nargs}, seq_len(args)) ->\n  abi.loaded(app(s, \"vm\"), {lb}, {lc}, statics) -> abi.view(s, v, mem) in univ(1) ->\n  tr.pt(s, v, {b}, {c}, 0, {b}, empty, {fd}, {rs_args},\n    {}, abi.view(s, v, mem))\nproof\n",
            g.print(&wrap_q0),
        ));
    } else {
        o.push_str(&format!(
            "theorem {p}.body: all statics. {call}{cprem}all args v mem s. args in abi.ARGS -> v in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine ->\n  abi.loaded(app(s, \"vm\"), {lb}, {lc}, statics) -> abi.view(s, v, mem) in univ(1) ->\n  tr.pt(s, v, {b}, {c}, 0, {b}, empty, {fd}, empty,\n    {}, abi.view(s, v, mem))\nproof\n",
            g.print(&wrap_q0),
        ));
    }
    o.push_str("  fix statics\n");
    if let Some((f, _)) = &callee_text {
        o.push_str(&format!(
            "  fix G0\n  assume hcall0: {cimp}({f}, G0, {lb}, {lc}, statics)\n  assume htyp0: G0 in fn_space(abi.ARGS, powerset(univ(1)))\n  assume hio0: tr.callee_io(G0, {cn})\n"
        ));
    }
    o.push_str("  fix args\n  fix v\n  fix mem\n  fix s\n  assume hA: args in abi.ARGS\n  assume hvo: v in set_type(omega)\n  assume hmv: mem in x86_64_linux.Vm\n  assume hM: s in x86_64_linux.Machine\n");
    if guarded {
        o.push_str(&format!("  assume hg: ord_le({nargs}, seq_len(args))\n"));
    }
    o.push_str(&format!("  assume hl: abi.loaded(app(s, \"vm\"), {lb}, {lc}, statics)\n"));
    o.push_str("  assume hvu: abi.view(s, v, mem) in univ(1)\n");
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
    o.push_str("  let V := v\n  let W := abi.view(s, v, mem)\n");
    o.push_str("  // the world: a world\n  have hW: W in abi.World && W in univ(1) proof\n    have wt := apply(abi.world_typed, hM, hvo, hmv, hvu)\n    show by taut(wt, hvu)\n  qed\n");
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
    o.push_str("  // the spec's rest at each point\n");
    for (i, (n, t)) in g.qs.iter().enumerate() {
        if !g.scoped_q.contains(&i) {
            o.push_str(&format!("  let {} := {}\n", n, g.print(t)));
        }
    }
    o.push_str("  // the registers after each write; the wrapper after the result\n");
    for (i, (n, t)) in g.lets.iter().enumerate() {
        if !g.scoped_l.contains(&i) {
            o.push_str(&format!("  let {} := {}\n", n, t));
        }
    }
    o.push_str("  // the steps (each from the next point's claim)\n");
    for line in &pf.lines {
        o.push_str(&format!("  {}\n", line));
    }
    o.push_str(&format!("  show := {}\nqed\n\n", pf.expr));
    let ql = g.lambda(1, &proc);
    // (the code the contract holds: the program text, the function's piece of it)
    let fcode = g.code.strip_suffix("()").unwrap_or(&g.code);
    let fcode = fcode.strip_suffix(".code").unwrap_or(fcode).to_string();
    let hsub = format!(
        "  have hsub: all vm. abi.loaded(vm, {lb}, {lc}, statics) -> abi.code_at(vm, {b}, {c}) proof\n    fix vm\n    assume h: abi.loaded(vm, {lb}, {lc}, statics)\n    have l := mp(all_elim({fcode}.in_text, {{vm}}, {{statics}}), h)\n    show by taut(expand(l, abi.loaded))\n  qed\n"
    );
    let (cfix, cass, bodyc) = match &callee_text {
        Some((f, _)) => (
            "all G0. ".to_string(),
            format!("  fix G0\n  assume hcall0: {cimp}({f}, G0, {lb}, {lc}, statics)\n  assume htyp0: G0 in fn_space(abi.ARGS, powerset(univ(1)))\n  assume hio0: tr.callee_io(G0, {cn})\n"),
            format!("mp(all_elim({p}.body, {{statics}}, {{G0}}), hcall0, htyp0, hio0)"),
        ),
        None => (String::new(), String::new(), format!("all_elim({p}.body, {{statics}})")),
    };
    o.push_str(&format!("theorem {p}.implements: all statics. {cfix}{cprem}tr.implements_at({b}, {spec_app}, {lb}, {lc}, statics)\nproof\n  fix statics\n{cass}{hsub}"));
    if guarded {
        // (the arguments' registers at the entry: the map's entries one by one)
        let mut h = format!(
            "  have hregs: all args s. args in abi.ARGS -> s in x86_64_linux.Machine -> abi.entry_ok(s, args) -> ord_le({nargs}, seq_len(args)) -> tr.regs(s, {rs_args}) proof\n    fix args\n    fix s\n    assume hA hM he hg\n    have ln: seq_len(args) in omega by simp(hA)\n    have r0 := all_elim(tr.regs_empty, {{s}})\n"
        );
        for i in 0..nargs {
            let r = argregs[i as usize];
            let prev = at_args(&rs_maps[i as usize]);
            h.push_str(&format!(
                "    have a{i} := apply(tr.arg_reg, {{s}}, {{args}}, {{{i}}}, {{{r}}}, hM, he, simp(), (int_lt({i}, seq_len(args)) by arith(ln, expand(hg, ord_le))), simp(tr.argregs), simp())\n    have r{} := apply(tr.regs_add, {{s}}, {{{prev}}}, {{{r}}}, {{8}}, {{bits_of_int(64, app(args, {i}))}}, r{i}, simp(a{i}), simp(a{i}))\n",
                i + 1
            ));
        }
        h.push_str(&format!("    show := r{nargs}\n  qed\n"));
        o.push_str(&h);
        o.push_str(&format!(
            "  have m0 := mp(tr.entry_n[lb := {lb}, lc := {lc}, base := {b}, code := {c}, statics := statics, f := {b}, n := {nargs}, fd := {fd}, rs := x0. {rs_lam},\n    q := {ql}, kw := {kwl}],\n    simp(), hsub, hregs, {bodyc})\n"
        ));
    } else {
        if callee_text.is_some() {
            return Err("a caller without arguments: not covered yet".into());
        }
        let q0p = g.print(&q0raw);
        o.push_str(&format!("  have m0 := mp(tr.entry0[lb := {lb}, lc := {lc}, base := {b}, code := {c}, statics := statics, f := {b}, fd := {fd}, q := {q0p}, kw := {kwl}],\n    simp(), hsub, {bodyc})\n"));
    }
    o.push_str(&format!(
        "  have m: all args objs mem s o. args in abi.ARGS -> objs in set_type(omega) -> mem in x86_64_linux.Vm -> s in x86_64_linux.Machine -> s in univ(1) ->\n      abi.loaded(app(s, \"vm\"), {lb}, {lc}, statics) -> app(s, \"rip\") = {b} -> abi.entry_ok(s, args) -> tr.objs_ok(s, objs) -> abi.view_ok(s, objs, mem) -> tr.run_d(s, s, o) ->\n      tr.matches_t({spec_app}, args, objs, mem, s, o) by defs(m0, {spec_name})\n  show by defs(m, tr.implements_at)\nqed\n\n"
    ));
    // (the ABI's contract, from the bridge's)
    let imp = match &callee_text {
        None => format!("all_elim({p}.implements, {{statics}})"),
        Some(_) => format!("mp(all_elim({p}.implements, {{statics}}, {{G0}}), hcall0, htyp0, hio0)"),
    };
    o.push_str(&format!(
        "theorem {p}.implements_abi: all statics. {cfix}{cprem}abi.implements2_at(single(empty), {b}, {spec_app}, {lb}, {lc}, statics)\nproof\n  fix statics\n{cass}  show := apply(tr.implements_abi, {imp})\nqed\n"
    ));
    // (as a callee: tr.callee_io from the spec's structure -- a caller's
    // from its callee's)
    {
        let known: HashSet<String> = g.env.claims.iter().map(|(n, _)| n.clone()).chain(g.lemmas.keys().cloned()).collect();
        match crate::effects::Eff::new(&mut *g.env, &prefix, known).callee_io(ssym, cn) {
            Ok(t) => {
                o.push('\n');
                o.push_str(&t);
            }
            Err(e) => o.push_str(&format!("\n// no tr.callee_io yet: {}\n", e)),
        }
    }
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

/// a map's text `fn_update(f, k, v)`: f, k, v
fn split_update(t: &str) -> Option<[String; 3]> {
    let inner = t.strip_prefix("fn_update(")?.strip_suffix(')')?;
    let (mut depth, mut parts, mut last) = (0i32, Vec::new(), 0usize);
    for (k, ch) in inner.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(inner[last..k].trim().to_string());
                last = k + 1;
            }
            _ => {}
        }
    }
    parts.push(inner[last..].trim().to_string());
    <[String; 3]>::try_from(parts).ok()
}

/// `c in dom(hs)` for the homes' map text hs, by its updates: c's own
/// (`tr.dom_upd`) under the later ones (`tr.dom_keep`)
fn hdom_pf(hs: &str, c: &str) -> Option<String> {
    let [h, k, x] = split_update(hs)?;
    if k == c {
        return Some(format!("all_elim(tr.dom_upd, {{{h}}}, {{{k}}}, {{{x}}})"));
    }
    let inner = hdom_pf(&h, c)?;
    Some(format!("mp(all_elim(tr.dom_keep, {{{h}}}, {{{c}}}, {{{k}}}, {{{x}}}), {inner}, simp())"))
}

/// the homes two updates or more below the top of the map hs: their `in
/// dom` facts (simp(L) shows the others)
fn deep_hdoms(hs: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut cur = hs.to_string();
    while let Some([h, k, _]) = split_update(&cur) {
        keys.push(k);
        cur = h;
    }
    keys.iter().skip(2).filter_map(|k| hdom_pf(hs, k)).collect()
}
