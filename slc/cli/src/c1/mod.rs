//! C1 by the engine (docs/overview.md, C1): a function's machine code
//! implements its readable GIMPLE, proven by walking its decode facts
//! (`FN.at_ADDR`, from `slc steps`) alongside the spec's procedure
//! (`SPEC_fun`), one rule of proofs/translate*.core per step, the rules
//! applied through the kernel (`sl_proof::api`). Not trusted: the theorems
//! it returns are kernel sequents. No proof text is made.
//!
//! The entry is the function's first instruction, its arguments in their
//! registers (tr.entry_n); the prologue (`sub rsp, k`, the arguments'
//! stores) is instructions as any.
//! - the spec's rest is reduced at its head, by one lemma instance per step:
//!   a definition's body, a let, a choice (a placeholder witness, which no
//!   machine value can match), an operation (split on its definedness:
//!   undefined, the spec raises, which closes the case), a disjunct by its
//!   guard (a literal fact or the machine's branch condition), a block's
//!   end, a projection of a constructed outcome;
//! - each instruction is the instance of the rule for its pattern; a
//!   conditional branch splits the proof on its condition.
//! Nothing is searched: an instruction without a rule, a spec head without
//! a reduction, a machine value the spec does not have, stop it with an
//! error naming the address.

mod eff;
mod insn;
mod join;
mod proof;
pub mod rec;
mod spec;
mod top;

pub use top::c1;

use rec::{Slots, R};
use sl_kernel::ext::seq::Seq;
use sl_kernel::syntax::{self, Printer};
use sl_kernel::{Env, Nat, Node, SymKind, Term, VarId};
use std::collections::{BTreeMap, BTreeSet};

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
/// the wrapper's rest, with the value returned.
#[derive(Clone)]
enum Spec {
    Proc(usize),
    Ret(Term, Term),
}

/// A path's state at an address.
#[derive(Clone)]
struct St {
    a: u128,
    /// the frame's size: rsp is the entry's minus fr (`tr.inv`)
    fr: u128,
    /// the registers written: register, bytes, value; their map
    regs: Vec<(u128, u128, Term)>,
    rs: Term,
    /// the frame's depth (`tr.pt`'s fd)
    ds: Term,
    /// the spec's world, its facts: a set (`hvu`), a world and a set (`hw`)
    w: Term,
    hvu: Seq,
    hw: Seq,
    /// the homes: offset -> (bytes, value), and their map
    hsm: BTreeMap<u128, (u128, Term)>,
    hst: Term,
    /// the loop whose body this is (an index into `loops`)
    lp: Option<usize>,
    spec: Spec,
    /// the facts in scope: a branch's condition (or its negation), a
    /// defined operation's condition (assumed)
    hyps: Vec<(Term, Seq)>,
    /// the path's assumed facts: a call's results in bits(64) (for a
    /// result's store, which takes it whole)
    facts: Vec<Seq>,
    /// the literal facts `simp(L)` also has here: a join's variables words
    lfx: Vec<Seq>,
    /// the branches the path took (innermost last), for joins
    splits: Vec<join::Split>,
    /// a join's claim being proven at this address: not joined again
    no_join: Option<u128>,
    /// in a zero-initialization (`tr.ptz`): the zero xmm register, the
    /// address of the bytes still to be stored (a base, an offset), their
    /// count
    z: Option<(u128, Term, u128, u128)>,
}

/// A reduction of the spec's rest.
enum Red {
    /// to the rest `.0`, by the proof `.1` of `all o. runs(q2, W, o) ->
    /// runs(q, W, o)`
    Q(usize, R),
    /// the procedure's result
    Ret(Term),
    /// an operation defined under `cond`: ok to `ok.0` by `ok.1` (the slot
    /// `HC` the condition's proof), raising to `ub.0` by `ub.1` (`HN` its
    /// negation's)
    Split { cond: Term, ok: (usize, R), ub: (usize, R) },
    /// a store defined under `cond` (the rest kept: the machine's store
    /// makes it), raising as `Split`'s
    Guard { cond: Term, ub: (usize, R) },
    /// a call of `g` (the machine's `call` makes it): the block's
    /// continuation, handlers and rest (`one`: call1, the result's rax only)
    Call { g: Term, args: Vec<Term>, list: Term, one: bool, a: Term, xx: Term, dd: Term, k: Term },
}

/// A store of the spec: st8 / st16 / st32 / st64 / st_bytes (or a helper
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
    /// its raise when undefined (the slot `HN`)
    ub: rec::RA,
    /// st_bytes of zeros: its list (the stored value 0, n its length)
    data: Option<Term>,
}

/// One step towards a disjunct whose guard holds.
enum Pick {
    L,
    R,
    And(Term, rec::RA),
}

struct Gen<'e> {
    env: &'e mut Env,
    api: Option<sl_proof::api::Api>,
    /// the placeholders by name (for terms parsed): values `T`, choices `Z`,
    /// worlds, the fixed variables
    names: Vec<(String, VarId)>,
    /// the named values: their definitions (`T`, worlds, `Z`, `V`, `W`)
    vals: Vec<(VarId, Term)>,
    /// (their expansions; the values' names by their expansions, for canon)
    vexp: std::collections::HashMap<VarId, Term>,
    val_of: std::collections::HashMap<Term, VarId>,
    zs: Vec<VarId>,
    qs: Vec<Term>,
    insns: BTreeMap<u128, Insn>,
    imuls: BTreeSet<u128>,
    /// the per-immediate facts the rules take: a field's shift and mask
    fields: BTreeSet<(u128, u128, u128)>,
    /// their proofs, once made
    facts_made: Vec<(String, Seq)>,
    /// the result's bytes (the wrapper's gimple.result width)
    rbytes: u128,
    scratch: BTreeSet<u128>,
    base: Term,
    code: Term,
    prefix: String,
    kw: Term,
    /// the wrapper around the procedure's rest q: `WRAP(q)` with q as
    /// bound variable 0
    wrap: Term,
    /// the function's frame depth (`tr.frame`): its stack accesses reach
    /// fd bytes below the entry's rsp
    fd: u128,
    /// the current point's frame size, world, its `in univ(1)` fact
    fr: u128,
    w: Term,
    hvu: Option<Seq>,
    /// the spec's view at the entry (`W`): the state of its raises
    vw: Term,
    /// the fixed s, V (the entry's machine, its view's objects)
    s: Term,
    v: Term,
    /// the facts the entry provides: `W in abi.World && W in univ(1)`, `W in
    /// univ(1)`, the program loaded (`hl`), the callees' premises (`hcall`,
    /// `htyp`, `hio` by the spec's parameter)
    hw0: Option<Seq>,
    hvu0: Option<Seq>,
    hl: Option<Seq>,
    hcall: Vec<Option<Seq>>,
    htyp: Vec<Option<Seq>>,
    hio: Vec<Option<Seq>>,
    /// each spec parameter's call: its address, number of arguments,
    /// whether it is entered unaligned (its premises assumed at the first
    /// call), and the premises' statements
    cinfo: Vec<Option<(u128, usize, bool, [Term; 3])>>,
    /// the program's statics, the spec's parameters
    statics_t: Term,
    gs: Vec<Term>,
    n: usize,
    /// the loops met: their heads and claims
    loops: Vec<Loop>,
    nval: usize,
    /// the literal facts for simp (`L`, a loop step's counter, the maps'
    /// deep `in dom` facts)
    lf: Vec<Seq>,
    lf0: Option<Seq>,
    /// the calls met: the callee (a spec parameter), its address, the
    /// call's number of arguments, whether a call enters it with the stack
    /// not aligned (its contract then for any entry: tr.implements_at_u)
    callees: Vec<(Term, u128, usize, bool)>,
    /// the program text's base and code (every contract's)
    lbase: Term,
    lcode: Term,
    /// steps made (for the summary)
    steps: usize,
    /// the join points' claims, the paths recorded there; the code's
    /// predecessor counts
    joins: Vec<join::Join>,
    arrivals: Vec<join::Arrival>,
    preds: Option<BTreeMap<u128, usize>>,
    /// the entry's assumptions (in scope at every point)
    ambient: Vec<Term>,
}

/// A loop of the spec met at a machine address (its head): the claim there,
/// for every world and local with the invariant, by induction on the variant
#[derive(Clone)]
struct Loop {
    head: u128,
    /// the induction hypothesis, the bound K of the counting loop, the home
    /// d of its counter
    ih: Seq,
    k: u128,
    d: u128,
    /// the rest at the head, the counter abstracted (a term of the counter's
    /// variable `li`)
    qh: Term,
    li: Term,
    /// in the step: the counter's facts (tr.count_inv expanded), its
    /// invariant
    ci: Seq,
    cc: Seq,
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

    /// `name(args)`: a symbol's application, or an abbreviation's body
    fn mk(&self, name: &str, args: Vec<Term>) -> Term {
        match self.env.sym_by_name.get(name) {
            Some(s) => Term::app(*s, args),
            None => {
                let (k, body) = self.env.abbrevs.get(name).unwrap_or_else(|| panic!("no symbol or abbreviation `{}`", name));
                assert_eq!(*k, args.len(), "`{}`: its arguments", name);
                body.instantiate_params(&args, &self.env.binders_fn())
            }
        }
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

    /// a new fixed variable (or placeholder) named
    fn var(&mut self, name: &str) -> Term {
        let v = self.env.new_var(name, 0);
        self.names.push((name.to_string(), v));
        Term::var(v, vec![])
    }

    fn var_id(t: &Term) -> VarId {
        match t.node() {
            Node::Var(v, _) => *v,
            _ => unreachable!("not a variable"),
        }
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

    /// names the value `v` the term `t` (its expansion kept: values only
    /// name earlier ones, so it stays)
    fn push_val(&mut self, v: VarId, t: Term) {
        let e = self.expand(&t);
        // (canon's names: not a choice's placeholder -- its literal stands
        // for itself; the first name of a value)
        if self.is_value(v) && !self.zs.contains(&v) {
            self.val_of.entry(e.clone()).or_insert(v);
        }
        self.vexp.insert(v, e);
        self.vals.push((v, t));
    }

    /// `t` with its names expanded (to the kernel's terms)
    fn expand(&self, t: &Term) -> Term {
        match t.node() {
            Node::Var(v, a) if a.is_empty() => match self.vexp.get(v) {
                Some(e) => e.clone(),
                None => t.clone(),
            },
            Node::App(_, a) if !a.is_empty() => t.with_args(a.iter().map(|x| self.expand(x)).collect()),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.expand(x)).collect()),
            _ => t.clone(),
        }
    }

    /// the fact in scope `t` (the same term, or the same expanded: a join's
    /// premise holds raw what the code names later)
    fn hyp_find<'h>(&self, hyps: &'h [(Term, Seq)], t: &Term) -> Option<&'h (Term, Seq)> {
        if let Some(h) = hyps.iter().find(|h| h.0 == *t) {
            return Some(h);
        }
        let te = self.expand(t);
        hyps.iter().find(|h| self.expand(&h.0) == te)
    }

    /// `t` with each subterm that is a named value replaced by its name
    /// (compared expanded: a value named before its parts were)
    fn canon(&self, t: &Term) -> Term {
        self.canon_in(&self.expand(t))
    }

    /// a value's name (`T`, a world): not the fixed V and W
    fn is_value(&self, v: VarId) -> bool {
        !matches!(self.env.vars[v as usize].name.as_str(), "V" | "W")
    }

    fn canon_in(&self, t: &Term) -> Term {
        if let Some(v) = self.val_of.get(t) {
            return Term::var(*v, vec![]);
        }
        match t.node() {
            Node::App(_, a) if !a.is_empty() => t.with_args(a.iter().map(|x| self.canon_in(x)).collect()),
            _ => t.clone(),
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
        self.push_val(v, t);
        Term::var(v, vec![])
    }

    /// A commutative operation's value: the spec's name for it with its
    /// operands in the other order, if it has one (the rule's premise `r =
    /// op(..)` by simp), else a name as `value`
    fn value_comm(&mut self, t: &Term) -> Term {
        if let Node::App(f, a) = t.node() {
            let comm = ["bits_add", "bits_mul", "bits_and", "bits_or", "bits_xor"].contains(&self.env.syms[*f as usize].name.as_str());
            if comm && a.len() == 3 {
                let sw = self.canon(&t.with_args(vec![a[0].clone(), a[2].clone(), a[1].clone()]));
                if let Node::Var(v, _) = sw.node() {
                    if self.vals.iter().any(|x| x.0 == *v) {
                        return sw;
                    }
                }
            }
        }
        self.value(t)
    }

    /// the premise `r = op(n, a, b)` for value_comm's r: simp(L) for the
    /// spec's value itself; with its operands swapped, the commutation
    /// (x86.and_comm, x86.mul_comm; simp's arithmetic for `bits_add`)
    fn comm_premise(&self, r: &Term, op: &Term) -> rec::RA {
        if self.expand(r) != self.expand(op) {
            if let Node::App(f, a) = op.node() {
                let lemma = match self.env.syms[*f as usize].name.as_str() {
                    "bits_and" => Some("x86.and_comm"),
                    "bits_mul" => Some("x86.mul_comm"),
                    _ => None,
                };
                if let Some(l) = lemma {
                    return rec::p(R::Inst(l.into(), vec![("n", a[0].clone()), ("a", a[2].clone()), ("b", a[1].clone())]));
                }
            }
        }
        rec::simp_l()
    }

    /// a literal's value (a constant defined as one, a sum of them)
    fn eval_lit(&self, t: &Term) -> Option<u128> {
        if let Some(n) = nat(t) {
            return Some(n);
        }
        if let Node::Var(v, _) = t.node() {
            return self.vals.iter().rev().find(|x| x.0 == *v).and_then(|x| self.eval_lit(&x.1));
        }
        if let Some(a) = self.app(t, "int_add", 2) {
            return Some(self.eval_lit(&a[0])? + self.eval_lit(&a[1])?);
        }
        // (a negative constant as GIMPLE writes it: 2^n - k)
        if let Some(a) = self.app(t, "bits_neg", 2) {
            let (n, k) = (nat(&a[0])?, self.eval_lit(&a[1])?);
            return (n < 128).then(|| ((1u128 << n) - k % (1u128 << n)) % (1u128 << n));
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
        self.qs.push(t);
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

    /// `fn_update(m, k, pair(n, v))`
    fn upd(&self, m: &Term, k: u128, n: u128, v: &Term) -> Term {
        self.mk("fn_update", vec![m.clone(), lit(k), self.mk("pair", vec![lit(n), v.clone()])])
    }

    /// the state after writing v (n bytes) to r, at a
    fn set_reg(&mut self, st: &St, a: u128, r: u128, n: u128, v: Term) -> St {
        let mut st2 = st.clone();
        st2.rs = self.upd(&st.rs, r, n, &v);
        st2.regs.push((r, n, v));
        st2.a = a;
        st2
    }

    /// the point claim's spec argument: `WRAP(q)`, or the wrapper after the
    /// result
    fn p(&self, spec: &Spec) -> Term {
        match spec {
            Spec::Proc(i) => self.wrap_of(&self.qs[*i]),
            Spec::Ret(_, pr) => pr.clone(),
        }
    }

    fn wrap_of(&self, q: &Term) -> Term {
        self.wrap.instantiate_params(std::slice::from_ref(q), &self.env.binders_fn())
    }

    /// `KW(x0, x1, x2)` as a value of 3 parameters: the wrapper's
    /// continuation
    fn kw3(&self) -> Term {
        self.kw.clone()
    }

    /// the point claim `tr.pt(s, V, base, code, fr, a, hs, ds, rs, p, w)`
    fn pt(&self, st: &St, a: u128) -> Term {
        self.mk(
            "tr.pt",
            vec![self.s.clone(), self.v.clone(), self.base.clone(), self.code.clone(), lit(st.fr), lit(a), st.hst.clone(), st.ds.clone(), st.rs.clone(), self.p(&st.spec), st.w.clone()],
        )
    }

    /// a term from text (terms only), the placeholders by their names
    fn parse(&mut self, text: &str) -> Result<Term, String> {
        let names = self.names.clone();
        syntax::parse_term(self.env, text, &names).map_err(|e| format!("{}: {}", text, e.0))
    }

    /// (C1_TRACE: a message)
    fn trace(&self, m: impl FnOnce() -> String) {
        if std::env::var("C1_TRACE").is_ok() {
            static T0: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
            eprintln!("c1 {} [{:.2}]", m(), T0.get_or_init(std::time::Instant::now).elapsed().as_secs_f64());
        }
    }

    /// a step's evaluation (counted)
    fn run(&mut self, r: &R, slots: Slots) -> Result<Seq, String> {
        self.steps += 1;
        // (C1_TRACE: each step's rule, and its time)
        if std::env::var("C1_TRACE").is_ok() {
            let t0 = std::time::Instant::now();
            let res = self.ev(r, slots);
            eprintln!("c1 step {} {} {:.3}s{}", self.steps, self.head_name(r), t0.elapsed().as_secs_f64(), if res.is_err() { " (failed)" } else { "" });
            return res;
        }
        self.ev(r, slots)
    }
}

/// `fn_update(f, k, v)`: f, k, v
fn upd_parts(g: &Gen, t: &Term) -> Option<(Term, Term, Term)> {
    let a = g.app(t, "fn_update", 3)?;
    Some((a[0].clone(), a[1].clone(), a[2].clone()))
}

/// The proof checker with the C1 engine: proofs by `sl_proof`, `c1` lines
/// by `c1`.
pub struct Checker;

impl syntax::Prover for Checker {
    fn prove(&mut self, env: &mut Env, req: &syntax::ProofRequest) -> sl_kernel::KResult<Seq> {
        sl_proof::ScriptProver.prove(env, req)
    }

    fn c1(&mut self, env: &mut Env, fname: &str, spec: &str, prefix: &str) -> sl_kernel::KResult<Vec<(String, Seq)>> {
        c1(env, fname, spec, prefix).map_err(sl_kernel::KernelError)
    }
}
