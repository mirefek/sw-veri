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

mod cfg;
mod eff;
mod gref;
mod insn;
mod join;
mod nf;
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

/// the callee-saved registers (tr.cs_reg): rbx, rbp, r12 - r15
const CS_REGS: [u128; 6] = [3, 5, 12, 13, 14, 15];

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
    spec: Spec,
    /// the facts in scope: a branch's condition (or its negation), a
    /// defined operation's condition (assumed)
    hyps: Vec<(Term, Seq)>,
    /// the facts that are the code's branch conditions (indices into hyps),
    /// and those of them that decided a spec's `if` already: each decides
    /// one (at -O0 each `if` has its own test; a later `if` on the same
    /// condition waits for its own, as every path does)
    bconds: Vec<usize>,
    spent: Vec<usize>,
    /// the path's assumed facts: a call's results in bits(64) (for a
    /// result's store, which takes it whole)
    facts: Vec<Seq>,
    /// the literal facts `simp(L)` also has here: a join's variables words
    lfx: Vec<Seq>,
    /// the branches the path took (innermost last), for joins
    splits: Vec<join::Split>,
    /// a join's claim being proven at this address: not joined again
    no_join: Option<u128>,
    /// a block's lemma being proven from this address: no block again
    no_block: Option<u128>,
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
    /// (`stk`: call1_s, a callee with stack arguments)
    Call { g: Term, args: Vec<Term>, list: Term, one: bool, stk: bool, a: Term, xx: Term, dd: Term, k: Term },
    /// a system call (gimple.sys_call1, sys_call3, sys_call6; the machine's `syscall`
    /// makes it): its number and arguments, the block's continuation,
    /// handlers and rest
    Sys { n: Term, args: Vec<Term>, a: Term, xx: Term, dd: Term, k: Term },
    /// a loop's iteration ended by the body leaving with `e` (`tr.lcont`):
    /// the rest `k` in the wrapper `kw`
    Exit { e: Term, k: Term, kw: Term },
}

/// The CFG's walk under its loop rule (`tr.cfg_lv`, cfg.rs): its head, the
/// homes there as a function of the locals, the walk's state outside it
/// (the breakpoints, the wrapper) to restore at its exit
#[derive(Clone)]
struct LoopG {
    head: u128,
    hs: Term,
    bkp: Term,
    wrap: Term,
    kw: Term,
    /// the iteration's world and locals in the universe
    hu: Seq,
    /// the frame at the head, the registers there (tr.cs_sub's rc)
    fd: Term,
    rc: Vec<(u128, u128, Term)>,
    /// the locals' invariant, and its assumption in the iteration
    yt: Term,
    hy: Seq,
}

pub(super) use sl_kernel::prof;

/// The flags a compare sets (proofs/translate_flags.core): of `cmp a, b`
/// at a width (x86i.subf), of a test's result (x86i.logf)
enum Flags {
    Sub(u128, Term, Term),
    Log(u128, Term),
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
    /// a compare-and-swap (gimple.cas32): its operands t, s; its result
    /// (the old dword)
    cas: Option<(Term, Term, Term)>,
    /// a bitfield (gimple.stbf): its size, position, width, field
    bf: Option<(Term, Term, Term, Term)>,
}

/// One step towards a disjunct whose guard holds.
enum Pick {
    L,
    R,
    And(Term, rec::RA),
}

#[derive(Clone)]
struct SArgs {
    stk: Term,
    hsa: Seq,
    hso: Seq,
    hstk: Seq,
    args: Vec<(Term, Seq, Seq)>,
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
    /// (memo tables: a term's expansion -- for good, a value's name being
    /// new to the terms before it; a term's canonical form -- until a value
    /// is named)
    exp_memo: std::cell::RefCell<std::collections::HashMap<Term, Term>>,
    canon_memo: std::cell::RefCell<std::collections::HashMap<Term, Term>>,
    /// (the subterms searched for a redex -- at a depth --, an equation of
    /// a term with itself, a whole field: none there, for good)
    no_redex: std::cell::RefCell<std::collections::HashSet<(Term, u32)>>,
    no_refl: std::cell::RefCell<std::collections::HashSet<(Term, u32)>>,
    no_field: std::cell::RefCell<std::collections::HashSet<Term>>,
    /// (the normal forms made, nf.rs: for good -- a name's meaning is fixed)
    nf_memo: std::collections::HashMap<Term, (Term, Option<Seq>)>,
    /// (N seeing through bitwise operations' names too: a low byte's
    /// comparison only, `eq_nf_bits` -- its normal forms memoized apart)
    nf_bits: bool,
    nf_bits_memo: std::collections::HashMap<Term, (Term, Option<Seq>)>,
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
    /// (its `in abi.World && in univ(1)` fact)
    hww: Option<Seq>,
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
    /// the entry's machine typed, its arguments (for the entry's
    /// condition); the ABI's entry assumed (`abi.entry_ok(s, args)`) and
    /// the alignment from it (`tr.sal16(s)`) once an aligned call or a
    /// system call needs it -- else the claim is for any alignment
    ent_m: Option<(Seq, Term)>,
    ent_al: Option<(Term, Seq)>,
    /// a function with stack arguments (beyond the six in registers): the
    /// arguments' list stk, `abi.stack_args(s, stk)`, `tr.sargs_off(s, v,
    /// seq_len(stk))`, `stk in list_type(bits(64))` and by argument j its
    /// facts `int_lt(j, seq_len(stk))`, `x = bits_of_int(64, stk[j])` (x
    /// the spec's argument)
    sargs: Option<SArgs>,
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
    nval: usize,
    /// the walk's points, by address (the resource guard's report), and
    /// the function's name
    visits: BTreeMap<u128, usize>,
    fname: String,
    /// the literal facts for simp (`L`, a loop step's counter, the maps'
    /// deep `in dom` facts)
    lf: Vec<Seq>,
    lf0: Option<Seq>,
    /// the hints (`c1 .. using L, ..`): N's equations beyond its own
    /// (nf.rs), facts `all xs. H.. -> l = r`, l's instances rewritten to
    /// r's (the premises closed facts, by evaluation)
    hints: Vec<Seq>,
    /// the calls met: the callee (a spec parameter), its address, the
    /// call's number of arguments, whether a call enters it with the stack
    /// not aligned (its contract then for any entry: tr.implements_at_u)
    callees: Vec<(Term, u128, usize, bool)>,
    /// the program text's base and code (every contract's)
    lbase: Term,
    lcode: Term,
    /// steps made (for the summary)
    steps: usize,
    /// the universe facts of the walk's own variables set aside (a loop's
    /// locals, in its exit's walk; a join claim's)
    hus: Vec<Seq>,
    /// the variables made before the walk (the function's fixed ones)
    vmark0: usize,
    /// the locals' homes (scripts/locmap.py, the -O0 build's DWARF): the
    /// local's position in the locals, its home's key, the addresses
    /// where it lives there
    locmap: Vec<(usize, u128, u128, u128)>,
    /// the facts the last reduction's guard was decided by; the point's
    /// spent branch conditions (St::spent)
    picked: std::cell::RefCell<Vec<Term>>,
    spent_now: std::cell::RefCell<Vec<Term>>,
    /// the entry's assumptions (in scope at every point)
    ambient: Vec<Term>,
    /// the claim's breakpoints (`tr.sim`'s bkp, a predicate of a machine
    /// state) and their arrival condition (bka, of a state, a program and a
    /// world): none (`false`) but in a loop's body walk -- every rule's
    /// instance takes them
    bkp: Term,
    bka: Term,
    /// the loop whose iteration is being walked (its head the breakpoint)
    lpg: Option<LoopG>,
    /// the readable CFG's guide (cfg.rs): each block's live locals, the
    /// locals' widths; the body's start; the CFG walk going on
    cfg_meta: Option<(Vec<(u128, u128)>, Vec<u64>)>,
    cfg_start: u128,
    cfg: Option<cfg::Cfg>,
    /// the CFG ⊑ structured walk's points (gref.rs)
    gref: Option<gref::GRef>,
    /// the reducer's lets as written, not in N (two translations of the
    /// same statements compared: `refines`)
    raw_lets: bool,
    /// the refined procedures' parameters (`refines`): in univ(1) by
    /// hypothesis -- a premise of the procedures' refinement, discharged at
    /// the wrapper's arguments (words)
    params: Vec<Term>,
    /// callees' refinements found (CFG layer's, structured layer's)
    grefs: std::collections::HashMap<(String, String), Seq>,
    /// the refinement walk's choices in scope, with their domains' facts
    /// (`x in S`, assumed): a loop's start state in univ(1)
    gtyped: Vec<(Term, Seq)>,
}

/// the seconds since the first trace line
fn trace_t0() -> f64 {
    static T0: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    T0.get_or_init(std::time::Instant::now).elapsed().as_secs_f64()
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
        // (a part with no bound variable from outside it as it is; each
        // shared part once)
        type M = std::collections::HashMap<(Term, u32), Option<Term>>;
        fn go(g: &Gen, t: &Term, depth: u32, f: &dyn Fn(u32) -> Option<u32>, memo: &mut M) -> Option<Term> {
            if g.env.loose_depth_m(t) <= depth {
                return Some(t.clone());
            }
            let compound = matches!(t.node(), Node::App(_, a) | Node::Var(_, a) if !a.is_empty());
            if compound {
                if let Some(x) = memo.get(&(t.clone(), depth)) {
                    return x.clone();
                }
            }
            let out = (|| {
                Some(match t.node() {
                    Node::BVar(i) if *i >= depth => Term::bvar(f(i - depth)? + depth),
                    Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
                    Node::Var(_, a) => t.with_args(a.iter().map(|x| go(g, x, depth, f, memo)).collect::<Option<_>>()?),
                    Node::App(s, a) => {
                        let bs = &g.env.syms[*s as usize].binders;
                        t.with_args(a.iter().zip(bs).map(|(x, &k)| go(g, x, depth + k, f, memo)).collect::<Option<_>>()?)
                    }
                })
            })();
            if compound {
                memo.insert((t.clone(), depth), out.clone());
            }
            out
        }
        go(self, t, depth, f, &mut M::new())
    }

    /// `t` under the binders `ctx` (outermost first) as a value of the
    /// parameters `params`; None if it uses a binder that is not one
    fn lam(&self, t: &Term, ctx: &[&str], params: &[&str]) -> Option<Term> {
        let _p = prof::g("lam");
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
        self.canon_memo.borrow_mut().clear();
    }

    /// A world after a store, named v (t its definition, of the world w
    /// before): its kernel term `letin(W, x. body)`, the world before bound
    /// once -- not copied into the new one, nor into the stored value that
    /// read it (a run of stores would grow its term 4-fold per store); and
    /// `letin(W, x. body) = body(W)` (`letin_eq`), the equation from the
    /// world as the lemmas state it (substituted) to it -- None if no let
    /// is needed (W an atom)
    fn push_world(&mut self, v: VarId, t: Term, w: &Term) -> Option<R> {
        let ew = self.expand(w);
        if !matches!(ew.node(), Node::App(_, a) | Node::Var(_, a) if !a.is_empty()) || self.env.loose_depth_m(&ew) > 0 {
            self.push_val(v, t);
            return None;
        }
        let e2 = self.expand(&t);
        let body = self.abstract_sub(&e2, &ew);
        // (named as the world before, in messages and for `zeta`)
        let e = self.mk("letin", vec![ew.clone(), body.clone()]);
        let e = match w.node() {
            Node::Var(x, a) if a.is_empty() => e.with_binder_name(Some(self.env.var(*x).name.into())),
            _ => e,
        };
        if self.is_value(v) && !self.zs.contains(&v) {
            self.val_of.entry(e.clone()).or_insert(v);
        }
        self.vexp.insert(v, e);
        self.vals.push((v, t));
        self.canon_memo.borrow_mut().clear();
        Some(R::Inst("letin_eq".into(), vec![("a", ew), ("f", body)]))
    }

    /// the closed term t with each occurrence of the closed term `x` a
    /// variable bound at t's top (the body of a binder of one): its shared
    /// parts visited once
    fn abstract_sub(&self, t: &Term, x: &Term) -> Term {
        fn go(g: &Gen, t: &Term, x: &Term, d: u32, memo: &mut std::collections::HashMap<(usize, u32), Term>) -> Term {
            if t == x {
                return Term::bvar(d);
            }
            let key = (t.node() as *const Node as usize, d);
            if let Some(r) = memo.get(&key) {
                return r.clone();
            }
            let r = match t.node() {
                Node::App(s, a) if !a.is_empty() => t.with_args(a.iter().enumerate().map(|(i, y)| go(g, y, x, d + g.env.binders_fn()(*s, i), memo)).collect()),
                Node::Var(_, a) if !a.is_empty() => t.with_args(a.iter().map(|y| go(g, y, x, d, memo)).collect()),
                _ => t.clone(),
            };
            memo.insert(key, r.clone());
            r
        }
        go(self, t, x, 0, &mut std::collections::HashMap::new())
    }

    /// the fact f about the world as the lemmas state it (`e2`, the
    /// substituted form) as one about its let form, by `eq_subst` and the
    /// equation `eq` (`letin(..) = e2`)
    fn world_conv(&mut self, f: Seq, eq: &R) -> Result<Seq, String> {
        let eqs = self.run(eq, &[])?;
        let x = self.app(eqs.concl(), "eq", 2).ok_or("world_conv: not an equation")?.to_vec();
        let (e_let, e2) = (x[0].clone(), x[1].clone());
        let pl = self.abstract_sub(f.concl(), &e2);
        let back = self.run(&rec::mp(R::Inst("eq_sym".into(), vec![("a", e_let.clone()), ("b", e2.clone())]), vec![rec::s(&eqs)]), &[])?;
        self.run(&rec::mp(R::Inst("eq_subst".into(), vec![("a", e2), ("b", e_let), ("p", pl)]), vec![rec::s(&back), rec::s(&f)]), &[])
    }

    /// `t` with its names expanded (to the kernel's terms)
    fn expand(&self, t: &Term) -> Term {
        match t.node() {
            Node::Var(v, a) if a.is_empty() => match self.vexp.get(v) {
                Some(e) => e.clone(),
                None => t.clone(),
            },
            Node::App(_, a) | Node::Var(_, a) if !a.is_empty() => {
                if let Some(e) = self.exp_memo.borrow().get(t) {
                    return e.clone();
                }
                let e = t.with_args(a.iter().map(|x| self.expand(x)).collect());
                self.exp_memo.borrow_mut().insert(t.clone(), e.clone());
                e
            }
            _ => t.clone(),
        }
    }

    /// the facts among `facts` about t (sharing a variable with it): a simp
    /// sequent rests on every fact it is given
    fn facts_about(&self, facts: &[Seq], t: &Term) -> Vec<R> {
        let mut tv = Vec::new();
        self.expand(t).vars(&mut tv);
        facts
            .iter()
            .filter(|f| {
                let mut fv = Vec::new();
                f.concl().vars(&mut fv);
                fv.iter().any(|v| tv.contains(v))
            })
            .cloned()
            .map(R::S)
            .collect()
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
        let _p = prof::g("canon");
        self.canon_in(&self.expand(t))
    }

    /// a value's name (`T`, a world): not the fixed V and W
    fn is_value(&self, v: VarId) -> bool {
        !matches!(self.env.var(v).name, "V" | "W")
    }

    fn canon_in(&self, t: &Term) -> Term {
        if let Some(v) = self.val_of.get(t) {
            return Term::var(*v, vec![]);
        }
        match t.node() {
            Node::App(_, a) if !a.is_empty() => {
                if let Some(c) = self.canon_memo.borrow().get(t) {
                    return c.clone();
                }
                let c = t.with_args(a.iter().map(|x| self.canon_in(x)).collect());
                self.canon_memo.borrow_mut().insert(t.clone(), c.clone());
                c
            }
            _ => t.clone(),
        }
    }

    /// A value's name (a new one for a new value); literals, constants and
    /// names stand for themselves.
    fn value(&mut self, t: &Term) -> Term {
        let _p = prof::g("value");
        let t = self.canon(t);
        match t.node() {
            Node::Nat(_) | Node::Var(..) => return t,
            Node::App(_, a) if a.is_empty() => return t,
            _ => {}
        }
        if std::env::var("C1_NF_CHECK").is_ok() {
            if let Ok((n, Some(_))) = self.norm(&t) {
                eprintln!("c1 nf: {} named not normal: {} (N: {})", self.fname, self.print(&t), self.print(&n));
            }
        }
        let name = format!("T{}", self.nval);
        self.nval += 1;
        let v = self.env.new_var(&name, 0);
        self.names.push((name, v));
        self.push_val(v, t);
        Term::var(v, vec![])
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
        if let Some(a) = self.app(t, "bits_add", 3) {
            let n = nat(&a[0]).filter(|n| *n <= 64)?;
            return Some((self.eval_lit(&a[1])? + self.eval_lit(&a[2])?) % (1u128 << n));
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

    /// `tr.sal16(s)`: the entry aligned as the ABI has it -- the entry's
    /// condition then the ABI's (`abi.entry_ok`, assumed at the first need;
    /// the alignment by `abi.entry_stack`)
    fn sal16(&mut self) -> Result<Seq, String> {
        if let Some((_, sq)) = &self.ent_al {
            return Ok(sq.clone());
        }
        let (hm, args) = self.ent_m.clone().ok_or("the entry's machine: not known")?;
        let et = self.mk("abi.entry_ok", vec![self.s.clone(), args]);
        let he = self.assume(&et)?;
        let st = self.run(&R::Apply(Box::new(R::F("abi.entry_stack".into())), vec![rec::s(&hm), rec::s(&he)]), &[])?;
        let goal = self.mk("eq", vec![self.mk("int_mod", vec![self.mk("bits_add", vec![lit(64), self.gpr(&self.s, 4), lit(8)]), lit(16)]), lit(0)]);
        let sal = self.evp(&rec::RP::Taut(vec![R::S(st)]), &goal, &[])?;
        self.ent_al = Some((et, sal.clone()));
        Ok(sal)
    }

    /// m's register r, `app(app(m, "gpr"), r)`
    fn gpr(&self, m: &Term, r: u128) -> Term {
        self.mk("app", vec![self.mk("app", vec![m.clone(), Term::bytes(b"gpr")]), lit(r)])
    }

    /// the callee-saved registers st holds (register, bytes, value): those a
    /// callee keeps (tr.cs_sub's rc at a call)
    fn cs_held(&self, st: &St) -> Vec<(u128, u128, Term)> {
        CS_REGS.iter().filter_map(|&r| self.reg(st, r).map(|(n, v)| (r, n, v))).collect()
    }

    /// ... those holding their entry value, not saved in a home st keeps:
    /// a label's or a loop head's (the saved ones are restored from their
    /// homes)
    fn cs_fixed(&self, st: &St) -> Vec<(u128, u128, Term)> {
        self.cs_held(st)
            .into_iter()
            .filter(|(r, n, v)| {
                let e = self.gpr(&self.s, *r);
                *n == 8 && self.canon(v) == self.canon(&e) && !st.hsm.values().any(|(m, x)| *m == 8 && self.canon(x) == self.canon(&e))
            })
            .collect()
    }

    /// the map of the entries es
    fn regs_map(&self, es: &[(u128, u128, Term)]) -> Term {
        es.iter().fold(self.mk("empty", vec![]), |m, (r, n, v)| self.upd(&m, *r, *n, v))
    }

    /// st's registers: only the entries es
    fn with_regs(&self, st: &St, es: &[(u128, u128, Term)]) -> St {
        let mut st2 = st.clone();
        st2.regs = es.to_vec();
        st2.rs = self.regs_map(es);
        st2
    }

    /// `tr.cs_sub(rc, rs)`, rc the map of es (each rs's entry)
    fn cs_sub_pf(&self, es: &[(u128, u128, Term)], rs: &Term) -> R {
        let mut pf = R::Inst("tr.cs_sub_empty".into(), vec![("rs", rs.clone())]);
        let mut rc = self.mk("empty", vec![]);
        for (r, n, v) in es {
            pf = rec::mpf("tr.cs_sub_add", vec![rec::t(&rc), rec::t(rs), rec::t(&lit(*r)), rec::t(&lit(*n)), rec::t(v), rec::p(pf), rec::simp0(), rec::simp_l(), rec::simp_l()]);
            rc = self.upd(&rc, *r, *n, v);
        }
        pf
    }

    /// `tr.cs_rs(s, rs)`: the six at their entry values (at a return)
    fn cs_rs_pf(&self, rs: &Term) -> R {
        rec::mp(R::Inst("tr.cs_rs_intro".into(), vec![("s", self.s.clone()), ("rs", rs.clone())]), (0..12).map(|_| rec::simp_l()).collect())
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

    /// the claim reaching a point `tr.pt(s, bkp, bka, V, base, code, fr, a,
    /// hs, ds, rs, p, w)` (a successor's)
    fn pt(&self, st: &St, a: u128) -> Term {
        self.claim_t("tr.pt", st, a)
    }

    fn claim_t(&self, name: &str, st: &St, a: u128) -> Term {
        self.mk(
            name,
            vec![
                self.s.clone(),
                self.bkp.clone(),
                self.bka.clone(),
                self.v.clone(),
                self.base.clone(),
                self.code.clone(),
                lit(st.fr),
                lit(a),
                st.hst.clone(),
                st.ds.clone(),
                st.rs.clone(),
                self.p(&st.spec),
                st.w.clone(),
            ],
        )
    }

    /// a term from text (terms only), the placeholders by their names
    fn parse(&mut self, text: &str) -> Result<Term, String> {
        let names = self.names.clone();
        syntax::parse_term(self.env, text, &names).map_err(|e| format!("{}: {}", text, e.0))
    }

    /// (C1_TRACE: a message)
    fn trace(&self, m: impl FnOnce() -> String) {
        if std::env::var("C1_TRACE").is_ok_and(|v| v != "phase") {
            eprintln!("c1 {} [{:.2}]", m(), trace_t0());
        }
    }

    /// (C1_TRACE, `phase` too: a walk's phase -- no terms printed)
    fn phase(&self, m: impl FnOnce() -> String) {
        if std::env::var("C1_TRACE").is_ok() {
            // (and the resident memory, MB)
            let rss = std::fs::read_to_string("/proc/self/statm").ok().and_then(|s| s.split_whitespace().nth(1)?.parse::<u64>().ok()).map(|p| p * 4096 / 1_000_000).unwrap_or(0);
            eprintln!("c1 {} [{:.2}, {} MB]", m(), trace_t0(), rss);
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

    fn c1(&mut self, env: &mut Env, fname: &str, spec: &str, prefix: &str, hints: &[String]) -> sl_kernel::KResult<Vec<(String, Seq)>> {
        c1(env, fname, spec, prefix, hints).map_err(sl_kernel::KernelError)
    }

    fn refines(&mut self, env: &mut Env, name: &str, low: &str, high: &str) -> sl_kernel::KResult<Seq> {
        gref::refines(env, name, low, high).map_err(sl_kernel::KernelError)
    }
}
