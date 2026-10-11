//! The logical environment and the inference rules.
//!
//! A `Thm` can only be produced by the functions of this module, so every
//! `Thm` value is a consequence of the axioms and definitions added to its
//! `Env`.

use crate::nat::Nat;
use crate::term::{Node, SymId, Term, VarId};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone)]
pub struct KernelError(pub String);

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.0)
    }
}

pub type KResult<T> = Result<T, KernelError>;

fn err<T>(msg: impl Into<String>) -> KResult<T> {
    Err(KernelError(msg.into()))
}

#[derive(Debug, Clone)]
pub enum SymKind {
    /// built into the kernel (`imp`, `eq`, literal operations)
    Builtin,
    /// declared by `const`; meaning only through axioms
    Primitive,
    /// introduced by a conservative definition
    Defined { params: Vec<VarId>, body: Term },
}

#[derive(Debug, Clone)]
pub struct SymInfo {
    pub name: String,
    pub binders: Vec<u32>, // per argument: number of bound variables
    pub kind: SymKind,
}

#[derive(Debug, Clone)]
pub struct VarInfo {
    pub name: String,
    pub arity: u32,
}

/// A proven statement. Private field: only the kernel can construct it.
#[derive(Clone, Debug)]
pub struct Thm(Term);

impl Thm {
    pub fn prop(&self) -> &Term {
        &self.0
    }

    /// For the trusted extensions (`crate::ext`) only: each derived rule
    /// there documents how its conclusions follow from the kernel's rules.
    pub(crate) fn by_extension(t: Term) -> Thm {
        Thm(t)
    }
}

pub struct Builtins {
    pub imp: SymId,
    pub eq: SymId,
    pub is_nat: SymId,
    pub lit_lt: SymId,
    pub lit_add: SymId,
    pub lit_sub: SymId,
    pub lit_mul: SymId,
    pub lit_div: SymId,
    pub lit_mod: SymId,
    pub bytes_len: SymId,
    pub bytes_at: SymId,
}

pub struct Env {
    pub syms: Vec<SymInfo>,
    pub sym_by_name: HashMap<String, SymId>,
    pub vars: Vec<VarInfo>,
    pub axioms: Vec<(String, Thm)>,
    pub defs: Vec<(SymId, Thm)>,
    pub claims: Vec<(String, Term)>,
    /// proven theorems (checked proofs from core files)
    pub theorems: Vec<(String, Thm)>,
    /// open lemmas and conditional theorems (`ext::facts`; never `Thm`s)
    pub open: crate::ext::facts::OpenFacts,
    pub builtins: Builtins,
    /// abbreviations (`abbrev NAME(params) := term`, a proof's `let`): read
    /// as their expansion -- the body with its k parameters as the outer k
    /// bound variables, instantiated like a definition's. Only the parser
    /// sees them; terms never contain them.
    pub abbrevs: HashMap<String, (usize, Term)>,
    /// definitions the proof checker's implicit unfolding leaves folded
    /// (`irreducible NAME`; explicit unfolding still unfolds them). A hint
    /// for proof search only: the kernel's rules ignore it.
    pub irreducible: std::collections::HashSet<SymId>,
    /// the registered rewrite rules of the proof checker's simp (`simp
    /// NAME`: a proven fact, an equation or equivalence possibly under
    /// premises), in order. A hint for proof search only.
    pub simp_set: Vec<String>,
    /// the memory procedure's views (`mem_view NAME`: an equation unfolding
    /// a read or a write into `gimple.bytes_at` / `store_le`) and frame
    /// equations (`mem_frame NAME`: a predicate the bytes do not matter
    /// to), in order. Hints for the proof checker's `mem` rules.
    pub mem_views: Vec<String>,
    pub mem_frames: Vec<String>,
    /// closure facts (`mem_closure NAME`: a property of a written state from
    /// the state's, applied backward to discharge a premise)
    pub mem_closures: Vec<String>,
    /// the bit rules (`bit_rule NAME`: `H.. -> (bit(P, i) <-> φ)`, a word
    /// P's bit), in order. Hints for the proof checker's `bitwise`.
    pub bit_rules: Vec<String>,
    /// the symbols defined by the canonical prelude: those numbered below
    /// this (`ext::pinned`), if it was loaded
    pub prelude_end: Option<usize>,
    /// the layer definitions with their pinned bodies (`ext::pinned`)
    pub pinned: std::collections::HashSet<SymId>,
    /// (terms checked well-formed, at a depth: they stay so, the
    /// environment only growing -- each checked once)
    wf_ok: std::cell::RefCell<std::collections::HashSet<(Term, u32)>>,
    /// (terms' loose depths under this environment's binders, computed
    /// once)
    ld_memo: std::cell::RefCell<HashMap<Term, u32>>,
}

impl Env {
    /// A symbol a trusted extension relies on by name: a symbol of the
    /// canonical prelude, or a pinned definition (`ext::pinned`); else
    /// none (another file's symbol of that name means something else).
    pub fn ksym(&self, name: &str) -> Option<SymId> {
        let s = *self.sym_by_name.get(name)?;
        (self.pinned.contains(&s) || self.prelude_end.is_some_and(|e| (s as usize) < e)).then_some(s)
    }

    /// A symbol's name, for dispatch in a trusted extension: the name only
    /// if the symbol is what `ksym` resolves it to, else "" (no rule's).
    pub fn kname(&self, s: SymId) -> &str {
        let name = self.syms[s as usize].name.as_str();
        if self.ksym(name) == Some(s) { name } else { "" }
    }

    pub fn new() -> Env {
        let mut env = Env {
            syms: Vec::new(),
            sym_by_name: HashMap::new(),
            vars: Vec::new(),
            axioms: Vec::new(),
            defs: Vec::new(),
            claims: Vec::new(),
            theorems: Vec::new(),
            open: Default::default(),
            abbrevs: HashMap::new(),
            irreducible: Default::default(),
            simp_set: Vec::new(),
            mem_views: Vec::new(),
            mem_frames: Vec::new(),
            mem_closures: Vec::new(),
            bit_rules: Vec::new(),
            prelude_end: None,
            pinned: Default::default(),
            wf_ok: Default::default(),
            ld_memo: Default::default(),
            builtins: Builtins {
                imp: 0,
                eq: 0,
                is_nat: 0,
                lit_lt: 0,
                lit_add: 0,
                lit_sub: 0,
                lit_mul: 0,
                lit_div: 0,
                lit_mod: 0,
                bytes_len: 0,
                bytes_at: 0,
            },
        };
        let mut b = |name: &str, arity: usize| env.add_sym(name, vec![0; arity], SymKind::Builtin).unwrap();
        let imp = b("imp", 2);
        let eq = b("eq", 2);
        let is_nat = b("is_nat", 1);
        let lit_lt = b("lit_lt", 2);
        let lit_add = b("lit_add", 2);
        let lit_sub = b("lit_sub", 2);
        let lit_mul = b("lit_mul", 2);
        let lit_div = b("lit_div", 2);
        let lit_mod = b("lit_mod", 2);
        let bytes_len = b("bytes_len", 1);
        let bytes_at = b("bytes_at", 2);
        env.builtins = Builtins { imp, eq, is_nat, lit_lt, lit_add, lit_sub, lit_mul, lit_div, lit_mod, bytes_len, bytes_at };
        env
    }

    fn add_sym(&mut self, name: &str, binders: Vec<u32>, kind: SymKind) -> KResult<SymId> {
        if self.sym_by_name.contains_key(name) {
            return err(format!("symbol `{}` already declared", name));
        }
        // (an abbreviation is read before symbols: a symbol of its name
        // would never be what a statement mentions)
        if self.abbrevs.contains_key(name) {
            return err(format!("`{}` is an abbreviation", name));
        }
        let id = self.syms.len() as SymId;
        self.syms.push(SymInfo { name: name.to_string(), binders, kind });
        self.sym_by_name.insert(name.to_string(), id);
        Ok(id)
    }

    pub fn binders_fn(&self) -> impl Fn(SymId, usize) -> u32 + '_ {
        move |s, i| self.syms[s as usize].binders[i]
    }

    pub fn new_var(&mut self, name: &str, arity: u32) -> VarId {
        self.vars.push(VarInfo { name: name.to_string(), arity });
        (self.vars.len() - 1) as VarId
    }

    /// Well-formedness: arities of symbols and variables, no loose bound
    /// variables (at the given outer depth).
    pub fn check_wf(&self, t: &Term, depth: u32) -> KResult<()> {
        let big = matches!(t.node(), Node::App(_, a) | Node::Var(_, a) if !a.is_empty());
        if big && self.wf_ok.borrow().contains(&(t.clone(), depth)) {
            return Ok(());
        }
        self.check_wf_node(t, depth)?;
        if big {
            self.wf_ok.borrow_mut().insert((t.clone(), depth));
        }
        Ok(())
    }

    /// `t.loose_depth(..)` under this environment's binders, each compound
    /// term's computed once
    pub fn loose_depth_m(&self, t: &Term) -> u32 {
        match t.node() {
            Node::BVar(i) => i + 1,
            Node::Var(_, a) | Node::App(_, a) if a.is_empty() => 0,
            Node::Var(_, a) | Node::App(_, a) => {
                if let Some(d) = self.ld_memo.borrow().get(t) {
                    return *d;
                }
                let d = match t.node() {
                    Node::App(s, _) => a.iter().enumerate().map(|(i, x)| self.loose_depth_m(x).saturating_sub(self.syms[*s as usize].binders[i])).max().unwrap_or(0),
                    _ => a.iter().map(|x| self.loose_depth_m(x)).max().unwrap_or(0),
                };
                self.ld_memo.borrow_mut().insert(t.clone(), d);
                d
            }
            _ => 0,
        }
    }

    /// `t.instantiate_params(args, ..)` (the same term): its parts without
    /// a parameter kept as they are, a closed argument not shifted
    pub fn instantiate_params_m(&self, t: &Term, args: &[Term]) -> Term {
        self.inst_m(t, args, 0)
    }

    fn inst_m(&self, t: &Term, args: &[Term], depth: u32) -> Term {
        if self.loose_depth_m(t) <= depth {
            return t.clone();
        }
        let k = args.len() as u32;
        match t.node() {
            Node::BVar(i) if *i >= depth => {
                let a = &args[(k - 1 - (i - depth)) as usize];
                if self.loose_depth_m(a) == 0 { a.clone().labelled_as(t) } else { a.shift(depth, 0, &self.binders_fn()).labelled_as(t) }
            }
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.inst_m(x, args, depth)).collect()),
            Node::App(s, a) => {
                let bs = &self.syms[*s as usize].binders;
                t.with_args(a.iter().enumerate().map(|(i, x)| self.inst_m(x, args, depth + bs[i])).collect())
            }
        }
    }

    /// `t.subst_var(v, value, ..)` (the same term): the value's instances
    /// as `instantiate_params_m` makes them
    pub fn subst_var_m(&self, t: &Term, v: VarId, value: &Term) -> Term {
        if !t.may_contain_var(v) {
            return t.clone();
        }
        match t.node() {
            Node::Var(w, args) => {
                let args: Vec<Term> = args.iter().map(|a| self.subst_var_m(a, v, value)).collect();
                if *w == v {
                    self.instantiate_params_m(value, &args).labelled_as(t)
                } else {
                    t.with_args(args)
                }
            }
            Node::App(_, args) => t.with_args(args.iter().map(|a| self.subst_var_m(a, v, value)).collect()),
            _ => t.clone(),
        }
    }

    fn check_wf_node(&self, t: &Term, depth: u32) -> KResult<()> {
        match t.node() {
            Node::BVar(i) => {
                if *i >= depth {
                    return err(format!("loose bound variable #{}", i));
                }
            }
            Node::Nat(_) | Node::Bytes(_) => {}
            Node::Var(v, args) => {
                let info = self.vars.get(*v as usize).ok_or_else(|| KernelError("unknown variable".into()))?;
                if args.len() as u32 != info.arity {
                    return err(format!("variable `{}` expects {} arguments, got {}", info.name, info.arity, args.len()));
                }
                for a in args.iter() {
                    self.check_wf(a, depth)?;
                }
            }
            Node::App(s, args) => {
                let info = self.syms.get(*s as usize).ok_or_else(|| KernelError("unknown symbol".into()))?;
                if args.len() != info.binders.len() {
                    return err(format!("`{}` expects {} arguments, got {}", info.name, info.binders.len(), args.len()));
                }
                for (i, a) in args.iter().enumerate() {
                    self.check_wf(a, depth + info.binders[i])?;
                }
            }
        }
        Ok(())
    }

    // (constants and axioms: the prelude's, through `syntax::load` only)
    pub(crate) fn declare_const(&mut self, name: &str, binders: Vec<u32>) -> KResult<SymId> {
        self.add_sym(name, binders, SymKind::Primitive)
    }

    pub(crate) fn add_axiom(&mut self, name: &str, prop: Term) -> KResult<Thm> {
        self.check_wf(&prop, 0)?;
        let thm = Thm(prop);
        self.axioms.push((name.to_string(), thm.clone()));
        Ok(thm)
    }

    /// Conservative definition `name(params) := body`. Parameter `p` of
    /// arity k becomes an argument binding k variables. Returns the
    /// defining equation `name(p0(..), ...) = body`.
    pub fn define(&mut self, name: &str, params: Vec<VarId>, body: Term) -> KResult<(SymId, Thm)> {
        self.check_wf(&body, 0)?;
        let mut used = Vec::new();
        body.vars(&mut used);
        for v in &used {
            if !params.contains(v) {
                return err(format!("definition of `{}` mentions `{}`, which is not a parameter", name, self.vars[*v as usize].name));
            }
        }
        for (i, p) in params.iter().enumerate() {
            if params[..i].contains(p) {
                return err(format!("definition of `{}`: repeated parameter", name));
            }
        }
        // (a name the extensions rely on: only with its pinned body)
        let pinned = crate::ext::pinned::check_def(self, name, &params, &body)?;
        let binders: Vec<u32> = params.iter().map(|p| self.vars[*p as usize].arity).collect();
        let sym = self.add_sym(name, binders.clone(), SymKind::Defined { params: params.clone(), body: body.clone() })?;
        if pinned {
            self.pinned.insert(sym);
        }
        let args: Vec<Term> = params
            .iter()
            .zip(&binders)
            .map(|(p, &k)| Term::var(*p, (0..k).rev().map(Term::bvar).collect()))
            .collect();
        let thm = Thm(self.mk_eq(Term::app(sym, args), body));
        self.defs.push((sym, thm.clone()));
        Ok((sym, thm))
    }

    pub fn add_claim(&mut self, name: &str, prop: Term) -> KResult<()> {
        self.check_wf(&prop, 0)?;
        let mut vs = Vec::new();
        prop.vars(&mut vs);
        if !vs.is_empty() {
            return err(format!("claim `{}` is not closed (schematic variable `{}`)", name, self.vars[vs[0] as usize].name));
        }
        self.claims.push((name.to_string(), prop));
        Ok(())
    }

    /// Records a proven theorem under a name (for later proofs to use).
    pub fn add_theorem(&mut self, name: &str, thm: Thm) -> KResult<()> {
        if self.theorems.iter().any(|(n, _)| n == name) || self.axioms.iter().any(|(n, _)| n == name) {
            return err(format!("fact `{}` already exists", name));
        }
        self.theorems.push((name.to_string(), thm));
        Ok(())
    }

    /// A theorem or axiom by name.
    pub fn fact(&self, name: &str) -> Option<&Thm> {
        self.theorems.iter().chain(self.axioms.iter()).find(|(n, _)| n == name).map(|(_, t)| t)
    }

    pub fn mk_imp(&self, a: Term, b: Term) -> Term {
        Term::app(self.builtins.imp, vec![a, b])
    }

    pub fn mk_eq(&self, a: Term, b: Term) -> Term {
        Term::app(self.builtins.eq, vec![a, b])
    }

    // ------------------------------------------------------------------
    //  Inference rules

    /// From `a -> b` and `a`, conclude `b`.
    pub fn modus_ponens(&self, imp: &Thm, a: &Thm) -> KResult<Thm> {
        match imp.0.node() {
            Node::App(s, args) if *s == self.builtins.imp && args[0] == a.0 => Ok(Thm(args[1].clone())),
            _ => err("modus ponens: premise does not match"),
        }
    }

    /// Instantiate schematic variable `v` by `value` (with `arity(v)` parameters).
    pub fn instantiate(&self, thm: &Thm, v: VarId, value: &Term) -> KResult<Thm> {
        let arity = self.vars.get(v as usize).ok_or_else(|| KernelError("unknown variable".into()))?.arity;
        self.check_wf(value, arity)?;
        Ok(Thm(thm.0.subst_var(v, value, &self.binders_fn())))
    }

    fn lit(t: &Term) -> KResult<&Nat> {
        match t.node() {
            Node::Nat(n) => Ok(n),
            _ => err("expected a numeric literal"),
        }
    }

    /// `is_nat(n)` for a numeric literal `n`.
    pub fn lit_is_nat(&self, n: &Term) -> KResult<Thm> {
        Self::lit(n)?;
        Ok(Thm(Term::app(self.builtins.is_nat, vec![n.clone()])))
    }

    /// For literals a, b: `lit_lt(a, b)`, `a = b` or `lit_lt(b, a)`.
    pub fn lit_compare(&self, a: &Term, b: &Term) -> KResult<Thm> {
        let (x, y) = (Self::lit(a)?, Self::lit(b)?);
        Ok(Thm(match x.cmp(y) {
            std::cmp::Ordering::Less => Term::app(self.builtins.lit_lt, vec![a.clone(), b.clone()]),
            std::cmp::Ordering::Equal => self.mk_eq(a.clone(), b.clone()),
            std::cmp::Ordering::Greater => Term::app(self.builtins.lit_lt, vec![b.clone(), a.clone()]),
        }))
    }

    /// `op(a, b) = c` for literal arithmetic (`op` one of lit_add, lit_sub,
    /// lit_mul, lit_div, lit_mod; sub/div/mod only when defined).
    pub fn lit_compute(&self, op: SymId, a: &Term, b: &Term) -> KResult<Thm> {
        let (x, y) = (Self::lit(a)?, Self::lit(b)?);
        let bi = &self.builtins;
        let r = if op == bi.lit_add {
            x.add(y)
        } else if op == bi.lit_mul {
            x.mul(y)
        } else if op == bi.lit_sub {
            x.sub(y).ok_or_else(|| KernelError("lit_sub: negative".into()))?
        } else if op == bi.lit_div {
            x.divmod(y).ok_or_else(|| KernelError("lit_div: by zero".into()))?.0
        } else if op == bi.lit_mod {
            x.divmod(y).ok_or_else(|| KernelError("lit_mod: by zero".into()))?.1
        } else {
            return err("lit_compute: not an arithmetic builtin");
        };
        Ok(Thm(self.mk_eq(Term::app(op, vec![a.clone(), b.clone()]), Term::nat(r))))
    }

    /// `bytes_len(B) = n` and `bytes_at(B, i) = byte`.
    pub fn bytes_len(&self, b: &Term) -> KResult<Thm> {
        match b.node() {
            Node::Bytes(v) => Ok(Thm(self.mk_eq(
                Term::app(self.builtins.bytes_len, vec![b.clone()]),
                Term::nat(Nat::from_u64(v.len() as u64)),
            ))),
            _ => err("expected a bytes literal"),
        }
    }

    pub fn bytes_at(&self, b: &Term, i: &Term) -> KResult<Thm> {
        let idx = Self::lit(i)?.to_u64().ok_or_else(|| KernelError("index too large".into()))?;
        match b.node() {
            Node::Bytes(v) if (idx as usize) < v.len() => Ok(Thm(self.mk_eq(
                Term::app(self.builtins.bytes_at, vec![b.clone(), i.clone()]),
                Term::nat(Nat::from_u64(v[idx as usize] as u64)),
            ))),
            _ => err("bytes_at: not a bytes literal or index out of range"),
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Env::new()
    }
}
