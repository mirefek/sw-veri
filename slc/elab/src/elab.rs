//! The elaborator: SL declarations -> kernel definitions.
//!
//! Procedures become programs (`mkprog(s o. F)`), where `F` is built in
//! continuation-passing style: each statement contributes `Frame`s that wrap
//! "the rest of the block". Compound statements join their branches through
//! existentially quantified variables, so the output stays linear in size.

use crate::build::B;
use crate::globals::{GName, Globals};
use crate::ty::{Ext, StateTy, Ty};
use sl_kernel::{Env, SymId, Term, VarId};
use sl_syntax::ast::*;
use sl_syntax::SourceMap;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Diag {
    pub span: Span,
    pub msg: String,
    pub warning: bool,
}

pub type R<T> = Result<T, Diag>;

pub fn err<T>(span: Span, msg: impl Into<String>) -> R<T> {
    Err(Diag { span, msg: msg.into(), warning: false })
}

// ----------------------------------------------------------------------
//  Context

#[derive(Clone, Debug)]
pub struct Local {
    pub name: String,
    pub term: Term,
    pub ty: Ty,
    pub mutable: bool,
}

/// A piece of formula with a hole for "the rest".
#[derive(Clone, Debug)]
pub enum Frame {
    /// `letin(value, var. HOLE)`
    Let { var: VarId, value: Term },
    /// run `prog` from `s_in`; normal outcome binds `s_out`, `v_out`
    Run { prog: Term, s_in: Term, s_out: VarId, v_out: VarId, exc: (VarId, VarId, Term), div: (VarId, Term) },
    /// nondeterministic choice of `var` from `dom` (a formula in `var`)
    Choose { var: VarId, dom: Term },
    /// `!cond || HOLE`
    Require(Term),
    /// `(cond && HOLE) || (!cond && fail)`
    Guard { cond: Term, fail: Term },
    /// `ex vars. body && HOLE`
    Join { vars: Vec<VarId>, body: Term },
    /// a compound statement with local outcome `r`:
    /// `ex r. body && ((normal && HOLE) || abrupt)`
    Local { r: VarId, body: Term, normal: Term, abrupt: Term },
    /// the rest is unreachable
    Terminal(Term),
}

/// Where control goes when a statement ends. Local outcomes encode
/// `normal`: ok(pair(s, vars), value), `ret`: exc(pair(s, vars), ("ret", v)),
/// `raise`: exc(pair(s, vars), ("raise", e)), `brk`: exc(pair(s, vars), ("brk", 0)),
/// divergence: diverge(t).
#[derive(Clone, Debug)]
pub enum Exit {
    /// top of a proc body: outcome variable `o`
    Proc { o: VarId },
    /// a compound statement (or loop body) with local outcome `r`
    Local { r: VarId, muts: Vec<usize>, is_loop: bool },
}

#[derive(Clone, Debug)]
pub struct Cx {
    pub module: String,
    pub pure: bool,
    pub state: Option<Term>,
    pub state_ty: Option<Ty>,
    pub locals: Vec<Local>,
    pub frames: Vec<Frame>,
    pub lift: HashMap<String, Term>,
    /// value generics (`w`) and type generics (`G`, `E`)
    pub gvals: HashMap<String, (Term, Ty)>,
    pub gtys: HashMap<String, (Ty, Term)>,
    pub exits: Vec<Exit>,
    /// the enclosing program's return type (`return e` is checked against it)
    pub ret: Option<Ty>,
}

impl Cx {
    pub fn new(module: &str) -> Cx {
        Cx {
            module: module.into(),
            pure: true,
            state: None,
            state_ty: None,
            locals: Vec::new(),
            frames: Vec::new(),
            lift: HashMap::new(),
            gvals: HashMap::new(),
            gtys: HashMap::new(),
            exits: Vec::new(),
            ret: None,
        }
    }

    pub fn local(&self, name: &str) -> Option<&Local> {
        self.locals.iter().rev().find(|l| l.name == name)
    }

    pub fn push_local(&mut self, name: &str, term: Term, ty: Ty, mutable: bool) {
        self.locals.push(Local { name: name.into(), term, ty, mutable });
    }

    pub fn mut_indices(&self) -> Vec<usize> {
        // the innermost binding of each mutable name
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        for (i, l) in self.locals.iter().enumerate().rev() {
            if seen.insert(l.name.clone()) && l.mutable {
                out.push(i);
            }
        }
        out.reverse();
        out
    }
}

// ----------------------------------------------------------------------
//  Signatures

#[derive(Clone, Debug, PartialEq)]
pub enum SigKind {
    Fn,
    Proc(Ty),
    Const,
}

#[derive(Clone, Debug)]
pub struct GenParam {
    pub name: String,
    pub var: VarId,
    /// `Some(ty)` for value generics (`[w: Width]`), `None` for type generics
    pub val_ty: Option<Ty>,
}

#[derive(Clone, Debug)]
pub struct Sig {
    pub core: String,
    pub lift: Vec<String>,
    pub generics: Vec<GenParam>,
    pub params: Vec<(String, VarId, Ty)>,
    pub ret: Ty,
    pub kind: SigKind,
    /// types may mention the state at the call (`bits[8*zsize(ctx.osz)]`)
    pub state_var: Option<VarId>,
}

// ----------------------------------------------------------------------
//  The elaborator

pub struct Elab<'s> {
    pub b: B,
    pub g: Globals,
    pub sm: &'s SourceMap,
    pub diags: Vec<Diag>,
    pub prelude_syms: usize,
    sigs: HashMap<String, Sig>,
    in_progress: HashSet<usize>,
    done: HashSet<usize>,
    failed: HashSet<usize>,
    /// set terms of named types (record / enum / sum / state / table insn)
    pub type_sets: HashMap<String, Term>,
    /// layer-parameter variables by qualified param name (for claims)
    pub lift_vars: HashMap<String, VarId>,
    pub claims: Vec<(String, Term)>,
    counter: usize,
}

impl<'s> Elab<'s> {
    pub fn new(env: Env, g: Globals, sm: &'s SourceMap) -> Elab<'s> {
        let prelude_syms = env.syms.len();
        Elab {
            b: B { env },
            g,
            sm,
            diags: Vec::new(),
            prelude_syms,
            sigs: HashMap::new(),
            in_progress: HashSet::new(),
            done: HashSet::new(),
            failed: HashSet::new(),
            type_sets: HashMap::new(),
            lift_vars: HashMap::new(),
            claims: Vec::new(),
            counter: 0,
        }
    }

    pub fn warn(&mut self, span: Span, msg: impl Into<String>) {
        self.diags.push(Diag { span, msg: msg.into(), warning: true });
    }

    pub fn fresh(&mut self, hint: &str) -> VarId {
        self.b.fresh(hint)
    }

    pub fn uniq(&mut self, base: &str) -> String {
        self.counter += 1;
        format!("{}${}", base, self.counter)
    }

    /// Defines `name(params) := body`; returns the symbol.
    pub fn define(&mut self, name: &str, params: Vec<VarId>, body: Term, span: Span) -> R<SymId> {
        match self.b.env.define(name, params, body) {
            Ok((s, _)) => Ok(s),
            Err(e) => err(span, format!("kernel rejected definition of `{}`: {}", name, e)),
        }
    }

    /// Elaborates every declaration.
    pub fn run(&mut self) {
        for i in 0..self.g.decls.len() {
            // root causes are recorded by `ensure`
            let _ = self.ensure(i);
        }
    }

    pub fn module_of(&self, i: usize) -> String {
        self.g.decls[i].module.clone()
    }

    /// Makes sure declaration `i` has been elaborated (its definitions exist).
    pub fn ensure(&mut self, i: usize) -> R<()> {
        if self.failed.contains(&i) {
            let d = &self.g.decls[i];
            return Err(Diag { span: d.decl.span, msg: format!("(depends on `{}`, which failed)", d.qual), warning: false });
        }
        if self.done.contains(&i) {
            return Ok(());
        }
        if !self.in_progress.insert(i) {
            let d = &self.g.decls[i];
            return err(d.decl.span, format!("`{}` is defined in terms of itself (recursion is not supported yet)", d.qual));
        }
        let r = self.elab_decl(i);
        self.in_progress.remove(&i);
        match &r {
            Ok(()) => {
                self.done.insert(i);
            }
            Err(d) => {
                self.failed.insert(i);
                // report the root cause once
                if !d.msg.starts_with("(depends on") {
                    self.diags.push(d.clone());
                }
                let q = self.g.decls[i].qual.clone();
                return Err(Diag { span: d.span, msg: format!("(depends on `{}`, which failed)", q), warning: false });
            }
        }
        r
    }

    // ------------------------------------------------------------------
    //  Types

    pub fn state_ty_named(&mut self, qual: &str) -> Ty {
        // `state H extends B { ghost ... }` = B & H.ghost
        let i = self.g.decls.iter().position(|d| d.qual == qual).unwrap();
        if let DeclKind::State { extends: Some(t), .. } = &self.g.decls[i].decl.kind {
            let module = self.g.decls[i].module.clone();
            let t = t.clone();
            if let Ok(Ty::State(mut base)) = self.ty(&Cx::new(&module), &t) {
                base.ext.push(Ext::Fields(qual.to_string()));
                return Ty::State(base);
            }
        }
        Ty::State(StateTy { base: qual.to_string(), ext: Vec::new() })
    }

    /// Resolves an AST type.
    pub fn ty(&mut self, cx: &Cx, t: &Type) -> R<Ty> {
        match t {
            Type::Named(n, args) => self.named_ty(cx, n, args),
            Type::Map(a, b) => Ok(Ty::Map(Box::new(self.ty(cx, a)?), Box::new(self.ty(cx, b)?))),
            Type::Tuple(ts) if ts.is_empty() => Ok(Ty::Unit),
            Type::Tuple(ts) => Ok(Ty::Tuple(ts.iter().map(|t| self.ty(cx, t)).collect::<R<_>>()?)),
            Type::Refine(v, base, pred) => {
                let bt = self.ty(cx, base)?;
                let set = self.ty_set(&bt, v.span)?;
                let x = self.fresh(&v.name);
                let mut cx2 = cx.clone();
                cx2.pure = true;
                cx2.push_local(&v.name, self.b.v(x), bt.clone(), false);
                let (p, _) = self.expr(&mut cx2, pred, Some(&Ty::Bool))?;
                let s = self.b.bind_app("set_select", vec![set], &[x], &p);
                Ok(Ty::Refine(Box::new(bt), s))
            }
            Type::Proc { state, params, ret } => {
                let st = match state {
                    Some(s) => self.ty(cx, s)?,
                    None => self.default_state(cx, t_span(t))?,
                };
                let ps = params.iter().map(|p| self.ty(cx, p)).collect::<R<Vec<_>>>()?;
                let r = match ret {
                    Some(r) => self.ty(cx, r)?,
                    None => Ty::Unit,
                };
                Ok(Ty::Proc { state: Box::new(st), params: ps, ret: Box::new(r) })
            }
            Type::And(a, b) => {
                let ta = self.ty(cx, a)?;
                let tb = self.ty(cx, b)?;
                match (ta, tb) {
                    (Ty::State(mut s), Ty::Param(n, t)) => {
                        s.ext.push(Ext::Param(n, t));
                        Ok(Ty::State(s))
                    }
                    (Ty::State(mut s), Ty::State(o)) => {
                        s.ext.extend(o.ext);
                        Ok(Ty::State(s))
                    }
                    _ => err(t_span(t), "`&` combines a state type with a state extension"),
                }
            }
            Type::EnumKind(_) => err(t_span(t), "`enum bits[k]` is only a kind of type parameters"),
        }
    }

    pub fn default_state(&mut self, cx: &Cx, span: Span) -> R<Ty> {
        if let Some(t) = &cx.state_ty {
            return Ok(t.clone());
        }
        match self.g.modules[&cx.module].default_state.clone() {
            Some(q) => Ok(self.state_ty_named(&q)),
            None => err(span, format!("module `{}` declares no state; write `proc[S]`", cx.module)),
        }
    }

    fn named_ty(&mut self, cx: &Cx, n: &Ident, args: &[GenArg]) -> R<Ty> {
        let arg_ty = |s: &mut Self, i: usize| -> R<Ty> {
            match args.get(i) {
                Some(GenArg::Type(t)) => s.ty(cx, t),
                _ => err(n.span, format!("`{}` needs a type argument", n.name)),
            }
        };
        match n.name.as_str() {
            "bool" => return Ok(Ty::Bool),
            "nat" => return Ok(Ty::Nat),
            "int" => return Ok(Ty::Int),
            "natinf" => return Ok(Ty::NatInf),
            "string" => return Ok(Ty::Str),
            "bits" => {
                let e = match args.first() {
                    Some(GenArg::Expr(e)) => e.clone(),
                    _ => return err(n.span, "`bits` needs a width"),
                };
                let mut cx2 = cx.clone();
                cx2.pure = true;
                let (w, _) = self.expr(&mut cx2, &e, Some(&Ty::Nat))?;
                return Ok(Ty::Bits(self.b.norm(&w)));
            }
            "Option" => return Ok(Ty::Opt(Box::new(arg_ty(self, 0)?))),
            "List" => return Ok(Ty::List(Box::new(arg_ty(self, 0)?))),
            "Seq" => return Ok(Ty::Seq(Box::new(arg_ty(self, 0)?))),
            "Set" => return Ok(Ty::Set(Box::new(arg_ty(self, 0)?))),
            "Outcome" => return Ok(Ty::Outcome(Box::new(arg_ty(self, 0)?), Box::new(arg_ty(self, 1)?))),
            _ => {}
        }
        if let Some((t, _)) = cx.gtys.get(&n.name) {
            return Ok(t.clone());
        }
        if let Some((m, rest)) = n.name.split_once('.') {
            // `table.Insn`
            if rest == "Insn" {
                if let Some(i) = self.g.find_decl(&cx.module, m) {
                    if matches!(self.g.decls[i].decl.kind, DeclKind::Table(_)) {
                        return Ok(Ty::Insn(self.g.decls[i].qual.clone()));
                    }
                }
            }
        }
        let i = match self.g.find_decl(&cx.module, &n.name) {
            Some(i) => i,
            None => return err(n.span, format!("unknown type `{}`", n.name)),
        };
        let qual = self.g.decls[i].qual.clone();
        let module = self.g.decls[i].module.clone();
        match self.g.decls[i].decl.kind.clone() {
            DeclKind::TypeDecl { generics, def: TypeDef::Alias(t), .. } => {
                // expand the alias, binding its type parameters
                let mut cx2 = Cx::new(&module);
                for (k, gp) in generics.iter().enumerate() {
                    let a = arg_ty(self, k)?;
                    let set = self.ty_set(&a, n.span)?;
                    cx2.gtys.insert(gp.name.name.clone(), (a, set));
                }
                self.ty(&cx2, &t)
            }
            DeclKind::TypeDecl { def: TypeDef::Sum(_), .. } => Ok(Ty::Sum(qual)),
            DeclKind::Enum { .. } => Ok(Ty::Enum(qual)),
            DeclKind::Record { .. } => Ok(Ty::Rec(qual)),
            DeclKind::State { .. } => Ok(self.state_ty_named(&qual)),
            _ => err(n.span, format!("`{}` is not a type", n.name)),
        }
    }

    /// The set of values of a type (a kernel term).
    pub fn ty_set(&mut self, t: &Ty, span: Span) -> R<Term> {
        let b = &self.b;
        Ok(match t {
            Ty::Bool => b.c("bool"),
            Ty::Nat => b.c("omega"),
            Ty::Int => b.c("int"),
            Ty::NatInf => b.c("natinf"),
            Ty::Unit => b.app("single", vec![b.empty()]),
            Ty::Bits(w) => b.app("bits", vec![w.clone()]),
            Ty::Tuple(ts) => {
                let mut sets = Vec::new();
                for t in ts {
                    sets.push(self.ty_set(t, span)?);
                }
                let last = sets.pop().unwrap();
                sets.into_iter().rev().fold(last, |acc, s| self.b.app("cart", vec![s, acc]))
            }
            Ty::Map(a, c) => {
                let sa = self.ty_set(a, span)?;
                let sc = self.ty_set(c, span)?;
                self.b.app("fn_space", vec![sa, sc])
            }
            Ty::List(e) => {
                let s = self.ty_set(e, span)?;
                self.b.app("list_type", vec![s])
            }
            Ty::Seq(e) => {
                let s = self.ty_set(e, span)?;
                self.b.app("seq_type", vec![s])
            }
            Ty::Set(e) => {
                let s = self.ty_set(e, span)?;
                self.b.app("set_type", vec![s])
            }
            Ty::Opt(e) => {
                let s = self.ty_set(e, span)?;
                self.b.app("option", vec![s])
            }
            Ty::Rec(n) | Ty::Enum(n) | Ty::Sum(n) => self.named_set(n, span)?,
            Ty::State(st) => self.state_set(st, span)?,
            Ty::Refine(_, s) => s.clone(),
            Ty::Outcome(s, v) => {
                let ss = self.ty_set(s, span)?;
                let vs = self.ty_set(v, span)?;
                self.b.app("outcome_type", vec![ss, vs])
            }
            Ty::Param(_, s) => s.clone(),
            Ty::Proc { params, .. } => {
                let progs = self.b.app("powerset", vec![self.b.app("univ", vec![self.b.nat(1)])]);
                let dom = if params.is_empty() {
                    self.ty_set(&Ty::Unit, span)?
                } else {
                    self.ty_set(&Ty::Tuple(params.clone()), span)?
                };
                self.b.app("fn_space", vec![dom, progs])
            }
            Ty::Prog(..) => self.b.app("powerset", vec![self.b.app("univ", vec![self.b.nat(1)])]),
            Ty::Str | Ty::Exc | Ty::Insn(_) | Ty::Unknown => b.app("univ", vec![b.nat(1)]),
        })
    }

    /// Set of a record / enum / sum / state declaration, defined once.
    pub fn named_set(&mut self, qual: &str, span: Span) -> R<Term> {
        if let Some(t) = self.type_sets.get(qual) {
            return Ok(t.clone());
        }
        let i = match self.g.decls.iter().position(|d| d.qual == qual) {
            Some(i) => i,
            None => return err(span, format!("unknown type `{}`", qual)),
        };
        let module = self.g.decls[i].module.clone();
        let cx = Cx::new(&module);
        let body = match self.g.decls[i].decl.kind.clone() {
            DeclKind::Enum { items, .. } => {
                let vals = self.enum_values(i)?;
                let _ = items;
                let ts: Vec<Term> = vals.iter().map(|(_, v)| self.b.natn(v.clone())).collect();
                self.b.set_of(ts)
            }
            DeclKind::Record { fields, .. } | DeclKind::State { fields, .. } => self.record_set(&cx, &fields, span)?,
            DeclKind::TypeDecl { def: TypeDef::Sum(vs), .. } => {
                let mut parts = Vec::new();
                for (j, v) in vs.iter().enumerate() {
                    let tys = v.params.iter().map(|p| self.ty(&cx, &p.ty)).collect::<R<Vec<_>>>()?;
                    let payload = match tys.len() {
                        0 => self.ty_set(&Ty::Unit, span)?,
                        1 => self.ty_set(&tys[0], span)?,
                        _ => self.ty_set(&Ty::Tuple(tys), span)?,
                    };
                    let x = self.fresh("x");
                    let tagged = self.b.tag(j as u64, self.b.v(x));
                    parts.push(self.b.bind_app("set_image", vec![payload], &[x], &tagged));
                }
                let last = parts.pop().unwrap_or_else(|| self.b.empty());
                parts.into_iter().rev().fold(last, |acc, p| self.b.app("union2", vec![p, acc]))
            }
            _ => return err(span, format!("`{}` has no set", qual)),
        };
        let name = format!("{}", qual);
        self.define(&name, vec![], body, span)?;
        let t = self.b.c(&name);
        self.type_sets.insert(qual.to_string(), t.clone());
        Ok(t)
    }

    fn record_set(&mut self, cx: &Cx, fields: &[Field], span: Span) -> R<Term> {
        let names: Vec<Term> = fields.iter().map(|f| self.b.str(&f.name.name)).collect();
        let keys = self.b.set_of(names);
        let r = self.fresh("r");
        let rv = self.b.v(r);
        let mut conds = vec![self.b.app("is_fun", vec![rv.clone()]), self.b.eq(self.b.app("dom", vec![rv.clone()]), keys.clone())];
        for f in fields {
            let ft = self.ty(cx, &f.ty)?;
            let fs = self.ty_set(&ft, span)?;
            conds.push(self.b.member(self.b.field(rv.clone(), &f.name.name), fs));
        }
        let cond = self.b.ands(conds);
        let univ = self.b.app("univ", vec![self.b.nat(1)]);
        let space = self.b.app("powerset", vec![self.b.app("cart", vec![keys, univ])]);
        Ok(self.b.bind_app("set_select", vec![space], &[r], &cond))
    }

    pub fn state_set(&mut self, st: &StateTy, span: Span) -> R<Term> {
        if st.base.starts_with('$') || st.base.is_empty() {
            return Ok(self.b.app("univ", vec![self.b.nat(1)]));
        }
        let mut s = self.named_set(&st.base, span)?;
        for e in &st.ext {
            let part = match e {
                Ext::Fields(q) => self.ghost_set(q, span)?,
                Ext::Param(_, t) => t.clone(),
            };
            s = self.b.app("rec_and", vec![s, part]);
        }
        Ok(s)
    }

    /// The set of records of the own fields of `state X extends ...`.
    fn ghost_set(&mut self, qual: &str, span: Span) -> R<Term> {
        let key = format!("{}.ghost", qual);
        if let Some(t) = self.type_sets.get(&key) {
            return Ok(t.clone());
        }
        let i = self.g.decls.iter().position(|d| d.qual == qual).unwrap();
        let module = self.g.decls[i].module.clone();
        let fields = match &self.g.decls[i].decl.kind {
            DeclKind::State { fields, .. } => fields.clone(),
            _ => unreachable!(),
        };
        let body = self.record_set(&Cx::new(&module), &fields, span)?;
        self.define(&key, vec![], body, span)?;
        let t = self.b.c(&key);
        self.type_sets.insert(key, t.clone());
        Ok(t)
    }

    /// Fields (name, type, is_trace) of a state type, base first.
    pub fn state_fields(&mut self, st: &StateTy) -> R<Vec<(String, Ty, bool)>> {
        let mut out = Vec::new();
        if let Some(m) = st.base.strip_prefix("$decoder:") {
            let ctx = self.decoder_ctx_ty(m, Span::default())?;
            return Ok(vec![
                ("bytes".into(), Ty::Map(Box::new(Ty::Nat), Box::new(Ty::Bits(self.b.nat(8)))), false),
                ("pos".into(), Ty::Nat, false),
                ("ctx".into(), ctx, false),
            ]);
        }
        if st.base.starts_with('$') {
            return Ok(out);
        }
        let mut quals = vec![st.base.clone()];
        for e in &st.ext {
            if let Ext::Fields(q) = e {
                quals.push(q.clone());
            }
        }
        for q in quals {
            let i = match self.g.decls.iter().position(|d| d.qual == q) {
                Some(i) => i,
                None => continue,
            };
            let module = self.g.decls[i].module.clone();
            if let DeclKind::State { fields, .. } = self.g.decls[i].decl.kind.clone() {
                for f in fields {
                    let t = self.ty(&Cx::new(&module), &f.ty)?;
                    out.push((f.name.name.clone(), t, f.trace));
                }
            }
        }
        Ok(out)
    }

    pub fn record_fields(&mut self, qual: &str) -> R<Vec<(String, Ty, bool)>> {
        let i = self.g.decls.iter().position(|d| d.qual == qual).unwrap();
        let module = self.g.decls[i].module.clone();
        match self.g.decls[i].decl.kind.clone() {
            DeclKind::Record { fields, .. } | DeclKind::State { fields, .. } => fields
                .iter()
                .map(|f| Ok((f.name.name.clone(), self.ty(&Cx::new(&module), &f.ty)?, f.trace)))
                .collect(),
            _ => Ok(Vec::new()),
        }
    }

    /// Fields of a record-like type (record or state).
    pub fn fields_of(&mut self, t: &Ty) -> R<Option<Vec<(String, Ty, bool)>>> {
        Ok(match t.strip() {
            Ty::Rec(q) => Some(self.record_fields(&q.clone())?),
            Ty::State(st) => Some(self.state_fields(&st.clone())?),
            _ => None,
        })
    }

    /// Paths of trace fields of a state type (e.g. `os.events`).
    pub fn trace_paths(&mut self, t: &Ty) -> R<Vec<(Vec<String>, Ty)>> {
        let mut out = Vec::new();
        self.trace_paths_in(t, &mut Vec::new(), &mut out, 0)?;
        Ok(out)
    }

    fn trace_paths_in(&mut self, t: &Ty, path: &mut Vec<String>, out: &mut Vec<(Vec<String>, Ty)>, depth: usize) -> R<()> {
        if depth > 4 {
            return Ok(());
        }
        if let Some(fs) = self.fields_of(t)? {
            for (n, ft, tr) in fs {
                path.push(n);
                if tr {
                    out.push((path.clone(), ft.clone()));
                } else {
                    self.trace_paths_in(&ft, path, out, depth + 1)?;
                }
                path.pop();
            }
        }
        Ok(())
    }

    /// The trace record of a state term: `{"os.events": s.os.events, ...}`.
    pub fn traces_of(&mut self, st_ty: &Ty, s: &Term) -> R<Term> {
        let paths = self.trace_paths(st_ty)?;
        let mut rec = Vec::new();
        for (p, _) in paths {
            let mut v = s.clone();
            for f in &p {
                v = self.b.field(v, f);
            }
            rec.push((p.join("."), v));
        }
        Ok(self.b.record(rec))
    }

    /// Enum values of declaration `i` (explicit `= e` or consecutive).
    pub fn enum_values(&mut self, i: usize) -> R<Vec<(String, sl_kernel::Nat)>> {
        let items = match &self.g.decls[i].decl.kind {
            DeclKind::Enum { items, .. } => items.clone(),
            _ => return Ok(Vec::new()),
        };
        let mut out = Vec::new();
        let mut next = sl_kernel::Nat::zero();
        for it in items {
            if let Some(v) = &it.value {
                match &v.kind {
                    ExprKind::Num(n) => next = n.clone(),
                    _ => return err(v.span, "enum values must be literals"),
                }
            }
            out.push((it.name.name.clone(), next.clone()));
            next = next.add(&sl_kernel::Nat::from_u64(1));
        }
        Ok(out)
    }

    // ------------------------------------------------------------------
    //  Generic substitution in types

    pub fn subst_ty(&self, t: &Ty, vals: &HashMap<VarId, Term>, tys: &HashMap<String, Ty>) -> Ty {
        let st = |x: &Term| -> Term {
            let mut r = x.clone();
            for (v, val) in vals {
                r = r.subst_var(*v, val, &self.b.env.binders_fn());
            }
            self.b.norm(&r)
        };
        let rec = |x: &Ty| Box::new(self.subst_ty(x, vals, tys));
        match t {
            Ty::Bits(w) => Ty::Bits(st(w)),
            Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|x| self.subst_ty(x, vals, tys)).collect()),
            Ty::Map(a, b) => Ty::Map(rec(a), rec(b)),
            Ty::List(a) => Ty::List(rec(a)),
            Ty::Seq(a) => Ty::Seq(rec(a)),
            Ty::Set(a) => Ty::Set(rec(a)),
            Ty::Opt(a) => Ty::Opt(rec(a)),
            Ty::Refine(a, s) => Ty::Refine(rec(a), st(s)),
            Ty::Proc { state, params, ret } => Ty::Proc {
                state: rec(state),
                params: params.iter().map(|x| self.subst_ty(x, vals, tys)).collect(),
                ret: rec(ret),
            },
            Ty::Prog(a, b) => Ty::Prog(rec(a), rec(b)),
            Ty::Outcome(a, b) => Ty::Outcome(rec(a), rec(b)),
            Ty::Param(n, s) => match tys.get(n) {
                Some(t) => t.clone(),
                None => Ty::Param(n.clone(), st(s)),
            },
            Ty::State(s) => {
                let mut out = StateTy { base: s.base.clone(), ext: Vec::new() };
                for e in &s.ext {
                    match e {
                        Ext::Param(n, set) => match tys.get(n) {
                            Some(Ty::State(x)) => out.ext.extend(x.ext.clone()),
                            Some(Ty::Param(m, s2)) => out.ext.push(Ext::Param(m.clone(), s2.clone())),
                            _ => out.ext.push(Ext::Param(n.clone(), st(set))),
                        },
                        other => out.ext.push(other.clone()),
                    }
                }
                Ty::State(out)
            }
            other => other.clone(),
        }
    }

    /// Unifies a parameter type (with generics) against an argument type,
    /// binding value generics (widths) and type generics.
    pub fn unify(&self, p: &Ty, a: &Ty, gens: &[GenParam], vals: &mut HashMap<VarId, Term>, tys: &mut HashMap<String, Ty>) {
        let is_gen_var = |t: &Term| -> Option<VarId> {
            match t.node() {
                sl_kernel::Node::Var(v, args) if args.is_empty() && gens.iter().any(|g| g.var == *v) => Some(*v),
                _ => None,
            }
        };
        match (p.strip(), a.strip()) {
            (Ty::Bits(pw), Ty::Bits(aw)) => {
                if let Some(v) = is_gen_var(pw) {
                    vals.entry(v).or_insert_with(|| aw.clone());
                }
                // `bits[8*n]` against `bits[8*m]` or `bits[64]`: n = m, n = 8
                if let sl_kernel::Node::App(s, args) = pw.node() {
                    if self.b.env.syms[*s as usize].name == "int_mul" {
                        if let (sl_kernel::Node::Nat(k), Some(v)) = (args[0].node(), is_gen_var(&args[1])) {
                            let aw = self.b.norm(aw);
                            let found = match aw.node() {
                                sl_kernel::Node::App(s2, a2)
                                    if self.b.env.syms[*s2 as usize].name == "int_mul" && a2[0] == args[0] =>
                                {
                                    Some(a2[1].clone())
                                }
                                sl_kernel::Node::Nat(m) => match m.divmod(k) {
                                    Some((q, r)) if r.is_zero() => Some(Term::nat(q)),
                                    _ => None,
                                },
                                _ => None,
                            };
                            if let Some(t) = found {
                                vals.entry(v).or_insert(t);
                            }
                        }
                    }
                }
            }
            (Ty::Param(n, _), _) if gens.iter().any(|g| g.name == *n && g.val_ty.is_none()) => {
                if !matches!(a, Ty::Unknown) {
                    tys.entry(n.clone()).or_insert_with(|| a.clone());
                }
            }
            (Ty::State(ps), Ty::State(as_)) => {
                // `B & G` against `B & exts`: G gets the extra extensions
                let pn: Vec<&Ext> = ps.ext.iter().filter(|e| !matches!(e, Ext::Param(..))).collect();
                if let Some(Ext::Param(n, _)) = ps.ext.iter().find(|e| matches!(e, Ext::Param(..))) {
                    let rest: Vec<Ext> = as_.ext.iter().filter(|e| !pn.contains(e)).cloned().collect();
                    if gens.iter().any(|g| &g.name == n) {
                        tys.entry(n.clone()).or_insert_with(|| Ty::State(StateTy { base: String::new(), ext: rest }));
                    }
                }
            }
            (Ty::Tuple(x), Ty::Tuple(y)) if x.len() == y.len() => {
                for (p, a) in x.iter().zip(y) {
                    self.unify(p, a, gens, vals, tys)
                }
            }
            (Ty::Map(a1, b1), Ty::Map(a2, b2)) | (Ty::Outcome(a1, b1), Ty::Outcome(a2, b2)) | (Ty::Prog(a1, b1), Ty::Prog(a2, b2)) => {
                self.unify(a1, a2, gens, vals, tys);
                self.unify(b1, b2, gens, vals, tys)
            }
            (Ty::List(x), Ty::List(y)) | (Ty::Seq(x), Ty::Seq(y)) | (Ty::Set(x), Ty::Set(y)) | (Ty::Opt(x), Ty::Opt(y)) => {
                self.unify(x, y, gens, vals, tys)
            }
            (Ty::Proc { state: s1, params: p1, ret: r1 }, Ty::Proc { state: s2, params: p2, ret: r2 }) => {
                self.unify(s1, s2, gens, vals, tys);
                for (x, y) in p1.iter().zip(p2) {
                    self.unify(x, y, gens, vals, tys)
                }
                self.unify(r1, r2, gens, vals, tys)
            }
            _ => {}
        }
    }

    /// Set term of an instantiated state extension (for `refines` with ghost).
    pub fn ext_set(&mut self, exts: &[Ext], span: Span) -> R<Term> {
        let mut parts = Vec::new();
        for e in exts {
            parts.push(match e {
                Ext::Fields(q) => self.ghost_set(q, span)?,
                Ext::Param(_, t) => t.clone(),
            });
        }
        let first = parts.first().cloned().unwrap_or_else(|| self.b.app("single", vec![self.b.empty()]));
        Ok(parts.into_iter().skip(1).fold(first, |acc, p| self.b.app("rec_and", vec![acc, p])))
    }

    /// Field names of the base part of a state type (for ghost splitting).
    pub fn base_keys(&mut self, st: &StateTy) -> R<Term> {
        let fs = self.state_fields(&StateTy { base: st.base.clone(), ext: Vec::new() })?;
        let names: Vec<Term> = fs.iter().map(|(n, _, _)| self.b.str(n)).collect();
        Ok(self.b.set_of(names))
    }

    // ------------------------------------------------------------------
    //  Signatures

    pub fn sig_of(&mut self, i: usize, which: &str) -> R<Sig> {
        let key = format!("{}#{}", self.g.decls[i].qual, which);
        if let Some(s) = self.sigs.get(&key) {
            return Ok(s.clone());
        }
        let sig = self.compute_sig(i, which)?;
        self.sigs.insert(key, sig.clone());
        Ok(sig)
    }

    /// A context holding a declaration's generics and layer parameters.
    pub fn header_cx(&mut self, i: usize, generics: &[sl_syntax::ast::Generic]) -> R<(Cx, Vec<String>, Vec<GenParam>)> {
        let module = self.module_of(i);
        let mut cx = Cx::new(&module);
        let lift: Vec<String> = self.g.param_deps[i].iter().cloned().collect();
        for q in &lift {
            let v = *self.lift_vars.entry(q.clone()).or_insert_with(|| self.b.env.new_var(&q.replace('.', "_"), 0));
            cx.lift.insert(q.clone(), self.b.v(v));
        }
        let mut gens = Vec::new();
        for gp in generics {
            let v = self.fresh(&gp.name.name);
            match &gp.kind {
                None => {
                    let t = self.b.v(v);
                    cx.gtys.insert(gp.name.name.clone(), (Ty::Param(gp.name.name.clone(), t.clone()), t));
                    gens.push(GenParam { name: gp.name.name.clone(), var: v, val_ty: None });
                }
                Some(Type::EnumKind(_)) => {
                    let t = self.b.v(v);
                    cx.gtys.insert(gp.name.name.clone(), (Ty::Param(gp.name.name.clone(), t.clone()), t));
                    gens.push(GenParam { name: gp.name.name.clone(), var: v, val_ty: None });
                }
                Some(k) => {
                    let kt = self.ty(&cx, k)?;
                    cx.gvals.insert(gp.name.name.clone(), (self.b.v(v), kt.clone()));
                    gens.push(GenParam { name: gp.name.name.clone(), var: v, val_ty: Some(kt) });
                }
            }
        }
        Ok((cx, lift, gens))
    }

    fn compute_sig(&mut self, i: usize, which: &str) -> R<Sig> {
        let decl = self.g.decls[i].decl.clone();
        let qual = self.g.decls[i].qual.clone();
        let span = decl.span;
        let params_of = |s: &mut Self, cx: &Cx, ps: &[Param]| -> R<Vec<(String, VarId, Ty)>> {
            ps.iter()
                .map(|p| {
                    let t = s.ty(cx, &p.ty)?;
                    let v = s.fresh(&p.name.name);
                    Ok((p.name.name.clone(), v, t))
                })
                .collect()
        };
        // dependent parameter types (`n: nat` then `bits[8*n]`) refer to earlier params
        let with_params = |cx: &mut Cx, s: &Self, ps: &[(String, VarId, Ty)]| {
            for (n, v, t) in ps {
                cx.push_local(n, s.b.v(*v), t.clone(), false);
            }
        };
        match &decl.kind {
            DeclKind::Fn(f) => {
                let (mut cx, lift, gens) = self.header_cx(i, &f.generics)?;
                let mut state_var = None;
                if f.kind == FnKind::Decoder {
                    let st = self.decoder_state(&cx, span)?;
                    let v = self.fresh("state");
                    cx.state = Some(self.b.v(v));
                    cx.state_ty = Some(st);
                    state_var = Some(v);
                }
                let params = self.params_seq(&mut cx, &f.params)?;
                with_params(&mut cx, self, &params);
                let ret = match (&f.kind, &f.ret) {
                    (FnKind::Pred, _) => Ty::Bool,
                    (_, Some(r)) => self.ty(&cx, r)?,
                    (_, None) => Ty::Unit,
                };
                let kind = match f.kind {
                    FnKind::Decoder => SigKind::Proc(self.decoder_state(&cx, span)?),
                    _ => SigKind::Fn,
                };
                Ok(Sig { core: qual, lift, generics: gens, params, ret, kind, state_var })
            }
            DeclKind::Proc(p) => {
                let (mut cx, lift, gens) = self.header_cx(i, &p.generics)?;
                let st = match &p.state {
                    Some(t) => self.ty(&cx, t)?,
                    None => self.default_state(&cx, span)?,
                };
                let v = self.fresh("state");
                cx.state = Some(self.b.v(v));
                cx.state_ty = Some(st.clone());
                let state_var = Some(v);
                let params = self.params_seq(&mut cx, &p.params)?;
                with_params(&mut cx, self, &params);
                let ret = match &p.ret {
                    Some(r) => self.ty(&cx, r)?,
                    None => Ty::Unit,
                };
                Ok(Sig { core: qual, lift, generics: gens, params, ret, kind: SigKind::Proc(st), state_var })
            }
            DeclKind::View { state, params, ty, .. } => {
                let (mut cx, lift, gens) = self.header_cx(i, &[])?;
                let st = match state {
                    Some(t) => self.ty(&cx, t)?,
                    None => self.default_state(&cx, span)?,
                };
                let v = self.fresh("state");
                cx.state = Some(self.b.v(v));
                cx.state_ty = Some(st.clone());
                let state_var = Some(v);
                let mut ps = self.params_seq(&mut cx, params)?;
                with_params(&mut cx, self, &ps);
                let vt = self.ty(&cx, ty)?;
                if which == "set" {
                    let v = self.fresh("v");
                    ps.push(("$v".into(), v, vt));
                    Ok(Sig { core: format!("{}.set", qual), lift, generics: gens, params: ps, ret: Ty::Unit, kind: SigKind::Proc(st), state_var })
                } else {
                    Ok(Sig { core: format!("{}.get", qual), lift, generics: gens, params: ps, ret: vt, kind: SigKind::Proc(st), state_var })
                }
            }
            DeclKind::Const { ty, value, .. } => {
                let (mut cx, lift, gens) = self.header_cx(i, &[])?;
                let t = match ty {
                    Some(t) => self.ty(&cx, t)?,
                    None => {
                        // infer from the value
                        let (_, t) = self.expr(&mut cx, value, None)?;
                        t
                    }
                };
                Ok(Sig { core: qual, lift, generics: gens, params: Vec::new(), ret: t, kind: SigKind::Const, state_var: None })
            }
            DeclKind::ParamPred { params, .. } => {
                let (cx, lift, gens) = self.header_cx(i, &[])?;
                let ps = params_of(self, &cx, params)?;
                Ok(Sig { core: qual, lift, generics: gens, params: ps, ret: Ty::Bool, kind: SigKind::Fn, state_var: None })
            }
            DeclKind::ParamFn { params, ret, .. } => {
                let (cx, lift, gens) = self.header_cx(i, &[])?;
                let ps = params_of(self, &cx, params)?;
                let r = self.ty(&cx, ret)?;
                Ok(Sig { core: qual, lift, generics: gens, params: ps, ret: r, kind: SigKind::Fn, state_var: None })
            }
            _ => err(span, format!("`{}` cannot be called", qual)),
        }
    }

    /// Parameters, each type may mention the earlier ones.
    fn params_seq(&mut self, cx: &mut Cx, ps: &[Param]) -> R<Vec<(String, VarId, Ty)>> {
        let mut out = Vec::new();
        let n0 = cx.locals.len();
        for p in ps {
            let t = self.ty(cx, &p.ty)?;
            let v = self.fresh(&p.name.name);
            cx.push_local(&p.name.name, self.b.v(v), t.clone(), false);
            out.push((p.name.name.clone(), v, t));
        }
        cx.locals.truncate(n0);
        Ok(out)
    }

    /// The decoder state type: bytes, position, context.
    pub fn decoder_state(&mut self, cx: &Cx, span: Span) -> R<Ty> {
        let _ = span;
        Ok(Ty::State(StateTy { base: format!("$decoder:{}", cx.module), ext: Vec::new() }))
    }

    pub fn decoder_ctx_ty(&mut self, module: &str, span: Span) -> R<Ty> {
        let ctx_decl = self
            .g
            .decls
            .iter()
            .find(|d| d.module == module && matches!(d.decl.kind, DeclKind::DecoderContext(_)))
            .map(|d| d.decl.clone());
        match ctx_decl {
            Some(Decl { kind: DeclKind::DecoderContext(t), .. }) => self.ty(&Cx::new(module), &t),
            _ => err(span, "no `decoder context` declared in this module"),
        }
    }

    /// Arguments passed for a signature's layer parameters.
    pub fn lift_args(&self, cx: &Cx, sig: &Sig, span: Span) -> R<Vec<Term>> {
        sig.lift
            .iter()
            .map(|q| match cx.lift.get(q) {
                Some(t) => Ok(t.clone()),
                None => err(span, format!("`{}` depends on layer parameter `{}`, which is not in scope", sig.core, q)),
            })
            .collect()
    }

    /// Resolves a bare name to global candidates, preferring ones that fit `exp`.
    pub fn global_candidates(&self, module: &str, name: &str) -> Vec<GName> {
        self.g.lookup(module, name)
    }
}

pub fn t_span(t: &Type) -> Span {
    match t {
        Type::Named(n, _) => n.span,
        Type::Refine(n, _, _) => n.span,
        _ => Span::default(),
    }
}
