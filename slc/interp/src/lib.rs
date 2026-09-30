//! An interpreter for SL, working directly on the checked AST.
//!
//! * decoding: pure functions, decoders and table matching (`decode`);
//! * execution: procedures over a concrete machine state (`step`), for
//!   differential testing against the real CPU.
//!
//! Values left open by the spec (`havoc`, `any`) are `Unknown`; the
//! nondeterministic choices (`either`, branching on an unknown condition,
//! `any x where x in S`) are explored by replaying with different choice
//! scripts. Untrusted tooling: claims are stated through the logic.

pub mod elf;
pub mod num;

use num::Int;
use sl_elab::globals::{GName, Globals};
use sl_syntax::ast::*;
use std::collections::BTreeMap;
use std::rc::Rc;

// ----------------------------------------------------------------------
//  Values

#[derive(Clone, Debug, PartialEq)]
pub enum V {
    /// a number; `w` is its bit width when known (bits[w])
    Num(Int, Option<u32>),
    Bool(bool),
    Tuple(Vec<V>),
    Rec(BTreeMap<String, V>),
    /// sum values, options (none = 0, some = 1) and exceptions
    Tag(String, u64, Vec<V>),
    Set(Vec<V>),
    Map(Rc<MapV>),
    Str(String),
    Unit,
    /// a value the spec leaves open
    Unknown,
    Closure(Rc<Closure>),
    /// a set too large to list, `{var | cond}`: membership evaluates `cond`
    SetOf(Rc<LazySet>),
}

#[derive(Debug, PartialEq)]
pub struct LazySet {
    var: String,
    cond: Expr,
    env: Vec<(String, V)>,
    module: String,
    tys: Vec<(String, usize)>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct MapV {
    /// explicit entries (and everything written)
    pub m: BTreeMap<String, V>,
    /// entries not in `m`: from the backing bytes, else the default
    pub backing: Option<Rc<Backing>>,
    pub default: Option<V>,
}

/// Map entries `base + i -> bits[8](bytes[i])` for each region, read lazily
/// (large memory images without a value per byte).
#[derive(Debug, PartialEq)]
pub struct Backing {
    /// (base, bytes), ascending and disjoint
    pub regions: Vec<(u64, Vec<u8>)>,
}

impl MapV {
    pub fn get(&self, k: &V) -> Option<V> {
        if let Some(v) = self.m.get(&k.key()) {
            return Some(v.clone());
        }
        if let (Some(b), V::Num(n, _)) = (&self.backing, k) {
            if let Some(a) = n.to_u64() {
                let k = b.regions.partition_point(|r| r.0 <= a);
                if let Some((base, bytes)) = k.checked_sub(1).map(|k| &b.regions[k]) {
                    if a - base < bytes.len() as u64 {
                        return Some(V::bits(bytes[(a - base) as usize] as u128, 8));
                    }
                }
            }
        }
        self.default.clone()
    }
}

#[derive(Debug, PartialEq)]
pub struct Closure {
    params: Vec<String>,
    body: Block,
    env: Vec<(String, V)>,
    module: String,
}

impl V {
    pub fn n(v: i128) -> V {
        V::Num(Int::from_i128(v), None)
    }
    pub fn bits(v: u128, w: u32) -> V {
        V::Num(Int::from_u128(v), Some(w))
    }
    pub fn int(&self) -> Result<Int, String> {
        match self {
            V::Num(n, _) => Ok(n.clone()),
            V::Bool(b) => Ok(Int::from_i128(*b as i128)),
            _ => Err(format!("expected a number, got {}", self.render())),
        }
    }
    pub fn num(&self) -> Result<i128, String> {
        self.int()?.to_i128().ok_or_else(|| "number too large".to_string())
    }
    pub fn bool(&self) -> Result<bool, String> {
        match self {
            V::Bool(b) => Ok(*b),
            _ => Err(format!("expected a bool, got {}", self.render())),
        }
    }
    /// key of a value in a map (widths do not matter)
    pub fn key(&self) -> String {
        match self {
            V::Num(n, _) => n.to_string(),
            V::Bool(b) => b.to_string(),
            other => other.render(),
        }
    }
    pub fn render(&self) -> String {
        match self {
            V::Num(n, Some(w)) if *w >= 8 => n.to_hex(),
            V::Num(n, _) => n.to_string(),
            V::Bool(b) => b.to_string(),
            V::Tuple(vs) => format!("({})", vs.iter().map(|v| v.render()).collect::<Vec<_>>().join(", ")),
            V::Rec(m) => format!("{{{}}}", m.iter().map(|(k, v)| format!("{}: {}", k, v.render())).collect::<Vec<_>>().join(", ")),
            V::Tag(n, _, vs) if vs.is_empty() => n.clone(),
            V::Tag(n, _, vs) => format!("{}({})", n, vs.iter().map(|v| v.render()).collect::<Vec<_>>().join(", ")),
            V::Set(vs) => format!("{{{}}}", vs.iter().map(|v| v.render()).collect::<Vec<_>>().join(", ")),
            V::Map(m) => format!("<map of {}>", m.m.len()),
            V::Str(s) => format!("{:?}", s),
            V::Unit => "()".into(),
            V::Unknown => "?".into(),
            V::Closure(_) => "<fn>".into(),
            V::SetOf(l) => format!("{{{} | ...}}", l.var),
        }
    }
    pub fn field(&self, f: &str) -> Option<&V> {
        match self {
            V::Rec(m) => m.get(f),
            _ => None,
        }
    }
    pub fn map_get(&self, k: &V) -> Option<V> {
        match self {
            V::Map(m) => m.get(k),
            _ => None,
        }
    }
}

/// Equality; `None` when an unknown value makes it undecided.
pub fn same(a: &V, b: &V) -> Option<bool> {
    match (a, b) {
        (V::Unknown, _) | (_, V::Unknown) => None,
        (V::Num(x, _), V::Num(y, _)) => Some(x == y),
        (V::Tag(n, _, x), V::Tag(m, _, y)) => {
            if n != m || x.len() != y.len() {
                return Some(false);
            }
            same_all(x, y)
        }
        (V::Tuple(x), V::Tuple(y)) if x.len() == y.len() => same_all(x, y),
        (V::Rec(x), V::Rec(y)) => {
            let mut all = Some(true);
            for (k, p) in x {
                match y.get(k).map(|q| same(p, q)) {
                    Some(Some(false)) | None => return Some(false),
                    Some(None) => all = None,
                    _ => {}
                }
            }
            all
        }
        _ => Some(a == b),
    }
}

fn same_all(x: &[V], y: &[V]) -> Option<bool> {
    let mut all = Some(true);
    for (p, q) in x.iter().zip(y) {
        match same(p, q) {
            Some(false) => return Some(false),
            None => all = None,
            _ => {}
        }
    }
    all
}

// ----------------------------------------------------------------------
//  Control flow and the run context

/// Non-local control flow.
#[derive(Debug, Clone)]
pub enum Flow {
    Return(V),
    Break,
    /// an exception of the spec (`segv`, `div_error`, ...)
    Raise(V),
    /// a decoder `guard` failed
    NoMatch,
    /// the spec allows any outcome
    Undefined,
    /// the interpreter cannot run this part of the spec
    Unsupported(String),
}

type F<T> = Result<T, Flow>;

fn unsupported<T>(msg: impl Into<String>) -> F<T> {
    Err(Flow::Unsupported(msg.into()))
}

impl From<String> for Flow {
    fn from(s: String) -> Flow {
        Flow::Unsupported(s)
    }
}

/// Decoder state.
struct DState {
    bytes: Vec<u8>,
    pos: usize,
    ctx: V,
}

/// Choices of one run: `script` fixes the first ones; `seen` records the
/// number of alternatives at each choice point.
#[derive(Default)]
struct Oracle {
    script: Vec<usize>,
    pos: usize,
    seen: Vec<usize>,
}

impl Oracle {
    fn choose(&mut self, k: usize) -> usize {
        let c = self.script.get(self.pos).copied().unwrap_or(0);
        self.seen.push(k);
        self.pos += 1;
        c
    }
}

struct Run {
    machine: Option<V>,
    dec: Option<DState>,
    oracle: Oracle,
    fuel: u64,
    /// candidate values for `any x where P` that cannot be enumerated
    hints: Vec<V>,
}

#[derive(Clone)]
struct Env {
    module: String,
    locals: Vec<(String, V)>,
    /// type parameters bound to enum declarations
    tys: Vec<(String, usize)>,
}

impl Env {
    fn get(&self, n: &str) -> Option<&V> {
        self.locals.iter().rev().find(|l| l.0 == n).map(|l| &l.1)
    }
    fn idx(&self, n: &str) -> Option<usize> {
        self.locals.iter().rposition(|l| l.0 == n)
    }
}

// ----------------------------------------------------------------------
//  Public API

/// A flattened table row.
pub struct FlatRow {
    pub prefix: Vec<Item>,
    pub consts: Vec<(String, V)>,
    pub row: Rc<Row>,
}

pub struct Match {
    pub row: usize,
    pub len: usize,
    pub binds: Vec<(String, V)>,
}

/// One outcome of executing a step.
#[derive(Debug, Clone)]
pub enum Outcome {
    Ok(V),
    Exc(V, V),
    Undefined,
    Unsupported(String),
}

pub struct Interp<'g> {
    pub g: &'g Globals,
    pub table: Table,
    pub table_qual: String,
    pub module: String,
    pub rows: Vec<FlatRow>,
    /// ranges up to this size are enumerated; larger ones are evaluated at
    /// breakpoints (and page boundaries) and sampled in between
    pub enum_limit: i128,
    /// set-builders stay lazy (membership evaluates the condition) even
    /// when small
    pub lazy_sets: bool,
    /// results of lambda applications `f[x]`
    memo: std::cell::RefCell<std::collections::HashMap<(usize, String), (Rc<Closure>, V)>>,
}

impl<'g> Interp<'g> {
    pub fn new(g: &'g Globals, table_name: &str) -> Result<Self, String> {
        let (idx, module) = g
            .decls
            .iter()
            .enumerate()
            .find(|(_, d)| matches!(d.decl.kind, DeclKind::Table(_)) && d.decl.name().map(|n| n.name == table_name).unwrap_or(false))
            .map(|(i, d)| (i, d.module.clone()))
            .ok_or_else(|| format!("no table `{}`", table_name))?;
        let table = match &g.decls[idx].decl.kind {
            DeclKind::Table(t) => t.clone(),
            _ => unreachable!(),
        };
        let mut it = Interp { g, table: table.clone(), table_qual: g.decls[idx].qual.clone(), module, rows: Vec::new(), enum_limit: 1 << 12, lazy_sets: false, memo: Default::default() };
        let mut rows = Vec::new();
        it.flatten(&table.entries, &mut Vec::new(), &mut Vec::new(), &mut rows)?;
        it.rows = rows;
        Ok(it)
    }

    fn flatten(&self, entries: &[TableEntry], prefix: &mut Vec<Item>, consts: &mut Vec<(String, V)>, out: &mut Vec<FlatRow>) -> Result<(), String> {
        for e in entries {
            match e {
                TableEntry::Row(r) => out.push(FlatRow { prefix: prefix.clone(), consts: consts.clone(), row: Rc::new(r.clone()) }),
                TableEntry::With { pat, item, entries } => {
                    prefix.push(Item::Bind(pat.clone(), item.clone()));
                    self.flatten(entries, prefix, consts, out)?;
                    prefix.pop();
                }
                TableEntry::For { var, ty, except, entries } => {
                    let j = self.g.find_decl(&self.module, &ty.name).ok_or("for over unknown enum")?;
                    for (name, v) in self.enum_values(j)? {
                        if except.iter().any(|x| x.name == name) {
                            continue;
                        }
                        consts.push((var.name.clone(), V::n(v)));
                        self.flatten(entries, prefix, consts, out)?;
                        consts.pop();
                    }
                }
            }
        }
        Ok(())
    }

    pub fn enum_values(&self, i: usize) -> Result<Vec<(String, i128)>, String> {
        let items = match &self.g.decls[i].decl.kind {
            DeclKind::Enum { items, .. } => items,
            _ => return Err("not an enum".into()),
        };
        let mut out = Vec::new();
        let mut next = 0i128;
        for it in items {
            if let Some(Expr { kind: ExprKind::Num(n), .. }) = &it.value {
                next = n.to_u64().unwrap_or(0) as i128;
            }
            out.push((it.name.name.clone(), next));
            next += 1;
        }
        Ok(out)
    }

    fn env0(&self) -> Env {
        Env { module: self.module.clone(), locals: Vec::new(), tys: Vec::new() }
    }

    fn run0(&self) -> Run {
        Run { machine: None, dec: None, oracle: Oracle::default(), fuel: 2_000_000, hints: Vec::new() }
    }

    /// All rows matching the start of `bytes`.
    pub fn decode(&self, bytes: &[u8]) -> Vec<Match> {
        let Some(ctx0) = self.ctx0() else { return Vec::new() };
        (0..self.rows.len()).filter_map(|k| self.match_row(bytes, k, &ctx0)).collect()
    }

    /// Row `k`, if it matches the start of `bytes` (other rows may match too).
    pub fn decode_row(&self, bytes: &[u8], k: usize) -> Option<Match> {
        self.match_row(bytes, k, &self.ctx0()?)
    }

    fn ctx0(&self) -> Option<V> {
        self.eval(&mut self.env0(), &self.table.context.clone(), &mut self.run0()).ok()
    }

    fn match_row(&self, bytes: &[u8], k: usize, ctx0: &V) -> Option<Match> {
        let fr = &self.rows[k];
        let mut run = self.run0();
        run.dec = Some(DState { bytes: bytes.to_vec(), pos: 0, ctx: ctx0.clone() });
        let mut env = self.env0();
        env.locals.extend(fr.consts.iter().cloned());
        let n0 = env.locals.len();
        let items = self.table.before.iter().chain(fr.prefix.iter()).chain(fr.row.items.iter()).chain(self.table.after.iter());
        for it in items {
            self.item(&mut env, it, &mut run).ok()?;
        }
        Some(Match { row: k, len: run.dec.as_ref().unwrap().pos, binds: env.locals[n0..].to_vec() })
    }

    /// Forgets remembered lambda results (and the lambdas kept for them).
    pub fn clear_memo(&self) {
        self.memo.borrow_mut().clear();
    }

    /// Calls the function or predicate `f` of `module` on values (`fuel`:
    /// the evaluation steps allowed).
    pub fn call_in(&self, module: &str, f: &str, args: Vec<V>, fuel: u64) -> Result<V, String> {
        let sp = Span::default();
        let name = |n: &str| Expr { kind: ExprKind::Name(Ident { name: n.to_string(), span: sp }), span: sp };
        let mut env = Env { module: module.to_string(), locals: Vec::new(), tys: Vec::new() };
        let mut arg_es = Vec::new();
        for (i, a) in args.into_iter().enumerate() {
            let n = format!("__arg{}", i);
            arg_es.push(name(&n));
            env.locals.push((n, a));
        }
        let call = Expr { kind: ExprKind::Call(Box::new(name(f)), arg_es), span: sp };
        let mut run = self.run0();
        run.fuel = fuel;
        self.eval(&mut env, &call, &mut run).map_err(|f| format!("{:?}", f))
    }

    /// Evaluates a (pure) expression with the given bindings.
    pub fn eval_with(&self, e: &Expr, binds: &[(String, V)]) -> Result<V, String> {
        let mut env = self.env0();
        env.locals.extend(binds.iter().cloned());
        self.eval(&mut env, e, &mut self.run0()).map_err(|f| format!("{:?}", f))
    }

    /// All outcomes of the spec's `step()` from machine state `m`
    /// (nondeterministic choices explored, at most `max_runs` runs).
    pub fn step(&self, m: &V, max_runs: usize) -> Vec<Outcome> {
        self.step_with_hints(m, max_runs, &[])
    }

    /// `step`, with candidate values for choices the interpreter cannot
    /// enumerate (`any x where P`: a hint satisfying P is a legitimate choice).
    pub fn step_with_hints(&self, m: &V, max_runs: usize, hints: &[V]) -> Vec<Outcome> {
        let body = match self.g.find_decl(&self.module, "step").map(|i| &self.g.decls[i].decl.kind) {
            Some(DeclKind::Proc(ProcDecl { body: Body::Block(b), .. })) => b.clone(),
            _ => return vec![Outcome::Unsupported("no `step`".into())],
        };
        let mut outs = Vec::new();
        let mut script: Vec<usize> = Vec::new();
        for _ in 0..max_runs {
            let mut run = self.run0();
            run.machine = Some(m.clone());
            run.oracle.script = script.clone();
            run.hints = hints.to_vec();
            let mut env = self.env0();
            let r = self.block(&mut env, &body, &mut run);
            outs.push(match r {
                Ok(()) | Err(Flow::Return(_)) => Outcome::Ok(run.machine.take().unwrap()),
                Err(Flow::Raise(e)) => Outcome::Exc(run.machine.take().unwrap(), e),
                Err(Flow::Undefined) => Outcome::Undefined,
                Err(Flow::Unsupported(s)) => Outcome::Unsupported(s),
                Err(other) => Outcome::Unsupported(format!("{:?}", other)),
            });
            // next script: advance the last choice point with alternatives left
            let seen = run.oracle.seen;
            let mut next: Vec<usize> = (0..seen.len()).map(|k| script.get(k).copied().unwrap_or(0)).collect();
            loop {
                let l = next.len();
                if l == 0 {
                    return outs;
                }
                if next[l - 1] + 1 < seen[l - 1] {
                    next[l - 1] += 1;
                    break;
                }
                next.pop();
            }
            script = next;
        }
        outs.push(Outcome::Unsupported("too many nondeterministic choices".into()));
        outs
    }

    // ------------------------------------------------------------------
    //  Table items

    fn item(&self, env: &mut Env, it: &Item, run: &mut Run) -> F<()> {
        match it {
            Item::Byte(e) => {
                let want = self.eval(env, e, run)?.int()?;
                let b = next_byte(run)?;
                if Int::from_i128(b as i128) != want {
                    return Err(Flow::NoMatch);
                }
                Ok(())
            }
            Item::Run(e) => {
                self.eval(env, e, run)?;
                Ok(())
            }
            Item::Bind(p, e) => {
                let v = self.eval(env, e, run)?;
                if !self.bind(env, p, &v)? {
                    return Err(Flow::NoMatch);
                }
                Ok(())
            }
            Item::Guard(e) => {
                let ok = match &e.kind {
                    ExprKind::Is(a, p) => {
                        let v = self.eval(env, a, run)?;
                        self.bind(env, p, &v)?
                    }
                    _ => self.eval(env, e, run)?.bool()?,
                };
                if !ok {
                    return Err(Flow::NoMatch);
                }
                Ok(())
            }
        }
    }

    // ------------------------------------------------------------------
    //  Patterns

    fn bind(&self, env: &mut Env, p: &Pattern, v: &V) -> F<bool> {
        if matches!(v, V::Unknown) && !matches!(p, Pattern::Wild(_)) {
            if let Pattern::Name(n) = p {
                if self.constant(env, &n.name, None)?.is_none() {
                    env.locals.push((n.name.clone(), V::Unknown));
                    return Ok(true);
                }
            }
            return unsupported("match on a value the spec leaves open");
        }
        match (p, v) {
            (Pattern::Wild(_), _) => Ok(true),
            (Pattern::Num(n, _), _) => Ok(v.int()? == Int::from_i128(n.to_u64().unwrap_or(0) as i128)),
            (Pattern::Bool(b, _), _) => Ok(v.bool()? == *b),
            (Pattern::Tuple(ps, _), V::Tuple(vs)) if ps.len() == vs.len() => {
                for (p, v) in ps.iter().zip(vs) {
                    if !self.bind(env, p, v)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Pattern::Name(n), _) => {
                if let Some(c) = self.constant(env, &n.name, Some(v))? {
                    return Ok(same(&c, v) == Some(true));
                }
                env.locals.push((n.name.clone(), v.clone()));
                Ok(true)
            }
            (Pattern::Ctor(n, ps), V::Tag(name, _, vs)) => {
                if n.name != *name || ps.len() != vs.len() {
                    return Ok(false);
                }
                for (p, v) in ps.iter().zip(vs) {
                    if !self.bind(env, p, v)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// Enum value / nullary constructor named `n` (of the scrutinee's kind).
    fn constant(&self, env: &Env, n: &str, like: Option<&V>) -> F<Option<V>> {
        if n == "none" {
            return Ok(Some(V::Tag("none".into(), 0, vec![])));
        }
        for c in self.g.lookup(&env.module, n) {
            match (c, like) {
                (GName::EnumVal(i, j), Some(V::Num(..)) | None) => {
                    let vals = self.enum_values(i)?;
                    return Ok(Some(V::n(vals[j].1)));
                }
                (GName::Ctor(i, j), Some(V::Tag(..)) | None) => {
                    if let DeclKind::TypeDecl { def: TypeDef::Sum(vs), .. } = &self.g.decls[i].decl.kind {
                        if vs[j].params.is_empty() {
                            return Ok(Some(V::Tag(n.into(), j as u64, vec![])));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(None)
    }

    // ------------------------------------------------------------------
    //  Expressions

    fn eval(&self, env: &mut Env, e: &Expr, run: &mut Run) -> F<V> {
        run.fuel = run.fuel.checked_sub(1).ok_or(Flow::Unsupported("out of fuel".into()))?;
        match &e.kind {
            ExprKind::Num(n) => Ok(V::Num(Int::from_u128(n.to_u64().map(|x| x as u128).unwrap_or(u128::MAX)), None)),
            ExprKind::Bool(b) => Ok(V::Bool(*b)),
            ExprKind::Str(s) => Ok(V::Str(s.clone())),
            ExprKind::SelfState => run.machine.clone().ok_or(Flow::Unsupported("self".into())),
            ExprKind::Name(n) => self.name(env, &n.name, run),
            ExprKind::Unary(op, a) => {
                let v = self.eval(env, a, run)?;
                Ok(match (op, v) {
                    (_, V::Unknown) => V::Unknown,
                    (UnOp::Not, V::Bool(b)) => V::Bool(!b),
                    (UnOp::Neg, V::Num(n, Some(w))) => V::Num(n.neg().wrap(w), Some(w)),
                    (UnOp::Neg, V::Num(n, None)) => V::Num(n.neg(), None),
                    (UnOp::BNot, V::Num(n, Some(w))) => V::Num(n.not_w(w), Some(w)),
                    (op, v) => return unsupported(format!("{:?} of {}", op, v.render())),
                })
            }
            ExprKind::Binary(op, a, b) => self.binary(env, *op, a, b, run),
            ExprKind::Call(f, args) => self.call(env, f, args, run),
            ExprKind::Index(a, idx) if matches!(&idx[0].kind, ExprKind::Binary(BinOp::Range, ..)) => {
                // `xs[a..b]`
                let ExprKind::Binary(_, lo, hi) = &idx[0].kind else { unreachable!() };
                let v = self.eval(env, a, run)?;
                let (lo, hi) = (self.eval(env, lo, run)?, self.eval(env, hi, run)?);
                match (v, lo, hi) {
                    (V::Tuple(vs), V::Num(l, _), V::Num(h, _)) => {
                        let (l, h) = (l.to_u64().unwrap_or(0) as usize, h.to_u64().unwrap_or(0) as usize);
                        if l > h || h > vs.len() {
                            return unsupported("list slice out of range");
                        }
                        Ok(V::Tuple(vs[l..h].to_vec()))
                    }
                    _ => Ok(V::Unknown),
                }
            }
            ExprKind::From(a, i) => {
                // `xs[a..]`
                match (self.eval(env, a, run)?, self.eval(env, i, run)?) {
                    (V::Tuple(vs), V::Num(l, _)) => Ok(V::Tuple(vs[(l.to_u64().unwrap_or(0) as usize).min(vs.len())..].to_vec())),
                    _ => Ok(V::Unknown),
                }
            }
            ExprKind::List(es) => Ok(V::Tuple(es.iter().map(|e| self.eval(env, e, run)).collect::<F<Vec<_>>>()?)),
            ExprKind::ListComp { elem, pat, iter, cond } => {
                let items = match &iter.kind {
                    ExprKind::Binary(BinOp::Range, a, b) => {
                        let (a, b) = (self.eval(env, a, run)?.num()?, self.eval(env, b, run)?.num()?);
                        if b - a > 1 << 16 {
                            return unsupported("comprehension over a large range");
                        }
                        (a..b).map(V::n).collect()
                    }
                    _ => match self.eval(env, iter, run)? {
                        V::Tuple(vs) => vs,
                        V::Unknown => return Ok(V::Unknown),
                        v => return unsupported(format!("comprehension over {}", v.render())),
                    },
                };
                let mut out = Vec::new();
                for x in items {
                    let n0 = env.locals.len();
                    let matched = self.bind(env, pat, &x)?;
                    let keep = matched
                        && match cond {
                            None => true,
                            Some(c) => match self.eval(env, c, run) {
                                Ok(V::Bool(b)) => b,
                                Ok(V::Unknown) => {
                                    env.locals.truncate(n0);
                                    return Ok(V::Unknown);
                                }
                                Ok(v) => v.bool()?,
                                Err(e) => {
                                    env.locals.truncate(n0);
                                    return Err(e);
                                }
                            },
                        };
                    let r = if keep { Some(self.eval(env, elem, run)) } else { None };
                    env.locals.truncate(n0);
                    if let Some(r) = r {
                        out.push(r?);
                    }
                }
                Ok(V::Tuple(out))
            }
            ExprKind::Index(a, idx) => {
                let v = self.eval(env, a, run)?;
                let i = self.eval(env, &idx[0], run)?;
                match (&v, &i) {
                    (V::Unknown, _) | (_, V::Unknown) => Ok(V::Unknown),
                    (V::Map(_), _) => v.map_get(&i).ok_or_else(|| Flow::Unsupported(format!("no map entry {}", i.render()))),
                    (V::Num(n, _), _) => Ok(V::Bool(n.bit(i.int()?.to_u64().unwrap_or(u64::MAX)))),
                    (V::Tuple(vs), _) => {
                        let k = i.num()? as usize;
                        vs.get(k).cloned().ok_or(Flow::Unsupported("tuple index".into()))
                    }
                    // a map given as a function (a lambda)
                    (V::Closure(c), _) => {
                        // lambdas are pure: remember their results (keeping
                        // the closure alive so its address is not reused)
                        let key = (Rc::as_ptr(c) as usize, i.key());
                        if let Some((_, v)) = self.memo.borrow().get(&key) {
                            return Ok(v.clone());
                        }
                        let v = self.call_closure(c, vec![i.clone()], run)?;
                        self.memo.borrow_mut().insert(key, (c.clone(), v.clone()));
                        Ok(v)
                    }
                    _ => unsupported(format!("index of {}", v.render())),
                }
            }
            ExprKind::Slice(a, hi, lo) => {
                let v = self.eval(env, a, run)?;
                let h = self.eval(env, hi, run)?.num()? as u64;
                let l = self.eval(env, lo, run)?.num()? as u64;
                let w = (h + 1 - l) as u32;
                match v {
                    V::Unknown => Ok(V::Unknown),
                    V::Num(n, _) => Ok(V::Num(n.shr(l).wrap(w), Some(w))),
                    v => unsupported(format!("slice of {}", v.render())),
                }
            }
            ExprKind::Field(a, f) => {
                let v = self.eval(env, a, run)?;
                match (v, f.name.as_str()) {
                    (V::Unknown, _) => Ok(V::Unknown),
                    (V::Rec(m), name) => m.get(name).cloned().ok_or_else(|| Flow::Unsupported(format!("no field {}", name))),
                    (V::Tag(_, 1, vs), "value") => Ok(vs[0].clone()),
                    (v, name) => unsupported(format!("field {} of {}", name, v.render())),
                }
            }
            ExprKind::Tuple(xs) => {
                if xs.is_empty() {
                    return Ok(V::Unit);
                }
                Ok(V::Tuple(xs.iter().map(|x| self.eval(env, x, run)).collect::<F<_>>()?))
            }
            ExprKind::Set(xs) => Ok(V::Set(xs.iter().map(|x| self.eval(env, x, run)).collect::<F<_>>()?)),
            ExprKind::SetBuilder { var, cond, .. } => self.set_builder(env, &var.name, cond, run),
            ExprKind::Record { fields, .. } => {
                let mut m = BTreeMap::new();
                for (f, x) in fields {
                    m.insert(f.name.clone(), self.eval(env, x, run)?);
                }
                Ok(V::Rec(m))
            }
            ExprKind::With(a, fields) => {
                let mut m = match self.eval(env, a, run)? {
                    V::Rec(m) => m,
                    v => return unsupported(format!("`with` on {}", v.render())),
                };
                for (f, x) in fields {
                    let v = self.eval(env, x, run)?;
                    m.insert(f.name.clone(), v);
                }
                Ok(V::Rec(m))
            }
            ExprKind::If(c, a, b) => {
                if self.cond(env, c, run)? {
                    self.block_value(env, a, run)
                } else {
                    self.block_value(env, b, run)
                }
            }
            ExprKind::Match(s, arms) => {
                let v = self.eval(env, s, run)?;
                for arm in arms {
                    for p in &arm.pats {
                        let n0 = env.locals.len();
                        if self.bind(env, p, &v)? {
                            let r = self.block_value(env, &arm.body, run);
                            env.locals.truncate(n0);
                            return r;
                        }
                        env.locals.truncate(n0);
                    }
                }
                unsupported("no match arm")
            }
            ExprKind::Is(a, p) => {
                let v = self.eval(env, a, run)?;
                let n0 = env.locals.len();
                let r = self.bind(env, p, &v)?;
                env.locals.truncate(n0);
                Ok(V::Bool(r))
            }
            ExprKind::Binder { kind: BinderKind::Sum, vars, domain: Some(d), body } => {
                let items: Vec<V> = match &d.kind {
                    ExprKind::Binary(BinOp::Range, a, b) => {
                        let (lo, hi) = (self.eval(env, a, run)?.num()?, self.eval(env, b, run)?.num()?);
                        (lo..hi).map(V::n).collect()
                    }
                    _ => match self.eval(env, d, run)? {
                        V::Tuple(vs) => vs,
                        V::Unknown => return Ok(V::Unknown),
                        v => return unsupported(format!("sum over {}", v.render())),
                    },
                };
                let mut acc = Int::zero();
                for i in items {
                    env.locals.push((vars[0].0.name.clone(), i));
                    let v = self.eval(env, body, run);
                    env.locals.pop();
                    match v? {
                        V::Unknown => return Ok(V::Unknown),
                        v => acc = acc.add(&v.int()?),
                    }
                }
                Ok(V::Num(acc, None))
            }
            ExprKind::Binder { kind: kind @ (BinderKind::All | BinderKind::Ex), vars, domain: None, body } => {
                let names: Vec<String> = vars.iter().map(|v| v.0.name.clone()).collect();
                self.quant(env, *kind == BinderKind::All, &names, body, run)
            }
            ExprKind::Any { var, cond, .. } => self.any(env, var.as_ref().map(|v| v.name.as_str()), cond.as_deref(), run),
            ExprKind::Lambda(ps, b) => Ok(V::Closure(Rc::new(Closure {
                params: ps.iter().map(|p| p.name.name.clone()).collect(),
                body: (**b).clone(),
                env: env.locals.clone(),
                module: env.module.clone(),
            }))),
            ExprKind::Block(b) => self.block_value(env, b, run),
            other => {
                let d = format!("{:?}", other);
                unsupported(format!("expression not supported by the interpreter: {}", d.split(['(', ' ', '{']).next().unwrap_or("")))
            }
        }
    }

    fn is_table(&self, env: &Env, n: &str) -> bool {
        self.g.find_decl(&env.module, n).map(|i| matches!(self.g.decls[i].decl.kind, DeclKind::Table(_))).unwrap_or(false)
    }

    /// A condition; an unknown one is a nondeterministic choice.
    fn cond(&self, env: &mut Env, c: &Expr, run: &mut Run) -> F<bool> {
        match self.eval(env, c, run)? {
            V::Unknown => Ok(run.oracle.choose(2) == 1),
            v => Ok(v.bool()?),
        }
    }

    /// `all x. P -> Q` / `ex x. P && Q` over a range: the bounds of each
    /// variable must be conjuncts of the premise (`lo <= x`, `x < hi`, ...;
    /// the lower bound defaults to 0). Unknown if the body is undecided.
    fn quant(&self, env: &mut Env, all: bool, vars: &[String], body: &Expr, run: &mut Run) -> F<V> {
        let Some((x, rest)) = vars.split_first() else {
            return match self.eval(env, body, run)? {
                V::Unknown => Ok(V::Unknown),
                v => Ok(V::Bool(v.bool()?)),
            };
        };
        let premise = match (&body.kind, all) {
            (ExprKind::Binary(BinOp::Imp, p, _), true) => p.as_ref(),
            // all x. !(P && Q) is all x. P -> !Q
            (ExprKind::Unary(UnOp::Not, inner), true) if matches!(&inner.kind, ExprKind::Binary(BinOp::And, ..)) => match &inner.kind {
                ExprKind::Binary(BinOp::And, p, _) => p.as_ref(),
                _ => unreachable!(),
            },
            (_, false) => body,
            _ => return unsupported("quantifier without a bounding premise"),
        };
        // `M[x] != none` with M a map whose other entries are none: x ranges
        // over M's keys
        if let Some(keys) = self.key_range(env, x, premise, run)? {
            let mut unknown = false;
            for k in keys {
                env.locals.push((x.to_string(), k));
                let v = self.quant(env, all, rest, body, run);
                env.locals.pop();
                match v? {
                    V::Bool(b) if b != all => return Ok(V::Bool(b)),
                    V::Unknown => unknown = true,
                    _ => {}
                }
            }
            return Ok(if unknown { V::Unknown } else { V::Bool(all) });
        }
        let (lo, hi) = self.bounds(env, x, premise, run)?;
        let segs = self.segments(env, x, lo, hi, run, &mut |me, env, run| me.quant(env, all, rest, body, run))?;
        let mut unknown = false;
        for (_, _, v) in segs {
            match v {
                V::Bool(b) if b != all => return Ok(V::Bool(b)),
                V::Unknown => unknown = true,
                _ => {}
            }
        }
        Ok(if unknown { V::Unknown } else { V::Bool(all) })
    }

    /// The truth of `f` for `x` in `lo..hi` (unbounded if `hi` is `None`), as
    /// segments `(from, to, value)` (`to` exclusive, `None`: no end). A small
    /// range is enumerated. A large one is evaluated at breakpoints (the
    /// numbers and map keys in scope, and their neighbours), assuming the
    /// value only changes there; every gap between breakpoints is sampled
    /// at its ends and middle, and a gap whose samples differ makes the
    /// evaluation unsupported rather than wrong.
    fn segments(
        &self,
        env: &mut Env,
        x: &str,
        lo: i128,
        hi: Option<i128>,
        run: &mut Run,
        f: &mut dyn FnMut(&Self, &mut Env, &mut Run) -> F<V>,
    ) -> F<Vec<(i128, Option<i128>, V)>> {
        let mut at = |i: i128, env: &mut Env, run: &mut Run| -> F<V> {
            env.locals.push((x.to_string(), V::n(i)));
            let r = f(self, env, run);
            env.locals.pop();
            let v = r?;
            Ok(match v {
                V::Bool(_) | V::Unknown => v,
                other => V::Bool(other.bool()?),
            })
        };
        if let Some(h) = hi {
            if h - lo <= self.enum_limit {
                let mut out = Vec::new();
                for i in lo..h.max(lo) {
                    out.push((i, Some(i + 1), at(i, env, run)?));
                }
                return Ok(out);
            }
        }
        let end = hi.unwrap_or(i128::MAX);
        let mut pts: Vec<i128> = self.breakpoints(env, run)?.into_iter().filter(|&p| p >= lo && p < end).collect();
        // page boundaries (memory properties change there), if not too many
        if let Some(h) = hi {
            if (h - lo) / 4096 <= 1 << 14 {
                let mut q = (lo + 4095) / 4096 * 4096;
                while q < h {
                    pts.extend([q - 1, q]);
                    q += 4096;
                }
            }
        }
        pts.push(lo);
        if let Some(h) = hi {
            pts.push(h - 1);
        }
        pts.sort();
        pts.dedup();
        let same_v = |a: &V, b: &V| matches!((a, b), (V::Unknown, V::Unknown)) || same(a, b) == Some(true);
        let mut out = Vec::new();
        for (k, &p) in pts.iter().enumerate() {
            out.push((p, Some(p + 1), at(p, env, run)?));
            // the gap after p
            let (g0, g1) = (p + 1, pts.get(k + 1).copied().or(hi));
            match g1 {
                Some(g1) if g1 <= g0 => {}
                Some(g1) => {
                    let a = at(g0, env, run)?;
                    for q in [g0 + (g1 - g0) / 2, g1 - 1] {
                        if !same_v(&at(q, env, run)?, &a) {
                            return unsupported("quantifier over a large range: not constant between breakpoints");
                        }
                    }
                    out.push((g0, Some(g1), a));
                }
                None => {
                    let a = at(g0, env, run)?;
                    for q in [g0 + 1, g0 + (1 << 20), 1i128 << 40, 1i128 << 62] {
                        if q > g0 && !same_v(&at(q, env, run)?, &a) {
                            return unsupported("unbounded quantifier: not constant after the last breakpoint");
                        }
                    }
                    out.push((g0, None, a));
                }
            }
        }
        Ok(out)
    }

    /// Numbers in scope (locals and the machine state, including map keys)
    /// and their neighbours: where a predicate over a number can change.
    fn breakpoints(&self, env: &Env, run: &Run) -> F<Vec<i128>> {
        fn walk(v: &V, out: &mut Vec<i128>, budget: &mut usize) {
            if *budget == 0 {
                return;
            }
            *budget -= 1;
            match v {
                V::Num(n, _) => {
                    if let Some(i) = n.to_i128() {
                        out.push(i);
                    }
                }
                V::Tuple(vs) | V::Set(vs) | V::Tag(_, _, vs) => vs.iter().for_each(|x| walk(x, out, budget)),
                V::Rec(m) => m.values().for_each(|x| walk(x, out, budget)),
                V::Map(m) => {
                    if m.m.len() <= 4096 {
                        for (k, x) in &m.m {
                            if let Ok(i) = k.parse::<i128>() {
                                out.push(i);
                            }
                            walk(x, out, budget);
                        }
                    }
                    if let Some(b) = &m.backing {
                        for (base, bytes) in &b.regions {
                            out.push(*base as i128);
                            out.push(*base as i128 + bytes.len() as i128);
                        }
                    }
                }
                _ => {}
            }
        }
        let mut raw = Vec::new();
        let mut budget = 200_000usize;
        for (_, v) in &env.locals {
            walk(v, &mut raw, &mut budget);
        }
        if let Some(m) = &run.machine {
            walk(m, &mut raw, &mut budget);
        }
        if budget == 0 {
            return unsupported("too many breakpoints");
        }
        let mut out: Vec<i128> = raw.into_iter().flat_map(|i| [i - 1, i, i + 1]).filter(|&i| i >= 0).collect();
        out.sort();
        out.dedup();
        Ok(out)
    }

    /// The keys of M, if a conjunct of `cond` is `M[x] != none` and every
    /// entry of M not listed is none.
    fn key_range(&self, env: &mut Env, x: &str, cond: &Expr, run: &mut Run) -> F<Option<Vec<V>>> {
        let mut conj = Vec::new();
        conjuncts(cond, &mut conj);
        for c in conj {
            let ExprKind::Binary(BinOp::Ne, a, b) = &c.kind else { continue };
            if !matches!(&b.kind, ExprKind::Name(n) if n.name == "none") {
                continue;
            }
            let ExprKind::Index(m, idx) = &a.kind else { continue };
            if idx.len() != 1 || !matches!(&idx[0].kind, ExprKind::Name(n) if n.name == x) {
                continue;
            }
            if let Ok(V::Map(mv)) = self.eval(env, m, run) {
                if mv.backing.is_none() && matches!(&mv.default, Some(V::Tag(t, _, _)) if t == "none") {
                    let keys = mv.m.iter().filter(|(_, v)| !matches!(v, V::Tag(t, _, _) if t == "none"));
                    return Ok(Some(keys.filter_map(|(k, _)| k.parse::<i128>().ok()).map(V::n).collect()));
                }
            }
        }
        Ok(None)
    }

    /// Bounds `lo <= x < hi` of a natural-number variable from the
    /// conjuncts of `cond` (`lo` defaults to 0).
    fn bounds(&self, env: &mut Env, x: &str, cond: &Expr, run: &mut Run) -> F<(i128, Option<i128>)> {
        let mut conj = Vec::new();
        conjuncts(cond, &mut conj);
        let is_x = |e: &Expr| matches!(&e.kind, ExprKind::Name(n) if n.name == x);
        let (mut lo, mut hi) = (0i128, None::<i128>);
        for c in conj {
            let ExprKind::Binary(op, a, b) = &c.kind else { continue };
            // `x in S`: the bounds of S
            if *op == BinOp::In && is_x(a) {
                let (l2, h2) = match self.eval(env, b, run) {
                    Ok(V::SetOf(l)) => {
                        let mut e2 = Env { module: l.module.clone(), locals: l.env.clone(), tys: l.tys.clone() };
                        self.bounds(&mut e2, &l.var, &l.cond, run)?
                    }
                    Ok(V::Set(vs)) => {
                        let ns: Vec<i128> = vs.iter().filter_map(|v| v.num().ok()).collect();
                        match (ns.iter().min(), ns.iter().max()) {
                            (Some(&l), Some(&h)) if ns.len() == vs.len() => (l, Some(h + 1)),
                            _ => (0, Some(0)),
                        }
                    }
                    _ => continue,
                };
                lo = lo.max(l2);
                if let Some(h2) = h2 {
                    hi = Some(hi.map_or(h2, |x| x.min(h2)));
                }
                continue;
            }
            // normalize to `x op e` or `e op x`
            let (bound, lower, strict) = match (op, is_x(a), is_x(b)) {
                (BinOp::Lt, true, false) => (b, false, true),
                (BinOp::Le, true, false) => (b, false, false),
                (BinOp::Gt, true, false) => (b, true, true),
                (BinOp::Ge, true, false) => (b, true, false),
                (BinOp::Lt, false, true) => (a, true, true),
                (BinOp::Le, false, true) => (a, true, false),
                (BinOp::Gt, false, true) => (a, false, true),
                (BinOp::Ge, false, true) => (a, false, false),
                _ => continue,
            };
            let v = match self.eval(env, bound, run) {
                Ok(V::Num(n, _)) => n.to_i128().ok_or_else(|| Flow::Unsupported("huge bound".into()))?,
                _ => continue,
            };
            if lower {
                lo = lo.max(if strict { v + 1 } else { v });
            } else {
                let h = if strict { v } else { v + 1 };
                hi = Some(hi.map_or(h, |x| x.min(h)));
            }
        }
        Ok((lo, hi))
    }

    /// `any x where P`: a choice from `S` if P is `x in S`; else a choice
    /// among the run's hints and the ends of P's range that satisfy P; else
    /// unknown.
    fn any(&self, env: &mut Env, var: Option<&str>, cond: Option<&Expr>, run: &mut Run) -> F<V> {
        if let (Some(v), Some(c)) = (var, cond) {
            if !matches!(&c.kind, ExprKind::Binary(BinOp::In, ..)) {
                let mut cands = run.hints.clone();
                if let Ok((lo, Some(hi))) = self.bounds(env, v, c, run) {
                    cands.extend([V::n(lo), V::n(hi - 1)]);
                }
                let mut ok: Vec<V> = Vec::new();
                for h in cands {
                    env.locals.push((v.to_string(), h.clone()));
                    let r = self.eval(env, c, run);
                    env.locals.pop();
                    if matches!(r, Ok(V::Bool(true))) && !ok.iter().any(|o| same(o, &h) == Some(true)) {
                        ok.push(h);
                    }
                }
                if !ok.is_empty() {
                    let k = run.oracle.choose(ok.len());
                    return Ok(ok[k].clone());
                }
            }
        }
        if let (Some(v), Some(Expr { kind: ExprKind::Binary(BinOp::In, a, s), .. })) = (var, cond) {
            if matches!(&a.kind, ExprKind::Name(n) if n.name == v) {
                if let V::Set(items) = self.eval(env, s, run)? {
                    if items.is_empty() {
                        return Err(Flow::Undefined);
                    }
                    let k = run.oracle.choose(items.len());
                    return Ok(items[k].clone());
                }
            }
        }
        Ok(V::Unknown)
    }

    /// The segments of `{var: nat | cond}` (see `segments`).
    fn set_segments(&self, env: &mut Env, var: &str, cond: &Expr, run: &mut Run) -> F<Vec<(i128, Option<i128>, V)>> {
        let (lo, hi) = self.bounds(env, var, cond, run)?;
        self.segments(env, var, lo, hi, run, &mut |me, env, run| me.eval(env, cond, run))
    }

    fn set_builder(&self, env: &mut Env, var: &str, cond: &Expr, run: &mut Run) -> F<V> {
        let lazy = |env: &Env| {
            Ok(V::SetOf(Rc::new(LazySet {
                var: var.to_string(),
                cond: cond.clone(),
                env: env.locals.clone(),
                module: env.module.clone(),
                tys: env.tys.clone(),
            })))
        };
        // small sets are listed; large (or not listable) ones stay lazy
        if self.lazy_sets {
            return lazy(env);
        }
        match self.bounds(env, var, cond, run) {
            Ok((lo, Some(hi))) if hi - lo <= 1 << 12 => {}
            _ => return lazy(env),
        }
        let mut out = Vec::new();
        for (a, b, v) in self.set_segments(env, var, cond, run)? {
            match (v, b) {
                (V::Bool(false), _) => {}
                (V::Bool(true), Some(b)) if b - a <= 1 << 12 => out.extend((a..b).map(V::n)),
                (V::Bool(true), _) => return unsupported("a large set"),
                _ => return Ok(V::Unknown),
            }
        }
        Ok(V::Set(out))
    }

    fn name(&self, env: &Env, n: &str, run: &mut Run) -> F<V> {
        if let Some(v) = env.get(n) {
            return Ok(v.clone());
        }
        if n == "ctx" {
            if let Some(d) = &run.dec {
                return Ok(d.ctx.clone());
            }
        }
        if let Some(m) = &run.machine {
            if let Some(v) = m.field(n) {
                return Ok(v.clone());
            }
        }
        if let Some(c) = self.constant(env, n, None)? {
            return Ok(c);
        }
        if let Some(i) = self.g.find_decl(&env.module, n) {
            match &self.g.decls[i].decl.kind {
                DeclKind::Const { value, .. } => {
                    let mut e2 = Env { module: self.g.decls[i].module.clone(), locals: vec![], tys: vec![] };
                    return self.eval(&mut e2, &value.clone(), &mut self.run0());
                }
                DeclKind::Exception { params, .. } if params.is_empty() => return Ok(V::Tag(n.into(), 0, vec![])),
                _ => {}
            }
        }
        unsupported(format!("unknown name `{}`", n))
    }

    fn binary(&self, env: &mut Env, op: BinOp, a: &Expr, b: &Expr, run: &mut Run) -> F<V> {
        use BinOp::*;
        if matches!(op, And | Or | Imp) {
            let x = self.eval(env, a, run)?;
            let short = match (&x, op) {
                (V::Bool(false), And) => Some(false),
                (V::Bool(true), Or) => Some(true),
                (V::Bool(false), Imp) => Some(true),
                _ => None,
            };
            if let Some(r) = short {
                return Ok(V::Bool(r));
            }
            let y = self.eval(env, b, run)?;
            return Ok(match (x, y) {
                (V::Bool(p), V::Bool(q)) => V::Bool(match op {
                    And => p && q,
                    Or => p || q,
                    _ => !p || q,
                }),
                (_, V::Bool(false)) if op == And => V::Bool(false),
                (_, V::Bool(true)) if op == Or => V::Bool(true),
                _ => V::Unknown,
            });
        }
        if matches!(op, In | NotIn) {
            let x = self.eval(env, a, run)?;
            let r = match &b.kind {
                ExprKind::Binary(Range, lo, hi) => {
                    let (l, h) = (self.eval(env, lo, run)?.int()?, self.eval(env, hi, run)?.int()?);
                    let n = x.int()?;
                    l <= n && n < h
                }
                ExprKind::Name(t) if env.tys.iter().any(|x| x.0 == t.name) => {
                    let i = env.tys.iter().find(|x| x.0 == t.name).unwrap().1;
                    let n = x.num()?;
                    self.enum_values(i)?.iter().any(|v| v.1 == n)
                }
                _ => match self.eval(env, b, run)? {
                    V::Set(vs) => {
                        let mut r = Some(false);
                        for v in &vs {
                            match same(v, &x) {
                                Some(true) => {
                                    r = Some(true);
                                    break;
                                }
                                None => r = None,
                                _ => {}
                            }
                        }
                        match r {
                            Some(r) => r,
                            None => return Ok(V::Unknown),
                        }
                    }
                    V::SetOf(l) => {
                        let mut e2 = Env { module: l.module.clone(), locals: l.env.clone(), tys: l.tys.clone() };
                        e2.locals.push((l.var.clone(), x.clone()));
                        match self.eval(&mut e2, &l.cond, run)? {
                            V::Unknown => return Ok(V::Unknown),
                            v => v.bool()?,
                        }
                    }
                    v => return unsupported(format!("`in` on {}", v.render())),
                },
            };
            return Ok(V::Bool(if op == In { r } else { !r }));
        }
        let x = self.eval(env, a, run)?;
        let y = self.eval(env, b, run)?;
        if matches!(op, Eq | Ne) {
            return Ok(match same(&x, &y) {
                Some(eq) => V::Bool(if op == Eq { eq } else { !eq }),
                None => V::Unknown,
            });
        }
        if matches!(x, V::Unknown) || matches!(y, V::Unknown) {
            return Ok(V::Unknown);
        }
        if op == Iff {
            return Ok(V::Bool(x.bool()? == y.bool()?));
        }
        if let (Concat, V::Tuple(xs), V::Tuple(ys)) = (op, &x, &y) {
            return Ok(V::Tuple(xs.iter().chain(ys).cloned().collect()));
        }
        let (p, wp) = match x {
            V::Num(n, w) => (n, w),
            V::Bool(b) => (Int::from_i128(b as i128), None),
            v => return unsupported(format!("{:?} on {}", op, v.render())),
        };
        let wq = match &y {
            V::Num(_, w) => *w,
            _ => None,
        };
        let q = y.int()?;
        let w = wp.or(wq);
        let wr = |n: Int| match w {
            Some(w) => V::Num(n.wrap(w), Some(w)),
            None => V::Num(n, None),
        };
        let sgn = |n: &Int, w: Option<u32>| -> Int {
            match w {
                Some(w) if w > 0 && n.bit(w as u64 - 1) => n.sub(&Int::pow2(w as u64)),
                _ => n.clone(),
            }
        };
        let k = || q.to_u64().unwrap_or(u64::MAX).min(1 << 20);
        Ok(match op {
            Lt => V::Bool(p < q),
            Le => V::Bool(p <= q),
            Gt => V::Bool(p > q),
            Ge => V::Bool(p >= q),
            SLt => V::Bool(sgn(&p, w) < sgn(&q, w)),
            SLe => V::Bool(sgn(&p, w) <= sgn(&q, w)),
            SGt => V::Bool(sgn(&p, w) > sgn(&q, w)),
            SGe => V::Bool(sgn(&p, w) >= sgn(&q, w)),
            Add => wr(p.add(&q)),
            Sub => wr(p.sub(&q)),
            Mul => wr(p.mul(&q)),
            Div | Mod => match p.div_euclid(&q) {
                Some((d, m)) => wr(if op == Div { d } else { m }),
                None => return unsupported("division by zero in the spec"),
            },
            BAnd => wr(p.bitop(&q, |a, b| a & b)),
            BOr => wr(p.bitop(&q, |a, b| a | b)),
            BXor => wr(p.bitop(&q, |a, b| a ^ b)),
            Shl => wr(p.shl(k())),
            Shr => wr(p.shr(k())),
            Sar => {
                let s = sgn(&p, wp);
                wr(s.div_euclid(&Int::pow2(k())).unwrap().0)
            }
            Pow => V::Num(p.pow(k()), None),
            _ => return unsupported(format!("operator {:?}", op)),
        })
    }

    fn block_value(&self, env: &mut Env, b: &Block, run: &mut Run) -> F<V> {
        let n0 = env.locals.len();
        let mut last = V::Unit;
        let r = (|| {
            for s in &b.stmts {
                match &s.kind {
                    StmtKind::Expr(e) => last = self.eval(env, e, run)?,
                    StmtKind::If { cond, then, els: Some(els) } => {
                        last = if self.cond(env, cond, run)? { self.block_value(env, then, run)? } else { self.block_value(env, els, run)? }
                    }
                    StmtKind::Match { scrut, arms } => {
                        let e = Expr { kind: ExprKind::Match(Box::new(scrut.clone()), arms.clone()), span: s.span };
                        last = self.eval(env, &e, run)?;
                    }
                    StmtKind::Return(Some(e)) => last = self.eval(env, e, run)?,
                    _ => self.stmt(env, s, run)?,
                }
            }
            Ok(())
        })();
        env.locals.truncate(n0);
        r.map(|_| last)
    }

    // ------------------------------------------------------------------
    //  Statements

    fn block(&self, env: &mut Env, b: &Block, run: &mut Run) -> F<()> {
        let n0 = env.locals.len();
        let mut r = Ok(());
        for s in &b.stmts {
            r = self.stmt(env, s, run);
            if r.is_err() {
                break;
            }
        }
        // keep assignments to outer variables, drop inner declarations
        env.locals.truncate(n0);
        r
    }

    fn stmt(&self, env: &mut Env, s: &Stmt, run: &mut Run) -> F<()> {
        run.fuel = run.fuel.checked_sub(1).ok_or(Flow::Unsupported("out of fuel".into()))?;
        match &s.kind {
            StmtKind::Let { pat, value, .. } => {
                let v = match (&value.kind, pat) {
                    (ExprKind::Any { var: None, cond, maybe, els, .. }, Pattern::Name(n)) => {
                        // `any? .. else S` may take S (which leaves)
                        if let (true, Some(b)) = (*maybe, els) {
                            if run.oracle.choose(2) == 0 {
                                return self.block(env, b, run);
                            }
                        }
                        self.any(env, Some(&n.name), cond.as_deref(), run)?
                    }
                    _ => self.eval(env, value, run)?,
                };
                if !self.bind(env, pat, &v)? {
                    return unsupported("let pattern did not match");
                }
                Ok(())
            }
            StmtKind::Var { name, value, .. } => {
                let v = self.eval(env, value, run)?;
                env.locals.push((name.name.clone(), v));
                Ok(())
            }
            StmtKind::Assign { target, value, .. } => {
                let v = self.eval(env, value, run)?;
                self.assign(env, target, v, run)
            }
            StmtKind::Emit { target, event } => {
                // append the event to the trace field
                let ev = self.eval(env, event, run)?;
                let v = match self.eval(env, target, run)? {
                    V::Tuple(mut vs) => {
                        vs.push(ev);
                        V::Tuple(vs)
                    }
                    _ => V::Unknown,
                };
                self.assign(env, target, v, run)
            }
            StmtKind::If { cond, then, els } => {
                if self.cond(env, cond, run)? {
                    self.block(env, then, run)
                } else if let Some(e) = els {
                    self.block(env, e, run)
                } else {
                    Ok(())
                }
            }
            StmtKind::Match { scrut, arms } => {
                let v = self.eval(env, scrut, run)?;
                for arm in arms {
                    for p in &arm.pats {
                        let n0 = env.locals.len();
                        if self.bind(env, p, &v)? {
                            let r = self.block(env, &arm.body, run);
                            env.locals.truncate(n0);
                            return r;
                        }
                        env.locals.truncate(n0);
                    }
                }
                Err(Flow::Undefined) // no arm matches: undefined
            }
            StmtKind::While { cond, body } => loop {
                if !self.cond(env, cond, run)? {
                    return Ok(());
                }
                match self.block(env, body, run) {
                    Ok(()) => {}
                    Err(Flow::Break) => return Ok(()),
                    Err(e) => return Err(e),
                }
            },
            StmtKind::Loop(b) => loop {
                match self.block(env, b, run) {
                    Ok(()) => {}
                    Err(Flow::Break) => return Ok(()),
                    Err(e) => return Err(e),
                }
            },
            StmtKind::For { var, iter, body } => {
                let (lo, hi) = match &iter.kind {
                    ExprKind::Binary(BinOp::Range, a, b) => (self.eval(env, a, run)?.num()?, self.eval(env, b, run)?.num()?),
                    _ => return unsupported("for over a non-range"),
                };
                for i in lo..hi {
                    env.locals.push((var.name.clone(), V::n(i)));
                    let r = self.block(env, body, run);
                    env.locals.pop();
                    match r {
                        Ok(()) => {}
                        Err(Flow::Break) => break,
                        Err(e) => return Err(e),
                    }
                }
                Ok(())
            }
            StmtKind::Break => Err(Flow::Break),
            StmtKind::Return(v) => {
                let r = match v {
                    Some(e) => self.eval(env, e, run)?,
                    None => V::Unit,
                };
                Err(Flow::Return(r))
            }
            StmtKind::Raise(e) => {
                let v = self.eval(env, e, run)?;
                Err(Flow::Raise(v))
            }
            StmtKind::Try { body, catches } => match self.block(env, body, run) {
                Err(Flow::Raise(e)) => {
                    for (p, b) in catches {
                        let n0 = env.locals.len();
                        if self.bind(env, p, &e)? {
                            let r = self.block(env, b, run);
                            env.locals.truncate(n0);
                            return r;
                        }
                        env.locals.truncate(n0);
                    }
                    Err(Flow::Raise(e))
                }
                other => other,
            },
            StmtKind::Either(blocks) => {
                let k = run.oracle.choose(blocks.len());
                self.block(env, &blocks[k], run)
            }
            StmtKind::Havoc { targets, maybe, els, .. } => {
                // `havoc? .. else S` may take S (a choice); a plain `else` is
                // taken only when no value exists, which the interpreter
                // does not decide: it assumes one does
                if let (true, Some(b)) = (*maybe, els) {
                    if run.oracle.choose(2) == 0 {
                        return self.block(env, b, run);
                    }
                }
                for t in targets {
                    match &t.kind {
                        ExprKind::FieldSet(base, fs) => {
                            for f in fs {
                                let e = Expr { kind: ExprKind::Field(base.clone(), f.clone()), span: t.span };
                                self.assign(env, &e, V::Unknown, run)?;
                            }
                        }
                        _ => self.assign(env, t, V::Unknown, run)?,
                    }
                }
                Ok(())
            }
            StmtKind::Require(c) => {
                if self.cond(env, c, run)? {
                    Ok(())
                } else {
                    Err(Flow::Undefined)
                }
            }
            StmtKind::Guard(e) => match self.eval(env, e, run)? {
                V::Bool(true) => Ok(()),
                _ => Err(Flow::NoMatch),
            },
            StmtKind::Undefined => Err(Flow::Undefined),
            StmtKind::Expr(e) => {
                self.eval(env, e, run)?;
                Ok(())
            }
            StmtKind::Block(b) => self.block(env, b, run),
        }
    }

    // ------------------------------------------------------------------
    //  Assignment

    /// Assigns through a path: variable / state field / `ctx` field, then
    /// fields, map entries, bits and slices; or a view's setter.
    fn assign(&self, env: &mut Env, target: &Expr, v: V, run: &mut Run) -> F<()> {
        let mut steps = Vec::new();
        let mut cur = target;
        loop {
            match &cur.kind {
                ExprKind::Field(a, f) => {
                    steps.push(Step::Field(f.name.clone()));
                    cur = a;
                }
                ExprKind::Index(a, idx) if idx.len() == 1 => {
                    let k = self.eval(env, &idx[0], run)?;
                    steps.push(Step::Key(k));
                    cur = a;
                }
                ExprKind::Slice(a, hi, lo) => {
                    let h = self.eval(env, hi, run)?.num()? as u64;
                    let l = self.eval(env, lo, run)?.num()? as u64;
                    steps.push(Step::Slice(h, l));
                    cur = a;
                }
                ExprKind::Call(f, args) if steps.is_empty() => {
                    if let ExprKind::Name(n) = &f.kind {
                        if let Some(i) = self.g.find_decl(&env.module, &n.name) {
                            if matches!(self.g.decls[i].decl.kind, DeclKind::View { .. }) {
                                return self.view_set(env, i, args, v, run);
                            }
                        }
                    }
                    return unsupported("assignment through a call");
                }
                ExprKind::Name(_) | ExprKind::SelfState => break,
                _ => return unsupported("unsupported assignment target"),
            }
        }
        steps.reverse();
        let root: &mut V = match &cur.kind {
            ExprKind::SelfState => run.machine.as_mut().ok_or(Flow::Unsupported("self".into()))?,
            ExprKind::Name(n) => {
                if let Some(i) = env.idx(&n.name) {
                    &mut env.locals[i].1
                } else if n.name == "ctx" && run.dec.is_some() {
                    &mut run.dec.as_mut().unwrap().ctx
                } else {
                    match run.machine.as_mut() {
                        Some(V::Rec(m)) if m.contains_key(&n.name) => m.get_mut(&n.name).unwrap(),
                        _ => return unsupported(format!("assignment to unknown `{}`", n.name)),
                    }
                }
            }
            _ => unreachable!(),
        };
        put(root, &steps, v)
    }

    // ------------------------------------------------------------------
    //  Calls

    fn call(&self, env: &mut Env, f: &Expr, args: &[Expr], run: &mut Run) -> F<V> {
        // table members
        if let ExprKind::Field(t, m) = &f.kind {
            if let ExprKind::Name(tn) = &t.kind {
                if env.get(&tn.name).is_none() && self.is_table(env, &tn.name) {
                    return self.table_call(env, &m.name, args, run);
                }
            }
        }
        let (name, gargs) = match &f.kind {
            ExprKind::Name(n) => (n.name.clone(), vec![]),
            ExprKind::Index(inner, g) => match &inner.kind {
                ExprKind::Name(n) => (n.name.clone(), g.clone()),
                _ => return unsupported("unsupported call"),
            },
            _ => return unsupported("unsupported call"),
        };
        if let Some(V::Closure(c)) = env.get(&name).cloned() {
            let vals = args.iter().map(|a| self.eval(env, a, run)).collect::<F<Vec<_>>>()?;
            return self.call_closure(&c, vals, run);
        }
        match name.as_str() {
            "next" => return Ok(V::Num(Int::from_i128(next_byte(run)? as i128), Some(8))),
            "peek" => {
                let d = run.dec.as_ref().ok_or(Flow::Unsupported("peek outside a decoder".into()))?;
                return Ok(V::Num(Int::from_i128(*d.bytes.get(d.pos).ok_or(Flow::NoMatch)? as i128), Some(8)));
            }
            "len" => {
                return Ok(match self.eval(env, &args[0], run)? {
                    V::Tuple(vs) => V::n(vs.len() as i128),
                    V::Unknown => V::Unknown,
                    v => return unsupported(format!("len of {}", v.render())),
                })
            }
            "concat" => {
                return Ok(match self.eval(env, &args[0], run)? {
                    V::Tuple(vs) => {
                        let mut out = Vec::new();
                        for v in vs {
                            match v {
                                V::Tuple(xs) => out.extend(xs),
                                _ => return Ok(V::Unknown),
                            }
                        }
                        V::Tuple(out)
                    }
                    _ => V::Unknown,
                })
            }
            "uint" => {
                return Ok(match self.eval(env, &args[0], run)? {
                    V::Num(n, _) => V::Num(n, None),
                    V::Unknown => V::Unknown,
                    v => return unsupported(format!("uint of {}", v.render())),
                })
            }
            "sint" => {
                return Ok(match self.eval(env, &args[0], run)? {
                    V::Num(n, Some(w)) => V::Num(if n.bit(w as u64 - 1) { n.sub(&Int::pow2(w as u64)) } else { n }, None),
                    V::Unknown => V::Unknown,
                    v => return unsupported(format!("sint of {}", v.render())),
                })
            }
            "abs" => {
                return Ok(match self.eval(env, &args[0], run)? {
                    V::Num(n, _) => V::Num(if n.is_neg() { n.neg() } else { n }, None),
                    _ => V::Unknown,
                })
            }
            "min" | "max" => {
                // of a set-builder: from its segments, which may be large
                if let ExprKind::SetBuilder { var, cond, .. } = &args[0].kind {
                    let segs = self.set_segments(env, &var.name, cond, run)?;
                    if segs.iter().any(|s| matches!(s.2, V::Unknown)) {
                        return Ok(V::Unknown);
                    }
                    let t: Vec<&(i128, Option<i128>, V)> = segs.iter().filter(|s| matches!(s.2, V::Bool(true))).collect();
                    return match (name.as_str(), t.first(), t.last()) {
                        ("min", Some(s), _) => Ok(V::n(s.0)),
                        ("max", _, Some((_, Some(b), _))) => Ok(V::n(b - 1)),
                        _ => unsupported("min/max of an empty or unbounded set"),
                    };
                }
                return match self.eval(env, &args[0], run)? {
                    V::Set(vs) if !vs.is_empty() => {
                        let mut ns = vs.iter().map(|v| v.int()).collect::<Result<Vec<_>, _>>()?;
                        ns.sort();
                        Ok(V::Num(if name == "min" { ns[0].clone() } else { ns.pop().unwrap() }, None))
                    }
                    _ => unsupported("min/max of an empty or non-literal set"),
                }
            }
            "some" => return Ok(V::Tag("some".into(), 1, vec![self.eval(env, &args[0], run)?])),
            "bits" | "zext" | "sext" => {
                let w = self.eval(env, &gargs[0], run)?.num()? as u32;
                return Ok(match self.eval(env, &args[0], run)? {
                    V::Unknown => V::Unknown,
                    V::Num(n, src) => {
                        let r = match (name.as_str(), src) {
                            ("sext", Some(s)) if s > 0 && n.bit(s as u64 - 1) => n.sub(&Int::pow2(s as u64)).wrap(w),
                            _ => n.wrap(w),
                        };
                        V::Num(r, Some(w))
                    }
                    V::Bool(b) => V::Num(Int::from_i128(b as i128), Some(w)),
                    v => return unsupported(format!("conversion of {}", v.render())),
                });
            }
            _ => {}
        }
        // type parameter conversion `E(x)`
        if env.tys.iter().any(|t| t.0 == name) {
            return Ok(V::Num(self.eval(env, &args[0], run)?.int()?, None));
        }
        for c in self.g.lookup(&env.module, &name) {
            match c {
                GName::Ctor(_, j) => {
                    let vals = args.iter().map(|a| self.eval(env, a, run)).collect::<F<Vec<_>>>()?;
                    return Ok(V::Tag(name.clone(), j as u64, vals));
                }
                GName::Decl(i) => match &self.g.decls[i].decl.kind {
                    DeclKind::Enum { .. } => return Ok(V::Num(self.eval(env, &args[0], run)?.int()?, None)),
                    DeclKind::Exception { .. } => {
                        let vals = args.iter().map(|a| self.eval(env, a, run)).collect::<F<Vec<_>>>()?;
                        return Ok(V::Tag(name.clone(), 0, vals));
                    }
                    DeclKind::Fn(fd) => {
                        let fd = fd.clone();
                        return self.call_body(env, i, &fd.generics, &fd.params, fd.ret.as_ref(), &fd.body, &gargs, args, run);
                    }
                    DeclKind::Proc(pd) => {
                        let pd = pd.clone();
                        return self.call_body(env, i, &pd.generics, &pd.params, pd.ret.as_ref(), &pd.body, &gargs, args, run);
                    }
                    DeclKind::View { params, ty, get, .. } => {
                        let body = match get {
                            ViewGet::Expr(e) => Body::Expr(e.clone()),
                            ViewGet::Block(b) => Body::Block(b.clone()),
                        };
                        let (params, ty) = (params.clone(), ty.clone());
                        return self.call_body(env, i, &[], &params, Some(&ty), &body, &[], args, run);
                    }
                    _ => {}
                },
                _ => {}
            }
        }
        unsupported(format!("cannot call `{}`", name))
    }

    fn call_closure(&self, c: &Closure, vals: Vec<V>, run: &mut Run) -> F<V> {
        let mut env = Env { module: c.module.clone(), locals: c.env.clone(), tys: vec![] };
        for (p, v) in c.params.iter().zip(vals) {
            env.locals.push((p.clone(), v));
        }
        self.block_value(&mut env, &c.body, run)
    }

    /// Binds parameters (inferring width generics from argument widths),
    /// runs the body, and gives the result its declared width.
    #[allow(clippy::too_many_arguments)]
    fn call_body(
        &self,
        env: &mut Env,
        i: usize,
        generics: &[sl_syntax::ast::Generic],
        params: &[Param],
        ret: Option<&Type>,
        body: &Body,
        gargs: &[Expr],
        args: &[Expr],
        run: &mut Run,
    ) -> F<V> {
        let mut callee = Env { module: self.g.decls[i].module.clone(), locals: Vec::new(), tys: Vec::new() };
        for (g, a) in generics.iter().zip(gargs) {
            if let ExprKind::Name(n) = &a.kind {
                if let Some(j) = self.g.find_decl(&env.module, &n.name) {
                    if matches!(self.g.decls[j].decl.kind, DeclKind::Enum { .. }) {
                        callee.tys.push((g.name.name.clone(), j));
                        continue;
                    }
                }
            }
            let v = self.eval(env, a, run)?;
            callee.locals.push((g.name.name.clone(), v));
        }
        let mut vals = Vec::new();
        for a in args {
            vals.push(self.eval(env, a, run)?);
        }
        // generic widths from argument widths: `bits[w]` / `bits[8*n]`
        for (p, v) in params.iter().zip(&vals) {
            let (Type::Named(tn, ga), V::Num(_, Some(w))) = (&p.ty, v) else { continue };
            if tn.name != "bits" {
                continue;
            }
            if let Some(GenArg::Expr(e)) = ga.first() {
                let is_gen = |n: &str, callee: &Env| generics.iter().any(|g| g.name.name == n) && callee.get(n).is_none();
                match &e.kind {
                    ExprKind::Name(n) if is_gen(&n.name, &callee) => callee.locals.push((n.name.clone(), V::n(*w as i128))),
                    ExprKind::Binary(BinOp::Mul, k, n) => {
                        if let (ExprKind::Num(k), ExprKind::Name(n)) = (&k.kind, &n.kind) {
                            let k = k.to_u64().unwrap_or(1) as u32;
                            if is_gen(&n.name, &callee) && k > 0 {
                                callee.locals.push((n.name.clone(), V::n((*w / k) as i128)));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        for (p, v) in params.iter().zip(vals) {
            let v = self.fit(&mut callee, &p.ty, v);
            callee.locals.push((p.name.name.clone(), v));
        }
        let r = match body {
            Body::Expr(e) => self.eval(&mut callee, e, run),
            Body::Block(b) => match self.block(&mut callee, b, run) {
                Ok(()) => Ok(V::Unit),
                Err(Flow::Return(v)) => Ok(v),
                Err(e) => Err(e),
            },
        }?;
        // the declared width of the result
        Ok(match ret {
            Some(t) => self.fit(&mut callee, t, r),
            None => r,
        })
    }

    /// Give a number the width of its declared type `bits[e]` (evaluated in
    /// `env`), wrapping untyped literals such as `-1`.
    fn fit(&self, env: &mut Env, ty: &Type, v: V) -> V {
        let (Type::Named(tn, ga), V::Num(n, _)) = (ty, &v) else { return v };
        if tn.name != "bits" {
            return v;
        }
        let Some(GenArg::Expr(e)) = ga.first() else { return v };
        match self.eval(env, e, &mut self.run0()).and_then(|x| Ok(x.num()?)) {
            Ok(w) => V::Num(n.wrap(w as u32), Some(w as u32)),
            Err(_) => v,
        }
    }

    fn view_set(&self, env: &mut Env, i: usize, args: &[Expr], v: V, run: &mut Run) -> F<()> {
        let (params, ty, set_var, set) = match &self.g.decls[i].decl.kind {
            DeclKind::View { params, ty, set_var, set, .. } => (params.clone(), ty.clone(), set_var.clone(), set.clone()),
            _ => unreachable!(),
        };
        let mut callee = Env { module: self.g.decls[i].module.clone(), locals: Vec::new(), tys: Vec::new() };
        for (p, a) in params.iter().zip(args) {
            let x = self.eval(env, a, run)?;
            callee.locals.push((p.name.name.clone(), x));
        }
        let v = self.fit(&mut callee, &ty, v);
        callee.locals.push((set_var.name.clone(), v));
        match self.block(&mut callee, &set, run) {
            Ok(()) | Err(Flow::Return(_)) => Ok(()),
            Err(e) => Err(e),
        }
    }

    /// `table.decode(bytes)` and `table.execute(insn)`.
    fn table_call(&self, env: &mut Env, member: &str, args: &[Expr], run: &mut Run) -> F<V> {
        match member {
            "decode" => {
                let f = self.eval(env, &args[0], run)?;
                let mut bytes = Vec::new();
                for i in 0..15 {
                    let b = match &f {
                        V::Closure(c) => self.call_closure(c, vec![V::n(i)], run)?,
                        V::Map(_) => f.map_get(&V::n(i)).unwrap_or(V::Unknown),
                        _ => V::Unknown,
                    };
                    match b {
                        V::Num(n, _) => bytes.push(n.to_u64().unwrap_or(0) as u8),
                        _ => break,
                    }
                }
                let ms = self.decode(&bytes);
                Ok(V::Set(
                    ms.into_iter()
                        .map(|m| {
                            let rec: BTreeMap<String, V> = m.binds.into_iter().collect();
                            V::Tuple(vec![V::n(m.len as i128), V::Tag("$insn".into(), m.row as u64, vec![V::Rec(rec)])])
                        })
                        .collect(),
                ))
            }
            "execute" => {
                let (k, binds) = match self.eval(env, &args[0], run)? {
                    V::Tag(_, k, vs) => (k as usize, vs[0].clone()),
                    v => return unsupported(format!("execute of {}", v.render())),
                };
                let fr = &self.rows[k];
                let mut e2 = self.env0();
                e2.locals.extend(fr.consts.iter().cloned());
                if let V::Rec(m) = binds {
                    e2.locals.extend(m);
                }
                match self.block(&mut e2, &fr.row.body.clone(), run) {
                    Ok(()) => Ok(V::Unit),
                    Err(Flow::Return(v)) => Ok(v),
                    Err(e) => Err(e),
                }
            }
            _ => unsupported(format!("table member `{}`", member)),
        }
    }
}

enum Step {
    Field(String),
    Key(V),
    Slice(u64, u64),
}

fn put(slot: &mut V, steps: &[Step], v: V) -> F<()> {
    let Some((s, rest)) = steps.split_first() else {
        *slot = v;
        return Ok(());
    };
    match s {
        Step::Field(f) => match slot {
            V::Rec(m) => put(m.entry(f.clone()).or_insert(V::Unknown), rest, v),
            V::Unknown => Ok(()),
            other => unsupported(format!("field {} of {}", f, other.render())),
        },
        Step::Key(k) => match slot {
            V::Map(m) => {
                let m = Rc::make_mut(m);
                let mut e = m.get(k).unwrap_or(V::Unknown);
                put(&mut e, rest, v)?;
                m.m.insert(k.key(), e);
                Ok(())
            }
            V::Num(n, _) if rest.is_empty() => {
                let i = k.int()?.to_u64().unwrap_or(0);
                let bit = Int::pow2(i);
                let cleared = n.bitop(&bit, |a, b| a & !b);
                match v {
                    V::Bool(true) => *n = cleared.bitop(&bit, |a, b| a | b),
                    V::Bool(false) => *n = cleared,
                    _ => *slot = V::Unknown,
                }
                Ok(())
            }
            V::Unknown => Ok(()),
            other => unsupported(format!("index assignment on {}", other.render())),
        },
        Step::Slice(h, l) => {
            match (&mut *slot, &v) {
                (V::Num(n, _), V::Num(x, _)) => {
                    let width = h + 1 - l;
                    let mask = Int::pow2(width).sub(&Int::from_i128(1)).shl(*l);
                    let cleared = n.bitop(&mask, |a, b| a & !b);
                    *n = cleared.bitop(&x.wrap(width as u32).shl(*l), |a, b| a | b);
                }
                _ => *slot = V::Unknown,
            }
            Ok(())
        }
    }
}

fn next_byte(run: &mut Run) -> F<u8> {
    let d = run.dec.as_mut().ok_or(Flow::Unsupported("next() outside a decoder".into()))?;
    let b = *d.bytes.get(d.pos).ok_or(Flow::NoMatch)?;
    d.pos += 1;
    Ok(b)
}

/// A map value (for building machine states).
pub fn map(entries: Vec<(V, V)>, default: Option<V>) -> V {
    V::Map(Rc::new(MapV { m: entries.into_iter().map(|(k, v)| (k.key(), v)).collect(), backing: None, default }))
}

/// A map value whose other entries come from `bytes` at `base`.
pub fn map_backed(entries: Vec<(V, V)>, default: Option<V>, base: u64, bytes: Vec<u8>) -> V {
    V::Map(Rc::new(MapV {
        m: entries.into_iter().map(|(k, v)| (k.key(), v)).collect(),
        backing: Some(Rc::new(Backing { regions: vec![(base, bytes)] })),
        default,
    }))
}

/// A map backed by several memory regions (ascending, disjoint).
pub fn map_backed_regions(entries: Vec<(V, V)>, default: Option<V>, mut regions: Vec<(u64, Vec<u8>)>) -> V {
    regions.sort_by_key(|r| r.0);
    V::Map(Rc::new(MapV {
        m: entries.into_iter().map(|(k, v)| (k.key(), v)).collect(),
        backing: Some(Rc::new(Backing { regions })),
        default,
    }))
}

fn conjuncts<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &e.kind {
        ExprKind::Binary(BinOp::And, a, b) => {
            conjuncts(a, out);
            conjuncts(b, out);
        }
        _ => out.push(e),
    }
}
