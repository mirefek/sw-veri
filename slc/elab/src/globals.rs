//! Global declarations, modules, name resolution, parameter dependencies.

use sl_syntax::ast::*;
use std::collections::{BTreeSet, HashMap, HashSet};

pub struct GDecl {
    pub module: String,
    pub qual: String,
    pub decl: Decl,
}

pub struct ModInfo {
    pub kind: ModuleKind,
    /// this module and everything it uses, transitively
    pub visible: Vec<String>,
    /// the module's `state` declaration (default state of its procs)
    pub default_state: Option<String>,
}

/// What a bare name can denote at global level.
#[derive(Clone, Debug, PartialEq)]
pub enum GName {
    Decl(usize),
    /// variant `v` of the sum type declared at `decl`
    Ctor(usize, usize),
    /// value of the enum declared at `decl`
    EnumVal(usize, usize),
}

pub struct Globals {
    pub decls: Vec<GDecl>,
    pub modules: HashMap<String, ModInfo>,
    /// simple name -> candidates (with their module)
    pub names: HashMap<String, Vec<(String, GName)>>,
    /// layer params each declaration depends on (qualified names of param decls)
    pub param_deps: Vec<BTreeSet<String>>,
}

impl Globals {
    pub fn build(files: Vec<File>) -> Result<Globals, String> {
        let mut decls = Vec::new();
        let mut mod_uses: HashMap<String, (ModuleKind, BTreeSet<String>)> = HashMap::new();
        let mut default_state: HashMap<String, String> = HashMap::new();
        for f in files {
            let m = f.module.name.clone();
            let e = mod_uses.entry(m.clone()).or_insert((f.kind, BTreeSet::new()));
            if e.0 != f.kind {
                return Err(format!("module `{}` declared both as spec and as layer", m));
            }
            e.1.extend(f.uses.iter().map(|u| u.name.clone()));
            for d in f.decls {
                if let DeclKind::State { name, .. } = &d.kind {
                    default_state.entry(m.clone()).or_insert(format!("{}.{}", m, name.name));
                }
                let qual = match d.name() {
                    Some(n) => format!("{}.{}", m, n.name),
                    None => format!("{}.$decl{}", m, decls.len()),
                };
                decls.push(GDecl { module: m.clone(), qual, decl: d });
            }
        }
        let mut modules = HashMap::new();
        for (m, (kind, _)) in &mod_uses {
            let mut visible = vec![m.clone()];
            let mut i = 0;
            while i < visible.len() {
                if let Some((_, us)) = mod_uses.get(&visible[i]) {
                    for u in us {
                        if !mod_uses.contains_key(u) {
                            return Err(format!("module `{}` uses unknown module `{}`", visible[i], u));
                        }
                        if !visible.contains(u) {
                            visible.push(u.clone());
                        }
                    }
                }
                i += 1;
            }
            modules.insert(m.clone(), ModInfo { kind: *kind, visible, default_state: default_state.get(m).cloned() });
        }
        let mut names: HashMap<String, Vec<(String, GName)>> = HashMap::new();
        let mut seen: HashSet<String> = HashSet::new();
        for (i, gd) in decls.iter().enumerate() {
            if let Some(n) = gd.decl.name() {
                if !seen.insert(gd.qual.clone()) {
                    return Err(format!("`{}` declared twice", gd.qual));
                }
                names.entry(n.name.clone()).or_default().push((gd.module.clone(), GName::Decl(i)));
            }
            match &gd.decl.kind {
                DeclKind::TypeDecl { def: TypeDef::Sum(vs), .. } => {
                    for (j, v) in vs.iter().enumerate() {
                        names.entry(v.name.name.clone()).or_default().push((gd.module.clone(), GName::Ctor(i, j)));
                    }
                }
                DeclKind::Enum { items, .. } => {
                    for (j, it) in items.iter().enumerate() {
                        names.entry(it.name.name.clone()).or_default().push((gd.module.clone(), GName::EnumVal(i, j)));
                    }
                }
                _ => {}
            }
        }
        let mut g = Globals { decls, modules, names, param_deps: Vec::new() };
        g.compute_param_deps();
        Ok(g)
    }

    /// Candidates for `name` visible from `module`: the module's own
    /// declarations shadow those of the modules it uses.
    pub fn lookup(&self, module: &str, name: &str) -> Vec<GName> {
        let vis = &self.modules[module].visible;
        let Some(cs) = self.names.get(name) else { return Vec::new() };
        let own: Vec<GName> = cs.iter().filter(|(m, _)| m == module).map(|(_, g)| g.clone()).collect();
        if !own.is_empty() {
            return own;
        }
        cs.iter().filter(|(m, _)| vis.contains(m)).map(|(_, g)| g.clone()).collect()
    }

    pub fn find_decl(&self, module: &str, name: &str) -> Option<usize> {
        self.lookup(module, name).into_iter().find_map(|g| match g {
            GName::Decl(i) => Some(i),
            _ => None,
        })
    }

    fn compute_param_deps(&mut self) {
        let n = self.decls.len();
        let refs: Vec<HashSet<String>> = self.decls.iter().map(|d| names_in_decl(&d.decl)).collect();
        let mut deps: Vec<BTreeSet<String>> = vec![BTreeSet::new(); n];
        for (i, d) in self.decls.iter().enumerate() {
            if matches!(d.decl.kind, DeclKind::ParamPred { .. } | DeclKind::ParamFn { .. }) {
                deps[i].insert(d.qual.clone());
            }
        }
        let resolved: Vec<Vec<usize>> = (0..n)
            .map(|i| {
                let m = &self.decls[i].module;
                refs[i].iter().filter_map(|nm| self.find_decl(m, nm)).collect()
            })
            .collect();
        loop {
            let mut changed = false;
            for i in 0..n {
                for &j in &resolved[i] {
                    if j != i {
                        let add: Vec<String> = deps[j].difference(&deps[i]).cloned().collect();
                        if !add.is_empty() {
                            deps[i].extend(add);
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        self.param_deps = deps;
    }
}

// ----------------------------------------------------------------------
//  Names referenced by a declaration (over-approximation)

pub fn names_in_decl(d: &Decl) -> HashSet<String> {
    let mut out = HashSet::new();
    let mut c = Collector { out: &mut out };
    match &d.kind {
        DeclKind::TypeDecl { def, .. } => match def {
            TypeDef::Alias(t) => c.ty(t),
            TypeDef::Sum(vs) => vs.iter().for_each(|v| v.params.iter().for_each(|p| c.ty(&p.ty))),
        },
        DeclKind::Enum { items, repr, .. } => {
            if let Some(r) = repr {
                c.ty(r)
            }
            items.iter().filter_map(|i| i.value.as_ref()).for_each(|e| c.expr(e));
        }
        DeclKind::Record { fields, .. } => fields.iter().for_each(|f| c.ty(&f.ty)),
        DeclKind::State { fields, extends, .. } => {
            fields.iter().for_each(|f| c.ty(&f.ty));
            if let Some(t) = extends {
                c.ty(t)
            }
        }
        DeclKind::Const { ty, value, .. } => {
            if let Some(t) = ty {
                c.ty(t)
            }
            c.expr(value)
        }
        DeclKind::Exception { params, .. } | DeclKind::ParamPred { params, .. } => params.iter().for_each(|p| c.ty(&p.ty)),
        DeclKind::ParamFn { params, ret, .. } => {
            params.iter().for_each(|p| c.ty(&p.ty));
            c.ty(ret)
        }
        DeclKind::Fn(f) => {
            f.params.iter().for_each(|p| c.ty(&p.ty));
            if let Some(r) = &f.ret {
                c.ty(r)
            }
            c.body(&f.body)
        }
        DeclKind::Proc(p) => {
            p.params.iter().for_each(|x| c.ty(&x.ty));
            if let Some(r) = &p.ret {
                c.ty(r)
            }
            if let Some(s) = &p.state {
                c.ty(s)
            }
            c.body(&p.body)
        }
        DeclKind::View { params, ty, get, set, state, .. } => {
            params.iter().for_each(|x| c.ty(&x.ty));
            c.ty(ty);
            if let Some(s) = state {
                c.ty(s)
            }
            match get {
                ViewGet::Expr(e) => c.expr(e),
                ViewGet::Block(b) => c.block(b),
            }
            c.block(set)
        }
        DeclKind::DecoderContext(t) => c.ty(t),
        DeclKind::Notations { .. } => {}
        DeclKind::Table(t) => {
            c.expr(&t.context);
            t.before.iter().chain(t.after.iter()).for_each(|i| c.item(i));
            t.entries.iter().for_each(|e| c.entry(e));
        }
        DeclKind::Law { params, prop, .. } => {
            params.iter().for_each(|p| c.ty(&p.ty));
            c.expr(prop)
        }
        DeclKind::Theorem { params, prop, .. } => {
            params.iter().for_each(|p| c.ty(&p.ty));
            c.expr(prop)
        }
    }
    out
}

struct Collector<'a> {
    out: &'a mut HashSet<String>,
}

impl<'a> Collector<'a> {
    fn ty(&mut self, t: &Type) {
        match t {
            Type::Named(n, args) => {
                self.out.insert(n.name.clone());
                for a in args {
                    match a {
                        GenArg::Type(t) => self.ty(t),
                        GenArg::Expr(e) => self.expr(e),
                    }
                }
            }
            Type::Map(a, b) | Type::And(a, b) => {
                self.ty(a);
                self.ty(b)
            }
            Type::Tuple(ts) => ts.iter().for_each(|t| self.ty(t)),
            Type::Refine(_, t, e) => {
                self.ty(t);
                self.expr(e)
            }
            Type::Proc { state, params, ret } => {
                if let Some(s) = state {
                    self.ty(s)
                }
                params.iter().for_each(|t| self.ty(t));
                if let Some(r) = ret {
                    self.ty(r)
                }
            }
            Type::EnumKind(e) => self.expr(e),
        }
    }
    fn body(&mut self, b: &Body) {
        match b {
            Body::Expr(e) => self.expr(e),
            Body::Block(b) => self.block(b),
        }
    }
    fn block(&mut self, b: &Block) {
        b.stmts.iter().for_each(|s| self.stmt(s))
    }
    fn pat(&mut self, p: &Pattern) {
        match p {
            Pattern::Name(n) => {
                self.out.insert(n.name.clone());
            }
            Pattern::Ctor(n, ps) => {
                self.out.insert(n.name.clone());
                ps.iter().for_each(|p| self.pat(p))
            }
            Pattern::Tuple(ps, _) => ps.iter().for_each(|p| self.pat(p)),
            _ => {}
        }
    }
    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Let { pat, ty, value } => {
                self.pat(pat);
                if let Some(t) = ty {
                    self.ty(t)
                }
                self.expr(value)
            }
            StmtKind::Var { ty, value, .. } => {
                if let Some(t) = ty {
                    self.ty(t)
                }
                self.expr(value)
            }
            StmtKind::Assign { target, value, .. } => {
                self.expr(target);
                self.expr(value)
            }
            StmtKind::Emit { target, event } => {
                self.expr(target);
                self.expr(event)
            }
            StmtKind::If { cond, then, els } => {
                self.expr(cond);
                self.block(then);
                if let Some(e) = els {
                    self.block(e)
                }
            }
            StmtKind::Match { scrut, arms } => {
                self.expr(scrut);
                arms.iter().for_each(|a| {
                    a.pats.iter().for_each(|p| self.pat(p));
                    self.block(&a.body)
                })
            }
            StmtKind::While { cond, body } => {
                self.expr(cond);
                self.block(body)
            }
            StmtKind::For { iter, body, .. } => {
                self.expr(iter);
                self.block(body)
            }
            StmtKind::Loop(b) | StmtKind::Block(b) => self.block(b),
            StmtKind::Return(Some(e)) | StmtKind::Raise(e) | StmtKind::Require(e) | StmtKind::Guard(e) | StmtKind::Expr(e) => {
                self.expr(e)
            }
            StmtKind::Try { body, catches } => {
                self.block(body);
                catches.iter().for_each(|(p, b)| {
                    self.pat(p);
                    self.block(b)
                })
            }
            StmtKind::Either(bs) => bs.iter().for_each(|b| self.block(b)),
            StmtKind::Havoc { targets, cond, els, .. } => {
                targets.iter().for_each(|t| self.expr(t));
                if let Some(c) = cond {
                    self.expr(c)
                }
                if let Some(b) = els {
                    self.block(b)
                }
            }
            StmtKind::Return(None) | StmtKind::Break | StmtKind::Undefined => {}
        }
    }
    fn item(&mut self, i: &Item) {
        match i {
            Item::Byte(e) | Item::Run(e) | Item::Guard(e) => self.expr(e),
            Item::Bind(p, e) => {
                self.pat(p);
                self.expr(e)
            }
        }
    }
    fn entry(&mut self, e: &TableEntry) {
        match e {
            TableEntry::Row(r) => {
                r.items.iter().for_each(|i| self.item(i));
                self.block(&r.body)
            }
            TableEntry::With { item, entries, .. } => {
                self.expr(item);
                entries.iter().for_each(|e| self.entry(e))
            }
            TableEntry::For { ty, entries, .. } => {
                self.out.insert(ty.name.clone());
                entries.iter().for_each(|e| self.entry(e))
            }
        }
    }
    fn expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Name(n) => {
                self.out.insert(n.name.clone());
            }
            ExprKind::Unary(_, a) | ExprKind::Field(a, _) | ExprKind::FieldSet(a, _) => self.expr(a),
            ExprKind::Binary(_, a, b) | ExprKind::From(a, b) => {
                self.expr(a);
                self.expr(b)
            }
            ExprKind::Call(f, args) | ExprKind::Index(f, args) => {
                self.expr(f);
                args.iter().for_each(|a| self.expr(a))
            }
            ExprKind::Slice(a, b, c) => {
                self.expr(a);
                self.expr(b);
                self.expr(c)
            }
            ExprKind::Tuple(es) | ExprKind::List(es) | ExprKind::Set(es) => es.iter().for_each(|x| self.expr(x)),
            ExprKind::ListComp { elem, pat, iter, cond } => {
                self.expr(elem);
                self.pat(pat);
                self.expr(iter);
                if let Some(c) = cond {
                    self.expr(c)
                }
            }
            ExprKind::SetBuilder { ty, cond, .. } => {
                self.ty(ty);
                self.expr(cond)
            }
            ExprKind::Record { name, fields } => {
                self.out.insert(name.name.clone());
                fields.iter().for_each(|(_, v)| self.expr(v))
            }
            ExprKind::With(a, fields) => {
                self.expr(a);
                fields.iter().for_each(|(_, v)| self.expr(v))
            }
            ExprKind::If(c, a, b) => {
                self.expr(c);
                self.block(a);
                self.block(b)
            }
            ExprKind::Match(s, arms) => {
                self.expr(s);
                arms.iter().for_each(|a| {
                    a.pats.iter().for_each(|p| self.pat(p));
                    self.block(&a.body)
                })
            }
            ExprKind::Binder { vars, domain, body, .. } => {
                vars.iter().filter_map(|v| v.1.as_ref()).for_each(|t| self.ty(t));
                if let Some(d) = domain {
                    self.expr(d)
                }
                self.expr(body)
            }
            ExprKind::Any { ty, cond, els, .. } => {
                self.ty(ty);
                if let Some(c) = cond {
                    self.expr(c)
                }
                if let Some(b) = els {
                    self.block(b)
                }
            }
            ExprKind::Lambda(ps, b) => {
                ps.iter().for_each(|p| self.ty(&p.ty));
                self.block(b)
            }
            ExprKind::Is(a, p) => {
                self.expr(a);
                self.pat(p)
            }
            ExprKind::Labeled(_, a) => self.expr(a),
            ExprKind::Block(b) => self.block(b),
            ExprKind::Do(t, b) => {
                if let Some(t) = t {
                    self.ty(t)
                }
                self.block(b)
            }
            ExprKind::WithView(v, b) => {
                self.expr(v);
                self.block(b)
            }
            ExprKind::Num(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::SelfState => {}
        }
    }
}
