//! Declarations.

use crate::elab::*;
use crate::ty::{StateTy, Ty};
use sl_kernel::{Term, VarId};
use sl_syntax::ast::*;

impl<'s> Elab<'s> {
    pub fn elab_decl(&mut self, i: usize) -> R<()> {
        let decl = self.g.decls[i].decl.clone();
        let qual = self.g.decls[i].qual.clone();
        let span = decl.span;
        match &decl.kind {
            DeclKind::TypeDecl { def: TypeDef::Sum(_), .. } | DeclKind::Enum { .. } | DeclKind::Record { .. } => {
                self.named_set(&qual, span)?;
                Ok(())
            }
            DeclKind::State { .. } => {
                if let Ty::State(st) = self.state_ty_named(&qual) {
                    let s = self.ty_set(&Ty::State(st), span)?;
                    let _ = s;
                }
                Ok(())
            }
            DeclKind::TypeDecl { .. }
            | DeclKind::Exception { .. }
            | DeclKind::DecoderContext(_)
            | DeclKind::Notations { .. }
            | DeclKind::ParamPred { .. }
            | DeclKind::ParamFn { .. } => Ok(()),
            DeclKind::Const { value, .. } => {
                let sig = self.sig_of(i, "")?;
                let (mut cx, lift, _) = self.header_cx(i, &[])?;
                let (t, _) = self.pure_expr(&mut cx, value, Some(&sig.ret))?;
                let params = self.lift_params(&lift);
                self.define(&sig.core, params, t, span)?;
                Ok(())
            }
            DeclKind::Fn(f) => self.elab_fn(i, f),
            DeclKind::Proc(p) => {
                let sig = self.sig_of(i, "")?;
                let st = match &sig.kind {
                    SigKind::Proc(s) => s.clone(),
                    _ => unreachable!(),
                };
                let (mut cx, lift, gens) = self.header_cx_from_sig(i, &sig, &p.generics)?;
                let body = match &p.body {
                    Body::Block(b) => b.clone(),
                    Body::Expr(e) => Block { span: e.span, stmts: vec![Stmt { span: e.span, kind: StmtKind::Return(Some(e.clone())) }] },
                };
                let prog = self.program(&cx, &st, &body, &sig.ret, span)?;
                cx.locals.clear();
                let params = self.all_params(&lift, &gens, &sig);
                self.define(&sig.core, params, prog, span)?;
                Ok(())
            }
            DeclKind::View { get, set_var, set, .. } => {
                // get
                let gsig = self.sig_of(i, "get")?;
                let st = match &gsig.kind {
                    SigKind::Proc(s) => s.clone(),
                    _ => unreachable!(),
                };
                let (cx, lift, gens) = self.header_cx_from_sig(i, &gsig, &[])?;
                let gbody = match get {
                    ViewGet::Block(b) => b.clone(),
                    ViewGet::Expr(e) => Block { span: e.span, stmts: vec![Stmt { span: e.span, kind: StmtKind::Return(Some(e.clone())) }] },
                };
                let gprog = self.program(&cx, &st, &gbody, &gsig.ret, span)?;
                let params = self.all_params(&lift, &gens, &gsig);
                self.define(&gsig.core, params, gprog, span)?;
                // set
                let ssig = self.sig_of(i, "set")?;
                let (mut cx, lift, gens) = self.header_cx_from_sig(i, &ssig, &[])?;
                // the value parameter is called `$v` in the signature; bind the user's name
                let (_, vv, vt) = ssig.params.last().unwrap().clone();
                cx.push_local(&set_var.name, self.b.v(vv), vt, false);
                let sprog = self.program(&cx, &st, set, &Ty::Unit, span)?;
                let params = self.all_params(&lift, &gens, &ssig);
                self.define(&ssig.core, params, sprog, span)?;
                Ok(())
            }
            DeclKind::Table(t) => self.elab_table(i, t),
            DeclKind::Law { params, prop, .. } => {
                let (mut cx, lift, _) = self.header_cx(i, &[])?;
                let body = self.closed_prop(&mut cx, params, prop, span)?;
                let ps = self.lift_params(&lift);
                self.define(&qual, ps, body, span)?;
                Ok(())
            }
            DeclKind::Theorem { generics, params, prop, .. } => {
                let (mut cx, lift, gens) = self.header_cx(i, generics)?;
                let body = self.closed_prop(&mut cx, params, prop, span)?;
                // generics and layer parameters are universally quantified;
                // layer laws become hypotheses
                let mut vars: Vec<VarId> = gens.iter().map(|g| g.var).collect();
                let mut stmt = body;
                if !lift.is_empty() {
                    let laws = self.laws_of(&cx, &lift, span)?;
                    stmt = self.b.imp(laws, stmt);
                    vars.extend(lift.iter().map(|q| self.lift_vars[q]));
                }
                let claim = self.b.all(&vars, stmt);
                self.claims.push((qual, claim));
                Ok(())
            }
        }
    }

    fn lift_params(&self, lift: &[String]) -> Vec<VarId> {
        lift.iter().map(|q| self.lift_vars[q]).collect()
    }

    fn all_params(&self, lift: &[String], gens: &[crate::elab::GenParam], sig: &Sig) -> Vec<VarId> {
        let mut ps = self.lift_params(lift);
        ps.extend(gens.iter().map(|g| g.var));
        ps.extend(sig.params.iter().map(|p| p.1));
        ps
    }

    /// Context with the signature's own generic and parameter variables.
    fn header_cx_from_sig(&mut self, i: usize, sig: &Sig, _generics: &[sl_syntax::ast::Generic]) -> R<(Cx, Vec<String>, Vec<crate::elab::GenParam>)> {
        let module = self.module_of(i);
        let mut cx = Cx::new(&module);
        for q in &sig.lift {
            cx.lift.insert(q.clone(), self.b.v(self.lift_vars[q]));
        }
        for g in &sig.generics {
            match &g.val_ty {
                Some(t) => {
                    cx.gvals.insert(g.name.clone(), (self.b.v(g.var), t.clone()));
                }
                None => {
                    let t = self.b.v(g.var);
                    cx.gtys.insert(g.name.clone(), (Ty::Param(g.name.clone(), t.clone()), t));
                }
            }
        }
        for (n, v, t) in &sig.params {
            if n != "$v" {
                cx.push_local(n, self.b.v(*v), t.clone(), false);
            }
        }
        Ok((cx, sig.lift.clone(), sig.generics.clone()))
    }

    fn elab_fn(&mut self, i: usize, f: &FnDecl) -> R<()> {
        let sig = self.sig_of(i, "")?;
        let span = self.g.decls[i].decl.span;
        let (mut cx, lift, gens) = self.header_cx_from_sig(i, &sig, &f.generics)?;
        let params = self.all_params(&lift, &gens, &sig);
        let body = match (&f.kind, &f.body) {
            (FnKind::Decoder, b) => {
                let st = match &sig.kind {
                    SigKind::Proc(s) => s.clone(),
                    _ => unreachable!(),
                };
                let blk = match b {
                    Body::Block(b) => b.clone(),
                    Body::Expr(e) => Block { span: e.span, stmts: vec![Stmt { span: e.span, kind: StmtKind::Return(Some(e.clone())) }] },
                };
                self.program(&cx, &st, &blk, &sig.ret, span)?
            }
            (_, Body::Expr(e)) => {
                let (t, ty) = self.pure_expr(&mut cx, e, Some(&sig.ret))?;
                if !crate::expr::compatible(&sig.ret, &ty) {
                    return err(e.span, format!("`{}` returns {}, but its body is {}", sig.core, sig.ret.describe(), ty.describe()));
                }
                t
            }
            // statements, deterministic: evaluated to the returned value (a
            // term of lets and conditionals -- no programs, no choices)
            (_, Body::Block(b)) => self.det_block(&mut cx, &b.stmts, &sig.ret, &sig.core, b.span)?,
        };
        self.define(&sig.core, params, body, span)?;
        Ok(())
    }

    /// A `fn`'s block body as the term of its value: `let` / `var` / an
    /// assignment bind the rest (`letin`), `if` / `match` choose between the
    /// rests of their branches (`ite`; a `match` with no arm matching takes
    /// the last, as in expressions), `return e` is e. Statements that run
    /// programs or choose (loops, `either`, `any`, `require`, ...) belong in
    /// a `proc`.
    fn det_block(&mut self, cx: &mut Cx, stmts: &[Stmt], ret: &Ty, name: &str, span: Span) -> R<Term> {
        let Some((st, rest)) = stmts.split_first() else {
            return err(span, format!("`{}`: a `fn` body ends with `return`", name));
        };
        let nondet = || err(st.span, format!("`{}`: a `fn` body is deterministic -- this statement runs a program or chooses; write a `proc`", name));
        let then = |b: &Block| b.stmts.iter().chain(rest.iter()).cloned().collect::<Vec<Stmt>>();
        match &st.kind {
            StmtKind::Let { .. } | StmtKind::Var { .. } | StmtKind::Assign { .. } => {
                let f0 = cx.frames.len();
                self.stmt(cx, st)?;
                if cx.frames[f0..].iter().any(|f| !matches!(f, Frame::Let { .. })) {
                    return nondet();
                }
                let frames = cx.frames.split_off(f0);
                let body = self.det_block(cx, rest, ret, name, span)?;
                Ok(self.wrap_frames(frames, body))
            }
            StmtKind::If { cond, then: a, els } => {
                let (c, _) = self.pure_expr(cx, cond, Some(&Ty::Bool))?;
                let sa = then(a);
                let sb = match els {
                    Some(b) => then(b),
                    None => rest.to_vec(),
                };
                let ta = self.det_block(&mut cx.clone(), &sa, ret, name, span)?;
                let tb = self.det_block(&mut cx.clone(), &sb, ret, name, span)?;
                Ok(self.b.ite(c, ta, tb))
            }
            StmtKind::Match { scrut, arms } => {
                let (sv, sty) = self.pure_expr(cx, scrut, None)?;
                let mut alts = Vec::new();
                for arm in arms {
                    let mut conds = Vec::new();
                    let mut binds = Vec::new();
                    for p in &arm.pats {
                        let (c, bs) = self.pattern(cx, p, &sv, &sty)?;
                        conds.push(c);
                        if binds.is_empty() {
                            binds = bs;
                        }
                    }
                    let mut ca = cx.clone();
                    for (n, t, ty) in binds {
                        ca.push_local(&n, t, ty, false);
                    }
                    let v = self.det_block(&mut ca, &then(&arm.body), ret, name, span)?;
                    alts.push((self.b.ors(conds), v));
                }
                // (first match wins; the last arm is the default)
                let Some((_, last)) = alts.pop() else { return err(st.span, "a `match` without arms") };
                Ok(alts.into_iter().rev().fold(last, |acc, (c, v)| self.b.ite(c, v, acc)))
            }
            StmtKind::Block(b) => self.det_block(cx, &then(b), ret, name, span),
            StmtKind::Return(Some(e)) => {
                let (t, ty) = self.pure_expr(cx, e, Some(ret))?;
                if !crate::expr::compatible(ret, &ty) {
                    return err(e.span, format!("`{}` returns {}, but this is {}", name, ret.describe(), ty.describe()));
                }
                Ok(t)
            }
            _ => nondet(),
        }
    }

    /// `all params. (types) -> prop`
    fn closed_prop(&mut self, cx: &mut Cx, params: &[Param], prop: &Expr, span: Span) -> R<Term> {
        let mut vars = Vec::new();
        let mut guards = Vec::new();
        for p in params {
            let t = self.ty(cx, &p.ty)?;
            let set = self.ty_set(&t, span)?;
            let v = self.fresh(&p.name.name);
            guards.push(self.b.member(self.b.v(v), set));
            cx.push_local(&p.name.name, self.b.v(v), t, false);
            vars.push(v);
        }
        let (body, _) = self.pure_expr(cx, prop, Some(&Ty::Bool))?;
        let g = self.b.ands(guards);
        let inner = self.b.imp(g, body);
        Ok(if vars.is_empty() { body_or(inner) } else { self.b.all(&vars, inner) })
    }

    /// Conjunction of all laws of the layers defining `lift`.
    pub fn laws_of(&mut self, cx: &Cx, lift: &[String], span: Span) -> R<Term> {
        let mods: Vec<String> = lift.iter().map(|q| q.split('.').next().unwrap().to_string()).collect();
        let law_idx: Vec<usize> = (0..self.g.decls.len())
            .filter(|&j| mods.contains(&self.g.decls[j].module) && matches!(self.g.decls[j].decl.kind, DeclKind::Law { .. }))
            .collect();
        let mut parts = Vec::new();
        for j in law_idx {
            self.ensure(j)?;
            let deps: Vec<String> = self.g.param_deps[j].iter().cloned().collect();
            let args: Vec<Term> = deps
                .iter()
                .map(|q| cx.lift.get(q).cloned().ok_or(()))
                .collect::<Result<_, _>>()
                .or_else(|_| err(span, "law parameters not in scope"))?;
            parts.push(self.b.app(&self.g.decls[j].qual.clone(), args));
        }
        Ok(self.b.ands(parts))
    }

    // ------------------------------------------------------------------
    //  Tables

    fn elab_table(&mut self, i: usize, t: &Table) -> R<()> {
        let module = self.module_of(i);
        let qual = self.g.decls[i].qual.clone();
        let span = self.g.decls[i].decl.span;
        let dstate = Ty::State(StateTy { base: format!("$decoder:{}", module), ext: vec![] });
        let ctx_ty = self.decoder_ctx_ty(&module, span)?;
        // flatten `for` / `with`
        let mut rows = Vec::new();
        self.flatten(&module, &t.entries, &mut Vec::new(), &mut Vec::new(), &mut rows)?;
        let machine = self.default_state(&Cx::new(&module), span)?;
        let mut alts_dec = Vec::new();
        let mut alts_exe = Vec::new();
        let b_var = self.fresh("b");
        let z = self.fresh("z");
        let x = self.fresh("x");
        let s_exe = self.fresh("s");
        let o_exe = self.fresh("o");
        for (k, (prefix, consts, row)) in rows.iter().enumerate() {
            // 1. the row's decoder program: returns the tuple of its bindings
            let s = self.fresh("s");
            let o = self.fresh("o");
            let mut cx = Cx::new(&module);
            cx.pure = false;
            cx.state = Some(self.b.v(s));
            cx.state_ty = Some(dstate.clone());
            cx.exits = vec![Exit::Proc { o }];
            for (n, t, ty) in consts {
                cx.push_local(n, t.clone(), ty.clone(), false);
            }
            let n0 = cx.locals.len();
            let items: Vec<Item> = t.before.iter().chain(prefix.iter()).chain(row.items.iter()).chain(t.after.iter()).cloned().collect();
            for it in &items {
                self.item(&mut cx, it, row.span)?;
            }
            let bound: Vec<(String, Term, Ty)> = cx.locals[n0..].iter().map(|l| (l.name.clone(), l.term.clone(), l.ty.clone())).collect();
            let result = self.b.tuple(bound.iter().map(|b| b.1.clone()).collect());
            let fin = self.exit_ret(&cx, result);
            let frames = std::mem::take(&mut cx.frames);
            let f = self.wrap_frames(frames, fin);
            let prog = self.b.bind_app("mkprog", vec![], &[s, o], &f);
            let row_name = format!("{}.row{}", qual, k);
            self.define(&row_name, vec![], prog, row.span)?;
            // 2. the row's body program over the machine state
            let bx = self.fresh("x");
            let mut bcx = Cx::new(&module);
            for (n, t, ty) in consts {
                bcx.push_local(n, t.clone(), ty.clone(), false);
            }
            let nb = bound.len();
            for (j, (n, _, ty)) in bound.iter().enumerate() {
                bcx.push_local(n, self.b.proj(self.b.v(bx), j, nb), ty.clone(), false);
            }
            let body = self.program(&bcx, &machine, &row.body, &Ty::Unit, row.span)?;
            let body_name = format!("{}.body{}", qual, k);
            self.define(&body_name, vec![bx], body, row.span)?;
            // 3. decode / execute alternatives
            let st = self.fresh("st");
            let v = self.fresh("v");
            let ctx0 = self.pure_const(&module, &t.context, &ctx_ty)?;
            let init = self.b.record(vec![("bytes".into(), self.b.v(b_var)), ("pos".into(), self.b.nat(0)), ("ctx".into(), ctx0)]);
            let runs = self.b.app("runs", vec![self.b.c(&row_name), init, self.b.app("ok", vec![self.b.v(st), self.b.v(v)])]);
            let pick = self.b.eq(self.b.v(z), self.b.pair(self.b.field(self.b.v(st), "pos"), self.b.tag(k as u64, self.b.v(v))));
            let inner = self.b.and(runs, pick);
            alts_dec.push(self.b.ex(&[st, v], inner));
            let is_k = self.b.eq(self.b.fst(self.b.v(x)), self.b.nat(k as u64));
            let run_body = self.b.app("runs", vec![self.b.app(&body_name, vec![self.b.snd(self.b.v(x))]), self.b.v(s_exe), self.b.v(o_exe)]);
            alts_exe.push(self.b.and(is_k, run_body));
        }
        let univ1 = self.b.app("univ", vec![self.b.nat(1)]);
        let space = self.b.app("cart", vec![self.b.c("omega"), univ1]);
        let dec = self.b.bind_app("set_select", vec![space], &[z], &self.b.ors(alts_dec));
        self.define(&format!("{}.decode", qual), vec![b_var], dec, span)?;
        let exe = self.b.bind_app("mkprog", vec![], &[s_exe, o_exe], &self.b.ors(alts_exe));
        self.define(&format!("{}.execute", qual), vec![x], exe, span)?;
        Ok(())
    }

    fn pure_const(&mut self, module: &str, e: &Expr, ty: &Ty) -> R<Term> {
        let mut cx = Cx::new(module);
        Ok(self.pure_expr(&mut cx, e, Some(ty))?.0)
    }

    /// Unrolls `for x in Enum { .. }` and prepends `with` items.
    fn flatten(
        &mut self,
        module: &str,
        entries: &[TableEntry],
        prefix: &mut Vec<Item>,
        consts: &mut Vec<(String, Term, Ty)>,
        out: &mut Vec<(Vec<Item>, Vec<(String, Term, Ty)>, Row)>,
    ) -> R<()> {
        for e in entries {
            match e {
                TableEntry::Row(r) => out.push((prefix.clone(), consts.clone(), r.clone())),
                TableEntry::With { pat, item, entries } => {
                    prefix.push(Item::Bind(pat.clone(), item.clone()));
                    self.flatten(module, entries, prefix, consts, out)?;
                    prefix.pop();
                }
                TableEntry::For { var, ty, except, entries } => {
                    let j = match self.g.find_decl(module, &ty.name) {
                        Some(j) if matches!(self.g.decls[j].decl.kind, DeclKind::Enum { .. }) => j,
                        _ => return err(ty.span, format!("`for` in a table ranges over an enum, not `{}`", ty.name)),
                    };
                    let q = self.g.decls[j].qual.clone();
                    let values = self.enum_values(j)?;
                    for x in except {
                        if !values.iter().any(|(n, _)| *n == x.name) {
                            return err(x.span, format!("`{}` is not an item of `{}`", x.name, ty.name));
                        }
                    }
                    for (name, v) in values {
                        if except.iter().any(|x| x.name == name) {
                            continue;
                        }
                        consts.push((var.name.clone(), self.b.natn(v), Ty::Enum(q.clone())));
                        self.flatten(module, entries, prefix, consts, out)?;
                        consts.pop();
                    }
                }
            }
        }
        Ok(())
    }

    fn item(&mut self, cx: &mut Cx, it: &Item, span: Span) -> R<()> {
        match it {
            Item::Byte(e) => {
                let s = cx.state.clone().unwrap();
                let pos = self.b.field(s.clone(), "pos");
                let byte = self.b.app_fn(self.b.field(s.clone(), "bytes"), pos.clone());
                let s2 = self.b.fn_update(s, self.b.str("pos"), self.b.app("int_add", vec![pos, self.b.nat(1)]));
                let (want, _) = self.expr(cx, e, Some(&Ty::Bits(self.b.nat(8))))?;
                let nomatch = self.b.app("exc_val", vec![self.b.str("nomatch"), self.b.empty()]);
                let st = cx.state.clone().unwrap();
                let fail = self.exit_raise(cx, st, nomatch);
                cx.frames.push(Frame::Guard { cond: self.b.eq(byte, want), fail });
                let sv = self.fresh("s");
                cx.frames.push(Frame::Let { var: sv, value: s2 });
                cx.state = Some(self.b.v(sv));
                Ok(())
            }
            Item::Run(e) => {
                self.expr(cx, e, None)?;
                Ok(())
            }
            Item::Bind(p, e) => {
                let (t, ty) = self.expr(cx, e, None)?;
                let x = self.fresh("x");
                cx.frames.push(Frame::Let { var: x, value: t });
                let (_, binds) = self.pattern(cx, p, &self.b.v(x), &ty)?;
                for (n, t, ty) in binds {
                    cx.push_local(&n, t, ty, false);
                }
                Ok(())
            }
            Item::Guard(e) => {
                let (cond, binds) = match &e.kind {
                    ExprKind::Is(a, p) => {
                        let (t, ty) = self.expr(cx, a, None)?;
                        self.pattern(cx, p, &t, &ty)?
                    }
                    _ => (self.expr(cx, e, Some(&Ty::Bool))?.0, vec![]),
                };
                let nomatch = self.b.app("exc_val", vec![self.b.str("nomatch"), self.b.empty()]);
                let st = cx.state.clone().unwrap();
                let fail = self.exit_raise(cx, st, nomatch);
                cx.frames.push(Frame::Guard { cond, fail });
                for (n, t, ty) in binds {
                    cx.push_local(&n, t, ty, false);
                }
                let _ = span;
                Ok(())
            }
        }
    }
}

fn body_or(t: Term) -> Term {
    t
}
