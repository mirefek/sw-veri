//! Expressions.

use crate::elab::*;
use crate::globals::GName;
use crate::ty::{Ext, StateTy, Ty};
use sl_kernel::{Nat, Term, VarId};
use sl_syntax::ast::*;
use std::collections::HashMap;

/// Literal-like expressions take their type from the context.
pub fn literalish(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Num(_) => true,
        ExprKind::Unary(UnOp::Neg, a) => literalish(a),
        ExprKind::Binary(op, a, b) if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Pow) => {
            literalish(a) && literalish(b)
        }
        ExprKind::Set(xs) | ExprKind::List(xs) => xs.iter().all(literalish),
        ExprKind::Any { .. } | ExprKind::Lambda(..) => true,
        ExprKind::Name(n) => n.name == "none",
        _ => false,
    }
}

impl<'s> Elab<'s> {
    /// Elaborates `e`; where a `bool` or a number is expected, the type must
    /// fit (other expected types are checked where they are used).
    pub fn expr(&mut self, cx: &mut Cx, e: &Expr, exp: Option<&Ty>) -> R<(Term, Ty)> {
        let r = self.expr_inner(cx, e, exp)?;
        if let Some(x) = exp {
            let bad = match x.strip() {
                Ty::Bool => !compatible(x, &r.1),
                Ty::Nat | Ty::Int | Ty::NatInf => matches!(r.1.strip(), Ty::Bool),
                _ => false,
            };
            if bad {
                return err(e.span, format!("expected {}, got {}", x.describe(), r.1.describe()));
            }
        }
        Ok(r)
    }

    fn expr_inner(&mut self, cx: &mut Cx, e: &Expr, exp: Option<&Ty>) -> R<(Term, Ty)> {
        let span = e.span;
        match &e.kind {
            ExprKind::Num(n) => {
                let t = match exp.map(|t| t.strip()) {
                    Some(t @ (Ty::Nat | Ty::Int | Ty::NatInf | Ty::Bits(_) | Ty::Enum(_))) => t.clone(),
                    Some(Ty::Param(..)) => exp.unwrap().clone(),
                    _ => Ty::Nat,
                };
                Ok((self.b.natn(n.clone()), t))
            }
            ExprKind::Bool(v) => Ok((if *v { self.b.tru() } else { self.b.fls() }, Ty::Bool)),
            ExprKind::Str(s) => Ok((self.b.str(s), Ty::Str)),
            ExprKind::SelfState => match (&cx.state, &cx.state_ty) {
                (Some(s), Some(t)) => Ok((s.clone(), t.clone())),
                _ => err(span, "`self` outside a procedure"),
            },
            ExprKind::Name(id) => self.name_expr(cx, id, exp),
            ExprKind::Unary(op, a) => self.unary(cx, *op, a, exp, span),
            ExprKind::Binary(op, a, b) => self.binary(cx, *op, a, b, exp, span),
            ExprKind::Call(f, args) => self.call(cx, f, args, exp, span),
            ExprKind::Index(a, idx) => self.index(cx, a, idx, exp, span),
            ExprKind::Slice(a, hi, lo) => {
                let (t, ty) = self.expr(cx, a, None)?;
                let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
                let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
                if !matches!(ty.strip(), Ty::Bits(_) | Ty::Nat | Ty::Unknown) {
                    return err(span, format!("slice of a non-bits value ({})", ty.describe()));
                }
                let w = self.slice_width(&h, &l);
                Ok((self.b.app("bits_slice", vec![t, h, l]), Ty::Bits(w)))
            }
            ExprKind::From(a, k) => {
                let (t, ty) = self.expr(cx, a, None)?;
                let (kt, _) = self.expr(cx, k, Some(&Ty::Nat))?;
                Ok((self.b.app("seq_drop", vec![t, kt]), ty))
            }
            ExprKind::Field(a, f) => self.field_expr(cx, a, f, span),
            ExprKind::FieldSet(..) => err(span, "`x.{a, b}` is only allowed in `havoc`"),
            ExprKind::Tuple(xs) => {
                if xs.is_empty() {
                    return Ok((self.b.empty(), Ty::Unit));
                }
                let exps: Vec<Option<Ty>> = match exp.map(|t| t.strip()) {
                    Some(Ty::Tuple(ts)) if ts.len() == xs.len() => ts.iter().cloned().map(Some).collect(),
                    _ => vec![None; xs.len()],
                };
                let mut ts = Vec::new();
                let mut tys = Vec::new();
                for (x, et) in xs.iter().zip(exps) {
                    let (t, ty) = self.expr(cx, x, et.as_ref())?;
                    ts.push(t);
                    tys.push(ty);
                }
                Ok((self.b.tuple(ts), Ty::Tuple(tys)))
            }
            ExprKind::List(xs) => {
                let et = match exp.map(|t| t.strip()) {
                    Some(Ty::List(t) | Ty::Seq(t)) => Some((**t).clone()),
                    _ => None,
                };
                // [a, b, c] = seq_one(a) ++ seq_one(b) ++ seq_one(c): the
                // form list reasoning normalizes (associativity of ++)
                let mut acc: Option<Term> = None;
                let mut ety = et.clone().unwrap_or(Ty::Unknown);
                for x in xs {
                    let (t, ty) = self.expr(cx, x, et.as_ref())?;
                    ety = ty;
                    let one = self.b.app("seq_one", vec![t]);
                    acc = Some(match acc {
                        None => one,
                        Some(a) => self.b.app("seq_concat", vec![a, one]),
                    });
                }
                Ok((acc.unwrap_or_else(|| self.b.empty()), Ty::List(Box::new(ety))))
            }
            ExprKind::Set(xs) => {
                let mut et = match exp.map(|t| t.strip()) {
                    Some(Ty::Set(t)) => Some((**t).clone()),
                    _ => None,
                };
                let mut items = Vec::new();
                for x in xs {
                    let (t, ty) = self.expr(cx, x, et.as_ref())?;
                    if et.is_none() && !literalish(x) {
                        et = Some(ty);
                    }
                    items.push(t);
                }
                Ok((self.b.set_of(items), Ty::Set(Box::new(et.unwrap_or(Ty::Nat)))))
            }
            ExprKind::SetBuilder { var, ty, cond } => {
                let t = self.ty(cx, ty)?;
                let set = self.ty_set(&t, span)?;
                let x = self.fresh(&var.name);
                cx.push_local(&var.name, self.b.v(x), t.clone(), false);
                let r = self.pure_expr(cx, cond, Some(&Ty::Bool));
                cx.locals.pop();
                let (c, _) = r?;
                Ok((self.b.bind_app("set_select", vec![set], &[x], &c), Ty::Set(Box::new(t))))
            }
            ExprKind::ListComp { elem, pat, iter, cond } => self.list_comp(cx, elem, pat, iter, cond.as_deref(), span),
            ExprKind::Record { name, fields } => self.record_lit(cx, name, fields, span),
            ExprKind::With(a, fields) => {
                let (mut t, ty) = self.expr(cx, a, exp)?;
                let fs = self.fields_of(&ty)?.unwrap_or_default();
                for (f, v) in fields {
                    let ft = fs.iter().find(|x| x.0 == f.name).map(|x| x.1.clone());
                    if ft.is_none() && !fs.is_empty() {
                        return err(f.span, format!("no field `{}` in {}", f.name, ty.describe()));
                    }
                    let (vt, _) = self.expr(cx, v, ft.as_ref())?;
                    t = self.b.fn_update(t, self.b.str(&f.name), vt);
                }
                Ok((t, ty))
            }
            ExprKind::If(c, a, b) => self.if_expr(cx, c, a, b, exp, span),
            ExprKind::Match(s, arms) => self.match_expr(cx, s, arms, exp, span),
            ExprKind::Binder { kind, vars, domain, body } => self.binder(cx, *kind, vars, domain.as_deref(), body, span),
            ExprKind::Any { var, ty, cond, els, .. } => {
                if els.is_some() {
                    return err(span, "`any ... else` only in `let x = any ...`");
                }
                let t = self.ty(cx, ty)?;
                let name = var.as_ref().map(|v| v.name.clone()).unwrap_or_else(|| "$any".into());
                self.any_value(cx, &name, t, cond.as_deref(), span)
            }
            ExprKind::Lambda(params, body) => self.lambda(cx, params, body, exp, span),
            ExprKind::Is(a, p) => {
                let (t, ty) = self.expr(cx, a, None)?;
                let (c, _) = self.pattern(cx, p, &t, &ty)?;
                Ok((c, Ty::Bool))
            }
            ExprKind::Block(b) => self.block_value(cx, b, exp, span),
            ExprKind::Do(st, b) => {
                let sty = match st {
                    Some(t) => self.ty(cx, t)?,
                    None => self.default_state(cx, span)?,
                };
                let prog = self.program(cx, &sty, b, &Ty::Unit, span)?;
                Ok((prog, Ty::Prog(Box::new(sty), Box::new(Ty::Unit))))
            }
            ExprKind::WithView(v, b) => self.with_view(cx, v, b, exp, span),
        }
    }

    /// An expression that must not have effects.
    pub fn pure_expr(&mut self, cx: &mut Cx, e: &Expr, exp: Option<&Ty>) -> R<(Term, Ty)> {
        let n = cx.frames.len();
        let r = self.expr(cx, e, exp)?;
        if cx.frames.len() != n {
            return err(e.span, "this expression may not execute programs (it is under a binder or in a pure context)");
        }
        Ok(r)
    }

    // ------------------------------------------------------------------
    //  Names

    fn name_expr(&mut self, cx: &mut Cx, id: &Ident, exp: Option<&Ty>) -> R<(Term, Ty)> {
        let name = id.name.as_str();
        if let Some(l) = cx.local(name) {
            return Ok((l.term.clone(), l.ty.clone()));
        }
        if let Some((t, ty)) = cx.gvals.get(name) {
            return Ok((t.clone(), ty.clone()));
        }
        if let (Some(s), Some(st)) = (cx.state.clone(), cx.state_ty.clone()) {
            if let Some(fs) = self.fields_of(&st)? {
                if let Some((_, fty, _)) = fs.iter().find(|f| f.0 == name) {
                    return Ok((self.b.field(s, name), fty.clone()));
                }
            }
        }
        if name == "none" {
            let inner = match exp.map(|t| t.strip()) {
                Some(Ty::Opt(t)) => (**t).clone(),
                _ => Ty::Unknown,
            };
            return Ok((self.b.c("none"), Ty::Opt(Box::new(inner))));
        }
        let cands = self.global_candidates(&cx.module, name);
        let chosen = self.choose_candidate(&cands, exp);
        match chosen {
            Some(GName::EnumVal(i, j)) => {
                let vals = self.enum_values(i)?;
                let q = self.g.decls[i].qual.clone();
                Ok((self.b.natn(vals[j].1.clone()), Ty::Enum(q)))
            }
            Some(GName::Ctor(i, j)) => self.ctor_app(cx, i, j, &[], id.span),
            Some(GName::Decl(i)) => {
                self.ensure(i)?;
                match self.g.decls[i].decl.kind.clone() {
                    DeclKind::Const { .. } => {
                        let sig = self.sig_of(i, "")?;
                        let args = self.lift_args(cx, &sig, id.span)?;
                        Ok((self.b.app(&sig.core, args), sig.ret.clone()))
                    }
                    DeclKind::Exception { params, .. } if params.is_empty() => {
                        Ok((self.b.app("exc_val", vec![self.b.str(name), self.b.empty()]), Ty::Exc))
                    }
                    DeclKind::Proc(_) => self.proc_value(cx, i, id.span),
                    _ => err(id.span, format!("`{}` is not a value", name)),
                }
            }
            None => err(id.span, format!("unknown name `{}`", name)),
        }
    }

    fn choose_candidate(&self, cands: &[GName], exp: Option<&Ty>) -> Option<GName> {
        if cands.len() <= 1 {
            return cands.first().cloned();
        }
        let want = exp.map(|t| t.strip().clone());
        for c in cands {
            let ok = match (c, &want) {
                (GName::EnumVal(i, _), Some(Ty::Enum(q))) => &self.g.decls[*i].qual == q,
                (GName::Ctor(i, _), Some(Ty::Sum(q))) => &self.g.decls[*i].qual == q,
                (GName::Decl(i), Some(Ty::Exc)) => matches!(self.g.decls[*i].decl.kind, DeclKind::Exception { .. }),
                _ => false,
            };
            if ok {
                return Some(c.clone());
            }
        }
        // declarations win over enum values and constructors
        cands.iter().find(|c| matches!(c, GName::Decl(_))).cloned().or_else(|| cands.first().cloned())
    }

    /// Sum constructor application `ctor(args)`.
    pub fn ctor_app(&mut self, cx: &mut Cx, i: usize, j: usize, args: &[Expr], span: Span) -> R<(Term, Ty)> {
        let module = self.module_of(i);
        let vs = match &self.g.decls[i].decl.kind {
            DeclKind::TypeDecl { def: TypeDef::Sum(vs), .. } => vs.clone(),
            _ => unreachable!(),
        };
        let v = &vs[j];
        if v.params.len() != args.len() {
            return err(span, format!("`{}` takes {} arguments", v.name.name, v.params.len()));
        }
        let hcx = Cx::new(&module);
        let mut ts = Vec::new();
        for (p, a) in v.params.iter().zip(args) {
            let pt = self.ty(&hcx, &p.ty)?;
            let (t, at) = self.expr(cx, a, Some(&pt))?;
            if !compatible(&pt, &at) {
                return err(a.span, format!("argument `{}` of `{}`: expected {}, got {}", p.name.name, v.name.name, pt.describe(), at.describe()));
            }
            ts.push(t);
        }
        let q = self.g.decls[i].qual.clone();
        Ok((self.b.tag(j as u64, self.b.tuple(ts)), Ty::Sum(q)))
    }

    /// A named procedure as a value: `fn_build(params, x. p(x))`.
    fn proc_value(&mut self, cx: &mut Cx, i: usize, span: Span) -> R<(Term, Ty)> {
        let sig = self.sig_of(i, "")?;
        if !sig.generics.is_empty() {
            return err(span, "generic procedures cannot be used as values");
        }
        let st = match &sig.kind {
            SigKind::Proc(s) => s.clone(),
            _ => unreachable!(),
        };
        let ptys: Vec<Ty> = sig.params.iter().map(|p| p.2.clone()).collect();
        let x = self.fresh("x");
        let n = ptys.len();
        let mut args = self.lift_args(cx, &sig, span)?;
        for k in 0..n {
            args.push(self.b.proj(self.b.v(x), k, n));
        }
        let body = self.b.app(&sig.core, args);
        let dom = if n == 0 { self.ty_set(&Ty::Unit, span)? } else { self.ty_set(&Ty::Tuple(ptys.clone()), span)? };
        Ok((
            self.b.bind_app("fn_build", vec![dom], &[x], &body),
            Ty::Proc { state: Box::new(st), params: ptys, ret: Box::new(sig.ret.clone()) },
        ))
    }

    // ------------------------------------------------------------------
    //  Fields

    fn field_expr(&mut self, cx: &mut Cx, a: &Expr, f: &Ident, span: Span) -> R<(Term, Ty)> {
        let (t, ty) = self.expr(cx, a, None)?;
        self.field_of(t, &ty, f, span)
    }

    pub fn field_of(&mut self, t: Term, ty: &Ty, f: &Ident, span: Span) -> R<(Term, Ty)> {
        match ty.strip() {
            Ty::Opt(inner) if f.name == "value" => Ok((self.b.snd(t), (**inner).clone())),
            Ty::Unknown | Ty::Param(..) => Ok((self.b.field(t, &f.name), Ty::Unknown)),
            Ty::State(st) if st.base == "$trace" => {
                // trace records have flat keys: `t.os.events` is t["os.events"]
                let prefix = st.ext.iter().map(|e| if let Ext::Param(n, _) = e { n.clone() } else { String::new() }).collect::<Vec<_>>();
                let mut path = prefix.clone();
                path.push(f.name.clone());
                let base = match st.ext.first() {
                    Some(Ext::Param(_, b)) if !prefix.is_empty() => b.clone(),
                    _ => t.clone(),
                };
                let term = self.b.field(base.clone(), &path.join("."));
                let _ = term;
                let mut ext: Vec<Ext> = Vec::new();
                for (k, p) in path.iter().enumerate() {
                    ext.push(Ext::Param(p.clone(), if k == 0 { base.clone() } else { self.b.empty() }));
                }
                let key = path.join(".");
                // a leaf is used as a sequence; an inner node only for further access
                Ok((self.b.field(base, &key), Ty::State(StateTy { base: "$trace".into(), ext })))
            }
            other => match self.fields_of(other)? {
                Some(fs) => match fs.iter().find(|x| x.0 == f.name) {
                    Some((_, ft, _)) => Ok((self.b.field(t, &f.name), ft.clone())),
                    None => err(f.span, format!("no field `{}` in {}", f.name, ty.describe())),
                },
                None => err(span, format!("field access `.{}` on {}", f.name, ty.describe())),
            },
        }
    }

    // ------------------------------------------------------------------
    //  Operators

    fn unary(&mut self, cx: &mut Cx, op: UnOp, a: &Expr, exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        match op {
            UnOp::Not => {
                let (t, _) = self.expr(cx, a, Some(&Ty::Bool))?;
                Ok((self.b.not(t), Ty::Bool))
            }
            UnOp::Neg => {
                let (t, ty) = self.expr(cx, a, exp)?;
                match ty.strip() {
                    Ty::Bits(w) => Ok((self.b.app("bits_neg", vec![w.clone(), t]), ty.clone())),
                    Ty::Nat | Ty::Int | Ty::Unknown => Ok((self.b.app("int_neg", vec![t]), Ty::Int)),
                    _ => err(span, format!("negation of {}", ty.describe())),
                }
            }
            UnOp::BNot => {
                let (t, ty) = self.expr(cx, a, exp)?;
                match ty.strip() {
                    Ty::Bits(w) => Ok((self.b.app("bits_not", vec![w.clone(), t]), ty.clone())),
                    _ => err(span, format!("`~` needs bits, got {}", ty.describe())),
                }
            }
        }
    }

    /// Elaborates both operands of a numeric operator; literals take the
    /// type of the other side.
    fn operands(&mut self, cx: &mut Cx, a: &Expr, b: &Expr, exp: Option<&Ty>) -> R<(Term, Term, Ty)> {
        let exp_num = exp.filter(|t| t.is_numeric() && !matches!(t, Ty::Unknown));
        if literalish(a) && !literalish(b) {
            let (tb, tyb) = self.expr(cx, b, exp_num)?;
            let (ta, _) = self.expr(cx, a, Some(&tyb))?;
            return Ok((ta, tb, tyb));
        }
        let (ta, tya) = self.expr(cx, a, exp_num)?;
        let (tb, tyb) = self.expr(cx, b, Some(&tya))?;
        let ty = match (tya.strip(), tyb.strip()) {
            (Ty::Nat, Ty::Int) | (Ty::Int, Ty::Nat) => Ty::Int,
            (Ty::Unknown, t) => t.clone(),
            _ => tya,
        };
        Ok((ta, tb, ty))
    }

    fn binary(&mut self, cx: &mut Cx, op: BinOp, a: &Expr, b: &Expr, exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        use BinOp::*;
        match op {
            And | Or | Imp | Iff => {
                let (ta, _) = self.expr(cx, a, Some(&Ty::Bool))?;
                let (tb, _) = self.expr(cx, b, Some(&Ty::Bool))?;
                let t = match op {
                    And => self.b.app("and", vec![ta, tb]),
                    Or => self.b.or(ta, tb),
                    Imp => self.b.imp(ta, tb),
                    _ => self.b.app("iff", vec![ta, tb]),
                };
                Ok((t, Ty::Bool))
            }
            Eq | Ne => {
                let (ta, tb, _) = self.operands(cx, a, b, None)?;
                let e = self.b.eq(ta, tb);
                Ok((if op == Ne { self.b.not(e) } else { e }, Ty::Bool))
            }
            Lt | Le | Gt | Ge => {
                let (ta, tb, ty) = self.operands(cx, a, b, None)?;
                let (x, y) = if matches!(op, Gt | Ge) { (tb, ta) } else { (ta, tb) };
                let strict = matches!(op, Lt | Gt);
                let t = match ty.strip() {
                    Ty::Seq(_) | Ty::List(_) | Ty::State(_) if !strict => self.b.app("subset", vec![x, y]),
                    Ty::Unknown => {
                        // e.g. prefix of trace sequences whose type is not known
                        if strict {
                            self.b.app("ord_lt", vec![x, y])
                        } else {
                            self.b.app("subset", vec![x, y])
                        }
                    }
                    // (with infinity: the order of ordinals)
                    Ty::NatInf => self.b.app(if strict { "ord_lt" } else { "ord_le" }, vec![x, y]),
                    _ => self.b.app(if strict { "int_lt" } else { "int_le" }, vec![x, y]),
                };
                Ok((t, Ty::Bool))
            }
            SLt | SLe | SGt | SGe => {
                let (ta, tb, ty) = self.operands(cx, a, b, None)?;
                let w = match ty.strip() {
                    Ty::Bits(w) => w.clone(),
                    _ => return err(span, "signed comparison of non-bits values"),
                };
                let sa = self.b.app("sint", vec![w.clone(), ta]);
                let sb = self.b.app("sint", vec![w, tb]);
                let (x, y) = if matches!(op, SGt | SGe) { (sb, sa) } else { (sa, sb) };
                let strict = matches!(op, SLt | SGt);
                Ok((self.b.app(if strict { "int_lt" } else { "int_le" }, vec![x, y]), Ty::Bool))
            }
            In | NotIn => {
                let (ta, tya) = self.expr(cx, a, None)?;
                let set = self.membership_set(cx, b, &tya, span)?;
                let m = self.b.member(ta, set);
                Ok((if op == NotIn { self.b.not(m) } else { m }, Ty::Bool))
            }
            Range => err(span, "a range `a..b` is only allowed in `for`, `sum`, `in` and slices"),
            Refines => {
                let (ta, tya) = self.expr(cx, a, None)?;
                let (tb, tyb) = self.expr(cx, b, None)?;
                match (tya.strip(), tyb.strip()) {
                    (Ty::Prog(sa, _), Ty::Prog(sb, _)) => {
                        let (Ty::State(x), Ty::State(y)) = (sa.strip(), sb.strip()) else {
                            return err(span, "`refines` compares programs over states");
                        };
                        let extra: Vec<Ext> = y.ext.iter().filter(|e| !x.ext.contains(e)).cloned().collect();
                        if extra.is_empty() {
                            Ok((self.b.app("refines", vec![ta, tb]), Ty::Bool))
                        } else {
                            let g = self.ext_set(&extra, span)?;
                            Ok((self.b.app("refines_ghost", vec![ta, tb, g]), Ty::Bool))
                        }
                    }
                    _ => err(span, "`refines` compares two programs"),
                }
            }
            Concat => {
                let (ta, tya) = self.expr(cx, a, exp)?;
                let (tb, _) = self.expr(cx, b, Some(&tya))?;
                Ok((self.b.app("seq_concat", vec![ta, tb]), tya))
            }
            Pow => {
                let (ta, _) = self.expr(cx, a, Some(&Ty::Nat))?;
                let (tb, _) = self.expr(cx, b, Some(&Ty::Nat))?;
                Ok((self.b.app("int_pow", vec![ta, tb]), if matches!(exp, Some(Ty::Int)) { Ty::Int } else { Ty::Nat }))
            }
            Add | Sub | Mul | Div | Mod | SDiv | SMod | BAnd | BOr | BXor | Shl | Shr | Sar => {
                let (ta, tb, mut ty) = if matches!(op, Shl | Shr | Sar) {
                    let (ta, tya) = self.expr(cx, a, exp)?;
                    let (tb, _) = self.expr(cx, b, Some(&Ty::Nat))?;
                    (ta, tb, tya)
                } else {
                    self.operands(cx, a, b, exp)?
                };
                if matches!(exp, Some(Ty::Int)) && matches!(ty.strip(), Ty::Nat) {
                    ty = Ty::Int;
                }
                self.arith(op, ta, tb, ty, span)
            }
        }
    }

    fn arith(&mut self, op: BinOp, a: Term, b: Term, ty: Ty, span: Span) -> R<(Term, Ty)> {
        use BinOp::*;
        let name = match (ty.strip(), op) {
            (Ty::Bits(_), Add) => "bits_add",
            (Ty::Bits(_), Sub) => "bits_sub",
            (Ty::Bits(_), Mul) => "bits_mul",
            (Ty::Bits(_), BAnd) => "bits_and",
            (Ty::Bits(_), BOr) => "bits_or",
            (Ty::Bits(_), BXor) => "bits_xor",
            (Ty::Bits(_), Shl) => "bits_shl",
            (Ty::Bits(_), Sar) => "bits_sar",
            (Ty::Bits(_), Shr) => return Ok((self.b.app("bits_shr", vec![self.width(&ty), a, b]), ty)),
            (Ty::Bits(_), Div) => return Ok((self.b.app("int_div", vec![a, b]), ty)),
            (Ty::Bits(_), Mod) => return Ok((self.b.app("int_mod", vec![a, b]), ty)),
            // numbers are integers (naturals: the non-negative ones)
            (Ty::Int | Ty::Nat | Ty::Enum(_) | Ty::Unknown | Ty::NatInf, Add) => "int_add",
            (Ty::Int | Ty::Nat | Ty::Enum(_) | Ty::Unknown | Ty::NatInf, Sub) => "int_sub",
            (Ty::Int | Ty::Nat | Ty::Enum(_) | Ty::Unknown | Ty::NatInf, Mul) => "int_mul",
            (Ty::Int | Ty::Nat | Ty::Enum(_) | Ty::Unknown, Div) => "int_div",
            (Ty::Int | Ty::Nat | Ty::Enum(_) | Ty::Unknown, Mod) => "int_mod",
            (Ty::Nat | Ty::Unknown, BOr) => "int_or",
            (Ty::Nat | Ty::Unknown, BAnd) => "int_and",
            _ => return err(span, format!("operator {:?} on {}", op, ty.describe())),
        };
        let t = if name.starts_with("bits_") {
            let w = self.width(&ty);
            self.b.app(name, vec![w, a, b])
        } else {
            self.b.app(name, vec![a, b])
        };
        Ok((t, ty))
    }

    /// Width of `x[hi:lo]`, i.e. hi + 1 - lo; `x[e-1:0]` has width e.
    pub fn slice_width(&self, hi: &Term, lo: &Term) -> Term {
        let (hi, lo) = (self.b.norm(hi), self.b.norm(lo));
        if matches!(lo.node(), sl_kernel::Node::Nat(n) if n.is_zero()) {
            if let sl_kernel::Node::App(s, args) = hi.node() {
                if self.b.env.syms[*s as usize].name == "int_sub" && matches!(args[1].node(), sl_kernel::Node::Nat(n) if n.to_u64() == Some(1)) {
                    return args[0].clone();
                }
            }
        }
        self.b.norm(&self.b.app("int_sub", vec![self.b.app("int_add", vec![hi, self.b.nat(1)]), lo]))
    }

    pub fn width(&self, ty: &Ty) -> Term {
        match ty.strip() {
            Ty::Bits(w) => w.clone(),
            _ => self.b.nat(64),
        }
    }

    /// The set on the right of `x in S`.
    fn membership_set(&mut self, cx: &mut Cx, s: &Expr, elem: &Ty, span: Span) -> R<Term> {
        if let ExprKind::Binary(BinOp::Range, lo, hi) = &s.kind {
            let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
            let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
            return Ok(self.b.app("int_range", vec![l, h]));
        }
        // a type name (enum type, type parameter)
        if let ExprKind::Name(n) = &s.kind {
            if cx.local(&n.name).is_none() {
                if let Some((_, set)) = cx.gtys.get(&n.name) {
                    return Ok(set.clone());
                }
                if let Some(i) = self.g.find_decl(&cx.module, &n.name) {
                    if matches!(self.g.decls[i].decl.kind, DeclKind::Enum { .. } | DeclKind::Record { .. } | DeclKind::TypeDecl { .. }) {
                        let t = self.ty(cx, &Type::Named(n.clone(), vec![]))?;
                        return self.ty_set(&t, span);
                    }
                }
            }
        }
        let (t, _) = self.expr(cx, s, Some(&Ty::Set(Box::new(elem.clone()))))?;
        Ok(t)
    }

    // ------------------------------------------------------------------
    //  Indexing

    fn index(&mut self, cx: &mut Cx, a: &Expr, idx: &[Expr], _exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        if idx.len() != 1 {
            return err(span, "unexpected generic arguments (only allowed in calls)");
        }
        let (t, ty) = self.expr(cx, a, None)?;
        if let ExprKind::Binary(BinOp::Range, lo, hi) = &idx[0].kind {
            let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
            let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
            return Ok((self.b.app("seq_slice", vec![t, l, h]), ty));
        }
        match ty.strip() {
            Ty::Map(k, v) => {
                let (kt, _) = self.expr(cx, &idx[0], Some(k))?;
                Ok((self.b.app_fn(t, kt), (**v).clone()))
            }
            Ty::Bits(_) | Ty::Nat => {
                let (i, _) = self.expr(cx, &idx[0], Some(&Ty::Nat))?;
                Ok((self.b.app("bit", vec![t, i]), Ty::Bool))
            }
            Ty::List(e) | Ty::Seq(e) => {
                let (i, _) = self.expr(cx, &idx[0], Some(&Ty::Nat))?;
                Ok((self.b.app_fn(t, i), (**e).clone()))
            }
            Ty::Unknown => {
                let (i, _) = self.expr(cx, &idx[0], None)?;
                Ok((self.b.app_fn(t, i), Ty::Unknown))
            }
            Ty::Tuple(ts) => match &idx[0].kind {
                ExprKind::Num(n) if (n.to_u64().unwrap_or(u64::MAX) as usize) < ts.len() => {
                    let k = n.to_u64().unwrap() as usize;
                    Ok((self.b.proj(t, k, ts.len()), ts[k].clone()))
                }
                _ => err(span, "a tuple is indexed by a literal position"),
            },
            _ => err(span, format!("cannot index {}", ty.describe())),
        }
    }

    // ------------------------------------------------------------------
    //  Records, comprehensions, binders

    fn record_lit(&mut self, cx: &mut Cx, name: &Ident, fields: &[(Ident, Expr)], span: Span) -> R<(Term, Ty)> {
        let ty = self.ty(cx, &Type::Named(name.clone(), vec![]))?;
        let fs = match self.fields_of(&ty)? {
            Some(fs) => fs,
            None => return err(span, format!("`{}` is not a record", name.name)),
        };
        let mut vals = Vec::new();
        for (f, fty, _) in &fs {
            let e = match fields.iter().find(|x| x.0.name == *f) {
                Some((_, e)) => e,
                None => return err(span, format!("field `{}` missing in `{}` literal", f, name.name)),
            };
            let (t, et) = self.expr(cx, e, Some(fty))?;
            if !compatible(fty, &et) {
                return err(e.span, format!("field `{}` of `{}`: expected {}, got {}", f, name.name, fty.describe(), et.describe()));
            }
            vals.push((f.clone(), t));
        }
        for (f, _) in fields {
            if !fs.iter().any(|x| x.0 == f.name) {
                return err(f.span, format!("no field `{}` in `{}`", f.name, name.name));
            }
        }
        Ok((self.b.record(vals), ty))
    }

    fn list_comp(&mut self, cx: &mut Cx, elem: &Expr, pat: &Pattern, iter: &Expr, cond: Option<&Expr>, span: Span) -> R<(Term, Ty)> {
        if let (ExprKind::Binary(BinOp::Range, lo, hi), Pattern::Name(v), None) = (&iter.kind, pat, cond) {
            let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
            let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
            let i = self.fresh(&v.name);
            let val = self.b.app("int_add", vec![l.clone(), self.b.v(i)]);
            cx.push_local(&v.name, val, Ty::Nat, false);
            let r = self.pure_expr(cx, elem, None);
            cx.locals.pop();
            let (e, ety) = r?;
            let len = self.b.app("int_sub", vec![h, l]);
            return Ok((self.b.bind_app("fn_build", vec![len], &[i], &e), Ty::List(Box::new(ety))));
        }
        let (s, sty) = self.expr(cx, iter, None)?;
        let ety = match sty.strip() {
            Ty::List(t) | Ty::Seq(t) => (**t).clone(),
            _ => Ty::Unknown,
        };
        let x = self.fresh("x");
        let (pc, binds) = self.pattern(cx, pat, &self.b.v(x), &ety)?;
        let n0 = cx.locals.len();
        for (n, t, ty) in binds {
            cx.push_local(&n, t, ty, false);
        }
        let c = match cond {
            Some(c) => {
                let (ct, _) = self.pure_expr(cx, c, Some(&Ty::Bool))?;
                self.b.and(pc, ct)
            }
            None => pc,
        };
        let r = self.pure_expr(cx, elem, None);
        cx.locals.truncate(n0);
        let (e, rty) = r?;
        let filtered = self.b.bind_app("seq_filter", vec![s], &[x], &c);
        let _ = span;
        Ok((self.b.bind_app("seq_map", vec![filtered], &[x], &e), Ty::Seq(Box::new(rty))))
    }

    fn binder(&mut self, cx: &mut Cx, kind: BinderKind, vars: &[(Ident, Option<Type>)], domain: Option<&Expr>, body: &Expr, span: Span) -> R<(Term, Ty)> {
        if kind == BinderKind::Sum {
            let v = &vars[0].0;
            let dom = domain.unwrap();
            if let ExprKind::Binary(BinOp::Range, lo, hi) = &dom.kind {
                let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
                let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
                let i = self.fresh(&v.name);
                cx.push_local(&v.name, self.b.v(i), Ty::Nat, false);
                let r = self.pure_expr(cx, body, Some(&Ty::Nat));
                cx.locals.pop();
                let (e, _) = r?;
                return Ok((self.b.bind_app("int_sum", vec![l, h], &[i], &e), Ty::Nat));
            }
            let (s, sty) = self.expr(cx, dom, None)?;
            let ety = match sty.strip() {
                Ty::List(t) | Ty::Seq(t) => (**t).clone(),
                _ => Ty::Unknown,
            };
            let x = self.fresh(&v.name);
            cx.push_local(&v.name, self.b.v(x), ety, false);
            let r = self.pure_expr(cx, body, Some(&Ty::Nat));
            cx.locals.pop();
            let (e, _) = r?;
            return Ok((self.b.bind_app("seq_sum", vec![s], &[x], &e), Ty::NatInf));
        }
        let mut xs = Vec::new();
        let mut doms = Vec::new();
        let n0 = cx.locals.len();
        for (v, t) in vars {
            let ty = match t {
                Some(t) => self.ty(cx, t)?,
                None => return err(v.span, "quantified variables need a type (`all x: T. ...`)"),
            };
            let set = self.ty_set(&ty, span)?;
            let x = self.fresh(&v.name);
            doms.push(self.b.member(self.b.v(x), set));
            cx.push_local(&v.name, self.b.v(x), ty, false);
            xs.push(x);
        }
        let r = self.pure_expr(cx, body, Some(&Ty::Bool));
        cx.locals.truncate(n0);
        let (bt, _) = r?;
        let guard = self.b.ands(doms);
        let t = match kind {
            BinderKind::All => {
                let inner = self.b.imp(guard, bt);
                self.b.all(&xs, inner)
            }
            _ => {
                let inner = self.b.and(guard, bt);
                self.b.ex(&xs, inner)
            }
        };
        Ok((t, Ty::Bool))
    }

    /// `any x: T where P` (an effect in procedures).
    pub fn any_value(&mut self, cx: &mut Cx, name: &str, ty: Ty, cond: Option<&Expr>, span: Span) -> R<(Term, Ty)> {
        let (x, dom) = self.any_dom(cx, name, &ty, cond, span)?;
        cx.frames.push(Frame::Choose { var: x, dom });
        Ok((self.b.v(x), ty))
    }

    /// The choice of `any name: ty where cond`: its variable and the formula
    /// it must satisfy.
    pub fn any_dom(&mut self, cx: &mut Cx, name: &str, ty: &Ty, cond: Option<&Expr>, span: Span) -> R<(VarId, Term)> {
        if cx.pure {
            return err(span, "`any` is a nondeterministic choice: only in procedures");
        }
        let set = self.ty_set(ty, span)?;
        let x = self.fresh(name);
        let mut dom = self.b.member(self.b.v(x), set);
        if let Some(c) = cond {
            cx.push_local(name, self.b.v(x), ty.clone(), false);
            let r = self.pure_expr(cx, c, Some(&Ty::Bool));
            cx.locals.pop();
            let (ct, _) = r?;
            dom = self.b.and(dom, ct);
        }
        Ok((x, dom))
    }

    fn lambda(&mut self, cx: &mut Cx, params: &[Param], body: &Block, exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        let mut ptys = Vec::new();
        for p in params {
            ptys.push(self.ty(cx, &p.ty)?);
        }
        let x = self.fresh("x");
        let n = params.len();
        let n0 = cx.locals.len();
        let mut inner = cx.clone();
        inner.frames.clear();
        for (k, (p, t)) in params.iter().zip(&ptys).enumerate() {
            inner.push_local(&p.name.name, self.b.proj(self.b.v(x), k, n), t.clone(), false);
        }
        let dom = if n == 1 { self.ty_set(&ptys[0], span)? } else { self.ty_set(&Ty::Tuple(ptys.clone()), span)? };
        if let Some(Ty::Proc { state, ret, .. }) = exp.map(|t| t.strip()) {
            // a procedure value: arguments -> program
            let (st, rt) = ((**state).clone(), (**ret).clone());
            let prog = self.program(&inner, &st, body, &rt, span)?;
            cx.locals.truncate(n0);
            return Ok((
                self.b.bind_app("fn_build", vec![dom], &[x], &prog),
                Ty::Proc { state: Box::new(st), params: ptys, ret: Box::new(rt) },
            ));
        }
        inner.pure = true;
        let (v, vty) = self.block_value(&mut inner, body, None, span)?;
        if !inner.frames.is_empty() {
            return err(span, "a function value cannot execute programs");
        }
        Ok((self.b.bind_app("fn_build", vec![dom], &[x], &v), Ty::Map(Box::new(if n == 1 { ptys[0].clone() } else { Ty::Tuple(ptys) }), Box::new(vty))))
    }

    /// The value of a block used as an expression: its last statement.
    pub fn block_value(&mut self, cx: &mut Cx, b: &Block, exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        let n0 = cx.locals.len();
        let (last, init) = match b.stmts.split_last() {
            Some(x) => x,
            None => return Ok((self.b.empty(), Ty::Unit)),
        };
        let r = (|| {
            for s in init {
                self.stmt(cx, s)?;
            }
            match &last.kind {
                StmtKind::Expr(e) | StmtKind::Return(Some(e)) => self.expr(cx, e, exp),
                // `if` / `match` statements in value position are expressions
                StmtKind::If { cond, then, els: Some(els) } => {
                    let e = Expr { kind: ExprKind::If(Box::new(cond.clone()), then.clone(), Box::new(els.clone())), span: last.span };
                    self.expr(cx, &e, exp)
                }
                StmtKind::Match { scrut, arms } => {
                    let e = Expr { kind: ExprKind::Match(Box::new(scrut.clone()), arms.clone()), span: last.span };
                    self.expr(cx, &e, exp)
                }
                _ => err(span, "a block used as a value must end with an expression"),
            }
        })();
        cx.locals.truncate(n0);
        r
    }

    // ------------------------------------------------------------------
    //  Conditionals as expressions

    fn if_expr(&mut self, cx: &mut Cx, c: &Expr, a: &Block, b: &Block, exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        let (ct, _) = self.expr(cx, c, Some(&Ty::Bool))?;
        let r = self.fresh("r");
        let muts = cx.mut_indices();
        let mut ca = cx.clone();
        ca.frames.clear();
        ca.exits.push(Exit::Local { r, muts: muts.clone(), is_loop: false });
        let (ta, tya) = self.block_value(&mut ca, a, exp, span)?;
        let exp2 = exp.cloned().or(Some(tya.clone()));
        let mut cb = cx.clone();
        cb.frames.clear();
        cb.exits.push(Exit::Local { r, muts, is_loop: false });
        let (tb, _) = self.block_value(&mut cb, b, exp2.as_ref(), span)?;
        if ca.frames.is_empty() && cb.frames.is_empty() {
            return Ok((self.b.ite(ct, ta, tb), tya));
        }
        let nct = self.b.not(ct.clone());
        self.join_values(cx, r, vec![(ct, ca, ta), (nct, cb, tb)], tya, span)
    }

    fn match_expr(&mut self, cx: &mut Cx, s: &Expr, arms: &[Arm], exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        let (st, sty) = self.expr(cx, s, None)?;
        let r = self.fresh("r");
        let muts = cx.mut_indices();
        let mut prev: Vec<Term> = Vec::new();
        let mut raw: Vec<Term> = Vec::new();
        let mut branches = Vec::new();
        let mut rty: Option<Ty> = exp.cloned();
        for arm in arms {
            let mut alts = Vec::new();
            let mut binds = Vec::new();
            for p in &arm.pats {
                let (c, bs) = self.pattern(cx, p, &st, &sty)?;
                alts.push(c);
                if binds.is_empty() {
                    binds = bs;
                }
            }
            let cond = self.b.ors(alts);
            let mut guard = cond.clone();
            for p in &prev {
                guard = self.b.and(self.b.not(p.clone()), guard);
            }
            prev.push(cond.clone());
            raw.push(cond);
            let mut ca = cx.clone();
            ca.frames.clear();
            ca.exits.push(Exit::Local { r, muts: muts.clone(), is_loop: false });
            for (n, t, ty) in binds {
                ca.push_local(&n, t, ty, false);
            }
            let (v, vty) = self.block_value(&mut ca, &arm.body, rty.as_ref(), arm.span)?;
            if rty.is_none() || matches!(rty, Some(Ty::Unknown)) {
                rty = Some(vty);
            }
            branches.push((guard, ca, v));
        }
        let rty = rty.unwrap_or(Ty::Unknown);
        if branches.iter().all(|b| b.1.frames.is_empty()) {
            // ite chain (first match wins); the last arm is the default
            let mut it = branches.into_iter().zip(raw).rev();
            let ((_, _, last), _) = it.next().unwrap();
            let t = it.fold(last, |acc, ((_, _, v), c)| self.b.ite(c, v, acc));
            return Ok((t, rty));
        }
        self.join_values(cx, r, branches, rty, span)
    }

    /// Joins branches that executed programs through the local outcome `r`.
    fn join_values(&mut self, cx: &mut Cx, r: VarId, branches: Vec<(Term, Cx, Term)>, ty: Ty, span: Span) -> R<(Term, Ty)> {
        if cx.pure {
            return err(span, "programs executed in a conditional of a pure expression");
        }
        let mut alts = Vec::new();
        for (c, bcx, v) in branches {
            let fin = self.exit_normal(&bcx, v);
            let body = self.wrap_frames(bcx.frames, fin);
            alts.push(self.b.and(c, body));
        }
        let body = self.b.ors(alts);
        let value = self.finish_local(cx, r, body, false);
        Ok((value, ty))
    }

    /// Applies frames (innermost last) around `hole`.
    pub fn wrap_frames(&mut self, frames: Vec<Frame>, hole: Term) -> Term {
        let mut t = hole;
        for f in frames.into_iter().rev() {
            t = self.wrap(f, t);
        }
        t
    }

    pub fn wrap(&mut self, f: Frame, hole: Term) -> Term {
        match f {
            Frame::Let { var, value } => self.b.letin(value, var, &hole),
            Frame::Run { prog, s_in, s_out, v_out, exc: (es, ee, ef), div: (dt, df) } => self.b.bind_args(
                "bind_rel",
                vec![(vec![], prog), (vec![], s_in), (vec![s_out, v_out], hole), (vec![es, ee], ef), (vec![dt], df)],
            ),
            Frame::Choose { var, dom } => self.b.bind_args("any_rel", vec![(vec![var], dom), (vec![var], hole)]),
            Frame::Require(c) => self.b.or(self.b.not(c), hole),
            Frame::Guard { cond, fail } => {
                let a = self.b.and(cond.clone(), hole);
                let b = self.b.and(self.b.not(cond), fail);
                self.b.or(a, b)
            }
            Frame::Join { vars, body } => {
                let inner = self.b.and(body, hole);
                self.b.ex(&vars, inner)
            }
            Frame::Local { r, body, normal, abrupt } => {
                let cont = self.b.or(self.b.and(normal, hole), abrupt);
                let inner = self.b.and(body, cont);
                self.b.ex(&[r], inner)
            }
            Frame::Terminal(t) => t,
        }
    }

    // ------------------------------------------------------------------
    //  Programs as values

    /// A block as a program over `st` returning `ret`: `mkprog(s o. F)`.
    pub fn program(&mut self, outer: &Cx, st: &Ty, body: &Block, ret: &Ty, span: Span) -> R<Term> {
        let s = self.fresh("s");
        let o = self.fresh("o");
        let mut cx = outer.clone();
        cx.pure = false;
        cx.frames.clear();
        cx.state = Some(self.b.v(s));
        cx.state_ty = Some(st.clone());
        cx.exits = vec![Exit::Proc { o }];
        // outer locals stay visible, but not mutable from inside
        for l in cx.locals.iter_mut() {
            l.mutable = false;
        }
        let _ = ret;
        let f = self.block_formula(&mut cx, body, span)?;
        Ok(self.b.bind_app("mkprog", vec![], &[s, o], &f))
    }

    /// `with view(args) { body }`: run `body` over the view's state.
    fn with_view(&mut self, cx: &mut Cx, v: &Expr, body: &Block, exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        let (vname, vargs) = match &v.kind {
            ExprKind::Call(f, args) => match &f.kind {
                ExprKind::Name(n) => (n.clone(), args.clone()),
                _ => return err(span, "`with` needs a view call"),
            },
            _ => return err(span, "`with` needs a view call"),
        };
        let i = match self.g.find_decl(&cx.module, &vname.name) {
            Some(i) if matches!(self.g.decls[i].decl.kind, DeclKind::View { .. }) => i,
            _ => return err(vname.span, format!("`{}` is not a view", vname.name)),
        };
        self.ensure(i)?;
        let gsig = self.sig_of(i, "get")?;
        let ssig = self.sig_of(i, "set")?;
        let outer_st = match cx.state_ty.clone() {
            Some(Ty::State(s)) => s,
            _ => return err(span, "`with` outside a procedure"),
        };
        let inner_base = match gsig.ret.strip() {
            Ty::State(s) => s.clone(),
            _ => return err(span, "`with` needs a view whose value is a state"),
        };
        // the inner state keeps the outer state's extensions (ghost fields)
        let inner_st = StateTy { base: inner_base.base.clone(), ext: outer_st.ext.clone() };
        let mut args = Vec::new();
        for (a, p) in vargs.iter().zip(&gsig.params) {
            let (t, _) = self.expr(cx, a, Some(&p.2))?;
            args.push(t);
        }
        let mut gargs = self.lift_args(cx, &gsig, span)?;
        gargs.extend(args.clone());
        let get = self.b.app(&gsig.core, gargs);
        let w0 = self.run_prog(cx, get, gsig.ret.clone(), span)?;
        // inner state: the view's value plus the ghost part of the outer state
        let okeys = self.base_keys(&StateTy { base: outer_st.base.clone(), ext: vec![] })?;
        let ghost = self.b.app("ghost_part", vec![cx.state.clone().unwrap(), okeys.clone()]);
        let w0g = self.b.app("rec_merge", vec![w0, ghost]);
        let rt = exp.cloned().unwrap_or(Ty::Unknown);
        let prog = self.program(cx, &Ty::State(inner_st.clone()), body, &rt, span)?;
        // run the body from w0g
        let s_before = cx.state.clone().unwrap();
        let w1 = self.fresh("w");
        let r = self.fresh("v");
        let es = self.fresh("s");
        let ee = self.fresh("e");
        let dt = self.fresh("t");
        // exceptions and divergence of the body propagate (after writing back)
        let ikeys = self.base_keys(&StateTy { base: inner_st.base.clone(), ext: vec![] })?;
        let exc_state = {
            let back = self.b.app("restrict", vec![self.b.v(es), ikeys.clone()]);
            let _ = back;
            // on exceptions the world is written back without running `set`
            self.b.v(es)
        };
        let _ = exc_state;
        let ef = {
            let s2 = self.b.app("rec_merge", vec![
                self.b.app("ghost_part", vec![s_before.clone(), self.b.app("union2", vec![okeys.clone(), ikeys.clone()])]),
                self.b.app("ghost_part", vec![self.b.v(es), ikeys.clone()]),
            ]);
            let merged = self.b.app("rec_merge", vec![self.b.app("restrict", vec![s_before.clone(), okeys.clone()]), s2]);
            self.exit_raise(cx, merged, self.b.v(ee))
        };
        let df = self.exit_div(cx, self.b.v(dt));
        cx.frames.push(Frame::Run { prog, s_in: w0g, s_out: w1, v_out: r, exc: (es, ee, ef), div: (dt, df) });
        cx.state = Some(s_before);
        // write back through the view's setter, then restore the ghost part
        let mut sargs = self.lift_args(cx, &ssig, span)?;
        sargs.extend(args);
        let wv = self.b.app("restrict", vec![self.b.v(w1), ikeys.clone()]);
        sargs.push(wv);
        let set = self.b.app(&ssig.core, sargs);
        self.run_prog(cx, set, Ty::Unit, span)?;
        let after = cx.state.clone().unwrap();
        let newghost = self.b.app("ghost_part", vec![self.b.v(w1), ikeys]);
        let st2 = self.b.app("rec_merge", vec![self.b.app("restrict", vec![after, okeys]), newghost]);
        let sv = self.fresh("s");
        cx.frames.push(Frame::Let { var: sv, value: st2 });
        cx.state = Some(self.b.v(sv));
        Ok((self.b.v(r), rt))
    }

    /// Executes a program in the current procedure: returns its value.
    pub fn run_prog(&mut self, cx: &mut Cx, prog: Term, ret: Ty, span: Span) -> R<Term> {
        if cx.pure {
            return err(span, "a program is executed in a pure context");
        }
        let _ = ret;
        let s_in = cx.state.clone().unwrap();
        let s_out = self.fresh("s");
        let v_out = self.fresh("v");
        let es = self.fresh("s");
        let ee = self.fresh("e");
        let ef = self.exit_raise(cx, self.b.v(es), self.b.v(ee));
        let dt = self.fresh("t");
        let df = self.exit_div(cx, self.b.v(dt));
        cx.frames.push(Frame::Run { prog, s_in, s_out, v_out, exc: (es, ee, ef), div: (dt, df) });
        cx.state = Some(self.b.v(s_out));
        Ok(self.b.v(v_out))
    }

    // ------------------------------------------------------------------
    //  Calls

    fn call(&mut self, cx: &mut Cx, f: &Expr, args: &[Expr], exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        // explicit generics / conversions: f[g](args)
        if let ExprKind::Index(inner, gargs) = &f.kind {
            if let ExprKind::Name(n) = &inner.kind {
                if cx.local(&n.name).is_none() && !self.is_state_field(cx, &n.name)? {
                    return self.generic_call(cx, n, gargs, args, exp, span);
                }
            }
        }
        // table members: x86.decode(b)
        if let ExprKind::Field(t, m) = &f.kind {
            if let ExprKind::Name(tn) = &t.kind {
                if cx.local(&tn.name).is_none() {
                    if let Some(i) = self.g.find_decl(&cx.module, &tn.name) {
                        if matches!(self.g.decls[i].decl.kind, DeclKind::Table(_)) {
                            return self.table_call(cx, i, m, args, span);
                        }
                    }
                }
            }
        }
        let name = match &f.kind {
            ExprKind::Name(n) => n.clone(),
            _ => {
                // a proc-typed value
                let (ft, fty) = self.expr(cx, f, None)?;
                return self.call_value(cx, ft, &fty, args, span);
            }
        };
        if let Some(l) = cx.local(&name.name).cloned() {
            return self.call_value(cx, l.term, &l.ty, args, span);
        }
        if let Some(r) = self.builtin_call(cx, &name, args, exp, span)? {
            return Ok(r);
        }
        if let Some((t, _)) = cx.gtys.get(&name.name).cloned() {
            // conversion of a number to a type parameter (an enum kind)
            let (x, _) = self.expr(cx, &args[0], Some(&Ty::Nat))?;
            return Ok((x, t));
        }
        let cands = self.global_candidates(&cx.module, &name.name);
        let chosen = self.choose_candidate(&cands, exp);
        match chosen {
            Some(GName::Ctor(i, j)) => self.ctor_app(cx, i, j, args, span),
            Some(GName::Decl(i)) => self.decl_call(cx, i, &[], args, exp, span),
            Some(GName::EnumVal(..)) => err(span, format!("`{}` is an enum value, not a function", name.name)),
            None => err(name.span, format!("unknown function `{}`", name.name)),
        }
    }

    fn is_state_field(&mut self, cx: &Cx, name: &str) -> R<bool> {
        if let Some(st) = cx.state_ty.clone() {
            if let Some(fs) = self.fields_of(&st)? {
                return Ok(fs.iter().any(|f| f.0 == name));
            }
        }
        Ok(false)
    }

    /// Calls a proc-typed value `spec(args)`.
    fn call_value(&mut self, cx: &mut Cx, ft: Term, fty: &Ty, args: &[Expr], span: Span) -> R<(Term, Ty)> {
        match fty.strip() {
            Ty::Proc { state, params, ret } => {
                let mut ts = Vec::new();
                for (a, p) in args.iter().zip(params) {
                    ts.push(self.expr(cx, a, Some(p))?.0);
                }
                let prog = self.b.app_fn(ft, self.b.tuple(ts));
                self.use_program(cx, prog, state, ret, span)
            }
            Ty::Map(k, v) => {
                let (kt, _) = self.expr(cx, &args[0], Some(k))?;
                Ok((self.b.app_fn(ft, kt), (**v).clone()))
            }
            _ => err(span, format!("calling a value of type {}", fty.describe())),
        }
    }

    /// A program in a procedure is executed; in a pure context it is a value.
    fn use_program(&mut self, cx: &mut Cx, prog: Term, state: &Ty, ret: &Ty, span: Span) -> R<(Term, Ty)> {
        if cx.pure {
            return Ok((prog, Ty::Prog(Box::new(state.clone()), Box::new(ret.clone()))));
        }
        if let (Some(Ty::State(cur)), Ty::State(want)) = (&cx.state_ty, state.strip()) {
            if cur.base != want.base && !want.base.starts_with("$decoder") {
                return err(span, format!("calls a procedure over `{}` from a procedure over `{}` (use `with`)", want.base, cur.base));
            }
        }
        let v = self.run_prog(cx, prog, ret.clone(), span)?;
        Ok((v, ret.clone()))
    }

    /// Call of a global declaration (fn / pred / proc / view / decoder / param).
    pub fn decl_call(&mut self, cx: &mut Cx, i: usize, gargs: &[Expr], args: &[Expr], exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        self.ensure(i)?;
        let kind = self.g.decls[i].decl.kind.clone();
        let name = self.g.decls[i].decl.name().map(|n| n.name.clone()).unwrap_or_default();
        match &kind {
            DeclKind::Exception { params, .. } => {
                let module = self.module_of(i);
                let hcx = Cx::new(&module);
                let mut ts = Vec::new();
                for (p, a) in params.iter().zip(args) {
                    let pt = self.ty(&hcx, &p.ty)?;
                    ts.push(self.expr(cx, a, Some(&pt))?.0);
                }
                return Ok((self.b.app("exc_val", vec![self.b.str(&name), self.b.tuple(ts)]), Ty::Exc));
            }
            DeclKind::Enum { .. } => {
                // conversion from a number
                let (t, _) = self.expr(cx, &args[0], Some(&Ty::Nat))?;
                return Ok((t, Ty::Enum(self.g.decls[i].qual.clone())));
            }
            DeclKind::ParamPred { .. } | DeclKind::ParamFn { .. } => {
                let sig = self.sig_of(i, "")?;
                let mut ts = Vec::new();
                for (a, p) in args.iter().zip(&sig.params) {
                    ts.push(self.expr(cx, a, Some(&p.2))?.0);
                }
                let var = match cx.lift.get(&sig.core) {
                    Some(v) => v.clone(),
                    None => return err(span, format!("layer parameter `{}` not in scope", sig.core)),
                };
                let x = self.b.tuple(ts);
                return Ok(if matches!(kind, DeclKind::ParamPred { .. }) {
                    (self.b.member(x, var), Ty::Bool)
                } else {
                    (self.b.app_fn(var, x), sig.ret.clone())
                });
            }
            _ => {}
        }
        let which = if matches!(kind, DeclKind::View { .. }) { "get" } else { "" };
        let sig = self.sig_of(i, which)?;
        let (vals, tys, argts) = self.bind_args(cx, &sig, gargs, args, span)?;
        let mut call_args = self.lift_args(cx, &sig, span)?;
        for g in &sig.generics {
            match &g.val_ty {
                Some(_) => call_args.push(vals.get(&g.var).cloned().unwrap_or_else(|| self.b.v(g.var))),
                None => {
                    let t = match tys.get(&g.name) {
                        Some(t) => self.ty_arg_set(t, span)?,
                        None => {
                            self.warn(span, format!("could not infer type parameter `{}` of `{}`", g.name, sig.core));
                            self.b.app("univ", vec![self.b.nat(1)])
                        }
                    };
                    call_args.push(t);
                }
            }
        }
        call_args.extend(argts);
        let ret = self.subst_ty(&sig.ret, &vals, &tys);
        let term = self.b.app(&sig.core, call_args);
        let _ = exp;
        match &sig.kind {
            SigKind::Proc(st) => {
                let st = self.subst_ty(st, &vals, &tys);
                self.use_program(cx, term, &st, &ret, span)
            }
            _ => Ok((term, ret)),
        }
    }

    /// Set term for an inferred type argument.
    fn ty_arg_set(&mut self, t: &Ty, span: Span) -> R<Term> {
        match t {
            Ty::State(st) if st.base.is_empty() => self.ext_set(&st.ext, span),
            _ => self.ty_set(t, span),
        }
    }

    /// Elaborates arguments against a signature, inferring generics.
    pub fn bind_args(&mut self, cx: &mut Cx, sig: &Sig, gargs: &[Expr], args: &[Expr], span: Span) -> R<(HashMap<VarId, Term>, HashMap<String, Ty>, Vec<Term>)> {
        if args.len() != sig.params.len() {
            return err(span, format!("`{}` takes {} arguments, {} given", sig.core, sig.params.len(), args.len()));
        }
        let mut vals: HashMap<VarId, Term> = HashMap::new();
        let mut tys: HashMap<String, Ty> = HashMap::new();
        // explicit generic arguments
        for (g, a) in sig.generics.iter().zip(gargs) {
            match &g.val_ty {
                Some(t) => {
                    let (v, _) = self.expr(cx, a, Some(t))?;
                    vals.insert(g.var, self.b.norm(&v));
                }
                None => {
                    let t = self.expr_as_type(cx, a)?;
                    tys.insert(g.name.clone(), t);
                }
            }
        }
        if let (Some(sv), Some(st)) = (sig.state_var, cx.state.clone()) {
            vals.insert(sv, st);
        }
        let mut out: Vec<Option<Term>> = vec![None; args.len()];
        let mut deferred = Vec::new();
        for (k, (a, p)) in args.iter().zip(&sig.params).enumerate() {
            // earlier parameters appear in later parameter types
            let pty = self.subst_ty(&p.2, &vals, &tys);
            let known = !self.has_generics(&pty, &sig.generics, &vals, &tys);
            if known || !literalish(a) {
                let (t, aty) = self.expr(cx, a, if known { Some(&pty) } else { None })?;
                self.unify(&pty, &aty, &sig.generics, &mut vals, &mut tys);
                let pty = self.subst_ty(&p.2, &vals, &tys);
                self.check_arg(sig, k, &pty, &aty, a.span)?;
                vals.insert(p.1, t.clone());
                out[k] = Some(t);
            } else {
                deferred.push(k);
            }
        }
        for k in deferred {
            let pty = self.subst_ty(&sig.params[k].2, &vals, &tys);
            let (t, aty) = self.expr(cx, &args[k], Some(&pty))?;
            self.unify(&pty, &aty, &sig.generics, &mut vals, &mut tys);
            let pty = self.subst_ty(&sig.params[k].2, &vals, &tys);
            self.check_arg(sig, k, &pty, &aty, args[k].span)?;
            vals.insert(sig.params[k].1, t.clone());
            out[k] = Some(t);
        }
        // parameter placeholders are not generics: keep only generic bindings for types
        Ok((vals, tys, out.into_iter().map(|t| t.unwrap()).collect()))
    }

    fn check_arg(&mut self, sig: &Sig, k: usize, p: &Ty, a: &Ty, span: Span) -> R<()> {
        if !compatible(p, a) {
            return err(span, format!("argument `{}` of `{}`: expected {}, got {}", sig.params[k].0, sig.core, p.describe(), a.describe()));
        }
        self.check_width(p, a, span);
        Ok(())
    }

    /// Different literal widths are an error, different symbolic ones a warning.
    pub fn check_width(&mut self, e: &Ty, a: &Ty, span: Span) {
        if let (Ty::Bits(x), Ty::Bits(y)) = (e.strip(), a.strip()) {
            let (x, y) = (self.b.norm(x), self.b.norm(y));
            if x != y {
                let lit = |t: &Term| matches!(t.node(), sl_kernel::Node::Nat(_));
                let p = sl_kernel::syntax::Printer::new(&self.b.env);
                let msg = if lit(&x) && lit(&y) {
                    format!("width mismatch: bits[{}] expected, bits[{}] given", p.term(&x), p.term(&y))
                } else {
                    format!("could not show the widths equal: bits[{}] expected, bits[{}] given", p.term(&x), p.term(&y))
                };
                if lit(&x) && lit(&y) {
                    self.diags.push(Diag { span, msg, warning: false });
                } else {
                    self.warn(span, msg);
                }
            }
        }
    }

    fn has_generics(&self, t: &Ty, gens: &[GenParam], vals: &HashMap<VarId, Term>, tys: &HashMap<String, Ty>) -> bool {
        let mut vs = Vec::new();
        let mut names = Vec::new();
        collect_ty_vars(t, &mut vs, &mut names);
        gens.iter().any(|g| (vs.contains(&g.var) && !vals.contains_key(&g.var)) || (names.contains(&g.name) && !tys.contains_key(&g.name)))
    }

    fn expr_as_type(&mut self, cx: &mut Cx, e: &Expr) -> R<Ty> {
        match &e.kind {
            ExprKind::Name(n) => self.ty(cx, &Type::Named(n.clone(), vec![])),
            _ => err(e.span, "expected a type"),
        }
    }

    /// `name[g](args)`: conversions and explicit generic instantiation.
    fn generic_call(&mut self, cx: &mut Cx, n: &Ident, gargs: &[Expr], args: &[Expr], exp: Option<&Ty>, span: Span) -> R<(Term, Ty)> {
        match n.name.as_str() {
            "bits" | "zext" | "sext" => {
                let (w, _) = self.expr(cx, &gargs[0], Some(&Ty::Nat))?;
                let w = self.b.norm(&w);
                if args.len() != 1 {
                    return err(span, format!("`{}[n]` takes one argument", n.name));
                }
                let (x, xty) = self.expr(cx, &args[0], None)?;
                let out = Ty::Bits(w.clone());
                let t = match (n.name.as_str(), xty.strip()) {
                    ("zext", Ty::Bits(_)) => x,
                    ("sext", Ty::Bits(m)) => self.b.app("bits_sext", vec![m.clone(), w, x]),
                    ("bits", Ty::Int | Ty::Nat | Ty::Bits(_) | Ty::Enum(_) | Ty::Unknown | Ty::NatInf) => self.b.app("bits_of_int", vec![w, x]),
                    _ => return err(span, format!("`{}[..]` of {}", n.name, xty.describe())),
                };
                Ok((t, out))
            }
            _ => match self.g.find_decl(&cx.module, &n.name) {
                Some(i) => self.decl_call(cx, i, gargs, args, exp, span),
                None => err(n.span, format!("unknown function `{}`", n.name)),
            },
        }
    }

    fn builtin_call(&mut self, cx: &mut Cx, name: &Ident, args: &[Expr], exp: Option<&Ty>, span: Span) -> R<Option<(Term, Ty)>> {
        let one = |s: &mut Self, cx: &mut Cx, e: Option<&Ty>| -> R<(Term, Ty)> {
            if args.len() != 1 {
                return err(span, format!("`{}` takes one argument", name.name));
            }
            s.expr(cx, &args[0], e)
        };
        Ok(Some(match name.name.as_str() {
            "uint" => {
                let (t, _) = one(self, cx, None)?;
                (t, Ty::Nat)
            }
            "sint" => {
                let (t, ty) = one(self, cx, None)?;
                let w = self.width(&ty);
                (self.b.app("sint", vec![w, t]), Ty::Int)
            }
            "abs" => {
                let (t, _) = one(self, cx, Some(&Ty::Int))?;
                (self.b.app("int_abs", vec![t]), Ty::Nat)
            }
            "len" => {
                let (t, _) = one(self, cx, None)?;
                (self.b.app("seq_len", vec![t]), Ty::NatInf)
            }
            "min" | "max" => {
                let (t, _) = one(self, cx, None)?;
                (self.b.app(if name.name == "min" { "int_min" } else { "int_max" }, vec![t]), Ty::Nat)
            }
            "concat" => {
                let (t, ty) = one(self, cx, None)?;
                let inner = match ty.strip() {
                    Ty::Seq(t) | Ty::List(t) => (**t).clone(),
                    _ => Ty::Unknown,
                };
                (self.b.app("seq_flatten", vec![t]), inner)
            }
            "some" => {
                let inner = match exp.map(|t| t.strip()) {
                    Some(Ty::Opt(t)) => Some((**t).clone()),
                    _ => None,
                };
                let (t, ty) = one(self, cx, inner.as_ref())?;
                (self.b.app("some", vec![t]), Ty::Opt(Box::new(ty)))
            }
            "outcome" => {
                if args.len() != 3 {
                    return err(span, "`outcome(s, p, o)` takes three arguments");
                }
                let (s, _) = self.expr(cx, &args[0], None)?;
                let (p, _) = self.expr(cx, &args[1], None)?;
                let (o, _) = self.expr(cx, &args[2], None)?;
                (self.b.app("runs", vec![p, s, o]), Ty::Bool)
            }
            "ok" | "exc" | "diverge" => {
                let ts = args.iter().map(|a| self.expr(cx, a, None).map(|x| x.0)).collect::<R<Vec<_>>>()?;
                (self.b.app(&name.name, ts), Ty::Outcome(Box::new(Ty::Unknown), Box::new(Ty::Unknown)))
            }
            "next" | "peek" => {
                if cx.pure || !matches!(&cx.state_ty, Some(Ty::State(s)) if s.base.starts_with("$decoder")) {
                    return err(span, format!("`{}()` is only available in decoders", name.name));
                }
                let s = cx.state.clone().unwrap();
                let pos = self.b.field(s.clone(), "pos");
                let v = self.b.app_fn(self.b.field(s.clone(), "bytes"), pos.clone());
                if name.name == "next" {
                    let s2 = self.b.fn_update(s, self.b.str("pos"), self.b.app("int_add", vec![pos, self.b.nat(1)]));
                    let sv = self.fresh("s");
                    cx.frames.push(Frame::Let { var: sv, value: s2 });
                    cx.state = Some(self.b.v(sv));
                }
                (v, Ty::Bits(self.b.nat(8)))
            }
            _ => return Ok(None),
        }))
    }

    /// `table.decode(bytes)` / `table.execute(insn)`.
    fn table_call(&mut self, cx: &mut Cx, i: usize, m: &Ident, args: &[Expr], span: Span) -> R<(Term, Ty)> {
        self.ensure(i)?;
        let qual = self.g.decls[i].qual.clone();
        match m.name.as_str() {
            "decode" => {
                let (b, _) = self.expr(cx, &args[0], None)?;
                Ok((
                    self.b.app(&format!("{}.decode", qual), vec![b]),
                    Ty::Set(Box::new(Ty::Tuple(vec![Ty::Nat, Ty::Insn(qual)]))),
                ))
            }
            "execute" => {
                let (x, _) = self.expr(cx, &args[0], None)?;
                let prog = self.b.app(&format!("{}.execute", qual), vec![x]);
                let st = self.default_state(cx, span)?;
                self.use_program(cx, prog, &st, &Ty::Unit, span)
            }
            _ => err(m.span, format!("tables have `decode` and `execute`, not `{}`", m.name)),
        }
    }

    // ------------------------------------------------------------------
    //  Patterns

    /// Condition and bindings for matching `t: ty` against `p`.
    pub fn pattern(&mut self, cx: &mut Cx, p: &Pattern, t: &Term, ty: &Ty) -> R<(Term, Vec<(String, Term, Ty)>)> {
        match p {
            Pattern::Wild(_) => Ok((self.b.tru(), vec![])),
            Pattern::Num(n, _) => Ok((self.b.eq(t.clone(), self.b.natn(n.clone())), vec![])),
            Pattern::Bool(v, _) => Ok((if *v { t.clone() } else { self.b.not(t.clone()) }, vec![])),
            Pattern::Tuple(ps, _) => {
                let tys = match ty.strip() {
                    Ty::Tuple(ts) if ts.len() == ps.len() => ts.clone(),
                    _ => vec![Ty::Unknown; ps.len()],
                };
                let mut conds = Vec::new();
                let mut binds = Vec::new();
                for (k, (sp, st)) in ps.iter().zip(&tys).enumerate() {
                    let (c, bs) = self.pattern(cx, sp, &self.b.proj(t.clone(), k, ps.len()), st)?;
                    conds.push(c);
                    binds.extend(bs);
                }
                Ok((self.b.ands(conds), binds))
            }
            Pattern::Name(n) => {
                // a nullary constructor / enum value of the scrutinee's type, or a binding
                if let Some(c) = self.constant_pattern(cx, &n.name, ty)? {
                    return Ok((self.b.eq(t.clone(), c), vec![]));
                }
                Ok((self.b.tru(), vec![(n.name.clone(), t.clone(), ty.clone())]))
            }
            Pattern::Ctor(n, ps) => self.ctor_pattern(cx, n, ps, t, ty),
        }
    }

    fn constant_pattern(&mut self, cx: &Cx, name: &str, ty: &Ty) -> R<Option<Term>> {
        if name == "none" && matches!(ty.strip(), Ty::Opt(_) | Ty::Unknown) {
            return Ok(Some(self.b.c("none")));
        }
        for c in self.global_candidates(&cx.module, name) {
            match (&c, ty.strip()) {
                (GName::EnumVal(i, j), Ty::Enum(q)) if &self.g.decls[*i].qual == q => {
                    let vals = self.enum_values(*i)?;
                    return Ok(Some(self.b.natn(vals[*j].1.clone())));
                }
                (GName::EnumVal(i, j), Ty::Param(..) | Ty::Unknown) => {
                    let vals = self.enum_values(*i)?;
                    return Ok(Some(self.b.natn(vals[*j].1.clone())));
                }
                (GName::Ctor(i, j), Ty::Sum(q)) if &self.g.decls[*i].qual == q => {
                    return Ok(Some(self.b.tag(*j as u64, self.b.empty())));
                }
                _ => {}
            }
        }
        Ok(None)
    }

    fn tagged_pattern(&mut self, cx: &mut Cx, t: &Term, k: u64, subs: Vec<(Term, Ty)>, ps: &[Pattern]) -> R<(Term, Vec<(String, Term, Ty)>)> {
        let mut conds = vec![self.b.eq(self.b.fst(t.clone()), self.b.nat(k))];
        let mut binds = Vec::new();
        for (sp, (st, sty)) in ps.iter().zip(subs) {
            let (c, bs) = self.pattern(cx, sp, &st, &sty)?;
            conds.push(c);
            binds.extend(bs);
        }
        Ok((self.b.ands(conds), binds))
    }

    fn ctor_pattern(&mut self, cx: &mut Cx, n: &Ident, ps: &[Pattern], t: &Term, ty: &Ty) -> R<(Term, Vec<(String, Term, Ty)>)> {
        let payload = self.b.snd(t.clone());
        let n_args = ps.len();
        if n.name == "some" {
            let inner = match ty.strip() {
                Ty::Opt(x) => (**x).clone(),
                _ => Ty::Unknown,
            };
            return self.tagged_pattern(cx, t, 1, vec![(payload.clone(), inner)], ps);
        }
        if matches!(n.name.as_str(), "ok" | "exc" | "diverge") && matches!(ty.strip(), Ty::Outcome(..) | Ty::Unknown) {
            let (st, vt) = match ty.strip() {
                Ty::Outcome(a, b) => ((**a).clone(), (**b).clone()),
                _ => (Ty::Unknown, Ty::Unknown),
            };
            let p0 = self.b.proj(payload.clone(), 0, 2);
            let p1 = self.b.proj(payload.clone(), 1, 2);
            let _ = n_args;
            return match n.name.as_str() {
                "ok" => self.tagged_pattern(cx, t, 0, vec![(p0, st), (p1, vt)], ps),
                "exc" => self.tagged_pattern(cx, t, 1, vec![(p0, st), (p1, Ty::Exc)], ps),
                _ => {
                    let tr = Ty::State(StateTy { base: "$trace".into(), ext: vec![] });
                    self.tagged_pattern(cx, t, 2, vec![(payload.clone(), tr)], ps)
                }
            };
        }
        // exception patterns
        if matches!(ty.strip(), Ty::Exc) {
            if let Some(i) = self.g.find_decl(&cx.module, &n.name) {
                if let DeclKind::Exception { params, .. } = self.g.decls[i].decl.kind.clone() {
                    let module = self.module_of(i);
                    let mut conds = vec![self.b.eq(self.b.fst(t.clone()), self.b.str(&n.name))];
                    let mut binds = Vec::new();
                    let args = self.b.snd(t.clone());
                    for (k, (sp, pp)) in ps.iter().zip(&params).enumerate() {
                        let pt = self.ty(&Cx::new(&module), &pp.ty)?;
                        let (c, bs) = self.pattern(cx, sp, &self.b.proj(args.clone(), k, params.len()), &pt)?;
                        conds.push(c);
                        binds.extend(bs);
                    }
                    return Ok((self.b.ands(conds), binds));
                }
            }
        }
        // sum constructors
        for c in self.global_candidates(&cx.module, &n.name) {
            if let GName::Ctor(i, j) = c {
                let fits = match ty.strip() {
                    Ty::Sum(q) => &self.g.decls[i].qual == q,
                    _ => true,
                };
                if !fits {
                    continue;
                }
                let module = self.module_of(i);
                let vs = match &self.g.decls[i].decl.kind {
                    DeclKind::TypeDecl { def: TypeDef::Sum(vs), .. } => vs.clone(),
                    _ => unreachable!(),
                };
                let v = &vs[j];
                if v.params.len() != ps.len() {
                    return err(n.span, format!("`{}` has {} fields", n.name, v.params.len()));
                }
                let mut subs = Vec::new();
                for (k, pp) in v.params.iter().enumerate() {
                    let pt = self.ty(&Cx::new(&module), &pp.ty)?;
                    subs.push((self.b.proj(payload.clone(), k, v.params.len()), pt));
                }
                return self.tagged_pattern(cx, t, j as u64, subs, ps);
            }
        }
        err(n.span, format!("unknown constructor `{}` in pattern", n.name))
    }
}

/// Whether a value of type `a` may be used where `e` is expected. Numbers:
/// nat and int mix (nat is a subset of int); bits only with bits (widths
/// are compared separately) or enum values; unknown types always fit.
pub fn compatible(e: &Ty, a: &Ty) -> bool {
    use Ty::*;
    match (e.strip(), a.strip()) {
        (Unknown, _) | (_, Unknown) | (Param(..), _) | (_, Param(..)) => true,
        (Nat | Int | NatInf, Nat | Int | NatInf) => true,
        (Bits(_), Bits(_)) => true,
        (Bits(_) | Nat, Enum(_)) | (Enum(_), Bits(_) | Nat) => true,
        (Enum(x), Enum(y)) => x == y,
        (Bool, Bool) | (Str, Str) | (Unit, Unit) | (Exc, Exc) => true,
        (Tuple(x), Tuple(y)) => x.len() == y.len() && x.iter().zip(y).all(|(p, q)| compatible(p, q)),
        (Map(k1, v1), Map(k2, v2)) => compatible(k1, k2) && compatible(v1, v2),
        (List(x) | Seq(x), List(y) | Seq(y)) => compatible(x, y),
        (Set(x), Set(y)) | (Opt(x), Opt(y)) => compatible(x, y),
        (Rec(x), Rec(y)) | (Sum(x), Sum(y)) | (Insn(x), Insn(y)) => x == y,
        (State(x), State(y)) => x.base == y.base || x.base.is_empty() || y.base.is_empty(),
        (Proc { .. }, Proc { .. }) | (Prog(..), Prog(..)) | (Outcome(..), Outcome(..)) => true,
        _ => false,
    }
}

pub fn collect_ty_vars(t: &Ty, vs: &mut Vec<VarId>, names: &mut Vec<String>) {
    let term_vars = |x: &Term, vs: &mut Vec<VarId>| x.vars(vs);
    match t {
        Ty::Bits(w) => term_vars(w, vs),
        Ty::Param(n, _) => names.push(n.clone()),
        Ty::State(s) => {
            for e in &s.ext {
                if let Ext::Param(n, _) = e {
                    names.push(n.clone())
                }
            }
        }
        Ty::Tuple(ts) => ts.iter().for_each(|t| collect_ty_vars(t, vs, names)),
        Ty::Map(a, b) | Ty::Outcome(a, b) | Ty::Prog(a, b) => {
            collect_ty_vars(a, vs, names);
            collect_ty_vars(b, vs, names)
        }
        Ty::List(a) | Ty::Seq(a) | Ty::Set(a) | Ty::Opt(a) | Ty::Refine(a, _) => collect_ty_vars(a, vs, names),
        Ty::Proc { state, params, ret } => {
            collect_ty_vars(state, vs, names);
            params.iter().for_each(|p| collect_ty_vars(p, vs, names));
            collect_ty_vars(ret, vs, names)
        }
        _ => {}
    }
}

#[allow(dead_code)]
fn nat_of(t: &Term) -> Option<Nat> {
    match t.node() {
        sl_kernel::Node::Nat(n) => Some(n.clone()),
        _ => None,
    }
}
