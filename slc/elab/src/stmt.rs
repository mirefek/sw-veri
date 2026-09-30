//! Statements.

use crate::elab::*;
use crate::ty::Ty;
use sl_kernel::{Term, VarId};
use sl_syntax::ast::*;

/// A path to an assigned location.
enum Root {
    Local(usize),
    State,
    View(usize, Vec<Expr>),
}

enum Step {
    Field(String),
    Index(Term, Ty),
    /// hi, lo, width of the sliced value
    Slice(Term, Term, Term),
}

impl<'s> Elab<'s> {
    // ------------------------------------------------------------------
    //  Exits

    fn vars_tuple(&self, cx: &Cx, muts: &[usize]) -> Term {
        self.b.tuple(muts.iter().map(|&i| cx.locals[i].term.clone()).collect())
    }

    fn local_state(&self, cx: &Cx, muts: &[usize]) -> Term {
        self.b.pair(cx.state.clone().unwrap_or_else(|| self.b.empty()), self.vars_tuple(cx, muts))
    }

    fn kind_val(&self, kind: &str, v: Term) -> Term {
        self.b.pair(self.b.str(kind), v)
    }

    pub fn exit_normal(&mut self, cx: &Cx, value: Term) -> Term {
        match cx.exits.last() {
            Some(Exit::Proc { o }) => self.b.eq(self.b.v(*o), self.b.app("ok", vec![cx.state.clone().unwrap(), value])),
            Some(Exit::Local { r, muts, .. }) => {
                let l = self.local_state(cx, muts);
                self.b.eq(self.b.v(*r), self.b.app("ok", vec![l, value]))
            }
            None => self.b.tru(),
        }
    }

    pub fn exit_ret(&mut self, cx: &Cx, v: Term) -> Term {
        match cx.exits.last() {
            Some(Exit::Proc { o }) => self.b.eq(self.b.v(*o), self.b.app("ok", vec![cx.state.clone().unwrap(), v])),
            Some(Exit::Local { r, muts, .. }) => {
                let l = self.local_state(cx, muts);
                self.b.eq(self.b.v(*r), self.b.app("exc", vec![l, self.kind_val("ret", v)]))
            }
            None => self.b.tru(),
        }
    }

    pub fn exit_raise(&mut self, cx: &Cx, s: Term, e: Term) -> Term {
        match cx.exits.last() {
            Some(Exit::Proc { o }) => self.b.eq(self.b.v(*o), self.b.app("exc", vec![s, e])),
            Some(Exit::Local { r, muts, .. }) => {
                let l = self.b.pair(s, self.vars_tuple(cx, muts));
                self.b.eq(self.b.v(*r), self.b.app("exc", vec![l, self.kind_val("raise", e)]))
            }
            None => self.b.tru(),
        }
    }

    pub fn exit_div(&mut self, cx: &Cx, t: Term) -> Term {
        match cx.exits.last() {
            Some(Exit::Proc { o }) => self.b.eq(self.b.v(*o), self.b.app("diverge", vec![t])),
            Some(Exit::Local { r, .. }) => self.b.eq(self.b.v(*r), self.b.app("diverge", vec![t])),
            None => self.b.tru(),
        }
    }

    fn exit_brk(&mut self, cx: &Cx, span: Span) -> R<Term> {
        if !cx.exits.iter().any(|e| matches!(e, Exit::Local { is_loop: true, .. })) {
            return err(span, "`break` outside a loop");
        }
        match cx.exits.last() {
            Some(Exit::Local { r, muts, .. }) => {
                let l = self.local_state(cx, muts);
                Ok(self.b.eq(self.b.v(*r), self.b.app("exc", vec![l, self.kind_val("brk", self.b.empty())])))
            }
            _ => err(span, "`break` outside a loop"),
        }
    }

    /// After a compound statement with local outcome `r`: continue on normal
    /// outcomes (and `break` for loops), dispatch the others to the
    /// enclosing exit. Returns the normal value.
    pub fn finish_local(&mut self, cx: &mut Cx, r: VarId, body: Term, is_loop: bool) -> Term {
        let muts = cx.mut_indices();
        let rv = self.b.v(r);
        let l = self.b.app("out_state", vec![rv.clone()]);
        let val = self.b.app("out_value", vec![rv.clone()]);
        let kind = self.b.fst(val.clone());
        let payload = self.b.snd(val.clone());
        // a context seeing the state and variables carried by `r`
        let mut at = cx.clone();
        at.state = Some(self.b.fst(l.clone()));
        for (k, &i) in muts.iter().enumerate() {
            at.locals[i].term = self.b.proj(self.b.snd(l.clone()), k, muts.len());
        }
        let is_exc = self.b.eq(self.b.fst(rv.clone()), self.b.nat(1));
        let is = |s: &Self, k: &str| s.b.and(is_exc.clone(), s.b.eq(kind.clone(), s.b.str(k)));
        let mut abrupt = Vec::new();
        let ret = self.exit_ret(&at, payload.clone());
        abrupt.push(self.b.and(is(self, "ret"), ret));
        let st = at.state.clone().unwrap();
        let raise = self.exit_raise(&at, st, payload.clone());
        abrupt.push(self.b.and(is(self, "raise"), raise));
        if !is_loop {
            if let Ok(brk) = self.exit_brk(&at, Span::default()) {
                abrupt.push(self.b.and(is(self, "brk"), brk));
            }
        }
        let is_div = self.b.eq(self.b.fst(rv.clone()), self.b.nat(2));
        let div = self.exit_div(&at, self.b.snd(rv.clone()));
        abrupt.push(self.b.and(is_div, div));
        let mut normal = self.b.eq(self.b.fst(rv.clone()), self.b.nat(0));
        if is_loop {
            normal = self.b.or(normal, is(self, "brk"));
        }
        let abrupt = self.b.ors(abrupt);
        cx.frames.push(Frame::Local { r, body, normal, abrupt });
        cx.state = at.state.clone();
        for &i in &muts {
            cx.locals[i].term = at.locals[i].term.clone();
        }
        val
    }

    // ------------------------------------------------------------------
    //  Blocks

    /// The formula of a block; its normal end goes to the innermost exit.
    pub fn block_formula(&mut self, cx: &mut Cx, b: &Block, _span: Span) -> R<Term> {
        self.stmts_formula(cx, &b.stmts, Vec::new(), None)
    }

    /// Statements with extra frames before them and an optional statement
    /// to run after them (loop counters).
    fn stmts_formula(&mut self, cx: &mut Cx, stmts: &[Stmt], pre: Vec<Frame>, post: Option<(usize, Term)>) -> R<Term> {
        let n0 = cx.locals.len();
        let f0 = cx.frames.len();
        cx.frames.extend(pre);
        let mut terminal = false;
        for s in stmts {
            self.stmt(cx, s)?;
            if matches!(cx.frames.last(), Some(Frame::Terminal(_))) {
                terminal = true;
                break;
            }
        }
        let end = if terminal {
            self.b.tru()
        } else {
            if let Some((i, v)) = post {
                cx.locals[i].term = v;
            }
            self.exit_normal(cx, self.b.empty())
        };
        let frames = cx.frames.split_off(f0);
        cx.locals.truncate(n0);
        Ok(self.wrap_frames(frames, end))
    }

    /// Runs statements of a nested block in `cx` (scoped locals, same frames).
    fn scoped(&mut self, cx: &mut Cx, b: &Block) -> R<()> {
        let n0 = cx.locals.len();
        for s in &b.stmts {
            self.stmt(cx, s)?;
            if matches!(cx.frames.last(), Some(Frame::Terminal(_))) {
                break;
            }
        }
        // keep updated values of outer mutable variables
        cx.locals.truncate(n0);
        Ok(())
    }

    // ------------------------------------------------------------------
    //  Statements

    pub fn stmt(&mut self, cx: &mut Cx, s: &Stmt) -> R<()> {
        let span = s.span;
        match &s.kind {
            StmtKind::Let { pat, ty, value } => {
                let declared = match ty {
                    Some(t) => Some(self.ty(cx, t)?),
                    None => None,
                };
                let (t, vty) = match (&value.kind, pat) {
                    (ExprKind::Any { var: None, ty: aty, cond, maybe, els }, Pattern::Name(n)) => {
                        let at = self.ty(cx, aty)?;
                        if let Some(s) = els {
                            // `let x = any T where P else S` (S leaves):
                            //   [either { S } or {}]  if !(ex x. P) { S }  let x = any T where P
                            if !leaves(s) {
                                return err(s.span, "the `else` of `let x = any ...` must end with `return` or `raise`");
                            }
                            if *maybe {
                                self.branches(cx, vec![(self.b.tru(), Some((**s).clone())), (self.b.tru(), None)], span)?;
                            }
                            let (x, dom) = self.any_dom(cx, &n.name, &at, cond.as_deref(), span)?;
                            let exists = self.b.ex(&[x], dom);
                            let none = self.b.not(exists.clone());
                            self.branches(cx, vec![(none, Some((**s).clone())), (exists, None)], span)?;
                        }
                        self.any_value(cx, &n.name, at, cond.as_deref(), span)?
                    }
                    (ExprKind::Any { els: Some(_), .. }, _) => return err(span, "`any ... else` binds a single name"),
                    _ => self.expr(cx, value, declared.as_ref())?,
                };
                let vty = declared.unwrap_or(vty);
                let x = self.fresh(match pat {
                    Pattern::Name(n) => &n.name,
                    _ => "t",
                });
                cx.frames.push(Frame::Let { var: x, value: t });
                let (c, binds) = self.pattern(cx, pat, &self.b.v(x), &vty)?;
                if !self.b.is_true(&c) {
                    return err(span, "a `let` pattern must always match");
                }
                for (n, t, ty) in binds {
                    cx.push_local(&n, t, ty, false);
                }
                Ok(())
            }
            StmtKind::Var { name, ty, value } => {
                let declared = match ty {
                    Some(t) => Some(self.ty(cx, t)?),
                    None => None,
                };
                let (t, vty) = self.expr(cx, value, declared.as_ref())?;
                let x = self.fresh(&name.name);
                cx.frames.push(Frame::Let { var: x, value: t });
                cx.push_local(&name.name, self.b.v(x), declared.unwrap_or(vty), true);
                Ok(())
            }
            StmtKind::Assign { ghost, target, value } => {
                let (root, steps, leaf_ty) = self.lvalue(cx, target)?;
                let is_ghost = self.touches_ghost(cx, &root, &steps)?;
                if is_ghost != *ghost {
                    return err(span, if is_ghost {
                        "assignment to a ghost field needs `ghost`"
                    } else {
                        "`ghost` assignment to a non-ghost location"
                    });
                }
                let (v, vty) = self.expr(cx, value, Some(&leaf_ty))?;
                if !crate::expr::compatible(&leaf_ty, &vty) {
                    return err(value.span, format!("cannot assign {} to a location of type {}", vty.describe(), leaf_ty.describe()));
                }
                self.check_width(&leaf_ty, &vty, value.span);
                self.store(cx, root, steps, v, span)
            }
            StmtKind::Emit { target, event } => {
                let (root, steps, leaf_ty) = self.lvalue(cx, target)?;
                let ety = match leaf_ty.strip() {
                    Ty::Seq(t) | Ty::List(t) => (**t).clone(),
                    _ => Ty::Unknown,
                };
                let (ev, _) = self.expr(cx, event, Some(&ety))?;
                let cur = self.load(cx, &root, &steps)?;
                let one = self.b.app("seq_one", vec![ev]);
                let v = self.b.app("seq_concat", vec![cur, one]);
                self.store(cx, root, steps, v, span)
            }
            StmtKind::If { cond, then, els } => {
                let (c, _) = self.expr(cx, cond, Some(&Ty::Bool))?;
                let mut branches = vec![(c.clone(), Some(then.clone()))];
                branches.push((self.b.not(c), els.clone()));
                self.branches(cx, branches, span)
            }
            StmtKind::Match { scrut, arms } => {
                let (st, sty) = self.expr(cx, scrut, None)?;
                let mut prev: Vec<Term> = Vec::new();
                let mut branches = Vec::new();
                let mut binds_per = Vec::new();
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
                    prev.push(cond);
                    branches.push((guard, Some(arm.body.clone())));
                    binds_per.push(binds);
                }
                // no matching arm: undefined
                let any = self.b.ors(prev);
                cx.frames.push(Frame::Require(any));
                self.branches_with(cx, branches, binds_per, span)
            }
            StmtKind::Either(blocks) => {
                let branches = blocks.iter().map(|b| (self.b.tru(), Some(b.clone()))).collect();
                self.branches(cx, branches, span)
            }
            StmtKind::While { cond, body } => self.loop_stmt(cx, Some(cond), None, body, span),
            StmtKind::Loop(body) => self.loop_stmt(cx, None, None, body, span),
            StmtKind::For { var, iter, body } => self.for_stmt(cx, var, iter, body, span),
            StmtKind::Break => {
                let f = self.exit_brk(cx, span)?;
                cx.frames.push(Frame::Terminal(f));
                Ok(())
            }
            StmtKind::Return(v) => {
                let (t, _) = match v {
                    Some(e) => self.expr(cx, e, None)?,
                    None => (self.b.empty(), Ty::Unit),
                };
                let f = self.exit_ret(cx, t);
                cx.frames.push(Frame::Terminal(f));
                Ok(())
            }
            StmtKind::Raise(e) => {
                let (t, _) = self.expr(cx, e, Some(&Ty::Exc))?;
                let s = cx.state.clone().unwrap_or_else(|| self.b.empty());
                let f = self.exit_raise(cx, s, t);
                cx.frames.push(Frame::Terminal(f));
                Ok(())
            }
            StmtKind::Try { body, catches } => self.try_stmt(cx, body, catches, span),
            StmtKind::Havoc { targets, cond, maybe, els: None } => {
                let _ = maybe;
                self.havoc(cx, targets, cond.as_ref(), span)
            }
            // `havoc? v where P else S` = either { S } or { havoc v where P else S }
            StmtKind::Havoc { targets, cond, maybe: true, els: Some(s) } => {
                let inner = Stmt { kind: StmtKind::Havoc { targets: targets.clone(), cond: cond.clone(), maybe: false, els: Some(s.clone()) }, span };
                let blk = Block { stmts: vec![inner], span };
                self.branches(cx, vec![(self.b.tru(), Some(s.clone())), (self.b.tru(), Some(blk))], span)
            }
            // `havoc v where P else S` = if (ex v. P) { havoc v where P } else { S }
            StmtKind::Havoc { targets, cond, maybe: false, els: Some(s) } => {
                let (x, dom, _) = self.havoc_parts(cx, targets, cond.as_ref(), span)?;
                let exists = self.b.ex(&[x], dom);
                let none = self.b.not(exists.clone());
                let plain = Stmt { kind: StmtKind::Havoc { targets: targets.clone(), cond: cond.clone(), maybe: false, els: None }, span };
                let blk = Block { stmts: vec![plain], span };
                self.branches(cx, vec![(exists, Some(blk)), (none, Some(s.clone()))], span)
            }
            StmtKind::Require(e) => {
                let (c, _) = self.expr(cx, e, Some(&Ty::Bool))?;
                cx.frames.push(Frame::Require(c));
                Ok(())
            }
            StmtKind::Guard(e) => {
                let (c, _) = self.expr(cx, e, Some(&Ty::Bool))?;
                let nomatch = self.b.app("exc_val", vec![self.b.str("nomatch"), self.b.empty()]);
                let s = cx.state.clone().unwrap();
                let fail = self.exit_raise(cx, s, nomatch);
                cx.frames.push(Frame::Guard { cond: c, fail });
                Ok(())
            }
            StmtKind::Undefined => {
                cx.frames.push(Frame::Terminal(self.b.tru()));
                Ok(())
            }
            StmtKind::Expr(e) => {
                self.expr(cx, e, None)?;
                Ok(())
            }
            StmtKind::Block(b) => self.scoped(cx, b),
        }
    }

    fn branches(&mut self, cx: &mut Cx, branches: Vec<(Term, Option<Block>)>, span: Span) -> R<()> {
        let n = branches.len();
        self.branches_with(cx, branches, vec![Vec::new(); n], span)
    }

    /// `ex r. OR_i (cond_i && block_i) && continue`
    fn branches_with(&mut self, cx: &mut Cx, branches: Vec<(Term, Option<Block>)>, binds: Vec<Vec<(String, Term, Ty)>>, _span: Span) -> R<()> {
        if cx.pure {
            // statements in pure functions still execute over the unit state
        }
        let r = self.fresh("r");
        let muts = cx.mut_indices();
        let mut alts = Vec::new();
        for ((c, blk), bs) in branches.into_iter().zip(binds) {
            let mut bcx = cx.clone();
            bcx.frames.clear();
            bcx.exits.push(Exit::Local { r, muts: muts.clone(), is_loop: false });
            for (n, t, ty) in bs {
                bcx.push_local(&n, t, ty, false);
            }
            let f = match blk {
                Some(b) => self.stmts_formula(&mut bcx, &b.stmts, Vec::new(), None)?,
                None => self.exit_normal(&bcx, self.b.empty()),
            };
            alts.push(self.b.and(c, f));
        }
        let body = self.b.ors(alts);
        self.finish_local(cx, r, body, false);
        Ok(())
    }

    // ------------------------------------------------------------------
    //  Loops

    /// `while cond { body }` (or `loop`) with an optional counter
    /// `(counter local index, bound, loop variable name, value)`.
    fn loop_stmt(&mut self, cx: &mut Cx, cond: Option<&Expr>, counter: Option<(usize, Term, String, Box<dyn Fn(&B2, Term) -> Term>)>, body: &Block, span: Span) -> R<()> {
        if cx.pure && cx.state.is_none() {
            cx.state = Some(self.b.empty());
        }
        let st_ty = cx.state_ty.clone().unwrap_or(Ty::Unit);
        let muts = cx.mut_indices();
        let l0 = self.local_state(cx, &muts);
        let l = self.fresh("l");
        let lo = self.fresh("lo");
        let mut bcx = cx.clone();
        bcx.frames.clear();
        bcx.state = Some(self.b.fst(self.b.v(l)));
        for (k, &i) in muts.iter().enumerate() {
            bcx.locals[i].term = self.b.proj(self.b.snd(self.b.v(l)), k, muts.len());
        }
        bcx.exits.push(Exit::Local { r: lo, muts: muts.clone(), is_loop: true });
        let mut pre = Vec::new();
        let mut post = None;
        let n0 = bcx.locals.len();
        if let Some(c) = cond {
            let (ct, _) = self.expr(&mut bcx, c, Some(&Ty::Bool))?;
            let brk = self.exit_brk(&bcx, span)?;
            pre.append(&mut bcx.frames);
            pre.push(Frame::Guard { cond: ct, fail: brk });
        }
        if let Some((ci, bound, name, mk)) = counter {
            let cur = bcx.locals[ci].term.clone();
            let lt = self.b.app("int_lt", vec![cur.clone(), bound]);
            let brk = self.exit_brk(&bcx, span)?;
            pre.push(Frame::Guard { cond: lt, fail: brk });
            let item = mk(&B2(&self.b), cur.clone());
            let x = self.fresh(&name);
            pre.push(Frame::Let { var: x, value: item });
            let ity = Ty::Unknown;
            bcx.push_local(&name, self.b.v(x), ity, false);
            post = Some((ci, self.b.app("int_add", vec![cur, self.b.nat(1)])));
        }
        let _ = n0;
        let bf = self.stmts_formula(&mut bcx, &body.stmts, pre, post)?;
        let r = self.fresh("r");
        let lt = self.fresh("l");
        let s_of_l = self.b.fst(self.b.v(lt));
        let tr = self.traces_of(&st_ty, &s_of_l)?;
        let wr = self.b.bind_args(
            "while_rel",
            vec![(vec![], l0), (vec![l], self.b.tru()), (vec![l, lo], bf), (vec![lt], tr), (vec![], self.b.v(r))],
        );
        self.finish_local(cx, r, wr, true);
        Ok(())
    }

    fn for_stmt(&mut self, cx: &mut Cx, var: &Ident, iter: &Expr, body: &Block, span: Span) -> R<()> {
        if cx.pure && cx.state.is_none() {
            cx.state = Some(self.b.empty());
        }
        let (start, bound, elem_of): (Term, Term, Box<dyn Fn(&B2, Term) -> Term>) = match &iter.kind {
            ExprKind::Binary(BinOp::Range, lo, hi) => {
                let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
                let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
                (l, h, Box::new(|_b: &B2, i: Term| i))
            }
            _ => {
                let (s, sty) = self.expr(cx, iter, None)?;
                let list = match sty.strip() {
                    Ty::List(_) | Ty::Seq(_) => s,
                    Ty::Set(_) => {
                        // some enumeration of the set (order unspecified)
                        let lv = self.fresh("l");
                        let dom = self.b.app("set_enum", vec![self.b.v(lv), s]);
                        cx.frames.push(Frame::Choose { var: lv, dom });
                        self.b.v(lv)
                    }
                    _ => return err(span, format!("cannot iterate over {}", sty.describe())),
                };
                let len = self.b.app("seq_len", vec![list.clone()]);
                (self.b.nat(0), len, Box::new(move |b: &B2, i: Term| b.0.app_fn(list.clone(), i)))
            }
        };
        // the counter is a mutable local
        let c = self.fresh("i");
        cx.frames.push(Frame::Let { var: c, value: start });
        cx.push_local("$counter", self.b.v(c), Ty::Nat, true);
        let ci = cx.locals.len() - 1;
        let r = self.loop_stmt(cx, None, Some((ci, bound, var.name.clone(), elem_of)), body, span);
        cx.locals.truncate(ci);
        r
    }

    // ------------------------------------------------------------------
    //  try / catch

    fn try_stmt(&mut self, cx: &mut Cx, body: &Block, catches: &[(Pattern, Block)], span: Span) -> R<()> {
        let muts = cx.mut_indices();
        let rt = self.fresh("rt");
        let r = self.fresh("r");
        let mut bcx = cx.clone();
        bcx.frames.clear();
        bcx.exits.push(Exit::Local { r: rt, muts: muts.clone(), is_loop: false });
        let bf = self.stmts_formula(&mut bcx, &body.stmts, Vec::new(), None)?;
        // dispatch rt into r: normal and non-raise outcomes pass through
        let rtv = self.b.v(rt);
        let val = self.b.app("out_value", vec![rtv.clone()]);
        let is_raise = self.b.and(self.b.eq(self.b.fst(rtv.clone()), self.b.nat(1)), self.b.eq(self.b.fst(val.clone()), self.b.str("raise")));
        let e = self.b.snd(val);
        let l = self.b.app("out_state", vec![rtv.clone()]);
        let mut hcx = cx.clone();
        hcx.frames.clear();
        hcx.state = Some(self.b.fst(l.clone()));
        for (k, &i) in muts.iter().enumerate() {
            hcx.locals[i].term = self.b.proj(self.b.snd(l.clone()), k, muts.len());
        }
        hcx.exits.push(Exit::Local { r, muts: muts.clone(), is_loop: false });
        let mut alts = vec![self.b.and(self.b.not(is_raise.clone()), self.b.eq(self.b.v(r), rtv.clone()))];
        let mut prev: Vec<Term> = Vec::new();
        for (p, blk) in catches {
            let (c, binds) = self.pattern(&mut hcx.clone(), p, &e, &Ty::Exc)?;
            let mut guard = self.b.and(is_raise.clone(), c.clone());
            for q in &prev {
                guard = self.b.and(self.b.not(q.clone()), guard);
            }
            prev.push(c);
            let mut h = hcx.clone();
            for (n, t, ty) in binds {
                h.push_local(&n, t, ty, false);
            }
            let hf = self.stmts_formula(&mut h, &blk.stmts, Vec::new(), None)?;
            alts.push(self.b.and(guard, hf));
        }
        // not caught: re-raise
        let uncaught = prev.iter().fold(is_raise, |acc, q| self.b.and(acc, self.b.not(q.clone())));
        alts.push(self.b.and(uncaught, self.b.eq(self.b.v(r), rtv)));
        let dispatch = self.b.ors(alts);
        let inner = self.b.and(bf, dispatch);
        let body = self.b.ex(&[rt], inner);
        let _ = span;
        self.finish_local(cx, r, body, false);
        Ok(())
    }

    // ------------------------------------------------------------------
    //  Locations: loads and stores

    fn lvalue(&mut self, cx: &mut Cx, e: &Expr) -> R<(Root, Vec<Step>, Ty)> {
        match &e.kind {
            ExprKind::Name(n) => {
                if let Some(i) = cx.locals.iter().rposition(|l| l.name == n.name) {
                    if !cx.locals[i].mutable {
                        return err(n.span, format!("`{}` is not mutable (use `var`)", n.name));
                    }
                    return Ok((Root::Local(i), vec![], cx.locals[i].ty.clone()));
                }
                let st = match cx.state_ty.clone() {
                    Some(t) => t,
                    None => return err(n.span, format!("cannot assign to `{}`", n.name)),
                };
                let fs = self.fields_of(&st)?.unwrap_or_default();
                match fs.iter().find(|f| f.0 == n.name) {
                    Some((_, t, _)) => Ok((Root::State, vec![Step::Field(n.name.clone())], t.clone())),
                    None => err(n.span, format!("`{}` is not a variable or state field", n.name)),
                }
            }
            ExprKind::SelfState => match cx.state_ty.clone() {
                Some(t) => Ok((Root::State, vec![], t)),
                None => err(e.span, "`self` outside a procedure"),
            },
            ExprKind::Field(a, f) => {
                let (root, mut steps, ty) = self.lvalue(cx, a)?;
                let fs = self.fields_of(&ty)?.unwrap_or_default();
                match fs.iter().find(|x| x.0 == f.name) {
                    Some((_, t, _)) => {
                        steps.push(Step::Field(f.name.clone()));
                        Ok((root, steps, t.clone()))
                    }
                    None => err(f.span, format!("no field `{}` in {}", f.name, ty.describe())),
                }
            }
            ExprKind::Index(a, idx) if idx.len() == 1 => {
                let (root, mut steps, ty) = self.lvalue(cx, a)?;
                match ty.strip() {
                    Ty::Map(k, v) => {
                        let (kt, _) = self.expr(cx, &idx[0], Some(k))?;
                        steps.push(Step::Index(kt, ty.clone()));
                        Ok((root, steps, (**v).clone()))
                    }
                    Ty::Bits(_) => {
                        let (it, _) = self.expr(cx, &idx[0], Some(&Ty::Nat))?;
                        steps.push(Step::Index(it, ty.clone()));
                        Ok((root, steps, Ty::Bool))
                    }
                    _ => err(e.span, format!("cannot assign to an index of {}", ty.describe())),
                }
            }
            ExprKind::Slice(a, hi, lo) => {
                let (root, mut steps, ty) = self.lvalue(cx, a)?;
                let (h, _) = self.expr(cx, hi, Some(&Ty::Nat))?;
                let (l, _) = self.expr(cx, lo, Some(&Ty::Nat))?;
                let w = self.slice_width(&h, &l);
                let full = self.width(&ty);
                steps.push(Step::Slice(h, l, full));
                Ok((root, steps, Ty::Bits(w)))
            }
            ExprKind::Call(f, args) => {
                if let ExprKind::Name(n) = &f.kind {
                    if let Some(i) = self.g.find_decl(&cx.module, &n.name) {
                        if matches!(self.g.decls[i].decl.kind, DeclKind::View { .. }) {
                            self.ensure(i)?;
                            let sig = self.sig_of(i, "get")?;
                            // the value type depends on the arguments (`bits[w]`)
                            let mut probe = cx.clone();
                            let (vals, tys, _) = self.bind_args(&mut probe, &sig, &[], args, e.span)?;
                            let t = self.subst_ty(&sig.ret, &vals, &tys);
                            return Ok((Root::View(i, args.clone()), vec![], t));
                        }
                    }
                }
                err(e.span, "only views can be assigned through a call")
            }
            _ => err(e.span, "not an assignable location"),
        }
    }

    /// Whether a location is (inside) a ghost state field.
    fn touches_ghost(&mut self, cx: &Cx, root: &Root, steps: &[Step]) -> R<bool> {
        if !matches!(root, Root::State) {
            return Ok(false);
        }
        let (Some(Step::Field(f)), Some(crate::ty::Ty::State(st))) = (steps.first(), cx.state_ty.clone()) else {
            return Ok(false);
        };
        for q in st.ext.iter().filter_map(|e| if let crate::ty::Ext::Fields(q) = e { Some(q.clone()) } else { None }) {
            let i = self.g.decls.iter().position(|d| d.qual == q).unwrap();
            if let DeclKind::State { fields, .. } = &self.g.decls[i].decl.kind {
                if fields.iter().any(|x| x.ghost && x.name.name == *f) {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn root_value(&self, cx: &Cx, root: &Root) -> Term {
        match root {
            Root::Local(i) => cx.locals[*i].term.clone(),
            _ => cx.state.clone().unwrap(),
        }
    }

    fn load(&mut self, cx: &mut Cx, root: &Root, steps: &[Step]) -> R<Term> {
        if let Root::View(i, args) = root {
            let n = self.g.decls[*i].decl.name().unwrap().clone();
            let call = Expr { kind: ExprKind::Call(Box::new(Expr { kind: ExprKind::Name(n.clone()), span: n.span }), args.clone()), span: n.span };
            return Ok(self.expr(cx, &call, None)?.0);
        }
        let mut v = self.root_value(cx, root);
        for s in steps {
            v = match s {
                Step::Field(f) => self.b.field(v, f),
                Step::Index(k, ty) => match ty.strip() {
                    Ty::Bits(_) => self.b.app("bit", vec![v, k.clone()]),
                    _ => self.b.app_fn(v, k.clone()),
                },
                Step::Slice(h, l, _) => self.b.app("bits_slice", vec![v, h.clone(), l.clone()]),
            };
        }
        Ok(v)
    }

    /// The updated root after writing `v` at `steps` of `cur`.
    fn update(&self, cur: Term, steps: &[Step], v: Term) -> Term {
        match steps.split_first() {
            None => v,
            Some((Step::Field(f), rest)) => {
                let inner = self.update(self.b.field(cur.clone(), f), rest, v);
                self.b.fn_update(cur, self.b.str(f), inner)
            }
            Some((Step::Index(k, ty), rest)) => match ty.strip() {
                Ty::Bits(w) => self.b.app("bits_set_bit", vec![w.clone(), cur, k.clone(), v]),
                _ => {
                    let inner = self.update(self.b.app_fn(cur.clone(), k.clone()), rest, v);
                    self.b.fn_update(cur, k.clone(), inner)
                }
            },
            Some((Step::Slice(h, l, w), _)) => self.b.app("bits_set_slice", vec![w.clone(), cur, h.clone(), l.clone(), v]),
        }
    }

    fn store(&mut self, cx: &mut Cx, root: Root, steps: Vec<Step>, v: Term, span: Span) -> R<()> {
        match root {
            Root::View(i, args) => {
                let sig = self.sig_of(i, "set")?;
                let gsig = self.sig_of(i, "get")?;
                let mut probe = cx.clone();
                let (_, _, argts) = self.bind_args(&mut probe, &gsig, &[], &args, span)?;
                cx.frames.extend(probe.frames.drain(cx.frames.len()..));
                cx.state = probe.state.clone();
                let mut cargs = self.lift_args(cx, &sig, span)?;
                cargs.extend(argts);
                cargs.push(v);
                let prog = self.b.app(&sig.core, cargs);
                let st = match &sig.kind {
                    SigKind::Proc(s) => s.clone(),
                    _ => unreachable!(),
                };
                let _ = st;
                self.run_prog(cx, prog, Ty::Unit, span)?;
                Ok(())
            }
            Root::Local(i) => {
                let cur = cx.locals[i].term.clone();
                let nv = self.update(cur, &steps, v);
                let x = self.fresh(&cx.locals[i].name.clone());
                cx.frames.push(Frame::Let { var: x, value: nv });
                cx.locals[i].term = self.b.v(x);
                Ok(())
            }
            Root::State => {
                let cur = cx.state.clone().unwrap();
                let nv = self.update(cur, &steps, v);
                let x = self.fresh("s");
                cx.frames.push(Frame::Let { var: x, value: nv });
                cx.state = Some(self.b.v(x));
                Ok(())
            }
        }
    }

    // ------------------------------------------------------------------
    //  havoc

    fn havoc(&mut self, cx: &mut Cx, targets: &[Expr], cond: Option<&Expr>, span: Span) -> R<()> {
        let (x, dom, work) = self.havoc_parts(cx, targets, cond, span)?;
        cx.frames.push(Frame::Choose { var: x, dom });
        // name the new state / locals
        if let Some(s) = work.state.clone() {
            if Some(&s) != cx.state.as_ref() {
                let sv = self.fresh("s");
                cx.frames.push(Frame::Let { var: sv, value: s });
                cx.state = Some(self.b.v(sv));
            }
        }
        for i in 0..cx.locals.len() {
            if work.locals[i].term != cx.locals[i].term {
                let lv = self.fresh(&cx.locals[i].name.clone());
                cx.frames.push(Frame::Let { var: lv, value: work.locals[i].term.clone() });
                cx.locals[i].term = self.b.v(lv);
            }
        }
        Ok(())
    }

    /// The choice a `havoc` makes: its variable (a tuple of the new values),
    /// the formula it must satisfy, and the context with the targets set to
    /// the new values.
    fn havoc_parts(&mut self, cx: &mut Cx, targets: &[Expr], cond: Option<&Expr>, span: Span) -> R<(VarId, Term, Cx)> {
        // expand `x.{a, b}`
        let mut locs: Vec<Expr> = Vec::new();
        for t in targets {
            match &t.kind {
                ExprKind::FieldSet(base, fs) => {
                    for f in fs {
                        locs.push(Expr { kind: ExprKind::Field(base.clone(), f.clone()), span: t.span });
                    }
                }
                _ => locs.push(t.clone()),
            }
        }
        let x = self.fresh("h");
        let n = locs.len();
        let mut work = cx.clone();
        work.frames.clear();
        let mut doms = Vec::new();
        for (k, l) in locs.iter().enumerate() {
            let (root, steps, ty) = self.lvalue(&mut work, l)?;
            if matches!(root, Root::View(..)) {
                return err(l.span, "`havoc` of a view");
            }
            let set = self.ty_set(&ty, span)?;
            let val = self.b.proj(self.b.v(x), k, n);
            doms.push(self.b.member(val.clone(), set));
            // traces may only be extended
            let old = self.load(&mut work, &root, &steps)?;
            for (p, _) in self.trace_paths(&ty)? {
                let mut o = old.clone();
                let mut nv = val.clone();
                for f in &p {
                    o = self.b.field(o, f);
                    nv = self.b.field(nv, f);
                }
                doms.push(self.b.app("subset", vec![o, nv]));
            }
            let cur = self.root_value(&work, &root);
            let upd = self.update(cur, &steps, val);
            match root {
                Root::Local(i) => work.locals[i].term = upd,
                Root::State => work.state = Some(upd),
                Root::View(..) => unreachable!(),
            }
        }
        if !work.frames.is_empty() {
            return err(span, "`havoc` targets may not execute programs");
        }
        if let Some(c) = cond {
            let (ct, _) = self.pure_expr(&mut work, c, Some(&Ty::Bool))?;
            doms.push(ct);
        }
        let _ = cx;
        Ok((x, self.b.ands(doms), work))
    }
}

/// The block ends by leaving (`return` or `raise`).
fn leaves(b: &Block) -> bool {
    matches!(b.stmts.last().map(|s| &s.kind), Some(StmtKind::Return(_) | StmtKind::Raise(_)))
}

/// A read-only view of the builder for closures.
pub struct B2<'a>(pub &'a crate::build::B);
