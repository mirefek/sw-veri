//! Construction of kernel terms with named placeholders.
//!
//! Local variables are represented by fresh schematic variables (arity 0)
//! while a term is built; `bind` turns them into bound variables of a binder
//! constant (de Bruijn abstraction).

use sl_kernel::{Env, Nat, Node, SymId, Term, VarId};

pub struct B {
    pub env: Env,
}

impl B {
    pub fn sym(&self, name: &str) -> SymId {
        match self.env.sym_by_name.get(name) {
            Some(s) => *s,
            None => panic!("prelude symbol `{}` missing", name),
        }
    }

    pub fn has(&self, name: &str) -> bool {
        self.env.sym_by_name.contains_key(name)
    }

    pub fn app(&self, name: &str, args: Vec<Term>) -> Term {
        let s = self.sym(name);
        debug_assert!(
            self.env.syms[s as usize].binders.iter().all(|&b| b == 0),
            "`{}` binds variables; use bind_app",
            name
        );
        assert_eq!(self.env.syms[s as usize].binders.len(), args.len(), "arity of `{}`", name);
        Term::app(s, args)
    }

    pub fn c(&self, name: &str) -> Term {
        self.app(name, vec![])
    }

    pub fn nat(&self, n: u64) -> Term {
        Term::nat(Nat::from_u64(n))
    }

    pub fn natn(&self, n: Nat) -> Term {
        Term::nat(n)
    }

    pub fn str(&self, s: &str) -> Term {
        Term::bytes(s.as_bytes())
    }

    pub fn fresh(&mut self, hint: &str) -> VarId {
        let id = self.env.vars.len();
        let clean: String = hint.chars().filter(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
        let clean = if clean.is_empty() || !clean.chars().next().unwrap().is_ascii_alphabetic() {
            format!("v{}", clean)
        } else {
            clean
        };
        self.env.new_var(&format!("{}${}", clean, id), 0)
    }

    pub fn v(&self, id: VarId) -> Term {
        Term::var(id, vec![])
    }

    /// Replaces placeholders `vars` by bound variables (last = innermost).
    pub fn abstract_vars(&self, vars: &[VarId], body: &Term) -> Term {
        self.abs_at(vars, body, 0)
    }

    fn abs_at(&self, vars: &[VarId], t: &Term, depth: u32) -> Term {
        let k = vars.len() as u32;
        match t.node() {
            Node::Var(v, args) if args.is_empty() => match vars.iter().position(|x| x == v) {
                Some(j) => Term::bvar(depth + (k - 1 - j as u32)),
                None => t.clone(),
            },
            Node::Var(v, args) => Self::kept(t, Term::var(*v, args.iter().map(|a| self.abs_at(vars, a, depth)).collect())),
            Node::App(s, args) => {
                if !self.mentions(t, vars) {
                    return t.clone();
                }
                let bs = &self.env.syms[*s as usize].binders;
                Self::kept(t, Term::app(*s, args.iter().enumerate().map(|(i, a)| self.abs_at(vars, a, depth + bs[i])).collect()))
            }
            _ => t.clone(),
        }
    }

    /// `new`, a rebuilt `old`: its label and binder name kept (a conjunct's
    /// label under a quantifier)
    fn kept(old: &Term, new: Term) -> Term {
        new.with_label(old.label().map(Into::into)).with_binder_name(old.binder_name().map(Into::into))
    }

    fn mentions(&self, t: &Term, vars: &[VarId]) -> bool {
        match t.node() {
            Node::Var(v, args) => vars.contains(v) || args.iter().any(|a| self.mentions(a, vars)),
            Node::App(_, args) => args.iter().any(|a| self.mentions(a, vars)),
            _ => false,
        }
    }

    /// Applies a binder constant: `name(plain..., vars. body)` where the
    /// binding argument is the last one.
    pub fn bind_app(&self, name: &str, plain: Vec<Term>, vars: &[VarId], body: &Term) -> Term {
        let s = self.sym(name);
        let bs = &self.env.syms[s as usize].binders;
        assert_eq!(bs.len(), plain.len() + 1, "arity of `{}`", name);
        assert_eq!(*bs.last().unwrap() as usize, vars.len(), "binders of `{}`", name);
        let mut args = plain;
        args.push(self.abstract_vars(vars, body));
        Term::app(s, args)
    }

    /// General form: each argument with its own bound placeholders.
    pub fn bind_args(&self, name: &str, args: Vec<(Vec<VarId>, Term)>) -> Term {
        let s = self.sym(name);
        let bs = self.env.syms[s as usize].binders.clone();
        assert_eq!(bs.len(), args.len(), "arity of `{}`", name);
        Term::app(
            s,
            args.iter()
                .enumerate()
                .map(|(i, (vs, t))| {
                    assert_eq!(vs.len() as u32, bs[i], "binders of `{}` arg {}", name, i);
                    self.abstract_vars(vs, t)
                })
                .collect(),
        )
    }

    // ------------------------------------------------------------------
    //  Logic

    pub fn tru(&self) -> Term {
        self.c("true")
    }
    pub fn fls(&self) -> Term {
        self.c("false")
    }
    pub fn eq(&self, a: Term, b: Term) -> Term {
        self.env.mk_eq(a, b)
    }
    pub fn imp(&self, a: Term, b: Term) -> Term {
        self.env.mk_imp(a, b)
    }
    pub fn not(&self, a: Term) -> Term {
        self.app("not", vec![a])
    }
    pub fn and(&self, a: Term, b: Term) -> Term {
        if self.is_true(&a) {
            return b;
        }
        if self.is_true(&b) {
            return a;
        }
        self.app("and", vec![a, b])
    }
    pub fn or(&self, a: Term, b: Term) -> Term {
        self.app("or", vec![a, b])
    }
    pub fn ands(&self, ts: Vec<Term>) -> Term {
        ts.into_iter().fold(self.tru(), |a, b| self.and(a, b))
    }
    pub fn ors(&self, ts: Vec<Term>) -> Term {
        let mut it = ts.into_iter();
        match it.next() {
            None => self.fls(),
            Some(first) => it.fold(first, |a, b| self.or(a, b)),
        }
    }
    pub fn is_true(&self, t: &Term) -> bool {
        matches!(t.node(), Node::App(s, a) if a.is_empty() && self.env.syms[*s as usize].name == "true")
    }
    pub fn ex(&mut self, vars: &[VarId], body: Term) -> Term {
        let mut t = body;
        for v in vars.iter().rev() {
            t = self.bind_app("ex", vec![], &[*v], &t);
        }
        t
    }
    pub fn all(&mut self, vars: &[VarId], body: Term) -> Term {
        let mut t = body;
        for v in vars.iter().rev() {
            t = self.bind_app("all", vec![], &[*v], &t);
        }
        t
    }
    pub fn ite(&self, c: Term, a: Term, b: Term) -> Term {
        self.app("ite", vec![c, a, b])
    }
    pub fn letin(&self, value: Term, x: VarId, body: &Term) -> Term {
        self.bind_app("letin", vec![value], &[x], body)
    }
    pub fn member(&self, a: Term, s: Term) -> Term {
        self.app("in", vec![a, s])
    }

    // ------------------------------------------------------------------
    //  Data

    pub fn pair(&self, a: Term, b: Term) -> Term {
        self.app("pair", vec![a, b])
    }
    pub fn fst(&self, a: Term) -> Term {
        self.app("fst", vec![a])
    }
    pub fn snd(&self, a: Term) -> Term {
        self.app("snd", vec![a])
    }
    pub fn empty(&self) -> Term {
        self.c("empty")
    }
    /// n-tuples: () = empty, (a) = a, (a, b, c) = pair(a, pair(b, c))
    pub fn tuple(&self, mut ts: Vec<Term>) -> Term {
        match ts.len() {
            0 => self.empty(),
            1 => ts.pop().unwrap(),
            _ => {
                let last = ts.pop().unwrap();
                ts.into_iter().rev().fold(last, |acc, t| self.pair(t, acc))
            }
        }
    }
    pub fn proj(&self, t: Term, i: usize, n: usize) -> Term {
        if n == 1 {
            return t;
        }
        let mut cur = t;
        for _ in 0..i {
            cur = self.snd(cur);
        }
        if i + 1 == n {
            cur
        } else {
            self.fst(cur)
        }
    }
    pub fn tag(&self, k: u64, v: Term) -> Term {
        self.app("tag", vec![self.nat(k), v])
    }
    pub fn app_fn(&self, f: Term, x: Term) -> Term {
        self.app("app", vec![f, x])
    }
    pub fn field(&self, r: Term, f: &str) -> Term {
        let s = self.str(f);
        self.app_fn(r, s)
    }
    pub fn fn_update(&self, f: Term, k: Term, v: Term) -> Term {
        self.app("fn_update", vec![f, k, v])
    }
    pub fn set_of(&self, items: Vec<Term>) -> Term {
        items.into_iter().rev().fold(self.empty(), |acc, x| self.app("insert", vec![x, acc]))
    }
    pub fn record(&self, fields: Vec<(String, Term)>) -> Term {
        fields.into_iter().fold(self.empty(), |acc, (f, v)| {
            let k = self.str(&f);
            self.fn_update(acc, k, v)
        })
    }

    /// Normal form of a width: literal arithmetic is folded, and linear
    /// combinations (`int_add`, `succ`, multiplication by a literal, and
    /// `int_sub` when the result is visibly non-negative) are brought to a
    /// canonical sum.
    pub fn norm(&self, t: &Term) -> Term {
        let t = self.fold(t);
        match self.linear(&t) {
            Some(p) => self.from_linear(p),
            None => t,
        }
    }

    /// `t` as constant + sum of coefficient * atom.
    fn linear(&self, t: &Term) -> Option<(Nat, Vec<(Term, Nat)>)> {
        let one = Nat::from_u64(1);
        match t.node() {
            Node::Nat(n) => Some((n.clone(), vec![])),
            Node::App(s, a) => {
                let name = self.env.syms[*s as usize].name.as_str();
                match (name, a.len()) {
                    ("succ", 1) => {
                        let (c, xs) = self.linear(&a[0])?;
                        Some((c.add(&one), xs))
                    }
                    ("int_add", 2) => {
                        let (c1, x1) = self.linear(&a[0])?;
                        let (c2, x2) = self.linear(&a[1])?;
                        Some((c1.add(&c2), merge(x1, x2)))
                    }
                    ("int_mul", 2) => {
                        let (k, x) = match (a[0].node(), a[1].node()) {
                            (Node::Nat(k), _) => (k.clone(), &a[1]),
                            (_, Node::Nat(k)) => (k.clone(), &a[0]),
                            _ => return Some((Nat::zero(), vec![(t.clone(), one)])),
                        };
                        let (c, xs) = self.linear(x)?;
                        Some((c.mul(&k), xs.into_iter().map(|(v, m)| (v, m.mul(&k))).filter(|(_, m)| !m.is_zero()).collect()))
                    }
                    ("int_sub", 2) => {
                        let (c1, x1) = self.linear(&a[0])?;
                        let (c2, x2) = self.linear(&a[1])?;
                        // only when every part of the subtrahend is present
                        let c = c1.sub(&c2);
                        let mut out = x1.clone();
                        for (v, m) in x2 {
                            let i = out.iter().position(|(w, _)| *w == v);
                            match i.and_then(|i| out[i].1.sub(&m).map(|d| (i, d))) {
                                Some((i, d)) => out[i].1 = d,
                                None => return Some((Nat::zero(), vec![(t.clone(), one)])),
                            }
                        }
                        match c {
                            Some(c) => Some((c, out.into_iter().filter(|(_, m)| !m.is_zero()).collect())),
                            None => Some((Nat::zero(), vec![(t.clone(), one)])),
                        }
                    }
                    _ => Some((Nat::zero(), vec![(t.clone(), one)])),
                }
            }
            _ => Some((Nat::zero(), vec![(t.clone(), one)])),
        }
    }

    fn from_linear(&self, (c, xs): (Nat, Vec<(Term, Nat)>)) -> Term {
        let mut parts: Vec<Term> = Vec::new();
        for (v, m) in xs {
            parts.push(if m.to_u64() == Some(1) { v } else { self.app("int_mul", vec![Term::nat(m), v]) });
        }
        if !c.is_zero() || parts.is_empty() {
            parts.push(Term::nat(c));
        }
        let mut it = parts.into_iter();
        let first = it.next().unwrap();
        it.fold(first, |acc, p| self.app("int_add", vec![acc, p]))
    }

    /// Folds literal arithmetic.
    fn fold(&self, t: &Term) -> Term {
        match t.node() {
            Node::App(s, args) if !args.is_empty() => {
                let name = self.env.syms[*s as usize].name.clone();
                let args: Vec<Term> = args.iter().map(|a| self.fold(a)).collect();
                if name == "succ" {
                    if let Node::Nat(n) = args[0].node() {
                        return Term::nat(n.add(&Nat::from_u64(1)));
                    }
                }
                if let (2, Some(Node::Nat(a)), Some(Node::Nat(b))) =
                    (args.len(), args.first().map(|x| x.node()), args.get(1).map(|x| x.node()))
                {
                    let r = match name.as_str() {
                        "int_add" => Some(a.add(b)),
                        "int_mul" => Some(a.mul(b)),
                        // (a negative difference stays unfolded)
                        "int_sub" => a.sub(b),
                        "int_div" => a.divmod(b).map(|x| x.0),
                        "int_mod" => a.divmod(b).map(|x| x.1),
                        "int_pow" =>b.to_u64().filter(|&e| e <= 4096).map(|e| (0..e).fold(Nat::from_u64(1), |acc, _| acc.mul(a))),
                        _ => None,
                    };
                    if let Some(r) = r {
                        return Term::nat(r);
                    }
                }
                Term::app(*s, args)
            }
            _ => t.clone(),
        }
    }
}

/// Adds two linear combinations (atoms compared structurally).
fn merge(mut a: Vec<(Term, Nat)>, b: Vec<(Term, Nat)>) -> Vec<(Term, Nat)> {
    for (v, m) in b {
        match a.iter().position(|(w, _)| *w == v) {
            Some(i) => a[i].1 = a[i].1.add(&m),
            None => a.push((v, m)),
        }
    }
    a
}
