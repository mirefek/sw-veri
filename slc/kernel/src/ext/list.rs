//! Lists: equality up to associativity of `++`, lengths (for `arith`),
//! indexing, and extensionality.
//!
//! Trusted extension. Lists are the prelude's finite sequences: functions
//! whose domain is a natural number (`list_type(T)`). A list expression is
//! read as a concatenation of pieces: `seq_one(x)` (the list `[x]`),
//! `empty` (`[]`), `seq_concat(a, b)` (`a ++ b`), `seq_append(a, x)`
//! (`a ++ [x]`), and opaque terms `l` known to be lists by a premise
//! `l in list_type(T)`. What is relied on are theorems of the prelude about
//! lists a, b (each a function on a natural number):
//!
//! * `++` is associative with unit `[]`, and `seq_append(a, x) = a ++ [x]`;
//!   `a ++ b` and `[x]` are lists;
//! * `seq_len([]) = 0`, `seq_len([x]) = 1`,
//!   `seq_len(a ++ b) = seq_len(a) + seq_len(b)`, and `seq_len(a)` is a
//!   natural;
//! * `[x][0] = x`; `(a ++ b)[i] = a[i]` for `i < seq_len(a)` and
//!   `= b[i - seq_len(a)]` for `seq_len(a) <= i < seq_len(a) + seq_len(b)`;
//! * two lists with the same length and the same elements are equal (they
//!   are the same set of pairs: `set_ext`).

use super::prop::Logic;
use crate::env::{Env, KResult, KernelError};
use crate::syntax::Printer;
use crate::term::{Node, SymId, Term};

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

#[derive(Clone, Copy)]
pub(crate) struct LSyms {
    pub concat: Option<SymId>,
    pub one: Option<SymId>,
    pub append: Option<SymId>,
    pub empty: Option<SymId>,
    pub len: Option<SymId>,
    pub list_type: Option<SymId>,
    pub app: Option<SymId>,
    pub in_: SymId,
}

impl LSyms {
    pub(crate) fn new(env: &Env) -> LSyms {
        let s = |n: &str| env.ksym(n);
        LSyms {
            concat: s("seq_concat"),
            one: s("seq_one"),
            append: s("seq_append"),
            empty: s("empty"),
            len: s("seq_len"),
            list_type: s("list_type"),
            app: s("app"),
            in_: s("in").unwrap_or(u32::MAX),
        }
    }
}

/// A piece of a flattened list.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Piece {
    /// `[x]`
    One(Term),
    /// a list known from a premise
    List(Term),
}

fn is(s: SymId, o: Option<SymId>) -> bool {
    o == Some(s)
}

/// The lists the premises name: `l in list_type(T)`.
pub(crate) fn known_lists(env: &Env, premises: &[Term]) -> Vec<Term> {
    let s = LSyms::new(env);
    premises
        .iter()
        .filter_map(|p| match p.node() {
            Node::App(i, a) if *i == s.in_ => match a[1].node() {
                Node::App(lt, _) if is(*lt, s.list_type) => Some(a[0].clone()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// `t` as a concatenation of pieces, if it is a list expression over known
/// lists.
pub(crate) fn flatten(s: &LSyms, t: &Term, known: &[Term]) -> Option<Vec<Piece>> {
    match t.node() {
        Node::App(e, a) if a.is_empty() && is(*e, s.empty) => Some(Vec::new()),
        Node::App(o, a) if is(*o, s.one) => Some(vec![Piece::One(a[0].clone())]),
        Node::App(c, a) if is(*c, s.concat) => {
            let mut x = flatten(s, &a[0], known)?;
            x.extend(flatten(s, &a[1], known)?);
            Some(x)
        }
        Node::App(c, a) if is(*c, s.append) => {
            let mut x = flatten(s, &a[0], known)?;
            x.push(Piece::One(a[1].clone()));
            Some(x)
        }
        _ if known.contains(t) => Some(vec![Piece::List(t.clone())]),
        _ => None,
    }
}

/// `t` as a concatenation of pieces, a known list taken whole even when it
/// is itself a concatenation (`flatten` takes it apart); `[]` and `[x]`
/// still by their lengths.
pub(crate) fn flatten_known(s: &LSyms, t: &Term, known: &[Term]) -> Option<Vec<Piece>> {
    match t.node() {
        Node::App(e, a) if a.is_empty() && is(*e, s.empty) => Some(Vec::new()),
        Node::App(o, a) if is(*o, s.one) => Some(vec![Piece::One(a[0].clone())]),
        _ if known.contains(t) => Some(vec![Piece::List(t.clone())]),
        Node::App(c, a) if is(*c, s.concat) => {
            let mut x = flatten_known(s, &a[0], known)?;
            x.extend(flatten_known(s, &a[1], known)?);
            Some(x)
        }
        Node::App(c, a) if is(*c, s.append) => {
            let mut x = flatten_known(s, &a[0], known)?;
            x.push(Piece::One(a[1].clone()));
            Some(x)
        }
        _ => None,
    }
}

impl Logic {
    /// `premises -> A = B` for list expressions A, B with the same pieces.
    pub fn list_eq(&self, env: &Env, premises: &[Term], goal: &Term) -> KResult<()> {
        let s = LSyms::new(env);
        let known = known_lists(env, premises);
        let (a, b) = match goal.node() {
            Node::App(e, x) if *e == env.builtins.eq => (&x[0], &x[1]),
            _ => return err("lists: the goal is not an equation"),
        };
        let p = Printer::new(env);
        let fa = flatten(&s, a, &known).ok_or_else(|| KernelError(format!("lists: not a list expression over known lists: {}", p.term(a))))?;
        let fb = flatten(&s, b, &known).ok_or_else(|| KernelError(format!("lists: not a list expression over known lists: {}", p.term(b))))?;
        if fa != fb {
            return err(format!("lists: `{}` and `{}` have different pieces", p.term(a), p.term(b)));
        }
        Ok(())
    }

    /// `premises -> L[i] = e`: for `t = app(L, i)` with L a list expression,
    /// the piece i falls in (its bounds shown by `arith` from the premises),
    /// and e the element there. Returns the equation.
    pub fn list_at(&self, env: &Env, premises: &[Term], t: &Term) -> KResult<Term> {
        let s = LSyms::new(env);
        let known = known_lists(env, premises);
        let l = match t.node() {
            Node::App(f, a) if is(*f, s.app) => &a[0],
            _ => return err("at: not `app(L, i)`"),
        };
        // (the pieces down to the known lists and singletons; failing, a
        // known concatenation taken as one piece)
        let first = flatten(&s, l, &known)
            .ok_or_else(|| KernelError("at: not a list expression over known lists".into()))
            .and_then(|p| self.list_at_pieces(env, premises, t, p));
        if first.is_err() {
            if let Some(p) = flatten_known(&s, l, &known) {
                if let Ok(r) = self.list_at_pieces(env, premises, t, p) {
                    return Ok(r);
                }
            }
        }
        first
    }

    fn list_at_pieces(&self, env: &Env, premises: &[Term], t: &Term, pieces: Vec<Piece>) -> KResult<Term> {
        let s = LSyms::new(env);
        let i = match t.node() {
            Node::App(_, a) => &a[1],
            _ => return err("at: not `app(L, i)`"),
        };
        let g = |n: &str| env.ksym(n);
        let (Some(int_add), Some(int_sub), Some(int_le), Some(int_lt), Some(and), Some(omega), Some(len)) =
            (g("int_add"), g("int_sub"), g("int_le"), g("int_lt"), g("and"), g("omega"), s.len)
        else {
            return err("at: needs the prelude's arithmetic and lists");
        };
        // (the index must be a natural: arithmetic compares values only)
        let i_nat = Term::app(s.in_, vec![i.clone(), Term::app(omega, vec![])]);
        // offset of the current piece: a literal plus lengths of lists
        let mut ones: u64 = 0;
        let mut lens: Vec<Term> = Vec::new();
        // `ones + len1 + len2 + ..` (without a leading 0)
        let off_term = |ones: u64, lens: &[Term]| {
            let mut parts: Vec<Term> = Vec::new();
            if ones > 0 || lens.is_empty() {
                parts.push(Term::nat(crate::nat::Nat::from_u64(ones)));
            }
            parts.extend(lens.iter().cloned());
            let mut o = parts[0].clone();
            for p in &parts[1..] {
                o = Term::app(int_add, vec![o, p.clone()]);
            }
            o
        };
        for pc in &pieces {
            let (plen, elem) = match pc {
                Piece::One(_) => (Term::nat(crate::nat::Nat::from_u64(1)), None::<Term>),
                Piece::List(m) => (Term::app(len, vec![m.clone()]), Some(m.clone())),
            };
            let off = off_term(ones, &lens);
            let lo = Term::app(int_le, vec![off.clone(), i.clone()]);
            let hi = Term::app(int_lt, vec![i.clone(), Term::app(int_add, vec![off.clone(), plen.clone()])]);
            let goal = Term::app(and, vec![i_nat.clone(), Term::app(and, vec![lo, hi])]);
            if self.arith(env, premises, &goal).is_ok() {
                let e = match (pc, elem) {
                    (Piece::One(x), _) => x.clone(),
                    (Piece::List(_), Some(m)) => {
                        let zero = ones == 0 && lens.is_empty();
                        let idx = if zero { i.clone() } else { Term::app(int_sub, vec![i.clone(), off]) };
                        Term::app(s.app.unwrap(), vec![m, idx])
                    }
                    _ => unreachable!(),
                };
                return Ok(env.mk_eq(t.clone(), e));
            }
            match pc {
                Piece::One(_) => ones += 1,
                Piece::List(m) => lens.push(Term::app(len, vec![m.clone()])),
            }
        }
        err(format!("at: cannot place the index `{}` in one piece of the list (bounds not shown by arith)", Printer::new(env).term(i)))
    }

    /// Extensionality: from `A in list_type(_)`, `B in list_type(_)`,
    /// `seq_len(A) = seq_len(B)` and
    /// `all i. i in omega -> int_lt(i, seq_len(A)) -> app(A, i) = app(B, i)`:
    /// `A = B`.
    pub fn list_ext(&self, env: &Env, ha: &Term, hb: &Term, hlen: &Term, hel: &Term) -> KResult<Term> {
        let s = LSyms::new(env);
        let member = |h: &Term| -> Option<Term> {
            match h.node() {
                Node::App(i, a) if *i == s.in_ => match a[1].node() {
                    Node::App(lt, _) if is(*lt, s.list_type) => Some(a[0].clone()),
                    _ => None,
                },
                _ => None,
            }
        };
        let (Some(a), Some(b)) = (member(ha), member(hb)) else { return err("list_ext: the first two premises are `A in list_type(T)`, `B in list_type(T')`") };
        let (len, app) = (s.len.unwrap(), s.app.unwrap());
        let omega = env.ksym("omega").ok_or_else(|| KernelError("no omega".into()))?;
        let int_lt = env.ksym("int_lt").ok_or_else(|| KernelError("no int_lt".into()))?;
        let want_len = env.mk_eq(Term::app(len, vec![a.clone()]), Term::app(len, vec![b.clone()]));
        if hlen != &want_len {
            return err("list_ext: the third premise is `seq_len(A) = seq_len(B)`");
        }
        // all i. i in omega -> int_lt(i, seq_len(A)) -> app(A, i) = app(B, i)
        let i = Term::bvar(0);
        let body = env.mk_imp(
            Term::app(s.in_, vec![i.clone(), Term::app(omega, vec![])]),
            env.mk_imp(
                Term::app(int_lt, vec![i.clone(), Term::app(len, vec![a.clone()])]),
                env.mk_eq(Term::app(app, vec![a.clone(), i.clone()]), Term::app(app, vec![b.clone(), i])),
            ),
        );
        let want_el = Term::app(self.all, vec![body]);
        if hel != &want_el {
            let p = Printer::new(env);
            return err(format!("list_ext: the fourth premise is `{}`", p.term(&want_el)));
        }
        Ok(env.mk_eq(a, b))
    }
}
