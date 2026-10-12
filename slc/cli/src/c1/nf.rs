//! The normal form of values (docs/overview.md, the rules' standard form):
//! N, a fixed list of proven, oriented equations (proofs/translate_nf.core),
//! applied innermost first, each step a kernel rewrite (`eq_subst`) by an
//! instance of one equation. A rule producing a value takes N of its
//! expression; one consuming a value compares normal forms (a match). Values'
//! names are atoms (their definitions are normal already).
//!
//! At a node, its arguments normal, the first that applies of:
//! - a closed literal term: its numeral (evaluated; the equation by the
//!   kernel's evaluation);
//! - a cast of a word of its width (or narrower): the word (`nf.boi_in`,
//!   the word's width by its operation's `*_in` lemma, `nf.bits_le`);
//! - a shift by a literal: a product by 2^k (`nf.shl_mul`);
//! - a commutative operation: its operands in one order, literals last
//!   (`nf.add_comm`, `x86.mul_comm`, `x86.and_comm`, `nf.or_comm`,
//!   `x86i.xor_comm`).

use super::rec::{self, R, RA};
use super::{lit, nat, Gen};
use sl_kernel::ext::seq::Seq;
use sl_kernel::{Node, Term};
use std::cmp::Ordering;

/// the commutative operations and their commutation
const COMM: [(&str, &str); 5] = [("bits_add", "nf.add_comm"), ("bits_mul", "x86.mul_comm"), ("bits_and", "x86.and_comm"), ("bits_or", "nf.or_comm"), ("bits_xor", "x86i.xor_comm")];

impl<'e> Gen<'e> {
    /// N(t) and the proof of `t = N(t)` (None: t is normal)
    pub(super) fn norm(&mut self, t: &Term) -> Result<(Term, Option<Seq>), String> {
        let t = self.canon(t);
        let r = self.nf(&t, 0)?;
        Ok(match r.1 {
            Some(e) => (self.canon(&r.0), Some(e)),
            None => r,
        })
    }

    /// A rule's result `r = E` (the standard form's premise): r the name of
    /// N(E), the premise by N's rewrites
    pub(super) fn result(&mut self, e: &Term) -> Result<(Term, RA), String> {
        let (n, pf) = self.norm(e)?;
        let r = self.value(&n);
        let prem = match pf {
            Some(pf) => Seq::sym(self.env, &pf).map_err(|e| e.0)?,
            None => Seq::refl(self.env, &self.expand(e)).map_err(|e| e.0)?,
        };
        Ok((r, rec::s(&prem)))
    }

    /// A consumer's `u = v` (the machine's value, the spec's): their normal
    /// forms the same (a match), the proof by N's rewrites
    pub(super) fn eq_nf(&mut self, u: &Term, v: &Term) -> Result<Option<RA>, String> {
        let (nu, pu) = self.norm(u)?;
        let (nv, pv) = self.norm(v)?;
        if self.canon(&nu) != self.canon(&nv) {
            return Ok(None);
        }
        let pu = match pu {
            Some(e) => e,
            None => Seq::refl(self.env, &self.expand(u)).map_err(|e| e.0)?,
        };
        let e = match pv {
            Some(e) => Seq::trans(self.env, &pu, &Seq::sym(self.env, &e).map_err(|e| e.0)?).map_err(|e| e.0)?,
            None => pu,
        };
        Ok(Some(rec::s(&e)))
    }

    /// A condition decided by a match after N: the comparison g (`=`, `<`,
    /// `<=`, under negations) and a fact in scope of the same comparison
    /// (or an order's dual, an equation either way round) of operands with
    /// the same normal forms. Its value, the fact rewritten (N's proofs, at
    /// the operands) to one of g's own operands, and the fact.
    pub(super) fn guard_nf(&mut self, g: &Term, hyps: &[(Term, Seq)]) -> Option<(bool, Vec<Seq>)> {
        fn strip(g: &Gen, t: &Term) -> (usize, Term) {
            let (mut k, mut e) = (0, t.clone());
            while let Some(a) = g.app(&e, "not", 1).map(|a| a[0].clone()) {
                k += 1;
                e = a;
            }
            (k, e)
        }
        const OPS: [&str; 3] = ["eq", "int_lt", "int_le"];
        if g.loose_depth(&self.env.binders_fn()) > 0 {
            return None;
        }
        let (k, e) = strip(self, g);
        let (op, x) = OPS.iter().find_map(|o| self.app(&e, o, 2).map(|x| (*o, x.to_vec())))?;
        let nx: Vec<(Term, Option<Seq>)> = x.iter().map(|t| self.norm(t)).collect::<Result<_, _>>().ok()?;
        let cx: Vec<Term> = nx.iter().map(|n| self.canon(&n.0)).collect();
        // (the latest facts first: a branch just taken)
        for (_, hs) in hyps.iter().rev() {
            let (hk, he) = strip(self, hs.concl());
            let Some((hop, y)) = OPS.iter().find_map(|o| self.app(&he, o, 2).map(|y| (*o, y.to_vec()))) else { continue };
            // (the fact's operand i is the guard's operand perm[i])
            let (perm, flip) = match (op, hop) {
                ("eq", "eq") | ("int_lt", "int_lt") | ("int_le", "int_le") => ([0usize, 1], false),
                ("int_lt", "int_le") | ("int_le", "int_lt") => ([1, 0], true),
                _ => continue,
            };
            let Ok(ny) = y.iter().map(|t| self.norm(t)).collect::<Result<Vec<_>, _>>() else { continue };
            let cy: Vec<Term> = ny.iter().map(|n| self.canon(&n.0)).collect();
            let perm = if cy[0] == cx[perm[0]] && cy[1] == cx[perm[1]] {
                perm
            } else if op == "eq" && cy[0] == cx[1] && cy[1] == cx[0] {
                [1, 0]
            } else {
                continue;
            };
            // (the fact with each operand replaced by the guard's: y = N = x)
            let mut f = hs.clone();
            for i in 0..2 {
                let xe = self.expand(&x[perm[i]]);
                if y[i] == xe {
                    continue;
                }
                let ey = match &ny[i].1 {
                    Some(p) => p.clone(),
                    None => Seq::refl(self.env, &y[i]).ok()?,
                };
                let eq = match &nx[perm[i]].1 {
                    Some(p) => Seq::trans(self.env, &ey, &Seq::sym(self.env, p).ok()?).ok()?,
                    None => ey,
                };
                let (_, he) = strip(self, f.concl());
                let Node::App(s, a) = he.node() else { return None };
                let mut ab = a.to_vec();
                ab[i] = Term::bvar(0);
                let mut body = Term::app(*s, ab);
                for _ in 0..hk {
                    body = self.mk("not", vec![body]);
                }
                f = Seq::subst(self.env, &eq, &body, &f).ok()?;
            }
            // (the fact itself too: a branch condition that decided an `if`
            // is spent by its own statement, proof.rs)
            return Some(((hk % 2 == k % 2) != flip, vec![f, hs.clone()]));
        }
        None
    }

    /// (depth: the rules applied on the way here -- bounded: a hint's
    /// equation undoing another's fails, not loops)
    fn nf(&mut self, t: &Term, depth: usize) -> Result<(Term, Option<Seq>), String> {
        if depth > 64 {
            return Err(format!("N: no normal form of {} (an equation undoing another's: a hint against N's order?)", self.print(t)));
        }
        if let Some(r) = self.nf_memo.get(t) {
            return Ok(r.clone());
        }
        let Node::App(f, args) = t.node() else { return Ok((t.clone(), None)) };
        if args.is_empty() || self.env.syms[*f as usize].binders.iter().any(|k| *k > 0) {
            return Ok((t.clone(), None));
        }
        // (the arguments, left to right)
        let mut cur = t.clone();
        let mut pf: Option<Seq> = None;
        for i in 0..args.len() {
            let (a2, e) = self.nf(&args[i], depth)?;
            if let Some(e) = e {
                let Node::App(_, ca) = cur.node() else { unreachable!() };
                let mut ca2 = ca.to_vec();
                ca2[i] = a2;
                let next = cur.with_args(ca2);
                let c = self.cong(&cur, i, &e)?;
                pf = Some(self.chain(pf, c)?);
                cur = next;
            }
        }
        // (a rule at the node: then the result's normal form)
        if let Some((next, e)) = self.nf_top(&cur)? {
            pf = Some(self.chain(pf, e)?);
            let (n2, e2) = self.nf(&next, depth + 1)?;
            if let Some(e2) = e2 {
                pf = Some(self.chain(pf, e2)?);
            }
            cur = n2;
        }
        let r = (cur, pf);
        self.nf_memo.insert(t.clone(), r.clone());
        Ok(r)
    }

    /// `t = t2` from `a = a2` for t's argument i (t2: t with a2 there)
    fn cong(&self, t: &Term, i: usize, e: &Seq) -> Result<Seq, String> {
        let Node::App(_, a) = t.node() else { unreachable!() };
        let mut ab = a.to_vec();
        ab[i] = Term::bvar(0);
        let te = self.expand(t);
        let body = self.env.mk_eq(te.clone(), self.expand(&t.with_args(ab)));
        let r = Seq::refl(self.env, &te).map_err(|e| e.0)?;
        Seq::subst(self.env, e, &body, &r).map_err(|e| e.0)
    }

    fn chain(&self, a: Option<Seq>, b: Seq) -> Result<Seq, String> {
        match a {
            None => Ok(b),
            Some(a) => Seq::trans(self.env, &a, &b).map_err(|e| e.0),
        }
    }

    /// a rule at t's head (its arguments normal): the result, `t = it`
    fn nf_top(&mut self, t: &Term) -> Result<Option<(Term, Seq)>, String> {
        let Node::App(f, a) = t.node() else { return Ok(None) };
        let name = self.env.syms[*f as usize].name.clone();
        // a closed literal term: its numeral
        if !matches!(name.as_str(), "pair" | "tag") {
            if let Some(k) = self.lit_eval(t) {
                let goal = self.env.mk_eq(self.expand(t), lit(k));
                let lg = &self.api.as_ref().expect("the proving context").lg;
                let e = Seq::eval_goal(self.env, lg, &[], &goal).map_err(|e| format!("N: {}: {}", self.print(t), e.0))?;
                return Ok(Some((lit(k), e)));
            }
        }
        // a cast of a word of its width or narrower
        if name == "bits_of_int" && a.len() == 2 {
            if let (Some(n), Some((m, hin))) = (nat(&a[0]), self.word_of(&a[1])) {
                if m <= n {
                    let hin = if m == n {
                        hin
                    } else {
                        rec::mp(R::Inst("nf.bits_le".into(), vec![("m", lit(m)), ("n", lit(n)), ("x", a[1].clone())]), vec![rec::simp0(), rec::simp0(), rec::simp0(), rec::p(hin)])
                    };
                    let r = rec::mp(R::Inst("nf.boi_in".into(), vec![("n", a[0].clone()), ("x", a[1].clone())]), vec![rec::simp0(), rec::p(hin)]);
                    let e = self.run(&r, &[])?;
                    return Ok(Some((a[1].clone(), e)));
                }
            }
        }
        // a shift by a literal: a product by 2^k
        if name == "bits_shl" && a.len() == 3 && nat(&a[2]).is_some() {
            let r = R::Inst("nf.shl_mul".into(), vec![("n", a[0].clone()), ("a", a[1].clone()), ("k", a[2].clone())]);
            let e = self.run(&r, &[])?;
            let next = self.mk("bits_mul", vec![a[0].clone(), a[1].clone(), self.mk("pow2", vec![a[2].clone()])]);
            return Ok(Some((next, e)));
        }
        // a commutative operation: its operands ordered
        if let Some((_, lemma)) = COMM.iter().find(|c| c.0 == name) {
            if a.len() == 3 && term_cmp(&a[1], &a[2]) == Ordering::Greater {
                let r = R::Inst(lemma.to_string(), vec![("n", a[0].clone()), ("a", a[1].clone()), ("b", a[2].clone())]);
                let e = self.run(&r, &[])?;
                return Ok(Some((t.with_args(vec![a[0].clone(), a[2].clone(), a[1].clone()]), e)));
            }
        }
        // a hint's equation (`c1 .. using L`)
        for h in self.hints.clone() {
            if let Some(x) = self.hint_at(&h, t)? {
                return Ok(Some(x));
            }
        }
        Ok(None)
    }

    /// the hint `all xs. H.. -> l = r` at t (an instance of l): r's
    /// instance, and `t = it` (the premises closed facts, by evaluation)
    fn hint_at(&mut self, h: &Seq, t: &Term) -> Result<Option<(Term, Seq)>, String> {
        // (p, BVar(j) for j < n the variables, against x)
        fn mat(p: &Term, x: &Term, n: u32, bs: &mut Vec<Option<Term>>) -> bool {
            match (p.node(), x.node()) {
                (Node::BVar(j), _) if *j < n => match &bs[*j as usize] {
                    Some(y) => y == x,
                    None => {
                        bs[*j as usize] = Some(x.clone());
                        true
                    }
                },
                (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => a.iter().zip(b.iter()).all(|(p, x)| mat(p, x, n, bs)),
                (Node::Var(f, a), Node::Var(g, b)) if f == g && a.len() == b.len() => a.iter().zip(b.iter()).all(|(p, x)| mat(p, x, n, bs)),
                _ => p == x,
            }
        }
        let (mut n, mut b) = (0u32, h.concl().clone());
        while let Some(a) = self.app(&b, "all", 1) {
            b = a[0].clone();
            n += 1;
        }
        while let Some(x) = self.app(&b, "imp", 2) {
            b = x[1].clone();
        }
        let Some(lr) = self.app(&b, "eq", 2).map(|x| x.to_vec()) else { return Ok(None) };
        let mut bs = vec![None; n as usize];
        if !mat(&lr[0], t, n, &mut bs) || bs.iter().any(|b| b.is_none()) {
            return Ok(None);
        }
        // (the outermost `all` first: BVar(n - 1))
        let args: Vec<RA> = (0..n).rev().map(|j| rec::t(bs[j as usize].as_ref().unwrap())).collect();
        let mut sq = self.run(&R::Mp(Box::new(R::S(h.clone())), args), &[])?;
        while let Some(x) = self.app(sq.concl(), "imp", 2).map(|x| x.to_vec()) {
            let lg = &self.api.as_ref().expect("the proving context").lg;
            let Ok(pf) = Seq::eval_goal(self.env, lg, &[], &x[0]) else { return Ok(None) };
            sq = Seq::mp(self.env, &sq, &pf).map_err(|e| e.0)?;
        }
        // (r's instance: its variables the matched terms)
        let vals: Vec<Term> = (0..n).map(|j| bs[j as usize].clone().unwrap()).collect();
        let next = lr[1].instantiate_params(&vals.iter().rev().cloned().collect::<Vec<_>>(), &self.env.binders_fn());
        Ok(Some((next, sq)))
    }

    /// t a word of m bits by its operation (a value's: its definition's):
    /// m, and the proof of `t in bits(m)`
    fn word_of(&self, t: &Term) -> Option<(u128, R)> {
        let d = match t.node() {
            Node::Var(v, a) if a.is_empty() => self.vals.iter().rev().find(|x| x.0 == *v).map(|x| x.1.clone())?,
            _ => t.clone(),
        };
        let Node::App(f, a) = d.node() else { return None };
        let name = self.env.syms[*f as usize].name.as_str();
        let (lemma, binds): (&str, Vec<&'static str>) = match (name, a.len()) {
            ("bits_add", 3) => ("nf.add_in", vec!["n", "a", "b"]),
            ("bits_sub", 3) => ("nf.sub_in", vec!["n", "a", "b"]),
            ("bits_mul", 3) => ("nf.mul_in", vec!["n", "a", "b"]),
            ("bits_neg", 2) => ("nf.neg_in", vec!["n", "a"]),
            ("bits_of_int", 2) => ("nf.of_int_in", vec!["n", "z"]),
            ("bits_sext", 3) => ("nf.sext_in", vec!["m", "n", "x"]),
            ("bits_and", 3) => ("bits_and_in", vec!["n", "x", "y"]),
            ("bits_or", 3) => ("bits_or_in", vec!["n", "x", "y"]),
            ("bits_xor", 3) => ("bits_xor_in", vec!["n", "x", "y"]),
            ("bits_not", 2) => ("bits_not_in", vec!["n", "x"]),
            _ => return None,
        };
        let m = nat(if name == "bits_sext" { &a[1] } else { &a[0] })?;
        let r = rec::mp(R::Inst(lemma.into(), binds.into_iter().zip(a.iter().cloned()).collect()), vec![rec::simp0()]);
        Some((m, r))
    }

    /// a closed literal term's value, a natural (words of up to 64 bits,
    /// naturals below 2^127; integers between on the way, as GIMPLE's
    /// negative constants `bits_of_int(n, int_neg(k))`)
    pub(super) fn lit_eval(&self, t: &Term) -> Option<u128> {
        self.ilit_eval(t).and_then(|v| u128::try_from(v).ok())
    }

    fn ilit_eval(&self, t: &Term) -> Option<i128> {
        if let Some(n) = nat(t) {
            return i128::try_from(n).ok();
        }
        let Node::App(f, a) = t.node() else { return None };
        let name = self.env.syms[*f as usize].name.as_str();
        let iv: Vec<i128> = a.iter().map(|x| self.ilit_eval(x)).collect::<Option<_>>()?;
        // (the integer operations)
        match (name, iv.as_slice()) {
            ("int_neg", [x]) => return Some(-x),
            ("int_sub", [x, y]) => return x.checked_sub(*y),
            ("int_add", [x, y]) => return x.checked_add(*y),
            ("int_mul", [x, y]) => return x.checked_mul(*y),
            ("bits_of_int", [n, x]) if (0..=64).contains(n) => return Some(x.rem_euclid(1i128 << n)),
            _ => {}
        }
        // (the words' and naturals' operations: of naturals)
        let v: Vec<u128> = iv.iter().map(|x| u128::try_from(*x).ok()).collect::<Option<_>>()?;
        const LIM: u128 = 1 << 126;
        let w = |n: u128| (n <= 64).then(|| (1u128 << n) - 1);
        let r = match (name, v.as_slice()) {
            ("bits_add", [n, x, y]) => (x.checked_add(*y)?) & w(*n)?,
            ("bits_sub", [n, x, y]) => (x & w(*n)?).wrapping_sub(y & w(*n)?) & w(*n)?,
            ("bits_mul", [n, x, y]) => ((x & w(*n)?).checked_mul(y & w(*n)?)?) & w(*n)?,
            ("bits_neg", [n, x]) => 0u128.wrapping_sub(x & w(*n)?) & w(*n)?,
            ("bits_and", [n, x, y]) => x & y & w(*n)?,
            ("bits_or", [n, x, y]) => (x | y) & w(*n)?,
            ("bits_xor", [n, x, y]) => (x ^ y) & w(*n)?,
            ("bits_not", [n, x]) => !x & w(*n)?,
            ("bits_shl", [n, x, k]) if *k < 64 => (x & w(*n)?).checked_mul(1 << k)? & w(*n)?,
            ("bits_shr", [n, x, k]) if *k < 128 => (x & w(*n)?) >> k,
            ("bits_sext", [m, n, x]) if *m >= 1 => {
                let x = x & w(*m)?;
                let s = if x >> (m - 1) & 1 == 1 { x | (w(*n)? & !w(*m)?) } else { x };
                s & w(*n)?
            }
            ("pow2", [k]) if *k < 126 => 1 << k,
            ("int_pow", [2, k]) if *k < 126 => 1 << k,
            ("int_div", [x, y]) if *y > 0 => x / y,
            ("int_mod", [x, y]) if *y > 0 => x % y,
            _ => return None,
        };
        (r < LIM).then_some(r as i128)
    }
}

/// the operands' order: values (by their names), operations, literals last
fn term_cmp(a: &Term, b: &Term) -> Ordering {
    fn rank(t: &Term) -> u8 {
        match t.node() {
            Node::Var(..) => 0,
            Node::App(..) | Node::BVar(_) | Node::Bytes(_) => 1,
            Node::Nat(_) => 2,
        }
    }
    match (a.node(), b.node()) {
        (Node::Var(x, xa), Node::Var(y, ya)) => x.cmp(y).then_with(|| args_cmp(xa, ya)),
        (Node::App(f, xa), Node::App(g, ya)) => f.cmp(g).then_with(|| args_cmp(xa, ya)),
        (Node::Nat(x), Node::Nat(y)) => x.cmp(y),
        (Node::BVar(x), Node::BVar(y)) => x.cmp(y),
        _ => rank(a).cmp(&rank(b)),
    }
}

fn args_cmp(a: &[Term], b: &[Term]) -> Ordering {
    for (x, y) in a.iter().zip(b) {
        let c = term_cmp(x, y);
        if c != Ordering::Equal {
            return c;
        }
    }
    a.len().cmp(&b.len())
}
