//! The normal form of values (docs/overview.md, the rules' standard form):
//! N, a fixed list of proven, oriented equations (proofs/translate_nf.core),
//! applied innermost first, each step a kernel rewrite (`eq_subst`) by an
//! instance of one equation. A rule producing a value takes N of its
//! expression; one consuming a value compares normal forms (a match). Values'
//! names are atoms (their definitions are normal already), but for a name of
//! a sum or product: its definition (the ring's terms seen through names).
//!
//! At a node, its arguments normal, the first that applies of:
//! - a closed literal term: its numeral (evaluated; the equation by the
//!   kernel's evaluation);
//! - a cast of a word of its width (or narrower): the word (`nf.boi_in`,
//!   the word's width by its operation's `*_in` lemma, `nf.bits_le`);
//! - a shift by a literal: a product by 2^k (`nf.shl_mul`); a value added
//!   to itself: twice it (`nf.add_self`);
//! - a word's low k bits (`x + 0` at k bits): of a word of at most k bits,
//!   the word (`nf.lo_fit`); of a bitwise operation of at least k bits, the
//!   operation's on the operands' low k bits (`nf.lo_and`, `nf.lo_or`,
//!   `nf.lo_xor`) -- a narrower register's value; its names seen through
//!   only in that comparison (`eq_nf_bits`);
//! - the ring of words modulo 2^n: a sum nested to the left
//!   (`nf.add_assoc`), its terms in order (`nf.add_swap`), its literals
//!   gathered last (`nf.add_lits`); a product by a literal distributed over a
//!   sum (`nf.mul_distr`), literal factors gathered (`nf.mul_mul`);
//!   GIMPLE's sum of two literals (a static's field) the word sum
//!   (`nf.int_add_bits`);
//! - a commutative operation: its operands in one order, literals last
//!   (`nf.add_comm`, `x86.mul_comm`, `x86.and_comm`, `nf.or_comm`,
//!   `x86i.xor_comm`).
//!
//! The order of operands is the kernel terms' (by their hash, the names
//! expanded): the same whatever was named when.

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
        Ok(self.eq_nf_seq(u, v)?.map(|e| rec::s(&e)))
    }

    /// `eq_nf_seq` with bitwise operations' names seen through (a narrower
    /// register's bits against the spec's: the machine's 32-bit `or` of a
    /// byte, GIMPLE's 8-bit one); N's own normal forms untouched
    pub(super) fn eq_nf_bits(&mut self, u: &Term, v: &Term) -> Result<Option<Seq>, String> {
        std::mem::swap(&mut self.nf_memo, &mut self.nf_bits_memo);
        self.nf_bits = true;
        let r = self.eq_nf_seq(u, v);
        self.nf_bits = false;
        std::mem::swap(&mut self.nf_memo, &mut self.nf_bits_memo);
        r
    }

    /// the same, the equation's proof
    pub(super) fn eq_nf_seq(&mut self, u: &Term, v: &Term) -> Result<Option<Seq>, String> {
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
        Ok(Some(e))
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
        if depth > 256 {
            return Err(format!("N: no normal form of {} (an equation undoing another's: a hint against N's order?)", self.print(t)));
        }
        if let Some(r) = self.nf_memo.get(t) {
            return Ok(r.clone());
        }
        // (a name of a sum or product: its definition -- the ring's terms
        // seen through names; with `nf_bits`, a bitwise operation's too --
        // a narrower register's bits; the same kernel term, no step)
        if let Node::Var(v, a) = t.node() {
            if a.is_empty() {
                let def = self.vals.iter().rev().find(|x| x.0 == *v).map(|x| x.1.clone());
                let ops: &[&str] = if self.nf_bits { &["bits_add", "bits_mul", "bits_and", "bits_or", "bits_xor"] } else { &["bits_add", "bits_mul"] };
                // (and a one-element list's: a stack object's address list)
                if let Some(d) = def.filter(|d| ops.iter().any(|o| self.app(d, o, 3).is_some()) || self.app(d, "seq_one", 1).is_some()) {
                    let r = self.nf(&d, depth)?;
                    self.nf_memo.insert(t.clone(), r.clone());
                    return Ok(r);
                }
            }
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
            if e.is_none() && a2 == args[i] {
                continue;
            }
            let Node::App(_, ca) = cur.node() else { unreachable!() };
            let mut ca2 = ca.to_vec();
            ca2[i] = a2;
            let next = cur.with_args(ca2);
            // (a name unfolded: the same kernel term)
            if let Some(e) = e {
                let c = self.cong(&cur, i, &e)?;
                pf = Some(self.chain(pf, c)?);
            }
            cur = next;
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
        // a one-element list's first element (a stack object's address)
        if name == "app" && a.len() == 2 && nat(&a[1]) == Some(0) {
            if let Some(x) = self.app(&a[0], "seq_one", 1).map(|x| x[0].clone()) {
                let e = self.run(&R::Inst("nf.seq_one0".into(), vec![("x", x.clone())]), &[])?;
                return Ok(Some((x, e)));
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
        // a value added to itself: twice it
        if name == "bits_add" && a.len() == 3 && a[1] == a[2] {
            let e = self.run(&R::Inst("nf.add_self".into(), vec![("n", a[0].clone()), ("x", a[1].clone())]), &[])?;
            return Ok(Some((self.mk("bits_mul", vec![a[0].clone(), a[1].clone(), lit(2)]), e)));
        }
        // a word's low k bits (a narrower register's value, `x + 0` at k
        // bits): of a word of at most k bits, the word; of a bitwise
        // operation of at least k bits, the operation's on the operands'
        // low k bits
        if name == "bits_add" && a.len() == 3 && nat(&a[2]) == Some(0) {
            if let Some(k) = nat(&a[0]) {
                if let Some((m, hin)) = self.word_of(&a[1]) {
                    if m <= k {
                        let r = rec::mp(
                            R::Inst("nf.lo_fit".into(), vec![("k", a[0].clone()), ("m", lit(m)), ("x", a[1].clone())]),
                            vec![rec::simp0(), rec::simp0(), rec::simp0(), rec::p(hin)],
                        );
                        let e = self.run(&r, &[])?;
                        return Ok(Some((a[1].clone(), e)));
                    }
                }
                for (op, lemma) in [("bits_and", "nf.lo_and"), ("bits_or", "nf.lo_or"), ("bits_xor", "nf.lo_xor")] {
                    let Some(x) = self.app(&a[1], op, 3).map(|x| x.to_vec()) else { continue };
                    let Some(n) = nat(&x[0]) else { continue };
                    if k > n {
                        continue;
                    }
                    let (Some(pa), Some(pb)) = (self.nat_of(&x[1]), self.nat_of(&x[2])) else { continue };
                    let r = rec::mp(
                        R::Inst(lemma.into(), vec![("k", a[0].clone()), ("n", x[0].clone()), ("a", x[1].clone()), ("b", x[2].clone())]),
                        vec![rec::simp0(), rec::simp0(), rec::simp0(), pa, pb],
                    );
                    let e = self.run(&r, &[])?;
                    let lo = |g: &Gen, y: &Term| g.mk("bits_add", vec![a[0].clone(), y.clone(), lit(0)]);
                    return Ok(Some((self.mk(op, vec![a[0].clone(), lo(self, &x[1]), lo(self, &x[2])]), e)));
                }
            }
        }
        // a sum: nested to the left, its terms in order, literals gathered
        // last (the ring modulo 2^n)
        let inst = |g: &mut Gen, l: &str, bs: Vec<(&'static str, Term)>| g.run(&rec::mp(R::Inst(l.into(), bs), vec![rec::simp0()]), &[]);
        if name == "bits_add" && a.len() == 3 {
            let n = a[0].clone();
            if let Some(r) = self.app(&a[2], "bits_add", 3).filter(|r| r[0] == n).map(|r| r.to_vec()) {
                let e = inst(self, "nf.add_assoc", vec![("n", n.clone()), ("a", a[1].clone()), ("b", r[1].clone()), ("c", r[2].clone())])?;
                let next = self.mk("bits_add", vec![n.clone(), self.mk("bits_add", vec![n, a[1].clone(), r[1].clone()]), r[2].clone()]);
                return Ok(Some((next, e)));
            }
            if let Some(l) = self.app(&a[1], "bits_add", 3).filter(|l| l[0] == n).map(|l| l.to_vec()) {
                let (x, b, c) = (l[1].clone(), l[2].clone(), a[2].clone());
                // (two literals, or two like terms, last: together -- then
                // gathered, combined)
                if (nat(&b).is_some() && nat(&c).is_some()) || self.like(&n, &b, &c).is_some() {
                    let e = inst(self, "nf.add_lits", vec![("n", n.clone()), ("x", x.clone()), ("k1", b.clone()), ("k2", c.clone())])?;
                    return Ok(Some((self.mk("bits_add", vec![n.clone(), x, self.mk("bits_add", vec![n, b, c])]), e)));
                }
                if self.sum_cmp(&n, &b, &c) == Ordering::Greater {
                    let e = inst(self, "nf.add_swap", vec![("n", n.clone()), ("x", x.clone()), ("b", b.clone()), ("c", c.clone())])?;
                    return Ok(Some((self.mk("bits_add", vec![n.clone(), self.mk("bits_add", vec![n, x, c]), b]), e)));
                }
            } else {
                // (two terms: like ones combined, a*c1 + a*c2 = a*(c1 + c2);
                // else ordered -- their bases, literals last)
                if let Some((lemma, bs, next)) = self.like(&n, &a[1], &a[2]) {
                    let e = inst(self, lemma, bs)?;
                    return Ok(Some((next, e)));
                }
                if self.sum_cmp(&n, &a[1], &a[2]) == Ordering::Greater {
                    let e = self.run(&R::Inst("nf.add_comm".into(), vec![("n", n.clone()), ("a", a[1].clone()), ("b", a[2].clone())]), &[])?;
                    return Ok(Some((t.with_args(vec![n, a[2].clone(), a[1].clone()]), e)));
                }
            }
        }
        // a product by a literal: distributed over a sum, literal factors
        // gathered
        if name == "bits_mul" && a.len() == 3 && nat(&a[2]).is_some() {
            let n = a[0].clone();
            if let Some(s) = self.app(&a[1], "bits_add", 3).filter(|s| s[0] == n).map(|s| s.to_vec()) {
                let e = inst(self, "nf.mul_distr", vec![("n", n.clone()), ("a", s[1].clone()), ("b", s[2].clone()), ("c", a[2].clone())])?;
                let m = |g: &Gen, x: &Term| g.mk("bits_mul", vec![n.clone(), x.clone(), a[2].clone()]);
                return Ok(Some((self.mk("bits_add", vec![n.clone(), m(self, &s[1]), m(self, &s[2])]), e)));
            }
            if let Some(m) = self.app(&a[1], "bits_mul", 3).filter(|m| m[0] == n && nat(&m[2]).is_some()).map(|m| m.to_vec()) {
                let e = inst(self, "nf.mul_mul", vec![("n", n.clone()), ("a", m[1].clone()), ("c1", m[2].clone()), ("c2", a[2].clone())])?;
                return Ok(Some((self.mk("bits_mul", vec![n.clone(), m[1].clone(), self.mk("bits_mul", vec![n, m[2].clone(), a[2].clone()])]), e)));
            }
        }
        // GIMPLE's sum of two literals (a static's field's address): the
        // word sum, in the address range by evaluation
        if name == "int_add" && a.len() == 2 {
            if let (Some(x), Some(y)) = (self.eval_lit(&a[0]), self.eval_lit(&a[1])) {
                if x.checked_add(y).is_some_and(|s| s < 1u128 << 64) {
                    let lg = &self.api.as_ref().expect("the proving context").lg;
                    let omega = self.mk("omega", vec![]);
                    let goals = [
                        self.mk("in", vec![self.expand(&a[0]), omega.clone()]),
                        self.mk("in", vec![self.expand(&a[1]), omega]),
                        self.mk("int_lt", vec![self.expand(t), self.mk("pow2", vec![lit(64)])]),
                    ];
                    let mut ps = Vec::new();
                    for g in &goals {
                        ps.push(rec::s(&Seq::eval_goal(self.env, lg, &[], g).map_err(|e| format!("N: {}: {}", self.print(g), e.0))?));
                    }
                    let e = self.run(&rec::mp(R::Inst("nf.int_add_bits".into(), vec![("a", a[0].clone()), ("b", a[1].clone())]), ps), &[])?;
                    return Ok(Some((self.mk("bits_add", vec![lit(64), a[0].clone(), a[1].clone()]), e)));
                }
            }
        }
        // a commutative operation: its operands ordered (a sum's: above)
        if let Some((_, lemma)) = COMM.iter().find(|c| c.0 == name && name != "bits_add") {
            if a.len() == 3 && self.term_cmp(&a[1], &a[2]) == Ordering::Greater {
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

    /// `t in omega`'s proof: a literal's by evaluation, a word's from its
    /// width (`nf.bits_nat`); None if t is neither
    pub(super) fn nat_of(&self, t: &Term) -> Option<RA> {
        if nat(t).is_some() {
            return Some(rec::simp0());
        }
        let (m, hin) = self.word_of(t)?;
        Some(rec::p(rec::mp(R::Inst("nf.bits_nat".into(), vec![("m", lit(m)), ("x", t.clone())]), vec![rec::p(hin)])))
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

/// a term's place in the operands' order apart from its kernel term's
/// hash: literals last
fn rank(t: &Term) -> u8 {
    match t.node() {
        Node::Nat(_) => 1,
        _ => 0,
    }
}

/// the structural order of kernel terms (a hash's tie)
fn struct_cmp(a: &Term, b: &Term) -> Ordering {
    let args_cmp = |xa: &[Term], ya: &[Term]| {
        for (x, y) in xa.iter().zip(ya) {
            let c = struct_cmp(x, y);
            if c != Ordering::Equal {
                return c;
            }
        }
        xa.len().cmp(&ya.len())
    };
    let k = |t: &Term| match t.node() {
        Node::Var(..) => 0,
        Node::App(..) => 1,
        Node::BVar(_) => 2,
        Node::Bytes(_) => 3,
        Node::Nat(_) => 4,
    };
    match (a.node(), b.node()) {
        (Node::Var(x, xa), Node::Var(y, ya)) => x.cmp(y).then_with(|| args_cmp(xa, ya)),
        (Node::App(f, xa), Node::App(g, ya)) => f.cmp(g).then_with(|| args_cmp(xa, ya)),
        (Node::Nat(x), Node::Nat(y)) => x.cmp(y),
        (Node::BVar(x), Node::BVar(y)) => x.cmp(y),
        (Node::Bytes(x), Node::Bytes(y)) => x.cmp(y),
        _ => k(a).cmp(&k(b)),
    }
}

impl<'e> Gen<'e> {
    /// a sum's term without its literal factor (at width n)
    fn base(&self, n: &Term, t: &Term) -> Term {
        match self.app(t, "bits_mul", 3) {
            Some(m) if m[0] == *n && nat(&m[2]).is_some() => m[1].clone(),
            _ => t.clone(),
        }
    }

    /// a sum's terms' order: literals last, by their bases, then themselves
    /// (like terms next to each other)
    fn sum_cmp(&self, n: &Term, a: &Term, b: &Term) -> Ordering {
        rank(&self.expand(a)).cmp(&rank(&self.expand(b))).then_with(|| self.term_cmp(&self.base(n, a), &self.base(n, b))).then_with(|| self.term_cmp(a, b))
    }

    /// two like terms (not literals) b + c: the equation combining them, its
    /// instance, the result
    #[allow(clippy::type_complexity)]
    fn like(&self, n: &Term, b: &Term, c: &Term) -> Option<(&'static str, Vec<(&'static str, Term)>, Term)> {
        if nat(b).is_some() || nat(c).is_some() || self.expand(&self.base(n, b)) != self.expand(&self.base(n, c)) {
            return None;
        }
        let k = |t: &Term| self.app(t, "bits_mul", 3).filter(|m| m[0] == *n && nat(&m[2]).is_some()).map(|m| m[2].clone());
        let mul = |a: &Term, x: Term| self.mk("bits_mul", vec![n.clone(), a.clone(), x]);
        let add = |x: Term, y: Term| self.mk("bits_add", vec![n.clone(), x, y]);
        let a = self.base(n, b);
        Some(match (k(b), k(c)) {
            (Some(c1), Some(c2)) => ("nf.add_like", vec![("n", n.clone()), ("a", a.clone()), ("c1", c1.clone()), ("c2", c2.clone())], mul(&a, add(c1, c2))),
            (None, Some(c2)) => ("nf.add_like1", vec![("n", n.clone()), ("a", a.clone()), ("c", c2.clone())], mul(&a, add(lit(1), c2))),
            (Some(c1), None) => ("nf.add_like2", vec![("n", n.clone()), ("a", a.clone()), ("c", c1.clone())], mul(&a, add(c1, lit(1)))),
            (None, None) => ("nf.add_self", vec![("n", n.clone()), ("x", a.clone())], mul(&a, lit(2))),
        })
    }

    /// the operands' order: by the kernel terms (the names expanded: the
    /// same order whatever was named when), literals last
    fn term_cmp(&self, a: &Term, b: &Term) -> Ordering {
        use std::hash::{Hash, Hasher};
        let (ea, eb) = (self.expand(a), self.expand(b));
        let h = |t: &Term| {
            let mut s = std::collections::hash_map::DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        };
        rank(&ea).cmp(&rank(&eb)).then_with(|| h(&ea).cmp(&h(&eb))).then_with(|| struct_cmp(&ea, &eb))
    }
}
