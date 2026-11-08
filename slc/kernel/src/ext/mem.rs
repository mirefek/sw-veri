//! Memory reads through writes: `mem_read`.
//!
//! Trusted extension. A read of m bytes at b of a memory M,
//! `gimple.bytes_at(M, b, m)` (the sum of `app(app(M, "bytes"), bits_add(64,
//! b, bits_of_int(64, i))) * 256^i` for i < m: M's bytes alone), where M is
//! built by updates of other fields `fn_update(M', k, x)` (k a string other
//! than "bytes") and of its bytes `fn_update(M', "bytes", X)`, X built by
//! writes `x86_64_linux.store_le(X', a, n, v)` (the byte at y:
//! `bits_of_int(8, int_div(v, 256^(y - a)))` if `bits_sub(64, y, a) < n`,
//! else X''s) on some memory's bytes `app(M'', "bytes")` (the read then
//! M'''s) or on bytes of another form, is resolved by walking M from the
//! outside in. Each n is a numeral, m too unless every write is apart; the
//! facts (premises) must give, by `arith`, the read's and each write's
//! range in the address space -- `0 <= b`, `b + m <= 2^64` (likewise a, n)
//! -- so that the addresses `bits_add` / `bits_sub` form are the integer
//! ones. For each write, in this order:
//!
//! * apart (`a + n <= b || b + m <= a`): every byte read is M''s (for b + i
//!   below a the distance `bits_sub(64, b + i, a)` is `b + i - a + 2^64 >=
//!   n`): the read is M''s, and the walk goes on;
//! * the same (a = b, n = m): byte i is v's i-th base-256 digit, so the read
//!   is `int_mod(v, int_pow(256, n))`;
//! * contained (`a <= b`, `b + m <= a + n`): byte i is v's digit `b - a + i`,
//!   so the read is `int_mod(int_div(v, int_pow(256, int_sub(b, a))),
//!   int_pow(256, m))` (`(v div 256^d) div 256^i = v div 256^(d + i)`);
//!
//! else, with earlier writes passed (or other fields' updates), the read is
//! of the memory at this write (it left in place); else an error naming the
//! write. A byte `app(app(M, "bytes"), b)`, b in bits(64) by `arith` (so
//! store_le's `fn_build` applies at b), is read the same as one byte (m =
//! 1): past apart writes, inside one `bits_of_int(8, int_div(v,
//! int_pow(256, int_sub(b, a))))` (`int_pow(256, 0)` if b is a), the rest
//! `app(app(M', "bytes"), b)`. A memory or bytes of
//! another form end the walk: the read is then `gimple.bytes_at` of that
//! memory (of `fn_update(M', "bytes", X')` for bytes X'). The facts given to
//! each `arith` check are the premises connected to its terms (a choice of
//! premises, so sound however it is made).
//! What is relied on: the definitions of `gimple.bytes_at`,
//! `x86_64_linux.store_le` and the prelude's `fn_update` / `app` /
//! `fn_build`, base-256 digits of an integer (floor division), and
//! `arith`'s soundness.

use super::prop::Logic;
use crate::env::{Env, KResult, KernelError};
use crate::nat::Nat;
use crate::syntax::Printer;
use crate::term::{Node, Term};

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

fn numeral(t: &Term) -> Option<u128> {
    match t.node() {
        Node::Nat(n) => n.to_u128(),
        _ => None,
    }
}

/// t's maximal subterms not headed by an arithmetic symbol (its terms as
/// arith reads them); of a membership `x in T`, with `in_`, x's only (T a
/// type, shared by unrelated facts)
fn names(t: &Term, arith: &[crate::term::SymId], in_: Option<crate::term::SymId>, out: &mut Vec<Term>) {
    match t.node() {
        Node::App(f, a) if Some(*f) == in_ && a.len() == 2 => names(&a[0], arith, in_, out),
        Node::App(f, a) if arith.contains(f) => {
            for x in a.iter() {
                names(x, arith, in_, out);
            }
        }
        Node::Nat(_) | Node::BVar(_) => {}
        _ => {
            if !out.contains(t) {
                out.push(t.clone());
            }
        }
    }
}

impl Logic {
    /// the premises (their positions) about the goal's terms, as `arith`
    /// reads terms (its maximal subterms not headed by an arithmetic or
    /// propositional symbol). Narrow: the premises mentioning one of them,
    /// and through the equations among those, their other sides' terms (an
    /// address's equation, then the bounds of its terms). Wide (for when the
    /// narrow choice does not do): the premises connected to the goal by
    /// shared terms -- a membership's type not shared --, those that branch
    /// (a disjunction, negation, implication: arith splits their cases) only
    /// when about the goal's own terms.
    pub fn arith_relevant(&self, env: &Env, premises: &[Term], goal: &Term, wide: bool) -> Vec<usize> {
        let arith_syms: Vec<_> = [
            "int_add", "int_sub", "int_neg", "int_mul", "int_div", "int_mod", "int_pow", "pow2", "int_le", "int_lt", "bits_add", "bits_sub", "bits_of_int", "bits",
            "omega", "not", "and", "or",
        ]
        .iter()
        .filter_map(|n| env.ksym(*n))
        .chain([env.builtins.eq, env.builtins.imp, self.in_])
        .collect();
        let in_ = wide.then_some(self.in_);
        let mut gn = Vec::new();
        names(goal, &arith_syms, in_, &mut gn);
        let pns: Vec<Vec<Term>> = premises
            .iter()
            .map(|p| {
                let mut pn = Vec::new();
                names(p, &arith_syms, in_, &mut pn);
                pn
            })
            .collect();
        if !wide {
            let mut sel: Vec<bool> = pns.iter().map(|pn| pn.iter().any(|x| gn.contains(x))).collect();
            // (through the equations selected: their other sides' terms)
            let eq = env.builtins.eq;
            let mut en = Vec::new();
            for (i, p) in premises.iter().enumerate() {
                if sel[i] && matches!(p.node(), Node::App(f, _) if *f == eq) {
                    for x in &pns[i] {
                        if !gn.contains(x) && !en.contains(x) {
                            en.push(x.clone());
                        }
                    }
                }
            }
            for (i, pn) in pns.iter().enumerate() {
                if !sel[i] && pn.iter().any(|x| en.contains(x)) {
                    sel[i] = true;
                }
            }
            return (0..premises.len()).filter(|&i| sel[i]).collect();
        }
        let branching: Vec<_> = ["not", "or"].iter().filter_map(|n| env.ksym(*n)).chain([env.builtins.imp]).collect();
        fn branches(t: &Term, arith: &[crate::term::SymId], br: &[crate::term::SymId]) -> bool {
            match t.node() {
                Node::App(f, _) if br.contains(f) => true,
                Node::App(f, a) if arith.contains(f) => a.iter().any(|x| branches(x, arith, br)),
                _ => false,
            }
        }
        let goal_names = gn.clone();
        let br: Vec<bool> = premises.iter().map(|p| branches(p, &arith_syms, &branching)).collect();
        let mut sel = vec![false; premises.len()];
        loop {
            let mut grew = false;
            for (i, pn) in pns.iter().enumerate() {
                let near = if br[i] { &goal_names } else { &gn };
                if !sel[i] && pn.iter().any(|x| near.contains(x)) {
                    sel[i] = true;
                    grew = true;
                    for x in pn {
                        if !gn.contains(x) {
                            gn.push(x.clone());
                        }
                    }
                }
            }
            if !grew {
                break;
            }
        }
        (0..premises.len()).filter(|&i| sel[i]).collect()
    }

    /// whether a premise branches arith's cases (a disjunction, implication
    /// or negation, also inside a conjunction)
    pub fn branching(&self, env: &Env, t: &Term) -> bool {
        let (and, or, not) = (env.ksym("and"), env.ksym("or"), env.ksym("not"));
        match t.node() {
            Node::App(f, _) if Some(*f) == or || Some(*f) == not || *f == env.builtins.imp => true,
            Node::App(f, a) if Some(*f) == and => a.iter().any(|x| self.branching(env, x)),
            _ => false,
        }
    }

    /// the premise sets `arith_rel` tries, in order: the narrow choice
    /// (`arith_relevant`) without its branching premises (no case splits on
    /// facts the goal may not need), the narrow choice, the wide one (each
    /// only if not the set before); and the narrow choice's place
    pub fn arith_tiers(&self, env: &Env, premises: &[Term], goal: &Term) -> (Vec<Vec<usize>>, usize) {
        let narrow = self.arith_relevant(env, premises, goal, false);
        let units: Vec<usize> = narrow.iter().copied().filter(|&i| !self.branching(env, &premises[i])).collect();
        let wide = self.arith_relevant(env, premises, goal, true);
        let mut out = Vec::new();
        if units.len() < narrow.len() {
            out.push(units);
        }
        let at = out.len();
        let same = wide == narrow;
        out.push(narrow);
        if !same {
            out.push(wide);
        }
        (out, at)
    }

    /// `goal` by arith from the premises about its terms (`arith_tiers`)
    pub fn arith_rel(&self, env: &Env, premises: &[Term], goal: &Term) -> bool {
        self.arith_tiers(env, premises, goal).0.into_iter().any(|sel| {
            let rel: Vec<Term> = sel.into_iter().map(|i| premises[i].clone()).collect();
            self.arith(env, &rel, goal).is_ok()
        })
    }

    /// `t = r`, t = `gimple.bytes_at(M, b, m)` resolved through M's writes
    /// (see the module docs).
    pub fn mem_read(&self, env: &Env, premises: &[Term], t: &Term) -> KResult<Term> {
        let g = |n: &str| env.ksym(n);
        let (Some(bytes_at), Some(fn_update), Some(store_le), Some(app), Some(int_add), Some(int_sub), Some(int_le), Some(int_mod), Some(int_div), Some(int_pow), Some(and), Some(or)) = (
            g("gimple.bytes_at"),
            g("fn_update"),
            g("x86_64_linux.store_le"),
            g("app"),
            g("int_add"),
            g("int_sub"),
            g("int_le"),
            g("int_mod"),
            g("int_div"),
            g("int_pow"),
            g("and"),
            g("or"),
        ) else {
            return err("mem_read: needs the prelude, gimple.bytes_at and x86_64_linux.store_le");
        };
        let pr = Printer::new(env);
        let is_bytes_key = |k: &Term| matches!(k.node(), Node::Bytes(k) if &**k == b"bytes");
        let nat = |v: u128| Term::nat(Nat::from_u128(v));
        // (a byte `app(app(M, "bytes"), b)`: read as one byte, b in bits(64))
        let (mut m_t, b, m, byte) = match t.node() {
            Node::App(f, a) if *f == bytes_at && a.len() == 3 => (a[0].clone(), a[1].clone(), a[2].clone(), false),
            Node::App(f, a) if *f == app && a.len() == 2 => match a[0].node() {
                Node::App(f2, c) if *f2 == app && c.len() == 2 && is_bytes_key(&c[1]) => (c[0].clone(), a[1].clone(), nat(1), true),
                _ => return err(format!("mem_read: not `gimple.bytes_at(M, b, m)` or `M.bytes[b]`: {}", pr.short(t))),
            },
            _ => return err(format!("mem_read: not `gimple.bytes_at(M, b, m)` or `M.bytes[b]`: {}", pr.short(t))),
        };
        let Some(bits_of_int) = g("bits_of_int") else { return err("mem_read: needs bits_of_int") };
        if byte {
            let (in_, Some(bits)) = (self.in_, g("bits")) else { return err("mem_read: needs bits") };
            let b64 = Term::app(in_, vec![b.clone(), Term::app(bits, vec![nat(64)])]);
            if !self.arith_rel(env, premises, &b64) {
                return err(format!("mem_read: the byte's address not shown in bits(64): {}", pr.short(&b)));
            }
        }
        // (a numeral for a write the read meets; any size past apart writes)
        let mn = numeral(&m);
        let two64 = nat(1u128 << 64);
        let zero = nat(0);
        let le = |x: Term, y: Term| Term::app(int_le, vec![x, y]);
        let add = |x: Term, y: Term| Term::app(int_add, vec![x, y]);
        let conj = |x: Term, y: Term| Term::app(and, vec![x, y]);
        let in_range = |a: &Term, n: &Term| conj(le(zero.clone(), a.clone()), le(add(a.clone(), n.clone()), two64.clone()));
        // (each goal from the premises about its terms)
        let holds = |goal: &Term| self.arith_rel(env, premises, goal);
        if !holds(&in_range(&b, &m)) {
            return err(format!("mem_read: the read's range not shown in the address space: 0 <= {0}, {0} + {1} <= 2^64", pr.short(&b), pr.short(&m)));
        }
        let mut steps = 0;
        // in a memory's bytes: (the memory updated, the key, the bytes X)
        let mut cur: Option<(Term, Term, Term)> = None;
        loop {
            let Some((inner, key, x)) = cur.clone() else {
                // a memory: past its other fields' updates, into its bytes
                let Node::App(f, a) = m_t.node() else { break };
                if *f != fn_update || a.len() != 3 {
                    break;
                }
                match a[1].node() {
                    Node::Bytes(_) if is_bytes_key(&a[1]) => cur = Some((a[0].clone(), a[1].clone(), a[2].clone())),
                    // (another field: the bytes are the inner memory's)
                    Node::Bytes(_) => {
                        m_t = a[0].clone();
                        steps += 1;
                    }
                    _ => break,
                }
                continue;
            };
            let Node::App(s, sa) = x.node() else { break };
            // a memory's bytes app(W, "bytes"): W's
            if *s == app && sa.len() == 2 && is_bytes_key(&sa[1]) {
                m_t = sa[0].clone();
                cur = None;
                steps += 1;
                continue;
            }
            // store_le(X', wa, wn, v)
            if *s != store_le || sa.len() != 4 {
                break;
            }
            let (wa, wn_t, v) = (sa[1].clone(), sa[2].clone(), sa[3].clone());
            let Some(wn) = numeral(&wn_t) else {
                return err(format!("mem_read: a write of a size not a numeral: {}", pr.short(&x)));
            };
            if !holds(&in_range(&wa, &wn_t)) {
                return err(format!("mem_read: a write's range not shown in the address space: 0 <= {0}, {0} + {1} <= 2^64", pr.short(&wa), wn));
            }
            // (the steps before this write: past writes shown apart, other
            // fields' updates)
            let passed = steps;
            steps += 1;
            // apart: past it
            let apart = Term::app(or, vec![le(add(wa.clone(), wn_t.clone()), b.clone()), le(add(b.clone(), m.clone()), wa.clone())]);
            if holds(&apart) {
                cur = Some((inner, key, sa[0].clone()));
                continue;
            }
            let pow = |e: Term| Term::app(int_pow, vec![nat(256), e]);
            // a byte inside the write: its digit b - a
            if byte {
                if holds(&conj(le(wa.clone(), b.clone()), le(add(b.clone(), m.clone()), add(wa.clone(), wn_t.clone())))) {
                    let d = if wa == b { nat(0) } else { Term::app(int_sub, vec![b.clone(), wa.clone()]) };
                    let r = Term::app(bits_of_int, vec![nat(8), Term::app(int_div, vec![v, pow(d)])]);
                    return Ok(Term::app(env.builtins.eq, vec![t.clone(), r]));
                }
            } else if let Some(mn) = mn {
                // the same: its value
                if wn == mn && holds(&conj(le(wa.clone(), b.clone()), le(b.clone(), wa.clone()))) {
                    let r = Term::app(int_mod, vec![v, pow(nat(wn))]);
                    return Ok(Term::app(env.builtins.eq, vec![t.clone(), r]));
                }
                // contained: its digits from b - a
                if holds(&conj(le(wa.clone(), b.clone()), le(add(b.clone(), m.clone()), add(wa.clone(), wn_t.clone())))) {
                    let d = Term::app(int_sub, vec![b.clone(), wa.clone()]);
                    let r = Term::app(int_mod, vec![Term::app(int_div, vec![v, pow(d)]), pow(nat(mn))]);
                    return Ok(Term::app(env.builtins.eq, vec![t.clone(), r]));
                }
            }
            // (a write not decided after others passed: the read of the
            // memory there, this write in place -- as at a form not looked
            // into, below; every write passed was apart)
            if passed > 0 {
                steps = passed;
                break;
            }
            return err(format!(
                "mem_read: the read of {} bytes at {} and the write of {} bytes at {}: not shown apart, the same, or the read inside the write{}",
                pr.short(&m),
                pr.short(&b),
                wn,
                pr.short(&wa),
                if mn.is_none() { " (the read's size not a numeral: only apart writes pass)" } else { "" }
            ));
        }
        // (the rest: a memory, or bytes of another form in their memory)
        let rest = match cur {
            Some((inner, key, x)) => Term::app(fn_update, vec![inner, key, x]),
            None => m_t,
        };
        if steps == 0 {
            return err(format!("mem_read: no write to read through in {}", pr.short(&rest)));
        }
        let r = if byte { Term::app(app, vec![Term::app(app, vec![rest, Term::bytes(b"bytes")]), b]) } else { Term::app(bytes_at, vec![rest, b, m]) };
        Ok(Term::app(env.builtins.eq, vec![t.clone(), r]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax;

    // the prelude, the read and the write in their pinned definitions, and
    // the terms of the cases as constants
    fn env() -> Env {
        let mut env = Env::new();
        syntax::load(&mut env, super::super::pinned::PRELUDE, true).expect("the prelude loads");
        let mut decls = String::new();
        for (n, ps, body) in super::super::pinned::PINNED_DEFS {
            if *n == "gimple.bytes_at" || *n == "x86_64_linux.store_le" {
                decls.push_str(&format!("def {}({}) := {}\n", n, ps.join(", "), body));
            }
        }
        decls.push_str("const M\nconst W\nconst X\nconst a\nconst b\nconst c\nconst d\nconst k\nconst v\n");
        syntax::load(&mut env, &decls, true).expect("the definitions load");
        env
    }

    fn read(env: &mut Env, premises: &[&str], t: &str) -> KResult<String> {
        let lg = Logic::new(env)?;
        let ps: Vec<Term> = premises.iter().map(|p| syntax::parse_term(env, p, &[]).unwrap()).collect();
        let t = syntax::parse_term(env, t, &[]).unwrap();
        let r = lg.mem_read(env, &ps, &t)?;
        let Node::App(_, s) = r.node() else { unreachable!() };
        Ok(syntax::Printer::new(env).term(&s[1]))
    }

    const RANGE: [&str; 4] = ["int_le(0, a)", "int_le(int_add(a, 2), b)", "int_le(0, b)", "int_le(int_add(b, 8), 18446744073709551616)"];

    #[test]
    fn writes_in_bytes_of_any_form() {
        let mut env = env();
        // a write on bytes not a memory's: the read is of those bytes
        let r = read(&mut env, &RANGE, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(X, a, 2, v)), b, 8)"#).unwrap();
        assert_eq!(r, r#"gimple.bytes_at(fn_update(M, "bytes", X), b, 8)"#);
        // on another memory's bytes: that memory's
        let r = read(&mut env, &RANGE, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(app(W, "bytes"), a, 2, v)), b, 8)"#).unwrap();
        assert_eq!(r, "gimple.bytes_at(W, b, 8)");
        // no write: nothing to resolve
        assert!(read(&mut env, &RANGE, r#"gimple.bytes_at(fn_update(M, "bytes", X), b, 8)"#).is_err());
    }

    #[test]
    fn past_the_apart_writes_up_to_an_undecided_one() {
        let mut env = env();
        // a apart from the read, c not decided: the read of the memory at c's write
        let ps = ["int_le(0, b)", "int_le(int_add(b, 8), 18446744073709551616)", "int_le(0, a)", "int_le(int_add(a, 8), b)", "int_le(0, c)", "int_le(int_add(c, 8), 18446744073709551616)"];
        let t = r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(x86_64_linux.store_le(X, c, 8, d), a, 8, v)), b, 8)"#;
        let r = read(&mut env, &ps, t).unwrap();
        assert_eq!(r, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(X, c, 8, d)), b, 8)"#);
        // the first write itself undecided: no step, an error
        let t1 = r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(X, c, 8, d)), b, 8)"#;
        assert!(read(&mut env, &ps, t1).is_err());
    }

    #[test]
    fn a_byte_through_writes() {
        let mut env = env();
        let ps = ["b in bits(64)", "int_le(0, a)", "int_le(int_add(a, 8), b)", "int_le(0, c)", "int_le(int_add(c, 8), 18446744073709551616)"];
        // past the apart write, then up to the undecided one
        let t = r#"app(app(fn_update(M, "bytes", x86_64_linux.store_le(x86_64_linux.store_le(X, c, 8, d), a, 8, v)), "bytes"), b)"#;
        assert_eq!(read(&mut env, &ps, t).unwrap(), r#"app(app(fn_update(M, "bytes", x86_64_linux.store_le(X, c, 8, d)), "bytes"), b)"#);
        // inside a write: its digit
        let pin = ["b in bits(64)", "int_le(0, a)", "int_le(a, b)", "int_lt(b, int_add(a, 8))", "int_le(int_add(a, 8), 18446744073709551616)"];
        let t2 = r#"app(app(fn_update(M, "bytes", x86_64_linux.store_le(X, a, 8, v)), "bytes"), b)"#;
        assert_eq!(read(&mut env, &pin, t2).unwrap(), "bits_of_int(8, int_div(v, int_pow(256, int_sub(b, a))))");
        // the address not in bits(64): no read
        let t3 = r#"app(app(fn_update(M, "bytes", x86_64_linux.store_le(X, a, 8, v)), "bytes"), k)"#;
        assert!(read(&mut env, &pin, t3).is_err());
    }

    #[test]
    fn a_read_of_any_size_past_apart_writes_only() {
        let mut env = env();
        let apart = ["int_le(0, b)", "int_le(0, k)", "int_le(int_add(b, k), a)", "int_le(int_add(a, 1), 18446744073709551616)"];
        let r = read(&mut env, &apart, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(app(M, "bytes"), a, 1, v)), b, k)"#).unwrap();
        assert_eq!(r, "gimple.bytes_at(M, b, k)");
        // a write it meets: its digits need the size
        let meets = ["int_le(0, b)", "int_le(1, k)", "a = b", "int_le(int_add(b, k), 18446744073709551616)"];
        assert!(read(&mut env, &meets, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(app(M, "bytes"), a, 1, v)), b, k)"#).is_err());
    }

    #[test]
    fn the_wide_choice_of_premises() {
        let mut env = env();
        // a + 2 <= c <= d <= b: c <= d mentions no term of the read or write
        let chain = ["int_le(0, a)", "int_le(int_add(a, 2), c)", "int_le(c, d)", "int_le(d, b)", "int_le(int_add(b, 8), 18446744073709551616)"];
        let r = read(&mut env, &chain, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(app(M, "bytes"), a, 2, v)), b, 8)"#).unwrap();
        assert_eq!(r, "gimple.bytes_at(M, b, 8)");
        // the write not apart: the same chain reversed proves nothing
        let back = ["int_le(0, b)", "int_le(b, c)", "int_le(c, d)", "int_le(d, a)", "int_le(int_add(a, 2), 18446744073709551616)", "int_le(a, int_add(b, 3))"];
        assert!(read(&mut env, &back, r#"gimple.bytes_at(fn_update(M, "bytes", x86_64_linux.store_le(app(M, "bytes"), a, 2, v)), b, 8)"#).is_err());
    }
}
