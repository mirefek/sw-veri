//! Memory reads through writes: `mem_read`.
//!
//! Trusted extension. A read of m bytes at b of a memory M,
//! `gimple.bytes_at(M, b, m)` (the sum of `app(app(M, "bytes"), bits_add(64,
//! b, bits_of_int(64, i))) * 256^i` for i < m), where M is built by writes
//! `fn_update(M', "bytes", x86_64_linux.store_le(app(M', "bytes"), a, n, v))`
//! (the byte at y: `bits_of_int(8, int_div(v, 256^(y - a)))` if `bits_sub(64,
//! y, a) < n`, else M''s) and updates of other fields
//! `fn_update(M', k, x)` (k a string other than "bytes"), is resolved by
//! walking M from the outside in. m and each n are numerals; the facts
//! (premises) must give, by `arith`, the read's and each write's range in
//! the address space -- `0 <= b`, `b + m <= 2^64` (likewise a, n) -- so that
//! the addresses `bits_add` / `bits_sub` form are the integer ones. For each
//! write, in this order:
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
//! else the walk stops with an error naming the write. A memory of another
//! form ends the walk: the read is then `gimple.bytes_at` of that memory.
//! The facts given to each `arith` check are the premises mentioning one of
//! its terms (a choice of premises, so sound however it is made).
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
/// arith reads them)
fn names(t: &Term, arith: &[crate::term::SymId], out: &mut Vec<Term>) {
    match t.node() {
        Node::App(f, a) if arith.contains(f) => {
            for x in a.iter() {
                names(x, arith, out);
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
    /// the premises (their positions) mentioning a term of the goal, as
    /// `arith` reads terms: its maximal subterms not headed by an arithmetic
    /// or propositional symbol
    pub fn arith_relevant(&self, env: &Env, premises: &[Term], goal: &Term) -> Vec<usize> {
        let arith_syms: Vec<_> = [
            "int_add", "int_sub", "int_mul", "int_div", "int_mod", "int_pow", "pow2", "int_le", "int_lt", "bits_add", "bits_sub", "bits_of_int", "bits",
            "omega", "not", "and", "or",
        ]
        .iter()
        .filter_map(|n| env.sym_by_name.get(*n).copied())
        .chain([env.builtins.eq, env.builtins.imp, self.in_])
        .collect();
        let mut gn = Vec::new();
        names(goal, &arith_syms, &mut gn);
        (0..premises.len())
            .filter(|&i| {
                let mut pn = Vec::new();
                names(&premises[i], &arith_syms, &mut pn);
                pn.iter().any(|x| gn.contains(x))
            })
            .collect()
    }

    /// `t = r`, t = `gimple.bytes_at(M, b, m)` resolved through M's writes
    /// (see the module docs).
    pub fn mem_read(&self, env: &Env, premises: &[Term], t: &Term) -> KResult<Term> {
        let g = |n: &str| env.sym_by_name.get(n).copied();
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
        let (mut m_t, b, m) = match t.node() {
            Node::App(f, a) if *f == bytes_at && a.len() == 3 => (a[0].clone(), a[1].clone(), a[2].clone()),
            _ => return err(format!("mem_read: not `gimple.bytes_at(M, b, m)`: {}", pr.short(t))),
        };
        let mn = numeral(&m).ok_or_else(|| KernelError("mem_read: the read's size is not a numeral".into()))?;
        let nat = |v: u128| Term::nat(Nat::from_u128(v));
        let two64 = nat(1u128 << 64);
        let zero = nat(0);
        let le = |x: Term, y: Term| Term::app(int_le, vec![x, y]);
        let add = |x: Term, y: Term| Term::app(int_add, vec![x, y]);
        let conj = |x: Term, y: Term| Term::app(and, vec![x, y]);
        let in_range = |a: &Term, n: &Term| conj(le(zero.clone(), a.clone()), le(add(a.clone(), n.clone()), two64.clone()));
        // (each goal from the premises about its terms)
        let holds = |goal: &Term| {
            let rel: Vec<Term> = self.arith_relevant(env, premises, goal).into_iter().map(|i| premises[i].clone()).collect();
            self.arith(env, &rel, goal).is_ok()
        };
        if !holds(&in_range(&b, &m)) {
            return err(format!("mem_read: the read's range not shown in the address space: 0 <= {0}, {0} + {1} <= 2^64", pr.short(&b), mn));
        }
        let mut steps = 0;
        while let Node::App(f, a) = m_t.node() {
            if *f != fn_update || a.len() != 3 {
                break;
            }
            let (inner, key, x) = (&a[0], &a[1], &a[2]);
            match key.node() {
                Node::Bytes(k) if &**k == b"bytes" => {}
                // (another field: the bytes are the inner memory's)
                Node::Bytes(_) => {
                    m_t = inner.clone();
                    steps += 1;
                    continue;
                }
                _ => break,
            }
            // fn_update(inner, "bytes", store_le(app(inner, "bytes"), wa, wn, v))
            let Node::App(s, sa) = x.node() else { break };
            if *s != store_le || sa.len() != 4 {
                break;
            }
            let base_ok = matches!(sa[0].node(), Node::App(f2, b2) if *f2 == app && b2.len() == 2 && b2[0] == *inner
                && matches!(b2[1].node(), Node::Bytes(k) if &**k == b"bytes"));
            if !base_ok {
                break;
            }
            let (wa, wn_t, v) = (sa[1].clone(), sa[2].clone(), sa[3].clone());
            let Some(wn) = numeral(&wn_t) else {
                return err(format!("mem_read: a write of a size not a numeral: {}", pr.short(x)));
            };
            if !holds(&in_range(&wa, &wn_t)) {
                return err(format!("mem_read: a write's range not shown in the address space: 0 <= {0}, {0} + {1} <= 2^64", pr.short(&wa), wn));
            }
            steps += 1;
            // apart: past it
            let apart = Term::app(or, vec![le(add(wa.clone(), wn_t.clone()), b.clone()), le(add(b.clone(), m.clone()), wa.clone())]);
            if holds(&apart) {
                m_t = inner.clone();
                continue;
            }
            let pow = |e: Term| Term::app(int_pow, vec![nat(256), e]);
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
            return err(format!(
                "mem_read: the read of {} bytes at {} and the write of {} bytes at {}: not shown apart, the same, or the read inside the write",
                mn,
                pr.short(&b),
                wn,
                pr.short(&wa)
            ));
        }
        if steps == 0 {
            return err(format!("mem_read: no write to read through in {}", pr.short(&m_t)));
        }
        let r = Term::app(bytes_at, vec![m_t, b, m]);
        Ok(Term::app(env.builtins.eq, vec![t.clone(), r]))
    }
}
