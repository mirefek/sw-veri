//! `slc translate`: the certificate of a function's C1 by statement patterns
//! (docs/bridge-pattern-design.md). Not trusted: it writes a proof that
//! `slc kernel-check` checks, with proofs/translate.core's rules.
//!
//! It walks the function's decode facts (`FN.at_ADDR`, build/leaf_steps.core)
//! from the entry, alongside the spec's procedure (`SPEC_fun`): each
//! instruction is the instance of the rule for its pattern, each spec
//! statement (a definition's body, a choice, a let, the result) the instance
//! of a reduction. The proof is the chain of instances, backwards from the
//! return; the side conditions are literal facts, proven by `simp(L)`.
//! Nothing is searched: an instruction without a rule, or a spec statement
//! that the machine's values do not match, stops it with an error.

use crate::commands::CResult;
use sl_kernel::syntax::{self, Printer};
use sl_kernel::{Env, Nat, Node, SymKind, Term, VarId};
use std::collections::{BTreeMap, BTreeSet};

const USAGE: &str = "usage: slc translate FN SPEC PREFIX -o OUT.core FILE.core...";
const P64: u128 = 1 << 64;

/// A decode fact: at `addr`, `len` bytes decode to `tag(row, fields)`.
struct Insn {
    name: String,
    len: u128,
    row: u128,
    fields: Term,
    base: Term,
    code: Term,
}

/// The spec's side at a point: the procedure's rest, or (after its result)
/// the wrapper's rest with the value returned.
enum Spec {
    Proc(usize),
    Ret(Term),
}

struct Gen<'e> {
    env: &'e mut Env,
    /// named values: the let's variable and its term (over earlier names)
    vals: Vec<(VarId, Term)>,
    /// the procedure's rests: name, term
    qs: Vec<(String, Term)>,
    /// the register maps after each write: name, register, bytes, value
    rs: Vec<(String, u128, u128, Term)>,
    /// the steps, in order: `have` text with `{NEXT}` for the next step's name
    steps: Vec<(String, String)>,
    /// sub-proofs to place before the steps
    pre: Vec<String>,
    /// top-level theorems (the immediates' products)
    thms: Vec<String>,
    imuls: BTreeSet<u128>,
    scratch: BTreeSet<u128>,
    // the fixed text of every rule instance
    base: String,
    code: String,
    prefix: String,
    kw: Term,
}

fn nat(t: &Term) -> Option<u128> {
    match t.node() {
        Node::Nat(n) => n.to_u128(),
        _ => None,
    }
}

fn lit(v: u128) -> Term {
    Term::nat(Nat::from_u128(v))
}

impl<'e> Gen<'e> {
    fn name(&self, t: &Term) -> Option<&str> {
        match t.node() {
            Node::App(s, _) => Some(&self.env.syms[*s as usize].name),
            _ => None,
        }
    }

    /// `t` as `NAME(args)`
    fn app<'t>(&self, t: &'t Term, name: &str, n: usize) -> Option<&'t [Term]> {
        match t.node() {
            Node::App(s, a) if self.env.syms[*s as usize].name == name && a.len() == n => Some(a),
            _ => None,
        }
    }

    fn mk(&self, name: &str, args: Vec<Term>) -> Term {
        Term::app(self.env.sym_by_name[name], args)
    }

    fn print(&self, t: &Term) -> String {
        Printer::new(self.env).term(t)
    }

    fn lambda(&self, k: usize, t: &Term) -> String {
        Printer::new(self.env).lambda(k, t)
    }

    /// `pair(a, pair(b, .. rest))` as its n components (the last the rest)
    fn pairs(&self, t: &Term, n: usize) -> Option<Vec<Term>> {
        let mut out = Vec::new();
        let mut t = t.clone();
        for _ in 1..n {
            let a = self.app(&t, "pair", 2)?;
            out.push(a[0].clone());
            t = a[1].clone();
        }
        out.push(t);
        Some(out)
    }

    /// `tag(k, x)` with the literal k
    fn tag(&self, t: &Term) -> Option<(u128, Term)> {
        let a = self.app(t, "tag", 2)?;
        Some((nat(&a[0])?, a[1].clone()))
    }

    /// a memory operand `tag(2, {seg, base, index, scale, disp})`: its fields
    fn memop(&self, t: &Term) -> Option<BTreeMap<String, Term>> {
        let (k, mut r) = self.tag(t)?;
        if k != 2 {
            return None;
        }
        let mut out = BTreeMap::new();
        while let Some(a) = self.app(&r, "fn_update", 3) {
            let Node::Bytes(b) = a[1].node() else { return None };
            out.entry(String::from_utf8(b.to_vec()).ok()?).or_insert(a[2].clone());
            r = a[0].clone();
        }
        self.app(&r, "empty", 0)?;
        Some(out)
    }

    /// `[rsp + d]`: the displacement
    fn rsp_mem(&self, t: &Term) -> Option<Term> {
        let m = self.memop(t)?;
        let base = self.tag(m.get("base")?)?;
        (nat(m.get("seg")?)? == 0 && base.0 == 2 && nat(&base.1)? == 4 && self.app(m.get("index")?, "none", 0).is_some() && nat(m.get("scale")?)? == 1)
            .then(|| m["disp"].clone())
    }

    /// The bound variables of `t` (at `depth`) renumbered by `f`; None if
    /// one has no image.
    fn remap(&self, t: &Term, depth: u32, f: &dyn Fn(u32) -> Option<u32>) -> Option<Term> {
        Some(match t.node() {
            Node::BVar(i) if *i >= depth => Term::bvar(f(i - depth)? + depth),
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => t.clone(),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.remap(x, depth, f)).collect::<Option<_>>()?),
            Node::App(s, a) => {
                let bs = &self.env.syms[*s as usize].binders;
                t.with_args(a.iter().zip(bs).map(|(x, &k)| self.remap(x, depth + k, f)).collect::<Option<_>>()?)
            }
        })
    }

    /// `t` with each subterm that is a named value replaced by its name
    fn canon(&self, t: &Term) -> Term {
        let t = match t.node() {
            Node::App(_, a) => t.with_args(a.iter().map(|x| self.canon(x)).collect()),
            Node::Var(_, a) => t.with_args(a.iter().map(|x| self.canon(x)).collect()),
            _ => t.clone(),
        };
        match self.vals.iter().find(|(_, e)| *e == t) {
            Some((v, _)) => Term::var(*v, vec![]),
            None => t,
        }
    }

    /// A value's name (a new one for a new value); literals, constants and
    /// names stand for themselves.
    fn value(&mut self, t: &Term) -> Term {
        let t = self.canon(t);
        match t.node() {
            Node::Nat(_) | Node::Var(..) => return t,
            Node::App(_, a) if a.is_empty() => return t,
            _ => {}
        }
        let v = self.env.new_var(&format!("T{}", self.vals.len()), 0);
        self.vals.push((v, t));
        Term::var(v, vec![])
    }

    fn new_q(&mut self, t: Term) -> usize {
        self.qs.push((format!("Q{}", self.qs.len()), t));
        self.qs.len() - 1
    }

    fn rs_name(&self) -> String {
        self.rs.last().map(|r| r.0.clone()).unwrap_or_else(|| "empty".into())
    }

    fn reg(&self, r: u128) -> Option<(u128, Term)> {
        self.rs.iter().rev().find(|x| x.1 == r).map(|x| (x.2, x.3.clone()))
    }

    fn set_reg(&mut self, r: u128, n: u128, v: Term) {
        self.rs.push((format!("R{}", self.rs.len() + 1), r, n, v));
    }

    fn need_reg(&self, r: u128, n: u128, what: &str) -> Result<Term, String> {
        match self.reg(r) {
            Some((m, v)) if m == n => Ok(v),
            Some((m, _)) => Err(format!("{}: register {} holds {} bytes, not {}", what, r, m, n)),
            None => Err(format!("{}: register {} holds no value of the procedure", what, r)),
        }
    }

    /// the spec's point claim's last two arguments
    fn p(&self, spec: &Spec) -> String {
        match spec {
            Spec::Proc(i) => format!("WRAP({})", self.qs[*i].0),
            Spec::Ret(_) => "PR".into(),
        }
    }

    fn step(&mut self, text: String) {
        let n = format!("p{}", self.steps.len());
        self.steps.push((n, text));
    }

    /// `tr.wred` instance header at `a`
    fn wred(&self, a: u128, q: usize, q2: usize) -> String {
        format!(
            "tr.wred[s := s, v := V, base := {}, code := {}, a := {}, hs := HS, rs := {}, w := W, q := {}, q2 := {}, kw := x0 x1 x2. KW(x0, x1, x2)]",
            self.base,
            self.code,
            a,
            self.rs_name(),
            self.qs[q].0,
            self.qs[q2].0
        )
    }

    /// The spec's statements before the next instruction: definitions'
    /// bodies, choices, lets, the result.
    fn reduce(&mut self, a: u128, mut spec: Spec) -> Result<Spec, String> {
        loop {
            let Spec::Proc(i) = spec else { return Ok(spec) };
            let q = self.qs[i].1.clone();
            // a procedure's definition: its body
            if let Node::App(f, args) = q.node() {
                if let SymKind::Defined { params, body } = &self.env.syms[*f as usize].kind {
                    if self.name(&q) != Some("mkprog") {
                        let fname = self.env.syms[*f as usize].name.clone();
                        let mut b = body.clone();
                        for (p, x) in params.clone().iter().zip(args.iter()) {
                            b = b.subst_var(*p, x, &self.env.binders_fn());
                        }
                        let b = self.canon(&b);
                        let j = self.new_q(b);
                        let u = format!("u{}", self.steps.len());
                        self.pre.push(format!(
                            "  have {}: all o. runs({}, W, o) -> runs({}, W, o) proof\n    fix o\n    assume h: runs({}, W, o)\n    show by defs(h, {})\n  qed",
                            u, self.qs[j].0, self.qs[i].0, self.qs[j].0, fname
                        ));
                        let t = format!("mp({}, {}, {{NEXT}})", self.wred(a, i, j), u);
                        self.step(t);
                        spec = Spec::Proc(j);
                        continue;
                    }
                }
            }
            let Some(m) = self.app(&q, "mkprog", 1) else { return Err(format!("the spec's rest is not a program: {}", self.print(&q))) };
            let body = m[0].clone();
            if let Some(x) = self.app(&body, "any_rel", 2) {
                // a choice: the witness 0 (of `x in bits(n)`)
                let d = self.remap(&x[0], 0, &|i| (i == 0).then_some(0)).ok_or("a choice whose domain depends on the state")?;
                let ok = self.app(&d, "in", 2).map_or(false, |a| matches!(a[0].node(), Node::BVar(0)) && self.app(&a[1], "bits", 1).is_some());
                if !ok {
                    return Err(format!("a choice from {}", self.lambda(1, &d)));
                }
                let q2 = self.mk("mkprog", vec![x[1].instantiate_params(&[Term::bvar(1), Term::bvar(0), lit(0)], &self.env.binders_fn())]);
                let j = self.new_q(q2);
                let t = format!(
                    "mp({}, mp(tr.q_any[c := 0, d := {}, b := {}], simp(), {{W}}), {{NEXT}})",
                    self.wred(a, i, j),
                    self.lambda(1, &d),
                    self.lambda(3, &x[1])
                );
                self.step(t);
                spec = Spec::Proc(j);
                continue;
            }
            if let Some(x) = self.app(&body, "letin", 2) {
                if x[0].loose_depth(&self.env.binders_fn()) > 0 {
                    return Err(format!("a let of the state: {}", self.lambda(2, &x[0])));
                }
                let e = self.value(&x[0]);
                let q2 = self.mk("mkprog", vec![x[1].instantiate_params(&[Term::bvar(1), Term::bvar(0), e.clone()], &self.env.binders_fn())]);
                let j = self.new_q(q2);
                let t = format!(
                    "mp({}, mp(tr.q_let[e := {}, b := {}], {{W}}), {{NEXT}})",
                    self.wred(a, i, j),
                    self.print(&e),
                    self.lambda(3, &x[1])
                );
                self.step(t);
                spec = Spec::Proc(j);
                continue;
            }
            // the result: `x1 = ok(x0, val)`
            if let Some(x) = self.app(&body, "eq", 2) {
                if let Some(o) = self.app(&x[1], "ok", 2) {
                    if matches!(x[0].node(), Node::BVar(0)) && matches!(o[0].node(), Node::BVar(1)) && o[1].loose_depth(&self.env.binders_fn()) == 0 {
                        let val = self.value(&o[1]);
                        let t = format!(
                            "mp(tr.wret[s := s, v := V, base := {}, code := {}, a := {}, hs := HS, rs := {}, w := W, val := {}, kw := x0 x1 x2. KW(x0, x1, x2)], simp(hvu), {{NEXT}})",
                            self.base,
                            self.code,
                            a,
                            self.rs_name(),
                            self.print(&val)
                        );
                        self.step(t);
                        return Ok(Spec::Ret(val));
                    }
                }
            }
            return Ok(spec);
        }
    }

    /// the instance's common head: `{s}, {V}, {base}, {code}, {a}, {a2}, {len}`
    fn head(&self, rule: &str, a: u128, insn: &Insn) -> String {
        format!("mp(tr.{}, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}", rule, self.base, self.code, a, (a + insn.len) % P64, insn.len)
    }

    /// the instance's tail: the vars after the operands, the decode fact,
    /// n literal facts, the extra premises, the next point
    fn tail(&self, spec: &Spec, insn: &Insn, n: usize, extra: &[String]) -> String {
        let mut t = format!(", {{HS}}, {{{}}}, {{{}}}, {{W}}, {}", self.rs_name(), self.p(spec), insn.name);
        for _ in 0..n {
            t.push_str(", simp(L)");
        }
        for e in extra {
            t.push_str(", ");
            t.push_str(e);
        }
        t.push_str(", {NEXT})");
        t
    }

    fn terms(&self, ts: &[&Term]) -> String {
        ts.iter().map(|t| format!(", {{{}}}", self.print(t))).collect()
    }

    /// The instruction at `a` (the spec at `spec` before it); the spec after.
    fn insn(&mut self, a: u128, insn: &Insn, spec: Spec, hs: &BTreeMap<u128, (u128, Term)>) -> Result<Spec, String> {
        let at = format!("{:x}", a);
        let fs = self.print(&insn.fields);
        let bad = |what: &str| format!("{:x}: {} (row {}): {}", a, what, insn.row, fs);
        let reg = |g: &Term| nat(g).ok_or_else(|| bad("a register that is not a literal"));
        let f = &insn.fields;
        let home = |d: &Term| -> Result<Term, String> {
            let d = nat(d).ok_or_else(|| bad("a displacement that is not a literal"))?;
            match hs.get(&d) {
                Some((4, x)) => Ok(x.clone()),
                _ => Err(format!("{}: no 4-byte home at rsp{:+}", at, d as i128 - if d >= P64 / 2 { P64 as i128 } else { 0 })),
            }
        };
        match insn.row {
            // mov r32, [rsp + d]: the home's value
            76 => {
                let x = self.pairs(f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&d)?;
                let t = self.head("load32_home", a, insn) + &self.terms(&[&x[1], &d, &x[3], &x[4], &v]) + &self.tail(&spec, insn, 7, &[]);
                self.step(t);
                self.scratch.insert(g);
                self.set_reg(g, 4, v);
            }
            // neg r32
            64 => {
                let x = self.pairs(f, 4).ok_or_else(|| bad("fields"))?;
                if nat(&x[1]) != Some(3) {
                    return Err(bad("unknown operation"));
                }
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 {
                    return Err(bad("neg of memory"));
                }
                let gn = reg(&g)?;
                let u = self.need_reg(gn, 4, &at)?;
                let t = self.head("neg32", a, insn) + &self.terms(&[&g, &x[3], &u]) + &self.tail(&spec, insn, 4, &[]);
                self.step(t);
                let r = self.mk("bits_sub", vec![lit(32), lit(0), u]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                self.set_reg(gn, 4, r);
            }
            // and r32, [rsp + d]: the home's value and the register's
            48 => {
                let x = self.pairs(f, 5).ok_or_else(|| bad("fields"))?;
                let d = self.rsp_mem(&x[2]).ok_or_else(|| bad("not a home"))?;
                let g = reg(&x[1])?;
                let v = home(&d)?;
                let u = self.need_reg(g, 4, &at)?;
                let t = self.head("and32_home", a, insn) + &self.terms(&[&x[1], &d, &x[3], &x[4], &v, &u]) + &self.tail(&spec, insn, 9, &[]);
                self.step(t);
                let r = self.mk("bits_and", vec![lit(32), v, u]);
                let r = self.value(&r);
                self.scratch.insert(g);
                self.set_reg(g, 4, r);
            }
            // imul r32, r32, imm
            89 => {
                let x = self.pairs(f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let (k, h) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 {
                    return Err(bad("imul of memory"));
                }
                let hn = reg(&h)?;
                let c = nat(&x[5]).ok_or_else(|| bad("an immediate that is not a literal"))?;
                if c >= 1 << 31 {
                    return Err(bad("a negative immediate (no product lemma yet)"));
                }
                let u = self.need_reg(hn, 4, &at)?;
                self.imuls.insert(c);
                let by = format!("{}.imul_{}", self.prefix, c);
                let t = self.head("imul32", a, insn) + &self.terms(&[&x[1], &h, &x[3], &x[4], &x[5], &u]) + &self.tail(&spec, insn, 4, &[by, "simp(L)".into(), "simp(L)".into()]);
                self.step(t);
                let r = self.mk("bits_mul", vec![lit(32), u, x[5].clone()]);
                let r = self.value(&r);
                self.scratch.insert(g);
                self.set_reg(g, 4, r);
            }
            // shr r32, imm
            72 => {
                let x = self.pairs(f, 5).ok_or_else(|| bad("fields"))?;
                if nat(&x[1]) != Some(5) {
                    return Err(bad("unknown operation"));
                }
                let (k, g) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                let c = nat(&x[4]).ok_or_else(|| bad("a count that is not a literal"))?;
                if k != 0 || c == 0 || c >= 32 {
                    return Err(bad("not shr r32, 1..31"));
                }
                let gn = reg(&g)?;
                let u = self.need_reg(gn, 4, &at)?;
                let t = self.head("shr32", a, insn) + &self.terms(&[&g, &x[3], &x[4], &u]) + &self.tail(&spec, insn, 7, &[]);
                self.step(t);
                let r = self.mk("bits_shr", vec![lit(32), u, x[4].clone()]);
                let r = self.value(&r);
                self.scratch.insert(gn);
                self.set_reg(gn, 4, r);
            }
            // mov r32, r32 (the store form: rm the destination)
            75 => {
                let x = self.pairs(f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let Some((0, h)) = self.tag(&x[2]) else { return Err(bad("a store (only the prologue's is matched)")) };
                let hn = reg(&h)?;
                let u = self.need_reg(g, 4, &at)?;
                let t = self.head("mov32_rr", a, insn) + &self.terms(&[&x[1], &h, &x[3], &x[4], &u]) + &self.tail(&spec, insn, 5, &[]);
                self.step(t);
                self.scratch.insert(hn);
                self.set_reg(hn, 4, u);
            }
            // lea r64, [rip + d]: a static's address
            78 => {
                let x = self.pairs(f, 6).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let mut m = BTreeMap::new();
                let mut r = x[5].clone();
                while let Some(u) = self.app(&r, "fn_update", 3) {
                    if let Node::Bytes(b) = u[1].node() {
                        m.entry(String::from_utf8_lossy(b).to_string()).or_insert(u[2].clone());
                    }
                    r = u[0].clone();
                }
                let d = m.get("disp").and_then(nat).ok_or_else(|| bad("not rip-relative"))?;
                if !m.get("base").map_or(false, |b| self.tag(b).map_or(false, |(k, _)| k == 1)) {
                    return Err(bad("not rip-relative"));
                }
                let a2 = (a + insn.len) % P64;
                let addr = (a2 + d) % P64;
                // the static whose address it is, when the spec names it
                let q = match &spec {
                    Spec::Proc(i) => self.qs[*i].1.clone(),
                    Spec::Ret(v) => v.clone(),
                };
                let mut found = None;
                self.statics(&q, addr, &mut found);
                let biga = found.unwrap_or_else(|| lit(addr));
                let t = self.head("lea_rip", a, insn) + &self.terms(&[&x[1], &lit(d), &x[2], &x[3], &x[4], &biga]) + &self.tail(&spec, insn, 4, &[]);
                self.step(t);
                self.scratch.insert(g);
                self.set_reg(g, 8, biga);
            }
            // movzx r32, byte [b + i]: the spec's ld8(elem(gg, u, 1))
            79 => {
                let x = self.pairs(f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let m = self.memop(&x[2]).ok_or_else(|| bad("fields"))?;
                let (bk, b) = self.tag(&m["base"]).ok_or_else(|| bad("fields"))?;
                let i = self.app(&m["index"], "some", 1).ok_or_else(|| bad("no index"))?[0].clone();
                if bk != 2 || nat(&m["disp"]) != Some(0) || nat(&m["scale"]) != Some(1) || x[3] != x[2] {
                    return Err(bad("not [b + i]"));
                }
                let (bn, iname) = (reg(&b)?, reg(&i)?);
                let u = self.need_reg(bn, 4, &at)?;
                let gg = self.need_reg(iname, 8, &at)?;
                let Spec::Proc(qi) = spec else { return Err(format!("{}: a load after the procedure's result", at)) };
                let q = self.qs[qi].1.clone();
                let shape = || -> Option<(Term, Term, Term)> {
                    let body = &self.app(&q, "mkprog", 1)?[0];
                    let b1 = self.app(body, "bind_rel", 5)?;
                    let el = self.app(&b1[0], "gimple.elem", 3)?;
                    (nat(&el[2])? == 1 && matches!(b1[1].node(), Node::BVar(1))).then_some(())?;
                    let b2 = self.app(&b1[2], "bind_rel", 5)?;
                    let ld = self.app(&b2[0], "gimple.ld8", 2)?;
                    (matches!(ld[0].node(), Node::BVar(0)) && nat(&ld[1])? == 0 && matches!(b2[1].node(), Node::BVar(1))).then_some(())?;
                    Some((el[0].clone(), el[1].clone(), b2[2].clone()))
                };
                let Some((sgg, su, k)) = shape() else { return Err(format!("{}: the spec is not at a byte load of an element: {}", at, self.print(&q))) };
                if self.canon(&sgg) != gg || self.canon(&su) != u {
                    return Err(format!("{}: the load's address is not the spec's: {} + {} against {} + {}", at, self.print(&gg), self.print(&u), self.print(&sgg), self.print(&su)));
                }
                // k(x10, x11, x1): its body under x0 x1 x8 x9 x10 x11
                let kl = self.remap(&k, 0, &|j| match j {
                    0 => Some(1),
                    1 => Some(2),
                    4 => Some(0),
                    _ => None,
                });
                let kl = kl.ok_or_else(|| format!("{}: the loaded byte's use reads the element's state", at))?;
                let wv = self.wvar();
                let vm = self.mk("app", vec![wv, Term::bytes(b"vm")]);
                let ad = self.mk("int_add", vec![gg.clone(), u.clone()]);
                let ba = self.mk("gimple.bytes_at", vec![vm, ad, lit(1)]);
                let by = self.mk("bits_of_int", vec![lit(8), ba]);
                let by = self.value(&by);
                let q2 = self.mk("mkprog", vec![kl.instantiate_params(&[Term::bvar(1), by.clone(), Term::bvar(0)], &self.env.binders_fn())]);
                let j = self.new_q(q2);
                let mut t = format!(
                    "mp(tr.ld8_elem[s := s, v := V, base := {}, code := {}, a := {}, a2 := {}, len := {}, g := {}, b := {}, i := {}, z2 := {}, gg := {}, u := {}, hs := HS, rs := {}, w := W, k := {}, kw := x0 x1 x2. KW(x0, x1, x2)], {}",
                    self.base,
                    self.code,
                    a,
                    (a + insn.len) % P64,
                    insn.len,
                    g,
                    bn,
                    iname,
                    self.print(&x[4]),
                    self.print(&gg),
                    self.print(&u),
                    self.rs_name(),
                    self.lambda(3, &kl),
                    insn.name
                );
                for _ in 0..12 {
                    t.push_str(", simp(L)");
                }
                t.push_str(", hvu, {NEXT})");
                self.step(t);
                self.scratch.insert(g);
                self.set_reg(g, 1, by);
                return Ok(Spec::Proc(j));
            }
            // movsx r32, r8
            81 => {
                let x = self.pairs(f, 5).ok_or_else(|| bad("fields"))?;
                let g = reg(&x[1])?;
                let (k, h) = self.tag(&x[2]).ok_or_else(|| bad("fields"))?;
                if k != 0 || x[3] != x[2] {
                    return Err(bad("not movsx r32, r8"));
                }
                let hn = reg(&h)?;
                if hn >= 4 {
                    return Err(bad("a high byte register"));
                }
                let b = self.need_reg(hn, 1, &at)?;
                let t = self.head("movsx8", a, insn) + &self.terms(&[&x[1], &h, &x[4], &b]) + &self.tail(&spec, insn, 6, &[]);
                self.step(t);
                let r = self.mk("bits_sext", vec![lit(8), lit(32), b]);
                let r = self.value(&r);
                self.scratch.insert(g);
                self.set_reg(g, 4, r);
            }
            _ => return Err(bad("no rule for the instruction")),
        }
        Ok(spec)
    }

    fn wvar(&self) -> Term {
        let v = self.env.vars.iter().rposition(|x| x.name == "W").unwrap() as VarId;
        Term::var(v, vec![])
    }

    /// nullary defined constants of `t` whose value is `addr`
    fn statics(&self, t: &Term, addr: u128, found: &mut Option<Term>) {
        match t.node() {
            Node::App(s, a) => {
                if a.is_empty() {
                    if let SymKind::Defined { params, body } = &self.env.syms[*s as usize].kind {
                        if params.is_empty() && nat(body) == Some(addr) {
                            *found = Some(t.clone());
                        }
                    }
                }
                a.iter().for_each(|x| self.statics(x, addr, found));
            }
            Node::Var(_, a) => a.iter().for_each(|x| self.statics(x, addr, found)),
            _ => {}
        }
    }
}

/// The files' statements: a theorem becomes a claim (its statement), a
/// schematic one is left out -- the generator reads statements only, and
/// checks nothing.
fn statements(src: &str) -> String {
    let code = |l: &str| l.split("//").next().unwrap_or("").trim().to_string();
    let mut out = String::new();
    let mut lines = src.split_inclusive('\n');
    while let Some(l) = lines.next() {
        let Some(rest) = l.strip_prefix("theorem ") else {
            out.push_str(l);
            continue;
        };
        let schematic = rest.find(|c: char| c == ':' || c == '(').map_or(false, |i| rest[i..].starts_with('('));
        // the statement runs to the line `proof`
        let mut head = format!("claim {}", rest);
        loop {
            let Some(n) = lines.next() else { break };
            if code(n) == "proof" {
                break;
            }
            head.push_str(n);
        }
        let mut nest = 1;
        while nest > 0 {
            let Some(n) = lines.next() else { break };
            let t = code(n);
            if t == "qed" {
                nest -= 1;
            } else if t == "proof" || t.ends_with(" proof") {
                nest += 1;
            }
        }
        if !schematic {
            out.push_str(&head);
        }
    }
    out
}

pub fn translate(args: &[String]) -> CResult {
    let mut out_path = None;
    let mut pos = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "-o" {
            out_path = it.next().cloned();
        } else {
            pos.push(a.clone());
        }
    }
    let (Some(out_path), true) = (out_path, pos.len() >= 4) else { return Err(USAGE.into()) };
    let (fname, spec_name, prefix) = (pos[0].clone(), pos[1].clone(), pos[2].clone());
    let mut env = Env::new();
    for (i, f) in pos[3..].iter().enumerate() {
        let src = std::fs::read_to_string(f).map_err(|e| format!("{}: {}", f, e))?;
        syntax::load(&mut env, &statements(&src), i == 0).map_err(|e| format!("{}: {}", f, e))?;
    }

    // the decode facts
    let mut insns: BTreeMap<u128, Insn> = BTreeMap::new();
    let pre = format!("{}.at_", fname);
    for (name, t) in env.claims.clone() {
        if !name.starts_with(&pre) {
            continue;
        }
        let g = Gen0(&env);
        let parsed = (|| -> Option<(u128, Insn)> {
            let t = &g.app(t.clone(), "all")?;
            let t = &g.app(t.clone(), "all")?;
            let i1 = g.imp(t)?;
            let i2 = g.imp(&i1.1)?;
            let i3 = g.imp(&i2.1)?;
            let ca = g.args(&i2.0, "abi.code_at")?;
            let rip = g.args(&i3.0, "eq")?;
            let ex = g.args(&g.args(&i3.1, "runs")?[0], "x86_64_linux.exec_body")?;
            let tg = g.args(&ex[1], "tag")?;
            Some((
                nat(&rip[1])?,
                Insn { name: name.clone(), len: nat(&ex[0])?, row: nat(&tg[0])?, fields: tg[1].clone(), base: ca[1].clone(), code: ca[2].clone() },
            ))
        })();
        let (a, insn) = parsed.ok_or_else(|| format!("{}: not a decode fact", name))?;
        insns.insert(a, insn);
    }
    let (&entry, first) = insns.iter().next().ok_or_else(|| format!("no decode facts `{}*`", pre))?;
    let (base_t, code_t) = (first.base.clone(), first.code.clone());
    if nat(&base_t) != Some(entry) {
        return Err(format!("the first decode fact is at {:x}, not the base", entry));
    }

    // the spec: fn_build(D, x0. mkprog(x1 x2. !ord_le(1, seq_len(x0)) || bind_rel(PROC, x1, KW, EXC, DIV)))
    let ssym = *env.sym_by_name.get(&spec_name).ok_or_else(|| format!("no spec `{}`", spec_name))?;
    let SymKind::Defined { body: sbody, .. } = env.syms[ssym as usize].kind.clone() else { return Err(format!("`{}` is not a definition", spec_name)) };
    let args_v = env.new_var("args", 0);
    let s_v = env.new_var("s", 0);
    let w_v = env.new_var("W", 0);
    let q_v = env.new_var("q", 0);
    let mut g = Gen {
        env: &mut env,
        vals: Vec::new(),
        qs: Vec::new(),
        rs: Vec::new(),
        steps: Vec::new(),
        pre: Vec::new(),
        thms: Vec::new(),
        imuls: BTreeSet::new(),
        scratch: BTreeSet::new(),
        base: String::new(),
        code: String::new(),
        prefix: prefix.clone(),
        kw: Term::bvar(0),
    };
    g.base = g.print(&base_t);
    g.code = g.print(&code_t);
    let _ = w_v;
    let parts = (|| -> Option<(Term, Term, Term, Term)> {
        let fb = g.app(&sbody, "fn_build", 2)?;
        let mp = g.app(&fb[1], "mkprog", 1)?;
        let or = g.app(&mp[0], "or", 2)?;
        let guard = g.app(&or[0], "not", 1)?;
        let le = g.app(&guard[0], "ord_le", 2)?;
        (nat(&le[0])? == 1).then_some(())?;
        let br = g.app(&or[1], "bind_rel", 5)?;
        matches!(br[1].node(), Node::BVar(1)).then_some(())?;
        // PROC(x0); KW(x3, x4, x2); the wrapper without x0
        let proc = g.remap(&br[0], 0, &|i| (i == 2).then_some(0))?;
        let kw = g.remap(&br[2], 0, &|i| match i {
            0 => Some(1),
            1 => Some(2),
            2 => Some(0),
            _ => None,
        })?;
        let bs = g.env.syms[g.env.sym_by_name["bind_rel"] as usize].binders.clone();
        let rest: Vec<Term> = br[1..].iter().zip(&bs[1..]).map(|(x, &k)| g.remap(x, k, &|i| (i < 2).then_some(i))).collect::<Option<_>>()?;
        let mut wa = vec![Term::var(q_v, vec![])];
        wa.extend(rest);
        let wrap = g.mk("mkprog", vec![g.mk("bind_rel", wa)]);
        Some((proc, kw, wrap, br[2].clone()))
    })();
    let (proc, kw, wrap, _) = parts.ok_or_else(|| format!("`{}`: not a one-argument procedure's spec", spec_name))?;
    g.kw = kw.clone();

    // the entry: mov [rsp + d], edi
    let e0 = &insns[&entry];
    let ef = g.pairs(&e0.fields, 5).ok_or("the entry's fields")?;
    let d = match (e0.row, nat(&ef[0]), nat(&ef[1]), g.rsp_mem(&ef[2])) {
        (75, Some(4), Some(7), Some(d)) => d,
        _ => return Err(format!("the entry {:x} is not `mov [rsp + d], edi`", entry)),
    };
    let dn = nat(&d).ok_or("the entry's displacement")?;
    let a2 = (entry + e0.len) % P64;
    let bf = g.env.binders_fn();
    let args_t = Term::var(args_v, vec![]);
    let x = g.mk("bits_of_int", vec![lit(32), g.mk("app", vec![args_t.clone(), lit(0)])]);
    let q0raw = proc.instantiate_params(&[args_t.clone()], &bf);
    drop(bf);
    let wrap_q0 = wrap.subst_var(q_v, &q0raw, &g.env.binders_fn());
    let xn = g.value(&x);
    let mut hs = BTreeMap::new();
    hs.insert(dn, (4u128, xn.clone()));
    let q0 = g.canon(&q0raw);
    let i0 = g.new_q(q0);

    // the walk
    let mut a = a2;
    let mut spec = Spec::Proc(i0);
    let ret_val;
    loop {
        spec = g.reduce(a, spec)?;
        let insn = insns.get(&a).ok_or_else(|| format!("no decode fact at {:x}", a))?;
        if insn.row == 122 {
            let Spec::Ret(val) = &spec else { return Err(format!("{:x}: ret before the procedure's result", a)) };
            let v = g.need_reg(0, 4, &format!("{:x}", a))?;
            if &v != val {
                return Err(format!("{:x}: eax holds {}, the spec returns {}", a, g.print(&v), g.print(val)));
            }
            let t = format!(
                "mp(tr.ret_insn, {{s}}, {{V}}, {{{}}}, {{{}}}, {{{}}}, {{{}}}, {{HS}}, {{{}}}, {{PR}}, {{W}}, {{4}}, {{{}}}, {}, simp(L), simp(L), mp(tr.result32, {{W}}, {{{}}}))",
                g.base,
                g.code,
                a,
                insn.len,
                g.rs_name(),
                g.print(val),
                insn.name,
                g.print(val)
            );
            g.step(t);
            ret_val = Some(val.clone());
            break;
        }
        spec = g.insn(a, insn, spec, &hs)?;
        a = (a + insn.len) % P64;
    }

    // the text
    let pr = |g: &Gen, t: &Term| g.print(t);
    let mut o = String::new();
    o.push_str(&format!(
        "// {}'s C1 by translation (docs/bridge-pattern-design.md). Generated by\n//   slc translate {} {} {} -o OUT.core FILES (the spec's and the decode facts' files)\n// Each step: a rule of proofs/translate.core with its instance, the decode\n// fact (build/leaf_steps.core), literal facts (simp(L)), the next point.\n// Checked after proofs/translate.core.\n\n",
        fname, fname, spec_name, prefix
    ));
    let view = format!("tr.view1(s, {}, 4, bits_slice(app(app(s, \"gpr\"), 7), 31, 0))", dn);
    o.push_str(&format!("abbrev {p}.v(s) := {}\nabbrev {p}.w(s) := abi.view({p}.v(s), s)\n\n", view, p = prefix));
    for c in g.imuls.clone() {
        let t = format!(
            "theorem {p}.imul_{c}: tr.imul_by({c})\nproof\n  have g: all y. y in bits(32) -> bits_add(32, int_mul(sint(32, y), sint(32, {c})), 0) = bits_mul(32, y, {c}) proof\n    fix y\n    assume hy: y in bits(32)\n    have c1: int_lt(y, 2147483648) -> bits_add(32, int_mul(sint(32, y), {c}), 0) = bits_mul(32, y, {c}) proof\n      assume hl: int_lt(y, 2147483648)\n      show by defs(simp(hy, hl), bits_add, bits_mul, sint)\n    qed\n    have c2: !int_lt(y, 2147483648) -> bits_add(32, int_mul(sint(32, y), {c}), 0) = bits_mul(32, y, {c}) proof\n      assume hl: !int_lt(y, 2147483648)\n      have e: int_mod(int_mul(int_sub(y, 4294967296), {c}), 4294967296) = int_mod(int_mul(y, {c}), 4294967296) by arith(hy)\n      show by defs(simp(hy, hl, e), bits_add, bits_mul, sint)\n    qed\n    have e: bits_add(32, int_mul(sint(32, y), {c}), 0) = bits_mul(32, y, {c}) by taut(c1, c2)\n    show by simp(e)\n  qed\n  show by defs(g, tr.imul_by)\nqed\n\n",
            p = prefix,
            c = c
        );
        g.thms.push(t);
    }
    for t in &g.thms {
        o.push_str(t);
    }
    let p = &prefix;
    let wrap_s = pr(&g, &wrap_q0);
    o.push_str(&format!(
        "theorem {p}.body: all args s. args in abi.ARGS -> s in x86_64_linux.Machine -> ord_le(1, seq_len(args)) -> {p}.w(s) in univ(1) ->\n  tr.pt(s, {p}.v(s), {}, {}, {}, fn_update(empty, {}, pair(4, bits_of_int(32, app(args, 0)))), empty,\n    {}, {p}.w(s))\nproof\n",
        g.base, g.code, a2, dn, wrap_s
    ));
    o.push_str("  fix args\n  fix s\n  assume hA: args in abi.ARGS\n  assume hM: s in x86_64_linux.Machine\n  assume hg: ord_le(1, seq_len(args))\n");
    o.push_str(&format!("  assume hvu: {p}.w(s) in univ(1)\n"));
    let mut l = vec!["tr.dom_upd".to_string(), "tr.dom_keep".to_string()];
    let mut lt = vec!["(all f k v. k in dom(fn_update(f, k, v)))".to_string(), "(all f k j v. k in dom(f) -> !(k = j) -> k in dom(fn_update(f, j, v)))".to_string()];
    for r in &g.scratch {
        o.push_str(&format!("  have sc{r}: tr.scratch_reg({r}) by defs(simp(), tr.scratch_reg)\n"));
        l.push(format!("sc{}", r));
        lt.push(format!("tr.scratch_reg({})", r));
    }
    o.push_str(&format!("  // the literal facts: a map's keys, the registers written\n  have L: {} by taut({})\n", lt.join(" && "), l.join(", ")));
    let kwl = g.lambda(3, &g.kw);
    let kwb = kwl.split_once(". ").map(|x| x.1.to_string()).unwrap_or(kwl.clone());
    o.push_str(&format!("  // the wrapper: the procedure's rest q, its result returned\n  let KW(x0, x1, x2) := {}\n", kwb));
    let wl = g.print(&wrap);
    o.push_str(&format!("  let WRAP(q) := {}\n", wl));
    o.push_str(&format!("  let V := {p}.v(s)\n  let W := {p}.w(s)\n"));
    o.push_str("  // the values\n");
    for (v, t) in &g.vals {
        o.push_str(&format!("  let {} := {}\n", g.env.vars[*v as usize].name, g.print(t)));
    }
    o.push_str(&format!("  let HS := fn_update(empty, {}, pair(4, {}))\n", dn, g.print(&xn)));
    o.push_str("  // the registers after each write\n");
    let mut prev = "empty".to_string();
    for (n, r, b, v) in &g.rs {
        o.push_str(&format!("  let {} := fn_update({}, {}, pair({}, {}))\n", n, prev, r, b, g.print(v)));
        prev = n.clone();
    }
    o.push_str("  // the procedure's rest at each point\n");
    for (n, t) in &g.qs {
        o.push_str(&format!("  let {} := {}\n", n, g.print(t)));
    }
    if let Some(v) = &ret_val {
        o.push_str(&format!("  let PR := {}\n", g.print(&g.mk("mkprog", vec![g.kw.instantiate_params(&[Term::bvar(1), v.clone(), Term::bvar(0)], &g.env.binders_fn())]))));
    }
    for t in &g.pre {
        o.push_str(t);
        o.push('\n');
    }
    o.push_str("  // the steps, from the return back\n");
    let n = g.steps.len();
    for k in (0..n).rev() {
        let (name, t) = &g.steps[k];
        let t = match g.steps.get(k + 1) {
            Some((next, _)) => t.replace("{NEXT}", next),
            None => t.clone(),
        };
        if k == 0 {
            o.push_str(&format!("  show := {}\n", t));
        } else {
            o.push_str(&format!("  have {} := {}\n", name, t));
        }
    }
    o.push_str("qed\n\n");
    let ql = g.lambda(1, &proc);
    let at0 = &insns[&entry].name;
    o.push_str(&format!(
        "theorem {p}.implements: all statics. abi.implements2_at(single(empty), {b}, {spec}(), {b}, {c}, statics)\nproof\n  fix statics\n  have m0 := mp(tr.entry1_32[base := {b}, code := {c}, statics := statics, f := {b}, len := {len}, d := {d}, z1 := {z1}, z2 := {z2}, a2 := {a2},\n    q := {ql}, kw := {kwl}],\n    simp(), {at0}, simp(), simp(), simp(), simp(), {p}.body)\n",
        b = g.base,
        c = g.code,
        spec = spec_name,
        len = e0.len,
        d = dn,
        z1 = g.print(&ef[3]),
        z2 = g.print(&ef[4]),
        a2 = a2,
    ));
    o.push_str(&format!(
        "  have m: all args s o. args in abi.ARGS -> s in x86_64_linux.Machine -> abi.loaded(app(s, \"vm\"), {b}, {c}, statics) -> app(s, \"rip\") = {b} ->\n      abi.entry_ok(s, args) -> runs(abi.run_to_return(), s, o) -> abi.matches({spec}(), args, s, o) by defs(m0, {spec})\n  show := apply(abi.bridge_implements, m)\nqed\n",
        b = g.base,
        c = g.code,
        spec = spec_name
    ));
    let _ = s_v;
    std::fs::write(&out_path, o).map_err(|e| format!("{}: {}", out_path, e))?;
    println!("{}: {} steps, {} values", out_path, n, g.vals.len());
    Ok(())
}

/// statement access before the generator's state exists
struct Gen0<'e>(&'e Env);

impl Gen0<'_> {
    fn args(&self, t: &Term, name: &str) -> Option<Vec<Term>> {
        match t.node() {
            Node::App(s, a) if self.0.syms[*s as usize].name == name => Some(a.to_vec()),
            _ => None,
        }
    }
    fn app(&self, t: Term, name: &str) -> Option<Term> {
        self.args(&t, name).map(|a| a[0].clone())
    }
    fn imp(&self, t: &Term) -> Option<(Term, Term)> {
        match t.node() {
            Node::App(s, a) if *s == self.0.builtins.imp => Some((a[0].clone(), a[1].clone())),
            _ => None,
        }
    }
}
