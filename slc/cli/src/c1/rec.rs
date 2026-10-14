//! Proof recipes: what a step proves with, as data (a rule and its
//! arguments), evaluated by the proof checker's rules (`sl_proof::api`)
//! into kernel sequents. No proof text: the engine builds these directly.

use super::Gen;
use sl_kernel::ext::seq::Seq;
use sl_kernel::syntax::Printer;
use sl_kernel::{Nat, Node, Term, VarId};
use sl_proof::api::{A, G};

/// A proof.
#[derive(Clone)]
pub enum R {
    /// proven already
    S(Seq),
    /// a theorem by name
    F(String),
    /// a theorem's schematic variables (or leading `all`s) by name
    Inst(String, Vec<(&'static str, Term)>),
    /// `mp(r, a..)`
    Mp(Box<R>, Vec<RA>),
    /// `apply(r, a..)`
    Apply(Box<R>, Vec<RA>),
    /// `expand(r, D..)`
    Expand(Box<R>, Vec<String>),
    /// a fact given later (a condition's proof): its slot
    Slot(&'static str),
}

/// An argument of `mp` / `apply`: a term, or a premise's justification.
#[derive(Clone)]
pub enum RA {
    T(Term),
    P(RP),
}

/// A justification of a goal.
#[derive(Clone)]
pub enum RP {
    By(R),
    /// simp: with the literal facts (`L`) if `.0`, the facts, programs kept
    /// folded, loops unrolled
    Simp(bool, Vec<R>, Vec<String>, bool),
    Taut(Vec<R>),
    Arith(Vec<R>),
    /// bitwise at the width (a word equation bit by bit)
    Bitwise(Vec<R>, u128),
    Defs(Box<RP>, Vec<String>),
    Mp(R, Vec<RA>),
}

/// the facts the slots stand for
pub type Slots<'a> = &'a [(&'static str, Seq)];

/// `r` with its slot `name` the recipe `with` (a step whose next point is
/// another step's)
pub fn fill(r: R, name: &str, with: &R) -> R {
    fn fa(a: RA, name: &str, with: &R) -> RA {
        match a {
            RA::T(x) => RA::T(x),
            RA::P(rp) => RA::P(fp(rp, name, with)),
        }
    }
    fn fp(rp: RP, name: &str, with: &R) -> RP {
        match rp {
            RP::By(r) => RP::By(fill(r, name, with)),
            RP::Simp(l, rs, k, u) => RP::Simp(l, rs.into_iter().map(|r| fill(r, name, with)).collect(), k, u),
            RP::Taut(rs) => RP::Taut(rs.into_iter().map(|r| fill(r, name, with)).collect()),
            RP::Arith(rs) => RP::Arith(rs.into_iter().map(|r| fill(r, name, with)).collect()),
            RP::Bitwise(rs, n) => RP::Bitwise(rs.into_iter().map(|r| fill(r, name, with)).collect(), n),
            RP::Defs(i, n) => RP::Defs(Box::new(fp(*i, name, with)), n),
            RP::Mp(r, a) => RP::Mp(fill(r, name, with), a.into_iter().map(|x| fa(x, name, with)).collect()),
        }
    }
    match r {
        R::Slot(n) if n == name => with.clone(),
        R::Mp(h, a) => R::Mp(Box::new(fill(*h, name, with)), a.into_iter().map(|x| fa(x, name, with)).collect()),
        R::Apply(h, a) => R::Apply(Box::new(fill(*h, name, with)), a.into_iter().map(|x| fa(x, name, with)).collect()),
        R::Expand(h, n) => R::Expand(Box::new(fill(*h, name, with)), n),
        other => other,
    }
}

// (constructors)
pub fn f(name: &str) -> R {
    R::F(name.to_string())
}
pub fn mp(r: R, args: Vec<RA>) -> R {
    R::Mp(Box::new(r), args)
}
pub fn mpf(name: &str, args: Vec<RA>) -> R {
    mp(f(name), args)
}
pub fn t(x: &Term) -> RA {
    RA::T(x.clone())
}
pub fn p(r: R) -> RA {
    RA::P(RP::By(r))
}
pub fn s(x: &Seq) -> RA {
    RA::P(RP::By(R::S(x.clone())))
}
/// `simp(L)`
pub fn simp_l() -> RA {
    RA::P(RP::Simp(true, Vec::new(), Vec::new(), false))
}
/// `simp(L, r..)`
pub fn simp_lw(rs: Vec<R>) -> RA {
    RA::P(RP::Simp(true, rs, Vec::new(), false))
}
/// `simp()`
pub fn simp0() -> RA {
    RA::P(RP::Simp(false, Vec::new(), Vec::new(), false))
}
/// `simp(r..)`
pub fn simpw(rs: Vec<R>) -> RA {
    RA::P(RP::Simp(false, rs, Vec::new(), false))
}
pub fn taut(rs: Vec<R>) -> RA {
    RA::P(RP::Taut(rs))
}
pub fn arith(rs: Vec<R>) -> RA {
    RA::P(RP::Arith(rs))
}
pub fn defs(rp: RP, names: &[&str]) -> RA {
    RA::P(RP::Defs(Box::new(rp), names.iter().map(|n| n.to_string()).collect()))
}

impl<'e> Gen<'e> {
    /// the symbols named
    fn syms(&self, names: &[String]) -> Result<Vec<u32>, String> {
        names.iter().map(|n| self.env.sym_by_name.get(n.as_str()).copied().ok_or_else(|| format!("no definition `{}`", n))).collect()
    }

    /// `r` evaluated: a sequent
    pub fn ev(&mut self, r: &R, slots: Slots) -> Result<Seq, String> {
        let api = self.api.take().expect("the proving context");
        let res = self.ev_in(&api, r, slots);
        self.api = Some(api);
        res
    }

    /// `rp` evaluated against `goal`
    pub fn evp(&mut self, rp: &RP, goal: &Term, slots: Slots) -> Result<Seq, String> {
        let api = self.api.take().expect("the proving context");
        let g = self.expand(goal);
        let t0 = std::time::Instant::now();
        let _p = super::prof::g("evp");
        let res = self.g_of(&api, rp, slots).and_then(|g2| api.by(self.env, &g, g2).map_err(|e| e.0));
        self.api = Some(api);
        self.trace(|| format!("by {:.3}s: {}", t0.elapsed().as_secs_f64(), Printer::new(self.env).short(goal)));
        res
    }

    fn ev_in(&mut self, api: &sl_proof::api::Api, r: &R, slots: Slots) -> Result<Seq, String> {
        match r {
            R::S(x) => Ok(x.clone()),
            R::F(n) => {
                let s = api.fact(self.env, n).map_err(|e| e.0)?;
                self.bk_inst(api, s, n)
            }
            R::Slot(n) => slots.iter().find(|x| x.0 == *n).map(|x| x.1.clone()).ok_or_else(|| format!("no fact for the slot {}", n)),
            R::Inst(n, binds) => {
                let _p = super::prof::g("ev inst");
                let s = api.fact(self.env, n).map_err(|e| e.0)?;
                // (its breakpoint binders, found in its own statement)
                let bk: Vec<(VarId, Term)> = if binds.iter().any(|b| b.0 == "bkp") {
                    Vec::new()
                } else {
                    let mut vs = Vec::new();
                    s.concl().vars(&mut vs);
                    let by = |nm: &str, t: &Term| vs.iter().find(|v| self.env.vars[**v as usize].name == nm).map(|v| (*v, t.clone()));
                    by("bkp", &self.bkp).into_iter().chain(by("bka", &self.bka)).collect()
                };
                // (the breakpoints last: theirs mention the function's own
                // variables, s among them)
                let bs: Vec<(&str, Term)> = binds.iter().map(|(k, v)| (*k, self.expand(v))).collect();
                let s = {
                    let _p = super::prof::g("inst api");
                    api.inst(self.env, s, &bs).map_err(|e| format!("{}: {}", n, e.0))?
                };
                let _p = super::prof::g("inst bk");
                let mut s = s;
                for (v, t) in bk {
                    let te = self.expand(&t);
                    s = api.inst_var(self.env, s, v, &te).map_err(|e| format!("{}: {}", n, e.0))?;
                }
                Ok(s)
            }
            R::Mp(h, args) => {
                let s = self.ev_in(api, h, slots)?;
                let a = self.args_of(api, args, slots)?;
                let _p = super::prof::g("ev mp");
                api.mp(self.env, s, a).map_err(|e| format!("{}: {}", self.head_name(h), e.0))
            }
            R::Apply(h, args) => {
                let s = self.ev_in(api, h, slots)?;
                let a = self.args_of(api, args, slots)?;
                let _p = super::prof::g("ev apply");
                api.apply(self.env, s, a, None).map_err(|e| format!("{}: {}", self.head_name(h), e.0))
            }
            R::Expand(h, names) => {
                let s = self.ev_in(api, h, slots)?;
                let syms = self.syms(names)?;
                api.expand(self.env, s, &syms).map_err(|e| e.0)
            }
        }
    }

    /// a rule over the claim (its binders bkp, bka): at the walk's
    /// breakpoints
    fn bk_inst(&mut self, api: &sl_proof::api::Api, s: Seq, n: &str) -> Result<Seq, String> {
        let mut vs = Vec::new();
        s.concl().vars(&mut vs);
        if !vs.iter().any(|v| self.env.vars[*v as usize].name == "bkp") {
            return Ok(s);
        }
        let bs = [("bkp", self.bkp.clone()), ("bka", self.bka.clone())];
        api.inst(self.env, s, &bs).map_err(|e| format!("{}: {}", n, e.0))
    }

    pub fn head_name(&self, r: &R) -> String {
        match r {
            R::F(n) | R::Inst(n, _) => n.clone(),
            R::Mp(h, _) | R::Apply(h, _) | R::Expand(h, _) => self.head_name(h),
            _ => "a step".into(),
        }
    }

    fn args_of(&mut self, api: &sl_proof::api::Api, args: &[RA], slots: Slots) -> Result<Vec<A>, String> {
        let mut out = Vec::new();
        for a in args {
            out.push(match a {
                RA::T(x) => A::T(self.expand(x)),
                RA::P(rp) => A::G(self.g_of(api, rp, slots)?),
            });
        }
        Ok(out)
    }

    fn g_of(&mut self, api: &sl_proof::api::Api, rp: &RP, slots: Slots) -> Result<G, String> {
        Ok(match rp {
            RP::By(r) => G::By(self.ev_in(api, r, slots)?),
            RP::Simp(with_l, rs, keep, unroll) => {
                let mut fs = if *with_l { self.lf.clone() } else { Vec::new() };
                for r in rs {
                    fs.push(self.ev_in(api, r, slots)?);
                }
                G::Simp(fs, self.syms(keep)?, *unroll)
            }
            RP::Taut(rs) => G::Taut(rs.iter().map(|r| self.ev_in(api, r, slots)).collect::<Result<_, _>>()?),
            RP::Arith(rs) => G::Arith(rs.iter().map(|r| self.ev_in(api, r, slots)).collect::<Result<_, _>>()?),
            RP::Bitwise(rs, n) => G::Bitwise(rs.iter().map(|r| self.ev_in(api, r, slots)).collect::<Result<_, _>>()?, Some(Term::nat(Nat::from_u128(*n)))),
            RP::Defs(inner, names) => G::Defs(Box::new(self.g_of(api, inner, slots)?), self.syms(names)?),
            RP::Mp(r, args) => G::Mp(self.ev_in(api, r, slots)?, self.args_of(api, args, slots)?),
        })
    }

    /// `t` as a value of the variables `vs` (outermost first): a body with
    /// them bound (`x y. t`)
    pub fn abs(&self, t: &Term, vs: &[VarId]) -> Term {
        fn go(t: &Term, vs: &[VarId], depth: u32, bf: &dyn Fn(u32, usize) -> u32) -> Term {
            match t.node() {
                Node::Var(v, a) if a.is_empty() => match vs.iter().position(|w| w == v) {
                    Some(i) => Term::bvar(depth + (vs.len() - 1 - i) as u32),
                    None => t.clone(),
                },
                Node::Var(_, a) => t.with_args(a.iter().map(|x| go(x, vs, depth, bf)).collect()),
                Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| go(x, vs, depth + bf(*s, i), bf)).collect()),
                _ => t.clone(),
            }
        }
        let bf = self.env.binders_fn();
        go(&self.expand(t), vs, 0, &bf)
    }

    /// `s` with its hypotheses `hs` discharged (the last first) and the
    /// variables `vs` generalized (the last first): `all vs. hs -> ..`
    pub fn close(&mut self, s: Seq, hs: &[Term], vs: &[VarId]) -> Result<Seq, String> {
        let mut s = s;
        for h in hs.iter().rev() {
            s = s.discharge(self.env, &self.expand(h)).map_err(|e| e.0)?;
        }
        let api = self.api.take().expect("the proving context");
        let mut res = Ok(());
        for v in vs.iter().rev() {
            match Seq::gen(self.env, &api.lg, &s, *v) {
                Ok(x) => s = x,
                Err(e) => {
                    res = Err(e.0);
                    break;
                }
            }
        }
        self.api = Some(api);
        res.map(|_| s)
    }

    /// an assumption (a hypothesis of what follows)
    pub fn assume(&mut self, h: &Term) -> Result<Seq, String> {
        Seq::assume(self.env, self.expand(h)).map_err(|e| e.0)
    }
}
