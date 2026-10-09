//! The proof language of core files (`theorem NAME(params): φ proof ... qed`).
//!
//! Not trusted: it builds theorems only through the kernel's rules and its
//! trusted extensions (`sl_kernel::ext`), and the kernel checks that the
//! result is the stated theorem.
//!
//! A proof is a sequence of steps, one per line (a line continues while
//! brackets are open; `//` starts a comment):
//!
//! ```text
//! assume h: φ            hypothesis h (discharged at the end: φ -> ...)
//! assume h1 h2           the goal's next premises, named
//! fix x  /  fix x y      new variables (generalized at the end: all x. ...)
//! have h: φ := P         a fact from a proof expression (φ, if given, is checked)
//! have h: φ by R(args)   a fact by a rule that needs the goal φ (taut, ex_intro, ...)
//! have h1 h2 h3 ...      (any `have` with several names) its conjuncts, named
//! obtain x, h from P     a witness of P: `ex y. ψ(y)` (h: ψ(x))
//! obtain x y, h1 h2 from P   witnesses of `ex y z. ...`, its conjuncts named
//! show P  /  show φ by R(args)   the result (else the last `have`)
//! let N := t / let N(a, b) := t   an abbreviation, to the end of the block
//! ```
//!
//! Conjuncts are counted as written: `a && b && c` (`(a && b) && c`) has
//! three, an explicitly grouped `a && (b && c)` two; `_` names none. `h.k`
//! (also `R(args).k`) is the k-th conjunct of what h proves (from 1), by
//! `and_left` / `and_right` (core/logic.core) -- no tautology search. A line
//! starting with `by` or `:=` continues the step before.
//!
//! Labelled conjuncts: a definition's body or a statement may name its
//! conjuncts, `mM: m in Machine && sM: s in Machine` (term metadata, not
//! logic: `sl_kernel::Term`). `h.sM` / `R(args).sM` is the conjunct labelled
//! sM (a definition at the head of h's statement unfolded once if needed);
//! `have {sM, x = mM} := P` and `obtain v, {sM} from P` name the conjuncts
//! labelled so (x: the one labelled mM). Labels follow the terms through
//! instantiation and unfolding; a labelled group `l: (a && b)` is one
//! conjunct.
//!
//! (Core files also have `abbrev N(a, b) := t`; abbreviations are read as
//! their expansions.)
//!
//! Proof expressions: a fact (`h`, a theorem or axiom), instantiated
//! (`eq_subst[a := t, p := x. x = t]`: its parameters, or its leading
//! `all`s by their binder names, the others staying general), a rule
//! `name(args)`, or inline `(φ by R(args))` (a goal rule given its goal);
//! arguments are proof expressions, terms in braces `{t}`, occurrence
//! selections `{1, 3}`, or (for `unfold`, `expand`, `defs`) symbols.
//!
//! Rules: `mp(ab, a1, ..)` (in order: a proof discharges the leading
//! premise, a term `{t}` instantiates the leading `all`), `refl({t})`, `sym(e)`, `trans(e1, e2)`,
//! `subst({x. φ}, e, p)`, `conj(p1, .., pn)` (`p1 && .. && pn`, by
//! `and_intro`), `rewrite(e, p [, {k}..])` (every occurrence of e's left
//! side, or the k-th ones: numbered from 1, outer before inner, left to
//! right; e may be `all x... l = r`, rewriting its instances, also under
//! binders), `expand(p, c.. [, {k}..])` (c's occurrences unfolded once),
//! `unfold(sym)`,
//! `all_elim(p, {t1}, ..)`, `ex_intro({w}, {x. φ}, p)`, `witness(p)`,
//! `prop({t})`, `lit({t})`; `apply(f, a1, ..)`: f's leading `all`s and
//! schematic variables instantiated -- by the terms `{t}` among the ai, in
//! order, the rest by matching f's premises with the proofs (or a conjunct
//! of one), with a goal its conclusion first matched with the goal -- and f
//! applied to them; a function parameter applied to distinct bound
//! variables matches any term over them (a higher-order pattern); with a
//! goal only: `taut(p, ...)`, `ex_intro({w}, p)`. In `mp` and `apply`, a
//! goal rule (`simp(..)`, ..) proves its premise, and so does a nested
//! `apply` that only its premise determines.
//!
//! Unfolding: a fact proves a goal that differs from it by definitions
//! (implicitly unfolded at the mismatches, the newer definition first: in a
//! step's result against its goal, a premise of `mp` / `apply`, a stated
//! `assume`, a destructured `have` / `obtain`, `all_elim`); `assume` and
//! `fix` unfold a defined goal's head to the implication / `all` they
//! need. `irreducible NAME` (a declaration) keeps NAME folded there; the
//! step `unfold [D..] [in h]` unfolds explicitly (the goal, or fact h; no
//! D: the goal's head).
//!
//! Simplification: `rsimp(e1, .., D1, .. [, only])` (Lean-like, see
//! rsimp.rs): rewriting left to right with the facts and definitions given
//! and the registered rules (`simp NAME` declarations), to `true`; on a
//! fact, `rsimp(h, ..)`; as a step, `rsimp e1, .. [in h]` (the goal kept,
//! simplified, unless it became `true`). The older `simp` (symbolic
//! execution, closing paths by taut / arith) stays as it is.

use sl_kernel::ext::seq::{defined_sym, unfold_all, unfold_all_bounded};

/// subterms implicit unfolding may visit in a term (per attempt)
const UNFOLD_BUDGET: usize = 200_000;
use sl_kernel::ext::simp::LoopHint;
use sl_kernel::ext::{facts, Logic, Seq};
use sl_kernel::syntax::{parse_term, parse_value, Printer, ProofRequest, Prover};
use sl_kernel::{Env, KResult, KernelError, Node, SymId, Term, VarId};

mod bits;
mod mem;
mod rsimp;

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

/// The proof checker for `sl_kernel::syntax::load_with`.
pub struct ScriptProver;

impl Prover for ScriptProver {
    fn prove(&mut self, env: &mut Env, req: &ProofRequest) -> KResult<Seq> {
        let lg = Logic::new(env)?;
        let st = State::new(req.params.clone(), Vec::new(), Some(req.statement.clone()));
        let t0 = std::time::Instant::now();
        let r = run_block(env, &lg, st, &req.text, req.line, |env, s| conv_to(env, s, &req.statement, &[]));
        let t1 = std::time::Instant::now();
        let r = r.map_err(|e| KernelError(format!("proof of `{}`, {}", req.name, e.0)));
        // (STEP_SLOW=secs: also the proofs taking longer, and their final check)
        if let Some(lim) = std::env::var("STEP_SLOW").ok().and_then(|v| v.parse::<f64>().ok()) {
            let (a, b) = ((t1 - t0).as_secs_f64(), t1.elapsed().as_secs_f64());
            if a + b > lim {
                eprintln!("proof slow: {:.3}s (closing check {:.3}s): {}", a + b, b, req.name);
            }
        }
        r
    }
}

/// Runs the steps of a proof (or of a `proof ... qed` block inside one),
/// then closes its `assume`, `fix` and `obtain` steps. `line`: where the
/// text starts, for messages. `then`: the caller's check of the result,
/// while the block's `let`s still hold (its messages fold them).
fn run_block(env: &mut Env, lg: &Logic, mut st: State, text: &str, line: usize, then: impl FnOnce(&mut Env, Seq) -> KResult<Seq>) -> KResult<Seq> {
    let mut res = Ok(());
    // (STEP_SLOW=secs: the steps taking longer, reported -- a nested
    // block's with it)
    let slow = std::env::var("STEP_SLOW").ok().and_then(|v| v.parse::<f64>().ok());
    let all = steps(text);
    // (`show` ends its block: a step after it would replace the result)
    if let Some((line_no, _, _)) = all.iter().rev().skip(1).find(|(_, _, s)| s.split_whitespace().next() == Some("show")) {
        return Err(KernelError(format!("line {}: `show` before the block's last step (it ends the block)", line + line_no)));
    }
    for (line_no, body_no, step) in all {
        let t0 = std::time::Instant::now();
        res = st.step(env, lg, &step, line + line_no, line + body_no).map_err(|e| {
            if e.0.starts_with("line ") { e } else { KernelError(format!("line {}: {}", line + line_no, e.0)) }
        });
        if let Some(s) = slow {
            let dt = t0.elapsed().as_secs_f64();
            if dt > s {
                eprintln!("step slow: {:.3}s, line {}: {}", dt, line + line_no, step.chars().take(160).collect::<String>());
            }
        }
        if res.is_err() {
            break;
        }
    }
    let lets = std::mem::take(&mut st.lets);
    let r = res.and_then(|_| close(env, lg, st)).and_then(|s| then(env, s));
    // the block's `let`s end with it (an outer one it shadowed is back)
    for (name, prev) in lets.into_iter().rev() {
        match prev {
            Some(p) => env.abbrevs.insert(name, p),
            None => env.abbrevs.remove(&name),
        };
    }
    r
}

fn close(env: &mut Env, lg: &Logic, st: State) -> KResult<Seq> {
    {
        let mut s = st.last.clone().ok_or_else(|| KernelError("the proof is empty".into()))?;
        for fr in st.frames.iter().rev() {
            s = match fr {
                // an assumption already discharged by a step is not discharged again
                Frame::Assume(t) if st.discharged.borrow().contains(t) && !s.hyps().contains(t) => s,
                Frame::Assume(t) => s.discharge(env, t)?,
                // generalize over x only if it still occurs (a `gen` step may have done it)
                Frame::Fix(v) => {
                    let mut vs = Vec::new();
                    s.concl().vars(&mut vs);
                    if vs.contains(v) { Seq::gen(env, lg, &s, *v)? } else { s }
                }
                // ∃-elimination: ψ(x) ⊢ Q becomes ψ(c) -> Q with c the choice
                // witness of P, then modus ponens with `witness(P)`
                Frame::Obtain(v, prop, ex) => {
                    let s1 = s.discharge(env, prop)?;
                    if has_var(s.concl(), *v) {
                        return Err(KernelError(format!("the obtained `{}` occurs in the result", env.vars[*v as usize].name)));
                    }
                    if s1.hyps().iter().any(|h| has_var(h, *v)) {
                        return Err(KernelError(format!("the obtained `{}` occurs in an open assumption", env.vars[*v as usize].name)));
                    }
                    let w = Seq::witness(env, lg, ex)?;
                    let body = match ex.concl().node() {
                        Node::App(_, a) => a[0].clone(),
                        _ => unreachable!(),
                    };
                    let c = Term::app(lg.choose, vec![body]);
                    let s2 = Seq::inst(env, &s1, *v, &c)?;
                    Seq::mp(env, &s2, &w)?
                }
                Frame::Unfold(g, syms) => conv_to(env, s, g, syms)?,
                Frame::Flip(g) => {
                    let s = conv_to(env, s, &flip_term(env, lg, g)?, &[])?;
                    let s = flip_seq(env, lg, &s)?;
                    conv_to(env, s, g, &[])?
                }
                Frame::Rewrite(g, e) => {
                    let n = match e.concl().node() {
                        Node::App(_, a) => a[1].clone(),
                        _ => unreachable!(),
                    };
                    let s = conv_to(env, s, &n, &[])?;
                    let s = Seq::rewrite(env, &Seq::sym(env, e)?, &s)?;
                    conv_to(env, s, g, &[])?
                }
            };
        }
        Ok(s)
    }
}

impl State {
    fn new(scope: Vec<(String, VarId)>, facts: Vec<(String, Seq)>, goal: Option<Term>) -> State {
        State { scope, facts, frames: Vec::new(), last: None, discharged: Default::default(), goal, lets: Vec::new(), mem_cache: Default::default() }
    }
}

/// Implicit unfolding: the definitions (`start` and more) after whose
/// unfolding (`unfold_all`) `a` and `b` are the same, if any. Chosen at the
/// first mismatch: its heads' definitions (the newer first), else the
/// definitions around it (the innermost first), else any in the terms (the
/// newer first) -- one at a time, until the two agree. Definitions declared
/// `irreducible` are left folded (unless in `start`). No backtracking:
/// unfolding more never separates terms already equal.
fn unfold_match(env: &Env, a: &Term, b: &Term, start: &[SymId]) -> Option<Vec<SymId>> {
    let mut syms = start.to_vec();
    let ok = |s: SymId, syms: &[SymId]| {
        matches!(env.syms[s as usize].kind, sl_kernel::SymKind::Defined { .. }) && !env.irreducible.contains(&s) && !syms.contains(&s)
    };
    let head = |t: &Term| match t.node() {
        Node::App(s, _) => Some(*s),
        _ => None,
    };
    loop {
        // (a bounded effort: arithmetic's definitions, unfolded, explode)
        let (ua, ub) = if syms.is_empty() {
            (a.clone(), b.clone())
        } else {
            (unfold_all_bounded(env, a, &syms, UNFOLD_BUDGET)?, unfold_all_bounded(env, b, &syms, UNFOLD_BUDGET)?)
        };
        if ua == ub {
            return Some(syms);
        }
        // the path to the first mismatch
        let mut path = Vec::new();
        let (mut x, mut y) = (ua.clone(), ub.clone());
        loop {
            path.push((x.clone(), y.clone()));
            let next = match (x.node(), y.node()) {
                (Node::App(s, xa), Node::App(t, ya)) if s == t && xa.len() == ya.len() => xa.iter().zip(ya.iter()).find(|(p, q)| p != q).map(|(p, q)| (p.clone(), q.clone())),
                (Node::Var(s, xa), Node::Var(t, ya)) if s == t && xa.len() == ya.len() => xa.iter().zip(ya.iter()).find(|(p, q)| p != q).map(|(p, q)| (p.clone(), q.clone())),
                _ => None,
            };
            match next {
                Some((p, q)) => (x, y) = (p, q),
                None => break,
            }
        }
        let (mx, my) = path.pop().unwrap();
        let mut cands: Vec<SymId> = [head(&mx), head(&my)].into_iter().flatten().filter(|s| ok(*s, &syms)).collect();
        cands.sort_by(|p, q| q.cmp(p));
        if cands.is_empty() {
            cands = path.iter().rev().filter_map(|(p, _)| head(p)).filter(|s| ok(*s, &syms)).take(1).collect();
        }
        if cands.is_empty() {
            let mut all = Vec::new();
            syms_of(&ua, &mut all);
            syms_of(&ub, &mut all);
            cands = all.into_iter().filter(|s| ok(*s, &syms)).max().into_iter().collect();
        }
        syms.push(*cands.first()?);
    }
}

fn syms_of(t: &Term, out: &mut Vec<SymId>) {
    match t.node() {
        Node::App(s, a) => {
            out.push(*s);
            a.iter().for_each(|x| syms_of(x, out));
        }
        Node::Var(_, a) => a.iter().for_each(|x| syms_of(x, out)),
        _ => {}
    }
}

/// `s` as a proof of `goal`: the same, or the same after implicit unfolding
/// (`unfold_match`, from `start`); else the mismatch, on the folded terms.
fn conv_to(env: &Env, s: Seq, goal: &Term, start: &[SymId]) -> KResult<Seq> {
    if s.concl() == goal && start.is_empty() {
        return Ok(s);
    }
    match unfold_match(env, s.concl(), goal, start) {
        Some(syms) if syms.is_empty() => Ok(s),
        Some(syms) => Seq::conv(env, &s, goal, &syms),
        None => {
            let pp = Printer::new(env);
            err(format!("this proves `{}`, not `{}`\n  {}", pp.short(s.concl()), pp.short(goal), pp.mismatch(goal, s.concl())))
        }
    }
}

/// Modus ponens, the fact fitted to the premise by implicit unfolding.
fn mp_u(env: &Env, imp: &Seq, a: &Seq) -> KResult<Seq> {
    if let Node::App(i, c) = imp.concl().node() {
        if *i == env.builtins.imp && c[0] != *a.concl() {
            if let Some(syms) = unfold_match(env, a.concl(), &c[0], &[]) {
                return Seq::mp(env, imp, &Seq::conv(env, a, &c[0], &syms)?);
            }
        }
    }
    Seq::mp(env, imp, a)
}

/// `t` with its head definition unfolded once (an irreducible one only if
/// `forced`): the result and the definition.
fn unfold_head(env: &Env, t: &Term, forced: bool) -> Option<(Term, SymId)> {
    match t.node() {
        Node::App(s, _) if matches!(env.syms[*s as usize].kind, sl_kernel::SymKind::Defined { .. }) && (forced || !env.irreducible.contains(s)) => {
            let mut n = 0;
            Some((sl_kernel::ext::seq::unfold_at(env, t, *s, &[1], &mut n), *s))
        }
        _ => None,
    }
}

/// The fact `s` with its head definitions unfolded (implicitly: not
/// irreducible ones) until it has the form `want` (else `s`).
fn head_to(env: &Env, s: Seq, want: impl Fn(&Term) -> bool) -> KResult<Seq> {
    let (mut t, mut syms) = (s.concl().clone(), Vec::new());
    while !want(&t) {
        match unfold_head(env, &t, false) {
            Some((u, d)) => {
                t = u;
                syms.push(d);
            }
            None => return Ok(s),
        }
    }
    if syms.is_empty() { Ok(s) } else { Seq::conv(env, &s, &t, &syms) }
}

/// `t` (`all xs. H.. -> l = r`, or `l != r` / `!(l = r)` at the end) with
/// the conclusion's sides swapped
fn flip_term(env: &Env, lg: &Logic, t: &Term) -> KResult<Term> {
    let ne = env.sym_by_name.get("ne").copied();
    let not = env.sym_by_name.get("not").copied();
    match t.node() {
        Node::App(q, a) if *q == lg.all => Ok(t.with_args(vec![flip_term(env, lg, &a[0])?])),
        Node::App(q, a) if *q == env.builtins.imp => Ok(t.with_args(vec![a[0].clone(), flip_term(env, lg, &a[1])?])),
        Node::App(q, a) if *q == env.builtins.eq || Some(*q) == ne => Ok(t.with_args(vec![a[1].clone(), a[0].clone()])),
        Node::App(q, a) if Some(*q) == not && matches!(a[0].node(), Node::App(e, _) if *e == env.builtins.eq) => Ok(t.with_args(vec![flip_term(env, lg, &a[0])?])),
        _ => err(format!("flip: not an equation or disequation: {}", Printer::new(env).short(t))),
    }
}

/// `s` with its conclusion flipped (`flip_term`): under `all`s and
/// premises, by `sym`, or for a disequation by taut with `eq_sym`
fn flip_seq(env: &mut Env, lg: &Logic, s: &Seq) -> KResult<Seq> {
    let c = s.concl().clone();
    match c.node() {
        Node::App(q, _) if *q == lg.all => {
            let v = env.new_var(c.binder_name().unwrap_or("x"), 0);
            let f = flip_seq(env, lg, &Seq::all_elim(env, lg, s, &Term::var(v, vec![]))?)?;
            let g = Seq::gen(env, lg, &f, v)?;
            // (the binder's name as written)
            conv_to(env, g, &flip_term(env, lg, &c)?, &[])
        }
        Node::App(q, a) if *q == env.builtins.imp => {
            let h = a[0].clone();
            let f = flip_seq(env, lg, &Seq::mp(env, s, &Seq::assume(env, h.clone())?)?)?;
            f.discharge(env, &h)
        }
        Node::App(q, _) if *q == env.builtins.eq => Seq::sym(env, s),
        _ => {
            let target = flip_term(env, lg, &c)?;
            let (x, y) = match c.node() {
                Node::App(_, a) if a.len() == 2 => (a[0].clone(), a[1].clone()),
                Node::App(_, a) => match a[0].node() {
                    Node::App(_, b) => (b[0].clone(), b[1].clone()),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            };
            let mut l = facts::seq_of(env, "eq_sym").ok_or_else(|| KernelError("flip: `eq_sym` (core/logic.core) is not loaded".into()))?;
            let mut vs = Vec::new();
            l.concl().vars(&mut vs);
            for (v, t) in vs.iter().zip([y, x]) {
                l = Seq::inst(env, &l, *v, &t)?;
            }
            let ne = env.sym_by_name.get("ne").copied();
            let (s, target) = match c.node() {
                Node::App(q, _) if Some(*q) == ne => {
                    let syms = [ne.unwrap()];
                    let (u, ut) = (unfold_all(env, &c, &syms), unfold_all(env, &target, &syms));
                    (Seq::conv(env, s, &u, &syms)?, (ut, Some(target)))
                }
                _ => (s.clone(), (target, None)),
            };
            let r = Seq::taut(env, lg, &[&s, &l], &target.0)?;
            match target.1 {
                Some(t) => Seq::conv(env, &r, &t, &[ne.unwrap()]),
                None => Ok(r),
            }
        }
    }
}

fn nes_of(t: &Term, ne: Option<SymId>, out: &mut Vec<Term>) {
    if let Node::App(s, a) = t.node() {
        if Some(*s) == ne && !out.contains(t) {
            out.push(t.clone());
        }
        a.iter().for_each(|x| nes_of(x, ne, out));
    }
}

/// `a = b -> b = a` for the closed equations occurring both ways among
/// the premises and the goal (also as `a != b`)
fn sym_facts(env: &Env, ps: &[Seq], goal: &Term) -> KResult<Vec<Seq>> {
    fn eqs(env: &Env, t: &Term, ne: Option<SymId>, out: &mut Vec<(Term, Term)>) {
        if let Node::App(s, a) = t.node() {
            if (*s == env.builtins.eq || Some(*s) == ne) && a.len() == 2 && t.loose_depth(&env.binders_fn()) == 0 && a[0] != a[1] {
                let e = (a[0].clone(), a[1].clone());
                if !out.contains(&e) {
                    out.push(e);
                }
            }
            a.iter().for_each(|x| eqs(env, x, ne, out));
        }
    }
    let ne = env.sym_by_name.get("ne").copied();
    let mut all = Vec::new();
    for p in ps {
        eqs(env, p.concl(), ne, &mut all);
    }
    eqs(env, goal, ne, &mut all);
    let mut out = Vec::new();
    // (`a != b`: `!(a = b)`, both ways)
    let mut nes = Vec::new();
    for t in ps.iter().map(|p| p.concl()).chain([goal]) {
        nes_of(t, ne, &mut nes);
    }
    for t in nes.into_iter().filter(|t| t.loose_depth(&env.binders_fn()) == 0) {
        let ne = ne.unwrap();
        let u = unfold_all(env, &t, &[ne]);
        let f = Seq::conv(env, &Seq::assume(env, t.clone())?, &u, &[ne])?.discharge(env, &t)?;
        let g = Seq::conv(env, &Seq::assume(env, u.clone())?, &t, &[ne])?.discharge(env, &u)?;
        out.extend([f, g]);
    }
    for (a, b) in &all {
        if all.contains(&(b.clone(), a.clone())) {
            let Some(mut l) = facts::seq_of(env, "eq_sym") else { return Ok(Vec::new()) };
            let mut vs = Vec::new();
            l.concl().vars(&mut vs);
            for (v, t) in vs.iter().zip([a.clone(), b.clone()]) {
                l = Seq::inst(env, &l, *v, &t)?;
            }
            out.push(l);
        }
    }
    Ok(out)
}

fn has_var(t: &Term, v: VarId) -> bool {
    let mut vs = Vec::new();
    t.vars(&mut vs);
    vs.contains(&v)
}

/// Steps with their line numbers (relative to the start of the proof text)
/// and, for a sub-proof, its body's first line: a step continues on the
/// next lines while brackets are open.
fn steps(text: &str) -> Vec<(usize, usize, String)> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut start = 0;
    let mut depth = 0i32;
    // inside `... proof` .. `qed`: (start line, body line, header, body, nesting)
    let mut block: Option<(usize, usize, String, String, u32)> = None;
    let ends_proof = |s: &str| s == "proof" || s.ends_with(" proof");
    for (i, l) in text.lines().enumerate() {
        if let Some((st, bl, header, mut body, mut nest)) = block.take() {
            let t = l.split("//").next().unwrap_or("").trim();
            if t == "qed" {
                nest -= 1;
                if nest == 0 {
                    out.push((st, bl, format!("{}\n{}", header, body)));
                    continue;
                }
            } else if ends_proof(t) {
                nest += 1;
            }
            body.push_str(l);
            body.push('\n');
            block = Some((st, bl, header, body, nest));
            continue;
        }
        let l = match l.find("//") {
            Some(k) => &l[..k],
            None => l,
        };
        if l.trim().is_empty() && depth == 0 {
            continue;
        }
        // a line starting with `by` or `:=` continues the previous step
        if cur.is_empty() && (l.trim_start().starts_with("by ") || l.trim_start().starts_with(":= ")) {
            if let Some((k, _, prev)) = out.pop() {
                start = k;
                cur = prev;
            }
        }
        if cur.is_empty() {
            start = i;
        }
        cur.push(' ');
        cur.push_str(l.trim());
        depth += l.chars().map(|c| match c {
            '(' | '[' | '{' => 1,
            ')' | ']' | '}' => -1,
            _ => 0,
        }).sum::<i32>();
        // a line ending in an operator continues on the next line
        let open_op = ["=", "->", "&&", "||", "<->", ","].iter().any(|op| cur.trim_end().ends_with(op));
        if depth <= 0 && !open_op {
            let s = cur.trim().to_string();
            if ends_proof(&s) {
                // a sub-proof follows, up to its `qed`
                block = Some((start, i + 1, s[..s.len() - "proof".len()].trim().to_string(), String::new(), 1));
            } else {
                out.push((start, start, s));
            }
            cur.clear();
            depth = 0;
        }
    }
    if !cur.trim().is_empty() {
        out.push((start, start, cur.trim().to_string()));
    }
    out
}

enum Frame {
    Assume(Term),
    Fix(VarId),
    /// `obtain x, h from P`: the variable, its property, and P (`ex y. ψ(y)`)
    Obtain(VarId, Term, Seq),
    /// the goal unfolded (`unfold`, or `fix` / `assume` on a defined goal):
    /// the goal before, and the definitions unfolded
    Unfold(Term, Vec<SymId>),
    /// the goal simplified (`rsimp`): the goal before, and `goal = new`
    Rewrite(Term, Seq),
    /// the goal flipped (`flip`): the goal before
    Flip(Term),
}

struct State {
    scope: Vec<(String, VarId)>,
    facts: Vec<(String, Seq)>,
    frames: Vec<Frame>,
    last: Option<Seq>,
    /// assumptions discharged by a `discharge` step (not again at the end)
    discharged: std::cell::RefCell<Vec<Term>>,
    /// what is left to prove after the `assume` and `fix` steps so far
    /// (for `show by R`), if known
    goal: Option<Term>,
    /// the block's `let`s, with the abbreviation each shadowed
    lets: Vec<(String, Option<(usize, Term)>)>,
    /// the memory rules' rule sets and unfolded facts
    mem_cache: std::cell::RefCell<mem::MemCache>,
}

/// Rules that take their statement from the goal.
const GOAL_RULES: &[&str] = &["taut", "arith", "simp", "rsimp", "lists", "induct", "ex_intro", "defs", "sel", "eval", "mem", "bitwise", "cases"];

/// `a -> b`: (a, b)
fn imp_parts(env: &Env, t: &Term) -> KResult<(Term, Term)> {
    match t.node() {
        Node::App(i, c) if *i == env.builtins.imp => Ok((c[0].clone(), c[1].clone())),
        _ => err(format!("not an implication: {}", Printer::new(env).term(t))),
    }
}

/// Proof expressions.
#[derive(Debug)]
enum PE {
    /// a fact (hypothesis, earlier step, theorem or axiom)
    Ref(String),
    Rule(String, Vec<Arg>),
    /// instantiation of schematic variables: `var := value text`
    Inst(Box<PE>, Vec<(String, String)>),
    /// `P.k` / `P.l`: the k-th conjunct (from 1, as written) of what P
    /// proves / the conjunct labelled l
    Conj(Box<PE>, Result<usize, String>),
    /// `(φ by R(args))`: φ by a goal rule, inline (as `have h: φ by R`)
    By(String, Box<PE>),
}

#[derive(Debug)]
enum Arg {
    Proof(PE),
    Term(String),
}

/// Splits `s` at top-level occurrences of `sep` (outside brackets).
fn split_top(s: &str, sep: char) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        if c == sep && depth == 0 {
            out.push(cur.trim().to_string());
            cur.clear();
        } else {
            cur.push(c);
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur.trim().to_string());
    }
    out
}

/// an occurrence number `{k}` among a rule's arguments
fn occurrence(a: &Arg) -> Option<usize> {
    match a {
        Arg::Term(t) => t.trim().parse::<usize>().ok(),
        _ => None,
    }
}

/// `s` split at its last top-level (outside brackets) occurrence of `kw`
fn split_top_kw<'a>(s: &'a str, kw: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let mut found = None;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && s[i..].starts_with(kw) {
            found = Some(i);
        }
    }
    found.map(|i| (&s[..i], &s[i + kw.len()..]))
}

/// The index of the bracket closing the one at `open`.
fn closing(s: &str, open: usize) -> KResult<usize> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices().skip_while(|(i, _)| *i < open) {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(i);
                }
            }
            _ => {}
        }
    }
    err(format!("unbalanced brackets in `{}`", s))
}

/// `name`, `name(args)`, each optionally followed by `[var := value, ...]`.
fn parse_pe(s: &str) -> KResult<PE> {
    let s = s.trim();
    // (φ by R(args)): a goal rule with its goal, inline
    if s.starts_with('(') && closing(s, 0)? == s.len() - 1 {
        let inner = &s[1..s.len() - 1];
        if let Some((g, r)) = split_top_kw(inner, " by ") {
            return Ok(PE::By(g.trim().to_string(), Box::new(parse_pe(r)?)));
        }
        return parse_pe(inner);
    }
    let name_end = s.find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '$')).unwrap_or(s.len());
    let name = &s[..name_end];
    if name.is_empty() {
        return err(format!("expected a proof, found `{}`", s));
    }
    let mut pos = name_end + (s[name_end..].len() - s[name_end..].trim_start().len());
    let mut pe = if s[pos..].starts_with('(') {
        let close = closing(s, pos)?;
        let mut args = Vec::new();
        for a in split_top(&s[pos + 1..close], ',') {
            if let Some(t) = a.strip_prefix('{') {
                let t = t.strip_suffix('}').ok_or_else(|| KernelError(format!("unbalanced braces in `{}`", a)))?;
                args.push(Arg::Term(t.to_string()));
            } else {
                args.push(Arg::Proof(parse_pe(&a)?));
            }
        }
        pos = close + 1;
        let mut pe = PE::Rule(name.to_string(), args);
        // R(args).k.j / R(args).l: conjuncts of its result
        while let Some(r) = s[pos..].strip_prefix('.') {
            let n = r.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(r.len());
            if n == 0 {
                break;
            }
            pe = PE::Conj(Box::new(pe), r[..n].parse::<usize>().map_err(|_| r[..n].to_string()));
            pos += 1 + n;
        }
        pe
    } else {
        PE::Ref(name.to_string())
    };
    while s[pos..].trim_start().starts_with('[') {
        pos += s[pos..].len() - s[pos..].trim_start().len();
        let close = closing(s, pos)?;
        let mut insts = Vec::new();
        for part in split_top(&s[pos + 1..close], ',') {
            let (v, val) = part.split_once(":=").ok_or_else(|| KernelError(format!("expected `var := value` in `{}`", part)))?;
            insts.push((v.trim().to_string(), val.trim().to_string()));
        }
        pe = PE::Inst(Box::new(pe), insts);
        pos = close + 1;
    }
    if !s[pos..].trim().is_empty() {
        return err(format!("cannot read `{}` in `{}`", s[pos..].trim(), s));
    }
    Ok(pe)
}

impl State {
    fn term(&self, env: &mut Env, text: &str) -> KResult<Term> {
        parse_term(env, text, &self.scope)
    }

    fn fact(&self, env: &Env, name: &str) -> KResult<Seq> {
        if let Some((_, s)) = self.facts.iter().rev().find(|(n, _)| n == name) {
            return Ok(s.clone());
        }
        // theorems, axioms, conditional theorems, open lemmas
        if let Some(s) = facts::seq_of(env, name) {
            return Ok(s);
        }
        // h.k: the k-th conjunct of h (h.k.j: of that); h.l: the conjunct
        // labelled l
        if let Some((h, k)) = name.rsplit_once('.') {
            if let Ok(f) = self.fact(env, h) {
                return match k.parse::<usize>() {
                    Ok(k) => conj_get(env, &f, k),
                    Err(_) => conj_label(env, &f, k),
                };
            }
        }
        err(format!("unknown fact `{}`", name))
    }

    /// one step at `line` (a sub-proof's body from `body_line`)
    fn step(&mut self, env: &mut Env, lg: &Logic, step: &str, line: usize, body_line: usize) -> KResult<()> {
        // `have NAME: φ proof .. qed` / `show [φ] proof .. qed`: a sub-proof of
        // φ with its own assume / fix / obtain steps, closed at its `qed`
        if let Some((header, body)) = step.split_once('\n') {
            let (kw, rest) = header.split_once(' ').unwrap_or((header, ""));
            let (name, goal) = match kw {
                "have" => {
                    let (n, g) = rest.split_once(':').ok_or_else(|| KernelError("expected `have name: φ proof`".into()))?;
                    // `have c: case k of P proof`: P's k-th disjunct (as
                    // written, from 1) implies the current goal
                    let g = g.trim();
                    let goal = match g.strip_prefix("case ").and_then(|r| r.split_once(" of ")) {
                        Some((k, p)) => {
                            let k: usize = k.trim().parse().map_err(|_| KernelError(format!("`case {} of ..`: not a number", k.trim())))?;
                            let f = self.eval(env, lg, &parse_pe(p.trim())?)?;
                            let ds = disj_parts(env, f.concl());
                            let d = ds.get(k.wrapping_sub(1)).cloned().ok_or_else(|| {
                                KernelError(format!("`case {} of {}`: {} disjuncts in `{}`", k, p.trim(), ds.len(), Printer::new(env).short(f.concl())))
                            })?;
                            let cur = self.goal.clone().ok_or_else(|| KernelError("`case k of P`: no current goal here".into()))?;
                            Term::app(env.builtins.imp, vec![d, cur])
                        }
                        None => self.term(env, g)?,
                    };
                    (Some(n.trim().to_string()), goal)
                }
                "show" if rest.trim().is_empty() => {
                    (None, self.goal.clone().ok_or_else(|| KernelError("no current goal here: write `show φ proof`".into()))?)
                }
                "show" => (None, self.term(env, rest)?),
                _ => return err("a sub-proof belongs to `have NAME: φ` or `show [φ]`"),
            };
            let child = State::new(self.scope.clone(), self.facts.clone(), Some(goal.clone()));
            let s = run_block(env, lg, child, body, body_line, |env, s| self.check(env, s, &goal))?;
            if let Some(n) = name {
                self.facts.push((n, s.clone()));
            }
            self.last = Some(s);
            return Ok(());
        }
        let (kw, rest) = step.split_once(' ').unwrap_or((step, ""));
        match kw {
            // let NAME := t  /  let NAME(a, b) := t: an abbreviation, to the end
            // of the block (a term is read with it expanded)
            "let" => {
                let (head, body) = rest.split_once(":=").ok_or_else(|| KernelError("expected `let NAME := term`".into()))?;
                let head = head.trim();
                let (name, params) = match head.split_once('(') {
                    Some((n, ps)) => {
                        let ps = ps.strip_suffix(')').ok_or_else(|| KernelError("expected `let NAME(a, b) := term`".into()))?;
                        (n.trim(), ps.split(',').map(|p| p.trim().to_string()).filter(|p| !p.is_empty()).collect::<Vec<_>>())
                    }
                    None => (head, Vec::new()),
                };
                let k = params.len();
                let text = if k == 0 { body.trim().to_string() } else { format!("{}. {}", params.join(" "), body.trim()) };
                let t = parse_value(env, &text, &self.scope, k as u32)?;
                let prev = env.abbrevs.get(name).cloned();
                sl_kernel::syntax::define_abbrev(env, name, k, t)?;
                self.lets.push((name.to_string(), prev));
            }
            // assume h: φ  /  assume h1 h2 ..: the goal's leading premises
            "assume" => {
                let given: Vec<(String, Option<Term>)> = match rest.split_once(':') {
                    Some((n, t)) => vec![(n.trim().to_string(), Some(self.term(env, t)?))],
                    None if !rest.trim().is_empty() => rest.split_whitespace().map(|n| (n.to_string(), None)).collect(),
                    None => return err("expected `assume name: φ` or `assume name ..`"),
                };
                for (n, t) in given {
                    // (a defined goal: its head unfolded to an implication)
                    self.unfold_goal(env, |g| matches!(g.node(), Node::App(i, _) if *i == env.builtins.imp));
                    let t = match t {
                        // (SLC_TIDY: report a stated formula that is the goal's
                        // premise, for scripts/tidy_proofs.py)
                        Some(t) => {
                            if std::env::var("SLC_TIDY").is_ok() && matches!(self.goal.as_ref().map(|g| imp_parts(env, g)), Some(Ok((p, _))) if p == t) {
                                eprintln!("tidy-assume\t{}", line);
                            }
                            t
                        }
                        None => match self.goal.as_ref().map(|g| imp_parts(env, g)) {
                            Some(Ok((p, _))) => p,
                            _ => return err(format!("assume {}: the goal is not known to be an implication here (write `assume {}: φ`)", n, n)),
                        },
                    };
                    let s = Seq::assume(env, t.clone())?;
                    self.facts.push((n, s));
                    // (a stated premise: the goal's up to implicit unfolding)
                    self.goal = match self.goal.as_ref().map(|g| g.node()) {
                        Some(Node::App(i, a)) if *i == env.builtins.imp && (a[0] == t || unfold_match(env, &a[0], &t, &[]).is_some()) => Some(a[1].clone()),
                        _ => None,
                    };
                    self.frames.push(Frame::Assume(t));
                }
            }
            // fix x  /  fix x y ..
            "fix" => {
                for n in rest.split_whitespace() {
                    self.unfold_goal(env, |g| matches!(g.node(), Node::App(a, _) if *a == lg.all));
                    let v = env.new_var(n, 0);
                    self.scope.push((n.to_string(), v));
                    self.goal = match self.goal.as_ref().map(|g| g.node()) {
                        Some(Node::App(a, b)) if *a == lg.all => Some(b[0].instantiate_params(&[Term::var(v, vec![])], &env.binders_fn())),
                        _ => None,
                    };
                    self.frames.push(Frame::Fix(v));
                }
            }
            // unfold [D..] [in h]: the goal (or the fact h) with the
            // definitions D unfolded (every occurrence, repeatedly) -- or the
            // goal's head definition, once
            "unfold" => {
                let (names, h) = match split_top_kw(rest, "in") {
                    Some((a, b)) => (a.trim(), Some(b.trim())),
                    None => (rest.trim(), None),
                };
                let syms = names.split_whitespace().map(|n| defined_sym(env, n)).collect::<KResult<Vec<SymId>>>()?;
                match h {
                    Some(h) => {
                        if syms.is_empty() {
                            return err("expected `unfold D.. in h`");
                        }
                        let f = self.fact(env, h)?;
                        let t = unfold_all(env, f.concl(), &syms);
                        let s = Seq::conv(env, &f, &t, &syms)?;
                        self.facts.push((h.to_string(), s));
                    }
                    None => {
                        let g = self.goal.clone().ok_or_else(|| KernelError("unfold: no current goal here".into()))?;
                        let (u, syms) = if syms.is_empty() {
                            let (u, s) = unfold_head(env, &g, true).ok_or_else(|| KernelError("unfold: the goal's head is not a definition".into()))?;
                            (u, vec![s])
                        } else {
                            (unfold_all(env, &g, &syms), syms)
                        };
                        if u == g {
                            return err("unfold: the goal has none of these definitions");
                        }
                        self.frames.push(Frame::Unfold(g, syms));
                        self.goal = Some(u);
                    }
                }
            }
            // flip [in h]: the goal's (or the fact h's) equation or
            // disequation the other way round (under `all`s and premises)
            "flip" => match rest.trim().strip_prefix("in ") {
                Some(h) => {
                    let h = h.trim();
                    let f = self.fact(env, h)?;
                    let s = flip_seq(env, lg, &f)?;
                    self.facts.push((h.to_string(), s));
                }
                None if rest.trim().is_empty() => {
                    let g = self.goal.clone().ok_or_else(|| KernelError("flip: no current goal here".into()))?;
                    let u = flip_term(env, lg, &g)?;
                    self.frames.push(Frame::Flip(g));
                    self.goal = Some(u);
                }
                None => return err("expected `flip` or `flip in h`"),
            },
            // rsimp [e1, ..] [in h]: the goal (or the fact h) simplified with
            // the rules (see `rsimp`); a goal simplified to `true` is proven
            "rsimp" => {
                let (rules, h) = match split_top_kw(rest, "in") {
                    Some((a, b)) => (a.trim(), Some(b.trim())),
                    None => (rest.trim(), None),
                };
                let args = match parse_pe(&format!("rsimp({})", rules))? {
                    PE::Rule(_, a) => a,
                    _ => unreachable!(),
                };
                let rs = self.rsimp_rules(env, lg, &args)?;
                match h {
                    Some(h) => {
                        let f = self.fact(env, h)?;
                        let s = self.rsimp_fact(env, lg, f, &rs)?;
                        self.facts.push((h.to_string(), s));
                    }
                    None => {
                        let g = self.goal.clone().ok_or_else(|| KernelError("rsimp: no current goal here".into()))?;
                        let e = self.rsimp_eq(env, lg, &g, &rs, 0)?;
                        let n = match e.concl().node() {
                            Node::App(_, a) => a[1].clone(),
                            _ => unreachable!(),
                        };
                        match self.closes(env, lg, &n, &rs) {
                            Some(p) => self.last = Some(Seq::rewrite(env, &Seq::sym(env, &e)?, &p)?),
                            None if n == g => return err("rsimp: no rule applies to the goal"),
                            None => {
                                self.frames.push(Frame::Rewrite(g, e));
                                self.goal = Some(n);
                            }
                        }
                    }
                }
            }
            // print P: shows what P proves (and the current goal), for writing proofs
            "print" => {
                let s = self.eval(env, lg, &parse_pe(rest)?)?;
                eprintln!("line {}: {}", line, s.show(env));
                if let Some(g) = &self.goal {
                    eprintln!("  goal: {}", Printer::new(env).term(g));
                }
            }
            "step" => self.step_run(env, lg, rest)?,
            "obtain" => {
                // obtain x, h from P   (P: ex y. ψ(y); h: ψ(x) for a new x);
                // obtain x1 .. xn, h from P   (P: ex y1 .. yn. ψ);
                // obtain x.., h1 .. hk from P   (ψ's k conjuncts as written,
                // `conj_parts`; `_` names none)
                let (names, p) = rest.split_once(" from ").ok_or_else(|| KernelError("expected `obtain x, h from P`".into()))?;
                let (xs, hs) = names.split_once(',').ok_or_else(|| KernelError("expected `obtain x, h from P`".into()))?;
                let (xs, hs): (Vec<&str>, Vec<&str>) = (xs.split_whitespace().collect(), hs.split_whitespace().collect());
                if xs.is_empty() || hs.is_empty() {
                    return err("expected `obtain x.., h.. from P`");
                }
                let mut ex = self.eval(env, lg, &parse_pe(p)?)?;
                let mut prop = None;
                for x in &xs {
                    ex = head_to(env, ex, |t| matches!(t.node(), Node::App(e, _) if *e == lg.ex))?;
                    let body = match ex.concl().node() {
                        Node::App(e, a) if *e == lg.ex => a[0].clone(),
                        _ => return err(format!("obtain {}: `{}` is not `ex y. ...`", x, Printer::new(env).short(ex.concl()))),
                    };
                    let v = env.new_var(x, 0);
                    self.scope.push((x.to_string(), v));
                    let pv = body.instantiate_params(&[Term::var(v, vec![])], &env.binders_fn());
                    self.frames.push(Frame::Obtain(v, pv.clone(), ex));
                    // (the next witness: from this property, discharged by
                    // the frame above when the block closes)
                    ex = Seq::assume(env, pv.clone())?;
                    prop = Some(pv);
                }
                let h = Seq::assume(env, prop.unwrap())?;
                // (obtain x, {l1, l2} from P: the conjuncts labelled so)
                let hs_text = names.split_once(',').unwrap().1.trim();
                if let Some(inner) = hs_text.strip_prefix('{').and_then(|x| x.strip_suffix('}')) {
                    let ls: Vec<&str> = inner.split(',').map(|x| x.trim()).filter(|x| !x.is_empty()).collect();
                    let named = conj_labels(env, &h, &ls)?;
                    self.facts.extend(named);
                } else if hs.len() == 1 {
                    self.facts.push((hs[0].to_string(), h));
                } else {
                    let named = conj_named(env, &h, &hs, "obtain")?;
                    self.facts.extend(named);
                }
            }
            // have {l1, .., lk} [: φ] (:= P | by R): its conjuncts labelled
            // l1 .. lk, named so
            "have" if rest.trim_start().starts_with('{') => {
                let close = rest.find('}').ok_or_else(|| KernelError("expected `have {l1, ..} := P`".into()))?;
                let open = rest.find('{').unwrap();
                let ls: Vec<&str> = rest[open + 1..close].split(',').map(|x| x.trim()).filter(|x| !x.is_empty()).collect();
                self.step(env, lg, &format!("have __parts{}", &rest[close + 1..]), line, line)?;
                let (_, s) = self.facts.pop().unwrap();
                let named = conj_labels(env, &s, &ls)?;
                self.facts.extend(named);
            }
            // have h1 .. hk [: φ] (:= P | by R): its k conjuncts as written
            // (`_` names none; a last `..` ignores the rest, `r..` names it)
            "have" if rest.split(':').next().is_some_and(|l| l.split_whitespace().count() > 1) => {
                let k = rest.find(':').unwrap();
                let hs: Vec<&str> = rest[..k].split_whitespace().collect();
                self.step(env, lg, &format!("have __parts{}", &rest[k..]), line, line)?;
                let (_, s) = self.facts.pop().unwrap();
                let named = conj_named(env, &s, &hs, "have")?;
                self.facts.extend(named);
            }
            "have" | "show" => {
                // have NAME [: φ] (:= P | by R(args)) ;  show (P | φ by R(args))
                let (name, body) = if kw == "have" {
                    let k = rest.find(|c: char| c == ':' || c == ' ').ok_or_else(|| KernelError("expected `have name ...`".into()))?;
                    (Some(rest[..k].trim().to_string()), rest[k..].trim_start())
                } else {
                    (None, rest.trim())
                };
                let s = if let Some(by) = body.strip_prefix("by ").filter(|_| name.is_none()) {
                    // show by R: the current goal
                    let goal = self.goal.clone().ok_or_else(|| KernelError("no current goal here: write `show φ by ...`".into()))?;
                    self.by(env, lg, &goal, &parse_pe(by)?)?
                } else if let Some((goal, by)) = rsplit_kw(body, " by ") {
                    let goal = goal.trim().trim_start_matches(':').trim();
                    let goal = self.term(env, goal)?;
                    self.by(env, lg, &goal, &parse_pe(by.trim())?)?
                } else {
                    let (goal, p) = match body.strip_prefix(":=") {
                        Some(p) => (None, p),
                        None => match body.strip_prefix(':') {
                            Some(r) => {
                                let (g, p) = split_assign(r).ok_or_else(|| KernelError("expected `:=` or `by`".into()))?;
                                (Some(g), p)
                            }
                            None => (None, body),
                        },
                    };
                    let s = self.eval(env, lg, &parse_pe(p)?)?;
                    // (the fact's free schematic variables fitted to the
                    // stated formula, or show's current goal)
                    match goal {
                        Some(g) => {
                            let g = self.term(env, &g)?;
                            self.check(env, s, &g)?
                        }
                        None if kw == "show" => match self.goal.clone() {
                            Some(g) => self.fit(env, s, &g)?,
                            None => s,
                        },
                        None => s,
                    }
                };
                if let Some(n) = name {
                    self.facts.push((n, s.clone()));
                }
                self.last = Some(s);
            }
            _ => {
                let s = self.eval(env, lg, &parse_pe(step)?)?;
                self.last = Some(s);
            }
        }
        Ok(())
    }

    fn proofs(&self, env: &mut Env, lg: &Logic, args: &[Arg]) -> KResult<Vec<Seq>> {
        args.iter()
            .map(|a| match a {
                Arg::Proof(p) => self.eval(env, lg, p),
                Arg::Term(t) => err(format!("expected a proof, found the term `{}`", t)),
            })
            .collect()
    }

    fn term_arg(&self, env: &mut Env, a: Option<&Arg>, k: u32) -> KResult<Term> {
        match a {
            Some(Arg::Term(t)) => parse_value(env, t, &self.scope, k),
            _ => err("expected a term argument `{...}`"),
        }
    }

    fn proof_arg(&self, env: &mut Env, lg: &Logic, a: Option<&Arg>) -> KResult<Seq> {
        match a {
            Some(Arg::Proof(p)) => self.eval(env, lg, p),
            _ => err("expected a proof argument"),
        }
    }

    /// A proof of `goal`: rules that need the goal get it, and pass the
    /// goals of their premises on to goal-directed premises.
    fn by(&self, env: &mut Env, lg: &Logic, goal: &Term, pe: &PE) -> KResult<Seq> {
        let PE::Rule(name, args) = pe else {
            // a plain fact: check it against the goal
            let s = self.eval(env, lg, pe)?;
            return self.check(env, s, goal);
        };
        match name.as_str() {
            // rsimp(e1, .., D1, .. [, only]): the goal rewritten with the
            // rules to `true` (or a known fact)
            "rsimp" => {
                let rs = self.rsimp_rules(env, lg, args)?;
                self.rsimp_close(env, lg, goal, &rs, 0)
            }
            // taut(p1, ..): the goal by propositional logic, an equation the
            // same as its flip (`eq_sym` instances added for the equations
            // occurring both ways)
            "taut" => {
                let mut ps = self.proofs(env, lg, args)?;
                let syms = sym_facts(env, &ps, goal)?;
                ps.extend(syms);
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::taut(env, lg, &refs, goal)
            }
            "apply" => {
                let s = self.apply_to(env, lg, args, Some(goal))?;
                self.check(env, s, goal)
            }
            // arith(p1, ..): the goal by propositional logic and linear arithmetic
            // eval(p1, ..): the goal evaluated on concrete data, with the
            // premises' equations as known values
            "eval" => {
                let ps = self.proofs(env, lg, args)?;
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::eval_goal(env, lg, &refs, goal)
            }
            "arith" => {
                let ps = self.proofs(env, lg, args)?;
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::arith(env, lg, &refs, goal)
            }
            // mem(p1, ..): the goal by the memory rules (reads through writes,
            // frames), the writes' places by arith from the facts
            "mem" => {
                let ps = self.proofs(env, lg, args)?;
                let ps = split_conj(env, ps)?;
                self.mem_goal(env, lg, goal, &ps)
            }
            // cases({k}, {a}, {b}, R, p1, ..): the goal for each value of the
            // variable k in a .. b - 1 (a <= k < b from p.. by arith), by R
            "cases" => {
                let k = self.term_arg(env, args.first(), 0)?;
                let num = |t: Term| match t.node() {
                    Node::Nat(n) => n.to_u128().ok_or_else(|| KernelError("cases: a range bound too large".into())),
                    _ => err("cases: the range bounds must be numerals"),
                };
                let a = num(self.term_arg(env, args.get(1), 0)?)?;
                let b = num(self.term_arg(env, args.get(2), 0)?)?;
                let Some(Arg::Proof(r)) = args.get(3) else { return err("cases: expected a rule for each case, `cases({k}, {a}, {b}, R, ..)`") };
                let ps = self.proofs(env, lg, &args[4..])?;
                self.cases_goal(env, lg, goal, &k, a, b, r, &ps)
            }
            // bitwise([{n},] p1, ..): the goal bit by bit (a word equation
            // by extensionality), the bits explained by the bit rules
            "bitwise" => {
                let (width, rest) = match args.first() {
                    Some(Arg::Term(_)) => (Some(self.term_arg(env, args.first(), 0)?), &args[1..]),
                    _ => (None, &args[..]),
                };
                let ps = self.proofs(env, lg, rest)?;
                let ps = split_conj(env, ps)?;
                self.bitwise_goal(env, lg, goal, &ps, width)
            }
            // simp(p1, ..): the goal, simplified, from the simplified premises
            // (symbolic execution of `runs`), then taut or arith
            // Loops need invariants: a term `{l0 l. I}` (the loop's first
            // and current state), optionally followed by a variant `{l. m}`;
            // or `unroll`: loops without one are unrolled (when their
            // iterations are decided, e.g. on concrete data)
            "simp" => {
                let mut facts = Vec::new();
                let mut loops: Vec<LoopHint> = Vec::new();
                let mut keep = Vec::new();
                for a in args {
                    match a {
                        // keep(P): runs of program P stay folded
                        Arg::Proof(PE::Rule(r, xs)) if r == "keep" => {
                            for x in xs {
                                match x {
                                    Arg::Proof(PE::Ref(n)) => keep.push(defined_sym(env, n)?),
                                    _ => return err("keep(P, ..) takes names of programs"),
                                }
                            }
                        }
                        Arg::Proof(PE::Ref(r)) if r == "unroll" => {
                            loops.push(LoopHint { inv: Term::app(env.builtins.eq, vec![Term::bvar(0), Term::bvar(0)]), var: None, unroll: true })
                        }
                        Arg::Proof(_) => facts.push(self.proof_arg(env, lg, Some(a))?),
                        Arg::Term(t) => match parse_value(env, t, &self.scope, 2) {
                            Ok(inv) => loops.push(LoopHint { inv, var: None, unroll: false }),
                            Err(_) => {
                                let m = parse_value(env, t, &self.scope, 1)
                                    .map_err(|e| KernelError(format!("simp: `{{{}}}` is neither an invariant `{{l0 l. I}}` nor a variant `{{l. m}}`: {}", t, e.0)))?;
                                match loops.last_mut() {
                                    Some(h) if h.var.is_none() => h.var = Some(m),
                                    _ => return err(format!("simp: the variant `{{{}}}` must follow its invariant `{{l0 l. I}}`", t)),
                                }
                            }
                        },
                    }
                }
                let refs: Vec<&Seq> = facts.iter().collect();
                Seq::simp_goal(env, lg, &refs, goal, &loops, &keep)
            }
            // lists(p1, ..): `A = B` for list expressions with the same pieces
            // (the premises say which terms are lists)
            "lists" => {
                let ps = self.proofs(env, lg, args)?;
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::lists(env, lg, &refs, goal)
            }
            // induct(base, step): the goal `all n. n in omega -> P(n)` from
            // base: P(0) and step: all n. n in omega -> P(n) -> P(n + 1)
            // (the theorem `nat_ind`; base and step get their goals)
            "induct" => {
                let (Some(Arg::Proof(base)), Some(Arg::Proof(step))) = (args.first(), args.get(1)) else {
                    return err("induct takes a proof of the base case and one of the step");
                };
                let body = match goal.node() {
                    Node::App(a, b) if *a == lg.all => match b[0].node() {
                        Node::App(i, c) if *i == env.builtins.imp => c[1].clone(),
                        _ => return err("induct: the goal is not `all n. n in omega -> P(n)`"),
                    },
                    _ => return err("induct: the goal is not `all n. n in omega -> P(n)`"),
                };
                let ind = facts::seq_of(env, "nat_ind").ok_or_else(|| KernelError("induct needs the theorem `nat_ind` (core/nat.core)".into()))?;
                let mut vs = Vec::new();
                ind.concl().vars(&mut vs);
                let p = vs.iter().copied().find(|v| env.vars[*v as usize].name == "p").ok_or_else(|| KernelError("nat_ind has no `p`".into()))?;
                let ind = Seq::inst(env, &ind, p, &body)?;
                // P(0) -> (step) -> goal
                let (g_base, rest) = imp_parts(env, ind.concl())?;
                let (g_step, _) = imp_parts(env, &rest)?;
                let b = self.by(env, lg, &g_base, base)?;
                let s = self.by(env, lg, &g_step, step)?;
                let r = Seq::mp(env, &Seq::mp(env, &ind, &b)?, &s)?;
                self.check(env, r, goal)
            }
            // ex_intro({w1}, .., {wk}, p): the goal `ex x1 .. xk. φ`, p a proof of φ(w1, .., wk)
            "ex_intro" if matches!(args.last(), Some(Arg::Proof(_))) && args[..args.len() - 1].iter().all(|a| matches!(a, Arg::Term(_))) => {
                let mut layers = Vec::new();
                let mut g = goal.clone();
                for a in &args[..args.len() - 1] {
                    let body = match g.node() {
                        Node::App(s, b) if *s == lg.ex => b[0].clone(),
                        _ => return err(format!("ex_intro: `{}` is not `ex x. ...`", Printer::new(env).term(&g))),
                    };
                    let w = self.term_arg(env, Some(a), 0)?;
                    g = body.instantiate_params(std::slice::from_ref(&w), &env.binders_fn());
                    layers.push((w, body));
                }
                let Some(Arg::Proof(p)) = args.last() else { unreachable!() };
                let mut s = self.by(env, lg, &g, p)?;
                for (w, body) in layers.iter().rev() {
                    s = Seq::ex_intro(env, lg, &s, w, body)?;
                }
                Ok(s)
            }
            // sel(p): the goal `z in set_select(S, x. P)`, p a proof of `z in S && P(z)`
            "sel" => {
                let (ax, rhs) = self.select_def(env, goal)?;
                let p = match args.first() {
                    Some(Arg::Proof(p)) => p,
                    _ => return err("sel takes a proof"),
                };
                let s = self.by(env, lg, &rhs, p)?;
                Seq::taut(env, lg, &[&ax, &s], goal)
            }
            // defs(p, D1, .., Dn): p proves the goal up to unfolding the definitions Di
            "defs" => {
                let syms = self.syms(env, &args[1.min(args.len())..])?;
                let p = match args.first() {
                    Some(Arg::Proof(p)) => p,
                    _ => return err("defs takes a proof and definitions"),
                };
                let occ = self.occs(&args[1.min(args.len())..]);
                let unfolded = self.unfold_sel(env, goal, &syms, &occ)?;
                let s = match p {
                    PE::Rule(n, _) if GOAL_RULES.contains(&n.as_str()) => self.by(env, lg, &unfolded, p)?,
                    PE::Rule(n, a) if n == "apply" => self.apply_to(env, lg, a, Some(&unfolded))?,
                    _ => {
                        let s = self.eval(env, lg, p)?;
                        self.fit(env, s, &unfolded)?
                    }
                };
                Seq::conv(env, &s, goal, &syms)
            }
            _ => {
                let s = self.eval(env, lg, pe)?;
                self.check(env, s, goal)
            }
        }
    }

    /// `apply(f, a1, .., an)` (see `eval`).
    fn apply(&self, env: &mut Env, lg: &Logic, args: &[Arg]) -> KResult<Seq> {
        self.apply_to(env, lg, args, None)
    }

    /// `apply`, its conclusion first matched with the goal if there is one
    /// (binding the variables the premises have only applied to terms).
    fn apply_to(&self, env: &mut Env, lg: &Logic, args: &[Arg], goal: Option<&Term>) -> KResult<Seq> {
        let mut s = self.proof_arg(env, lg, args.first())?;
        let mut terms = Vec::new();
        // the proofs; a goal rule (`simp(..)`, `taut(..)`, ..) proves its
        // premise, instantiated, once the others have fixed the variables
        let mut proofs: Vec<Option<Seq>> = Vec::new();
        let mut goal_args: Vec<(usize, &PE, Option<Seq>)> = Vec::new();
        for a in &args[1..] {
            match a {
                Arg::Term(_) => terms.push(self.term_arg(env, Some(a), 0)?),
                Arg::Proof(p @ PE::Rule(n, _)) if GOAL_RULES.contains(&n.as_str()) => {
                    goal_args.push((proofs.len(), p, None));
                    proofs.push(None);
                }
                // (a nested apply: on its own if that determines it, else
                // against its premise as instantiated)
                Arg::Proof(p @ PE::Rule(n, _)) if n == "apply" => match self.eval(env, lg, p) {
                    Ok(s) if self.free_vars(&s).is_empty() => proofs.push(Some(s)),
                    r => {
                        goal_args.push((proofs.len(), p, r.ok()));
                        proofs.push(None);
                    }
                },
                Arg::Proof(_) => proofs.push(Some(self.proof_arg(env, lg, Some(a))?)),
            }
        }
        // the pattern variables: f's schematic variables (not fixed in this
        // proof, not in its hypotheses), then one per leading `all`
        let mut pvars = self.free_vars(&s);
        let mut terms = terms.into_iter();
        while let Node::App(a, _) = s.concl().node() {
            if *a != lg.all {
                break;
            }
            let t = match terms.next() {
                Some(t) => t,
                None => {
                    let v = env.new_var("x?", 0);
                    pvars.push(v);
                    Term::var(v, vec![])
                }
            };
            s = Seq::all_elim(env, lg, &s, &t)?;
        }
        if terms.next().is_some() {
            return err("apply: more terms than leading `all`s");
        }
        // match the conclusion with the goal, then the premises
        let mut binds: Vec<(VarId, Term)> = Vec::new();
        if let Some(g) = goal {
            let mut c = s.concl().clone();
            for _ in 0..proofs.len() {
                match imp_parts(env, &c) {
                    Ok((_, b)) => c = b,
                    Err(_) => break,
                }
            }
            let mut b = Vec::new();
            if pmatch(env, &c, g, &pvars, &mut b) {
                binds = b;
            }
        }
        let mut c = s.concl().clone();
        let and = env.sym_by_name.get("and").copied();
        for (i, p) in proofs.iter_mut().enumerate() {
            let (a, b) = imp_parts(env, &c).map_err(|_| KernelError(format!("apply: no premise for the proof number {}", i + 1)))?;
            c = b;
            let Some(p) = p else { continue };
            // (the variables bound so far substituted)
            let a = {
                let bf = env.binders_fn();
                binds.iter().fold(a, |t, (v, x)| t.subst_var(*v, x, &bf))
            };
            if !pmatch(env, &a, p.concl(), &pvars, &mut binds) {
                // a conjunct of the proof's statement that matches
                let mut cs = Vec::new();
                conjuncts(p.concl(), and, &mut cs);
                let hit = cs.iter().find(|x| {
                    let mut b = binds.clone();
                    pmatch(env, &a, x, &pvars, &mut b)
                });
                match hit {
                    Some(x) => {
                        pmatch(env, &a, x, &pvars, &mut binds);
                        let x = x.clone();
                        *p = Seq::taut(env, lg, &[&*p], &x)?;
                    }
                    None => {
                        let pp = Printer::new(env);
                        // (the premise with the variables matched so far)
                        let bf = env.binders_fn();
                        let a2 = binds.iter().fold(a.clone(), |t, (v, x)| t.subst_var(*v, x, &bf));
                        return err(format!("apply: the proof number {} does not match the premise `{}`\n  {}", i + 1, pp.short(&a2), pp.mismatch(&a2, p.concl())));
                    }
                }
            }
        }
        for v in &pvars {
            match binds.iter().find(|(w, _)| w == v) {
                Some((_, t)) => s = Seq::inst(env, &s, *v, t)?,
                None => {
                    let mut vs = Vec::new();
                    s.concl().vars(&mut vs);
                    if vs.contains(v) && env.vars[*v as usize].arity == 0 {
                        return err(format!("apply: `{}` is not determined (give it as a term `{{t}}`)", env.vars[*v as usize].name));
                    }
                }
            }
        }
        // the goal rules, on their premises as instantiated
        if !goal_args.is_empty() {
            let mut ps = Vec::new();
            let mut c = s.concl().clone();
            for _ in 0..proofs.len() {
                let (a, b) = imp_parts(env, &c)?;
                ps.push(a);
                c = b;
            }
            for (i, pe, eager) in goal_args {
                proofs[i] = Some(match (self.by(env, lg, &ps[i], pe), eager) {
                    (Ok(x), _) | (Err(_), Some(x)) => x,
                    (Err(e), None) => return err(format!("apply: premise {}: {}", i + 1, e.0)),
                });
            }
        }
        for p in proofs.iter().flatten() {
            s = mp_u(env, &s, p)?;
        }
        Ok(s)
    }

    /// For `z in set_select(S, x. P)`: the instance of the axiom
    /// `set_select_def` (`z in set_select(S, x. P) <-> z in S && P(z)`) and
    /// its right side.
    fn select_def(&self, env: &Env, t: &Term) -> KResult<(Seq, Term)> {
        let (inn, sel) = (env.sym_by_name.get("in").copied(), env.sym_by_name.get("set_select").copied());
        let (z, s, p) = match t.node() {
            Node::App(i, a) if Some(*i) == inn => match a[1].node() {
                Node::App(q, b) if Some(*q) == sel => (a[0].clone(), b[0].clone(), b[1].clone()),
                _ => return err(format!("not `z in set_select(...)`: {}", Printer::new(env).term(t))),
            },
            _ => return err(format!("not `z in set_select(...)`: {}", Printer::new(env).term(t))),
        };
        let ax = facts::seq_of(env, "set_select_def").ok_or_else(|| KernelError("no axiom `set_select_def`".into()))?;
        let mut vs = Vec::new();
        ax.concl().vars(&mut vs);
        let var = |n: &str| vs.iter().copied().find(|v| env.vars[*v as usize].name == n).ok_or_else(|| KernelError(format!("set_select_def has no `{}`", n)));
        let (vs_, vp, vz) = (var("s")?, var("p")?, var("z")?);
        let mut ax = Seq::inst(env, &ax, vs_, &s)?;
        ax = Seq::inst(env, &ax, vp, &p)?;
        ax = Seq::inst(env, &ax, vz, &z)?;
        let rhs = match ax.concl().node() {
            Node::App(_, a) if a.len() == 2 => a[1].clone(),
            _ => return err("set_select_def is not an equivalence"),
        };
        Ok((ax, rhs))
    }

    /// Defined symbols named by the arguments.
    fn syms(&self, env: &Env, args: &[Arg]) -> KResult<Vec<SymId>> {
        args.iter()
            .filter(|a| occurrence(a).is_none())
            .map(|a| match a {
                Arg::Proof(PE::Ref(n)) => defined_sym(env, n),
                _ => err("expected the name of a definition"),
            })
            .collect()
    }

    /// the occurrence numbers among `args` (`{2}`)
    fn occs(&self, args: &[Arg]) -> Vec<usize> {
        args.iter().filter_map(occurrence).collect()
    }

    /// `t` unfolded for `defs` / `expand`: every occurrence of `syms`
    /// (repeatedly), or only the chosen occurrences `occ` of one symbol
    fn unfold_sel(&self, env: &Env, t: &Term, syms: &[SymId], occ: &[usize]) -> KResult<Term> {
        if occ.is_empty() {
            return Ok(unfold_all(env, t, syms));
        }
        let [sym] = syms else { return err("occurrences ({k}) go with one definition") };
        let mut n = 0;
        let u = sl_kernel::ext::seq::unfold_at(env, t, *sym, occ, &mut n);
        if let Some(k) = occ.iter().find(|k| **k == 0 || **k > n) {
            return err(format!("no occurrence {} of `{}` ({} in all)", k, env.syms[*sym as usize].name, n));
        }
        Ok(u)
    }

    /// The schematic variables of `s` free to instantiate: not fixed in
    /// this proof, not in its hypotheses.
    fn free_vars(&self, s: &Seq) -> Vec<VarId> {
        let (mut vs, mut hv, mut out) = (Vec::new(), Vec::new(), Vec::new());
        s.concl().vars(&mut vs);
        for h in s.hyps() {
            h.vars(&mut hv);
        }
        for v in vs {
            if !hv.contains(&v) && !self.scope.iter().any(|(_, w)| *w == v) && !out.contains(&v) {
                out.push(v);
            }
        }
        out
    }

    /// `s` with its free schematic variables instantiated so that it is
    /// `target`, where they match it (else `s` as it is).
    fn fit(&self, env: &mut Env, s: Seq, target: &Term) -> KResult<Seq> {
        let pvars = self.free_vars(&s);
        let mut binds = Vec::new();
        if pvars.is_empty() || s.concl() == target || !pmatch(env, s.concl(), target, &pvars, &mut binds) {
            return Ok(s);
        }
        let mut s = s;
        for (v, t) in binds {
            s = Seq::inst(env, &s, v, &t)?;
        }
        Ok(s)
    }

    /// The goal's head definitions unfolded (implicitly: not irreducible
    /// ones) until it is of the form `want`.
    fn unfold_goal(&mut self, env: &Env, want: impl Fn(&Term) -> bool) {
        let Some(mut g) = self.goal.clone() else { return };
        let mut syms = Vec::new();
        while !want(&g) {
            match unfold_head(env, &g, false) {
                Some((u, s)) => {
                    g = u;
                    syms.push(s);
                }
                None => break,
            }
        }
        if !syms.is_empty() && want(&g) {
            self.frames.push(Frame::Unfold(self.goal.take().unwrap(), syms));
            self.goal = Some(g);
        }
    }

    fn check(&self, env: &mut Env, s: Seq, goal: &Term) -> KResult<Seq> {
        let s = self.fit(env, s, goal)?;
        conv_to(env, s, goal, &[])
    }

    /// `s` (`all x1 .. xn. φ`) with the binders named in `bound` instantiated
    /// by their values (`name[x2 := t]`), the ones before them kept general
    /// (eliminated with a fresh variable, generalized again).
    fn inst_bound(&self, env: &mut Env, lg: &Logic, mut s: Seq, bound: &[(&str, &str)]) -> KResult<Seq> {
        let mut names = Vec::new();
        let mut t = s.concl().clone();
        while let Node::App(a, x) = t.node() {
            if *a != lg.all {
                break;
            }
            names.push(t.binder_name().map(|n| n.to_string()));
            t = x[0].clone();
        }
        let mut last = 0;
        for (n, _) in bound {
            match names.iter().position(|m| m.as_deref() == Some(*n)) {
                Some(i) => last = last.max(i + 1),
                None => {
                    let known: Vec<&str> = names.iter().flatten().map(|x| x.as_str()).collect();
                    return err(format!("no variable `{}` to instantiate (the leading binders: {})", n, if known.is_empty() { "none".to_string() } else { known.join(", ") }));
                }
            }
        }
        let mut general = Vec::new();
        for name in names.iter().take(last) {
            let value = match bound.iter().find(|(n, _)| Some(*n) == name.as_deref()) {
                Some((_, text)) => self.term(env, text)?,
                None => {
                    let v = env.new_var(name.as_deref().unwrap_or("x"), 0);
                    general.push(v);
                    Term::var(v, vec![])
                }
            };
            s = Seq::all_elim(env, lg, &s, &value)?;
        }
        for v in general.into_iter().rev() {
            s = Seq::gen(env, lg, &s, v)?;
        }
        Ok(s)
    }

    /// `lemma` (a theorem, by name) applied to the facts `args`, by `apply`
    fn lemma(&mut self, env: &mut Env, lg: &Logic, lemma: &str, args: &[Seq]) -> KResult<Seq> {
        let n0 = self.facts.len();
        let mut pa = vec![Arg::Proof(PE::Ref(lemma.to_string()))];
        for (i, a) in args.iter().enumerate() {
            let name = format!("__step{}", i);
            self.facts.push((name.clone(), a.clone()));
            pa.push(Arg::Proof(PE::Ref(name)));
        }
        let r = self.apply_to(env, lg, &pa, None);
        self.facts.truncate(n0);
        r
    }

    /// `step x.., h.. from P with f1, ..`: P (a run of readable GIMPLE, or a
    /// fact on a program's outcome) inverted step by step -- the program's
    /// relation, `letin`s, binds by the `with` facts' one outcomes
    /// (`g.det`), the locals' choices and the `if`s' outcomes named by the
    /// names, the `if`s' branches by the `with` facts' conditions -- up to
    /// what it cannot step (a call, a loop, a branch or choice it has
    /// nothing for); that fact named h (or its conjuncts h..). Composes the
    /// lemmas of proofs/gimple_inv.core.
    fn step_run(&mut self, env: &mut Env, lg: &Logic, rest: &str) -> KResult<()> {
        let bad = || KernelError("expected `step [x.., ] h.. from P [with f1, ..] [using u1, ..]`".into());
        let (names, rest) = rest.split_once(" from ").ok_or_else(bad)?;
        let (rest, using_t) = match rest.split_once(" using ") {
            Some((r, u)) => (r, split_top(u, ',')),
            None => (rest, Vec::new()),
        };
        let (p, with) = match rest.split_once(" with ") {
            Some((p, w)) => (p, split_top(w, ',')),
            None => (rest, Vec::new()),
        };
        let mut using = Vec::new();
        for u in &using_t {
            using.push(self.eval(env, lg, &parse_pe(u.trim())?)?);
        }
        let using = split_conj(env, using)?;
        let (xs, hs): (Vec<String>, Vec<String>) = match names.split_once(',') {
            Some((x, h)) => (x.split_whitespace().map(String::from).collect(), h.split_whitespace().map(String::from).collect()),
            None => (Vec::new(), names.split_whitespace().map(String::from).collect()),
        };
        if hs.is_empty() {
            return Err(bad());
        }
        let mut xs: std::collections::VecDeque<String> = xs.into();
        let mut withs = std::collections::VecDeque::new();
        for w in &with {
            withs.push_back(self.eval(env, lg, &parse_pe(w.trim())?)?);
        }
        let sym = |n: &str| env.sym_by_name.get(n).copied();
        let (runs, mkprog, letin, bind, any, and, or, not, det) =
            (sym("runs"), sym("mkprog"), sym("letin"), sym("bind_rel"), sym("any_rel"), sym("and"), sym("or"), sym("not"), sym("g.det"));
        let head = |t: &Term| match t.node() {
            Node::App(f, a) => Some((*f, a.to_vec())),
            _ => None,
        };
        let (all_s, imp_s) = (lg.all, env.builtins.imp);
        let op_fact = |t: &Term| {
            let mut t = t.clone();
            loop {
                match t.node() {
                    Node::App(q, a) if *q == all_s => t = a[0].clone(),
                    Node::App(i, a) if *i == imp_s => t = a[1].clone(),
                    Node::App(d, _) => return Some(*d) == det,
                    _ => return false,
                }
            }
        };
        // an `if`'s outcome: ((c && T) || (c2 && E)) && K(x)
        let if_shape = |s: &Seq| {
            head(s.concl()).filter(|(g, _)| Some(*g) == and).and_then(|(_, ka)| {
                let (o, oa) = head(&ka[0])?;
                (Some(o) == or).then_some(())?;
                let (l, _) = head(&oa[0])?;
                let (r, _) = head(&oa[1])?;
                (Some(l) == and && Some(r) == and).then_some(())
            }).is_some()
        };
        let mut cur = self.eval(env, lg, &parse_pe(p.trim())?)?;
        // (`L && R` stepped in L, R pending: on L's outcome `x = V`, R at V)
        let mut pending: Vec<Seq> = Vec::new();
        for _ in 0..10000 {
            let Some((f, a)) = head(cur.concl()) else { break };
            if f == lg.eq && matches!(a[0].node(), Node::Var(..)) && !pending.is_empty() {
                let r = pending.pop().unwrap();
                let k = Seq::rewrite(env, &cur, &r)?;
                cur = self.step_simp(env, lg, k)?;
                continue;
            }
            if Some(f) == runs && head(&a[0]).is_some_and(|(g, _)| Some(g) == mkprog) {
                cur = self.lemma(env, lg, "g.runs_elim", &[cur])?;
            } else if let (true, Some((g, _))) = (Some(f) == runs, head(&a[0])) {
                // (a defined program: its definition)
                if !matches!(env.syms[g as usize].kind, sl_kernel::env::SymKind::Defined { .. }) {
                    break;
                }
                let name = env.syms[g as usize].name.clone();
                self.facts.push(("__stepc".into(), cur.clone()));
                let r = self.eval(env, lg, &parse_pe(&format!("expand(__stepc, {})", name))?);
                self.facts.pop();
                cur = r?;
            } else if Some(f) == letin {
                cur = self.lemma(env, lg, "g.letin_e", &[cur])?;
            } else if Some(f) == bind {
                // (an operation's one outcome: the next `with` fact)
                match withs.front() {
                    Some(w) if op_fact(w.concl()) => {
                        let w = withs.pop_front().unwrap();
                        cur = self.step_bind(env, lg, cur, w, &using)?;
                    }
                    _ => break,
                }
            } else if Some(f) == any {
                // (a local's choice: a word, named)
                if xs.is_empty() {
                    break;
                }
                let ex_t = Term::app(lg.ex, vec![a[0].clone()]);
                let Ok(ne) = self.by(env, lg, &ex_t, &parse_pe("ex_intro({0}, simp())")?) else { break };
                let e = self.lemma(env, lg, "g.any_e", &[ne, cur])?;
                let h = self.obtain_one(env, lg, e, &xs.pop_front().unwrap())?;
                cur = and_part(env, &h, true)?;
            } else if f == lg.ex {
                if xs.is_empty() {
                    break;
                }
                cur = self.obtain_one(env, lg, cur, &xs.pop_front().unwrap())?;
            } else if if_shape(&cur) {
                let h = cur.clone();
                // an `if`'s outcome: ((c && T) || (c2 && E)) && K(x)
                let branch = head(h.concl()).filter(|(g, _)| Some(*g) == and).and_then(|(_, ka)| {
                    let (o, oa) = head(&ka[0])?;
                    (Some(o) == or).then_some(())?;
                    let (l, la) = head(&oa[0])?;
                    let (r, ra) = head(&oa[1])?;
                    (Some(l) == and && Some(r) == and).then(|| (la[0].clone(), ra[0].clone()))
                });
                let Some((c, c2)) = branch else { unreachable!() };
                // (the branch: the next `with` fact implies its condition,
                // propositionally)
                let side = withs.front().and_then(|w| {
                    if let Ok(x) = Seq::taut(env, lg, &[w], &c) {
                        Some((true, x))
                    } else {
                        Seq::taut(env, lg, &[w], &c2).ok().map(|x| (false, x))
                    }
                });
                let Some((then, w)) = side else {
                    cur = h;
                    break;
                };
                withs.pop_front();
                let not = not.ok_or_else(|| KernelError("step: no `not`".into()))?;
                let (hif, hk) = (and_part(env, &h, false)?, and_part(env, &h, true)?);
                let mut t = if then {
                    let nn = Seq::taut(env, lg, &[&w], &Term::app(not, vec![c2.clone()]))?;
                    self.lemma(env, lg, "g.pick", &[hif, w, nn])?
                } else {
                    let nn = Seq::taut(env, lg, &[&w], &Term::app(not, vec![c.clone()]))?;
                    self.lemma(env, lg, "g.pick2", &[hif, w, nn])?
                };
                loop {
                    match head(t.concl()) {
                        Some((g, _)) if Some(g) == letin => t = self.lemma(env, lg, "g.letin_e", &[t])?,
                        Some((g, _)) if Some(g) == bind && withs.front().is_some_and(|w| op_fact(w.concl())) => {
                            let w = withs.pop_front().unwrap();
                            t = self.step_bind(env, lg, t, w, &using)?;
                        }
                        _ => break,
                    }
                }
                // (the branch's outcome x = V: K at V, its dispatch simplified)
                match head(t.concl()) {
                    Some((g, ta)) if g == lg.eq && matches!(ta[0].node(), Node::Var(..)) => {
                        let k = Seq::rewrite(env, &t, &hk)?;
                        cur = self.step_simp(env, lg, k)?;
                    }
                    _ => {
                        let both = Term::app(and.unwrap(), vec![t.concl().clone(), hk.concl().clone()]);
                        cur = Seq::taut(env, lg, &[&t, &hk], &both)?;
                        break;
                    }
                }
            } else if Some(f) == and && (!withs.is_empty() || !xs.is_empty())
                && head(&a[0]).is_some_and(|(g, _)| g == lg.ex || Some(g) == and || Some(g) == bind || Some(g) == letin || Some(g) == runs)
            {
                pending.push(and_part(env, &cur, true)?);
                cur = and_part(env, &cur, false)?;
            } else {
                // (an outcome's dispatch on a known outcome: simplified)
                let k = self.step_simp(env, lg, cur.clone())?;
                if k.concl() == cur.concl() {
                    break;
                }
                cur = k;
            }
        }
        while let Some(r) = pending.pop() {
            let both = Term::app(and.unwrap(), vec![cur.concl().clone(), r.concl().clone()]);
            cur = Seq::taut(env, lg, &[&cur, &r], &both)?;
        }
        if !withs.is_empty() {
            return err(format!("step: {} `with` facts not used (it stopped at `{}`)", withs.len(), Printer::new(env).short(cur.concl())));
        }
        if !xs.is_empty() {
            return err(format!("step: names not used: {} (it stopped at `{}`)", xs.into_iter().collect::<Vec<_>>().join(" "), Printer::new(env).short(cur.concl())));
        }
        if hs.len() == 1 {
            self.facts.push((hs[0].clone(), cur.clone()));
        } else {
            let hr: Vec<&str> = hs.iter().map(|x| x.as_str()).collect();
            let named = conj_named(env, &cur, &hr, "step")?;
            self.facts.extend(named);
        }
        self.last = Some(cur);
        Ok(())
    }

    /// a bind of `b` (`bind_rel(p, s, k, ..)`) by the operation's one
    /// outcome: a fact `g.det(p, s, ok(s1, v1))`, or a lemma concluding one
    /// (matched, its premises discharged from `using`: `mem_lemma_inst`);
    /// then the value read resolved (if it resolves) and the states
    /// simplified
    fn step_bind(&mut self, env: &mut Env, lg: &Logic, b: Seq, w: Seq, using: &[Seq]) -> KResult<Seq> {
        let det = env.sym_by_name.get("g.det").copied();
        let is_det = matches!(w.concl().node(), Node::App(d, _) if Some(*d) == det);
        let w = if is_det {
            w
        } else {
            let (p, s) = match b.concl().node() {
                Node::App(_, a) if a.len() == 5 => (a[0].clone(), a[1].clone()),
                _ => return err("step: not a bind"),
            };
            self.mem_lemma_inst(env, lg, &w, &p, &s, using)?
        };
        // (the value: ok(s1, v1)'s v1)
        let v1 = match w.concl().node() {
            Node::App(_, a) if a.len() == 3 => match a[2].node() {
                Node::App(_, o) if o.len() == 2 => Some(o[1].clone()),
                _ => None,
            },
            _ => None,
        };
        let mut cur = self.lemma(env, lg, "g.bind_inv", &[b, w])?;
        if !is_det {
            if let Some(e) = v1.and_then(|v1| self.mem_value(env, lg, &v1, using)) {
                cur = Seq::rewrite(env, &e, &cur)?;
            }
            cur = self.step_simp(env, lg, cur)?;
        }
        Ok(cur)
    }

    /// a run's outcome simplified: the outcome's parts and the propositional
    /// rules only (the program's terms as they are)
    fn step_simp(&mut self, env: &mut Env, lg: &Logic, k: Seq) -> KResult<Seq> {
        let rs = self.step_rules(env, lg)?;
        self.rsimp_fact(env, lg, k, &rs)
    }

    /// step's simplification rules: propositional, outcome parts, record
    /// fields
    pub(crate) fn step_rules(&self, env: &mut Env, lg: &Logic) -> KResult<std::rc::Rc<rsimp::Rules>> {
        if let Some(r) = self.mem_cache.borrow().rules.get(&2) {
            return Ok(r.clone());
        }
        let rules = "rsimp(eq_self, not_true, not_false, not_not, true_and, and_true, false_and, and_false, true_or, or_true, false_or, or_false, \
            fst_pair, snd_pair, letin_eq, out_state_ok, out_value_ok, out_state_exc, out_value_exc, fst_ok, fst_exc, fst_diverge, \
            app_update_same, app_update_other, fn_update_twice, only)";
        let args = match parse_pe(rules)? {
            PE::Rule(_, a) => a,
            _ => unreachable!(),
        };
        let r = std::rc::Rc::new(self.rsimp_rules(env, lg, &args)?);
        self.mem_cache.borrow_mut().rules.insert(2, r.clone());
        Ok(r)
    }

    /// `obtain x, h from e` (e: `ex y. ψ(y)`): h, ψ(x) for a new x
    fn obtain_one(&mut self, env: &mut Env, lg: &Logic, e: Seq, x: &str) -> KResult<Seq> {
        let body = match e.concl().node() {
            Node::App(f, a) if *f == lg.ex => a[0].clone(),
            _ => return err("step: not `ex y. ...`"),
        };
        let v = env.new_var(x, 0);
        self.scope.push((x.to_string(), v));
        let pv = body.instantiate_params(&[Term::var(v, vec![])], &env.binders_fn());
        self.frames.push(Frame::Obtain(v, pv.clone(), e));
        Seq::assume(env, pv)
    }

    fn eval(&self, env: &mut Env, lg: &Logic, p: &PE) -> KResult<Seq> {
        match p {
            PE::Ref(name) => self.fact(env, name),
            PE::By(g, p) => {
                let goal = self.term(env, g)?;
                self.by(env, lg, &goal, p)
            }
            PE::Conj(p, k) => {
                let s = self.eval(env, lg, p)?;
                match k {
                    Ok(k) => conj_get(env, &s, *k),
                    Err(l) => conj_label(env, &s, l),
                }
            }
            PE::Inst(p, insts) => {
                // simultaneous: names refer to the fact's variables before any
                // substitution; each goes through a fresh variable first
                let mut s = self.eval(env, lg, p)?;
                let mut vs = Vec::new();
                s.concl().vars(&mut vs);
                for h in s.hyps() {
                    h.vars(&mut vs);
                }
                let mut staged = Vec::new();
                // (names of leading `all` binders: instantiated after)
                let mut bound: Vec<(&str, &str)> = Vec::new();
                for (vname, text) in insts {
                    let cands: Vec<VarId> = vs.iter().copied().filter(|v| env.vars[*v as usize].name == *vname).collect();
                    let v = match cands.as_slice() {
                        [v] => *v,
                        [] => {
                            bound.push((vname, text));
                            continue;
                        }
                        _ => return err(format!("several variables named `{}`", vname)),
                    };
                    let k = env.vars[v as usize].arity;
                    let value = parse_value(env, text, &self.scope, k)?;
                    let tmp = env.new_var(&format!("{}'", vname), k);
                    let tmp_term = Term::var(tmp, (0..k).rev().map(Term::bvar).collect());
                    s = Seq::inst(env, &s, v, &tmp_term)?;
                    staged.push((tmp, value));
                }
                for (tmp, value) in staged {
                    s = Seq::inst(env, &s, tmp, &value)?;
                }
                if !bound.is_empty() {
                    s = self.inst_bound(env, lg, s, &bound)?;
                }
                Ok(s)
            }
            PE::Rule(name, args) => {
                let a0 = args.first();
                match name.as_str() {
                    // mp(f, x1, .., xn): f applied to x1, then to x2, ..; a
                    // goal rule xi (`simp(..)`, ..) proves the premise there
                    "mp" => {
                        if args.len() < 2 {
                            return err("mp takes a proof and its premises");
                        }
                        // (in order: a term `{t}` instantiates the leading
                        // `all`, a proof discharges the leading premise)
                        let mut s = self.proof_arg(env, lg, a0)?;
                        for a in &args[1..] {
                            if let Arg::Term(_) = a {
                                let t = self.term_arg(env, Some(a), 0)?;
                                s = Seq::all_elim(env, lg, &s, &t)?;
                                continue;
                            }
                            let x = match a {
                                Arg::Proof(p @ PE::Rule(n, _)) if GOAL_RULES.contains(&n.as_str()) => {
                                    let (prem, _) = imp_parts(env, s.concl())?;
                                    self.by(env, lg, &prem, p)?
                                }
                                // (a nested apply: on its own, or else
                                // against the premise)
                                Arg::Proof(p @ PE::Rule(n, _)) if n == "apply" => {
                                    let (prem, _) = imp_parts(env, s.concl())?;
                                    match self.eval(env, lg, p) {
                                        Ok(x) if x.concl() == &prem => x,
                                        _ => self.by(env, lg, &prem, p)?,
                                    }
                                }
                                _ => self.proof_arg(env, lg, Some(a))?,
                            };
                            s = mp_u(env, &s, &x)?;
                        }
                        Ok(s)
                    }
                    // apply(f, a1, .., an): f's variables (its leading `all`s
                    // and schematic ones) instantiated -- by the terms `{t}`
                    // among the ai, in order, and the rest by matching f's
                    // premises with the proofs among the ai -- then f applied
                    // to the proofs, in order
                    "apply" => self.apply(env, lg, args),
                    "refl" => {
                        let t = self.term_arg(env, a0, 0)?;
                        Seq::refl(env, &t)
                    }
                    // flip(p): p's equation or disequation the other way round
                    // (also under `all`s and premises)
                    "flip" => {
                        let x = self.proof_arg(env, lg, a0)?;
                        flip_seq(env, lg, &x)
                    }
                    "sym" => {
                        let x = self.proof_arg(env, lg, a0)?;
                        Seq::sym(env, &x)
                    }
                    "trans" => {
                        let (x, y) = (self.proof_arg(env, lg, a0)?, self.proof_arg(env, lg, args.get(1))?);
                        Seq::trans(env, &x, &y)
                    }
                    "subst" => {
                        let body = self.term_arg(env, a0, 1)?;
                        let (e, x) = (self.proof_arg(env, lg, args.get(1))?, self.proof_arg(env, lg, args.get(2))?);
                        Seq::subst(env, &e, &body, &x)
                    }
                    // conj(p1, .., pn): p1 && .. && pn (left-nested, as
                    // written), by and_intro -- no tautology search
                    "conj" => {
                        let ps = self.proofs(env, lg, args)?;
                        let mut it = ps.into_iter();
                        let mut acc = it.next().ok_or_else(|| KernelError("conj takes proofs".into()))?;
                        let lemma = facts::seq_of(env, "and_intro").ok_or_else(|| KernelError("`and_intro` (core/logic.core) is not loaded".into()))?;
                        let mut vs = Vec::new();
                        lemma.concl().vars(&mut vs);
                        for p in it {
                            let mut l = lemma.clone();
                            for (v, x) in vs.iter().zip([acc.concl().clone(), p.concl().clone()]) {
                                l = Seq::inst(env, &l, *v, &x)?;
                            }
                            acc = Seq::mp(env, &Seq::mp(env, &l, &acc)?, &p)?;
                        }
                        Ok(acc)
                    }
                    // rewrite(e, p [, {k}..]): e `a = b` (closed: eq_subst) or
                    // `all xs. l = r` (its instances, also under binders);
                    // every occurrence, or the k-th ones
                    "rewrite" => {
                        let (e, x) = (self.proof_arg(env, lg, a0)?, self.proof_arg(env, lg, args.get(1))?);
                        let occ = self.occs(&args[2.min(args.len())..]);
                        match e.concl().node() {
                            Node::App(q, _) if *q == lg.all => Seq::rewrite_under(env, lg, &e, &x, &occ),
                            _ if occ.is_empty() => Seq::rewrite(env, &e, &x),
                            _ => Seq::rewrite_at(env, &e, &x, &occ),
                        }
                    }
                    "unfold" => match a0 {
                        Some(Arg::Proof(PE::Ref(sym))) => Seq::def_eq(env, defined_sym(env, sym)?),
                        _ => err("unfold takes a symbol name"),
                    },
                    "discharge" => {
                        // discharge(p, h): h -> p, without the hypothesis h
                        let p = self.proof_arg(env, lg, a0)?;
                        let h = match args.get(1) {
                            Some(Arg::Proof(PE::Ref(h))) => h,
                            _ => return err("discharge takes a proof and an assumption's name"),
                        };
                        let t = self.facts.iter().rev().find(|(n, _)| n == h).map(|(_, s)| s.concl().clone());
                        let t = t.ok_or_else(|| KernelError(format!("no assumption `{}`", h)))?;
                        if !self.frames.iter().any(|f| matches!(f, Frame::Assume(a) if *a == t)) {
                            return err(format!("`{}` is not an assumption", h));
                        }
                        self.discharged.borrow_mut().push(t.clone());
                        p.discharge(env, &t)
                    }
                    "gen" => {
                        // gen(p, x): generalize over a variable introduced by `fix`
                        let p = self.proof_arg(env, lg, a0)?;
                        let v = match args.get(1) {
                            Some(Arg::Proof(PE::Ref(x))) => self.scope.iter().rev().find(|(n, _)| n == x).map(|(_, v)| *v),
                            _ => None,
                        };
                        let v = v.ok_or_else(|| KernelError("gen takes a proof and a variable".into()))?;
                        Seq::gen(env, lg, &p, v)
                    }
                    // all_elim(p, {t1}, .., {tn})
                    // part(p, {k}): the k-th conjunct (from 1) of p's
                    // `A1 && (A2 && ..)`, by taut
                    "part" => {
                        let p = self.proof_arg(env, lg, a0)?;
                        let k = match self.term_arg(env, args.get(1), 0)?.node() {
                            Node::Nat(n) => n.to_u64().unwrap_or(0) as usize,
                            _ => 0,
                        };
                        let and_s: SymId = env.sym_by_name.get("and").copied().ok_or_else(|| KernelError("part: no `and`".into()))?;
                        let mut t = p.concl().clone();
                        let mut i = 1;
                        loop {
                            match t.node() {
                                Node::App(a, x) if *a == and_s && x.len() == 2 && i < k => {
                                    t = x[1].clone();
                                    i += 1;
                                }
                                Node::App(a, x) if *a == and_s && x.len() == 2 && i == k => {
                                    t = x[0].clone();
                                    break;
                                }
                                _ if i == k => break,
                                _ => return err(format!("part: no conjunct {} (of {})", k, i)),
                            }
                        }
                        if k == 0 {
                            return err("part: conjuncts are counted from 1");
                        }
                        Seq::taut(env, lg, &[&p], &t)
                    }
                    "all_elim" => {
                        let mut p = self.proof_arg(env, lg, a0)?;
                        if args.len() < 2 {
                            return err("all_elim takes a proof and terms");
                        }
                        for a in &args[1..] {
                            let t = self.term_arg(env, Some(a), 0)?;
                            p = head_to(env, p, |t| matches!(t.node(), Node::App(e, _) if *e == lg.all))?;
                            p = Seq::all_elim(env, lg, &p, &t)?;
                        }
                        Ok(p)
                    }
                    "ex_intro" => {
                        let w = self.term_arg(env, a0, 0)?;
                        let body = self.term_arg(env, args.get(1), 1)?;
                        let p = self.proof_arg(env, lg, args.get(2))?;
                        Seq::ex_intro(env, lg, &p, &w, &body)
                    }
                    "witness" => {
                        let x = self.proof_arg(env, lg, a0)?;
                        Seq::witness(env, lg, &x)
                    }
                    "prop" => {
                        let t = self.term_arg(env, a0, 0)?;
                        Seq::prop(env, lg, &t)
                    }
                    "lit" => {
                        let t = self.term_arg(env, a0, 0)?;
                        lit(env, &t)
                    }
                    // expand(p, D1, .., Dn): p with the definitions Di unfolded
                    "expand" => {
                        let p = self.proof_arg(env, lg, a0)?;
                        let syms = self.syms(env, &args[1.min(args.len())..])?;
                        let occ = self.occs(&args[1.min(args.len())..]);
                        let goal = self.unfold_sel(env, p.concl(), &syms, &occ)?;
                        Seq::conv(env, &p, &goal, &syms)
                    }
                    // unsel(h): from `z in set_select(S, x. P)`, `z in S && P(z)`
                    "unsel" => {
                        let h = self.proof_arg(env, lg, a0)?;
                        let (ax, rhs) = self.select_def(env, h.concl())?;
                        Seq::taut(env, lg, &[&ax, &h], &rhs)
                    }
                    // rec({nat_rec(z, k v. s, n)} [, h]): its recursion equation for n = 0,
                    // or for n = m + 1 with h: m in omega
                    // members({S}, h1, ..): the members of S, evaluated on
                    // concrete data, with the equations h_i as known values
                    "members" => {
                        let t = self.term_arg(env, a0, 0)?;
                        let ps = self.proofs(env, lg, &args[1..])?;
                        let refs: Vec<&Seq> = ps.iter().collect();
                        Seq::members(env, lg, &t, &refs)
                    }
                    "rec" => {
                        let t = self.term_arg(env, a0, 0)?;
                        let h = match args.get(1) {
                            Some(_) => Some(self.proof_arg(env, lg, args.get(1))?),
                            None => None,
                        };
                        Seq::nat_rec_eq(env, lg, &t, h.as_ref())
                    }
                    // at({app(L, i)}, p1, ..): the element of a list expression at
                    // i, its bounds shown by arith from the premises
                    // mem_read({t}, p..): `t = r`, t's reads resolved (views,
                    // the kernel's mem_read, the value cleaned)
                    "mem_read" => {
                        let t = self.term_arg(env, a0, 0)?;
                        let ps = self.proofs(env, lg, &args[1.min(args.len())..])?;
                        let ps = split_conj(env, ps)?;
                        self.mem_read_eq(env, lg, &t, &ps, false)
                    }
                    // mem_bytes({bytes_at(M, b, m)}, p..): the read through M's
                    // writes (the kernel's `mem_read`, facts p..)
                    "mem_bytes" => {
                        let t = self.term_arg(env, a0, 0)?;
                        let ps = self.proofs(env, lg, &args[1.min(args.len())..])?;
                        let refs: Vec<&Seq> = ps.iter().collect();
                        Seq::mem_read(env, lg, &refs, &t)
                    }
                    "at" => {
                        let t = self.term_arg(env, a0, 0)?;
                        let ps = self.proofs(env, lg, &args[1.min(args.len())..])?;
                        let refs: Vec<&Seq> = ps.iter().collect();
                        let r = Seq::list_at(env, lg, &refs, &t);
                        // (a defined list constant: its definition's list)
                        let app_s = env.sym_by_name.get("app").copied();
                        match (&r, t.node()) {
                            (Err(_), Node::App(f, a)) if Some(*f) == app_s && a.len() == 2 => match a[0].node() {
                                Node::App(c, ca) if ca.is_empty() && matches!(env.syms[*c as usize].kind, sl_kernel::env::SymKind::Defined { .. }) => {
                                    let d = Seq::def_eq(env, *c)?;
                                    let body = match d.concl().node() {
                                        Node::App(_, e) if e.len() == 2 => e[1].clone(),
                                        _ => return r,
                                    };
                                    let t2 = Term::app(*f, vec![body, a[1].clone()]);
                                    let r2 = Seq::list_at(env, lg, &refs, &t2)?;
                                    Seq::rewrite(env, &Seq::sym(env, &d)?, &r2)
                                }
                                _ => r,
                            },
                            _ => r,
                        }
                    }
                    // list_ext(A in list_type(_), B in list_type(_), len A = len B,
                    //          all i. i in omega -> i < len A -> A[i] = B[i]): A = B
                    "list_ext" => {
                        let ps = self.proofs(env, lg, args)?;
                        match ps.as_slice() {
                            [a, b, l, e] => Seq::list_ext(env, lg, a, b, l, e),
                            _ => err("list_ext takes four proofs"),
                        }
                    }
                    // simp(p): a simplified consequence of p (runs of a program
                    // replaced by the conditions on its outcome)
                    "simp" if args.len() == 1 => {
                        let p = self.proof_arg(env, lg, a0)?;
                        Ok(Seq::simp(env, lg, &p))
                    }
                    // rsimp(h, e1, ..): the fact h simplified
                    "rsimp" => {
                        let h = self.proof_arg(env, lg, a0)?;
                        let rs = self.rsimp_rules(env, lg, &args[1.min(args.len())..])?;
                        self.rsimp_fact(env, lg, h, &rs)
                    }
                    "taut" | "arith" | "simp" | "lists" | "induct" | "defs" | "sel" | "eval" => err(format!("{} needs a goal: `have h: φ by {}(...)`, or inline `(φ by {}(...))`", name, name, name)),
                    other => err(format!("unknown rule `{}`", other)),
                }
            }
        }
    }
}

/// Matches the pattern `p` (its variables `pvars`) with `t`, extending
/// `binds`. A variable applied to distinct bound variables (`v(x0, x1)`
/// under the binders of x0, x1: a higher-order pattern) matches a term
/// whose bound variables from there are among those, abstracted over them.
fn pmatch(env: &Env, p: &Term, t: &Term, pvars: &[VarId], binds: &mut Vec<(VarId, Term)>) -> bool {
    pmatch_at(env, p, t, pvars, binds, 0, true)
}

/// (`delta`: where the heads differ, a definition unfolded)
fn pmatch_at(env: &Env, p: &Term, t: &Term, pvars: &[VarId], binds: &mut Vec<(VarId, Term)>, depth: u32, delta: bool) -> bool {
    match (p.node(), t.node()) {
        (Node::Var(v, a), _) if pvars.contains(v) && pattern_args(a, depth).is_some() => {
            let idx = pattern_args(a, depth).unwrap();
            let Some(val) = abstract_bvars(env, t, &idx, 0) else { return false };
            if let Some((_, b)) = binds.iter().find(|(w, _)| w == v) {
                return *b == val;
            }
            binds.push((*v, val));
            true
        }
        (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => {
            let bs = &env.syms[*f as usize].binders;
            a.iter().zip(b).enumerate().all(|(i, (x, y))| pmatch_at(env, x, y, pvars, binds, depth + bs[i], delta))
        }
        (Node::Var(v, a), Node::Var(w, b)) if v == w && a.len() == b.len() => a.iter().zip(b).all(|(x, y)| pmatch_at(env, x, y, pvars, binds, depth, delta)),
        _ if p == t => true,
        _ if !delta => false,
        // (different heads: the newer definition among them unfolded, once
        // -- implicit unfolding; the fact is converted when applied)
        _ => {
            let head = |x: &Term| match x.node() {
                Node::App(s, _) => Some(*s),
                _ => None,
            };
            let (hp, ht) = (head(p), head(t));
            let up = || unfold_head(env, p, false).filter(|(u, _)| u != p);
            let ut = || unfold_head(env, t, false).filter(|(u, _)| u != t);
            match (up(), ut()) {
                (Some((u, _)), Some(_)) if hp > ht => pmatch_at(env, &u, t, pvars, binds, depth, delta),
                (_, Some((u, _))) => pmatch_at(env, p, &u, pvars, binds, depth, delta),
                (Some((u, _)), None) => pmatch_at(env, &u, t, pvars, binds, depth, delta),
                (None, None) => false,
            }
        }
    }
}

/// the bound variables a pattern variable is applied to (distinct, bound
/// within `depth`)
fn pattern_args(a: &[Term], depth: u32) -> Option<Vec<u32>> {
    let mut idx = Vec::new();
    for x in a {
        match x.node() {
            Node::BVar(i) if *i < depth && !idx.contains(i) => idx.push(*i),
            _ => return None,
        }
    }
    Some(idx)
}

/// `t` (at `depth` binders below the match site) as the value of a
/// variable whose arguments are the bound variables `idx` of the match
/// site: `idx[j]` becomes parameter j; None if another variable bound
/// outside `t` occurs.
fn abstract_bvars(env: &Env, t: &Term, idx: &[u32], depth: u32) -> Option<Term> {
    let k = idx.len() as u32;
    Some(match t.node() {
        Node::BVar(i) if *i < depth => t.clone(),
        Node::BVar(i) => {
            let j = idx.iter().position(|x| *x == i - depth)? as u32;
            Term::bvar(depth + k - 1 - j)
        }
        Node::App(f, a) => {
            let bs = &env.syms[*f as usize].binders;
            t.with_args(a.iter().enumerate().map(|(i, x)| abstract_bvars(env, x, idx, depth + bs[i])).collect::<Option<_>>()?)
        }
        Node::Var(_, a) => t.with_args(a.iter().map(|x| abstract_bvars(env, x, idx, depth)).collect::<Option<_>>()?),
        _ => t.clone(),
    })
}

/// The conjuncts of `t`: the parts of its tree of `and`s (the inner
/// conjunctions too, after the leaves).
fn conjuncts(t: &Term, and: Option<SymId>, out: &mut Vec<Term>) {
    let mut inner = Vec::new();
    fn go(t: &Term, and: Option<SymId>, out: &mut Vec<Term>, inner: &mut Vec<Term>, top: bool) {
        match t.node() {
            Node::App(a, x) if Some(*a) == and => {
                if !top {
                    inner.push(t.clone());
                }
                go(&x[0], and, out, inner, false);
                go(&x[1], and, out, inner, false);
            }
            _ => out.push(t.clone()),
        }
    }
    go(t, and, out, &mut inner, true);
    out.append(&mut inner);
}

/// `t`'s conjuncts as written: `a && b && c` (`(a && b) && c`) is [a, b, c];
/// an explicitly grouped `a && (b && c)` is [a, b && c], and so is a
/// labelled `l: (a && b) && c` [l: a && b, c].
fn conj_parts(env: &Env, t: &Term) -> Vec<Term> {
    let and = env.sym_by_name.get("and").copied();
    let mut out = Vec::new();
    let mut t = t.clone();
    let mut top = true;
    loop {
        match t.node() {
            Node::App(a, x) if Some(*a) == and && (top || t.label().is_none()) => {
                top = false;
                out.push(x[1].clone());
                t = x[0].clone();
            }
            _ => break,
        }
    }
    out.push(t);
    out.reverse();
    out
}

/// facts with their conjunctions split, in order (the memory rules' facts)
fn split_conj(env: &Env, facts: Vec<Seq>) -> KResult<Vec<Seq>> {
    let and_s = env.sym_by_name.get("and").copied();
    let mut out = Vec::new();
    let mut todo: Vec<Seq> = facts.into_iter().rev().collect();
    while let Some(u) = todo.pop() {
        if matches!(u.concl().node(), Node::App(f, a) if Some(*f) == and_s && a.len() == 2) {
            todo.push(and_part(env, &u, true)?);
            todo.push(and_part(env, &u, false)?);
        } else {
            out.push(u);
        }
    }
    Ok(out)
}

/// a disjunction's disjuncts as written (`a || b || c`: three)
fn disj_parts(env: &Env, t: &Term) -> Vec<Term> {
    let or = env.sym_by_name.get("or").copied();
    let mut out = Vec::new();
    let mut t = t.clone();
    while let Node::App(a, x) = t.node() {
        if Some(*a) != or {
            break;
        }
        out.push(x[1].clone());
        t = x[0].clone();
    }
    out.push(t);
    out.reverse();
    out
}

/// `and_left` / `and_right` (core/logic.core) applied to `s`
fn and_part(env: &Env, s: &Seq, right: bool) -> KResult<Seq> {
    let (l, r) = match s.concl().node() {
        Node::App(a, x) if Some(*a) == env.sym_by_name.get("and").copied() => (x[0].clone(), x[1].clone()),
        _ => return err("not a conjunction"),
    };
    let name = if right { "and_right" } else { "and_left" };
    let mut lemma = facts::seq_of(env, name).ok_or_else(|| KernelError(format!("`{}` (core/logic.core) is not loaded", name)))?;
    let mut vs = Vec::new();
    lemma.concl().vars(&mut vs);
    for (v, x) in vs.into_iter().zip([l, r]) {
        lemma = Seq::inst(env, &lemma, v, &x)?;
    }
    Seq::mp(env, &lemma, s)
}

/// The k-th conjunct (from 1, as written: `conj_parts`) of `s`'s statement.
fn conj_get(env: &Env, s: &Seq, k: usize) -> KResult<Seq> {
    let n = conj_parts(env, s.concl()).len();
    if n < 2 || k == 0 || k > n {
        let what = if n < 2 { "is not a conjunction".to_string() } else { format!("has conjuncts 1 to {}", n) };
        return err(format!("conjunct {}: `{}` {}", k, Printer::new(env).short(s.concl()), what));
    }
    // ((p1 && p2) && ..) && pn: left n - k times, then right (unless k = 1)
    let mut s = s.clone();
    for _ in 0..n - k {
        s = and_part(env, &s, false)?;
    }
    if k > 1 {
        s = and_part(env, &s, true)?;
    }
    Ok(s)
}

/// The conjunct labelled `l` of `s`'s statement (a definition at its head
/// unfolded once if it has none: `hi.sM` for `hi: tr.inv(..)`).
fn conj_label(env: &Env, s: &Seq, l: &str) -> KResult<Seq> {
    let find = |s: &Seq| -> KResult<Option<Seq>> {
        let parts = conj_parts(env, s.concl());
        match parts.iter().position(|p| p.label() == Some(l)) {
            Some(_) if parts.len() == 1 => Ok(Some(s.clone())),
            Some(k) => conj_get(env, s, k + 1).map(Some),
            None => Ok(None),
        }
    };
    if let Some(r) = find(s)? {
        return Ok(r);
    }
    let mut s2 = s.clone();
    if let Node::App(f, _) = s.concl().node() {
        if matches!(env.syms[*f as usize].kind, sl_kernel::SymKind::Defined { .. }) {
            let goal = unfold_all(env, s.concl(), &[*f]);
            s2 = Seq::conv(env, s, &goal, &[*f])?;
            if let Some(r) = find(&s2)? {
                return Ok(r);
            }
        }
    }
    let labels: Vec<String> = conj_parts(env, s2.concl()).iter().filter_map(|p| p.label().map(|x| x.to_string())).collect();
    let have = if labels.is_empty() { "none".to_string() } else { labels.join(", ") };
    err(format!("no conjunct labelled `{}` in `{}` (its labels: {})", l, Printer::new(env).short(s.concl()), have))
}

/// The conjuncts labelled `labels` of `s`'s statement, named by their labels
/// (`have {a, b} := P`) or as given (`{x = a}`: x names the conjunct a).
fn conj_labels(env: &Env, s: &Seq, labels: &[&str]) -> KResult<Vec<(String, Seq)>> {
    labels
        .iter()
        .map(|item| {
            let (name, l) = match item.split_once('=') {
                Some((n, l)) => (n.trim(), l.trim()),
                None => (*item, *item),
            };
            Ok((name.to_string(), conj_label(env, s, l)?))
        })
        .collect()
}

/// All conjuncts (as written) of `s`'s statement, in order, named by
/// `names` (`_`: none) -- one pass down the chain.
fn conj_named(env: &Env, s: &Seq, names: &[&str], what: &str) -> KResult<Vec<(String, Seq)>> {
    // (a defined head: unfolded to the conjunction)
    let s = &head_to(env, s.clone(), |t| names.len() < 2 || conj_parts(env, t).len() > 1)?;
    let n = conj_parts(env, s.concl()).len();
    // (a last name `..` / `r..`: the rest of the conjuncts ignored / as
    // one conjunction r)
    let rest = names.last().and_then(|l| l.strip_suffix(".."));
    let m = if rest.is_some() { names.len() - 1 } else { names.len() };
    if (rest.is_none() && n != m) || (rest.is_some() && n <= m) {
        return err(format!("{}: {} names for {} conjuncts of `{}`", what, names.len(), n, Printer::new(env).short(s.concl())));
    }
    let mut parts = Vec::new();
    let mut cur = s.clone();
    for _ in 1..n {
        parts.push(and_part(env, &cur, true)?);
        cur = and_part(env, &cur, false)?;
    }
    parts.push(cur);
    parts.reverse();
    let tail = parts.split_off(m);
    let mut named: Vec<(String, Seq)> = names.iter().zip(parts).filter(|(h, _)| **h != "_").map(|(h, p)| (h.to_string(), p)).collect();
    if let Some(r) = rest.filter(|r| !r.is_empty()) {
        let lemma = facts::seq_of(env, "and_intro").ok_or_else(|| KernelError("`and_intro` (core/logic.core) is not loaded".into()))?;
        let mut vs = Vec::new();
        lemma.concl().vars(&mut vs);
        let mut it = tail.into_iter();
        let mut acc = it.next().unwrap();
        for p in it {
            let mut l = lemma.clone();
            for (v, x) in vs.iter().zip([acc.concl().clone(), p.concl().clone()]) {
                l = Seq::inst(env, &l, *v, &x)?;
            }
            acc = Seq::mp(env, &Seq::mp(env, &l, &acc)?, &p)?;
        }
        named.push((r.to_string(), acc));
    }
    Ok(named)
}

/// The kernel's literal rules, selected by the term's shape.
fn lit(env: &Env, t: &Term) -> KResult<Seq> {
    let b = &env.builtins;
    match t.node() {
        Node::App(s, a) if [b.lit_add, b.lit_sub, b.lit_mul, b.lit_div, b.lit_mod].contains(s) => Seq::kernel(env.lit_compute(*s, &a[0], &a[1])),
        Node::App(s, a) if *s == b.lit_lt => Seq::kernel(env.lit_compare(&a[0], &a[1])),
        Node::App(s, a) if *s == b.is_nat => Seq::kernel(env.lit_is_nat(&a[0])),
        Node::App(s, a) if *s == b.bytes_len => Seq::kernel(env.bytes_len(&a[0])),
        Node::App(s, a) if *s == b.bytes_at => Seq::kernel(env.bytes_at(&a[0], &a[1])),
        _ => err("lit: not a literal operation"),
    }
}

/// `goal by rule`: splits at the last top-level ` by `.
fn rsplit_kw<'a>(s: &'a str, kw: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let bytes = s.as_bytes();
    let mut found = None;
    for i in 0..s.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
        if depth == 0 && s[i..].starts_with(kw) {
            found = Some(i);
        }
    }
    found.map(|i| (&s[..i], &s[i + kw.len()..]))
}

/// `φ := P` -> (φ, P), at the top-level `:=`.
fn split_assign(s: &str) -> Option<(String, &str)> {
    let (g, p) = rsplit_kw(s, ":=")?;
    Some((g.trim().to_string(), p.trim()))
}
