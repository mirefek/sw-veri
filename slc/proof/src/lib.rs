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
//! (Core files also have `abbrev N(a, b) := t`; abbreviations are read as
//! their expansions.)
//!
//! Proof expressions: a fact (`h`, a theorem or axiom), instantiated
//! (`eq_subst[a := t, p := x. x = t]`), or a rule `name(args)`; arguments
//! are proof expressions, terms in braces `{t}`, or (for `unfold`) a symbol.
//!
//! Rules: `mp(ab, a1, ..)` (in order: a proof discharges the leading
//! premise, a term `{t}` instantiates the leading `all`), `refl({t})`, `sym(e)`, `trans(e1, e2)`,
//! `subst({x. φ}, e, p)`, `rewrite(e, p)`, `unfold(sym)`,
//! `all_elim(p, {t1}, ..)`, `ex_intro({w}, {x. φ}, p)`, `witness(p)`,
//! `prop({t})`, `lit({t})`; `apply(f, a1, ..)`: f's leading `all`s and
//! schematic variables instantiated -- by the terms `{t}` among the ai, in
//! order, the rest by matching f's premises with the proofs (or a conjunct
//! of one) -- and f applied to them; with a goal only: `taut(p, ...)`,
//! `ex_intro({w}, p)`. In `mp` and `apply`, a goal rule (`simp(..)`, ..)
//! proves its premise.

use sl_kernel::ext::seq::{defined_sym, unfold_all};
use sl_kernel::ext::simp::LoopHint;
use sl_kernel::ext::{facts, Logic, Seq};
use sl_kernel::syntax::{parse_term, parse_value, Printer, ProofRequest, Prover};
use sl_kernel::{Env, KResult, KernelError, Node, SymId, Term, VarId};

fn err<T>(m: impl Into<String>) -> KResult<T> {
    Err(KernelError(m.into()))
}

/// The proof checker for `sl_kernel::syntax::load_with`.
pub struct ScriptProver;

impl Prover for ScriptProver {
    fn prove(&mut self, env: &mut Env, req: &ProofRequest) -> KResult<Seq> {
        let lg = Logic::new(env)?;
        let st = State::new(req.params.clone(), Vec::new(), Some(req.statement.clone()));
        run_block(env, &lg, st, &req.text, req.line).map_err(|e| KernelError(format!("proof of `{}`, {}", req.name, e.0)))
    }
}

/// Runs the steps of a proof (or of a `proof ... qed` block inside one),
/// then closes its `assume`, `fix` and `obtain` steps. `line`: where the
/// text starts, for messages.
fn run_block(env: &mut Env, lg: &Logic, mut st: State, text: &str, line: usize) -> KResult<Seq> {
    let mut res = Ok(());
    // (STEP_SLOW=secs: the steps taking longer, reported -- a nested
    // block's with it)
    let slow = std::env::var("STEP_SLOW").ok().and_then(|v| v.parse::<f64>().ok());
    for (line_no, body_no, step) in steps(text) {
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
    // the block's `let`s end with it (an outer one it shadowed is back)
    for (name, prev) in st.lets.drain(..).rev() {
        match prev {
            Some(p) => env.abbrevs.insert(name, p),
            None => env.abbrevs.remove(&name),
        };
    }
    res?;
    close(env, lg, st)
}

fn close(env: &Env, lg: &Logic, st: State) -> KResult<Seq> {
    {
        let mut s = st.last.clone().ok_or_else(|| KernelError("the proof is empty".into()))?;
        for fr in st.frames.iter().rev() {
            s = match fr {
                // an assumption already discharged by a step is not discharged again
                Frame::Assume(t) if st.discharged.borrow().contains(t) && !s.hyps().contains(t) => s,
                Frame::Assume(t) => s.discharge(env, t),
                // generalize over x only if it still occurs (a `gen` step may have done it)
                Frame::Fix(v) => {
                    let mut vs = Vec::new();
                    s.concl().vars(&mut vs);
                    if vs.contains(v) { Seq::gen(env, lg, &s, *v)? } else { s }
                }
                // ∃-elimination: ψ(x) ⊢ Q becomes ψ(c) -> Q with c the choice
                // witness of P, then modus ponens with `witness(P)`
                Frame::Obtain(v, prop, ex) => {
                    let s1 = s.discharge(env, prop);
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
            };
        }
        Ok(s)
    }
}

impl State {
    fn new(scope: Vec<(String, VarId)>, facts: Vec<(String, Seq)>, goal: Option<Term>) -> State {
        State { scope, facts, frames: Vec::new(), last: None, discharged: Default::default(), goal, lets: Vec::new() }
    }
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
}

/// Rules that take their statement from the goal.
const GOAL_RULES: &[&str] = &["taut", "arith", "simp", "lists", "induct", "ex_intro", "defs", "sel", "eval"];

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
    /// `P.k`: the k-th conjunct (from 1, as written) of what P proves
    Conj(Box<PE>, usize),
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
        // R(args).k.j: conjuncts of its result
        while let Some(r) = s[pos..].strip_prefix('.') {
            let n = r.find(|c: char| !c.is_ascii_digit()).unwrap_or(r.len());
            let Ok(k) = r[..n].parse::<usize>() else { break };
            pe = PE::Conj(Box::new(pe), k);
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
        // h.k: the k-th conjunct of h (h.k.j: of that)
        if let Some((h, k)) = name.rsplit_once('.') {
            if let Ok(k) = k.parse::<usize>() {
                return conj_get(env, &self.fact(env, h)?, k);
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
                    (Some(n.trim().to_string()), self.term(env, g)?)
                }
                "show" if rest.trim().is_empty() => {
                    (None, self.goal.clone().ok_or_else(|| KernelError("no current goal here: write `show φ proof`".into()))?)
                }
                "show" => (None, self.term(env, rest)?),
                _ => return err("a sub-proof belongs to `have NAME: φ` or `show [φ]`"),
            };
            let child = State::new(self.scope.clone(), self.facts.clone(), Some(goal.clone()));
            let s = run_block(env, lg, child, body, body_line)?;
            let s = self.check(env, s, &goal)?;
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
                    self.goal = match self.goal.as_ref().map(|g| g.node()) {
                        Some(Node::App(i, a)) if *i == env.builtins.imp && a[0] == t => Some(a[1].clone()),
                        _ => None,
                    };
                    self.frames.push(Frame::Assume(t));
                }
            }
            // fix x  /  fix x y ..
            "fix" => {
                for n in rest.split_whitespace() {
                    let v = env.new_var(n, 0);
                    self.scope.push((n.to_string(), v));
                    self.goal = match self.goal.as_ref().map(|g| g.node()) {
                        Some(Node::App(a, b)) if *a == lg.all => Some(b[0].instantiate_params(&[Term::var(v, vec![])], &env.binders_fn())),
                        _ => None,
                    };
                    self.frames.push(Frame::Fix(v));
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
                if hs.len() == 1 {
                    self.facts.push((hs[0].to_string(), h));
                } else {
                    let named = conj_named(env, &h, &hs, "obtain")?;
                    self.facts.extend(named);
                }
            }
            // have h1 .. hk [: φ] (:= P | by R): its k conjuncts as written
            // (`_` names none)
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
                    if let Some(g) = goal {
                        let g = self.term(env, &g)?;
                        if s.concl() != &g {
                            let pp = Printer::new(env);
                            return err(format!("this proves `{}`, not `{}`\n  {}", pp.short(s.concl()), pp.short(&g), pp.mismatch(&g, s.concl())));
                        }
                    }
                    s
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
            "taut" => {
                let ps = self.proofs(env, lg, args)?;
                let refs: Vec<&Seq> = ps.iter().collect();
                Seq::taut(env, lg, &refs, goal)
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
                let unfolded = unfold_all(env, goal, &syms);
                let s = match p {
                    PE::Rule(n, _) if GOAL_RULES.contains(&n.as_str()) => self.by(env, lg, &unfolded, p)?,
                    _ => self.eval(env, lg, p)?,
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
        let mut s = self.proof_arg(env, lg, args.first())?;
        let mut terms = Vec::new();
        // the proofs; a goal rule (`simp(..)`, `taut(..)`, ..) proves its
        // premise, instantiated, once the others have fixed the variables
        let mut proofs: Vec<Option<Seq>> = Vec::new();
        let mut goal_args: Vec<(usize, &PE)> = Vec::new();
        for a in &args[1..] {
            match a {
                Arg::Term(_) => terms.push(self.term_arg(env, Some(a), 0)?),
                Arg::Proof(p @ PE::Rule(n, _)) if GOAL_RULES.contains(&n.as_str()) => {
                    goal_args.push((proofs.len(), p));
                    proofs.push(None);
                }
                Arg::Proof(_) => proofs.push(Some(self.proof_arg(env, lg, Some(a))?)),
            }
        }
        // the pattern variables: f's schematic variables (not fixed in this
        // proof, not in its hypotheses), then one per leading `all`
        let mut pvars: Vec<VarId> = Vec::new();
        {
            let (mut vs, mut hv) = (Vec::new(), Vec::new());
            s.concl().vars(&mut vs);
            for h in s.hyps() {
                h.vars(&mut hv);
            }
            for v in vs {
                if !hv.contains(&v) && !self.scope.iter().any(|(_, w)| *w == v) && env.vars[v as usize].arity == 0 && !pvars.contains(&v) {
                    pvars.push(v);
                }
            }
        }
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
        // match the premises
        let mut binds: Vec<(VarId, Term)> = Vec::new();
        let mut c = s.concl().clone();
        let and = env.sym_by_name.get("and").copied();
        for (i, p) in proofs.iter_mut().enumerate() {
            let (a, b) = imp_parts(env, &c).map_err(|_| KernelError(format!("apply: no premise for the proof number {}", i + 1)))?;
            c = b;
            let Some(p) = p else { continue };
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
                    if vs.contains(v) {
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
            for (i, pe) in goal_args {
                proofs[i] = Some(self.by(env, lg, &ps[i], pe).map_err(|e| KernelError(format!("apply: premise {}: {}", i + 1, e.0)))?);
            }
        }
        for p in proofs.iter().flatten() {
            s = Seq::mp(env, &s, p)?;
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
            .map(|a| match a {
                Arg::Proof(PE::Ref(n)) => defined_sym(env, n),
                _ => err("expected the name of a definition"),
            })
            .collect()
    }

    fn check(&self, env: &Env, s: Seq, goal: &Term) -> KResult<Seq> {
        if s.concl() != goal {
            let pp = Printer::new(env);
            return err(format!("this proves `{}`, not `{}`\n  {}", pp.short(s.concl()), pp.short(goal), pp.mismatch(goal, s.concl())));
        }
        Ok(s)
    }

    fn eval(&self, env: &mut Env, lg: &Logic, p: &PE) -> KResult<Seq> {
        match p {
            PE::Ref(name) => self.fact(env, name),
            PE::Conj(p, k) => {
                let s = self.eval(env, lg, p)?;
                conj_get(env, &s, *k)
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
                for (vname, text) in insts {
                    let cands: Vec<VarId> = vs.iter().copied().filter(|v| env.vars[*v as usize].name == *vname).collect();
                    let v = match cands.as_slice() {
                        [v] => *v,
                        [] => return err(format!("no variable `{}` to instantiate", vname)),
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
                                _ => self.proof_arg(env, lg, Some(a))?,
                            };
                            s = Seq::mp(env, &s, &x)?;
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
                    "rewrite" => {
                        let (e, x) = (self.proof_arg(env, lg, a0)?, self.proof_arg(env, lg, args.get(1))?);
                        Seq::rewrite(env, &e, &x)
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
                        Ok(p.discharge(env, &t))
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
                        let goal = unfold_all(env, p.concl(), &syms);
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
                    "at" => {
                        let t = self.term_arg(env, a0, 0)?;
                        let ps = self.proofs(env, lg, &args[1.min(args.len())..])?;
                        let refs: Vec<&Seq> = ps.iter().collect();
                        Seq::list_at(env, lg, &refs, &t)
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
                    "taut" | "arith" | "simp" | "lists" | "induct" | "defs" | "sel" | "eval" => err(format!("{} needs a goal: `have h: φ by {}(...)`", name, name)),
                    other => err(format!("unknown rule `{}`", other)),
                }
            }
        }
    }
}

/// Matches the pattern `p` (its variables `pvars`, first-order) with `t`,
/// extending `binds`.
fn pmatch(env: &Env, p: &Term, t: &Term, pvars: &[VarId], binds: &mut Vec<(VarId, Term)>) -> bool {
    match (p.node(), t.node()) {
        (Node::Var(v, a), _) if a.is_empty() && pvars.contains(v) => {
            if let Some((_, b)) = binds.iter().find(|(w, _)| w == v) {
                return b == t;
            }
            if loose(env, t, 0) {
                return false;
            }
            binds.push((*v, t.clone()));
            true
        }
        (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => a.iter().zip(b).all(|(x, y)| pmatch(env, x, y, pvars, binds)),
        (Node::Var(v, a), Node::Var(w, b)) if v == w && a.len() == b.len() => a.iter().zip(b).all(|(x, y)| pmatch(env, x, y, pvars, binds)),
        _ => p == t,
    }
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
/// an explicitly grouped `a && (b && c)` is [a, b && c].
fn conj_parts(env: &Env, t: &Term) -> Vec<Term> {
    let and = env.sym_by_name.get("and").copied();
    let mut out = Vec::new();
    let mut t = t.clone();
    loop {
        match t.node() {
            Node::App(a, x) if Some(*a) == and => {
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

/// All conjuncts (as written) of `s`'s statement, in order, named by
/// `names` (`_`: none) -- one pass down the chain.
fn conj_named(env: &Env, s: &Seq, names: &[&str], what: &str) -> KResult<Vec<(String, Seq)>> {
    let n = conj_parts(env, s.concl()).len();
    if n != names.len() {
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
    Ok(names.iter().zip(parts).filter(|(h, _)| **h != "_").map(|(h, p)| (h.to_string(), p)).collect())
}

/// `t` has bound variables pointing outside it (beyond `depth` binders).
fn loose(env: &Env, t: &Term, depth: u32) -> bool {
    match t.node() {
        Node::BVar(i) => *i >= depth,
        Node::App(f, a) => a.iter().enumerate().any(|(i, x)| loose(env, x, depth + env.syms[*f as usize].binders[i])),
        Node::Var(_, a) => a.iter().any(|x| loose(env, x, depth)),
        _ => false,
    }
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
