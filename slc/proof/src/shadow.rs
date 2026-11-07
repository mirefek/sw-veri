//! The simp shadow (a diagnostic, not a rule): with `SLC_SHADOW=1`, each
//! `simp` goal is also tried by the determined procedures, and reported
//! on stderr:
//!
//! `shadow <TAB> line <TAB> simp ok|failed <TAB> secs <TAB> rsimp <TAB> secs
//!  <TAB> rsimp+arith <TAB> secs <TAB> eval <TAB> secs <TAB> args <TAB> goal`
//!
//! with each procedure's result `ok`, `failed` or `-` (not tried: a simp
//! with loop hints, `keep` or `lets`). It tells which simp calls rsimp
//! (with the same facts) already does, and how fast: the data for
//! retiring simp (docs/todo.md §1.1).

use super::*;
use std::cell::Cell;
use std::sync::OnceLock;

thread_local! {
    static LINE: Cell<usize> = const { Cell::new(0) };
    /// the simp call's number within its step (from 0, in evaluation order)
    static CALL: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("SLC_SHADOW").is_ok())
}

/// the line of the proof step being run
pub(crate) fn set_line(l: usize) {
    if on() {
        LINE.with(|c| c.set(l));
        CALL.with(|c| c.set(0));
    }
}

impl State {
    /// A simp goal as `rsimp` proves it (`rsimp_goal`), and how
    pub(crate) fn untrusted_simp(&self, env: &mut Env, lg: &Logic, goal: &Term, args: &[Arg], _facts: &[Seq]) -> KResult<(Seq, &'static str)> {
        // (simp's `keep(..)` dropped: rsimp unfolds only what it is given)
        let args: Vec<Arg> = args.iter().filter(|a| !matches!(a, Arg::Proof(PE::Rule(r, _)) if r == "keep")).cloned().collect();
        let rs = self.rsimp_rules(env, lg, &args)?;
        self.rsimp_goal(env, lg, goal, &rs)
    }
}

fn timed<T>(f: impl FnOnce() -> KResult<T>) -> (&'static str, f64) {
    let t0 = std::time::Instant::now();
    let r = f();
    (if r.is_ok() { "ok" } else { "failed" }, t0.elapsed().as_secs_f64())
}

impl State {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn shadow_simp(&self, env: &mut Env, lg: &Logic, goal: &Term, args: &[Arg], facts: &[Seq], plain: bool, simp_ok: bool, simp_t: f64) {
        let refs: Vec<&Seq> = facts.iter().collect();
        let (mut a, mut b, mut c) = (("-", 0.0), ("-", 0.0), ("-", 0.0));
        let call = CALL.with(|c| {
            let v = c.get();
            c.set(v + 1);
            v
        });
        // (SLC_SHADOW=rsimp: the replacement's attempt, within 0.1 s:
        // `shadow-r <TAB> line <TAB> call <TAB> simp secs <TAB> by <TAB> secs
        // <TAB> goal`, by `-` for a program path's simp, `failed` if none)
        if std::env::var("SLC_SHADOW").is_ok_and(|v| v == "rsimp") {
            let t0 = std::time::Instant::now();
            let mut by = if plain { super::rsimp::with_deadline(0.1, || self.untrusted_simp(env, lg, goal, args, facts)).map(|(_, b)| b).unwrap_or("failed") } else { "-" };
            // (what the trusted eval would prove of the rest: an untrusted
            // evaluation's target)
            let closed = {
                let mut vs = Vec::new();
                goal.vars(&mut vs);
                vs.is_empty()
            };
            if by == "failed" && closed {
                by = if Seq::eval_goal(env, lg, &[], goal).is_ok() { "failed-eval" } else { "failed-closed" };
            }
            let g: String = Printer::new(env).term(goal).chars().take(160).collect();
            // (the call as written, up to whitespace: where it is in its step)
            let text = format!("simp({})", super::args_text(args)).replace(['\t', '\n'], " ");
            eprintln!("shadow-r\t{}\t{}\t{:.4}\t{}\t{:.4}\t{}\t{}", LINE.with(|l| l.get()), call, simp_t, by, t0.elapsed().as_secs_f64(), g.replace(['\t', '\n'], " "), text);
            return;
        }
        // (SLC_SHADOW=types: the typing procedure alone, on membership goals)
        if std::env::var("SLC_SHADOW").is_ok_and(|v| v == "types") {
            if !matches!(goal.node(), Node::App(i, _) if *i == lg.in_) && !matches!(goal.node(), Node::App(f, _) if env.syms[*f as usize].name == "is_fun") {
                return;
            }
            let t = timed(|| {
                let mut ty = super::types::Typer::new(env, self, lg, facts)?;
                ty.prove(env, goal)
            });
            let g: String = Printer::new(env).term(goal).chars().take(200).collect();
            eprintln!("shadow-types\t{}\t{}\t{:.4}\t{}\t{:.4}\t{}", LINE.with(|l| l.get()), if simp_ok { "ok" } else { "failed" }, simp_t, t.0, t.1, g.replace(['\t', '\n'], " "));
            return;
        }
        if plain {
            a = timed(|| {
                let rs = self.rsimp_rules(env, lg, args)?;
                self.rsimp_close(env, lg, goal, &rs, 0)
            });
            // the normal form, then taut / arith with the same facts
            b = timed(|| {
                let rs = self.rsimp_rules(env, lg, args)?;
                let e = self.rsimp_eq(env, lg, goal, &rs, 0)?;
                let n = match e.concl().node() {
                    Node::App(_, x) => x[1].clone(),
                    _ => return err("rsimp: not an equation"),
                };
                let mut more: Vec<Seq> = Vec::new();
                for f in facts {
                    more.push(self.rsimp_fact(env, lg, f.clone(), &rs).unwrap_or_else(|_| f.clone()));
                }
                let mr: Vec<&Seq> = more.iter().collect();
                Seq::taut(env, lg, &mr, &n).or_else(|_| Seq::arith(env, lg, &mr, &n))
            });
            c = timed(|| Seq::eval_goal(env, lg, &refs, goal));
        }
        let g: String = Printer::new(env).term(goal).chars().take(200).collect();
        eprintln!(
            "shadow\t{}\t{}\t{:.4}\t{}\t{:.4}\t{}\t{:.4}\t{}\t{:.4}\t{}\t{}",
            LINE.with(|l| l.get()),
            if simp_ok { "ok" } else { "failed" },
            simp_t,
            a.0,
            a.1,
            b.0,
            b.1,
            c.0,
            c.1,
            args.len(),
            g.replace(['\t', '\n'], " ")
        );
    }
}
