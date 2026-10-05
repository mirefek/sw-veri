//! The search inventory (a diagnostic, not a rule): with `INVENTORY=1`,
//! each outermost call of a searching procedure -- simp, arith, tautology
//! -- is reported on stderr with where the extensions called it from (the
//! innermost frames in `ext/simp/`), its result, its time and its goal:
//!
//! `inv <TAB> kind <TAB> site < caller < .. <TAB> ok|failed <TAB> secs <TAB> goal`
//!
//! Calls inside another search (simp's arith) are its, not reported.

use crate::env::Env;
use crate::term::Term;
use std::cell::Cell;
use std::sync::OnceLock;

thread_local! {
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

fn on() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("INVENTORY").is_ok())
}

/// The extensions' frames calling (innermost first, at most three).
fn site() -> String {
    let bt = std::backtrace::Backtrace::force_capture().to_string();
    let mut frames: Vec<String> = Vec::new();
    for line in bt.lines() {
        let l = line.trim();
        let Some(at) = l.strip_prefix("at ") else { continue };
        let Some(i) = at.find("ext/simp") else { continue };
        let loc = &at[i + "ext/".len()..];
        // (file:line, without the column)
        let loc = match loc.rfind(':') {
            Some(c) if loc[..c].contains(':') => &loc[..c],
            _ => loc,
        };
        if loc.starts_with("simp.rs") {
            continue;
        }
        if frames.last().is_none_or(|f| f != loc) {
            frames.push(loc.to_string());
        }
        if frames.len() == 3 {
            break;
        }
    }
    if frames.is_empty() {
        "other".into()
    } else {
        frames.join(" < ")
    }
}

/// f's result, the call reported if outermost.
pub(crate) fn measure<T, E>(kind: &str, env: &Env, goal: &Term, f: impl FnOnce() -> Result<T, E>) -> Result<T, E> {
    if !on() {
        return f();
    }
    let outer = DEPTH.with(|d| {
        let v = d.get();
        d.set(v + 1);
        v == 0
    });
    let t0 = std::time::Instant::now();
    let r = f();
    DEPTH.with(|d| d.set(d.get() - 1));
    if outer {
        let dt = t0.elapsed().as_secs_f64();
        let g: String = crate::syntax::Printer::new(env).term(goal).chars().take(160).collect();
        eprintln!("inv\t{}\t{}\t{}\t{:.4}\t{}", kind, site(), if r.is_ok() { "ok" } else { "failed" }, dt, g.replace('\t', " "));
    }
    r
}
