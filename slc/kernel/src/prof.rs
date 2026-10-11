//! Timing for profiling (C1_PROF set): time and calls per named part,
//! inclusive, a part within itself timed once. Not part of the logic.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};
thread_local! {
    static T: RefCell<BTreeMap<&'static str, (Duration, u64)>> = RefCell::new(BTreeMap::new());
    static ON: bool = std::env::var("C1_PROF").is_ok();
    static ACTIVE: RefCell<Vec<&'static str>> = RefCell::new(Vec::new());
}
pub struct G(&'static str, Option<Instant>);
/// (a part within itself -- a recursive function's: timed once, the
/// outermost)
pub fn g(n: &'static str) -> G {
    if !ON.with(|o| *o) || ACTIVE.with(|a| a.borrow().contains(&n)) {
        return G(n, None);
    }
    ACTIVE.with(|a| a.borrow_mut().push(n));
    G(n, Some(Instant::now()))
}
impl Drop for G {
    fn drop(&mut self) {
        if let Some(t) = self.1 {
            ACTIVE.with(|a| {
                let mut a = a.borrow_mut();
                if let Some(i) = a.iter().rposition(|x| *x == self.0) {
                    a.remove(i);
                }
            });
            let d = t.elapsed();
            T.with(|m| {
                let mut m = m.borrow_mut();
                let e = m.entry(self.0).or_default();
                e.0 += d;
                e.1 += 1;
            });
        }
    }
}
/// the report at the end of a scope (a function's C1)
pub struct Rep(pub String);
impl Drop for Rep {
    fn drop(&mut self) {
        if ON.with(|o| *o) {
            report(&self.0)
        }
    }
}
pub fn report(f: &str) {
    T.with(|m| {
        let mut v: Vec<_> = m.borrow().iter().map(|(k, x)| (*k, *x)).collect();
        v.sort_by(|a, b| b.1 .0.cmp(&a.1 .0));
        for (k, (d, n)) in v {
            eprintln!("c1 prof {f}: {:>9.3}s {:>9} {}", d.as_secs_f64(), n, k);
        }
        m.borrow_mut().clear();
    })
}
