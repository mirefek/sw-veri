//! The walk's path helpers: the code's successors of an instruction,
//! a branch's split (the facts and variables before it), the homes' map
//! entries, the facts every path reaching a point has, the locals'
//! components. (The structured form's statement joins, which used them
//! first, are retired: C1 is against the readable CFG, slc/cli/src/c1/cfg.rs.)

use super::*;

/// a branch on the path: the facts and calls' results then (their
/// counts), the variables then (those made after are the branch's own)
#[derive(Clone, PartialEq)]
pub(super) struct Split {
    hyps: usize,
    facts: usize,
    mark: usize,
}

impl<'e> Gen<'e> {
    /// the split of a branch at st
    pub(super) fn split(&self, st: &St) -> Split {
        Split { hyps: st.hyps.len(), facts: st.facts.len(), mark: self.env.vars.len() }
    }

    /// the code's successors of the instruction at a
    pub(super) fn succs(&self, a: u128) -> Vec<u128> {
        let Some(i) = self.insns.get(&a) else { return Vec::new() };
        let a2 = (a + i.len) % P64;
        match i.row {
            // ret
            122 => Vec::new(),
            // jmp rel8
            125 => match nat(&i.fields) {
                Some(r) => vec![(a2 + if r & 0x80 != 0 { r + 0xffff_ffff_ffff_ff00 } else { r }) % P64],
                None => Vec::new(),
            },
            // jmp rel32
            124 => match nat(&i.fields) {
                Some(r) => vec![(a2 + if r & 0x8000_0000 != 0 { r + 0xffff_ffff_0000_0000 } else { r }) % P64],
                None => Vec::new(),
            },
            // jcc rel8, rel32
            127 | 128 => match self.jcc(a) {
                Ok((_, _, a3, tt, _)) => vec![a3, tt],
                Err(_) => vec![a2],
            },
            _ => vec![a2],
        }
    }

    /// the homes' map term `hst`: its entries in order (key, bytes, value)
    pub(super) fn home_entries(&self, hst: &Term) -> Option<Vec<(u128, u128, Term)>> {
        let mut out = Vec::new();
        let mut m = hst.clone();
        while let Some((parent, k, pv)) = upd_parts(self, &m) {
            let x = self.app(&pv, "pair", 2)?;
            out.push((nat(&k)?, nat(&x[0])?, x[1].clone()));
            m = parent;
        }
        self.app(&m, "empty", 0)?;
        out.reverse();
        Some(out)
    }

    /// the facts at st that every path reaching its point has, for a claim
    /// there over the locals (now y0), its terms `ts`: those before the
    /// path's first branch, not of its own values (made after that branch,
    /// but the claim's variables `vs`), nor of the walk's values in the
    /// locals (the claim's premise says what it knows of them), nor of
    /// values the claim does not mention
    pub(super) fn shared_facts(&self, st: &St, y0: &Term, vs: &[VarId], ts: &[&Term]) -> (Vec<(Term, Seq)>, Vec<Seq>, Vec<Seq>) {
        let mark = st.splits.first().map(|sp| sp.mark).unwrap_or(self.env.vars.len());
        let mut yvs = Vec::new();
        self.expand(y0).vars(&mut yvs);
        yvs.retain(|v| (*v as usize) >= self.vmark0);
        let mut tvs = vs.to_vec();
        for t in ts {
            self.expand(t).vars(&mut tvs);
        }
        let keep = |t: &Term| {
            let mut tv = Vec::new();
            t.vars(&mut tv);
            !tv.iter().any(|v| ((*v as usize) >= mark && !vs.contains(v)) || yvs.contains(v) || ((*v as usize) >= self.vmark0 && !tvs.contains(v)))
        };
        let (nh, nf) = st.splits.first().map(|sp| (sp.hyps, sp.facts)).unwrap_or((st.hyps.len(), st.facts.len()));
        let hyps = st.hyps[..nh.min(st.hyps.len())].iter().filter(|h| keep(&self.expand(&h.0))).cloned().collect();
        let facts = st.facts[..nf.min(st.facts.len())].iter().filter(|f| keep(f.concl())).cloned().collect();
        let lfx = st.lfx.iter().filter(|f| keep(f.concl())).cloned().collect();
        (hyps, facts, lfx)
    }

    /// the locals' components: `pair(a, pair(b, .. z))` as a, b, .. z
    pub(super) fn locals_of(&self, y: &Term) -> Vec<Term> {
        let mut comps = Vec::new();
        let mut cur = y.clone();
        while let Some(pa) = self.app(&cur, "pair", 2).map(|x| x.to_vec()) {
            comps.push(pa[0].clone());
            cur = pa[1].clone();
        }
        comps.push(cur);
        comps
    }
}
