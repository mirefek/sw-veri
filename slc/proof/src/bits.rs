//! `bitwise`: goals about words, bit by bit.
//!
//! A word equation `L = R` (n-bit words) is reduced by extensionality
//! (core/bits.core's `bits_ext`) to `bit(L, i) <-> bit(R, i)` for a fresh
//! index i < n. Each bit `bit(W, I)` met is then explained by a registered
//! bit rule (`bit_rule NAME`: `H.. -> (bit(P, j) <-> φ)`), the first whose
//! P matches W: its instance's premises shown from the facts (a fact, or
//! `arith`), its φ's bits explained in turn. Matching reads a numeral as
//! `pow2(k)`, `pow2(k) - 1` or (odd) `x * 2^t + (2^j - 1)` where the rule has
//! one, and a product either
//! way round; the instance's word is shown equal to W by `arith`. No
//! rewriting: the explanations, instances of the facts' `all`s at the
//! indices met, and of `bit_cong` (equal indices, the same bit) for the
//! bits left, are the premises of one `arith` call, which decides the
//! goal propositionally and over the indices.
//!
//! Untrusted: lemma instances, `mp`, and `arith`.

use super::*;

/// bits explained at most (a rule set that grows terms without end)
const LIMIT: usize = 200;

impl State {
    /// `bitwise([{n},] p..)`: the goal (a word equation of n-bit words, or a
    /// proposition about bits) from the facts p..
    pub(crate) fn bitwise_goal(&self, env: &mut Env, lg: &Logic, goal: &Term, facts: &[Seq], width: Option<Term>) -> KResult<Seq> {
        let Some((l, r)) = eq_sides(env, goal) else {
            return self.bitwise_prop(env, lg, goal, facts);
        };
        let n = match width.or_else(|| op_width(env, &l)).or_else(|| op_width(env, &r)) {
            Some(n) => n,
            None => return err("bitwise: the words' width not known: give it, `bitwise({n}, ..)`"),
        };
        let g = |s: &str| env.sym_by_name.get(s).copied().ok_or_else(|| KernelError(format!("bitwise: needs `{}` (core/bits.core)", s)));
        let (bit, bits, omega, int_lt) = (g("bit")?, g("bits")?, g("omega")?, g("int_lt")?);
        let in_omega = |t: &Term| Term::app(lg.in_, vec![t.clone(), Term::app(omega, vec![])]);
        let hn = self.bit_premise(env, lg, &in_omega(&n), facts)?;
        let hl = self.bit_premise(env, lg, &Term::app(lg.in_, vec![l.clone(), Term::app(bits, vec![n.clone()])]), facts)?;
        let hr = self.bit_premise(env, lg, &Term::app(lg.in_, vec![r.clone(), Term::app(bits, vec![n.clone()])]), facts)?;
        // at a fresh i < n
        let v = env.new_var("i", 0);
        let i = Term::var(v, vec![]);
        let (ai, al) = (in_omega(&i), Term::app(int_lt, vec![i.clone(), n.clone()]));
        let mut fs = facts.to_vec();
        fs.push(Seq::assume(env, ai.clone())?);
        fs.push(Seq::assume(env, al.clone())?);
        let iff = env.sym_by_name.get("iff").copied().ok_or_else(|| KernelError("bitwise: no `iff`".into()))?;
        let g2 = Term::app(iff, vec![Term::app(bit, vec![l.clone(), i.clone()]), Term::app(bit, vec![r.clone(), i.clone()])]);
        let p = self.bitwise_prop(env, lg, &g2, &fs)?;
        let p = Seq::gen(env, lg, &p.discharge(env, &al)?.discharge(env, &ai)?, v)?;
        let ext = facts::seq_of(env, "bits_ext").ok_or_else(|| KernelError("bitwise: needs `bits_ext` (core/bits.core)".into()))?;
        let e = Seq::mp(env, &Seq::all_elim(env, lg, &ext, &n)?, &hn)?;
        let e = Seq::all_elim(env, lg, &Seq::all_elim(env, lg, &e, &l)?, &r)?;
        let e = Seq::mp(env, &Seq::mp(env, &Seq::mp(env, &e, &hl)?, &hr)?, &p)?;
        Ok(e)
    }

    /// a proposition about bits: its bits explained, then `arith`
    fn bitwise_prop(&self, env: &mut Env, lg: &Logic, goal: &Term, facts: &[Seq]) -> KResult<Seq> {
        let bit = env.sym_by_name.get("bit").copied();
        let mut todo = Vec::new();
        collect_bits(goal, bit, &mut todo);
        let mut seen: Vec<Term> = Vec::new();
        let mut extra: Vec<Seq> = Vec::new();
        // (the bits no rule explains)
        let mut leaves: Vec<Term> = Vec::new();
        while let Some(t) = todo.pop() {
            if seen.contains(&t) {
                continue;
            }
            if seen.len() >= LIMIT {
                return err("bitwise: too many bits to explain");
            }
            seen.push(t.clone());
            match self.bit_explain(env, lg, &t, facts) {
                Some(s) => {
                    if let Node::App(_, a) = s.concl().node() {
                        collect_bits(&a[1], bit, &mut todo);
                    }
                    extra.push(s);
                }
                None => leaves.push(t),
            }
        }
        // the facts' `all`s at the indices met
        let mut idx: Vec<Term> = Vec::new();
        for t in seen.iter() {
            if let Node::App(_, a) = t.node() {
                if !idx.contains(&a[1]) {
                    idx.push(a[1].clone());
                }
            }
        }
        for f in facts {
            if !matches!(f.concl().node(), Node::App(q, _) if *q == lg.all) || !mentions_sym(f.concl(), bit) {
                continue;
            }
            for i in &idx {
                if let Ok(s) = Seq::all_elim(env, lg, f, i) {
                    extra.push(s);
                }
            }
        }
        // equal indices, the same bit (the bits left, and the facts')
        {
            let bf = env.binders_fn();
            for f in facts.iter().chain(extra.iter()) {
                let mut fb = Vec::new();
                collect_bits(f.concl(), bit, &mut fb);
                for t in fb {
                    if t.loose_depth(&bf) == 0 && !leaves.contains(&t) && !seen.contains(&t) {
                        leaves.push(t);
                    }
                }
            }
        }
        if let Some(cong) = facts::seq_of(env, "bit_cong") {
            let (c0, pv, _) = open_rule(env, lg, &cong)?;
            // (its variables x, a, b by name)
            let by_name = |n: &str| pv.iter().copied().find(|v| env.var(*v).name == n);
            let (Some(vx), Some(va), Some(vb)) = (by_name("x"), by_name("a"), by_name("b")) else {
                return err("bitwise: `bit_cong(x, a, b)` expected");
            };
            for (a, b) in leaves.iter().enumerate().flat_map(|(k, a)| leaves[k + 1..].iter().map(move |b| (a, b))) {
                let (Node::App(_, x), Node::App(_, y)) = (a.node(), b.node()) else { continue };
                if x[0] != y[0] || x[1] == y[1] {
                    continue;
                }
                let mut s = c0.clone();
                for (v, t) in [(vx, &x[0]), (va, &x[1]), (vb, &y[1])] {
                    s = Seq::inst(env, &s, v, t)?;
                }
                extra.push(s);
            }
        }
        // a word's bits at and above its width: none (`bit_high`)
        if let Some(high) = facts::seq_of(env, "bit_high") {
            let bits_s = env.sym_by_name.get("bits").copied();
            let widths: Vec<(Term, Term)> = facts
                .iter()
                .filter_map(|f| match f.concl().node() {
                    Node::App(i, a) if *i == lg.in_ => match a[1].node() {
                        Node::App(b, w) if Some(*b) == bits_s => Some((a[0].clone(), w[0].clone())),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            // (the facts' words; and every word operation met, its width)
            for t in leaves.iter().chain(seen.iter()).cloned().collect::<Vec<_>>() {
                let Node::App(_, ta) = t.node() else { continue };
                let mut ws: Vec<Term> = widths.iter().filter(|(x, _)| *x == ta[0]).map(|(_, n)| n.clone()).collect();
                if let Some(n) = op_width(env, &ta[0]) {
                    if !ws.contains(&n) {
                        ws.push(n);
                    }
                }
                for n in ws {
                    if let Ok(s) = self.bit_high_at(env, lg, &high, &ta[0], &n, &ta[1], facts) {
                        extra.push(s);
                    }
                }
            }
        }
        let mut ps: Vec<&Seq> = facts.iter().collect();
        ps.extend(extra.iter());
        Seq::arith(env, lg, &ps, goal).map_err(|e| KernelError(format!("bitwise: {} ({} bits explained, {} not)", e.0, extra.len(), leaves.len())))
    }

    /// `int_le(n, i) -> !bit(x, i)` (x in bits(n)): bit_high's other
    /// premises shown
    #[allow(clippy::too_many_arguments)]
    fn bit_high_at(&self, env: &mut Env, lg: &Logic, high: &Seq, x: &Term, n: &Term, i: &Term, facts: &[Seq]) -> KResult<Seq> {
        let (s, pv, _) = open_rule(env, lg, high)?;
        let by_name = |m: &str| pv.iter().copied().find(|v| env.var(*v).name == m);
        let (Some(vx), Some(vn), Some(vi)) = (by_name("x"), by_name("n"), by_name("i")) else {
            return err("bitwise: `bit_high(x, n, i)` expected");
        };
        let mut s = s;
        for (v, t) in [(vx, x), (vn, n), (vi, i)] {
            s = Seq::inst(env, &s, v, t)?;
        }
        // (x's range first: a fact, or its operation's lemma)
        let bits_s = env.sym_by_name.get("bits").copied().ok_or_else(|| KernelError("bitwise: no `bits`".into()))?;
        let r = self.bit_premise(env, lg, &Term::app(lg.in_, vec![x.clone(), Term::app(bits_s, vec![n.clone()])]), facts)?;
        let mut fs = facts.to_vec();
        fs.push(r);
        // (all premises but the last, n <= i)
        while let Ok((h, rest)) = imp_parts(env, s.concl()) {
            if imp_parts(env, &rest).is_err() {
                break;
            }
            let p = self.bit_premise(env, lg, &h, &fs)?;
            s = Seq::mp(env, &s, &p)?;
        }
        Ok(s)
    }

    /// `bit(W, I) <-> φ` by the first registered rule that matches with its
    /// premises shown; else by the first that matches, the premises not
    /// shown left as hypotheses (`H -> (bit(W, I) <-> φ)`: they may hold
    /// under the conditions of the bit's use, which `arith` sees)
    fn bit_explain(&self, env: &mut Env, lg: &Logic, t: &Term, facts: &[Seq]) -> Option<Seq> {
        for strict in [true, false] {
            for name in env.bit_rules.clone() {
                if let Some(s) = self.bit_rule_at(env, lg, &name, t, facts, strict) {
                    return Some(s);
                }
            }
        }
        None
    }

    fn bit_rule_at(&self, env: &mut Env, lg: &Logic, name: &str, t: &Term, facts: &[Seq], strict: bool) -> Option<Seq> {
        let Node::App(_, ta) = t.node() else { return None };
        let (w, i) = (ta[0].clone(), ta[1].clone());
        let rule = facts::seq_of(env, name)?;
        let (mut s, pv, concl) = open_rule(env, lg, &rule).ok()?;
        // concl: bit(P, J) <-> φ
        let Node::App(_, ca) = concl.node() else { return None };
        let Node::App(_, ba) = ca[0].node() else { return None };
        let (p, j) = (ba[0].clone(), ba[1].clone());
        let mut binds = Vec::new();
        if !bmatch(env, &p, &w, &pv, &mut binds) || !bmatch(env, &j, &i, &pv, &mut binds) {
            return None;
        }
        if pv.iter().any(|v| !binds.iter().any(|(u, _)| u == v)) {
            return None;
        }
        for (v, val) in &binds {
            s = Seq::inst(env, &s, *v, val).ok()?;
        }
        // its premises: shown, or (not strict) assumed
        let mut assumed = Vec::new();
        while let Ok((h, _)) = imp_parts(env, s.concl()) {
            let ph = match self.bit_premise(env, lg, &h, facts) {
                Ok(ph) => ph,
                Err(_) if !strict => {
                    assumed.push(h.clone());
                    Seq::assume(env, h).ok()?
                }
                Err(_) => return None,
            };
            s = Seq::mp(env, &s, &ph).ok()?;
        }
        // its word shown W (a numeral read as a power, a product turned)
        let Node::App(_, sa) = s.concl().node() else { return None };
        let Node::App(_, sb) = sa[0].node() else { return None };
        let pw = sb[0].clone();
        // (a power read from a numeral: pow2(k) = 2^k, rewritten)
        if pw != w {
            let mut pows = Vec::new();
            pow2_lits(env, &pw, &mut pows);
            for k in pows {
                let p2 = Term::app(env.sym_by_name["pow2"], vec![Term::nat(sl_kernel::Nat::from_u128(k as u128))]);
                if k >= 127 {
                    continue;
                }
                let e = Term::app(env.builtins.eq, vec![p2, Term::nat(sl_kernel::Nat::from_u128(1u128 << k))]);
                let pe = Seq::arith(env, lg, &[], &e).ok()?;
                s = Seq::rewrite(env, &pe, &s).ok()?;
            }
        }
        let Node::App(_, sa) = s.concl().node() else { return None };
        let Node::App(_, sb) = sa[0].node() else { return None };
        let pw = sb[0].clone();
        if pw != w {
            let e = Term::app(env.builtins.eq, vec![pw.clone(), w.clone()]);
            let refs: Vec<&Seq> = facts.iter().collect();
            let pe = Seq::arith(env, lg, &refs, &e).ok()?;
            s = Seq::rewrite(env, &pe, &s).ok()?;
        }
        for h in assumed.iter().rev() {
            s = s.discharge(env, h).ok()?;
        }
        Some(s)
    }

    /// a rule's premise: a fact, `arith` from the facts, or (a word's range)
    /// its operation's lemma
    fn bit_premise(&self, env: &mut Env, lg: &Logic, h: &Term, facts: &[Seq]) -> KResult<Seq> {
        if let Some(f) = facts.iter().find(|f| f.concl() == h) {
            return Ok(f.clone());
        }
        let refs: Vec<&Seq> = facts.iter().collect();
        if let Ok(s) = Seq::arith(env, lg, &refs, h) {
            return Ok(s);
        }
        // t in bits(n): the operation's lemma; t in omega: from t in bits(n)
        if let Node::App(f, a) = h.node() {
            if *f == lg.in_ {
                if let Node::App(op, _) = a[0].node() {
                    let lemma = match env.syms[*op as usize].name.as_str() {
                        "bits_and" => Some("bits_and_in"),
                        "bits_or" => Some("bits_or_in"),
                        "bits_xor" => Some("bits_xor_in"),
                        "bits_not" => Some("bits_not_in"),
                        _ => None,
                    };
                    if let Some(l) = lemma.and_then(|n| facts::seq_of(env, n)) {
                        // (its variables by matching its conclusion's word)
                        let (s, pv, c) = open_rule(env, lg, &l)?;
                        let mut binds = Vec::new();
                        let pat = match c.node() {
                            Node::App(g, ca) if *g == lg.in_ => ca[0].clone(),
                            _ => return err("bitwise: a range lemma not `op(..) in bits(n)`"),
                        };
                        if !super::pmatch(env, &pat, &a[0], &pv, &mut binds) || pv.iter().any(|v| !binds.iter().any(|(w, _)| w == v)) {
                            return err(format!("bitwise: `{}` not an instance of its range lemma", Printer::new(env).short(&a[0])));
                        }
                        let mut s = s;
                        for (v, t) in binds {
                            s = Seq::inst(env, &s, v, &t)?;
                        }
                        let hn = self.bit_premise(env, lg, &imp_parts(env, s.concl())?.0, facts)?;
                        let m = Seq::mp(env, &s, &hn)?;
                        if m.concl() == h {
                            return Ok(m);
                        }
                        // (in omega: the range read by arith)
                        return Seq::arith(env, lg, &[&m], h);
                    }
                }
            }
        }
        err(format!("bitwise: the premise `{}` not shown", Printer::new(env).short(h)))
    }
}

/// the word operations' width (their first argument)
fn op_width(env: &Env, t: &Term) -> Option<Term> {
    let Node::App(f, a) = t.node() else { return None };
    let name = env.syms[*f as usize].name.as_str();
    matches!(name, "bits_and" | "bits_or" | "bits_xor" | "bits_not" | "bits_neg" | "bits_shl" | "bits_shr" | "bits_of_int" | "bits_add" | "bits_sub" | "bits_mul" | "bits_set_slice")
        .then(|| a[0].clone())
}

fn eq_sides(env: &Env, t: &Term) -> Option<(Term, Term)> {
    match t.node() {
        Node::App(f, a) if *f == env.builtins.eq && a.len() == 2 => Some((a[0].clone(), a[1].clone())),
        _ => None,
    }
}

/// the closed `bit(W, I)` in t
fn collect_bits(t: &Term, bit: Option<SymId>, out: &mut Vec<Term>) {
    if let Node::App(f, a) = t.node() {
        if Some(*f) == bit && a.len() == 2 && !out.contains(t) {
            out.push(t.clone());
        }
        a.iter().for_each(|x| collect_bits(x, bit, out));
    }
}

fn mentions_sym(t: &Term, f: Option<SymId>) -> bool {
    match t.node() {
        Node::App(g, a) => Some(*g) == f || a.iter().any(|x| mentions_sym(x, f)),
        _ => false,
    }
}

/// a rule's parameters and leading `all`s as fresh variables: (the
/// instance, its variables, its conclusion after the premises)
pub(crate) fn open_rule(env: &mut Env, lg: &Logic, l: &Seq) -> KResult<(Seq, Vec<VarId>, Term)> {
    let mut s = l.clone();
    let mut vs: Vec<VarId> = Vec::new();
    let mut fv = Vec::new();
    s.concl().vars(&mut fv);
    for v in fv {
        if !vs.contains(&v) && !s.hyps().iter().any(|h| {
            let mut hv = Vec::new();
            h.vars(&mut hv);
            hv.contains(&v)
        }) {
            let w = env.new_var(&env.var(v).name.clone(), 0);
            s = Seq::inst(env, &s, v, &Term::var(w, vec![]))?;
            vs.push(w);
        }
    }
    while let Node::App(q, _) = s.concl().node() {
        if *q != lg.all {
            break;
        }
        let v = env.new_var(s.concl().binder_name().unwrap_or("x"), 0);
        s = Seq::all_elim(env, lg, &s, &Term::var(v, vec![]))?;
        vs.push(v);
    }
    let mut c = s.concl().clone();
    while let Ok((_, b)) = imp_parts(env, &c) {
        c = b;
    }
    Ok((s, vs, c))
}

/// a numeral's base-2 logarithm, if it is a power of 2
fn log2(t: &Term) -> Option<u32> {
    let Node::Nat(n) = t.node() else { return None };
    let v = n.to_u128()?;
    (v > 0 && v.is_power_of_two()).then(|| v.trailing_zeros())
}

/// p matches t, binding pvars: numerals read as `pow2(k)` or `pow2(k) - 1`,
/// a product x * 2^k (a mask's high bits: x its value above them), or a
/// sum x * 2^t + (2^j - 1) (an odd mask: its low ones, the rest), a
/// product either way round
fn bmatch(env: &Env, p: &Term, t: &Term, pvars: &[VarId], binds: &mut Vec<(VarId, Term)>) -> bool {
    let name = |s: SymId| env.syms[s as usize].name.as_str();
    let nat = |k: u32| Term::nat(sl_kernel::Nat::from_u128(k as u128));
    match (p.node(), t.node()) {
        (Node::Var(v, a), _) if a.is_empty() && pvars.contains(v) => {
            if let Some((_, b)) = binds.iter().find(|(w, _)| w == v) {
                return b == t;
            }
            binds.push((*v, t.clone()));
            true
        }
        // pow2(k) against 2^c
        (Node::App(f, a), Node::Nat(_)) if name(*f) == "pow2" && a.len() == 1 => match log2(t) {
            Some(c) => bmatch(env, &a[0], &nat(c), pvars, binds),
            None => false,
        },
        // pow2(k) - 1 against 2^c - 1
        (Node::App(f, a), Node::Nat(n)) if name(*f) == "int_sub" && a.len() == 2 && a[1] == nat(1) => {
            let Some(v) = n.to_u128().and_then(|v| v.checked_add(1)) else { return false };
            let t1 = Term::nat(sl_kernel::Nat::from_u128(v));
            matches!(a[0].node(), Node::App(g, _) if name(*g) == "pow2") && bmatch(env, &a[0], &t1, pvars, binds)
        }
        // x * 2^t + r against an odd numeral c not 2^k - 1: r its run of low
        // ones (2^j - 1), x * 2^t the rest (a mask's bits in runs)
        (Node::App(f, a), Node::Nat(n)) if name(*f) == "int_add" && a.len() == 2 => {
            let Some(v) = n.to_u128().filter(|v| v % 2 == 1 && !(v + 1).is_power_of_two()) else { return false };
            let r = (1u128 << v.trailing_ones()) - 1;
            let save = binds.clone();
            if bmatch(env, &a[1], &Term::nat(sl_kernel::Nat::from_u128(r)), pvars, binds) && bmatch(env, &a[0], &Term::nat(sl_kernel::Nat::from_u128(v - r)), pvars, binds) {
                return true;
            }
            *binds = save;
            false
        }
        // x * pow2(k) against c * 2^k (c odd, k > 0)
        (Node::App(f, a), Node::Nat(n)) if name(*f) == "int_mul" && a.len() == 2 => {
            let Some(v) = n.to_u128().filter(|v| *v > 0 && v.trailing_zeros() > 0) else { return false };
            let tz = v.trailing_zeros();
            let (hi, p2) = (Term::nat(sl_kernel::Nat::from_u128(v >> tz)), Term::nat(sl_kernel::Nat::from_u128(1u128 << tz)));
            let save = binds.clone();
            if bmatch(env, &a[0], &hi, pvars, binds) && bmatch(env, &a[1], &p2, pvars, binds) {
                return true;
            }
            *binds = save.clone();
            if bmatch(env, &a[1], &hi, pvars, binds) && bmatch(env, &a[0], &p2, pvars, binds) {
                return true;
            }
            *binds = save;
            false
        }
        (Node::App(f, a), Node::App(g, b)) if f == g && a.len() == b.len() => {
            let save = binds.clone();
            if a.iter().zip(b.iter()).all(|(x, y)| bmatch(env, x, y, pvars, binds)) {
                return true;
            }
            *binds = save.clone();
            // (a product the other way round)
            if name(*f) == "int_mul" && a.len() == 2 && bmatch(env, &a[0], &b[1], pvars, binds) && bmatch(env, &a[1], &b[0], pvars, binds) {
                return true;
            }
            *binds = save;
            false
        }
        _ => p == t,
    }
}

impl State {
    /// `cases({k}, {a}, {b}, R, p..)`: the goal for the variable k, a <= k
    /// < b (numerals; from the facts p.. by arith), each value c by R (the
    /// goal at c), the cases chained downwards: `c <= k -> G` from `c = k
    /// -> G` and `c + 1 <= k -> G`
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn cases_goal(&self, env: &mut Env, lg: &Logic, goal: &Term, k: &Term, a: u128, b: u128, r: &PE, facts: &[Seq]) -> KResult<Seq> {
        let Node::Var(v, va) = k.node() else { return err("cases: `{k}` must be a variable") };
        if !va.is_empty() || b <= a || b - a > 4096 {
            return err("cases: a variable k and a range a < b of at most 4096 values expected");
        }
        let g = |s: &str| env.sym_by_name.get(s).copied().ok_or_else(|| KernelError(format!("cases: needs `{}`", s)));
        let (int_le, or, not) = (g("int_le")?, g("or")?, g("not")?);
        let nat = |c: u128| Term::nat(sl_kernel::Nat::from_u128(c));
        let le = |x: Term, y: Term| Term::app(int_le, vec![x, y]);
        let body = abstract_var(goal, *v, 0, &env.binders_fn());
        let refs: Vec<&Seq> = facts.iter().collect();
        // above the range: no case
        let above = Term::app(not, vec![le(nat(b), k.clone())]);
        let na = Seq::arith(env, lg, &refs, &above).map_err(|_| KernelError(format!("cases: `{} < {}` not shown from the facts", Printer::new(env).short(k), b)))?;
        let lb = le(nat(b), k.clone());
        let mut chain = Seq::taut(env, lg, &[&na], &Term::app(env.builtins.imp, vec![lb, goal.clone()]))?;
        for c in (a..b).rev() {
            // the goal at c, by R; then at k = c
            let gc = body.instantiate_params(&[nat(c)], &env.binders_fn());
            // (R's terms at the case: k's name read as c)
            let kname = env.var(*v).name.clone();
            let rc = pe_at(r, &kname, &c.to_string());
            let pc = self.by(env, lg, &gc, &rc).map_err(|e| KernelError(format!("cases: the case {}: {}", c, e.0)))?;
            let eq = Term::app(env.builtins.eq, vec![nat(c), k.clone()]);
            let he = Seq::assume(env, eq.clone())?;
            let ec = Seq::subst(env, &he, &body, &pc)?.discharge(env, &eq)?;
            let lc = le(nat(c), k.clone());
            let split = Term::app(env.builtins.imp, vec![lc.clone(), Term::app(or, vec![eq.clone(), le(nat(c + 1), k.clone())])]);
            let d = Seq::arith(env, lg, &refs, &split)?;
            chain = Seq::taut(env, lg, &[&d, &ec, &chain], &Term::app(env.builtins.imp, vec![lc, goal.clone()]))?;
        }
        let lo = le(nat(a), k.clone());
        let pl = Seq::arith(env, lg, &refs, &lo).map_err(|_| KernelError(format!("cases: `{} <= {}` not shown from the facts", a, Printer::new(env).short(k))))?;
        Seq::mp(env, &chain, &pl)
    }
}

/// a proof expression with the identifier `name` in its terms replaced
fn pe_at(p: &PE, name: &str, by: &str) -> PE {
    let arg = |a: &Arg| match a {
        Arg::Term(t) => Arg::Term(replace_ident(t, name, by)),
        Arg::Proof(q) => Arg::Proof(pe_at(q, name, by)),
    };
    match p {
        PE::Ref(n) => PE::Ref(n.clone()),
        PE::Rule(n, a) => PE::Rule(n.clone(), a.iter().map(arg).collect()),
        PE::Inst(q, vs) => PE::Inst(Box::new(pe_at(q, name, by)), vs.iter().map(|(x, t)| (x.clone(), replace_ident(t, name, by))).collect()),
        PE::Conj(q, k) => PE::Conj(Box::new(pe_at(q, name, by)), k.clone()),
        PE::By(t, q) => PE::By(replace_ident(t, name, by), Box::new(pe_at(q, name, by))),
    }
}

/// `name` replaced by `by` where it is a whole identifier
fn replace_ident(t: &str, name: &str, by: &str) -> String {
    let ident = |c: char| c.is_alphanumeric() || c == '_' || c == '.' || c == '$';
    let mut out = String::new();
    // (positions in t: the character before a match is t's, not a cut rest's)
    let mut at = 0;
    while let Some(j) = t[at..].find(name) {
        let i = at + j;
        let before = t[..i].chars().last();
        let after = t[i + name.len()..].chars().next();
        out.push_str(&t[at..i]);
        if before.is_some_and(ident) || after.is_some_and(ident) {
            out.push_str(name);
        } else {
            out.push_str(by);
        }
        at = i + name.len();
    }
    out.push_str(&t[at..]);
    out
}

/// t with the variable v as the loose bound variable of a one-parameter
/// value (`BVar(depth)` under depth binders)
fn abstract_var(t: &Term, v: VarId, depth: u32, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
    match t.node() {
        Node::Var(w, a) if *w == v && a.is_empty() => Term::bvar(depth),
        Node::Var(_, a) => t.with_args(a.iter().map(|x| abstract_var(x, v, depth, binders)).collect()),
        Node::App(s, a) => t.with_args(a.iter().enumerate().map(|(i, x)| abstract_var(x, v, depth + binders(*s, i), binders)).collect()),
        _ => t.clone(),
    }
}

/// the exponents k of the `pow2(k)` in t, k a numeral
fn pow2_lits(env: &Env, t: &Term, out: &mut Vec<u32>) {
    if let Node::App(f, a) = t.node() {
        if env.syms[*f as usize].name == "pow2" && a.len() == 1 {
            if let Some(k) = match a[0].node() {
                Node::Nat(n) => n.to_u128().and_then(|k| u32::try_from(k).ok()),
                _ => None,
            } {
                if !out.contains(&k) {
                    out.push(k);
                }
            }
        }
        a.iter().for_each(|x| pow2_lits(env, x, out));
    }
}
