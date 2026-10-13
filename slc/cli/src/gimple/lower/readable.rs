//! Readable GIMPLE: a function as an SL proc close to the C source (see
//! `layers/gimple.sl`, "Readable GIMPLE: the operations").
//!
//! C variables keep their names (one mutable variable for all SSA versions
//! of a variable), temporaries `_13` become `t13`, values are words of their
//! precision, struct fields are read and written through accessors
//! (`meta_last_idx(meta)`), globals are named constants, and the called
//! functions are parameters. Acyclic control flow is structured into
//! nested `if`s, joining at the branch's immediate post-dominator.

use super::*;
use std::collections::{BTreeMap, BTreeSet};

/// What the readable functions of a file share: globals (name -> address)
/// and field accessors (name -> definition).
#[derive(Default)]
pub struct Shared {
    pub globals: BTreeMap<String, u64>,
    pub accessors: BTreeMap<String, String>,
    /// the control-flow graph as it is (`--cfg`), not structured
    pub cfg: bool,
}

/// Names the readable code must not shadow (gimple.sl's operations, SL
/// keywords, the state's fields).
const RESERVED: &[&str] = &[
    "sadd", "ssub", "smul", "sneg", "cdiv", "crem", "div", "rem", "shl", "shr", "sar", "smin", "smax", "umin", "umax", "b1", "padd", "mem", "ld8", "ld16",
    "ld32", "ld64", "ld128", "st8", "st16", "st32", "st64", "st128", "st_bytes", "ldbf", "stbf", "call", "call1", "call_objs", "call1_objs",
    "arg", "result", "elem", "inline_asm", "alloc_objs", "objs", "args", "any", "let", "var", "if", "else", "match", "while", "for", "in",
    "return", "fn", "proc", "pred", "type", "state", "self", "true", "false", "loop", "break", "either", "or", "havoc", "where", "require",
    "undefined", "ghost", "emit", "raise", "try", "catch", "vm", "os", "sp", "cpu", "fs_base", "uint", "sint", "zext", "sext", "bits",
    "nat", "int", "bool", "len", "all", "ex", "some", "none", "min", "max", "view", "with", "layer", "uses", "const", "law", "param",
];

fn sanitize(s: &str) -> String {
    let t: String = s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect();
    if RESERVED.contains(&t.as_str()) { format!("{}_", t) } else { t }
}

/// A literal of the given precision, negative when its top bit is set.
fn lit(v: i128, prec: u64) -> String {
    let w = wrap(v, prec);
    if prec >= 8 && prec <= 64 && w >= 1u128 << (prec - 1) {
        let neg = (1u128 << prec) - w;
        format!("-{}", neg)
    } else if w > 0xffff {
        format!("{:#x}", w)
    } else {
        w.to_string()
    }
}

/// The successors of block i: by its last statement, or falling through.
fn succs(f: &Func, index: &HashMap<u64, usize>, i: usize) -> Result<Vec<usize>, String> {
    let bi = |n: &u64| index.get(n).copied().ok_or_else(|| format!("no block {}", n));
    Ok(match f.blocks[i].stmts.last() {
        Some(S::Goto(t)) => vec![bi(t)?],
        Some(S::If { yes, no, .. }) => vec![bi(yes)?, bi(no)?],
        Some(S::Return(_)) => vec![],
        _ if i + 1 < f.blocks.len() => vec![i + 1],
        _ => return Err(format!("block {} has no successor", f.blocks[i].num)),
    })
}

struct Rx<'f> {
    f: &'f Func,
    fx: Fx,
    succ: Vec<Vec<usize>>,
    /// loops: header -> (its blocks, the exit `break` goes to)
    loops: HashMap<usize, (BTreeSet<usize>, Option<usize>)>,
    /// readable names of GIMPLE value names
    rn: HashMap<String, String>,
    /// value names bound by `let` (the others are variables)
    lets: BTreeSet<String>,
    /// variables: readable name -> width
    vars: BTreeMap<String, u64>,
    /// parameters: GIMPLE name -> (readable name, width); reassigned ones
    /// are copied into a variable
    params: Vec<(String, u64, bool)>,
    callees: Vec<String>,
    out: Vec<String>,
    depth: usize,
    emitted: usize,
    /// writing a block as its procedure: a jump to block n the tail call
    /// `{0}__b{n}({1})` (`{2}`: no result)
    tail: Option<(String, String, bool)>,
}

fn walk_e(e: &E, out: &mut Vec<String>) {
    match e {
        E::Name(n) => out.push(n.clone()),
        E::Num(_) => {}
        E::Addr(x) | E::Deref(x) | E::Neg(x) | E::Not(x) | E::Cast(_, x) | E::Field(x, _) | E::Arrow(x, _) | E::BitRef(x, _, _) => walk_e(x, out),
        E::Index(a, b) | E::Bin(_, a, b) => {
            walk_e(a, out);
            walk_e(b, out)
        }
        E::Mem { base, .. } => walk_e(base, out),
        E::Call(_, xs) | E::Code(_, xs) | E::Ctor(xs) => xs.iter().for_each(|x| walk_e(x, out)),
    }
}

/// (definitions, uses) of names in a statement
fn defs_uses(s: &S) -> (Vec<String>, Vec<String>) {
    let (mut d, mut u) = (Vec::new(), Vec::new());
    match s {
        S::Assign(l, r) => {
            match l {
                E::Name(n) => d.push(n.clone()),
                other => walk_e(other, &mut u),
            }
            walk_e(r, &mut u);
        }
        S::Call(l, _, args) => {
            match l {
                Some(E::Name(n)) => d.push(n.clone()),
                Some(other) => walk_e(other, &mut u),
                None => {}
            }
            args.iter().for_each(|a| walk_e(a, &mut u));
        }
        S::Asm { outs, ins, .. } => {
            for (_, e) in outs {
                match e {
                    E::Name(n) => d.push(n.clone()),
                    other => walk_e(other, &mut u),
                }
            }
            ins.iter().for_each(|(_, e)| walk_e(e, &mut u));
        }
        S::Return(Some(e)) => walk_e(e, &mut u),
        S::If { a, b, .. } => {
            walk_e(a, &mut u);
            walk_e(b, &mut u)
        }
        _ => {}
    }
    (d, u)
}

impl<'a> Lower<'a> {
    /// The readable form of `f`: its proc and its C function spec.
    pub fn readable(&mut self, f: &Func, sh: &mut Shared) -> Result<String, String> {
        let (fx, _) = self.frame(f)?;
        let index: HashMap<u64, usize> = f.blocks.iter().enumerate().map(|(i, b)| (b.num, i)).collect();
        let n = f.blocks.len();
        let mut succ = Vec::new();
        for i in 0..n {
            succ.push(succs(f, &index, i)?);
        }
        // back edges (to a block on the DFS stack): loops
        let mut back: BTreeSet<(usize, usize)> = BTreeSet::new();
        fn dfs(i: usize, succ: &[Vec<usize>], st: &mut [u8], back: &mut BTreeSet<(usize, usize)>) {
            st[i] = 1;
            for &s in &succ[i] {
                if st[s] == 1 {
                    back.insert((i, s));
                } else if st[s] == 0 {
                    dfs(s, succ, st, back);
                }
            }
            st[i] = 2;
        }
        dfs(0, &succ, &mut vec![0u8; n], &mut back);
        // the natural loop of each header: the blocks reaching a latch
        // without passing the header
        let mut loops: HashMap<usize, (BTreeSet<usize>, Option<usize>)> = HashMap::new();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for i in 0..n {
            for &s in &succ[i] {
                preds[s].push(i);
            }
        }
        for &(latch, h) in &back {
            let body = &mut loops.entry(h).or_default().0;
            body.insert(h);
            let mut work = vec![latch];
            while let Some(x) = work.pop() {
                if body.insert(x) {
                    work.extend(preds[x].iter().copied());
                }
            }
        }
        // the exit `break` goes to: the most frequent target outside
        for (_, (body, exit)) in loops.iter_mut() {
            let mut count: BTreeMap<usize, usize> = BTreeMap::new();
            for &b in body.iter() {
                for &s in &succ[b] {
                    if !body.contains(&s) {
                        *count.entry(s).or_default() += 1;
                    }
                }
            }
            *exit = count.iter().max_by_key(|(_, &c)| c).map(|(&s, _)| s);
        }
        let mut rx = Rx {
            f,
            fx,
            succ,
            loops,
            rn: HashMap::new(),
            lets: BTreeSet::new(),
            vars: BTreeMap::new(),
            params: Vec::new(),
            callees: Vec::new(),
            out: Vec::new(),
            depth: 1,
            emitted: 0,
            tail: None,
        };
        self.names(&mut rx)?;
        // (a function of a return alone: as it is, no CFG)
        let cfg = sh.cfg && !self.return_only(&rx, self.past(&rx, 0));
        if cfg {
            self.emit_cfg(&mut rx, sh)?;
        } else {
            // (the structuring: its routine on the blocks and their jumps)
            let g = self.graph(&mut rx, sh)?;
            let nodes = crate::gimple::structure::structure(&g)?;
            let mut lines = Vec::new();
            crate::gimple::structure::render(&g, &nodes, rx.depth, &mut lines);
            rx.out.extend(lines);
        }
        let total: usize = f.blocks.iter().map(|b| b.stmts.len()).sum();
        if rx.emitted > 4 * total + 8 {
            return Err("unstructured control flow (too much duplication)".into());
        }
        // the proc
        let fname = sanitize(&f.name);
        let ret = rx.fx.ret.clone();
        let ret_ty = match &ret {
            RT::Void => None,
            RT::Ptr(_) => Some("Addr".to_string()),
            RT::Struct(_) => Some("(bits[64], bits[64])".to_string()),
            t => Some(format!("bits[{}]", self.scalar(t)?.0)),
        };
        let two_words = matches!(ret, RT::Struct(_));
        let mut ps: Vec<String> = Vec::new();
        for (name, w, reassigned) in &rx.params {
            let ty = if *w == 64 { "bits[64]".to_string() } else { format!("bits[{}]", w) };
            ps.push(format!("{}{}: {}", name, if *reassigned { "_in" } else { "" }, ty));
        }
        for c in &rx.callees {
            ps.push(format!("{}: CFun2[World]", c));
        }
        let mut s = String::new();
        writeln!(s, "// {} {}", f.ret, f.name).unwrap();
        writeln!(s, "proc[World] {}({}){} {{", fname, ps.join(", "), ret_ty.as_ref().map(|t| format!(" -> {}", t)).unwrap_or_default()).unwrap();
        // (the CFG: the block to run first among the locals, and one more
        // local where it would be the only one -- the locals a pair)
        let order = self.var_order(&rx);
        if cfg {
            writeln!(s, "  var bb: nat = {}", rx.f.blocks[self.past(&rx, 0)].num).unwrap();
            if order.is_empty() {
                writeln!(s, "  var bb_none: nat = 0").unwrap();
            }
        }
        for (name, w, reassigned) in &rx.params {
            if *reassigned {
                writeln!(s, "  var {}: bits[{}] = {}_in", name, w, name).unwrap();
            }
        }
        for (v, w) in &rx.vars {
            if !rx.params.iter().any(|(p, _, _)| p == v) {
                writeln!(s, "  var {}: bits[{}] = any bits[{}]", v, w, w).unwrap();
            }
        }
        if !rx.fx.obj_list.is_empty() {
            let objs: Vec<String> = rx.fx.obj_list.iter().map(|(sz, al)| format!("({}, {})", sz, al)).collect();
            writeln!(s, "  let objs = alloc_objs([{}])", objs.join(", ")).unwrap();
        }
        for l in &rx.out {
            writeln!(s, "{}", l).unwrap();
        }
        writeln!(s, "}}").unwrap();
        // (the CFG's blocks as procedures, a jump a tail call -- the form
        // the structured form is proven from; loop-free functions without
        // stack objects, of a result in one word or none)
        if cfg && rx.loops.is_empty() && rx.fx.obj_list.is_empty() && !two_words {
            self.block_procs(&mut rx, sh, &fname, ret_ty.as_deref(), &order, &ps, &mut s)?;
        }
        // (the CFG's guide for C1, untrusted: each block's live locals, by
        // their positions after bb, a bit each; the locals' widths)
        if cfg {
            let live = self.cfg_live(&rx, &order)?;
            let items: Vec<String> = live.iter().map(|(b, m)| format!("({}, {})", b, m)).collect();
            writeln!(s, "fn {}_cfg_live() -> List[(nat, nat)] = [{}]", fname, items.join(", ")).unwrap();
            let ws: Vec<String> = order.iter().map(|(_, w)| w.to_string()).collect();
            writeln!(s, "fn {}_cfg_widths() -> List[nat] = [{}]", fname, ws.join(", ")).unwrap();
        }
        // the C function spec: arguments and result in registers
        let cps: Vec<String> = rx.callees.iter().map(|c| format!("{}: CFun2[World]", c)).collect();
        let mut call_args: Vec<String> = rx.params.iter().enumerate().map(|(i, (_, w, _))| format!("bits[{}](args[{}])", w, i)).collect();
        call_args.extend(rx.callees.iter().cloned());
        writeln!(s, "fn {}_fun({}) -> CFun2[World] = (args: Args) => {{", fname, cps.join(", ")).unwrap();
        // a call with fewer arguments than the function's parameters is
        // undefined (the missing ones would be whatever the registers hold)
        if !rx.params.is_empty() {
            writeln!(s, "  require len(args) >= {}", rx.params.len()).unwrap();
        }
        // (a function's stack objects end with it: the world's as before)
        let has_objs = !rx.fx.obj_list.is_empty();
        if has_objs {
            writeln!(s, "  let objs0 = objs").unwrap();
        }
        let drop = if has_objs { "\n  objs := objs0" } else { "" };
        match ret_ty {
            None => writeln!(s, "  {}({}){drop}\n  return (any bits[64], any bits[64])", fname, call_args.join(", ")).unwrap(),
            Some(_) if two_words => writeln!(s, "  let (r0, r1) = {}({}){drop}\n  return (r0, r1)", fname, call_args.join(", ")).unwrap(),
            Some(_) => writeln!(s, "  let r = {}({}){drop}\n  return (result(r), any bits[64])", fname, call_args.join(", ")).unwrap(),
        }
        writeln!(s, "}}").unwrap();
        Ok(s)
    }

    /// Readable names, and which values are `let`-bound temporaries.
    fn names(&mut self, rx: &mut Rx) -> Result<(), String> {
        let f = rx.f;
        // where each value name is defined and used
        let mut def_block: HashMap<String, usize> = HashMap::new();
        let mut use_blocks: HashMap<String, BTreeSet<usize>> = HashMap::new();
        let mut in_phi: BTreeSet<String> = BTreeSet::new();
        let mut all: Vec<String> = Vec::new();
        for (i, b) in f.blocks.iter().enumerate() {
            for p in &b.phis {
                def_block.insert(p.dst.clone(), i);
                in_phi.insert(p.dst.clone());
                all.push(p.dst.clone());
                for (e, _) in &p.args {
                    let mut u = Vec::new();
                    walk_e(e, &mut u);
                    for x in u {
                        in_phi.insert(x.clone());
                        all.push(x);
                    }
                }
            }
            for s in &b.stmts {
                let (d, u) = defs_uses(s);
                for x in d {
                    def_block.insert(x.clone(), i);
                    all.push(x);
                }
                for x in u {
                    use_blocks.entry(x.clone()).or_default().insert(i);
                    all.push(x);
                }
            }
        }
        // parameters (by their C names); reassigned when a version other
        // than the default definition is defined
        for (p, _) in &f.params {
            let t = rx.fx.decl.get(p).cloned().ok_or_else(|| format!("no type for parameter {}", p))?;
            let w = self.scalar(&t)?.0;
            let reassigned = def_block.keys().any(|d| is_ssa(d) && !d.ends_with("(D)") && ssa_base(d) == p);
            rx.params.push((sanitize(p), w, reassigned));
            if reassigned {
                rx.vars.insert(sanitize(p), w);
            }
        }
        for s in all {
            if rx.rn.contains_key(&s) || !self.is_value_name(&rx.fx, &s) {
                continue;
            }
            let bare = s.trim_end_matches("(D)");
            let base = if is_ssa(bare) { ssa_base(bare) } else { bare };
            let x = self.name(&mut rx.fx, &s)?;
            let w = rx.fx.types[x].0;
            let c_var = f.params.iter().any(|(p, _)| p == base) || f.decls.iter().any(|(d, _)| d == base && !is_ssa(d));
            let name = if c_var {
                sanitize(base)
            } else {
                format!("t{}", bare.rsplit('_').next().unwrap_or("0"))
            };
            if !c_var {
                // a temporary: `let` when defined and used in one block only
                let db = def_block.get(&s);
                let local = db.is_some() && !in_phi.contains(&s) && use_blocks.get(&s).is_none_or(|u| u.iter().all(|b| Some(b) == db));
                if local {
                    rx.lets.insert(s.clone());
                } else {
                    rx.vars.insert(name.clone(), w);
                }
            } else if !f.params.iter().any(|(p, _)| p == base) {
                rx.vars.insert(name.clone(), w);
            }
            rx.rn.insert(s.clone(), name);
        }
        Ok(())
    }

    fn line(&self, rx: &mut Rx, l: String) {
        rx.out.push(format!("{}{}", "  ".repeat(rx.depth), l));
    }

    /// a block with no statements of its own and no phis (just its jump):
    /// the CFG goes past it, to its target -- no code of its own either
    fn forwarder(&self, rx: &Rx, b: usize) -> bool {
        let blk = &rx.f.blocks[b];
        blk.phis.is_empty() && rx.succ[b].len() == 1 && blk.stmts.iter().all(|s| matches!(s, S::Goto(_)))
    }

    /// a block of a `return` (values copied before it, maybe in blocks on
    /// the way): written in place of the jumps to it
    /// (the compiler's code returns there too, or loads the value and
    /// joins the epilogue)
    fn return_only(&self, rx: &Rx, b: usize) -> bool {
        self.tail_of(rx, b, 0)
    }

    /// b a returning tail: values copied (names, numbers, their casts), then a
    /// `return`, or on to a returning tail (its one way)
    fn tail_of(&self, rx: &Rx, b: usize, depth: usize) -> bool {
        if depth > rx.f.blocks.len() {
            return false;
        }
        let stmts = &rx.f.blocks[b].stmts;
        let val = |e: &E| matches!(e, E::Name(_) | E::Num(_));
        let copy = |s: &S| matches!(s, S::Assign(E::Name(_), e) if val(e) || matches!(e, E::Cast(_, x) if val(x)));
        match stmts.last() {
            Some(S::Return(_)) => stmts[..stmts.len() - 1].iter().all(copy),
            _ => stmts.iter().all(|s| copy(s) || matches!(s, S::Goto(_))) && rx.succ[b].len() == 1 && self.tail_of(rx, rx.succ[b][0], depth + 1),
        }
    }

    /// a returning tail written in place: its copies, its way's phis'
    /// copies, on to the `return`
    fn emit_tail(&mut self, rx: &mut Rx, sh: &mut Shared, b: usize) -> Result<(), String> {
        let mut b = b;
        for _ in 0..=rx.f.blocks.len() {
            for st in rx.f.blocks[b].stmts.clone() {
                if !matches!(st, S::Goto(_)) {
                    self.rstmt(rx, sh, &st)?;
                }
            }
            if matches!(rx.f.blocks[b].stmts.last(), Some(S::Return(_))) {
                return Ok(());
            }
            let s = rx.succ[b][0];
            for l in self.phi_copies(rx, sh, b, s)? {
                self.line(rx, l);
            }
            b = s;
        }
        Err("a returning tail without its return".into())
    }

    /// where a jump to b goes: past forwarders
    fn past(&self, rx: &Rx, mut b: usize) -> usize {
        for _ in 0..rx.f.blocks.len() {
            if !self.forwarder(rx, b) {
                break;
            }
            b = rx.succ[b][0];
        }
        b
    }

    /// the locals in their order (the vars: reassigned parameters, then
    /// the others by name), with their widths
    fn var_order(&self, rx: &Rx) -> Vec<(String, u64)> {
        let mut out: Vec<(String, u64)> = rx.params.iter().filter(|p| p.2).map(|(n, w, _)| (n.clone(), *w)).collect();
        for (v, w) in &rx.vars {
            if !rx.params.iter().any(|(p, _, _)| p == v) {
                out.push((v.clone(), *w));
            }
        }
        out
    }

    /// The locals live at each block's entry (read before written on some
    /// way on; the phis' copies on the edges as the CFG writes them): per
    /// block number, a bit per local position
    fn cfg_live(&self, rx: &Rx, order: &[(String, u64)]) -> Result<Vec<(u64, u128)>, String> {
        if order.len() > 120 {
            return Err("more than 120 locals".into());
        }
        let pos = |g: &str| rx.rn.get(g).and_then(|r| order.iter().position(|(x, _)| x == r));
        let bit = |i: usize| 1u128 << i;
        let n = rx.f.blocks.len();
        // per block: used before written, written (its statements)
        let mut uses = vec![0u128; n];
        let mut defs = vec![0u128; n];
        for b in 0..n {
            for st in &rx.f.blocks[b].stmts {
                let (d, u) = defs_uses(st);
                for x in u {
                    if let Some(i) = pos(&x) {
                        if defs[b] & bit(i) == 0 {
                            uses[b] |= bit(i);
                        }
                    }
                }
                for x in d {
                    if let Some(i) = pos(&x) {
                        defs[b] |= bit(i);
                    }
                }
            }
        }
        // per edge: its copies (target, what they read), in order
        let edge = |from: usize, to: usize| -> Vec<(Option<usize>, u128)> {
            let from_num = rx.f.blocks[from].num;
            let mut cs = Vec::new();
            for p in &rx.f.blocks[to].phis {
                let Some((e, _)) = p.args.iter().find(|(_, b)| *b == from_num) else { continue };
                if let E::Name(nm) = e {
                    if rx.rn.get(nm).is_some() && rx.rn.get(nm) == rx.rn.get(&p.dst) {
                        continue;
                    }
                }
                let mut u = Vec::new();
                walk_e(e, &mut u);
                let m = u.iter().filter_map(|x| pos(x)).fold(0u128, |a, i| a | bit(i));
                cs.push((pos(&p.dst), m));
            }
            cs
        };
        let mut live = vec![0u128; n];
        loop {
            let mut changed = false;
            for b in (0..n).rev() {
                let mut out = 0u128;
                for &s in &rx.succ[b] {
                    let mut l = live[s];
                    for (d, u) in edge(b, s).into_iter().rev() {
                        if let Some(i) = d {
                            l &= !bit(i);
                        }
                        l |= u;
                    }
                    out |= l;
                }
                let li = uses[b] | (out & !defs[b]);
                if li != live[b] {
                    live[b] = li;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Ok((0..n).filter(|&b| !self.forwarder(rx, b) && !self.return_only(rx, b)).map(|b| (rx.f.blocks[b].num, live[b])).collect())
    }

    /// The control-flow graph as it is: `bb` the number of the block to
    /// run (GCC's), a `loop` running it -- found by `bb`'s bits, a tree of
    /// comparisons (the block of n among m by log m of them) -- each block
    /// its statements, then the next block's number (its phis' copies on
    /// the edge first), or a `return`.
    fn emit_cfg(&mut self, rx: &mut Rx, sh: &mut Shared) -> Result<(), String> {
        if rx.vars.contains_key("bb") || rx.params.iter().any(|(p, _, _)| p == "bb") {
            return Err("a variable named bb".into());
        }
        let mut bs: Vec<usize> = (0..rx.f.blocks.len()).filter(|&b| !self.forwarder(rx, b) && !self.return_only(rx, b)).collect();
        bs.sort_by_key(|&i| rx.f.blocks[i].num);
        self.line(rx, "loop {".into());
        rx.depth += 1;
        self.dispatch(rx, sh, &bs)?;
        rx.depth -= 1;
        self.line(rx, "}".into());
        Ok(())
    }

    /// The function's blocks and jumps for the structuring
    /// (crate::gimple::structure): each block's statements as lines, a
    /// branch's condition and its negation, each edge's copies (its
    /// target's phis).
    fn graph(&mut self, rx: &mut Rx, sh: &mut Shared) -> Result<crate::gimple::structure::Graph, String> {
        use crate::gimple::structure::{Block, Cond, Edge, Graph, Jump};
        let saved = (std::mem::take(&mut rx.out), rx.depth);
        rx.depth = 0;
        let mut blocks = Vec::new();
        for b in 0..rx.f.blocks.len() {
            let blk = rx.f.blocks[b].clone();
            let k = blk.stmts.len();
            let mut total = true;
            rx.out.clear();
            for (i, s) in blk.stmts.iter().enumerate() {
                if i + 1 == k && matches!(s, S::Goto(_) | S::If { .. }) {
                    break;
                }
                total &= self.total_stmt(rx, s);
                rx.emitted += 1;
                self.rstmt(rx, sh, s).map_err(|e| format!("block {}: {}: {:?}", blk.num, e, s))?;
            }
            let stmts = std::mem::take(&mut rx.out);
            let edge = |g: &mut Self, rx: &mut Rx, sh: &mut Shared, to: usize| -> Result<Edge, String> { Ok(Edge { to, copies: g.phi_copies(rx, sh, b, to)? }) };
            let term = match blk.stmts.last() {
                Some(S::Return(_)) => Jump::Return,
                Some(S::If { op, a, b: c, .. }) => {
                    let (op, a, c) = (op.clone(), a.clone(), c.clone());
                    let text = self.cond(rx, sh, &op, &a, &c)?;
                    let neg = self.cond(rx, sh, &negate(&op), &a, &c)?;
                    let (yes, no) = (rx.succ[b][0], rx.succ[b][1]);
                    Jump::If { cond: Cond { text, neg }, yes: edge(self, rx, sh, yes)?, no: edge(self, rx, sh, no)? }
                }
                _ => {
                    let to = rx.succ[b][0];
                    Jump::Goto(edge(self, rx, sh, to)?)
                }
            };
            blocks.push(Block { num: blk.num, stmts, total, term });
        }
        (rx.out, rx.depth) = saved;
        Ok(Graph { blocks, entry: 0 })
    }

    /// Each block of the CFG as its procedure `F__bN`: the function's
    /// fixed parameters and callees, then its locals (`order`) as
    /// parameters; its statements, a jump the next block's procedure
    /// called with them, its result returned. The successors first (each
    /// called after its definition). Then `F__entry`: the function's
    /// parameters and locals as it starts, the first block's procedure
    /// called.
    fn block_procs(&mut self, rx: &mut Rx, sh: &mut Shared, fname: &str, ret_ty: Option<&str>, order: &[(String, u64)], main_ps: &[String], s: &mut String) -> Result<(), String> {
        let blocks: Vec<usize> = (0..rx.f.blocks.len()).filter(|&b| !self.forwarder(rx, b) && !self.return_only(rx, b)).collect();
        // (where a block goes: past forwarders, not to a returning tail)
        let nexts: Vec<Vec<usize>> = (0..rx.f.blocks.len()).map(|b| rx.succ[b].iter().map(|&t| self.past(rx, t)).filter(|&t| !self.return_only(rx, t)).collect()).collect();
        let mut post: Vec<usize> = Vec::new();
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        fn dfs(b: usize, nexts: &[Vec<usize>], seen: &mut BTreeSet<usize>, post: &mut Vec<usize>) {
            if !seen.insert(b) {
                return;
            }
            for &t in &nexts[b] {
                dfs(t, nexts, seen, post);
            }
            post.push(b);
        }
        dfs(self.past(rx, 0), &nexts, &mut seen, &mut post);
        let fixed: Vec<(String, u64)> = rx.params.iter().filter(|p| !p.2).map(|(n, w, _)| (n.clone(), *w)).collect();
        let mut ps: Vec<String> = fixed.iter().map(|(n, w)| format!("{}: bits[{}]", n, w)).collect();
        ps.extend(rx.callees.iter().map(|c| format!("{}: CFun2[World]", c)));
        ps.extend(order.iter().map(|(n, w)| format!("{}_in: bits[{}]", n, w)));
        let mut args: Vec<String> = fixed.iter().map(|(n, _)| n.clone()).collect();
        args.extend(rx.callees.iter().cloned());
        args.extend(order.iter().map(|(n, _)| n.clone()));
        let saved = (std::mem::take(&mut rx.out), rx.depth);
        rx.tail = Some((fname.to_string(), args.join(", "), ret_ty.is_none()));
        for b in post.into_iter().filter(|b| blocks.contains(b)) {
            rx.out.clear();
            rx.depth = 1;
            self.cfg_block(rx, sh, b)?;
            writeln!(s, "proc[World] {}__b{}({}){} {{", fname, rx.f.blocks[b].num, ps.join(", "), ret_ty.map(|t| format!(" -> {}", t)).unwrap_or_default()).unwrap();
            for (n, w) in order {
                writeln!(s, "  var {}: bits[{}] = {}_in", n, w, n).unwrap();
            }
            for l in &rx.out {
                writeln!(s, "{}", l).unwrap();
            }
            writeln!(s, "}}").unwrap();
        }
        // (the entry: the parameters and locals as the function's, then its
        // first block)
        let (tf, targs, void) = rx.tail.take().expect("the tail call");
        writeln!(s, "proc[World] {}__entry({}){} {{", fname, main_ps.join(", "), ret_ty.map(|t| format!(" -> {}", t)).unwrap_or_default()).unwrap();
        for (name, w, reassigned) in &rx.params {
            if *reassigned {
                writeln!(s, "  var {}: bits[{}] = {}_in", name, w, name).unwrap();
            }
        }
        for (v, w) in &rx.vars {
            if !rx.params.iter().any(|(p, _, _)| p == v) {
                writeln!(s, "  var {}: bits[{}] = any bits[{}]", v, w, w).unwrap();
            }
        }
        let first = rx.f.blocks[self.past(rx, 0)].num;
        if void {
            writeln!(s, "  {}__b{}({})\n  return", tf, first, targs).unwrap();
        } else {
            writeln!(s, "  let r = {}__b{}({})\n  return r", tf, first, targs).unwrap();
        }
        writeln!(s, "}}").unwrap();
        (rx.out, rx.depth) = saved;
        Ok(())
    }

    /// the blocks bs (by number): which one, by comparisons of `bb`
    fn dispatch(&mut self, rx: &mut Rx, sh: &mut Shared, bs: &[usize]) -> Result<(), String> {
        if let [b] = bs {
            return self.cfg_block(rx, sh, *b);
        }
        let m = bs.len() / 2;
        self.line(rx, format!("if bb < {} {{", rx.f.blocks[bs[m]].num));
        rx.depth += 1;
        self.dispatch(rx, sh, &bs[..m])?;
        rx.depth -= 1;
        self.line(rx, "} else {".into());
        rx.depth += 1;
        self.dispatch(rx, sh, &bs[m..])?;
        rx.depth -= 1;
        self.line(rx, "}".into());
        Ok(())
    }

    /// one block: its statements, then where it goes
    fn cfg_block(&mut self, rx: &mut Rx, sh: &mut Shared, b: usize) -> Result<(), String> {
        let blk = &rx.f.blocks[b];
        self.line(rx, format!("// <bb {}>", blk.num));
        let k = blk.stmts.len();
        for (i, s) in blk.stmts.iter().enumerate() {
            if i + 1 == k && matches!(s, S::Goto(_) | S::If { .. }) {
                break;
            }
            rx.emitted += 1;
            self.rstmt(rx, sh, s).map_err(|e| format!("block {}: {}: {:?}", blk.num, e, s))?;
        }
        let go = |g: &mut Self, rx: &mut Rx, sh: &mut Shared, to: usize| -> Result<(), String> {
            // (past forwarders: each edge's phis' copies)
            let (mut from, mut to) = (b, to);
            for _ in 0..rx.f.blocks.len() {
                for l in g.phi_copies(rx, sh, from, to)? {
                    g.line(rx, l);
                }
                if !g.forwarder(rx, to) {
                    break;
                }
                from = to;
                to = rx.succ[to][0];
            }
            if g.return_only(rx, to) {
                return g.emit_tail(rx, sh, to);
            }
            match rx.tail.clone() {
                // (a block as its procedure: the next block's, a tail call)
                Some((f, args, void)) => {
                    let num = rx.f.blocks[to].num;
                    if void {
                        g.line(rx, format!("{}__b{}({})", f, num, args));
                        g.line(rx, "return".into());
                    } else {
                        g.line(rx, format!("let r = {}__b{}({})", f, num, args));
                        g.line(rx, "return r".into());
                    }
                }
                None => g.line(rx, format!("bb := {}", rx.f.blocks[to].num)),
            }
            Ok(())
        };
        match blk.stmts.last().cloned() {
            Some(S::Return(_)) => Ok(()),
            Some(S::If { op, a, b: c, .. }) => {
                let cond = self.cond(rx, sh, &op, &a, &c)?;
                let (yes, no) = (rx.succ[b][0], rx.succ[b][1]);
                self.line(rx, format!("if {} {{", cond));
                rx.depth += 1;
                go(self, rx, sh, yes)?;
                rx.depth -= 1;
                self.line(rx, "} else {".into());
                rx.depth += 1;
                go(self, rx, sh, no)?;
                rx.depth -= 1;
                self.line(rx, "}".into());
                Ok(())
            }
            _ => {
                let to = rx.succ[b][0];
                go(self, rx, sh, to)
            }
        }
    }

    /// an assignment to a GIMPLE temporary of a value defined whatever it
    /// computes: names, numbers, casts, comparisons, bitwise operations,
    /// and unsigned (wrapping) arithmetic -- no load, division, pointer or
    /// signed arithmetic (undefined at an overflow)
    fn total_stmt(&self, rx: &Rx, st: &S) -> bool {
        let S::Assign(E::Name(d), rhs) = st else { return false };
        d.starts_with('_') && self.total_expr(rx, rhs)
    }

    fn total_expr(&self, rx: &Rx, e: &E) -> bool {
        let unsigned = |x: &E| matches!(self.type_of(&rx.fx, x), Ok(RT::Int { signed: false, .. }));
        let int = |x: &E| matches!(self.type_of(&rx.fx, x), Ok(RT::Int { .. }));
        match e {
            E::Name(_) | E::Num(_) => true,
            E::Cast(_, x) => int(x) && self.total_expr(rx, x),
            E::Not(x) => int(x) && self.total_expr(rx, x),
            E::Neg(x) => unsigned(x) && self.total_expr(rx, x),
            E::Bin(op, a, b) => {
                let ok = match op.as_str() {
                    "==" | "!=" | "<" | "<=" | ">" | ">=" | "&" | "|" | "^" => int(a) || int(b),
                    // (a literal takes the other operand's type)
                    "+" | "-" | "*" => (unsigned(a) || matches!(**a, E::Num(_))) && (unsigned(b) || matches!(**b, E::Num(_))) && (unsigned(a) || unsigned(b)),
                    _ => false,
                };
                ok && self.total_expr(rx, a) && self.total_expr(rx, b)
            }
            _ => false,
        }
    }

    /// Assignments of the phis of `to` on the edge from `from` (none when
    /// the phi joins versions of one C variable).
    fn phi_copies(&mut self, rx: &mut Rx, sh: &mut Shared, from: usize, to: usize) -> Result<Vec<String>, String> {
        let from_num = rx.f.blocks[from].num;
        let phis = rx.f.blocks[to].phis.clone();
        let mut out = Vec::new();
        for p in &phis {
            let d = rx.rn.get(&p.dst).cloned().ok_or_else(|| format!("phi of {}", p.dst))?;
            let Some((e, _)) = p.args.iter().find(|(_, b)| *b == from_num) else { continue };
            if let E::Name(n) = e {
                if rx.rn.get(n) == Some(&d) {
                    continue;
                }
            }
            let x = self.name(&mut rx.fx, &p.dst)?;
            let w = rx.fx.types[x].0;
            let v = self.val(rx, sh, e, w)?;
            out.push(format!("{} := {}", d, v));
        }
        Ok(out)
    }

    /// the value of an operand as a word of `prec` bits
    fn val(&mut self, rx: &mut Rx, sh: &mut Shared, e: &E, prec: u64) -> Result<String, String> {
        match e {
            E::Num(n) => Ok(lit(*n, prec)),
            E::Name(s) if self.is_value_name(&rx.fx, s) => rx.rn.get(s).cloned().ok_or_else(|| format!("no name for {}", s)),
            E::Addr(r) => {
                let (b, o) = self.raddr(rx, sh, r)?;
                Ok(if o == 0 { b } else { format!("padd({}, {})", b, lit(o, 64)) })
            }
            _ => self.load(rx, sh, e),
        }
    }

    /// a literal-safe operand: a typed literal where the context cannot fix
    /// the type
    fn tval(&mut self, rx: &mut Rx, sh: &mut Shared, e: &E, prec: u64) -> Result<String, String> {
        let v = self.val(rx, sh, e, prec)?;
        Ok(if matches!(e, E::Num(_)) { format!("bits[{}]({})", prec, v) } else { v })
    }

    /// the address of a memory reference: an expression and a constant offset
    fn raddr(&mut self, rx: &mut Rx, sh: &mut Shared, e: &E) -> Result<(String, i128), String> {
        match e {
            E::Name(s) => {
                if let Some((k, _)) = rx.fx.objs.get(s) {
                    return Ok((format!("objs[{}]", k), 0));
                }
                if let Some(&a) = rx.fx.statics.get(s) {
                    sh.globals.insert(sanitize(s), a);
                    return Ok((sanitize(s), 0));
                }
                if self.is_value_name(&rx.fx, s) {
                    return Err(format!("the address of value `{}`", s));
                }
                let a = self.syms.addr(s).ok_or_else(|| format!("no symbol `{}`", s))?;
                sh.globals.insert(sanitize(s), a);
                Ok((sanitize(s), 0))
            }
            E::Mem { base, off, .. } => {
                let (b, o) = match &**base {
                    E::Addr(r) => self.raddr(rx, sh, r)?,
                    other => (self.val(rx, sh, other, 64)?, 0),
                };
                Ok((b, o + off))
            }
            E::Deref(p) => Ok((self.val(rx, sh, p, 64)?, 0)),
            E::Field(r, f) => {
                let t = self.type_of(&rx.fx, r)?;
                let (bit, _, bf) = self.member(&t, f)?;
                if bf.is_some() {
                    return Err(format!("the address of bitfield `{}`", f));
                }
                let (b, o) = self.raddr(rx, sh, r)?;
                Ok((b, o + (bit / 8) as i128))
            }
            E::Arrow(p, f) => self.raddr(rx, sh, &E::Field(Box::new(E::Deref(p.clone())), f.clone())),
            E::Index(r, ix) => {
                let et = match self.type_of(&rx.fx, r)? {
                    RT::Array(e, _) => *e,
                    t => return Err(format!("indexing a {:?}", t)),
                };
                let size = self.size(&et)?;
                let (b, o) = self.raddr(rx, sh, r)?;
                if let E::Num(n) = &**ix {
                    return Ok((b, o + n * size as i128));
                }
                let (ip, is) = self.scalar(&self.type_of(&rx.fx, ix)?)?;
                let i = self.val(rx, sh, ix, ip)?;
                let i64s = if ip == 64 { i } else if is { format!("sext[64]({})", i) } else { format!("zext[64]({})", i) };
                let base = if o == 0 { b } else { format!("padd({}, {})", b, lit(o, 64)) };
                Ok((format!("elem({}, {}, {})", base, i64s, size), 0))
            }
            _ => Err(format!("not a memory reference: {:?}", e)),
        }
    }

    /// the struct type and field of a field reference, and the struct's
    /// address
    fn field_ref(&mut self, rx: &mut Rx, sh: &mut Shared, e: &E) -> Result<Option<(u64, String, String, String)>, String> {
        let (r, f) = match e {
            E::Field(r, f) => ((**r).clone(), f.clone()),
            E::Arrow(p, f) => (E::Deref(p.clone()), f.clone()),
            _ => return Ok(None),
        };
        let t = self.type_of(&rx.fx, &r)?;
        let RT::Struct(die) = t else { return Ok(None) };
        // the struct's tag, or a typedef naming it
        let tag = self.dw.structs.iter().find(|(_, &d)| d == die).map(|(n, _)| n.clone());
        let tdef = || self.dw.typedefs.iter().find(|(_, &d)| matches!(self.dw.dies.get(&d), Some(DType::Typedef { to: Some(x) }) if *x == die)).map(|(n, _)| n.clone());
        let sname = tag.or_else(tdef).unwrap_or(format!("anon{}", die));
        let (b, o) = self.raddr(rx, sh, &r)?;
        let addr = if o == 0 { b } else { format!("padd({}, {})", b, lit(o, 64)) };
        Ok(Some((die, sname, f, addr)))
    }

    /// The accessor for a field (made on first use); its value width.
    fn accessor(&mut self, sh: &mut Shared, die: u64, sname: &str, field: &str, store: bool) -> Result<(String, u64), String> {
        let (bit, mt, bf) = self.member(&RT::Struct(die), field)?;
        let base = format!("{}_{}", sanitize(sname), sanitize(field));
        let (p, _) = self.scalar(&mt)?;
        let name = if store { format!("set_{}", base) } else { base };
        if !sh.accessors.contains_key(&name) {
            // (a bitfield's bytes: the smallest aligned unit of 1, 2, 4 or 8
            // bytes holding it, as GCC accesses it -- within the field's
            // memory location, the run of adjacent bitfields, which C lets
            // the access touch; else the bytes it spans)
            let unit = |n: u64| {
                [1u64, 2, 4, 8]
                    .iter()
                    .map(|s| (bit / 8 / s * s, *s))
                    .find(|(o, s)| 8 * (o + s) >= bit + n)
                    .unwrap_or((bit / 8, (bit % 8 + n + 7) / 8))
            };
            let def = match (bf, store) {
                (Some(n), false) => {
                    let (byte, size) = unit(n);
                    format!("proc[World] {}(p: Addr) -> bits[{}] {{ return bits[{}](ldbf(p, {}, {}, {}, {})) }}", name, n, n, byte, size, bit - 8 * byte, n)
                }
                (Some(n), true) => {
                    let (byte, size) = unit(n);
                    format!("proc[World] {}(p: Addr, v: bits[{}]) {{ stbf(p, {}, {}, {}, {}, uint(v)) }}", name, n, byte, size, bit - 8 * byte, n)
                }
                (None, _) => {
                    let byte = bit / 8;
                    let size = self.size(&mt)?;
                    if ![1, 2, 4, 8, 16].contains(&size) {
                        return Err(format!("field `{}` of {} bytes", field, size));
                    }
                    let w = 8 * size;
                    if store {
                        format!("proc[World] {}(p: Addr, v: bits[{}]) {{ st{}(p, {}, {}) }}", name, p, w, byte, if p == w { "v".to_string() } else { format!("zext[{}](v)", w) })
                    } else if p == w {
                        format!("proc[World] {}(p: Addr) -> bits[{}] {{ return ld{}(p, {}) }}", name, p, w, byte)
                    } else {
                        format!("proc[World] {}(p: Addr) -> bits[{}] {{ return bits[{}](ld{}(p, {})) }}", name, p, p, w, byte)
                    }
                }
            };
            sh.accessors.insert(name.clone(), def);
        }
        Ok((name, bf.unwrap_or(p)))
    }

    /// a load (as an expression)
    fn load(&mut self, rx: &mut Rx, sh: &mut Shared, e: &E) -> Result<String, String> {
        if let Some((die, sname, field, addr)) = self.field_ref(rx, sh, e)? {
            let (acc, _) = self.accessor(sh, die, &sname, &field, false)?;
            return Ok(format!("{}({})", acc, addr));
        }
        let t = self.type_of(&rx.fx, e)?;
        let (p, _) = self.scalar(&t)?;
        if let E::BitRef(r, bits, pos) = e {
            let (b, o) = self.raddr(rx, sh, r)?;
            let (o, size, bp) = (o + (*pos / 8) as i128, (pos % 8 + bits + 7) / 8, pos % 8);
            return Ok(format!("bits[{}](ldbf({}, {}, {}, {}, {}))", bits, b, lit(o, 64), size, bp, bits));
        }
        let size = self.size(&t)?;
        if ![1, 2, 4, 8, 16].contains(&size) {
            return Err(format!("a load of {} bytes", size));
        }
        let (b, o) = self.raddr(rx, sh, e)?;
        let l = format!("ld{}({}, {})", 8 * size, b, lit(o, 64));
        Ok(if p == 8 * size { l } else { format!("bits[{}]({})", p, l) })
    }

    /// a condition `a op b` (on the operands' type)
    fn cond(&mut self, rx: &mut Rx, sh: &mut Shared, op: &str, a: &E, b: &E) -> Result<String, String> {
        let t = if matches!(a, E::Num(_)) { self.type_of(&rx.fx, b)? } else { self.type_of(&rx.fx, a)? };
        let (p, s) = self.scalar(&t)?;
        let (x, y) = (self.val(rx, sh, a, p)?, self.val(rx, sh, b, p)?);
        Ok(match (op, s) {
            ("==", _) => format!("{} = {}", x, y),
            ("!=", _) => format!("{} != {}", x, y),
            ("<", false) => format!("{} < {}", x, y),
            ("<=", false) => format!("{} <= {}", x, y),
            (">", false) => format!("{} < {}", y, x),
            (">=", false) => format!("{} <= {}", y, x),
            ("<", true) => format!("{} <s {}", x, y),
            ("<=", true) => format!("{} <=s {}", x, y),
            (">", true) => format!("{} <s {}", y, x),
            (">=", true) => format!("{} <=s {}", y, x),
            (o, _) => return Err(format!("condition {}", o)),
        })
    }

    /// assign a value name: `let` or `:=`
    fn set(&mut self, rx: &mut Rx, name: &str, v: String) -> Result<(), String> {
        let r = rx.rn.get(name).cloned().ok_or_else(|| format!("no name for {}", name))?;
        let l = if rx.lets.contains(name) {
            // a literal needs its width (a variable has a declared type)
            let is_lit = v.trim_start_matches('-').chars().next().is_some_and(|c| c.is_ascii_digit()) && !v.contains(' ');
            let v = if is_lit {
                let x = self.name(&mut rx.fx, name)?;
                format!("bits[{}]({})", rx.fx.types[x].0, v)
            } else {
                v
            };
            format!("let {} = {}", r, v)
        } else {
            format!("{} := {}", r, v)
        };
        self.line(rx, l);
        Ok(())
    }

    fn rstmt(&mut self, rx: &mut Rx, sh: &mut Shared, s: &S) -> Result<(), String> {
        match s {
            S::Assign(lhs, rhs) => self.rassign(rx, sh, lhs, rhs),
            S::Call(Some(E::Name(x)), f, args) if f == ".MUL_OVERFLOW" || f == ".CTZ" => {
                let (ap, as_) = self.scalar(&self.type_of(&rx.fx, &args[0])?)?;
                let a = self.tval(rx, sh, &args[0], ap)?;
                let v = if f == ".CTZ" {
                    if args.len() > 1 {
                        return Err(".CTZ with a value for 0 (not yet in readable form)".into());
                    }
                    format!("ctz({})", a)
                } else {
                    format!("mul_ovf({}, {}, {})", a, self.val(rx, sh, &args[1], ap)?, as_)
                };
                let xi = self.name(&mut rx.fx, x)?;
                let xp = rx.fx.types[xi].0;
                let v = if f == ".CTZ" && xp != ap { format!("bits[{}]({})", xp, v) } else { v };
                self.set(rx, x, v)
            }
            S::Call(_, f, _) if f.starts_with('.') => Err(format!("internal function {} (not yet in readable form)", f)),
            S::Call(lhs, f, args) => {
                let fname = sanitize(f);
                if !rx.callees.contains(&fname) {
                    rx.callees.push(fname.clone());
                }
                let ptys: Vec<RT> = self.dw.params.get(f).map(|ps| ps.iter().filter_map(|&t| self.dwarf_rt(t).ok()).collect()).unwrap_or_default();
                let mut av = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let t = match (ptys.get(i), a) {
                        (Some(t), _) => t.clone(),
                        (None, E::Num(_)) => RT::int(64, false),
                        (None, a) => self.type_of(&rx.fx, a)?,
                    };
                    let (p, _) = self.scalar(&t)?;
                    av.push(format!("arg({})", self.tval(rx, sh, a, p)?));
                }
                let objs = !rx.fx.obj_list.is_empty();
                let (c1, c2) = if objs { ("call1_objs(objs, ", "call_objs(objs, ") } else { ("call1(", "call(") };
                match lhs {
                    None => {
                        let l = format!("{}{}, [{}])", c2, fname, av.join(", "));
                        self.line(rx, l);
                    }
                    Some(E::Name(n)) if self.is_value_name(&rx.fx, n) => {
                        let x = self.name(&mut rx.fx, n)?;
                        let w = rx.fx.types[x].0;
                        let v = format!("{}{}, [{}])", c1, fname, av.join(", "));
                        let v = if w == 64 { v } else { format!("bits[{}]({})", w, v) };
                        self.set(rx, n, v)?;
                    }
                    Some(m) => {
                        // a small struct returned in rax:rdx, stored to memory
                        let size = self.size(&self.type_of(&rx.fx, m)?)?;
                        let rest = size.saturating_sub(8);
                        if size <= 8 || ![1, 2, 4, 8].contains(&rest) {
                            return Err(format!("a struct result of {} bytes", size));
                        }
                        rx.emitted += 1;
                        let (w0, w1) = (format!("w{}_0", rx.emitted), format!("w{}_1", rx.emitted));
                        self.line(rx, format!("let ({}, {}) = {}{}, [{}])", w0, w1, c2, fname, av.join(", ")));
                        let (b, o) = self.raddr(rx, sh, m)?;
                        self.line(rx, format!("st64({}, {}, {})", b, lit(o, 64), w0));
                        let hi = if rest == 8 { w1 } else { format!("bits[{}]({})", 8 * rest, w1) };
                        self.line(rx, format!("st{}({}, {}, {})", 8 * rest, b, lit(o + 8, 64), hi));
                    }
                }
                Ok(())
            }
            S::Asm { tmpl, outs, ins } if outs.is_empty() && ins.is_empty() => {
                let code = assemble(tmpl)?;
                let bytes: Vec<String> = code.iter().map(|b| b.to_string()).collect();
                self.line(rx, format!("inline_asm([{}], [])", bytes.join(", ")));
                Ok(())
            }
            // the atomic primitives (layers/gimple.sl): x86_64's a_cas, a
            // 32-bit compare-and-swap -- "=a"(t), "=m"(*p) : "a"(t), "r"(s)
            S::Asm { tmpl, outs, ins } if tmpl.split_whitespace().collect::<Vec<_>>().join(" ") == "lock ; cmpxchg %3, %1" => {
                let shape = || -> Option<(&String, &E, &E, &E)> {
                    let [(c0, E::Name(t)), (c1, E::Deref(p))] = outs.as_slice() else { return None };
                    let [(c2, t_in), (c3, s)] = ins.as_slice() else { return None };
                    (c0 == "=a" && c1 == "=m" && c2 == "a" && c3 == "r").then_some((t, &**p, t_in, s))
                };
                let (t, p, t_in, s) = shape().ok_or("lock cmpxchg with other operands")?;
                for e in [t_in, s] {
                    if self.scalar(&self.type_of(&rx.fx, e)?)?.0 != 32 {
                        return Err("lock cmpxchg of other than 32 bits".into());
                    }
                }
                let v = format!("cas32({}, {}, {})", self.val(rx, sh, p, 64)?, self.val(rx, sh, t_in, 32)?, self.val(rx, sh, s, 32)?);
                self.set(rx, t, v)
            }
            S::Asm { .. } => Err("inline assembly with operands (not yet in readable form)".into()),
            S::Return(None) => {
                self.line(rx, "return".into());
                Ok(())
            }
            S::Return(Some(e)) => {
                let t = rx.fx.ret.clone();
                if let RT::Struct(_) = t {
                    // a small struct: its two words in rax:rdx
                    let size = self.size(&t)?;
                    let rest = size.saturating_sub(8);
                    if size <= 8 || ![1, 2, 4, 8].contains(&rest) {
                        return Err(format!("a struct result of {} bytes", size));
                    }
                    let (b, o) = self.raddr(rx, sh, e)?;
                    let hi = format!("ld{}({}, {})", 8 * rest, b, lit(o + 8, 64));
                    let hi = if rest == 8 { hi } else { format!("zext[64]({})", hi) };
                    self.line(rx, format!("return (ld64({}, {}), {})", b, lit(o, 64), hi));
                    return Ok(());
                }
                let (p, _) = self.scalar(&t)?;
                let v = self.val(rx, sh, e, p)?;
                self.line(rx, format!("return {}", v));
                Ok(())
            }
            _ => Err("control flow in the middle of a block".into()),
        }
    }

    fn rassign(&mut self, rx: &mut Rx, sh: &mut Shared, lhs: &E, rhs: &E) -> Result<(), String> {
        let value_lhs = matches!(lhs, E::Name(n) if self.is_value_name(&rx.fx, n));
        if !value_lhs {
            // a store
            let t = self.type_of(&rx.fx, lhs)?;
            if let E::Ctor(vals) = rhs {
                let size = self.size(&t)?;
                let bytes: Vec<u8> = if vals.is_empty() {
                    vec![0; size as usize]
                } else {
                    let n = vals.len() as u64;
                    let lane = size / n;
                    let mut b = Vec::new();
                    for v in vals {
                        let E::Num(v) = v else { return Err("non-constant aggregate".into()) };
                        let w = wrap(*v, 8 * lane);
                        for i in 0..lane {
                            b.push((w >> (8 * i)) as u8);
                        }
                    }
                    b
                };
                let (b, o) = self.raddr(rx, sh, lhs)?;
                let data: Vec<String> = bytes.iter().map(|b| b.to_string()).collect();
                self.line(rx, format!("st_bytes({}, {}, [{}])", b, lit(o, 64), data.join(", ")));
                return Ok(());
            }
            let (p, _) = self.scalar(&t)?;
            let v = self.val(rx, sh, rhs, p)?;
            if let Some((die, sname, field, addr)) = self.field_ref(rx, sh, lhs)? {
                let (acc, _) = self.accessor(sh, die, &sname, &field, true)?;
                self.line(rx, format!("{}({}, {})", acc, addr, v));
                return Ok(());
            }
            if let E::BitRef(..) = lhs {
                return Err("a store to BIT_FIELD_REF".into());
            }
            let size = self.size(&t)?;
            if ![1, 2, 4, 8, 16].contains(&size) {
                return Err(format!("a store of {} bytes", size));
            }
            let (b, o) = self.raddr(rx, sh, lhs)?;
            let v = if p == 8 * size { v } else { format!("zext[{}]({})", 8 * size, v) };
            self.line(rx, format!("st{}({}, {}, {})", 8 * size, b, lit(o, 64), v));
            return Ok(());
        }
        let E::Name(xn) = lhs else { unreachable!() };
        let x = self.name(&mut rx.fx, xn)?;
        let (xp, xs) = rx.fx.types[x];
        let is_ptr = matches!(self.name_ty(&rx.fx, xn)?, RT::Ptr(_));
        let v = match rhs {
            E::Bin(op, a, b) => {
                let cmp = ["==", "!=", "<", "<=", ">", ">="].contains(&op.as_str());
                if cmp {
                    let c = self.cond(rx, sh, op, a, b)?;
                    if xp == 1 { format!("b1({})", c) } else { format!("bits[{}](if {} {{ 1 }} else {{ 0 }})", xp, c) }
                } else if op == "+" && is_ptr {
                    format!("padd({}, {})", self.val(rx, sh, a, 64)?, self.val(rx, sh, b, 64)?)
                } else if op == "<<" || op == ">>" {
                    let x = self.tval(rx, sh, a, xp)?;
                    let k = match &**b {
                        E::Num(k) if (*k as u128) < xp as u128 => Some(k.to_string()),
                        _ => None,
                    };
                    match (op.as_str(), k) {
                        ("<<", Some(k)) => format!("{} << {}", x, k),
                        (">>", Some(k)) => format!("{} {} {}", x, if xs { ">>s" } else { ">>" }, k),
                        (o, None) => {
                            let (bp, _) = self.scalar(&self.type_of(&rx.fx, b)?)?;
                            let k = self.val(rx, sh, b, bp)?;
                            let h = if o == "<<" { "shl" } else if xs { "sar" } else { "shr" };
                            format!("{}({}, uint({}))", h, x, k)
                        }
                        _ => unreachable!(),
                    }
                } else {
                    let (x, y) = (self.tval(rx, sh, a, xp)?, self.val(rx, sh, b, xp)?);
                    match (op.as_str(), xs) {
                        ("+", true) => format!("sadd({}, {})", x, y),
                        ("-", true) => format!("ssub({}, {})", x, y),
                        ("*", true) => format!("smul({}, {})", x, y),
                        ("+", false) => format!("{} + {}", x, y),
                        ("-", false) => format!("{} - {}", x, y),
                        ("*", false) => format!("{} * {}", x, y),
                        ("/", s) => format!("cdiv({}, {}, {})", x, y, s),
                        ("%", s) => format!("crem({}, {}, {})", x, y, s),
                        ("&", _) => format!("{} & {}", x, y),
                        ("|", _) => format!("{} | {}", x, y),
                        ("^", _) => format!("{} xor {}", x, y),
                        (o, _) => return Err(format!("operator {}", o)),
                    }
                }
            }
            E::Code(c, args) if c == "MIN_EXPR" || c == "MAX_EXPR" => {
                let (x, y) = (self.tval(rx, sh, &args[0], xp)?, self.val(rx, sh, &args[1], xp)?);
                let h = match (c.as_str(), xs) {
                    ("MIN_EXPR", true) => "smin",
                    ("MIN_EXPR", false) => "umin",
                    (_, true) => "smax",
                    _ => "umax",
                };
                format!("{}({}, {})", h, x, y)
            }
            E::Code(c, args) if c == "IMAGPART_EXPR" || c == "REALPART_EXPR" => {
                // a complex value: the real part in the low half
                let (cp, _) = self.scalar(&self.type_of(&rx.fx, &args[0])?)?;
                let v = self.val(rx, sh, &args[0], cp)?;
                if c == "IMAGPART_EXPR" { format!("bits[{}]({} >> {})", xp, v, cp / 2) } else { format!("bits[{}]({})", xp, v) }
            }
            E::Neg(a) => {
                let x = self.tval(rx, sh, a, xp)?;
                if xs { format!("sneg({})", x) } else { format!("0 - {}", x) }
            }
            E::Not(a) => format!("~{}", self.tval(rx, sh, a, xp)?),
            E::Cast(_, a) => {
                let (fp, fs) = match &**a {
                    E::Num(_) => (xp, xs),
                    other => self.scalar(&self.type_of(&rx.fx, other)?)?,
                };
                let v = self.val(rx, sh, a, fp)?;
                if matches!(**a, E::Num(_)) || fp == xp {
                    v
                } else if xp > fp {
                    format!("{}[{}]({})", if fs { "sext" } else { "zext" }, xp, v)
                } else {
                    format!("bits[{}]({})", xp, v)
                }
            }
            E::Num(_) | E::Addr(_) => self.val(rx, sh, rhs, xp)?,
            E::Name(n) if self.is_value_name(&rx.fx, n) => self.val(rx, sh, rhs, xp)?,
            E::Code(c, _) => return Err(format!("{} (not yet in readable form)", c)),
            _ => self.load(rx, sh, rhs)?,
        };
        self.set(rx, xn, v)
    }
}

/// the comparison with the opposite outcome
fn negate(op: &str) -> String {
    match op {
        "==" => "!=",
        "!=" => "==",
        "<" => ">=",
        "<=" => ">",
        ">" => "<=",
        ">=" => "<",
        o => o,
    }
    .to_string()
}
