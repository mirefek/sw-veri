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
    /// the unit's functions all run before main (`--startup`): its calls
    /// `call0` (gimple.sl: no thread required, set up by the callee)
    pub startup: bool,
}

/// Names the readable code must not shadow (gimple.sl's operations, SL
/// keywords, the state's fields).
const RESERVED: &[&str] = &[
    "sadd", "ssub", "smul", "sneg", "cdiv", "crem", "div", "rem", "shl", "shr", "sar", "smin", "smax", "umin", "umax", "b1", "padd", "mem", "ld8", "ld16",
    "ld32", "ld64", "ld128", "st8", "st16", "st32", "st64", "st128", "st_bytes", "ldbf", "stbf", "call", "call1", "call_objs", "call1_objs", "call_s", "call1_s", "call0", "call1_0", "call0_objs", "call1_0_objs",
    "arg", "result", "elem", "inline_asm", "alloc_objs", "objs", "args", "any", "let", "var", "if", "else", "match", "while", "for", "in",
    "return", "fn", "proc", "pred", "type", "state", "self", "true", "false", "loop", "break", "either", "or", "havoc", "where", "require",
    "undefined", "ghost", "emit", "raise", "try", "catch", "vm", "os", "sp", "cpu", "fs_base", "uint", "sint", "zext", "sext", "bits",
    "nat", "int", "bool", "len", "all", "ex", "some", "none", "min", "max", "view", "with", "layer", "uses", "const", "law", "param",
];

/// the code map parameter of a function calling through pointers: the
/// function at each address
const FPTR: &str = "fptr";

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
        Some(S::Return(_)) | Some(S::Unreachable) => vec![],
        _ if i + 1 < f.blocks.len() => vec![i + 1],
        _ => return Err(format!("block {} has no successor", f.blocks[i].num)),
    })
}

struct Rx<'f> {
    f: &'f Func,
    fx: Fx,
    succ: Vec<Vec<usize>>,
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
    /// the callees called with more than six arguments (the rest on the
    /// stack: `CFunS`)
    callees_s: BTreeSet<String>,
    out: Vec<String>,
    depth: usize,
    emitted: usize,
    /// the statement written: its block's number, its index (names fresh
    /// by place, the same in every form)
    at: (u64, usize),
    /// the small structs held as words (`word_structs`): local -> its
    /// fields (C name, variable) in order
    words: BTreeMap<String, Vec<(String, String)>>,
}

/// a statement's word-struct variables (`word_structs`) written and read:
/// a field's as `n.f`, all of n's as n whole
fn word_defs_uses(s: &S, ws: &BTreeMap<String, Vec<(String, String)>>) -> (Vec<String>, Vec<String>) {
    fn reads(e: &E, ws: &BTreeMap<String, Vec<(String, String)>>, out: &mut Vec<String>) {
        if let E::Field(x, f) = e {
            if let E::Name(n) = &**x {
                if let Some(fs) = ws.get(n) {
                    out.extend(fs.iter().filter(|(g, _)| g == f).map(|(_, v)| v.clone()));
                    return;
                }
            }
        }
        match e {
            E::Name(n) => out.extend(ws.get(n).into_iter().flatten().map(|(_, v)| v.clone())),
            E::Num(_) | E::Str(_) => {}
            E::Addr(x) | E::Deref(x) | E::Neg(x) | E::Not(x) | E::Cast(_, x) | E::Field(x, _) | E::Arrow(x, _) | E::BitRef(x, _, _) => reads(x, ws, out),
            E::Index(a, b) | E::Bin(_, a, b) => {
                reads(a, ws, out);
                reads(b, ws, out)
            }
            E::Mem { base, .. } => reads(base, ws, out),
            E::Call(_, xs) | E::Code(_, xs) | E::Ctor(xs) => xs.iter().for_each(|x| reads(x, ws, out)),
        }
    }
    // (a target: n's variables, or n.f's)
    let target = |e: &E, d: &mut Vec<String>, u: &mut Vec<String>| match e {
        E::Name(n) => d.extend(ws.get(n).into_iter().flatten().map(|(_, v)| v.clone())),
        E::Field(x, f) if matches!(&**x, E::Name(n) if ws.contains_key(n)) => {
            let E::Name(n) = &**x else { unreachable!() };
            d.extend(ws[n].iter().filter(|(g, _)| g == f).map(|(_, v)| v.clone()))
        }
        other => reads(other, ws, u),
    };
    let (mut d, mut u) = (Vec::new(), Vec::new());
    match s {
        S::Assign(l, r) => {
            reads(r, ws, &mut u);
            target(l, &mut d, &mut u);
        }
        S::Call(l, _, args) => {
            args.iter().for_each(|a| reads(a, ws, &mut u));
            if let Some(l) = l {
                target(l, &mut d, &mut u);
            }
        }
        S::Asm { outs, ins, .. } => {
            ins.iter().for_each(|(_, e)| reads(e, ws, &mut u));
            outs.iter().for_each(|(_, e)| target(e, &mut d, &mut u));
        }
        S::Return(Some(e)) => reads(e, ws, &mut u),
        S::If { a, b, .. } => {
            reads(a, ws, &mut u);
            reads(b, ws, &mut u)
        }
        _ => {}
    }
    (d, u)
}

/// e uses n only as `n.f` (no address of it or of a field)
fn field_only(e: &E, n: &str) -> bool {
    let mentions = |x: &E| {
        let mut v = Vec::new();
        walk_e(x, &mut v);
        v.iter().any(|m| m == n)
    };
    match e {
        E::Field(x, _) if matches!(&**x, E::Name(m) if m == n) => true,
        E::Name(m) => m != n,
        E::Num(_) | E::Str(_) => true,
        E::Addr(x) => !mentions(x),
        E::Deref(x) | E::Neg(x) | E::Not(x) | E::Cast(_, x) | E::Field(x, _) | E::Arrow(x, _) | E::BitRef(x, _, _) => field_only(x, n),
        E::Index(a, b) | E::Bin(_, a, b) => field_only(a, n) && field_only(b, n),
        E::Mem { base, .. } => field_only(base, n),
        E::Call(_, xs) | E::Code(_, xs) | E::Ctor(xs) => xs.iter().all(|x| field_only(x, n)),
    }
}

/// a statement's uses of the word struct n: as a whole set from {}, from a
/// call or from another word struct, copied into one, returned; else a
/// field at a time
fn word_use_ok(s: &S, n: &str, ws: &BTreeMap<String, Vec<(String, String)>>) -> bool {
    let whole = |e: &E| matches!(e, E::Name(m) if m == n);
    let other = |e: &E| matches!(e, E::Name(m) if m != n && ws.contains_key(m));
    match s {
        S::Assign(l, r) if whole(l) => matches!(r, E::Ctor(v) if v.is_empty()) || other(r),
        S::Assign(l, r) if whole(r) => other(l),
        S::Assign(l, r) => field_only(l, n) && field_only(r, n),
        S::Call(l, _, args) => l.as_ref().is_none_or(|l| whole(l) || field_only(l, n)) && args.iter().all(|a| field_only(a, n)),
        S::Return(Some(e)) => whole(e) || field_only(e, n),
        S::If { a, b, .. } => field_only(a, n) && field_only(b, n),
        S::Asm { outs, ins, .. } => outs.iter().chain(ins.iter()).all(|(_, e)| field_only(e, n)),
        _ => true,
    }
}

fn walk_e(e: &E, out: &mut Vec<String>) {
    match e {
        E::Name(n) => out.push(n.clone()),
        E::Num(_) | E::Str(_) => {}
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
        S::Call(l, f, args) => {
            match l {
                Some(E::Name(n)) => d.push(n.clone()),
                Some(other) => walk_e(other, &mut u),
                None => {}
            }
            // (a call through a pointer: its value used)
            if super::is_ssa(f) {
                u.push(f.clone());
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
        let (mut fx, _) = self.frame(f)?;
        let words = self.word_structs(f, &mut fx)?;
        let index: HashMap<u64, usize> = f.blocks.iter().enumerate().map(|(i, b)| (b.num, i)).collect();
        let n = f.blocks.len();
        let mut succ = Vec::new();
        for i in 0..n {
            succ.push(succs(f, &index, i)?);
        }
        let mut rx = Rx {
            f,
            fx,
            succ,
            rn: HashMap::new(),
            lets: BTreeSet::new(),
            vars: BTreeMap::new(),
            params: Vec::new(),
            callees: Vec::new(),
            callees_s: BTreeSet::new(),
            out: Vec::new(),
            depth: 1,
            emitted: 0,
            at: (0, 0),
            words,
        };
        for fs in rx.words.values() {
            for (_, v) in fs {
                rx.vars.insert(v.clone(), 64);
            }
        }
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
        let callees_s = rx.callees_s.clone();
        let cty = |c: &String| if c == FPTR { "Addr -> CFun2[World]" } else if callees_s.contains(c) { "CFunS[World]" } else { "CFun2[World]" };
        for c in &rx.callees {
            ps.push(format!("{}: {}", c, cty(c)));
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
                // (a word struct's field: its struct and offset, for
                // scripts/locmap.py)
                let at = rx.words.iter().find_map(|(n, fs)| fs.iter().position(|(_, x)| x == v).map(|i| format!("  // {} + {}", n, 8 * i)));
                writeln!(s, "  var {}: bits[{}] = any bits[{}]{}", v, w, w, at.unwrap_or_default()).unwrap();
            }
        }
        if !rx.fx.obj_list.is_empty() {
            let objs: Vec<String> = rx.fx.obj_list.iter().map(|(sz, al)| format!("({}, {})", sz, al)).collect();
            // (the objects' C names, in order: scripts/locmap.py's)
            let mut names: Vec<(usize, &String)> = rx.fx.objs.iter().map(|(n, (k, _))| (*k, n)).collect();
            names.sort();
            let names: Vec<&str> = names.iter().map(|(_, n)| n.as_str()).collect();
            writeln!(s, "  let objs = alloc_objs([{}])  // {}", objs.join(", "), names.join(", ")).unwrap();
        }
        for l in &rx.out {
            writeln!(s, "{}", l).unwrap();
        }
        writeln!(s, "}}").unwrap();
        // (SLC_STRUCT_CHECK=1: the structuring of the CFG form read back
        // the same as of the blocks themselves)
        if cfg && std::env::var("SLC_STRUCT_CHECK").is_ok_and(|v| v == "1") {
            use crate::gimple::structure::{graph_of_cfg, render, structure};
            let ga = self.graph(&mut rx, sh)?;
            let (mut ta, mut tb) = (Vec::new(), Vec::new());
            render(&ga, &structure(&ga)?, 1, &mut ta);
            match graph_of_cfg(&s, &fname).and_then(|gb| structure(&gb).map(|t| (gb, t))) {
                Ok((gb, t)) => {
                    // (the cut labels: as the checker finds them, on the
                    // label graph alone)
                    use crate::gimple::structure::{cuts, label_cuts, label_leaves};
                    let c1 = cuts(&gb, &t);
                    match label_cuts(&label_leaves(&gb), gb.blocks[gb.entry].num) {
                        Ok(c2) if c2 == c1 => {}
                        Ok(c2) => eprintln!("structure check: {}: cut labels {:?}, on the label graph {:?}", fname, c1, c2),
                        Err(e) => eprintln!("structure check: {}: the label graph: {}", fname, e),
                    }
                    render(&gb, &t, 1, &mut tb);
                    if ta != tb {
                        let i = ta.iter().zip(tb.iter()).position(|(a, b)| a != b).unwrap_or(ta.len().min(tb.len()));
                        eprintln!("structure check: {}: differs at line {}: {:?} / {:?}", fname, i, ta.get(i), tb.get(i));
                        if let Ok(d) = std::env::var("SLC_STRUCT_DIR") {
                            let _ = std::fs::write(format!("{}/{}.ir", d, fname), ta.join("\n"));
                            let _ = std::fs::write(format!("{}/{}.cfg", d, fname), tb.join("\n"));
                        }
                    }
                }
                Err(e) => eprintln!("structure check: {}: {}", fname, e),
            }
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
        let cps: Vec<String> = rx.callees.iter().map(|c| format!("{}: {}", c, cty(c))).collect();
        let mut call_args: Vec<String> = rx.params.iter().enumerate().map(|(i, (_, w, _))| format!("bits[{}](args[{}])", w, i)).collect();
        call_args.extend(rx.callees.iter().cloned());
        // (more than six parameters: the rest on the stack)
        let (fty, aty) = if rx.params.len() > 6 { ("CFunS[World]", "ArgsS") } else { ("CFun2[World]", "Args") };
        writeln!(s, "fn {}_fun({}) -> {} = (args: {}) => {{", fname, cps.join(", "), fty, aty).unwrap();
        // a call with fewer arguments than the function's parameters is
        // undefined (the missing ones would be whatever the registers hold)
        if !rx.params.is_empty() {
            writeln!(s, "  require len(args) >= {}", rx.params.len()).unwrap();
        }
        // (a function's stack objects end with it: the world's as before --
        // its own bytes as the function left them; GCC's stack protector
        // with them -- the canary word at fs:0x28 -- the ABI's, never the
        // world's: the bridge's, not the spec's)
        let has_objs = !rx.fx.obj_list.is_empty();
        if has_objs {
            writeln!(s, "  let live0 = objs.live").unwrap();
        }
        let drop = if has_objs { "\n  objs := objs with { live: live0 }" } else { "" };
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

    /// The small structs whose address is never taken (two 8-byte scalar
    /// fields, as `struct mapinfo`; set from {}, a field at a time, from a
    /// call or another such struct, read a field at a time, returned): a
    /// variable per field (`x_f`) in place of a stack object -- GCC keeps
    /// them in frame slots or registers, as the other locals. Their objects
    /// dropped from fx's (the others renumbered).
    fn word_structs(&self, f: &Func, fx: &mut Fx) -> Result<BTreeMap<String, Vec<(String, String)>>, String> {
        let mut cand: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
        for (n, (_, t)) in fx.objs.iter() {
            let RT::Struct(s) = t else { continue };
            let Some(DType::Struct { members, .. }) = self.dw.dies.get(s) else { continue };
            if members.len() != 2 || self.size(t)? != 16 {
                continue;
            }
            let mut fs = Vec::new();
            let mut ok = true;
            for (i, m) in members.iter().enumerate() {
                let ty = self.dwarf_rt(m.ty)?;
                ok &= m.bit_size.is_none() && m.bit_off == 64 * i as u64 && self.scalar(&ty).is_ok_and(|(p, _)| p == 64);
                fs.push((m.name.clone(), sanitize(&format!("{}_{}", n, m.name))));
            }
            if ok {
                cand.insert(n.clone(), fs);
            }
        }
        // (any other use: a stack object -- and so the structs copied from
        // or into it)
        loop {
            let bad: Vec<String> = cand.keys().filter(|n| f.blocks.iter().any(|b| b.stmts.iter().any(|s| !word_use_ok(s, n, &cand)))).cloned().collect();
            if bad.is_empty() {
                break;
            }
            for n in bad {
                cand.remove(&n);
            }
        }
        let mut keep: Vec<(usize, String, RT)> = fx.objs.iter().filter(|(n, _)| !cand.contains_key(*n)).map(|(n, (k, t))| (*k, n.clone(), t.clone())).collect();
        keep.sort_by_key(|x| x.0);
        let old = std::mem::take(&mut fx.obj_list);
        fx.objs.clear();
        for (k, n, t) in keep {
            fx.objs.insert(n, (fx.obj_list.len(), t));
            fx.obj_list.push(old[k]);
        }
        Ok(cand)
    }

    /// a word struct's field: its variable
    fn word_var(&self, rx: &Rx, e: &E) -> Option<Result<String, String>> {
        let E::Field(x, fld) = e else { return None };
        let E::Name(n) = &**x else { return None };
        let fs = rx.words.get(n)?;
        Some(fs.iter().find(|(f, _)| f == fld).map(|(_, v)| v.clone()).ok_or_else(|| format!("no field `{}` of {}", fld, n)))
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
            // (the block's mark: one block, wherever written -- for the
            // structuring of this form, crate::gimple::structure)
            self.line(rx, format!("// <tail bb {}>", rx.f.blocks[b].num));
            for (i, st) in rx.f.blocks[b].stmts.clone().into_iter().enumerate() {
                if !matches!(st, S::Goto(_)) {
                    rx.at = (rx.f.blocks[b].num, i);
                    self.rstmt(rx, sh, &st)?;
                }
            }
            if matches!(rx.f.blocks[b].stmts.last(), Some(S::Return(_)) | Some(S::Unreachable)) {
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
        // (a word struct's field variables, by their readable names)
        let wpos = |v: &str| order.iter().position(|(x, _)| x == v);
        for b in 0..n {
            for st in &rx.f.blocks[b].stmts {
                let (d, u) = defs_uses(st);
                let (wd, wu) = word_defs_uses(st, &rx.words);
                for i in u.iter().filter_map(|x| pos(x)).chain(wu.iter().filter_map(|v| wpos(v))) {
                    if defs[b] & bit(i) == 0 {
                        uses[b] |= bit(i);
                    }
                }
                for i in d.iter().filter_map(|x| pos(x)).chain(wd.iter().filter_map(|v| wpos(v))) {
                    defs[b] |= bit(i);
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
                rx.at = (blk.num, i);
                self.rstmt(rx, sh, s).map_err(|e| format!("block {}: {}: {:?}", blk.num, e, s))?;
            }
            let stmts = std::mem::take(&mut rx.out);
            // (past forwarders, as the CFG form: each edge's copies)
            let edge = |g: &mut Self, rx: &mut Rx, sh: &mut Shared, to: usize| -> Result<Edge, String> {
                let (mut from, mut to, mut copies) = (b, to, Vec::new());
                for _ in 0..rx.f.blocks.len() {
                    copies.extend(g.phi_copies(rx, sh, from, to)?);
                    if !g.forwarder(rx, to) {
                        break;
                    }
                    from = to;
                    to = rx.succ[to][0];
                }
                Ok(Edge { to, copies })
            };
            let term = match blk.stmts.last() {
                Some(S::Return(_)) | Some(S::Unreachable) => Jump::Return,
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
        let labels = blocks.len();
        Ok(Graph { blocks, entry: self.past(rx, 0), labels })
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
            rx.at = (blk.num, i);
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
            g.line(rx, format!("bb := {}", rx.f.blocks[to].num));
            Ok(())
        };
        match blk.stmts.last().cloned() {
            Some(S::Return(_)) | Some(S::Unreachable) => Ok(()),
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
            E::Str(s) => {
                // (a constant named after its text: `str_dev_null`, `str_` for "")
                let name = format!("str_{}", sanitize(s.trim_matches(|c: char| !c.is_ascii_alphanumeric())));
                sh.globals.insert(name.clone(), self.lit_addr(s)?);
                Ok(name)
            }
            E::Name(s) if self.is_value_name(&rx.fx, s) => rx.rn.get(s).cloned().ok_or_else(|| format!("no name for {}", s)),
            // (a function's address: `f_at`, apart from its proc `f`)
            E::Name(s) if self.function_addr(&rx.fx, s).is_some() => {
                let name = format!("{}_at", sanitize(s));
                sh.globals.insert(name.clone(), self.function_addr(&rx.fx, s).unwrap_or(0));
                Ok(name)
            }
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
        if let Some(v) = self.word_var(rx, e) {
            return v;
        }
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
                // (a call through a pointer p: the function the code map
                // `fptr` has at p -- C1 links it to the code there)
                let fname = if self.is_value_name(&rx.fx, f) {
                    let p = self.val(rx, sh, &E::Name(f.clone()), 64)?;
                    if !rx.callees.iter().any(|c| c == FPTR) {
                        rx.callees.push(FPTR.to_string());
                    }
                    format!("{}[{}]", FPTR, p)
                } else {
                    let n = sanitize(f);
                    if !rx.callees.contains(&n) {
                        rx.callees.push(n.clone());
                    }
                    n
                };
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
                let stack = args.len() > 6;
                if stack {
                    if objs {
                        return Err(format!("a call of {} with stack arguments from a function with stack objects (not yet in readable form)", f));
                    }
                    rx.callees_s.insert(fname.clone());
                }
                let (c1, c2) = if stack && sh.startup {
                    ("call1_0_s(", "call0_s(")
                } else if stack {
                    ("call1_s(", "call_s(")
                } else if sh.startup && objs {
                    ("call1_0_objs(objs, ", "call0_objs(objs, ")
                } else if sh.startup {
                    ("call1_0(", "call0(")
                } else if objs {
                    ("call1_objs(objs, ", "call_objs(objs, ")
                } else {
                    ("call1(", "call(")
                };
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
                    // (into a word struct: its two words)
                    Some(E::Name(n)) if rx.words.contains_key(n) => {
                        let fs = rx.words[n].clone();
                        let (w0, w1) = (format!("w{}_{}_0", rx.at.0, rx.at.1), format!("w{}_{}_1", rx.at.0, rx.at.1));
                        self.line(rx, format!("let ({}, {}) = {}{}, [{}])", w0, w1, c2, fname, av.join(", ")));
                        self.line(rx, format!("{} := {}", fs[0].1, w0));
                        self.line(rx, format!("{} := {}", fs[1].1, w1));
                    }
                    Some(m) => {
                        // a small struct returned in rax:rdx, stored to memory
                        let size = self.size(&self.type_of(&rx.fx, m)?)?;
                        let rest = size.saturating_sub(8);
                        if size <= 8 || ![1, 2, 4, 8].contains(&rest) {
                            return Err(format!("a struct result of {} bytes", size));
                        }
                        let (w0, w1) = (format!("w{}_{}_0", rx.at.0, rx.at.1), format!("w{}_{}_1", rx.at.0, rx.at.1));
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
            // an empty template, each output tied to an input ("0"): no code,
            // the values copied (`__asm__("" : "+r"(stage2))`, hiding a value
            // from the optimizer)
            S::Asm { tmpl, outs, ins } if tmpl.trim().is_empty() && !outs.is_empty() => {
                for (k, (_, o)) in outs.iter().enumerate() {
                    let E::Name(x) = o else { return Err("an empty asm's output into memory".into()) };
                    let (_, i) = ins.iter().find(|(c, _)| c == &k.to_string()).ok_or("an empty asm's output not tied to an input")?;
                    let xi = self.name(&mut rx.fx, x)?;
                    let w = rx.fx.types[xi].0;
                    let v = self.val(rx, sh, i, w)?;
                    self.set(rx, x, v)?;
                }
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
            // x86_64's a_or: "=m"(*p) : "r"(v), a 32-bit or into memory
            S::Asm { tmpl, outs, ins } if tmpl.split_whitespace().collect::<Vec<_>>().join(" ") == "lock ; or %1, %0" => {
                let ([(c0, E::Deref(p))], [(c1, v)]) = (outs.as_slice(), ins.as_slice()) else { return Err("lock or with other operands".into()) };
                if c0 != "=m" || c1 != "r" || self.scalar(&self.type_of(&rx.fx, v)?)?.0 != 32 {
                    return Err("lock or other than of a 32-bit register into memory".into());
                }
                let l = format!("or32({}, {})", self.val(rx, sh, p, 64)?, self.val(rx, sh, v, 32)?);
                self.line(rx, l);
                Ok(())
            }
            // a system call (layers/gimple.sl's `sys_call1` / `sys_call2` /
            // `sys_call3` / `sys_call6`, by the arguments passed): x86_64's __syscallN --
            // "=a"(ret) : "a"(n), "D"(a1), "S"(a2), "d"(a3), ..; the
            // registers not passed are no argument of the call made
            S::Asm { tmpl, outs, ins } if tmpl.trim() == "syscall" => {
                let [(c0, E::Name(r))] = outs.as_slice() else { return Err("syscall with other outputs".into()) };
                if c0 != "=a" {
                    return Err("syscall's result not in rax".into());
                }
                let mut n = None;
                let mut a: Vec<Option<String>> = vec![None; 6];
                for (c, e) in ins {
                    if self.scalar(&self.type_of(&rx.fx, e)?)?.0 != 64 {
                        return Err("a syscall operand of other than 64 bits".into());
                    }
                    let v = self.val(rx, sh, e, 64)?;
                    // (an "r" operand a register variable: its register --
                    // __syscall4..6's r10, r8, r9)
                    let reg = match (c.as_str(), e) {
                        ("r", E::Name(x)) => rx.f.hard_regs.iter().find(|(nm, _)| nm == x).map(|(_, r)| r.as_str()).ok_or("a syscall \"r\" operand not a register variable")?,
                        (c, _) => c,
                    };
                    match reg {
                        "a" => n = Some(v),
                        "D" => a[0] = Some(v),
                        "S" => a[1] = Some(v),
                        "d" => a[2] = Some(v),
                        "r10" => a[3] = Some(v),
                        "r8" => a[4] = Some(v),
                        "r9" => a[5] = Some(v),
                        other => return Err(format!("syscall operand `{}` (not yet)", other)),
                    }
                }
                let n = n.ok_or("syscall without its number")?;
                let k = a.iter().take_while(|x| x.is_some()).count();
                if a[k..].iter().any(|x| x.is_some()) || ![1, 2, 3, 6].contains(&k) {
                    return Err(format!("syscall with {} arguments, or not the first ones (1, 2, 3 or 6 so far)", a.iter().flatten().count()));
                }
                let args: Vec<String> = a.into_iter().flatten().collect();
                self.set(rx, r, format!("sys_call{}({}, {})", k, n, args.join(", ")))
            }
            // the thread pointer (layers/gimple.sl's `thread_ptr`): __get_tp's
            // `mov %%fs:0,%0` -- "=r"(tp)
            S::Asm { tmpl, outs, ins } if tmpl.split_whitespace().collect::<String>() == "mov%%fs:0,%0" && ins.is_empty() => {
                let [(c0, E::Name(t))] = outs.as_slice() else { return Err("mov %fs:0 with other outputs".into()) };
                if c0 != "=r" {
                    return Err("mov %fs:0 into other than a register".into());
                }
                self.set(rx, t, "thread_ptr()".into())
            }
            S::Asm { .. } => Err("inline assembly with operands (not yet in readable form)".into()),
            S::Return(None) => {
                self.line(rx, "return".into());
                Ok(())
            }
            S::Unreachable => {
                self.line(rx, "undefined".into());
                Ok(())
            }
            S::Return(Some(e)) => {
                let t = rx.fx.ret.clone();
                // (a word struct: its words)
                if let Some(fs) = if let E::Name(n) = e { rx.words.get(n).cloned() } else { None } {
                    self.line(rx, format!("return ({}, {})", fs[0].1, fs[1].1));
                    return Ok(());
                }
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
        // a word struct set whole (from {}, or another's words) or a field
        if let Some(fs) = if let E::Name(n) = lhs { rx.words.get(n).cloned() } else { None } {
            let src = if let E::Name(m) = rhs { rx.words.get(m).cloned() } else { None };
            for (i, (_, v)) in fs.iter().enumerate() {
                let x = match &src {
                    Some(s) => s[i].1.clone(),
                    None => "0".to_string(),
                };
                self.line(rx, format!("{} := {}", v, x));
            }
            return Ok(());
        }
        if let Some(v) = self.word_var(rx, lhs) {
            let v = v?;
            let x = self.val(rx, sh, rhs, 64)?;
            self.line(rx, format!("{} := {}", v, x));
            return Ok(());
        }
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
            E::Num(_) | E::Addr(_) | E::Str(_) => self.val(rx, sh, rhs, xp)?,
            E::Name(n) if self.is_value_name(&rx.fx, n) || self.function_addr(&rx.fx, n).is_some() => self.val(rx, sh, rhs, xp)?,
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
