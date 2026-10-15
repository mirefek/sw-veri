//! `slc cputest`: differential testing of the instruction table against the
//! CPU this runs on.
//!
//! For every row of the spec's instruction table, random encodings of that
//! row and random machine states are generated; each case is executed on
//! the CPU (`cpu.rs`: every case ends with a signal, which tells where
//! control went or which exception was raised) and by the spec's own
//! `step()` (the interpreter); the CPU's behaviour must be one the spec
//! allows: the same exception, or a normal outcome with the same registers,
//! flags, memory and next rip. System calls run in a child process
//! (`sys.rs`) and are also compared on their I/O, memory map and exit.
//!
//! Each row runs in a subprocess, so an unexpected crash only fails its row.
//! Manual knowledge is kept in the case generators: `setup_hints` (registers
//! string instructions need), `aim_memory` / `aim_target` (where operands
//! and branch targets point) and `sys::generate` (system call arguments).

mod cpu;
mod sys;

use crate::commands::{repo_root, CResult};
use cpu::{CpuState, Fault, SIGBUS, SIGFPE, SIGILL, SIGSEGV, SIGTRAP};
use sl_interp::num::Int;
use sl_interp::{map, map_backed, same, Interp, Outcome, V};
use std::collections::{BTreeMap, BTreeSet};

const SCRATCH: u64 = 0x1000_0000; // 3 pages read/write, then read-only, write-only, exec-only
const SCRATCH_LEN: u64 = 0x6000;
const RO_PAGE: u64 = SCRATCH + 0x3000;
const WO_PAGE: u64 = SCRATCH + 0x4000;
const XO_PAGE: u64 = SCRATCH + 0x5000;
const DATA: u64 = SCRATCH + 0x1000; // memory operands land here
const CODE: u64 = 0x1001_0000; // one page read/write/execute; the instruction ends at CODE_END
const CODE_END: u64 = CODE + 0x1000; // a guard page (no access)

// ----------------------------------------------------------------------
//  Randomness (xorshift; deterministic per seed)

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }
    /// interesting 64-bit values
    fn value(&mut self) -> u64 {
        match self.below(10) {
            0 => 0,
            1 => u64::MAX,
            2 => 1u64 << self.below(64),
            3 => (1u64 << self.below(64)).wrapping_sub(1),
            4 => self.below(256),
            5 => 0x8000_0000_0000_0000 | self.below(4),
            6 => 0x7fff_ffff_ffff_ffff - self.below(4),
            7 => 0xffff_ffff_0000_0000 | self.next() >> 32,
            _ => self.next(),
        }
    }
}

// ----------------------------------------------------------------------
//  Spec machine states

fn bits(v: u64, w: u32) -> V {
    V::Num(Int::from_u128(v as u128), Some(w))
}

fn rec(fields: Vec<(&str, V)>) -> V {
    V::rec(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect::<BTreeMap<_, _>>())
}

const FLAG_BITS: [(&str, u32); 7] = [("cf", 0), ("pf", 2), ("af", 4), ("zf", 6), ("sf", 7), ("df", 10), ("of", 11)];

/// `some(Page { prot, kind: anon })` for prot bits r=1, w=2, x=4
fn page(prot: u8) -> V {
    let p = rec(vec![("r", V::Bool(prot & 1 != 0)), ("w", V::Bool(prot & 2 != 0)), ("x", V::Bool(prot & 4 != 0))]);
    V::Tag("some".into(), 1, vec![rec(vec![("prot", p), ("kind", V::n(0))])])
}

fn none() -> V {
    V::Tag("none".into(), 0, vec![])
}

fn xmm_value(x: [u64; 2]) -> V {
    V::Num(Int::from_u128(x[0] as u128 | (x[1] as u128) << 64), Some(128))
}

/// The spec's machine state for a case: the instruction at `start`, the
/// scratch pages, and (for system calls) the process environment.
/// The CPU features the spec depends on (`Cpu` in state.sl).
#[derive(Clone, Copy)]
struct Features {
    bmi1: bool,
    /// protection keys enabled by the OS (CPUID.7.0:ECX.OSPKE)
    pku: bool,
}

fn features() -> Features {
    let ecx = std::arch::x86_64::__cpuid_count(7, 0).ecx;
    Features { bmi1: std::arch::is_x86_feature_detected!("bmi1"), pku: ecx & (1 << 4) != 0 }
}

fn machine(st: &CpuState, scratch: &[u8], start: u64, insn: &[u8], cpu: Features, env: Option<&sys::SysEnv>) -> V {
    let gpr = map((0..16).map(|i| (V::n(i as i128), bits(st.gpr[i], 64))).collect(), None);
    let xmm = map((0..16).map(|i| (V::n(i as i128), xmm_value(st.xmm[i]))).collect(), None);
    let flags = V::rec(FLAG_BITS.iter().map(|(n, b)| (n.to_string(), V::Bool(st.flags >> b & 1 == 1))).collect());
    let pn = |a: u64| V::n((a >> 12) as i128);
    let mut pages = vec![
        (pn(SCRATCH), page(3)),
        (pn(SCRATCH + 0x1000), page(3)),
        (pn(SCRATCH + 0x2000), page(3)),
        (pn(RO_PAGE), page(1)),
        (pn(WO_PAGE), page(2)),
        (pn(XO_PAGE), page(4)),
        (pn(CODE), page(7)),
        (pn(CODE_END), page(0)),
    ];
    if let Some(env) = env {
        for (i, p) in env.arena.iter().enumerate() {
            pages.push((pn(sys::ARENA + 0x1000 * i as u64), p.map(page).unwrap_or_else(none)));
        }
    }
    // the scratch area is read lazily from the byte array
    let bytes: Vec<(V, V)> = insn.iter().enumerate().map(|(i, b)| (V::n((start + i as u64) as i128), bits(*b as u64, 8))).collect();
    let (brk_start, brk) = env.map(|e| (e.brk_start, e.brk)).unwrap_or((0, 0));
    let vm = rec(vec![
        ("pages", map(pages, Some(none()))),
        ("bytes", map_backed(bytes, Some(V::Unknown), SCRATCH, scratch.to_vec())),
        ("stack_top", bits(RO_PAGE, 64)),
        ("stack_limit", V::n(0x3000)),
        ("brk_start", bits(brk_start, 64)),
        ("brk", bits(brk, 64)),
    ]);
    let input = match env {
        Some(e) => V::tuple(e.input.iter().map(|b| bits(*b as u64, 8)).collect()),
        None => V::Unknown,
    };
    let os = rec(vec![("input", input), ("events", V::tuple(vec![])), ("creds", V::Unknown), ("secure", V::Bool(false))]);
    rec(vec![
        ("gpr", gpr),
        ("xmm", xmm),
        ("rip", bits(start, 64)),
        ("flags", flags),
        ("cpu", rec(vec![("bmi1", V::Bool(cpu.bmi1)), ("pku", V::Bool(cpu.pku))])),
        ("fs_base", bits(st.fs, 64)),
        ("gs_base", bits(st.gs, 64)),
        ("vm", vm),
        ("os", os),
    ])
}

const REG_NAMES: [&str; 16] = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];

fn chk(what: String, spec: Option<V>, cpu: V, diffs: &mut Vec<String>) {
    let spec = spec.unwrap_or(V::Unknown);
    if same(&spec, &cpu) == Some(false) {
        diffs.push(format!("{}: spec {} cpu {}", what, spec.render(), cpu.render()));
    }
}

/// Differences between a completed CPU run and one normal spec outcome.
/// Memory: `before` and `after` are the scratch area around the CPU run.
fn compare(out: &V, f: &Fault, rip: u64, before: &[u8], after: &[u8]) -> Vec<String> {
    let mut diffs = Vec::new();
    let st = &f.st;
    let gpr = out.field("gpr").cloned().unwrap_or(V::Unknown);
    let xmm = out.field("xmm").cloned().unwrap_or(V::Unknown);
    for i in 0..16 {
        chk(REG_NAMES[i].into(), gpr.map_get(&V::n(i as i128)), bits(st.gpr[i], 64), &mut diffs);
        chk(format!("xmm{}", i), xmm.map_get(&V::n(i as i128)), xmm_value(st.xmm[i]), &mut diffs);
    }
    let flags = out.field("flags").cloned().unwrap_or(V::Unknown);
    for (n, b) in FLAG_BITS {
        chk(n.into(), flags.field(n).cloned(), V::Bool(st.flags >> b & 1 == 1), &mut diffs);
    }
    chk("rip".into(), out.field("rip").cloned(), bits(rip, 64), &mut diffs);
    chk("fs_base".into(), out.field("fs_base").cloned(), bits(f.fs, 64), &mut diffs);
    chk("gs_base".into(), out.field("gs_base").cloned(), bits(f.gs, 64), &mut diffs);
    // Only bytes the spec wrote or the CPU changed can differ: every other
    // byte is `before` on both sides (the spec reads it from the backing).
    let mem = out.field("vm").and_then(|v| v.field("bytes")).cloned().unwrap_or(V::Unknown);
    let mut addrs: BTreeSet<u64> = (0..after.len()).filter(|&i| after[i] != before[i]).map(|i| SCRATCH + i as u64).collect();
    match &mem {
        V::Map(m) => addrs.extend(m.m.keys().filter_map(|k| k.parse::<u64>().ok()).filter(|a| a.wrapping_sub(SCRATCH) < SCRATCH_LEN)),
        _ => addrs.extend((0..SCRATCH_LEN).map(|i| SCRATCH + i)), // not a map: check everything
    }
    for a in addrs {
        let b = after[(a - SCRATCH) as usize];
        chk(format!("mem[{:#x}]", a), mem.map_get(&V::n(a as i128)), bits(b as u64, 8), &mut diffs);
    }
    diffs
}

/// Differences in what only system calls change: I/O, the memory map, brk.
fn compare_sys(out: &V, r: &sys::SysResult, env: &sys::SysEnv) -> Vec<String> {
    let mut diffs = Vec::new();
    let os = out.field("os");
    // I/O: the bytes written to fd 1 and 2, and how much stdin was consumed
    if let Some(V::Tuple(evs)) = os.and_then(|o| o.field("events")) {
        let mut written: [Option<Vec<u8>>; 2] = [Some(vec![]), Some(vec![])];
        let mut consumed = Some(0usize);
        let bytes = |d: &V| -> Option<Vec<u8>> {
            match d {
                V::Tuple(bs) => bs.iter().map(|b| b.int().ok().and_then(|x| x.to_u64()).map(|x| x as u8)).collect(),
                _ => None,
            }
        };
        for e in evs.iter() {
            match e {
                V::Tag(n, _, a) if n == "read" => consumed = consumed.zip(bytes(&a[0])).map(|(c, d)| c + d.len()),
                V::Tag(n, _, a) if n == "write" => {
                    let fd = a[0].int().ok().and_then(|x| x.to_u64()).unwrap_or(0);
                    if (1..=2).contains(&fd) {
                        let w = &mut written[fd as usize - 1];
                        *w = w.take().zip(bytes(&a[1])).map(|(mut x, d)| {
                            x.extend(d);
                            x
                        });
                    }
                }
                _ => consumed = None,
            }
        }
        for fd in 0..2 {
            if let Some(w) = &written[fd] {
                if *w != r.out[fd] {
                    diffs.push(format!("fd {} output: spec {:02x?} cpu {:02x?}", fd + 1, w, r.out[fd]));
                }
            }
        }
        if let Some(c) = consumed {
            if c != r.consumed {
                diffs.push(format!("stdin consumed: spec {} of {} bytes, cpu {}", c, env.input.len(), r.consumed));
            }
        }
    }
    // the memory map: every page the spec knows about
    let maps = cpu::parse_maps(&r.maps);
    let real = |p: u64| maps.iter().find(|m| m.0 <= p * 0x1000 && p * 0x1000 < m.1).map(|m| m.2);
    if let Some(V::Map(pages)) = out.field("vm").and_then(|v| v.field("pages")) {
        for (k, v) in &pages.m {
            let Ok(p) = k.parse::<u64>() else { continue };
            let spec = match v {
                V::Tag(n, _, a) if n == "some" => {
                    let pr = a[0].field("prot");
                    let b = |f: &str| pr.and_then(|x| x.field(f)).map(|x| matches!(x, V::Bool(true)));
                    match (b("r"), b("w"), b("x")) {
                        (Some(r), Some(w), Some(x)) => Some(Some(cpu::Perm { r, w, x })),
                        _ => None,
                    }
                }
                V::Tag(n, _, _) if n == "none" => Some(None),
                _ => None,
            };
            if let Some(spec) = spec {
                let cpu = real(p);
                if spec != cpu {
                    diffs.push(format!("page {:#x}: spec {:?} cpu {:?}", p * 0x1000, spec, cpu));
                }
            }
        }
    }
    chk("brk".into(), out.field("vm").and_then(|v| v.field("brk")).cloned(), bits(r.brk, 64), &mut diffs);
    diffs
}

// ----------------------------------------------------------------------
//  Generating cases

/// Harness hints (the manual part): procedures whose rows need registers
/// pointing into the scratch area.
fn setup_hints(body_calls: &[String], st: &mut CpuState, rng: &mut Rng) {
    if body_calls.iter().any(|c| matches!(c.as_str(), "movs" | "stos" | "rep_movs" | "rep_stos")) {
        st.gpr[6] = DATA + 0x400 + rng.below(64); // rsi
        st.gpr[7] = DATA + 0xa00 + rng.below(64); // rdi
        st.gpr[1] = rng.below(20); // rcx
    }
}

fn calls_in(b: &sl_syntax::ast::Block, out: &mut Vec<String>) {
    use sl_syntax::ast::*;
    fn expr(e: &Expr, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Call(f, args) => {
                if let ExprKind::Name(n) = &f.kind {
                    out.push(n.name.clone());
                }
                args.iter().for_each(|a| expr(a, out));
            }
            ExprKind::If(c, a, b) => {
                expr(c, out);
                calls_in(a, out);
                calls_in(b, out);
            }
            _ => {}
        }
    }
    for s in &b.stmts {
        match &s.kind {
            StmtKind::Expr(e) | StmtKind::Let { value: e, .. } => expr(e, out),
            StmtKind::Assign { target, value, .. } => {
                expr(target, out);
                expr(value, out)
            }
            StmtKind::If { cond, then, els } => {
                expr(cond, out);
                calls_in(then, out);
                if let Some(e) = els {
                    calls_in(e, out)
                }
            }
            StmtKind::Block(b) => calls_in(b, out),
            _ => {}
        }
    }
}

/// How a row's encodings look, read off its items (the manual part: the
/// meaning of the `intel` notations' decoders).
#[derive(Default, Debug)]
struct Template {
    /// legacy prefixes the row requires (66, F3, F0)
    prefixes: Vec<u8>,
    rex_w: bool,
    /// opcode bytes: (first value, number of values) for `b`, `b+r`, `b+cc`
    opcode: Vec<(u8, u8)>,
    /// a ModRM byte follows the opcode
    modrm: bool,
    /// `/digit`: the ModRM reg field
    reg: Option<u8>,
    /// a guard asks for a register (`rm is gp(_)`) or memory operand
    register_form: Option<bool>,
}

fn template(it: &Interp, k: usize) -> Template {
    use sl_syntax::ast::{ExprKind, Item, Pattern};
    let fr = &it.rows[k];
    let mut t = Template::default();
    let num = |e: &sl_syntax::ast::Expr| it.eval_with(e, &fr.consts).ok().and_then(|v| v.int().ok()).and_then(|v| v.to_u64());
    let call = |e: &sl_syntax::ast::Expr| match &e.kind {
        ExprKind::Call(f, args) => match &f.kind {
            ExprKind::Name(n) => Some((n.name.clone(), args.clone())),
            ExprKind::Index(g, _) => match &g.kind {
                ExprKind::Name(n) => Some((n.name.clone(), args.clone())),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    };
    fn guard_form(e: &sl_syntax::ast::Expr) -> Option<bool> {
        match &e.kind {
            ExprKind::Binary(sl_syntax::ast::BinOp::And, a, b) => guard_form(a).or_else(|| guard_form(b)),
            ExprKind::Is(x, Pattern::Ctor(c, _)) if matches!(&x.kind, ExprKind::Name(n) if n.name == "rm") => {
                Some(c.name == "gp")
            }
            _ => None,
        }
    }
    for item in fr.prefix.iter().chain(fr.row.items.iter()) {
        match item {
            Item::Byte(e) => t.opcode.push((num(e).unwrap_or(0) as u8, 1)),
            Item::Run(e) | Item::Bind(_, e) => match call(e) {
                Some((f, _)) if f == "rex_w" => t.rex_w = true,
                Some((f, _)) if f == "pfx66" => t.prefixes.push(0x66),
                Some((f, _)) if f == "rep" => t.prefixes.push(0xf3),
                Some((f, _)) if f == "lock" => t.prefixes.push(0xf0),
                Some((f, a)) if f == "plus_reg" => t.opcode.push((num(&a[0]).unwrap_or(0) as u8, 8)),
                Some((f, a)) if f == "plus_cc" => t.opcode.push((num(&a[0]).unwrap_or(0) as u8, 16)),
                Some((f, a)) if f == "modrm_ext" => {
                    t.modrm = true;
                    t.reg = num(&a[0]).map(|d| d as u8);
                }
                Some((f, _)) if f.starts_with("modrm") => t.modrm = true,
                _ => {}
            },
            Item::Guard(e) => t.register_form = t.register_form.or(guard_form(e)),
        }
    }
    t
}

/// A random encoding of row `k`, built from its template; the spec's
/// decoder decides whether it belongs to the row (and to no other).
fn encoding(it: &Interp, k: usize, t: &Template, rng: &mut Rng) -> Option<(Vec<u8>, Vec<(String, V)>)> {
    for _ in 0..400 {
        let mut pre: Vec<u8> = t.prefixes.clone();
        for (p, pct) in [(0x66, 30), (0xf3, 15), (0xf0, 10)] {
            if !pre.contains(&p) && rng.chance(pct) {
                pre.push(p);
            }
        }
        // legacy prefixes in random order, then REX
        for i in (1..pre.len()).rev() {
            pre.swap(i, rng.below(i as u64 + 1) as usize);
        }
        let mut b = pre;
        if t.rex_w {
            b.push(0x48 | rng.below(8) as u8);
        } else if rng.chance(50) {
            b.push(0x40 | rng.below(16) as u8);
        }
        for &(v, n) in &t.opcode {
            b.push(v + rng.below(n as u64) as u8);
        }
        if t.modrm {
            let md = match t.register_form {
                Some(true) => 3,
                Some(false) => rng.below(3) as u8,
                None => rng.below(4) as u8,
            };
            let reg = t.reg.unwrap_or(rng.below(8) as u8);
            b.push(md << 6 | reg << 3 | rng.below(8) as u8);
        }
        while b.len() < 15 {
            b.push(rng.next() as u8);
        }
        // cheap check against row k first, then ambiguity against all rows
        if it.decode_row(&b, k).is_none() {
            continue;
        }
        let ms = it.decode(&b);
        if ms.len() == 1 && ms[0].row == k {
            b.truncate(ms[0].len);
            return Some((b, ms[0].binds.clone()));
        }
    }
    None
}

/// The memory operand of a decoded instruction, if any.
fn mem_operand(binds: &[(String, V)]) -> Option<V> {
    binds.iter().find_map(|(_, v)| match v {
        V::Tag(n, _, a) if n == "ref" => a.first().cloned(),
        _ => None,
    })
}

fn fits_i32(x: u64) -> bool {
    (x as i64) >= i32::MIN as i64 && (x as i64) <= i32::MAX as i64
}

/// Replaces the 32-bit displacement `old` in the instruction by `new`; the
/// spec's decoder must agree that the operand's displacement changed (and
/// nothing else). Returns the new bindings.
fn patch_disp(it: &Interp, k: usize, insn: &mut Vec<u8>, old: u64, new: u64) -> Option<Vec<(String, V)>> {
    let o = (old as u32).to_le_bytes();
    for p in 0..insn.len().saturating_sub(3) {
        if insn[p..p + 4] != o {
            continue;
        }
        let mut b = insn.clone();
        b[p..p + 4].copy_from_slice(&(new as u32).to_le_bytes());
        let ms = it.decode(&b);
        if ms.len() == 1 && ms[0].row == k && ms[0].len == insn.len() {
            let d = mem_operand(&ms[0].binds).and_then(|m| m.field("disp").and_then(|d| d.int().ok()).and_then(|d| d.to_u64()));
            if d == Some(new as i32 as i64 as u64) {
                *insn = b;
                return Some(ms[0].binds.clone());
            }
        }
    }
    None
}

/// Makes the memory operand (if any) point into the data area, or (15%)
/// somewhere that faults: the read-only / write-only / exec-only / guard
/// page, a non-canonical or a kernel address. It sets the base or index
/// register, the fs/gs base, or (rip-relative and absolute operands) the
/// displacement in the instruction. Returns the address (`None`: no memory
/// operand).
fn aim_memory(it: &Interp, k: usize, insn: &mut Vec<u8>, binds: &mut Vec<(String, V)>, st: &mut CpuState, rng: &mut Rng) -> Option<u64> {
    let m = mem_operand(binds)?;
    let num = |v: Option<&V>| v.and_then(|x| x.int().ok()).and_then(|x| x.to_u64());
    let seg = num(m.field("seg")).unwrap_or(0);
    let disp = num(m.field("disp")).unwrap_or(0);
    let scale = num(m.field("scale")).unwrap_or(1);
    let index = match m.field("index") {
        Some(V::Tag(n, _, a)) if n == "some" => a.first().and_then(|x| x.int().ok()).and_then(|x| x.to_u64()).map(|x| x as usize),
        _ => None,
    };
    let base = match m.field("base") {
        Some(V::Tag(n, _, a)) if n == "base" => a[0].int().ok().and_then(|x| x.to_u64()).map(|x| x as usize),
        _ => None,
    };
    let rip_rel = matches!(m.field("base"), Some(V::Tag(n, _, _)) if n == "rip_rel");
    let mut target = if rng.chance(85) {
        DATA + 16 * rng.below(64)
    } else {
        match rng.below(8) {
            7 => 0x3000_0000 + 16 * rng.below(1 << 16), // unmapped
            0 => RO_PAGE + 16 * rng.below(64),
            1 => WO_PAGE + 16 * rng.below(64),
            2 => XO_PAGE + 16 * rng.below(64),
            3 => CODE_END + 16 * rng.below(64),
            4 => 0x8000_0000_0000_0000 | 16 * rng.below(1 << 20),
            5 => 0xffff_ffff_8000_0000 + 16 * rng.below(1 << 20), // kernel, reachable by a 32-bit displacement
            _ => 0xffff_8000_0000_0000 + 16 * rng.below(1 << 20),
        }
    };
    // an fs/gs operand: a segment base of the case's choosing
    let sb = match seg {
        2 | 3 => {
            let b = 0x2000_0000 + 0x1000 * rng.below(256);
            if seg == 2 { st.fs = b } else { st.gs = b }
            b
        }
        _ => 0,
    };
    // what base + index*scale + disp must add up to
    let mut want = target.wrapping_sub(sb);
    let fixed = if rip_rel { CODE_END } else { 0 }; // rip after the instruction
    if base.is_none() && index.is_none() || rip_rel {
        // only the displacement can move the address
        if !fits_i32(want.wrapping_sub(fixed)) {
            target = DATA + 16 * rng.below(64);
            want = target.wrapping_sub(sb);
        }
        let iv = index.map(|i| st.gpr[i].wrapping_mul(scale)).unwrap_or(0);
        let new = want.wrapping_sub(fixed).wrapping_sub(iv);
        if !fits_i32(new) {
            // rip-relative with an index cannot happen; keep the index small
            return None;
        }
        *binds = patch_disp(it, k, insn, disp, new)?;
        return Some(target);
    }
    let want = want.wrapping_sub(disp);
    match (base, index) {
        (Some(b), Some(i)) if b == i => {
            // the same register twice: v * (1 + scale) = want
            let d = 1 + scale;
            let w = want - want % d;
            st.gpr[b] = w / d;
            Some(target.wrapping_sub(want % d))
        }
        (Some(b), i) => {
            let iv = i.map(|i| st.gpr[i].wrapping_mul(scale)).unwrap_or(0);
            st.gpr[b] = want.wrapping_sub(iv);
            Some(target)
        }
        (None, Some(i)) => {
            // make want a multiple of the scale
            let w = want - want % scale;
            st.gpr[i] = w / scale;
            Some(target.wrapping_sub(want % scale))
        }
        (None, None) => unreachable!(),
    }
}

/// A branch target worth trying: before the instruction (int3 bytes), the
/// guard page, unmapped, data (not executable), non-canonical, kernel.
fn interesting_target(rng: &mut Rng) -> u64 {
    match rng.below(8) {
        0 => CODE + rng.below(0xf00),
        1 => CODE_END + rng.below(0x1000),
        2 => 0x2000_0000 + rng.below(1 << 20),
        3 => DATA + rng.below(0x800),
        4 => 0x8000_0000_0000_0000 | rng.below(1 << 20),
        5 => 0xffff_8000_0000_0000 + rng.below(1 << 20),
        _ => rng.value(),
    }
}

/// Harness hints for indirect branches: the return address (`ret`) or the
/// branch operand (`jmp`/`call` through a register or memory) is set to an
/// interesting target.
fn aim_target(kind: &str, binds: &[(String, V)], mem: Option<u64>, st: &mut CpuState, scratch: &mut [u8], rng: &mut Rng) {
    let t = interesting_target(rng);
    let store = |a: u64, scratch: &mut [u8]| {
        if a >= SCRATCH && a + 8 <= RO_PAGE {
            scratch[(a - SCRATCH) as usize..][..8].copy_from_slice(&t.to_le_bytes());
        }
    };
    match kind {
        "ret" => store(st.gpr[4], scratch),
        "indcall" | "indjump" => match binds.iter().find(|(n, _)| n == "rm").map(|x| &x.1) {
            Some(V::Tag(n, _, a)) if n == "gp" => {
                if let Some(r) = a[0].int().ok().and_then(|x| x.to_u64()) {
                    st.gpr[r as usize] = t;
                }
            }
            _ => {
                if let Some(a) = mem {
                    store(a, scratch)
                }
            }
        },
        _ => {}
    }
}

// ----------------------------------------------------------------------
//  What the CPU did

enum Obs {
    /// the instruction completed; the next instruction is at `rip`
    Done(u64),
    /// the instruction raised this exception (a spec exception value)
    Raised(V),
    Unexpected(String),
}

fn exc(name: &str, args: Vec<V>) -> V {
    V::Tag(name.into(), 0, args)
}

fn observe(f: &Fault, start: u64) -> Obs {
    if f.signo == SIGTRAP {
        return Obs::Done(f.rip - 1); // an int3 at the branch target
    }
    if f.signo == SIGSEGV && f.addr == f.rip && f.rip != start {
        return Obs::Done(f.rip); // fetching the next instruction faulted
    }
    if f.rip != start {
        return Obs::Unexpected(format!("signal {} code {:#x} addr {:#x} at rip {:#x}", f.signo, f.code, f.addr, f.rip));
    }
    match (f.signo, f.code) {
        (SIGSEGV, 1) => Obs::Raised(exc("segv", vec![bits(f.addr, 64), V::n(0)])), // SEGV_MAPERR
        (SIGSEGV, 2) => Obs::Raised(exc("segv", vec![bits(f.addr, 64), V::n(1)])), // SEGV_ACCERR
        (SIGSEGV, 0x80) => Obs::Raised(exc("segv", vec![bits(0, 64), V::n(2)])),   // SI_KERNEL
        (SIGSEGV, 4) => Obs::Raised(exc("segv", vec![bits(f.addr, 64), V::n(3)])), // SEGV_PKUERR
        (SIGFPE, _) => Obs::Raised(exc("div_error", vec![])),
        (SIGILL, _) => Obs::Raised(exc("ud", vec![])),
        (SIGBUS, 0x80) => Obs::Raised(exc("stack_fault", vec![])),                // #SS
        (SIGBUS, c) => Obs::Unexpected(format!("SIGBUS code {:#x} addr {:#x}", c, f.addr)),
        (s, c) => Obs::Unexpected(format!("signal {} code {:#x} addr {:#x}", s, c, f.addr)),
    }
}

fn noncanonical(a: u64) -> bool {
    a >= 1 << 47 && a < 0xffff_8000_0000_0000
}

fn render_outcome(o: &Outcome) -> String {
    match o {
        Outcome::Ok(v) => format!("ok, rip {}", v.field("rip").map(|r| r.render()).unwrap_or_default()),
        Outcome::Exc(_, e) => format!("raise {}", e.render()),
        Outcome::Undefined => "undefined".into(),
        Outcome::Unsupported(s) => format!("unsupported: {}", s),
    }
}

// ----------------------------------------------------------------------
//  The worker: all cases of one row

struct RowResult {
    tested: usize,
    skipped: BTreeMap<String, usize>,
    mismatches: Vec<String>,
}

/// The row as written in the spec (whitespace collapsed), with the constants
/// of an expanded `for` row; it identifies the row in reports and the limits
/// file.
fn row_label(it: &Interp, sm: &sl_syntax::SourceMap, k: usize) -> String {
    let text = sm.snippet(it.rows[k].row.span).lines().next().unwrap_or("").split_whitespace().collect::<Vec<_>>().join(" ");
    let consts: Vec<String> = it.rows[k].consts.iter().map(|(n, v)| format!("{}={}", n, v.render())).collect();
    if consts.is_empty() { text } else { format!("{}  [{}]", text, consts.join(",")) }
}

/// FNV-1a; seeds the samples of a row by its text, so adding rows to the
/// table does not change the samples of the others.
fn hash(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ b as u64).wrapping_mul(0x100_0000_01b3))
}

fn run_row(it: &Interp, setup: &cpu::Setup, k: usize, label: &str, n: usize, seed: u64) -> RowResult {
    let mut res = RowResult { tested: 0, skipped: BTreeMap::new(), mismatches: Vec::new() };
    let mut rng = Rng((hash(&seed.to_string()) ^ hash(label)) | 1);
    let body = &it.rows[k].row.body;
    let kind = crate::commands::flow_kind(body);
    let mut calls = Vec::new();
    calls_in(body, &mut calls);
    let feat = features();
    let (fs0, gs0) = cpu::saved_segs();
    let skip = |r: &mut RowResult, why: &str| *r.skipped.entry(why.to_string()).or_default() += 1;
    let tmpl = template(it, k);
    // the system call row covers many calls: more samples
    let n = if kind == "syscall" { 10 * n } else { n };
    // samples still to draw; a branch that must not run is redrawn
    let (mut remaining, mut redraws) = (n, 0usize);
    while remaining > 0 {
        remaining -= 1;
        let Some((mut insn, mut binds)) = encoding(it, k, &tmpl, &mut rng) else {
            skip(&mut res, "no encoding found");
            continue;
        };
        let mut st = CpuState { fs: fs0, gs: gs0, ..CpuState::default() };
        for r in st.gpr.iter_mut() {
            *r = rng.value();
        }
        st.gpr[4] = SCRATCH + 0x2800 - 8 * rng.below(32); // rsp
        st.gpr[5] = SCRATCH + 0x2000 + 8 * rng.below(32); // rbp
        for x in st.xmm.iter_mut() {
            *x = [rng.value(), rng.value()];
        }
        // arithmetic flags random, DF set only for string instructions
        let mut fl = 0x202u64;
        for (_, b) in FLAG_BITS {
            if b != 10 && rng.chance(50) {
                fl |= 1 << b;
            }
        }
        setup_hints(&calls, &mut st, &mut rng);
        if calls.iter().any(|c| c.contains("movs") || c.contains("stos")) && rng.chance(50) {
            fl |= 1 << 10;
        }
        st.flags = fl;
        // stack instructions: sometimes a stack pointer that faults
        let uses_stack = matches!(kind, "call" | "indcall" | "ret") || calls.iter().any(|c| c == "push" || c == "pop");
        if uses_stack && rng.chance(15) {
            st.gpr[4] = match rng.below(5) {
                0 => 0x3000_0000 + 8 * rng.below(1 << 16),
                1 => RO_PAGE + 8 * rng.below(64),
                2 => CODE_END + 8 * rng.below(64),
                3 => SCRATCH + 8 * rng.below(2), // just above unmapped memory
                _ => 0x8000_0000_0000_0000 | 8 * rng.below(1 << 16),
            };
        }
        let has_mem = mem_operand(&binds).is_some();
        let mem = aim_memory(it, k, &mut insn, &mut binds, &mut st, &mut rng);
        if has_mem && mem.is_none() {
            skip(&mut res, "memory operand could not be aimed");
            continue;
        }
        let mut scratch: Vec<u8> = (0..SCRATCH_LEN).map(|_| rng.next() as u8).collect();
        aim_target(kind, &binds, mem, &mut st, &mut scratch, &mut rng);
        let env = if kind == "syscall" { Some(sys::generate(&mut rng, &mut st, &mut scratch)) } else { None };
        let start = CODE_END - insn.len() as u64;
        let m = machine(&st, &scratch, start, &insn, feat, env.as_ref());

        // the CPU (system calls first, their results guide the spec's choices)
        let (outs, f, after, sysres) = if let Some(env) = &env {
            let r = match sys::run(&st, &insn, &scratch, env) {
                Ok(r) => r,
                Err(e) => {
                    res.mismatches.push(format!("bytes {:02x?}: {}", insn, e));
                    continue;
                }
            };
            let rax = r.fault.map(|f| f.st.gpr[0]).unwrap_or(0);
            let hints = [bits(rax, 64), V::n((rax >> 12) as i128), V::n(rax as i128)];
            let outs = it.step_with_hints(&m, 64, &hints);
            let f = r.fault.unwrap_or_default();
            let after = r.after.clone();
            (outs, f, after, Some(r))
        } else {
            let outs = it.step(&m, 64);
            // never run a branch into the instruction itself (it could loop)
            // or into code of this process
            let targets: Vec<u64> = outs
                .iter()
                .filter_map(|o| if let Outcome::Ok(v) = o { v.field("rip").and_then(|r| r.int().ok()).and_then(|r| r.to_u64()) } else { None })
                .collect();
            let into_itself = targets.iter().any(|&t| t >= start && t < CODE_END);
            let into_harness = targets.iter().any(|&t| setup.exec.iter().any(|&(a, b)| a <= t && t < b));
            if into_itself || into_harness {
                if redraws < 10 * n {
                    redraws += 1;
                    remaining += 1;
                } else {
                    skip(&mut res, if into_itself { "branch into the instruction itself" } else { "branch into the harness's code" });
                }
                continue;
            }
            if outs.iter().any(|o| matches!(o, Outcome::Undefined | Outcome::Unsupported(_))) {
                (outs, Fault::default(), Vec::new(), None)
            } else {
                let (f, after) = cpu::run(&st, &insn, &scratch);
                (outs, f, after, None)
            }
        };
        if outs.iter().any(|o| matches!(o, Outcome::Undefined)) {
            skip(&mut res, "spec: undefined (a deliberate gap in the spec, not in the test)");
            continue;
        }
        if let Some(Outcome::Unsupported(why)) = outs.iter().find(|o| matches!(o, Outcome::Unsupported(_))) {
            let call = if env.is_some() { format!(" (syscall {})", st.gpr[0]) } else { String::new() };
            skip(&mut res, &format!("interpreter: {}{}", why, call));
            continue;
        }
        res.tested += 1;

        // compare
        let oks: Vec<&V> = outs.iter().filter_map(|o| if let Outcome::Ok(v) = o { Some(v) } else { None }).collect();
        let excs: Vec<&V> = outs.iter().filter_map(|o| if let Outcome::Exc(_, e) = o { Some(e) } else { None }).collect();
        let spec_says = || outs.iter().map(render_outcome).collect::<Vec<_>>().join("; ");
        let problem: Option<String> = match (&sysres, sysres.as_ref().and_then(|r| r.exit)) {
            (Some(_), Some(code)) => {
                let e = exc("exit", vec![bits(code as u64, 8)]);
                if excs.iter().any(|x| same(x, &e) != Some(false)) {
                    None
                } else {
                    Some(format!("cpu: exit({}); spec: {}", code, spec_says()))
                }
            }
            _ => match observe(&f, start) {
                Obs::Done(rip) => {
                    let all: Vec<Vec<String>> = oks
                        .iter()
                        .map(|o| {
                            let mut d = compare(o, &f, rip, &scratch, &after);
                            if let (Some(r), Some(env)) = (&sysres, &env) {
                                d.extend(compare_sys(o, r, env));
                            }
                            d
                        })
                        .collect();
                    if all.iter().any(|d| d.is_empty()) {
                        None
                    } else if all.is_empty() {
                        Some(format!("cpu: completed, next rip {:#x}; spec: {}", rip, spec_says()))
                    } else {
                        // the differences to each normal outcome the spec allows
                        let per: Vec<String> = all
                            .iter()
                            .take(4)
                            .enumerate()
                            .map(|(i, d)| format!("outcome {}: {}", i + 1, d.join("\n        ")))
                            .collect();
                        Some(per.join("\n      "))
                    }
                }
                Obs::Raised(e) => {
                    // a branch to a non-canonical address: the spec faults
                    // when fetching there (segv(0, kernel)), the CPU already
                    // at the branch; the same crash
                    let gp = exc("segv", vec![bits(0, 64), V::n(2)]);
                    let branch_gp = same(&e, &gp) == Some(true)
                        && oks.iter().any(|o| o.field("rip").and_then(|r| r.int().ok()).and_then(|r| r.to_u64()).map_or(false, noncanonical));
                    if branch_gp || excs.iter().any(|x| same(x, &e) != Some(false)) {
                        None
                    } else {
                        Some(format!("cpu: raise {}; spec: {}", e.render(), spec_says()))
                    }
                }
                Obs::Unexpected(s) => Some(format!("cpu: {}; spec: {}", s, spec_says())),
            },
        };
        if let Some(p) = problem {
            let hex: Vec<String> = insn.iter().map(|b| format!("{:02x}", b)).collect();
            let regs: Vec<String> = st.gpr.iter().map(|r| format!("{:#x}", r)).collect();
            res.mismatches.push(format!("bytes {} | flags {:#x} | regs [{}]\n      {}", hex.join(" "), st.flags, regs.join(", "), p));
        }
    }
    res
}

// ----------------------------------------------------------------------
//  Command

const LIMITS_HEADER: &str = "\
# Rows of the x86 table that `slc cputest` does not compare with the CPU.
# Checked by `cargo test` (slc/cli/tests/cputest.rs): a new instruction the
# harness cannot test, or a gap that disappears, fails the test until this
# file is regenerated with `slc cputest --limits tests/cputest-limits.txt
# --update-limits` (review the diff). 'partly skipped' rows had samples the
# interpreter could not evaluate. Samples the spec leaves undefined are not
# limits of the test; they, and branches into the harness's own code, are
# only counted in the run's summary.
#
# reason | row
";

pub fn cputest(args: &[String]) -> CResult {
    let mut n = 40usize;
    let mut seed = 1u64;
    let mut only: Option<Vec<usize>> = None;
    let mut worker = false;
    let mut verbose = false;
    let mut limits_file: Option<String> = None;
    let mut update_limits = false;
    let mut it_args = args.iter();
    while let Some(a) = it_args.next() {
        match a.as_str() {
            "--n" => n = it_args.next().and_then(|x| x.parse().ok()).ok_or("--n N")?,
            "--seed" => seed = it_args.next().and_then(|x| x.parse().ok()).ok_or("--seed S")?,
            "--rows" => only = Some(it_args.next().ok_or("--rows K,..")?.split(',').filter_map(|x| x.parse().ok()).collect()),
            "--worker" => worker = true,
            "--verbose" => verbose = true,
            "--limits" => limits_file = Some(it_args.next().ok_or("--limits FILE")?.clone()),
            "--update-limits" => update_limits = true,
            other => return Err(format!("unknown argument `{}`", other)),
        }
    }
    let root = repo_root();
    let mut sm = sl_syntax::SourceMap::default();
    let files = crate::commands::parse_all(&[root.join("spec")], &mut sm)?;
    let g = sl_elab::globals::Globals::build(files)?;
    let it = Interp::new(&g, "x86")?;
    let testable: Vec<usize> = (0..it.rows.len()).collect();
    let explicit = only.is_some();
    let rows = only.unwrap_or_else(|| testable.clone());

    if worker {
        let setup = cpu::setup()?;
        cpu::sys(37, &[60 + n as u64 / 4]); // alarm: a hang fails the row
        for k in rows {
            let r = run_row(&it, &setup, k, &row_label(&it, &sm, k), n, seed);
            println!("ROW {} tested {} mismatches {}", k, r.tested, r.mismatches.len());
            for (why, c) in &r.skipped {
                println!("SKIP {} {}", c, why);
            }
            for m in r.mismatches.iter().take(3) {
                println!("MISMATCH {}", m);
            }
        }
        return Ok(());
    }

    // parent: one subprocess per row
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let (mut total, mut bad_rows, mut crashed) = (0usize, 0usize, 0usize);
    let mut skipped: BTreeMap<String, usize> = BTreeMap::new();
    let label_of = |k: usize| row_label(&it, &sm, k);
    if explicit && (limits_file.is_some() || update_limits) {
        return Err("--limits needs a run over all rows (no --rows)".into());
    }
    // rows (or samples of rows) the CPU is not compared on, with the reason
    let mut limits: Vec<(String, String)> = Vec::new();
    let mut never = 0usize;
    for k in &rows {
        let label = label_of(*k);
        let o = std::process::Command::new(&exe)
            .args(["cputest", "--worker", "--n", &n.to_string(), "--seed", &seed.to_string(), "--rows", &k.to_string()])
            .current_dir(&root)
            .output()
            .map_err(|e| e.to_string())?;
        let out = String::from_utf8_lossy(&o.stdout).to_string();
        if !o.status.success() {
            crashed += 1;
            let err = String::from_utf8_lossy(&o.stderr);
            println!("CRASH  row {:3} {}  ({}) {}", k, label, o.status, err.lines().last().unwrap_or(""));
            continue;
        }
        let mut tested = 0;
        let mut mism = Vec::new();
        let mut row_skips = Vec::new();
        for line in out.lines() {
            if let Some(r) = line.strip_prefix("ROW ") {
                let parts: Vec<&str> = r.split_whitespace().collect();
                tested = parts[2].parse().unwrap_or(0);
            } else if let Some(s) = line.strip_prefix("SKIP ") {
                let (c, why) = s.split_once(' ').unwrap_or(("0", s));
                *skipped.entry(why.to_string()).or_default() += c.parse::<usize>().unwrap_or(0);
                row_skips.push(format!("{} x {}", c, why));
            } else if line.starts_with("MISMATCH") || line.starts_with("      ") {
                mism.push(line.to_string());
            }
        }
        total += tested;
        // samples of a tested row the spec could not be compared on: a spec
        // bug (e.g. a wrong address) can hide here, so they are limits too
        if tested > 0 {
            for sk in &row_skips {
                let why = sk.split_once(" x ").map(|x| x.1).unwrap_or("");
                if why.starts_with("interpreter:") {
                    limits.push((format!("partly skipped: {}", why), label.clone()));
                }
            }
        }
        if tested == 0 {
            never += 1;
            // the most frequent skip reason
            let why = row_skips
                .iter()
                .filter_map(|s| s.split_once(" x ").map(|(c, w)| (c.parse::<usize>().unwrap_or(0), w.to_string())))
                .max()
                .map(|x| x.1)
                .unwrap_or_else(|| "no samples".into());
            limits.push((format!("never compared: {}", why), label.clone()));
        }
        if mism.is_empty() {
            let tag = if tested == 0 { "NONE " } else { "ok   " };
            println!("{}  row {:3} {:4} cases  {}", tag, k, tested, label);
            if tested == 0 || verbose {
                for s in &row_skips {
                    println!("         skipped {}", s);
                }
            }
        } else {
            bad_rows += 1;
            println!("FAIL   row {:3} {:4} cases  {}", k, tested, label);
            for m in mism.iter().take(12) {
                println!("       {}", m);
            }
        }
    }
    println!("\n{} rows, {} cases compared with the CPU; {} rows with mismatches, {} crashed, {} never compared",
        rows.len(), total, bad_rows, crashed, never);
    for (why, c) in &skipped {
        println!("  skipped {:5}: {}", c, why);
    }
    // a crashed worker (e.g. the spec on disk changed mid-run) is not a
    // disagreement; it is reported apart so the two are not confused
    let mut problems = Vec::new();
    if bad_rows > 0 {
        problems.push(format!("the spec disagrees with the CPU in {} rows", bad_rows));
    }
    if crashed > 0 {
        problems.push(format!("{} rows crashed (see CRASH lines)", crashed));
    }
    if explicit {
        return if problems.is_empty() { Ok(()) } else { Err(problems.join("; ")) };
    }
    limits.sort();
    println!("\nLimits: {} of {} rows are not compared with the CPU", limits.len(), it.rows.len());
    for (why, row) in &limits {
        println!("  {:40} {}", why, row);
    }
    if let Some(f) = &limits_file {
        let path = root.join(f);
        let text: String = limits.iter().map(|(w, r)| format!("{} | {}\n", w, r)).collect();
        if update_limits {
            std::fs::write(&path, format!("{}{}", LIMITS_HEADER, text)).map_err(|e| format!("{}: {}", f, e))?;
            println!("\nwrote {}", f);
        } else {
            let old = std::fs::read_to_string(&path).unwrap_or_default();
            let expected: BTreeSet<&str> =
                old.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')).collect();
            let actual: BTreeSet<&str> = text.lines().collect();
            let new_gaps: Vec<&&str> = actual.difference(&expected).collect();
            let covered: Vec<&&str> = expected.difference(&actual).collect();
            if !new_gaps.is_empty() || !covered.is_empty() {
                println!("\nThe limits differ from {}:", f);
                for l in &new_gaps {
                    println!("  new gap:          {}", l);
                }
                for l in &covered {
                    println!("  no longer a gap:  {}", l);
                }
                println!("Review, then accept with `slc cputest --limits {} --update-limits`.", f);
                problems.push(format!("the test limits differ from {}", f));
            }
        }
    }
    if problems.is_empty() { Ok(()) } else { Err(problems.join("; ")) }
}
