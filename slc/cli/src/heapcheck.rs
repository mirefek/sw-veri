//! `slc heapcheck ELF [ARGS...]`: evaluate the mallocng invariant
//! (layers/mallocng.sl) on the heaps of a real run.
//!
//! Runs the program under ptrace with breakpoints on `main`, `malloc`,
//! `calloc` and `free`, tracks the live blocks, and after each top-level
//! call snapshots the process (memory from /proc/PID/mem, mappings from
//! /proc/PID/maps). The abstraction function below reads mallocng's
//! structures into an `Abs`; the interpreter then evaluates each conjunct of
//! `rep(c, A, s)`. Evidence for the invariant's design, not a proof.

use crate::commands::{parse_all, repo_root, CResult};
use sl_interp::elf::Elf;
use sl_interp::{map, map_backed_regions, Interp, V};
use std::collections::{BTreeMap, BTreeSet};
use std::os::unix::fs::FileExt;
use std::os::unix::process::CommandExt;

// ----------------------------------------------------------------------
//  ptrace

const PTRACE_TRACEME: u64 = 0;
const PTRACE_POKEDATA: u64 = 5;
const PTRACE_CONT: u64 = 7;
const PTRACE_KILL: u64 = 8;
const PTRACE_SINGLESTEP: u64 = 9;
const PTRACE_GETREGS: u64 = 12;
const PTRACE_SETREGS: u64 = 13;
const PTRACE_SETOPTIONS: u64 = 0x4200;
const PTRACE_O_EXITKILL: u64 = 0x100000;

unsafe fn syscall4(nr: u64, a: u64, b: u64, c: u64, d: u64) -> i64 {
    let r: i64;
    std::arch::asm!("syscall", inlateout("rax") nr as i64 => r, in("rdi") a, in("rsi") b, in("rdx") c,
        in("r10") d, lateout("rcx") _, lateout("r11") _);
    r
}

fn ptrace(req: u64, pid: u64, addr: u64, data: u64) -> i64 {
    unsafe { syscall4(101, req, pid, addr, data) }
}

/// user_regs_struct
#[repr(C)]
#[derive(Default, Clone, Copy)]
struct Regs {
    r15: u64, r14: u64, r13: u64, r12: u64, rbp: u64, rbx: u64, r11: u64, r10: u64, r9: u64, r8: u64,
    rax: u64, rcx: u64, rdx: u64, rsi: u64, rdi: u64, orig_rax: u64, rip: u64, cs: u64, eflags: u64,
    rsp: u64, ss: u64, fs_base: u64, gs_base: u64, ds: u64, es: u64, fs: u64, gs: u64,
}

struct Tracee {
    pid: u64,
    mem: std::fs::File,
}

enum Stop {
    Trap,
    Exited(i32),
    Other(i32),
}

impl Tracee {
    fn wait(&self) -> Stop {
        let mut status: i32 = 0;
        unsafe { syscall4(61, self.pid, &mut status as *mut i32 as u64, 0, 0) };
        if status & 0x7f == 0 {
            return Stop::Exited((status >> 8) & 0xff);
        }
        if status & 0xff == 0x7f {
            let sig = (status >> 8) & 0xff;
            return if sig == 5 { Stop::Trap } else { Stop::Other(sig) };
        }
        Stop::Other(-1)
    }
    fn regs(&self) -> Regs {
        let mut r = Regs::default();
        ptrace(PTRACE_GETREGS, self.pid, 0, &mut r as *mut Regs as u64);
        r
    }
    fn set_regs(&self, r: &Regs) {
        ptrace(PTRACE_SETREGS, self.pid, 0, r as *const Regs as u64);
    }
    fn peek(&self, a: u64) -> u64 {
        let mut w = [0u8; 8];
        let _ = self.mem.read_at(&mut w, a);
        u64::from_le_bytes(w)
    }
    fn poke(&self, a: u64, w: u64) {
        ptrace(PTRACE_POKEDATA, self.pid, a, w);
    }
    fn cont(&self) {
        ptrace(PTRACE_CONT, self.pid, 0, 0);
    }
    fn step(&self) -> Stop {
        ptrace(PTRACE_SINGLESTEP, self.pid, 0, 0);
        self.wait()
    }
}

/// Breakpoints: address -> original word.
struct Bps(BTreeMap<u64, u64>);

impl Bps {
    fn set(&mut self, t: &Tracee, a: u64) {
        if self.0.contains_key(&a) {
            return;
        }
        let w = t.peek(a);
        self.0.insert(a, w);
        t.poke(a, (w & !0xff) | 0xcc);
    }
    fn clear(&mut self, t: &Tracee, a: u64) {
        if let Some(w) = self.0.remove(&a) {
            t.poke(a, w);
        }
    }
    /// Continue from the breakpoint at `a` (just hit): run its instruction
    /// with the original bytes, then re-arm it if `keep`.
    fn step_over(&mut self, t: &Tracee, a: u64, keep: bool) -> Result<(), String> {
        let mut r = t.regs();
        r.rip = a;
        t.set_regs(&r);
        self.clear(t, a);
        match t.step() {
            Stop::Trap => {}
            Stop::Exited(c) => return Err(format!("exited ({}) while stepping", c)),
            Stop::Other(s) => return Err(format!("signal {} while stepping", s)),
        }
        if keep {
            self.set(t, a);
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------
//  Snapshots

#[derive(Clone)]
struct Mapping {
    lo: u64,
    hi: u64,
    prot: (bool, bool, bool),
    name: String,
}

#[derive(Clone)]
struct Snapshot {
    maps: Vec<Mapping>,
    regions: Vec<(u64, Vec<u8>)>,
    brk: u64,
}

impl Snapshot {
    fn take(t: &Tracee) -> Result<Snapshot, String> {
        let text = std::fs::read_to_string(format!("/proc/{}/maps", t.pid)).map_err(|e| e.to_string())?;
        let mut maps = Vec::new();
        for l in text.lines() {
            let f: Vec<&str> = l.split_whitespace().collect();
            let (lo, hi) = f[0].split_once('-').ok_or("bad maps line")?;
            let (lo, hi) = (u64::from_str_radix(lo, 16).unwrap(), u64::from_str_radix(hi, 16).unwrap());
            let p = f[1].as_bytes();
            maps.push(Mapping { lo, hi, prot: (p[0] == b'r', p[1] == b'w', p[2] == b'x'), name: f.get(5).unwrap_or(&"").to_string() });
        }
        let mut regions = Vec::new();
        for m in &maps {
            if m.lo >= 0xffff_8000_0000_0000 {
                continue; // vsyscall
            }
            let mut buf = vec![0u8; (m.hi - m.lo) as usize];
            // unreadable pages (PROT_NONE, vvar) read as zero
            let _ = t.mem.read_at(&mut buf, m.lo);
            regions.push((m.lo, buf));
        }
        // the break: the end of [heap], else its start (/proc/PID/stat field 47)
        let brk = match maps.iter().filter(|m| m.name == "[heap]").map(|m| m.hi).max() {
            Some(h) => h,
            None => {
                let st = std::fs::read_to_string(format!("/proc/{}/stat", t.pid)).map_err(|e| e.to_string())?;
                let after = &st[st.rfind(')').unwrap() + 2..];
                after.split_whitespace().nth(44).and_then(|x| x.parse().ok()).unwrap_or(0)
            }
        };
        Ok(Snapshot { maps, regions, brk })
    }

    fn rd(&self, a: u64, n: u64) -> u64 {
        let mut v = 0u64;
        for i in 0..n {
            v |= (self.byte(a + i) as u64) << (8 * i);
        }
        v
    }

    fn set_byte(&mut self, a: u64, v: u8) {
        let k = self.regions.partition_point(|r| r.0 <= a);
        if let Some((base, b)) = k.checked_sub(1).map(|k| &mut self.regions[k]) {
            if a - *base < b.len() as u64 {
                b[(a - *base) as usize] = v;
            }
        }
    }

    fn byte(&self, a: u64) -> u8 {
        let k = self.regions.partition_point(|r| r.0 <= a);
        match k.checked_sub(1).map(|k| &self.regions[k]) {
            Some((base, b)) if a - base < b.len() as u64 => b[(a - base) as usize],
            _ => 0,
        }
    }
}

// ----------------------------------------------------------------------
//  The abstraction function: mallocng's state as an `Abs`

const NSLOTS: u64 = 101;
const SIZE_CLASSES: [u64; 48] = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 18, 20, 25, 31, 36, 42, 50, 63, 72, 84, 102, 127, 146, 170, 204, 255, 292,
    340, 409, 511, 584, 682, 818, 1023, 1169, 1364, 1637, 2047, 2340, 2730, 3276, 4095, 4680, 5460, 6552, 8191,
];

#[derive(Clone, Copy, Default, Debug)]
struct MetaV {
    prev: u64,
    next: u64,
    mem: u64,
    avail: u64,
    freed: u64,
    last_idx: u64,
    freeable: u64,
    sizeclass: u64,
    maplen: u64,
}

impl MetaV {
    fn stride(&self) -> u64 {
        if self.last_idx == 0 && self.maplen > 0 {
            self.maplen * 4096 - 16
        } else {
            16 * SIZE_CLASSES.get(self.sizeclass as usize).copied().unwrap_or(0)
        }
    }
    fn slot_start(&self, i: u64) -> u64 {
        self.mem + 16 + self.stride() * i
    }
}

#[derive(Clone, Debug)]
enum Use {
    Unused,
    Block(u64),
    Nested(u64),
}

#[derive(Clone)]
struct Abs {
    secret: u64,
    init_done: u64,
    auxv_at: u64,
    auxv: Vec<(u64, u64)>,
    areas: Vec<u64>,
    avail_cnt: u64,
    reserve: u64,
    reserve_cnt: u64,
    free_metas: Vec<u64>,
    used: Vec<u64>,
    metas: BTreeMap<u64, MetaV>,
    active: Vec<Vec<u64>>,
    slots: BTreeMap<u64, Vec<Use>>,
    brk: u64,
    /// what the function could not make sense of
    notes: Vec<String>,
}

/// Follows `next` (offset 8) from `head` until it comes back.
fn cyclic_list(s: &Snapshot, head: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut g = head;
    while g != 0 && out.len() < 100_000 {
        out.push(g);
        g = s.rd(g + 8, 8);
        if g == head {
            break;
        }
    }
    out
}

fn abstraction(s: &Snapshot, ctx: u64, libc: u64, blocks: &BTreeMap<u64, u64>) -> Abs {
    let mut notes = Vec::new();
    let secret = s.rd(ctx, 8);
    let init_done = s.rd(ctx + 8, 4);
    let avail_cnt = s.rd(ctx + 32, 8);
    let reserve_cnt = s.rd(ctx + 40, 8);
    let reserve = if reserve_cnt > 0 { s.rd(ctx + 72, 8) } else { 0 };
    let brk = s.rd(ctx + 920, 8);
    let mut areas = Vec::new();
    let mut h = s.rd(ctx + 56, 8);
    while h != 0 && areas.len() < 100_000 {
        areas.push(h);
        h = s.rd(h + 8, 8);
    }
    let free_metas = cyclic_list(s, s.rd(ctx + 16, 8));
    let active: Vec<Vec<u64>> = (0..48).map(|sc| cyclic_list(s, s.rd(ctx + 80 + 8 * sc, 8))).collect();
    let free_set: BTreeSet<u64> = free_metas.iter().copied().collect();
    let mut used = Vec::new();
    for (k, &a) in areas.iter().enumerate() {
        for j in 0..NSLOTS {
            let g = a + 24 + 40 * j;
            let avail = k + 1 == areas.len() && j + avail_cnt >= NSLOTS;
            if !avail && !free_set.contains(&g) {
                used.push(g);
            }
        }
    }
    used.sort();
    let mut metas = BTreeMap::new();
    for &g in &used {
        let w = s.rd(g + 32, 8);
        metas.insert(g, MetaV {
            prev: s.rd(g, 8),
            next: s.rd(g + 8, 8),
            mem: s.rd(g + 16, 8),
            avail: s.rd(g + 24, 4),
            freed: s.rd(g + 28, 4),
            last_idx: w & 31,
            freeable: (w >> 5) & 1,
            sizeclass: (w >> 6) & 63,
            maplen: w >> 12,
        });
    }
    // what each slot holds: free by the masks, else a nested group starting
    // there, else the client block inside it
    let nested_at: BTreeMap<u64, u64> = metas.iter().filter(|(_, v)| v.maplen == 0).map(|(g, v)| (v.mem, *g)).collect();
    let mut slots = BTreeMap::new();
    for (&g, v) in &metas {
        let mut us = Vec::new();
        for i in 0..=v.last_idx {
            if (v.avail | v.freed) >> i & 1 == 1 {
                us.push(Use::Unused);
                continue;
            }
            let st = v.slot_start(i);
            if let Some(&h) = nested_at.get(&st) {
                us.push(Use::Nested(h));
                continue;
            }
            let end = st + v.stride();
            match blocks.range(st..end).next() {
                Some((&p, _)) => us.push(Use::Block(p)),
                None => {
                    notes.push(format!("meta {:#x} slot {}: in use, but no block or nested group starts in it", g, i));
                    us.push(Use::Block(st));
                }
            }
        }
        slots.insert(g, us);
    }
    let (auxv_at, auxv) = if init_done == 0 {
        let q = s.rd(libc + 8, 8);
        let mut entries = Vec::new();
        for k in 0..1000 {
            let e = (s.rd(q + 16 * k, 8), s.rd(q + 16 * k + 8, 8));
            entries.push(e);
            if e.0 == 0 {
                break;
            }
        }
        (q, entries)
    } else {
        (0, Vec::new())
    };
    Abs { secret, init_done, auxv_at, auxv, areas, avail_cnt, reserve, reserve_cnt, free_metas, used, metas, active, slots, brk, notes }
}

// ----------------------------------------------------------------------
//  As interpreter values

fn n(x: u64) -> V {
    V::n(x as i128)
}

fn rec(fields: Vec<(&str, V)>) -> V {
    V::rec(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

fn list(xs: impl IntoIterator<Item = V>) -> V {
    V::tuple(xs.into_iter().collect())
}

fn some(v: V) -> V {
    V::Tag("some".into(), 1, vec![v])
}

fn none() -> V {
    V::Tag("none".into(), 0, vec![])
}

fn meta_v(v: &MetaV) -> V {
    rec(vec![
        ("prev", n(v.prev)), ("next", n(v.next)), ("mem", n(v.mem)), ("avail", n(v.avail)), ("freed", n(v.freed)),
        ("last_idx", n(v.last_idx)), ("freeable", n(v.freeable)), ("sizeclass", n(v.sizeclass)), ("maplen", n(v.maplen)),
    ])
}

fn abs_v(a: &Abs) -> V {
    let use_v = |u: &Use| match u {
        Use::Unused => V::Tag("unused".into(), 0, vec![]),
        Use::Block(p) => V::Tag("block".into(), 1, vec![n(*p)]),
        Use::Nested(g) => V::Tag("nested".into(), 2, vec![n(*g)]),
    };
    rec(vec![
        ("secret", n(a.secret)),
        ("init_done", n(a.init_done)),
        ("auxv_at", n(a.auxv_at)),
        ("auxv", list(a.auxv.iter().map(|&(k, v)| list([n(k), n(v)])))),
        ("areas", list(a.areas.iter().map(|&x| n(x)))),
        ("avail_cnt", n(a.avail_cnt)),
        ("reserve", n(a.reserve)),
        ("reserve_cnt", n(a.reserve_cnt)),
        ("free_metas", list(a.free_metas.iter().map(|&x| n(x)))),
        ("used", list(a.used.iter().map(|&x| n(x)))),
        ("metas", map(a.metas.iter().map(|(g, v)| (n(*g), meta_v(v))).collect(), Some(meta_v(&MetaV::default())))),
        ("active", list(a.active.iter().map(|l| list(l.iter().map(|&x| n(x)))))),
        ("slots", map(a.slots.iter().map(|(g, us)| (n(*g), list(us.iter().map(use_v)))).collect(), Some(list([])))),
        ("brk", n(a.brk)),
    ])
}

/// The machine state the invariant looks at: `vm` and the ghost `blocks`.
fn heap_v(s: &Snapshot, blocks: &BTreeMap<u64, u64>) -> V {
    let prot = |p: (bool, bool, bool)| rec(vec![("r", V::Bool(p.0)), ("w", V::Bool(p.1)), ("x", V::Bool(p.2))]);
    let mut pages = Vec::new();
    for m in &s.maps {
        if m.lo >= 0xffff_8000_0000_0000 {
            continue;
        }
        // enum Kind { anon, heap, stack }
        let kind = match m.name.as_str() {
            "[stack]" => 2,
            "[heap]" => 1,
            _ => 0,
        };
        for p in m.lo / 4096..m.hi / 4096 {
            pages.push((n(p), some(rec(vec![("prot", prot(m.prot)), ("kind", V::n(kind))]))));
        }
    }
    let vm = rec(vec![
        ("pages", map(pages, Some(none()))),
        ("bytes", map_backed_regions(Vec::new(), Some(V::bits(0, 8)), s.regions.clone())),
        ("brk", V::bits(s.brk as u128, 64)),
    ]);
    let bl = map(blocks.iter().map(|(&p, &sz)| (n(p), some(n(sz)))).collect(), Some(none()));
    rec(vec![("vm", vm), ("blocks", bl)])
}

// ----------------------------------------------------------------------
//  Checking

struct Checker<'g> {
    /// enumerates ranges up to 64 Ki (every code byte)
    thorough: Interp<'g>,
    /// enumerates up to 4 Ki, beyond that evaluates at page boundaries and
    /// breakpoints and samples in between (enough for page properties)
    fast: Interp<'g>,
    use_thorough: std::cell::Cell<bool>,
    c: V,
}

impl Checker<'_> {
    fn call(&self, f: &str, args: Vec<V>) -> Result<V, String> {
        let it = if self.use_thorough.get() { &self.thorough } else { &self.fast };
        it.call_in("mallocng", f, args, 20_000_000_000)
    }

    /// The conjuncts of `rep` that fail (or cannot be evaluated).
    fn check(&self, a: &Abs, s: &Snapshot, blocks: &BTreeMap<u64, u64>) -> Vec<String> {
        self.thorough.clear_memo();
        self.fast.clear_memo();
        let (av, hv) = (abs_v(a), heap_v(s, blocks));
        let (vm, bl) = (hv.field("vm").unwrap().clone(), hv.field("blocks").unwrap().clone());
        let mut bad: Vec<String> = a.notes.iter().map(|x| format!("abstraction: {}", x)).collect();
        // (the invariant's view: of `held`, the footprint but the context's
        // free bytes, as `rep` has it)
        let fp = match self.call("held", vec![self.c.clone(), av.clone(), bl.clone()]) {
            Ok(v) => v,
            Err(e) => return vec![format!("held: {}", e)],
        };
        let m = match self.call("mview", vec![vm.clone(), fp]) {
            Ok(v) => v,
            Err(e) => return vec![format!("mview: {}", e)],
        };
        // (the footprint's view, where the free bytes' access is stated)
        let mf = match self.call("footprint", vec![self.c.clone(), av.clone(), bl.clone()]).and_then(|f| self.call("mview", vec![vm.clone(), f])) {
            Ok(v) => v,
            Err(e) => return vec![format!("footprint view: {}", e)],
        };
        let regions = self.call("regions", vec![self.c.clone(), av.clone()]);
        let fpr = self.call("fp_ranges", vec![self.c.clone(), av.clone()]);
        let c = self.c.clone();
        let parts: Vec<(&str, &str, Vec<V>)> = vec![
            ("image_ok", "image_ok", vec![c.clone(), m.clone()]),
            ("ctx_ok", "ctx_ok", vec![c.clone(), av.clone(), m.clone()]),
            ("fresh_ok", "fresh_ok", vec![c.clone(), av.clone(), m.clone()]),
            ("areas_ok", "areas_ok", vec![c.clone(), av.clone(), m.clone()]),
            ("metas_partition", "metas_partition", vec![av.clone()]),
            ("active_ok", "active_ok", vec![av.clone()]),
            ("partial_ok", "partial_ok", vec![av.clone(), m.clone()]),
            ("reuse_ok", "reuse_ok", vec![av.clone()]),
            ("blocks_ok", "blocks_ok", vec![av.clone(), bl.clone()]),
            ("normal", "normal", vec![av.clone()]),
            ("brk_ok", "brk_ok", vec![av.clone(), vm.field("brk").unwrap().clone()]),
            ("perms_ok", "perms_ok", vec![c.clone(), av.clone(), m.clone(), bl.clone()]),
            ("blocks_wf", "blocks_wf", vec![bl.clone()]),
            ("live_rw", "live_rw", vec![hv.clone()]),
            ("free_rw", "free_rw", vec![c.clone(), mf.clone()]),
            ("grp_rw", "grp_rw", vec![c.clone(), av.clone(), vm.clone(), bl.clone()]),
        ];
        let timing = std::env::var("HEAPCHECK_TIMES").is_ok();
        let profile = std::env::var("HEAPCHECK_PROFILE").is_ok();
        for (label, f, args) in parts {
            let t0 = std::time::Instant::now();
            if profile {
                sl_interp::profile_start();
            }
            let r = self.call(f, args);
            if timing {
                eprintln!("  {:>16}: {:?}", label, t0.elapsed());
            }
            if profile {
                let calls: Vec<String> = sl_interp::profile_take().into_iter().take(8).map(|(n, k)| format!("{} {}", n, k)).collect();
                eprintln!("  {:>16}  calls: {}", "", calls.join(", "));
            }
            match r {
                Ok(V::Bool(true)) => {}
                Ok(v) => bad.push(format!("{}: {}", label, v.render())),
                Err(e) => bad.push(format!("{}: cannot evaluate: {}", label, e)),
            }
        }
        match regions.and_then(|r| self.call("separate", vec![r])) {
            Ok(V::Bool(true)) => {}
            other => bad.push(format!("separate: {:?}", other.map(|v| v.render()))),
        }
        match fpr.and_then(|r| self.call("fp_mapped", vec![r, bl.clone(), vm.clone()])) {
            Ok(V::Bool(true)) => {}
            other => bad.push(format!("fp_mapped: {:?}", other.map(|v| v.render()))),
        }
        // used_ok group by group, for a precise report
        for &g in &a.used {
            match self.call("group_ok", vec![av.clone(), m.clone(), bl.clone(), n(g)]) {
                Ok(V::Bool(true)) => {}
                other => bad.push(format!("group_ok({:#x}) {:?}: {:?}", g, a.metas[&g], other.map(|v| v.render()))),
            }
        }
        bad
    }
}

/// Corrupts a good state in known ways; each corruption must be reported.
fn selftest(ck: &Checker, a: &Abs, s: &Snapshot, blocks: &BTreeMap<u64, u64>, code_at: u64) -> Result<(), String> {
    let (&p, &n0) = blocks.iter().next().ok_or("selftest: no live block")?;
    let slot = a.slots.iter().find_map(|(g, us)| us.iter().position(|u| matches!(u, Use::Block(q) if *q == p)).map(|i| (*g, i)));
    let (g, i) = slot.ok_or("selftest: block not in a slot")?;
    let mut cases: Vec<(&str, Abs, Snapshot, BTreeMap<u64, u64>)> = Vec::new();
    let mut a1 = a.clone();
    a1.secret ^= 1;
    cases.push(("abstract secret differs from memory", a1, s.clone(), blocks.clone()));
    let mut a2 = a.clone();
    a2.slots.get_mut(&g).unwrap()[i] = Use::Unused;
    cases.push(("a used slot claimed free", a2, s.clone(), blocks.clone()));
    let mut s3 = s.clone();
    s3.set_byte(p - 3, s.byte(p - 3) ^ 1);
    cases.push(("block header byte p[-3] corrupted", a.clone(), s3, blocks.clone()));
    let mut b4 = blocks.clone();
    b4.remove(&p);
    cases.push(("a block forgotten", a.clone(), s.clone(), b4));
    let mut b5 = blocks.clone();
    b5.insert(p, n0 + 1);
    cases.push(("wrong block size", a.clone(), s.clone(), b5));
    let mut s6 = s.clone();
    for m in s6.maps.iter_mut() {
        if m.lo <= p && p < m.hi {
            // split off the block's page as read-only
            let pg = p & !4095;
            let (lo, hi, name) = (m.lo, m.hi, m.name.clone());
            m.hi = pg;
            let mut extra = vec![Mapping { lo: pg, hi: pg + 4096, prot: (true, false, false), name: name.clone() }];
            if pg + 4096 < hi {
                extra.push(Mapping { lo: pg + 4096, hi, prot: m.prot, name });
            }
            let _ = lo;
            s6.maps.extend(extra);
            break;
        }
    }
    s6.maps.retain(|m| m.lo < m.hi);
    s6.maps.sort_by_key(|m| m.lo);
    cases.push(("a block's page made read-only", a.clone(), s6, blocks.clone()));
    let mut s7 = s.clone();
    s7.set_byte(code_at, s.byte(code_at) ^ 0xff);
    cases.push(("a code byte changed (malloc's first byte)", a.clone(), s7, blocks.clone()));
    if let Some(&area) = a.areas.first() {
        let mut s8 = s.clone();
        s8.set_byte(area, s.byte(area) ^ 1);
        cases.push(("an area's check word corrupted", a.clone(), s8, blocks.clone()));
    }
    let mut missed = 0;
    for (what, a, s, b) in cases {
        let bad = ck.check(&a, &s, &b);
        match bad.first() {
            Some(first) => println!("  detected: {:<45} ({})", what, first),
            None => {
                missed += 1;
                println!("  MISSED:   {}", what);
            }
        }
    }
    if missed > 0 {
        return Err(format!("selftest: {} corruptions not detected", missed));
    }
    Ok(())
}

// ----------------------------------------------------------------------
//  The run

#[derive(Clone, Copy, PartialEq)]
enum Fun {
    Main,
    Malloc,
    Calloc,
    Free,
}

struct Frame {
    fun: Fun,
    arg: u64,
    size: u64,
    ret: u64,
    rsp: u64,
}

pub fn heapcheck(args: &[String]) -> CResult {
    let mut every = 1u64;
    let mut self_test = false;
    let mut max_checks = u64::MAX;
    let mut prog = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--every" => every = it.next().and_then(|x| x.parse().ok()).ok_or("--every N")?,
            "--max" => max_checks = it.next().and_then(|x| x.parse().ok()).ok_or("--max N")?,
            "--selftest" => self_test = true,
            _ => prog.push(a.clone()),
        }
    }
    let elf_path = prog.first().ok_or("usage: slc heapcheck [--every N] [--max N] ELF [ARGS...]")?.clone();
    let bytes = std::fs::read(&elf_path).map_err(|e| format!("{}: {}", elf_path, e))?;
    let elf = Elf::parse(bytes.clone())?;
    let sym = |n: &str| elf.symbol(n).map(|s| s.value).ok_or_else(|| format!("symbol `{}` not found", n));
    let (main_at, malloc_at, calloc_at, free_at) = (sym("main")?, sym("malloc")?, sym("calloc")?, sym("free")?);
    let (ctx, lock, libc, sct) = (sym("__malloc_context")?, sym("__malloc_lock")?, sym("__libc")?, sym("__malloc_size_classes")?);
    // (a_ctz_32's table; an optimized build counts with an instruction and
    // has none -- the class table's range then, a read-only constant too)
    let dbj = sym("debruijn32.0").unwrap_or(sct);

    // the spec and layers, for the interpreter
    let root = repo_root();
    let mut sm = sl_syntax::SourceMap::default();
    let files = parse_all(&[root.join("spec"), root.join("layers")], &mut sm)?;
    let g = sl_elab::globals::Globals::build(files)?;
    let mut thorough = Interp::new(&g, "x86")?;
    thorough.enum_limit = 1 << 16;
    thorough.lazy_sets = true;
    thorough.memo_calls = true;
    let mut fast = Interp::new(&g, "x86")?;
    fast.lazy_sets = true;
    fast.memo_calls = true;
    let checker = Checker {
        thorough,
        fast,
        use_thorough: std::cell::Cell::new(true),
        c: rec(vec![
            ("file", map_backed_regions(Vec::new(), Some(V::bits(0, 8)), vec![(0, bytes.clone())])),
            ("ctx", n(ctx)),
            ("lock", n(lock)),
            ("libc", n(libc)),
            ("sct", n(sct)),
            ("dbj", n(dbj)),
        ]),
    };

    // start the program, stopped at exec
    let mut cmd = std::process::Command::new(&elf_path);
    cmd.args(&prog[1..]);
    unsafe {
        cmd.pre_exec(|| {
            ptrace(PTRACE_TRACEME, 0, 0, 0);
            Ok(())
        });
    }
    let child = cmd.spawn().map_err(|e| e.to_string())?;
    let pid = child.id() as u64;
    let t = Tracee { pid, mem: std::fs::File::open(format!("/proc/{}/mem", pid)).map_err(|e| e.to_string())? };
    if !matches!(t.wait(), Stop::Trap) {
        return Err("the program did not stop at exec".into());
    }
    ptrace(PTRACE_SETOPTIONS, pid, 0, PTRACE_O_EXITKILL);
    let entries = [(main_at, Fun::Main), (malloc_at, Fun::Malloc), (calloc_at, Fun::Calloc), (free_at, Fun::Free)];
    let mut bps = Bps(BTreeMap::new());
    for (a, _) in entries {
        bps.set(&t, a);
    }

    let mut blocks: BTreeMap<u64, u64> = BTreeMap::new();
    let mut frames: Vec<Frame> = Vec::new();
    let (mut calls, mut checks, mut failures) = (0u64, 0u64, 0u64);
    let selftest_done = std::cell::Cell::new(false);
    let run_check = |what: &str, blocks: &BTreeMap<u64, u64>, originals: &BTreeMap<u64, u64>, checks: &mut u64, failures: &mut u64| -> Result<(), String> {
        let mut s = Snapshot::take(&t)?;
        // the program's own bytes under our breakpoints
        for (&a, &w) in originals {
            s.set_byte(a, w as u8);
        }
        let a = abstraction(&s, ctx, libc, blocks);
        let bad = checker.check(&a, &s, blocks);
        *checks += 1;
        if bad.is_empty() {
            let nested = a.metas.values().filter(|v| v.maplen == 0).count();
            let big = a.metas.values().filter(|v| v.sizeclass == 63).count();
            println!(
                "ok    {} ({} blocks, {} groups: {} nested, {} mapped, {} big; {} areas, {} free metas, {} reserved pages, brk {})",
                what,
                blocks.len(),
                a.used.len(),
                nested,
                a.used.len() - nested,
                big,
                a.areas.len(),
                a.free_metas.len(),
                a.reserve_cnt,
                match a.brk {
                    0 => "unused".to_string(),
                    u64::MAX => "given up".to_string(),
                    b => format!("{:#x}", b),
                }
            );
            if self_test && blocks.len() >= 2 && !a.areas.is_empty() {
                println!("selftest on this state (thorough):");
                checker.use_thorough.set(true);
                selftest(&checker, &a, &s, blocks, malloc_at)?;
                println!("selftest passed: every corruption was reported");
                selftest_done.set(true);
            }
        } else {
            *failures += 1;
            println!("FAIL  {}", what);
            for b in bad {
                println!("      {}", b);
            }
        }
        Ok(())
    };
    loop {
        if selftest_done.get() {
            ptrace(PTRACE_KILL, pid, 0, 0);
            return Ok(());
        }
        t.cont();
        match t.wait() {
            Stop::Exited(code) => {
                println!("exited with {}: {} calls, {} checks, {} failed", code, calls, checks, failures);
                break;
            }
            Stop::Other(sig) => {
                ptrace(PTRACE_KILL, pid, 0, 0);
                return Err(format!("the program stopped with signal {}", sig));
            }
            Stop::Trap => {}
        }
        let r = t.regs();
        let at = r.rip - 1;
        if let Some(&(_, f)) = entries.iter().find(|e| e.0 == at) {
            if f == Fun::Main {
                run_check("at main (thorough: every byte)", &blocks, &bps.0, &mut checks, &mut failures)?;
                checker.use_thorough.set(false);
            } else {
                let ret = t.peek(r.rsp);
                let size = match f {
                    Fun::Malloc => r.rdi,
                    Fun::Calloc => r.rdi.wrapping_mul(r.rsi),
                    _ => 0,
                };
                frames.push(Frame { fun: f, arg: r.rdi, size, ret, rsp: r.rsp });
                bps.set(&t, ret);
            }
            bps.step_over(&t, at, true)?;
        } else if let Some(k) = frames.iter().rposition(|fr| fr.ret == at && r.rsp == fr.rsp + 8) {
            let fr = frames.remove(k);
            match fr.fun {
                Fun::Malloc | Fun::Calloc if r.rax != 0 => {
                    blocks.insert(r.rax, fr.size);
                }
                Fun::Free if fr.arg != 0 => {
                    blocks.remove(&fr.arg);
                }
                _ => {}
            }
            let keep = frames.iter().any(|f| f.ret == at) || entries.iter().any(|e| e.0 == at);
            bps.step_over(&t, at, keep)?;
            if frames.is_empty() {
                calls += 1;
                if calls % every == 0 && checks < max_checks {
                    let what = match fr.fun {
                        Fun::Malloc => format!("call {}: malloc({}) = {:#x}", calls, fr.arg, r.rax),
                        Fun::Calloc => format!("call {}: calloc(.., ..) of {} = {:#x}", calls, fr.size, r.rax),
                        Fun::Free => format!("call {}: free({:#x})", calls, fr.arg),
                        Fun::Main => String::new(),
                    };
                    run_check(&what, &blocks, &bps.0, &mut checks, &mut failures)?;
                }
            }
        } else {
            ptrace(PTRACE_KILL, pid, 0, 0);
            return Err(format!("unexpected trap at {:#x}", at));
        }
    }
    if failures > 0 {
        return Err(format!("{} of {} checks failed", failures, checks));
    }
    Ok(())
}
