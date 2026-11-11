//! `slc mainrun ELF [--max N]`: the model run from a concrete exec state
//! (spec/linux/exec.sl's `exec_state`, with chosen argv, environment, stack
//! place and random bytes) until `main` is entered -- each step by the
//! interpreter (untrusted), the first outcome taken. Reports the steps, the
//! time, and where the run stopped: the trace a witness that some run reaches
//! `main` would rest on (docs/todo.md §2).

use crate::commands::{repo_root, CResult};
use sl_interp::elf::Elf;
use sl_interp::{map, map_backed_regions, Interp, Outcome, V};
use std::collections::BTreeMap;

const PAGE: u64 = 4096;
const TASK_SIZE: u64 = (1 << 47) - PAGE;

fn bits(v: u64, w: u32) -> V {
    V::Num(sl_interp::num::Int::from_u128(v as u128), Some(w))
}

fn rec(fields: Vec<(&str, V)>) -> V {
    V::rec(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect::<BTreeMap<_, _>>())
}

/// `some(Page { prot, kind })`, prot bits r=1 w=2 x=4, kind anon 0 / stack 2
fn page(prot: u32, kind: i128) -> V {
    let p = rec(vec![("r", V::Bool(prot & 1 != 0)), ("w", V::Bool(prot & 2 != 0)), ("x", V::Bool(prot & 4 != 0))]);
    V::Tag("some".into(), 1, vec![rec(vec![("prot", p), ("kind", V::n(kind))])])
}

fn none() -> V {
    V::Tag("none".into(), 0, vec![])
}

/// The initial machine: the image's pages and bytes, the stack with argv,
/// the (empty) environment and auxv, registers per exec_state
pub fn exec_machine(elf: &Elf, argv0: &str) -> Result<(V, u64), String> {
    // (the ELF's protection flags: PF_X 1, PF_W 2, PF_R 4 -> r 1, w 2, x 4)
    let prot = |f: u32| (f & 4 != 0) as u32 | ((f & 2 != 0) as u32) << 1 | ((f & 1 != 0) as u32) << 2;
    let mut pages: BTreeMap<u64, V> = BTreeMap::new();
    let mut regions: Vec<(u64, Vec<u8>)> = Vec::new();
    let mut image_end = 0;
    for s in &elf.segments {
        if s.memsz == 0 {
            continue;
        }
        for p in s.vaddr / PAGE..=(s.vaddr + s.memsz - 1) / PAGE {
            pages.insert(p, page(prot(s.flags), 0));
        }
        let data = elf.data[s.offset as usize..(s.offset + s.filesz) as usize].to_vec();
        regions.push((s.vaddr, data));
        image_end = image_end.max(s.vaddr + s.memsz);
    }
    // the stack: 32 pages below TASK_SIZE
    let top = TASK_SIZE / PAGE;
    let lo = top - 32;
    for p in lo..top {
        pages.insert(p, page(3, 2));
    }
    let mut stack: Vec<(u64, u8)> = Vec::new();
    let mut put = |a: u64, bs: &[u8]| {
        for (i, b) in bs.iter().enumerate() {
            stack.push((a + i as u64, *b));
        }
    };
    let mut hi = top * PAGE - 16;
    // the strings: argv[0] (also AT_EXECFN), the 16 random bytes
    let name: Vec<u8> = argv0.bytes().chain([0]).collect();
    hi -= name.len() as u64;
    let name_at = hi;
    put(name_at, &name);
    hi -= 16;
    let random_at = hi & !15;
    put(random_at, &(0..16u8).map(|i| 0x5a ^ i).collect::<Vec<_>>());
    // the headers' address: the first load segment's vaddr less its offset, + e_phoff
    let first = elf.segments.iter().find(|s| s.memsz > 0).ok_or("no load segment")?;
    let phoff = u64::from_le_bytes(elf.data[32..40].try_into().unwrap());
    let phnum = u16::from_le_bytes(elf.data[56..58].try_into().unwrap()) as u64;
    let phdr = first.vaddr - first.offset + phoff;
    let auxv: Vec<(u64, u64)> = vec![
        (3, phdr),
        (4, 56),
        (5, phnum),
        (6, PAGE),
        (9, elf.entry),
        (11, 1000),
        (12, 1000),
        (13, 1000),
        (14, 1000),
        (23, 0),
        (25, random_at),
        (31, name_at),
        (0, 0),
    ];
    // argc, argv[0], 0, (no envp) 0, auxv: 16-byte aligned
    let words = 4 + 2 * auxv.len() as u64;
    let sp = (random_at - 8 * words) & !15;
    let mut w = Vec::new();
    w.extend([1u64, name_at, 0, 0]);
    for (k, v) in &auxv {
        w.extend([*k, *v]);
    }
    for (i, x) in w.iter().enumerate() {
        put(sp + 8 * i as u64, &x.to_le_bytes());
    }
    let entries: Vec<(V, V)> = stack.iter().map(|(a, b)| (V::n(*a as i128), bits(*b as u64, 8))).collect();
    let brk = image_end.div_ceil(PAGE) * PAGE + 0x10000;
    let vm = rec(vec![
        ("pages", map(pages.into_iter().map(|(p, v)| (V::n(p as i128), v)).collect(), Some(none()))),
        ("bytes", map_backed_regions(entries, Some(bits(0, 8)), regions)),
        ("stack_top", bits(top * PAGE, 64)),
        ("stack_limit", V::n(8 << 20)),
        ("brk_start", bits(brk, 64)),
        ("brk", bits(brk, 64)),
    ]);
    let gpr = map((0..16).map(|i| (V::n(i as i128), bits(if i == 4 { sp } else { 0 }, 64))).collect(), None);
    let xmm = map((0..16).map(|i| (V::n(i as i128), bits(0, 128))).collect(), None);
    let flags = rec(["cf", "pf", "af", "zf", "sf", "df", "of"].iter().map(|n| (*n, V::Bool(false))).collect());
    let creds = rec(vec![("uid", bits(1000, 32)), ("euid", bits(1000, 32)), ("gid", bits(1000, 32)), ("egid", bits(1000, 32))]);
    let os = rec(vec![("input", V::tuple(vec![])), ("events", V::tuple(vec![])), ("creds", creds), ("secure", V::Bool(false))]);
    let m = rec(vec![
        ("gpr", gpr),
        ("xmm", xmm),
        ("rip", bits(elf.entry, 64)),
        ("flags", flags),
        ("cpu", rec(vec![("bmi1", V::Bool(false)), ("pku", V::Bool(false))])),
        ("fs_base", bits(0, 64)),
        ("gs_base", bits(0, 64)),
        ("vm", vm),
        ("os", os),
    ]);
    Ok((m, sp))
}

/// (PROBE) the initial machine as a kernel term, then `n` steps by the
/// kernel's evaluator (the decodings by `members`, the next state a
/// witness from the outcomes, `runs(..)` to it kernel-checked), each timed,
/// and `rip = main` at the end -- a `text` line's `mainrun N`
pub fn probe(env: &mut sl_kernel::Env, elf: &Elf, n: usize) -> Result<(), String> {
    use sl_kernel::ext::seq::Seq;
    let ke = |e: sl_kernel::KernelError| e.0;
    let prot = |f: u32| format!("fn_update(fn_update(fn_update(empty, \"r\", {}), \"w\", {}), \"x\", {})", f & 4 != 0, f & 2 != 0, f & 1 != 0);
    let pg = |pr: String, kind: u32| format!("some(fn_update(fn_update(empty, \"prot\", {}), \"kind\", {}))", pr, kind);
    // memory: the stack region a literal, the segments the file's bytes, else 0
    let (m0v, sp) = exec_machine(elf, "test_malloc")?;
    let top = TASK_SIZE;
    let bytes_v = m0v.field("vm").and_then(|v| v.field("bytes")).cloned().ok_or("bytes")?;
    let stack: Vec<u8> = (sp..top).map(|a| bytes_v.map_get(&V::n(a as i128)).and_then(|b| b.num().ok()).unwrap_or(0) as u8).collect();
    let hex: String = stack.iter().map(|b| format!("{:02x}", b)).collect();
    let mut bytes = "0".to_string();
    let mut pages = "none".to_string();
    // (the file's bytes: the claim's `musl_malloc.file`)
    for s in elf.segments.iter().filter(|s| s.memsz > 0) {
        bytes = format!(
            "ite(int_le({v}, a) && int_lt(a, {e}), ite(int_lt(a, {fe}), app(musl_malloc.file, int_add(int_sub(a, {v}), {o})), 0), {rest})",
            v = s.vaddr, e = s.vaddr + s.memsz, fe = s.vaddr + s.filesz, o = s.offset, rest = bytes
        );
        pages = format!("ite(int_le({}, p) && int_le(p, {}), {}, {})", s.vaddr / PAGE, (s.vaddr + s.memsz - 1) / PAGE, pg(prot(s.flags), 0), pages);
    }
    bytes = format!("ite(int_le({sp}, a) && int_lt(a, {top}), app(bytes_seq(bytes\"{hex}\"), int_sub(a, {sp})), {rest})", rest = bytes);
    let lo = top / PAGE - 32;
    pages = format!("ite(int_le({}, p) && int_lt(p, {}), {}, {})", lo, top / PAGE, pg(prot(6), 2), pages);
    let num = |path: &[&str]| -> u64 {
        let mut v = &m0v;
        for f in path {
            v = v.field(f).unwrap();
        }
        v.num().unwrap_or(0) as u64
    };
    let rec = |fs: &[(&str, String)]| fs.iter().fold("empty".to_string(), |acc, (k, v)| format!("fn_update({}, \"{}\", {})", acc, k, v));
    let flags = rec(&["cf", "pf", "af", "zf", "sf", "df", "of"].iter().map(|f| (*f, "false".to_string())).collect::<Vec<_>>());
    let vm = rec(&[
        ("pages", format!("fn_build(set_select(omega, p. int_lt(p, {})), p. {})", TASK_SIZE / PAGE, pages)),
        ("bytes", format!("fn_build(bits(64), a. {})", bytes)),
        ("stack_top", top.to_string()),
        ("stack_limit", (8u64 << 20).to_string()),
        ("brk_start", num(&["vm", "brk_start"]).to_string()),
        ("brk", num(&["vm", "brk"]).to_string()),
    ]);
    let creds = rec(&[("uid", "1000".into()), ("euid", "1000".into()), ("gid", "1000".into()), ("egid", "1000".into())]);
    let os = rec(&[("input", "empty".into()), ("events", "empty".into()), ("creds", creds), ("secure", "false".into())]);
    let m = rec(&[
        ("gpr", format!("fn_build(x86_64_linux.Reg, r. ite(r = 4, {}, 0))", sp)),
        ("xmm", "fn_build(x86_64_linux.Reg, r. 0)".into()),
        ("rip", elf.entry.to_string()),
        ("flags", flags),
        ("cpu", rec(&[("bmi1", "false".into()), ("pku", "false".into())])),
        ("fs_base", "0".into()),
        ("gs_base", "0".into()),
        ("vm", vm),
        ("os", os),
    ]);
    if std::env::var("PROBE_PRINT").is_ok() {
        eprintln!("probe m0: {}", m);
    }
    let mut mt = sl_kernel::syntax::parse_term(env, &m, &[]).map_err(ke)?;
    let lg = sl_kernel::ext::prop::Logic::new(env).map_err(ke)?;
    fn find_ok(env: &sl_kernel::Env, t: &sl_kernel::Term) -> Option<sl_kernel::Term> {
        if let sl_kernel::Node::App(f, a) = t.node() {
            if env.syms[*f as usize].name == "ok" && a.len() == 2 {
                return Some(a[0].clone());
            }
            return a.iter().find_map(|x| find_ok(env, x));
        }
        None
    }
    let t0 = std::time::Instant::now();
    for k in 0..n {
        let t1 = std::time::Instant::now();
        // (1) the decodings of the bytes at rip -- as step() forms them
        let (sym, app) = (|n: &str| env.sym_by_name[n], sl_kernel::Term::app);
        let (runs, fnb, omega) = (sym("runs"), sym("fn_build"), sym("omega"));
        let (appf, bits_add, rip_t, vm_t, bytes_t) = (sym("app"), sym("bits_add"), sl_kernel::Term::bytes(b"rip"), sl_kernel::Term::bytes(b"vm"), sl_kernel::Term::bytes(b"bytes"));
        let nat = |v: u64| sl_kernel::Term::nat(sl_kernel::nat::Nat::from_u64(v));
        let rip_v = app(appf, vec![mt.clone(), rip_t]);
        let mem = app(appf, vec![app(appf, vec![mt.clone(), vm_t]), bytes_t]);
        let window = app(fnb, vec![app(omega, vec![]), app(appf, vec![mem.shift(1, 0, &env.binders_fn()), app(bits_add, vec![nat(64), rip_v.shift(1, 0, &env.binders_fn()), sl_kernel::Term::bvar(0)])])]);
        let dset = app(sym("x86_64_linux.x86.decode"), vec![window]);
        let dm = Seq::members(env, &lg, &dset, &[]).map_err(|e| format!("step {}: decode: {}", k, e.0))?;
        let t2 = std::time::Instant::now();
        // the one decoding (len, insn)
        fn find_pair(env: &sl_kernel::Env, t: &sl_kernel::Term) -> Option<(sl_kernel::Term, sl_kernel::Term)> {
            if let sl_kernel::Node::App(f, a) = t.node() {
                if env.syms[*f as usize].name == "eq" && a.len() == 2 {
                    if let sl_kernel::Node::App(p, b) = a[1].node() {
                        if env.syms[*p as usize].name == "pair" && b.len() == 2 {
                            return Some((b[0].clone(), b[1].clone()));
                        }
                    }
                }
                return a.iter().find_map(|x| find_pair(env, x));
            }
            None
        }
        let (len, insn) = find_pair(env, dm.concl()).ok_or_else(|| format!("step {}: no decoding", k))?;
        // (2) exec_insn(len, insn)'s outcomes from mt
        // the outcome as a witness (no theorem), then `runs(.., ok(M', v))`
        // kernel-checked
        let ei = app(sym("x86_64_linux.exec_insn"), vec![len, insn]);
        let outs = lg.eval_outcomes(env, &ei, &mt).map_err(|e| format!("step {}: exec: {}", k, e.0))?;
        let t3 = std::time::Instant::now();
        let Some(o) = outs.iter().find(|o| find_ok(env, o).is_some()).cloned() else {
            // (each outcome's end: an exception's value)
            let c: Vec<String> = outs
                .iter()
                .map(|o| match o.node() {
                    sl_kernel::Node::App(_, a) if a.len() == 2 => sl_kernel::syntax::Printer::new(env).short(&a[1]),
                    _ => "?".into(),
                })
                .collect();
            return Err(format!("step {}: no ok outcome: ..{}", k, c.join(" | ..")));
        };
        let goal = app(runs, vec![ei, mt.clone(), o.clone()]);
        Seq::eval_goal(env, &lg, &[], &goal).map_err(|e| format!("step {}: check: {}", k, e.0))?;
        eprintln!("  decode {:.3} s, exec {:.3} s, check {:.3} s ({} outcomes)", (t2 - t1).as_secs_f64(), (t3 - t2).as_secs_f64(), t3.elapsed().as_secs_f64(), outs.len());
        mt = find_ok(env, &o).unwrap();
        eprintln!("kernel step {}: {:.3} s", k, t1.elapsed().as_secs_f64());
    }
    eprintln!("kernel: {} steps, {:.2} s", n, t0.elapsed().as_secs_f64());
    // where the run is: `rip = main` checked
    if let Some(main) = elf.symbol("main") {
        let (sym, app) = (|n: &str| env.sym_by_name[n], sl_kernel::Term::app);
        let rip = app(sym("app"), vec![mt.clone(), sl_kernel::Term::bytes(b"rip")]);
        let goal = app(sym("eq"), vec![rip, sl_kernel::Term::nat(sl_kernel::nat::Nat::from_u64(main.value))]);
        match Seq::eval_goal(env, &lg, &[], &goal) {
            Ok(_) => eprintln!("kernel: at main ({:#x})", main.value),
            Err(e) => eprintln!("kernel: not at main: {}", e.0.chars().take(200).collect::<String>()),
        }
    }
    Ok(())
}

fn rip(m: &V) -> Option<u64> {
    m.field("rip").and_then(|r| r.num().ok()).map(|n| n as u64)
}

pub fn mainrun(args: &[String]) -> CResult {
    let mut path = None;
    let mut max = 1_000_000usize;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--max" => max = it.next().and_then(|x| x.parse().ok()).ok_or("--max N")?,
            p => path = Some(p.to_string()),
        }
    }
    let path = path.ok_or("usage: slc mainrun ELF [--max N]")?;
    let elf = Elf::parse(std::fs::read(&path).map_err(|e| format!("{}: {}", path, e))?)?;
    let main_at = elf.symbol("main").ok_or("no symbol `main`")?.value;
    let root = repo_root();
    let mut sm = sl_syntax::SourceMap::default();
    let files = crate::commands::parse_all(&[root.join("spec")], &mut sm)?;
    let g = sl_elab::globals::Globals::build(files)?;
    let interp = Interp::new(&g, "x86")?;
    let (mut m, sp) = exec_machine(&elf, "test_malloc")?;
    println!("exec: entry {:#x}, rsp {:#x}, main {:#x}", elf.entry, sp, main_at);
    let t0 = std::time::Instant::now();
    // (choices the interpreter cannot enumerate: a small positive value)
    let hints = [bits(1, 64), V::n(1)];
    let mut n = 0;
    let mut syms: BTreeMap<String, usize> = BTreeMap::new();
    while rip(&m) != Some(main_at) {
        if n >= max {
            return Err(format!("{} steps, not at main (rip {:#x})", n, rip(&m).unwrap_or(0)));
        }
        let r = rip(&m).unwrap_or(0);
        let f = elf.symbol_at(r).map(|s| s.name.clone()).unwrap_or_else(|| "?".into());
        *syms.entry(f.clone()).or_default() += 1;
        let outs = interp.step_with_hints(&m, 64, &hints);
        match outs.into_iter().next() {
            Some(Outcome::Ok(m2)) => m = m2,
            Some(Outcome::Exc(_, e)) => return Err(format!("step {} at {:#x} ({}): raised {}", n, r, f, e.render())),
            Some(Outcome::Undefined) => return Err(format!("step {} at {:#x} ({}): undefined", n, r, f)),
            Some(Outcome::Unsupported(s)) => return Err(format!("step {} at {:#x} ({}): unsupported: {}", n, r, f, s)),
            None => return Err(format!("step {} at {:#x} ({}): no outcome", n, r, f)),
        }
        n += 1;
    }
    println!("main reached: {} steps, {:.2} s", n, t0.elapsed().as_secs_f64());
    let mut by: Vec<(usize, String)> = syms.into_iter().map(|(k, v)| (v, k)).collect();
    by.sort_by(|a, b| b.cmp(a));
    for (c, f) in by.iter().take(15) {
        println!("  {:6} {}", c, f);
    }
    Ok(())
}
