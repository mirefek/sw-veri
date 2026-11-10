//! The decode facts of a binary's functions, made in the checker: the
//! chain line
//!
//!   steps NAME "ELF" "SHA256" "SYMBOL .."
//!
//! (the ELF file by its path and hash: a line unchanged is a binary
//! unchanged, for the file cache). For every distinct instruction encoding
//! in the functions: a theorem `x86.step_HEX` that a machine whose bytes at
//! `rip` are the encoding's runs `step()` as `exec_insn(len, insn)` of its
//! one decoding -- for any `rip` and any state. Its hypotheses are the
//! bytes the decoder reads (the instruction's own, unless some row looks
//! further). Exclusivity (no other row matches) is shown by the evaluator
//! (`members`). The instruction boundaries come from the untrusted
//! interpreter; a wrong one only makes a theorem fail or go unused.
//!
//! Then, per function `F`: its bytes `F.code` (a definition), and for the
//! instruction at each address A, `F.at_A` (with the code loaded and
//! `rip = A`, a step runs the instruction's body: its fetch succeeds) --
//! the decode facts the C1 engine (`c1` lines) walks, the body's semantics
//! then by the instruction forms of proofs/x86_insn.core.
//!
//! All made by the kernel's rules (`sl_proof::api`), no proof text.
//!
//! `slc steps ELF SYMBOL... -o STEPS.core [--text TEXT.core]` writes the
//! line (with the ELF's hash), and the program text.

use crate::commands::{load_spec_globals, CResult};
use sl_interp::elf::Elf;
use sl_interp::Interp;
use sl_kernel::ext::seq::{defined_sym, unfold_all, Seq};
use sl_kernel::syntax::parse_term;
use sl_kernel::{Env, Node, Term, VarId};
use sl_proof::api::{Api, A, G};
use std::collections::BTreeMap;

type R<T> = Result<T, String>;

fn ke(x: sl_kernel::KernelError) -> String {
    x.0
}

const BYTES: &str = "app(app(app(m, \"vm\"), \"bytes\"), bits_add(64, app(m, \"rip\"), {k}))";
const DECODED: &str = "fn_build(omega, i. app(app(app(m, \"vm\"), \"bytes\"), bits_add(64, app(m, \"rip\"), bits_of_int(64, i))))";

fn byte_eq(k: usize, v: u8) -> String {
    format!("{} = {}", BYTES.replace("{k}", &k.to_string()), v)
}

/// A function by name (or `alias=address`, hex: the function at the
/// address, named alias -- a static function with copies in several
/// files): its name and symbol -- an assembly function without its size
/// (`.size`, e.g. musl's memcpy) up to the next symbol
fn function<'a>(elf: &'a Elf, s: &'a str) -> R<(&'a str, sl_interp::elf::Symbol)> {
    // (`!ADDR+LEN` suffixes: instructions skipped, `skips`)
    let s = s.split('!').next().unwrap_or(s);
    // (`name:len`: a symbol without its size, its bytes given -- crti's
    // `_init`, its section's end before the next symbol)
    if let Some((n, l)) = s.split_once(':') {
        let len: u64 = l.parse().map_err(|e| format!("{}: {}", s, e))?;
        let sym = elf.symbol(n).ok_or_else(|| format!("no symbol `{}`", n))?;
        return Ok((n, sl_interp::elf::Symbol { name: sym.name.clone(), value: sym.value, size: len }));
    }
    let (name, sym) = match s.split_once('=') {
        Some((alias, a)) => {
            let addr = u64::from_str_radix(a.trim_start_matches("0x"), 16).map_err(|e| format!("{}: {}", s, e))?;
            let sym = elf.symbol_at(addr).filter(|y| y.value == addr).ok_or_else(|| format!("no function at {:x}", addr))?;
            (alias, sym)
        }
        None => (s, elf.symbol(s).ok_or_else(|| format!("no symbol `{}`", s))?),
    };
    let size = if sym.size > 0 {
        sym.size
    } else {
        elf.symbols.iter().filter(|y| y.value > sym.value).map(|y| y.value).min().ok_or_else(|| format!("{}: no size, no symbol after it", s))? - sym.value
    };
    Ok((name, sl_interp::elf::Symbol { name: sym.name.clone(), value: sym.value, size }))
}

/// A function's `!ADDR+LEN` suffixes: instructions (address, length, hex)
/// passed over without a decode fact -- ones the model's decoder has not,
/// on no path the function runs (gcc's `addr32 call` of a weak symbol
/// absent); the boundaries are untrusted, so are these
fn skips(s: &str) -> R<Vec<(u64, u64)>> {
    s.split('!').skip(1).map(|p| {
        let (a, l) = p.split_once('+').ok_or_else(|| format!("{}: skip `{}` not ADDR+LEN", s, p))?;
        let a = u64::from_str_radix(a.trim_start_matches("0x"), 16).map_err(|e| format!("{}: {}", s, e))?;
        let l: u64 = l.parse().map_err(|e| format!("{}: {}", s, e))?;
        Ok((a, l))
    }).collect()
}

/// `slc steps ELF SYMBOL... -o STEPS.core [--text TEXT.core]`: the chain
/// line making the functions' decode facts, and the program text
pub fn steps(args: &[String]) -> CResult {
    let (mut out, mut text, mut pos) = (None, None, Vec::new());
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "-o" => out = it.next().cloned(),
            "--text" => text = it.next().cloned(),
            _ => pos.push(a.clone()),
        }
    }
    let usage = "usage: slc steps ELF SYMBOL... -o STEPS.core [--text TEXT.core]";
    let (Some(out), true) = (out, pos.len() >= 2) else { return Err(usage.into()) };
    let elf_path = &pos[0];
    let bytes = std::fs::read(elf_path).map_err(|e| format!("{}: {}", elf_path, e))?;
    let sha = crate::sha256::hex(&bytes);
    let elf = Elf::parse(bytes)?;
    // (the functions exist)
    let fns: Vec<(String, u64, u64)> = pos[1..].iter().map(|n| function(&elf, n).map(|(ns, sym)| (ns.to_string(), sym.value, sym.size))).collect::<R<_>>()?;
    let line = format!(
        "// The decode facts of the functions of {e} (made by the checker:\n// slc/cli/src/steps.rs). Written by `slc steps`.\n\nsteps decode \"{e}\" \"{sha}\" \"{f}\"\n",
        e = elf_path,
        sha = sha,
        f = pos[1..].join(" ")
    );
    std::fs::write(&out, line).map_err(|e| format!("{}: {}", out, e))?;
    println!("{}: the decode facts' line ({} functions)", out, fns.len());
    if let Some(t) = &text {
        exec_segment(&elf)?;
        let line = format!(
            "// The program text of {e}: the functions' code in address order and the\n// bytes between them, each function's code a piece of it (made by the\n// checker: slc/cli/src/steps.rs). Written by `slc steps --text`.\n\ntext program \"{e}\" \"{sha}\" \"{f}\"\n",
            e = elf_path,
            sha = sha,
            f = pos[1..].join(" ")
        );
        std::fs::write(t, line).map_err(|e| format!("{}: {}", t, e))?;
        println!("{}: the program text's line", t);
    }
    Ok(())
}

/// The chain lines `steps NAME "ELF" "SHA256" "SYMBOL .."` and `text ..`:
/// the definitions (made here, in order) and the theorems, by name (a
/// definition's with no sequent)
pub fn directive(env: &mut Env, kw: &str, elf_path: &str, sha: &str, fns: &[String]) -> R<Vec<(String, Option<Seq>)>> {
    let bytes = std::fs::read(elf_path).map_err(|e| format!("{}: {}", elf_path, e))?;
    let h = crate::sha256::hex(&bytes);
    if h != sha {
        return Err(format!("{}: its sha256 is {}, not {} (rebuilt: scripts/check.sh gen)", elf_path, h, sha));
    }
    let elf = Elf::parse(bytes)?;
    match kw {
        "steps" => decode_facts(env, &elf, fns),
        "text" => text_facts(env, &elf, fns),
        _ => Err(format!("`{}`: not a line of a binary", kw)),
    }
}

/// The proving context of a line (`Cx`): its variables (`names`, then
/// the placeholders `ph_a`, `ph_b`, `ph_c`)
fn context(env: &mut Env, names: &[&str]) -> R<(Cx, Vec<VarId>)> {
    let api = Api::new(env, Vec::new()).map_err(ke)?;
    let vs: Vec<VarId> = names.iter().map(|n| env.new_var(n, 0)).collect();
    let ph: Vec<VarId> = ["ph_a", "ph_b", "ph_c"].iter().map(|n| env.new_var(n, 0)).collect();
    let mut scope: Vec<(String, VarId)> = names.iter().zip(&vs).map(|(n, v)| (n.to_string(), *v)).collect();
    scope.extend(["ph_a", "ph_b", "ph_c"].iter().zip(&ph).map(|(n, v)| (n.to_string(), *v)));
    Ok((Cx { api, m: vs[0], o: vs[1], ph, scope }, vs))
}

/// `t`'s arguments if it is `f(..)` of `n` arguments
fn args_of(t: &Term, n: usize) -> R<Vec<Term>> {
    match t.node() {
        Node::App(_, a) if a.len() == n => Ok(a.to_vec()),
        _ => Err("an application expected".into()),
    }
}

/// The executable segment: its address and its bytes in the file (the
/// claim's `prog_base`, `prog_code`: slc/cli/src/claim.rs)
fn exec_segment(elf: &Elf) -> R<(u64, Vec<u8>)> {
    let exec: Vec<_> = elf.segments.iter().filter(|s| s.flags & 1 != 0 && s.filesz > 0).collect();
    let [xs] = exec.as_slice() else { return Err(format!("{} executable segments, expected one", exec.len())) };
    let b = elf.bytes_at(xs.vaddr, xs.filesz as usize).ok_or("the executable segment's bytes")?.to_vec();
    Ok((xs.vaddr, b))
}

/// The `text` line: the program text `text.code` (the executable
/// segment's bytes, as the claim's `prog_code`) and per function
/// `F.in_text`: `all vm st. abi.loaded(vm, TB, text.code, st) ->
/// abi.loaded(vm, A, F.code, st)` -- F's code (the `steps` line's
/// `F.code`) the text's bytes at its offset (`tr.loaded_slice`, the bytes
/// compared by evaluation)
fn text_facts(env: &mut Env, elf: &Elf, fns: &[String]) -> R<Vec<(String, Option<Seq>)>> {
    let fns: Vec<(String, u64, u64)> = fns.iter().map(|n| function(elf, n).map(|(ns, sym)| (ns.to_string(), sym.value, sym.size))).collect::<R<_>>()?;
    let (tb, seg) = exec_segment(elf)?;
    let (cx, vs) = context(env, &["vm", "st"])?;
    let lg = &cx.api.lg;
    let mut out = Vec::new();
    let segt = Term::bytes(&seg);
    let body = cx.tm(env, "bytes_seq(ph_a)", &[&segt])?;
    env.define("text.code", Vec::new(), body).map_err(ke)?;
    out.push(("text.code".to_string(), None));
    let code_sym = defined_sym(env, "text.code").map_err(ke)?;
    let h = cx.assume(env, &format!("abi.loaded(vm, {}, text.code(), st)", tb))?;
    let hb = cx.tm(env, &format!("abi.loaded(vm, {}, bytes_seq(ph_a), st)", tb), &[&segt])?;
    let hb = Seq::conv(env, &h, &hb, &[code_sym]).map_err(ke)?;
    let slice = cx.fact(env, "tr.loaded_slice")?;
    let (vm, st) = (Term::var(vs[0], vec![]), Term::var(vs[1], vec![]));
    let mut done = std::collections::HashSet::new();
    for (ns, a, _) in &fns {
        if !done.insert(ns.clone()) {
            continue;
        }
        let name = format!("{}.code", ns);
        let fsym = defined_sym(env, &name).map_err(ke)?;
        let eq = Seq::def_eq(env, fsym).map_err(ke)?;
        let c = args_of(&args_of(eq.concl(), 2)?[1], 1)?[0].clone();
        let off = a.checked_sub(tb).ok_or_else(|| format!("{} before the executable segment", ns))?;
        let (tbt, offt) = (cx.term(env, &tb.to_string())?, cx.term(env, &off.to_string())?);
        let mut s = cx.all_elim(env, &slice, &[vm.clone(), tbt, segt.clone(), c.clone(), offt, st.clone()])?;
        // the premises on concrete data, by evaluation: the numbers, the
        // lengths, and F's bytes the text's at the offset
        for _ in 0..6 {
            let p = args_of(s.concl(), 2)?[0].clone();
            let pf = Seq::eval_goal(env, lg, &[], &p).map_err(|e| format!("{}: {}", ns, e.0))?;
            s = Seq::mp(env, &s, &pf).map_err(ke)?;
        }
        let s = Seq::mp(env, &s, &hb).map_err(ke)?;
        // `loaded(vm, A, F.code(), st)`
        let goal = cx.term(env, &format!("abi.loaded(vm, {}, {}(), st)", a, name))?;
        let r = cx.simp_goal(env, &[&s, &eq], &goal, &[])?;
        let r = r.discharge(env, h.concl()).map_err(ke)?;
        let r = Seq::gen(env, lg, &Seq::gen(env, lg, &r, vs[1]).map_err(ke)?, vs[0]).map_err(ke)?;
        out.push((format!("{}.in_text", ns), Some(r)));
    }
    Ok(out)
}

/// The `steps` line's facts
fn decode_facts(env: &mut Env, elf: &Elf, fns: &[String]) -> R<Vec<(String, Option<Seq>)>> {
    // (STEPS_TRACE: the phases' times)
    let t0 = std::time::Instant::now();
    let phase = |m: &str| {
        if std::env::var("STEPS_TRACE").is_ok() {
            eprintln!("steps {} [{:.2}]", m, t0.elapsed().as_secs_f64());
        }
    };
    // instruction boundaries (untrusted: the interpreter's decoder)
    let mut sm = sl_syntax::SourceMap::default();
    let g = load_spec_globals(&mut sm)?;
    let interp = Interp::new(&g, "x86")?;
    phase("decoder loaded");
    // per function: name, address, code, its instructions (address, encoding)
    let mut funs: Vec<(String, u64, Vec<u8>, Vec<(u64, Vec<u8>)>)> = Vec::new();
    // encoding -> the 15 bytes at its first address
    let mut encodings: BTreeMap<Vec<u8>, Vec<u8>> = BTreeMap::new();
    let (mut n_insns, mut n_cached) = (0usize, 0usize);
    for s in fns {
        let (ns, sym) = function(&elf, s)?;
        let code = elf.bytes_at(sym.value, sym.size as usize).ok_or_else(|| format!("{}: no bytes", s))?.to_vec();
        let skip = skips(s)?;
        let mut insns = Vec::new();
        let mut addr = sym.value;
        while addr < sym.value + sym.size {
            // (an instruction the model's decoder has not: no fact, the C1
            // of a run reaching it fails there)
            if let Some(&(_, l)) = skip.iter().find(|(a, _)| *a == addr) {
                addr += l;
                continue;
            }
            let window = elf.bytes_at(addr, 15).unwrap_or(&[]).to_vec();
            // (an encoding met before starting the window: its length -- an
            // instruction's length is fixed by its own bytes; one candidate
            // only, else the interpreter decides. Only a boundary: the
            // kernel proves each encoding's step itself)
            let known: Vec<usize> = (1..=window.len()).filter(|&l| encodings.contains_key(&window[..l])).collect();
            let len = match known[..] {
                [l] => {
                    n_cached += 1;
                    l
                }
                _ => interp.decode(&window).first().map(|m| m.len).ok_or_else(|| format!("{:x}: not decoded", addr))?,
            };
            n_insns += 1;
            encodings.entry(window[..len].to_vec()).or_insert_with(|| window.clone());
            insns.push((addr, window[..len].to_vec()));
            addr += len as u64;
        }
        funs.push((ns.to_string(), sym.value, code, insns));
    }
    phase(&format!("decoded: {} encodings, {} instructions ({} by a known encoding)", encodings.len(), n_insns, n_cached));
    let (cx, _) = context(env, &["m", "o"])?;
    let dec = cx.term(env, &format!("x86_64_linux.x86.decode({})", DECODED))?;
    // (SLC_DECODE_PREP=kernel: decode the rows alone, decode_g their guarded
    // form -- proven equivalent once here; each encoding then evaluated on
    // decode_g, its members carried over to decode)
    let prep = if env.sym_by_name.contains_key("x86_64_linux.x86.decode_g") {
        let t1 = std::time::Instant::now();
        let eq = cx.decode_eq(env)?;
        phase(&format!("decode prepared (kernel), {:.2} s", t1.elapsed().as_secs_f64()));
        Some((eq, cx.term(env, &format!("x86_64_linux.x86.decode_g({})", DECODED))?))
    } else {
        None
    };
    let mut out = Vec::new();
    let mut steps: BTreeMap<Vec<u8>, Step> = BTreeMap::new();
    let mut names = std::collections::HashSet::new();
    for (enc, window) in &encodings {
        match cx.step(env, &dec, prep.as_ref(), enc, window) {
            Ok(st) => {
                if names.insert(st.name.clone()) {
                    out.push((st.name.clone(), Some(st.seq.clone())));
                }
                steps.insert(enc.clone(), st);
            }
            // (no theorem: the C1 of a function with it fails there)
            Err(e) => eprintln!("steps: no theorem for {}: {}", hex(enc), e),
        }
        phase(&format!("step {}", hex(enc)));
    }
    // per function: its code, and for each instruction what a step from it
    // does (`at_`)
    for (ns, base, code, insns) in &funs {
        let name = format!("{}.code", ns);
        let body = cx.tm(env, "bytes_seq(ph_a)", &[&Term::bytes(code)])?;
        env.define(&name, Vec::new(), body).map_err(ke)?;
        out.push((name, None));
        for (addr, enc) in insns {
            if let Some(st) = steps.get(enc) {
                out.push((format!("{}.at_{:x}", ns, addr), Some(cx.at(env, ns, *base, *addr, st)?)));
            }
        }
        phase(&format!("{}: at", ns));
    }
    Ok(out)
}

/// An encoding's step theorem: its name, the bytes it reads (offset,
/// value), the decoded instruction (length, term), its sequent
struct Step {
    name: String,
    bytes: Vec<(usize, u8)>,
    len: Term,
    insn: Term,
    seq: Seq,
}

/// The proving context: the machine state `m`, the outcome `o`, and the
/// placeholders `ph_a`, `ph_b`, `ph_c` of the statements parsed (terms
/// put in their place)
struct Cx {
    api: Api,
    m: VarId,
    o: VarId,
    ph: Vec<VarId>,
    scope: Vec<(String, VarId)>,
}

impl Cx {
    fn term(&self, env: &mut Env, s: &str) -> R<Term> {
        parse_term(env, s, &self.scope).map_err(ke)
    }

    /// `s` parsed, its placeholders `ph_a`, .. replaced by `ts`
    fn tm(&self, env: &mut Env, s: &str, ts: &[&Term]) -> R<Term> {
        let mut t = self.term(env, s)?;
        for (v, x) in self.ph.iter().zip(ts) {
            t = env.subst_var_m(&t, *v, x);
        }
        Ok(t)
    }

    /// `s` parsed, assumed
    fn assume(&self, env: &mut Env, s: &str) -> R<Seq> {
        let t = self.term(env, s)?;
        Seq::assume(env, t).map_err(ke)
    }

    /// a fact by name
    fn fact(&self, env: &Env, n: &str) -> R<Seq> {
        self.api.fact(env, n).map_err(ke)
    }

    /// `expand(s, D..)`: s with the definitions D unfolded
    fn expand(&self, env: &Env, s: &Seq, ds: &[&str]) -> R<Seq> {
        let syms = ds.iter().map(|d| defined_sym(env, d)).collect::<Result<Vec<_>, _>>().map_err(ke)?;
        let g = unfold_all(env, s.concl(), &syms);
        Seq::conv(env, s, &g, &syms).map_err(ke)
    }

    fn all_elim(&self, env: &Env, s: &Seq, ts: &[Term]) -> R<Seq> {
        let mut s = s.clone();
        for t in ts {
            s = Seq::all_elim(env, &self.api.lg, &s, t).map_err(ke)?;
        }
        Ok(s)
    }

    fn simp_goal(&self, env: &Env, facts: &[&Seq], goal: &Term, keep: &[&str]) -> R<Seq> {
        let keep = keep.iter().map(|d| defined_sym(env, d)).collect::<Result<Vec<_>, _>>().map_err(ke)?;
        Seq::simp_goal(env, &self.api.lg, facts, goal, &[], &keep).map_err(ke)
    }

    /// The step theorem of an encoding (`window`: the 15 bytes at one of
    /// its addresses):
    /// `byte_0 = v_0 -> .. -> runs(step(), m, o) -> runs(exec_insn(len, insn), m, o)`
    fn step(&self, env: &mut Env, dec: &Term, prep: Option<&(Seq, Term)>, enc: &[u8], window: &[u8]) -> R<Step> {
        let lg = &self.api.lg;
        // (the set evaluated: decode_g under SLC_DECODE_PREP=kernel)
        let evald = prep.map_or(dec, |p| &p.1);
        // the members of the decoding, from the instruction's own bytes,
        // else all 15
        let mut known = None;
        let mut err = String::new();
        for n in [enc.len(), window.len()] {
            let hs: Vec<Seq> = (0..n).map(|k| self.term(env, &byte_eq(k, window[k])).and_then(|t| Seq::assume(env, t).map_err(ke))).collect::<R<_>>()?;
            let refs: Vec<&Seq> = hs.iter().collect();
            match Seq::members(env, lg, evald, &refs) {
                Ok(d) => {
                    known = Some((d, hs));
                    break;
                }
                Err(e) => err = e.0,
            }
        }
        let Some((d, hs)) = known else { return Err(err) };
        let d = match prep {
            Some((eq, _)) => self.to_decode(env, eq, d, dec)?,
            None => d,
        };
        let c = one_member(d.concl()).ok_or("not exactly one decoding")?;
        let (len, insn) = match c.node() {
            Node::App(_, p) if p.len() == 2 => (p[0].clone(), p[1].clone()),
            _ => return Err("decoding not a pair".into()),
        };
        // the bytes read: the hypotheses `members` kept
        let bytes: Vec<(usize, u8)> = hs.iter().enumerate().filter(|(_, h)| d.hyps().contains(h.concl())).map(|(k, _)| (k, window[k])).collect();
        let name = format!("x86.step_{}", bytes.iter().map(|(_, b)| format!("{:02x}", b)).collect::<String>());
        let h = self.assume(env, "runs(x86_64_linux.step(), m, o)")?;
        // d1: all x. x in dec -> x = c
        let x = env.new_var("x", 0);
        let xv = Term::var(x, vec![]);
        let dx = self.expand(env, &self.all_elim(env, &d, &[xv.clone()])?, &["iff"])?;
        let g1 = self.tm(env, "ph_a in ph_b -> ph_a = ph_c", &[&xv, dec, &c])?;
        let d1 = Seq::gen(env, lg, &self.simp_goal(env, &[&dx], &g1, &[])?, x).map_err(ke)?;
        // dc: c in dec
        let in_c = self.tm(env, "ph_a in ph_b", &[&c, dec])?;
        let dcx = self.expand(env, &self.all_elim(env, &d, &[c.clone()])?, &["iff"])?;
        let dc = self.simp_goal(env, &[&dcx], &in_c, &[])?;
        // ty: c in cart(omega, univ(1))
        let cty = self.tm(env, "ph_a in cart(omega, univ(1))", &[&c])?;
        let ty = Seq::eval_goal(env, lg, &[], &cty).map_err(ke)?;
        // runs(exec_insn(len, insn), m, o): x86.step_one at this decoding
        // (proven once, proofs/x86.core -- not the step unfolded per encoding)
        let (mt, ot) = (self.term(env, "m")?, self.term(env, "o")?);
        let one = self.api.inst(env, self.fact(env, "x86.step_one")?, &[("m", mt), ("o", ot), ("n", len.clone()), ("i", insn.clone())]).map_err(ke)?;
        let mut s = one;
        for p in [&h, &d1, &dc, &ty] {
            s = Seq::mp(env, &s, p).map_err(ke)?;
        }
        s = s.discharge(env, h.concl()).map_err(ke)?;
        for &(k, _) in bytes.iter().rev() {
            s = s.discharge(env, hs[k].concl()).map_err(ke)?;
        }
        Ok(Step { name, bytes, len, insn, seq: s })
    }

    /// (SLC_DECODE_PREP=kernel) `all b z. A(b, z) <-> G(b, z)`: decode's
    /// condition (its rows' alternatives) and decode_g's (each led by its
    /// guard `x86.opc(b, K)`), proven once -- per guarded row, its theorem
    /// (proofs/x86_decode.core: the row's shape's lemma, by matching; the
    /// decoder before its byte keeping the position), then the two
    /// disjunctions by taut
    fn decode_eq(&self, env: &mut Env) -> R<Seq> {
        let sym = |env: &Env, n: &str| env.sym_by_name.get(n).copied().ok_or_else(|| format!("no symbol `{}`", n));
        let (dsym, gsym) = (defined_sym(env, "x86_64_linux.x86.decode").map_err(ke)?, defined_sym(env, "x86_64_linux.x86.decode_g").map_err(ke)?);
        let (or, and, ex, runs, ok, iff) = (sym(env, "or")?, sym(env, "and")?, sym(env, "ex")?, sym(env, "runs")?, sym(env, "ok")?, sym(env, "iff")?);
        let opc = sym(env, "x86_64_linux.x86.opc")?;
        let b = env.new_var("b", 0);
        let z = env.new_var("z", 0);
        let (bt, zt) = (Term::var(b, vec![]), Term::var(z, vec![]));
        // (a selection's condition at b, z)
        let cond = |env: &Env, s| -> R<Term> {
            let t = unfold_all(env, &Term::app(s, vec![bt.clone()]), &[s]);
            match t.node() {
                Node::App(_, a) if a.len() == 2 => Ok(a[1].instantiate_params(std::slice::from_ref(&zt), &env.binders_fn())),
                _ => Err("decode: not a selection".into()),
            }
        };
        let (ca, cg) = (cond(env, dsym)?, cond(env, gsym)?);
        fn disjuncts(t: &Term, or: u32, out: &mut Vec<Term>) {
            match t.node() {
                Node::App(o, a) if *o == or => {
                    disjuncts(&a[0], or, out);
                    disjuncts(&a[1], or, out);
                }
                _ => out.push(t.clone()),
            }
        }
        let lg = &self.api.lg;
        let alt_guard = self.api.inst(env, self.fact(env, "dec.alt_guard")?, &[("b", bt.clone())]).map_err(ke)?;
        // (alternative by alternative, the two disjunctions alike in shape:
        // dec.or_cong at each `||`; at a leaf the same alternative, or led by
        // its guard -- dec.guard_iff by the row's theorem)
        let s = self.or_iff(env, &ca, &cg, or, and, ex, runs, ok, opc, &alt_guard)?;
        let _ = (iff, disjuncts as fn(&Term, u32, &mut Vec<Term>));
        let s = Seq::gen(env, lg, &s, z).map_err(ke)?;
        // (the members of the two, folded: `all x. x in decode(b) <-> x in
        // decode_g(b)` -- what each use instantiates)
        let space = match unfold_all(env, &Term::app(dsym, vec![bt.clone()]), &[dsym]).node() {
            Node::App(_, a) if a.len() == 2 => a[0].clone(),
            _ => return Err("decode: not a selection".into()),
        };
        let sc = self.api.inst(env, self.fact(env, "dec.sel_cong")?, &[("S", space)]).map_err(ke)?;
        let sc = self.api.apply(env, sc, vec![A::G(G::By(s))], None).map_err(ke)?;
        let folded = self.tm(env, "all x. x in x86_64_linux.x86.decode(ph_a) <-> x in x86_64_linux.x86.decode_g(ph_a)", &[&bt])?;
        let s = Seq::conv(env, &sc, &folded, &[dsym, gsym]).map_err(ke)?;
        Seq::gen(env, lg, &s, b).map_err(ke)
    }

    /// `a <-> g`: decode's condition and decode_g's, or their parts alike
    #[allow(clippy::too_many_arguments)]
    fn or_iff(&self, env: &mut Env, a: &Term, g: &Term, or: u32, and: u32, ex: u32, runs: u32, ok: u32, opc: u32, alt_guard: &Seq) -> R<Seq> {
        if let (Node::App(o1, x), Node::App(o2, y)) = (a.node(), g.node()) {
            if *o1 == or && *o2 == or {
                let l = self.or_iff(env, &x[0], &y[0], or, and, ex, runs, ok, opc, alt_guard)?;
                let r = self.or_iff(env, &x[1], &y[1], or, and, ex, runs, ok, opc, alt_guard)?;
                return self.api.apply(env, self.fact(env, "dec.or_cong")?, vec![A::G(G::By(l)), A::G(G::By(r))], None).map_err(ke);
            }
        }
        if a == g {
            return self.api.inst(env, self.fact(env, "dec.iff_refl")?, &[("a", a.clone())]).map_err(ke);
        }
        let f = self.guard_fact(env, g, and, ex, runs, ok, opc, alt_guard, or)?;
        self.api.apply(env, self.fact(env, "dec.guard_iff")?, vec![A::G(G::By(f))], None).map_err(ke)
    }

    /// a guarded alternative `opc(b, K) && ALT`: `ALT -> opc(b, K)`, by the
    /// row's theorem
    #[allow(clippy::too_many_arguments)]
    fn guard_fact(&self, env: &mut Env, g: &Term, and: u32, ex: u32, runs: u32, ok: u32, opc: u32, alt_guard: &Seq, or: u32) -> R<Seq> {
        {
            let Node::App(a0, ga) = g.node() else { return Err("decode_g: an alternative not an application".into()) };
            if *a0 != and || !matches!(ga[0].node(), Node::App(o, _) if *o == opc) {
                return Err("decode_g: an alternative differs from decode's but has no guard".into());
            }
            let alt = &ga[1];
            // (the row: `ex st v. runs(ROW, ..) && ..`)
            let row = (|| {
                let Node::App(e1, x) = alt.node() else { return None };
                let Node::App(e2, y) = x[0].node() else { return None };
                let Node::App(a, w) = y[0].node() else { return None };
                let Node::App(r, u) = w[0].node() else { return None };
                let Node::App(rs, _) = u[0].node() else { return None };
                (*e1 == ex && *e2 == ex && *a == and && *r == runs).then_some(*rs)
            })()
            .ok_or("decode_g: an alternative not a row's run")?;
            let rt = self.row_thm(env, row, runs, ok, or)?;
            let ha = Seq::assume(env, alt.clone()).map_err(ke)?;
            let f = self.api.apply(env, alt_guard.clone(), vec![A::G(G::By(rt)), A::G(G::By(ha))], None).map_err(|e| format!("{}: {}", env.syms[row as usize].name, e.0))?;
            f.discharge(env, alt).map_err(ke)
        }
    }

    /// a row's theorem: `all s st v. runs(ROW, s, ok(st, v)) ->
    /// dec.opc_of(prefixes, s, K)` -- its top bind (dec.top), the
    /// continuation walked to the byte test (`byte_of`)
    fn row_thm(&self, env: &mut Env, row: u32, runs: u32, ok: u32, or: u32) -> R<Seq> {
        let lg = &self.api.lg;
        let name = env.syms[row as usize].name.clone();
        let (s, st, v) = (env.new_var("s", 0), env.new_var("st", 0), env.new_var("v", 0));
        let (s_t, o_t) = (Term::var(s, vec![]), Term::app(ok, vec![Term::var(st, vec![]), Term::var(v, vec![])]));
        let rt = Term::app(runs, vec![Term::app(row, vec![]), s_t.clone(), o_t.clone()]);
        let h = Seq::assume(env, rt).map_err(ke)?;
        let hx = self.api.expand(env, h.clone(), &[row]).map_err(ke)?;
        // mkprog(x0 x1. bind_rel(p, x0, x2 x3. K, ..)) at s, ok(st, v): K at
        // a fresh state s1 and value u
        let body = unfold_all(env, &Term::app(row, vec![]), &[row]);
        let Node::App(_, mk) = body.node() else { return Err(format!("{}: not a program", name)) };
        let top = mk[0].instantiate_params(&[s_t, o_t], &env.binders_fn());
        let k = self.bind_parts(env, &top).ok_or_else(|| format!("{}: not a bind", name))?[2].clone();
        let p = self.cont_proof(env, &k, or).map_err(|e| format!("{}: {}", name, e))?;
        let r = self.api.apply(env, self.fact(env, "dec.top")?, vec![A::G(G::By(hx)), A::G(G::By(p))], None).map_err(|e| format!("{} by dec.top: {}", name, e.0))?;
        let mut r = r.discharge(env, h.concl()).map_err(ke)?;
        for x in [v, st, s] {
            r = Seq::gen(env, lg, &r, x).map_err(ke)?;
        }
        Ok(r)
    }

    /// `bind_rel(q, s, k, x, d)`'s five arguments
    fn bind_parts(&self, env: &Env, t: &Term) -> Option<Vec<Term>> {
        match t.node() {
            Node::App(f, a) if env.syms[*f as usize].name == "bind_rel" && a.len() == 5 => Some(a.to_vec()),
            _ => None,
        }
    }

    /// a bind's continuation (its body, binding the state and the value):
    /// `all s1 u. K(s1, u) -> byte(s1) = k`
    fn cont_proof(&self, env: &mut Env, k: &Term, or: u32) -> R<Seq> {
        let lg = &self.api.lg;
        let (s1, u) = (env.new_var("s1", 0), env.new_var("u", 0));
        let kc = k.instantiate_params(&[Term::var(s1, vec![]), Term::var(u, vec![])], &env.binders_fn());
        let r = self.byte_of(env, &kc, or)?;
        let mut r = r.discharge(env, &kc).map_err(ke)?;
        for x in [u, s1] {
            r = Seq::gen(env, lg, &r, x).map_err(ke)?;
        }
        Ok(r)
    }

    /// `c` (a row's continuation at a state σ, its outcome ok) proves the
    /// byte at σ: the hypothesis c, `byte(σ) = k` -- the test itself
    /// (dec.test_ok), a let (opened), or a bind of a decoder that keeps the
    /// position (dec.bind_keeps, its continuation walked)
    fn byte_of(&self, env: &mut Env, c: &Term, or: u32) -> R<Seq> {
        let h = Seq::assume(env, c.clone()).map_err(ke)?;
        let head = match c.node() {
            Node::App(f, _) => *f,
            _ => return Err("a continuation not an application".into()),
        };
        if head == or {
            return self.api.apply(env, self.fact(env, "dec.test_ok")?, vec![A::G(G::By(h))], None).map_err(|e| format!("the byte test: {}", e.0));
        }
        let hname = env.syms[head as usize].name.clone();
        if hname == "letin" {
            let h2 = self.api.expand(env, h, &[head]).map_err(ke)?;
            let inner = self.byte_of(env, &h2.concl().clone(), or)?;
            let imp = inner.discharge(env, h2.concl()).map_err(ke)?;
            return Seq::mp(env, &imp, &h2).map_err(ke);
        }
        let a = self.bind_parts(env, c).ok_or_else(|| format!("before the byte test: `{}`, not a bind or a let", hname))?;
        let q = match a[0].node() {
            Node::App(q, x) if x.is_empty() => env.syms[*q as usize].name.rsplit('.').next().unwrap_or_default().to_string(),
            _ => return Err("before the byte test: a decoder not a constant".into()),
        };
        let keeps = self.fact(env, &format!("dec.keeps_{}", q)).map_err(|_| format!("before the byte test: `{}` (no dec.keeps_{} theorem)", q, q))?;
        let p = self.cont_proof(env, &a[2], or)?;
        self.api.apply(env, self.fact(env, "dec.bind_keeps")?, vec![A::G(G::By(keeps)), A::G(G::By(p)), A::G(G::By(h))], None).map_err(|e| format!("after `{}`: {}", q, e.0))
    }

    /// (SLC_DECODE_PREP=kernel) `d`, the members of decode_g(D), as those of
    /// decode(D): by the conditions' equivalence `eq` at D
    fn to_decode(&self, env: &mut Env, eq: &Seq, d: Seq, dec: &Term) -> R<Seq> {
        let darg = match dec.node() {
            Node::App(_, a) if a.len() == 1 => a[0].clone(),
            _ => return Err("decode: not applied".into()),
        };
        let e = self.all_elim(env, eq, &[darg])?;
        self.api.apply(env, self.fact(env, "dec.members_conv")?, vec![A::G(G::By(e)), A::G(G::By(d))], None).map_err(ke)
    }

    /// `NS.at_ADDR`: `all m o. runs(step(), m, o) -> abi.code_at(m.vm, BASE,
    /// NS.code()) -> m.rip = ADDR -> runs(exec_body(len, insn), m, o)`
    fn at(&self, env: &mut Env, ns: &str, base: u64, addr: u64, st: &Step) -> R<Seq> {
        let lg = &self.api.lg;
        let h = self.assume(env, "runs(x86_64_linux.step(), m, o)")?;
        let hc = self.assume(env, &format!("abi.code_at(app(m, \"vm\"), {}, {}.code())", base, ns))?;
        let hr = self.assume(env, &format!("app(m, \"rip\") = {}", addr))?;
        let code = format!("{}.code", ns);
        let c = self.expand(env, &self.expand(env, &hc, &["abi.code_at"])?, &[&code])?;
        // the step theorem's byte premises
        let mut e = st.seq.clone();
        for &(k, v) in &st.bytes {
            let off = self.term(env, &(addr - base + k as u64).to_string())?;
            let b = Seq::simp(env, lg, &self.all_elim(env, &c, &[off])?);
            let bk = self.term(env, &byte_eq(k, v))?;
            let hb = self.simp_goal(env, &[&hr, &b], &bk, &[])?;
            e = Seq::mp(env, &e, &hb).map_err(ke)?;
        }
        let e = Seq::mp(env, &e, &h).map_err(ke)?;
        // the fetch succeeds
        let vm = self.term(env, "app(m, \"vm\")")?;
        let nsc = self.term(env, &format!("{}()", code))?;
        let (tb, ta) = (self.term(env, &base.to_string())?, self.term(env, &addr.to_string())?);
        let cf0 = self.all_elim(env, &self.fact(env, "x86.code_fetch")?, &[vm, tb, nsc, ta, st.len.clone()])?;
        let cf0 = self.expand(env, &cf0, &[&code])?;
        let hcx = self.expand(env, &hc, &[&code])?;
        let cfg = self.tm(
            env,
            &format!("all i. i in omega -> int_lt(i, ph_a) -> x86_64_linux.fetchable(app(m, \"vm\"), bits_add(64, {}, bits_of_int(64, i)))", addr),
            &[&st.len],
        )?;
        let cf = self.simp_goal(env, &[&cf0, &hcx], &cfg, &[])?;
        let tf = self.fact(env, "x86.touch_range_fetch")?;
        let goal = self.tm(env, "runs(x86_64_linux.exec_body(ph_a, ph_b), m, o)", &[&st.len, &st.insn])?;
        let mut s = self.simp_goal(env, &[&e, &hr, &cf, &tf], &goal, &["x86_64_linux.step", "x86_64_linux.exec_body", "x86_64_linux.touch_range"])?;
        for a in [&hr, &hc, &h] {
            s = s.discharge(env, a.concl()).map_err(ke)?;
        }
        s = Seq::gen(env, lg, &s, self.o).map_err(ke)?;
        Seq::gen(env, lg, &s, self.m).map_err(ke)
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect::<Vec<_>>().join(" ")
}

/// `all x. x in S <-> x = c` -> c
fn one_member(fact: &Term) -> Option<Term> {
    let Node::App(_, a) = fact.node() else { return None };
    let Node::App(_, iff) = a[0].node() else { return None };
    let Node::App(_, eq) = iff.get(1)?.node() else { return None };
    match eq.get(1) {
        Some(c) if matches!(eq[0].node(), Node::BVar(0)) => Some(c.clone()),
        _ => None,
    }
}
