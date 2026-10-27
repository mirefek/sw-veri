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
use sl_proof::api::Api;
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
    for s in fns {
        let (ns, sym) = function(&elf, s)?;
        let code = elf.bytes_at(sym.value, sym.size as usize).ok_or_else(|| format!("{}: no bytes", s))?.to_vec();
        let mut insns = Vec::new();
        let mut addr = sym.value;
        while addr < sym.value + sym.size {
            let window = elf.bytes_at(addr, 15).unwrap_or(&[]).to_vec();
            let len = interp.decode(&window).first().map(|m| m.len).ok_or_else(|| format!("{:x}: not decoded", addr))?;
            encodings.entry(window[..len].to_vec()).or_insert_with(|| window.clone());
            insns.push((addr, window[..len].to_vec()));
            addr += len as u64;
        }
        funs.push((ns.to_string(), sym.value, code, insns));
    }
    phase(&format!("decoded: {} encodings", encodings.len()));
    let (cx, _) = context(env, &["m", "o"])?;
    let dec = cx.term(env, &format!("x86_64_linux.x86.decode({})", DECODED))?;
    let mut out = Vec::new();
    let mut steps: BTreeMap<Vec<u8>, Step> = BTreeMap::new();
    let mut names = std::collections::HashSet::new();
    for (enc, window) in &encodings {
        match cx.step(env, &dec, enc, window) {
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
    fn step(&self, env: &mut Env, dec: &Term, enc: &[u8], window: &[u8]) -> R<Step> {
        let lg = &self.api.lg;
        // the members of the decoding, from the instruction's own bytes,
        // else all 15
        let mut known = None;
        let mut err = String::new();
        for n in [enc.len(), window.len()] {
            let hs: Vec<Seq> = (0..n).map(|k| self.term(env, &byte_eq(k, window[k])).and_then(|t| Seq::assume(env, t).map_err(ke))).collect::<R<_>>()?;
            let refs: Vec<&Seq> = hs.iter().collect();
            match Seq::members(env, lg, dec, &refs) {
                Ok(d) => {
                    known = Some((d, hs));
                    break;
                }
                Err(e) => err = e.0,
            }
        }
        let Some((d, hs)) = known else { return Err(err) };
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
        // ne: !(dec = empty)
        let is_empty = self.tm(env, "ph_a = empty", &[dec])?;
        let e = Seq::assume(env, is_empty.clone()).map_err(ke)?;
        let ce = Seq::rewrite(env, &e, &dc).map_err(ke)?;
        let em = self.api.inst(env, self.fact(env, "empty_mem")?, &[("x", c.clone())]).map_err(ke)?;
        let f = self.term(env, "false")?;
        let ne0 = Seq::taut(env, lg, &[&ce, &em], &f).map_err(ke)?.discharge(env, &is_empty).map_err(ke)?;
        let not_empty = self.tm(env, "!(ph_a = empty)", &[dec])?;
        let ne = Seq::taut(env, lg, &[&ne0], &not_empty).map_err(ke)?;
        // ty: c in cart(omega, univ(1))
        let cty = self.tm(env, "ph_a in cart(omega, univ(1))", &[&c])?;
        let ty = Seq::eval_goal(env, lg, &[], &cty).map_err(ke)?;
        // runs(exec_insn(len, insn), m, o)
        let goal = self.tm(env, "runs(x86_64_linux.exec_insn(ph_a, ph_b), m, o)", &[&len, &insn])?;
        let mut s = self.simp_goal(env, &[&h, &d1, &dc, &ne, &ty], &goal, &["x86_64_linux.exec_insn"])?;
        s = s.discharge(env, h.concl()).map_err(ke)?;
        for &(k, _) in bytes.iter().rev() {
            s = s.discharge(env, hs[k].concl()).map_err(ke)?;
        }
        Ok(Step { name, bytes, len, insn, seq: s })
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
