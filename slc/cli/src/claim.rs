//! `slc claim malloc`: the full statement about a libc binary's allocator.

use crate::commands::{parse_all, prelude_text, repo_root, CResult};
use crate::sha256;
use sl_elab::elab::Cx;
use sl_interp::elf::Elf;
use sl_kernel::{syntax, Env, Nat, Term};
use std::path::PathBuf;

/// Data symbols the allocator (and libc code it depends on) owns in musl.
const MUSL_OWNED: &[&str] = &[
    "__malloc_context",
    "__malloc_lock",
    "__malloc_replaced",
    "__aligned_alloc_replaced",
    "__libc",
    "__hwcap",
    "__sysinfo",
    "__stack_chk_guard",
];

/// musl x86_64: offset of `errno_val` in `struct pthread`.
const MUSL_ERRNO_OFFSET: u64 = 0x34;

pub fn claim(args: &[String]) -> CResult {
    if args.first().map(|s| s.as_str()) != Some("malloc") {
        return Err("usage: slc claim malloc --elf ELF [-o OUT.core] [--owned SYM ...] [--program-exits N,..]".into());
    }
    let mut elf_path = None;
    let mut out = None;
    // (the program's claim too: its exit statuses allowed)
    let mut exits: Option<Vec<u64>> = None;
    // (musl's data symbols: owned if present; those given: required)
    let mut owned: Vec<(String, bool)> = MUSL_OWNED.iter().map(|s| (s.to_string(), false)).collect();
    let mut it = args[1..].iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--elf" => elf_path = it.next().cloned(),
            "-o" => out = it.next().map(PathBuf::from),
            "--owned" => owned.push((it.next().ok_or("--owned needs a symbol")?.clone(), true)),
            "--program-exits" => {
                let l = it.next().ok_or("--program-exits needs a list, e.g. 0,1")?;
                let v: Result<Vec<u64>, _> = l.split(',').map(|s| s.trim().parse::<u64>()).collect();
                exits = Some(v.map_err(|_| format!("--program-exits: `{}` is not a list of numbers", l))?);
            }
            other => return Err(format!("unknown argument `{}`", other)),
        }
    }
    let elf_path = elf_path.ok_or("--elf is required")?;
    let out = out.unwrap_or_else(|| PathBuf::from("musl_malloc.core"));
    let bytes = std::fs::read(&elf_path).map_err(|e| format!("{}: {}", elf_path, e))?;
    let elf = Elf::parse(bytes.clone())?;
    let sym = |n: &str| elf.symbol(n).map(|s| s.value).ok_or_else(|| format!("symbol `{}` not found in {}", n, elf_path));
    let (main_at, malloc_at, free_at) = (sym("main")?, sym("malloc")?, sym("free")?);

    // memory the allocator may own at `main`: read-only segments (code,
    // constant tables) + data symbols
    let mut ranges: Vec<(u64, u64, String)> = Vec::new();
    for s in &elf.segments {
        if s.flags & 2 == 0 && s.memsz > 0 {
            let what = if s.flags & 1 != 0 { "executable segment" } else { "read-only segment" };
            ranges.push((s.vaddr, s.vaddr + s.memsz, what.into()));
        }
    }
    for (n, required) in &owned {
        let found: Vec<_> = elf.symbols.iter().filter(|s| &s.name == n && s.size > 0).collect();
        match found.as_slice() {
            [s] => ranges.push((s.value, s.value + s.size, n.clone())),
            [] if !required => eprintln!("note: musl's symbol `{}` not in the binary, skipped", n),
            [] => return Err(format!("owned symbol `{}` not in {}", n, elf_path)),
            _ => return Err(format!("owned symbol `{}`: {} symbols of that name in {}", n, found.len(), elf_path)),
        }
    }

    // elaborate the spec and layers
    let root = repo_root();
    let mut sm = sl_syntax::SourceMap::default();
    let files = parse_all(&[root.join("spec"), root.join("layers")], &mut sm)?;
    let prelude = prelude_text()?;
    let mut el = sl_elab::elaborate(&prelude, files, &sm)?;
    if el.errors() > 0 {
        for d in el.render_diags() {
            eprintln!("{}", d);
        }
        return Err("elaboration failed".into());
    }

    // the statement
    let inv = el.fresh("alloc_inv");
    let own = el.fresh("alloc_owned");
    let errno_fn = {
        let x = el.fresh("u");
        let dom = el.b.app("single", vec![el.b.empty()]);
        el.b.bind_app("fn_build", vec![dom], &[x], &el.b.nat(MUSL_ERRNO_OFFSET))
    };
    el.b.env.define("musl_malloc.errno_offset", vec![], errno_fn).map_err(|e| e.to_string())?;
    let errno_fn = el.b.app("musl_malloc.errno_offset", vec![]);
    // the program as loaded (malloc.sl's `world_ok`): the executable
    // segment's bytes at its address, the static data the claim's STATIC
    let exec: Vec<_> = elf.segments.iter().filter(|s| s.flags & 1 != 0 && s.filesz > 0).collect();
    let [xs] = exec.as_slice() else { return Err(format!("{}: {} executable segments, expected one", elf_path, exec.len())) };
    let (xo, xn) = (xs.offset as usize, xs.filesz as usize);
    let xbytes = bytes.get(xo..xo + xn).ok_or("the executable segment past the file's end")?;
    let mut static_set = el.b.empty();
    for (lo, hi, _) in &ranges {
        let r = el.b.app("int_range", vec![el.b.natn(Nat::from_u64(*lo)), el.b.natn(Nat::from_u64(*hi))]);
        static_set = el.b.app("union2", vec![r, static_set]);
    }
    let unit_fn = |el: &mut sl_elab::Elab, name: &str, t: Term| -> Result<Term, String> {
        let x = el.fresh("u");
        let dom = el.b.app("single", vec![el.b.empty()]);
        let f = el.b.bind_app("fn_build", vec![dom], &[x], &t);
        let full = format!("musl_malloc.{}", name);
        el.b.env.define(&full, vec![], f).map_err(|e| format!("defining `{}`: {}", full, e))?;
        Ok(el.b.app(&full, vec![]))
    };
    let base_t = el.b.natn(Nat::from_u64(xs.vaddr));
    let base_fn = unit_fn(&mut el, "prog_base", base_t)?;
    let code_t = el.b.app("bytes_seq", vec![Term::bytes(xbytes)]);
    let code_fn = unit_fn(&mut el, "prog_code", code_t)?;
    let statics_fn = unit_fn(&mut el, "prog_statics", static_set.clone())?;
    let mut cx = Cx::new("claim_malloc");
    cx.lift.insert("malloc.alloc_inv".into(), el.b.v(inv));
    cx.lift.insert("malloc.alloc_owned".into(), el.b.v(own));
    cx.lift.insert("malloc.errno_offset".into(), errno_fn);
    cx.lift.insert("malloc.prog_base".into(), base_fn);
    cx.lift.insert("malloc.prog_code".into(), code_fn);
    cx.lift.insert("malloc.prog_statics".into(), statics_fn);
    let lift: Vec<String> = vec![
        "malloc.alloc_inv".into(),
        "malloc.alloc_owned".into(),
        "malloc.errno_offset".into(),
        "malloc.prog_base".into(),
        "malloc.prog_code".into(),
        "malloc.prog_statics".into(),
    ];
    let laws = el.laws_of(&cx, &lift, Default::default()).map_err(|d| d.msg)?;
    let i = el.g.find_decl("claim_malloc", "allocator_claim").ok_or("allocator_claim not found")?;
    let sig = el.sig_of(i, "").map_err(|d| d.msg)?;
    // the binary's data, as named constants (proofs refer to them by name)
    let named = |el: &mut sl_elab::Elab, name: &str, t: Term| -> Result<Term, String> {
        let full = format!("musl_malloc.{}", name);
        el.b.env.define(&full, vec![], t).map_err(|e| format!("defining `{}`: {}", full, e))?;
        Ok(el.b.app(&full, vec![]))
    };
    let mut call: Vec<Term> = sig.lift.iter().map(|q| cx.lift[q].clone()).collect();
    let file = el.b.app("bytes_seq", vec![Term::bytes(&bytes)]);
    call.push(named(&mut el, "file", file)?);
    for (n, a) in [("main_at", main_at), ("malloc_at", malloc_at), ("free_at", free_at)] {
        let t = el.b.natn(Nat::from_u64(a));
        call.push(named(&mut el, n, t)?);
    }
    call.push(named(&mut el, "static", static_set)?);
    // addresses of the data symbols, for the proofs
    for (lo, _, n) in &ranges {
        if !n.ends_with("segment") {
            let t = el.b.natn(Nat::from_u64(*lo));
            named(&mut el, &format!("at.{}", n), t)?;
        }
    }
    let body = el.b.app(&sig.core, call);
    let inner = el.b.and(laws, body);
    let statement = el.b.ex(&[inv, own], inner);
    el.claims.push(("musl_malloc".into(), statement));
    // the program's claim (layers/claim_program.sl): every run that ends
    // exits with one of the statuses, or dies of a stack overflow
    if let Some(exits) = &exits {
        let mut set = el.b.empty();
        for x in exits.iter().rev() {
            set = el.b.app("insert", vec![el.b.nat(*x), set]);
        }
        let set = named(&mut el, "exits", set)?;
        let file = el.b.app("musl_malloc.file", vec![]);
        let st = el.b.app("claim_program.program_ok", vec![file, set]);
        el.claims.push(("musl_program".into(), st));
    }

    // re-check with the kernel from the text, then write
    let text = el.core_text();
    let mut env = Env::new();
    syntax::load(&mut env, &prelude, true).map_err(|e| format!("prelude: {}", e))?;
    let rep = syntax::load(&mut env, &text, false).map_err(|e| format!("kernel rejected the claim text: {}", e))?;
    std::fs::write(&out, &text).map_err(|e| e.to_string())?;
    println!("wrote {} ({} bytes): {} definitions, claims: {}", out.display(), text.len(), rep.defs, rep.claims.join(", "));
    println!("kernel check: ok (definitions conservative, claims closed, no axioms outside the prelude)");

    // human-readable summary of everything the claim rests on
    let summary = summary(&root, &prelude, &elf_path, &bytes, &elf, (main_at, malloc_at, free_at), &ranges, exits.as_deref(), &env, &sm, &el);
    let spath = out.with_extension("summary.txt");
    std::fs::write(&spath, &summary).map_err(|e| e.to_string())?;
    println!("wrote {}", spath.display());
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn summary(
    root: &std::path::Path,
    prelude: &str,
    elf_path: &str,
    bytes: &[u8],
    elf: &Elf,
    addrs: (u64, u64, u64),
    ranges: &[(u64, u64, String)],
    exits: Option<&[u64]>,
    env: &Env,
    sm: &sl_syntax::SourceMap,
    el: &sl_elab::Elab,
) -> String {
    let mut s = String::new();
    let rel = |p: &std::path::Path| p.strip_prefix(root).unwrap_or(p).display().to_string();
    s.push_str("CLAIM musl_malloc\n================\n\n");
    s.push_str("Statement (in the logic of core/prelude.core; full text in the .core file):\n\n");
    // (the laws as declared in layers/malloc.sl)
    let laws: Vec<String> = sm
        .files
        .iter()
        .filter(|(p, _)| rel(p) == "layers/malloc.sl")
        .flat_map(|(_, t)| t.lines().filter_map(|l| l.strip_prefix("law ")).map(|l| l.split('(').next().unwrap_or("").trim().to_string()).collect::<Vec<_>>())
        .collect();
    s.push_str("  ex alloc_inv, alloc_owned.\n");
    s.push_str(&format!("    laws(alloc_inv, alloc_owned)                        -- layers/malloc.sl: {}\n", laws.join(", ")));
    s.push_str("    && init_at_main(FILE, main, STATIC)                 -- invariant holds, no blocks, when main starts\n");
    s.push_str("                                                           (for runs started without privileges:\n");
    s.push_str("                                                           claim_malloc.unprivileged)\n");
    s.push_str("    && implements(malloc) && implements(free)            -- layers/abi.sl, layers/malloc.sl\n\n");
    if let Some(x) = exits {
        let l: Vec<String> = x.iter().map(|v| v.to_string()).collect();
        s.push_str("CLAIM musl_program\n==================\n\n");
        s.push_str(&format!("  program_ok(FILE, {{{}}})                              -- layers/claim_program.sl\n", l.join(", ")));
        s.push_str("    every run from an unprivileged exec state that ends exits with one of these statuses,\n");
        s.push_str("    or dies of a stack overflow; no other crash (runs that never end allowed)\n\n");
    }
    s.push_str(&format!("Binary: {}\n  size {} bytes, sha256 {}\n  entry {:#x}\n", elf_path, bytes.len(), sha256::hex(bytes), elf.entry));
    s.push_str(&format!(
        "  main = {:#x}, malloc = {:#x}, free = {:#x}\n  errno: thread pointer + {:#x}\n",
        addrs.0, addrs.1, addrs.2, MUSL_ERRNO_OFFSET
    ));
    s.push_str("  STATIC (memory the allocator may own at main, besides the thread descriptor up to errno\n          and the auxiliary vector with its AT_RANDOM bytes on the initial stack):\n");
    for (lo, hi, n) in ranges {
        s.push_str(&format!("    [{:#x}, {:#x})  {}\n", lo, hi, n));
    }
    s.push_str("\nTrusted base:\n");
    s.push_str("  1. The kernel (slc/kernel): terms, modus ponens, instantiation, conservative definitions,\n");
    s.push_str("     literal arithmetic; it re-read and accepted the .core file.\n");
    s.push_str(&format!("  2. Logic axioms: core/prelude.core (sha256 {}):\n     ", sha256::hex(prelude.as_bytes())));
    s.push_str(&env.axioms.iter().map(|a| a.0.clone()).collect::<Vec<_>>().join(", "));
    s.push_str("\n  3. The model of x86_64 + Linux (module x86_64_linux) is assumed to describe the\n");
    s.push_str("     real machine and kernel. Its files:\n");
    let mut layers = Vec::new();
    for (path, text) in &sm.files {
        let line = format!("       {:<32} sha256 {}\n", rel(path), sha256::hex(text.as_bytes()));
        // (the model: the files under spec/)
        if rel(path).starts_with("spec/") {
            s.push_str(&line);
        } else {
            layers.push(line);
        }
    }
    s.push_str("\nLayers (definitions only: they add no assumptions, but they determine what the claim\nmeans, e.g. what malloc promises -- review them to judge what is claimed):\n");
    for l in layers {
        s.push_str(&l);
    }
    s.push_str(&format!(
        "\nThe .core file: {} definitions after the prelude, claims: {}.\n",
        env.syms.len() - el.prelude_syms,
        env.claims.iter().map(|c| c.0.clone()).collect::<Vec<_>>().join(", ")
    ));
    s.push_str("\nNotes:\n");
    s.push_str("  - No proof is given. The claim can only be true if every instruction and system call the\n");
    s.push_str("    allocator executes is modelled; run `slc coverage ELF malloc free` for the gaps.\n");
    s
}
