use sl_kernel::{syntax, Env};
use std::path::PathBuf;

pub type CResult = Result<(), String>;

/// The file cache of `kernel-check`: per checked file, its statements (the
/// file with its proofs replaced by `cached`, `sl_kernel::ext::cache`),
/// in build/kernel-cache. A file's entry is used when the file is not
/// newer than it and it was written by the same checker after the same
/// statements of the files before (their hash, `prefix`); otherwise the
/// file is checked and its entry written again.
struct Cache {
    dir: PathBuf,
    /// the checker's identity: its executable's modification time
    checker: String,
}

impl Cache {
    fn new() -> Cache {
        let exe = std::env::current_exe().ok().and_then(|e| std::fs::metadata(e).ok()).and_then(|m| m.modified().ok());
        let checker = exe.and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok()).map(|d| d.as_nanos().to_string()).unwrap_or_default();
        Cache { dir: repo_root().join("build/kernel-cache"), checker }
    }

    fn entry(&self, f: &std::path::Path) -> PathBuf {
        let abs = std::fs::canonicalize(f).unwrap_or_else(|_| f.to_path_buf());
        let key = crate::sha256::hex(abs.to_string_lossy().as_bytes());
        let base = f.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        self.dir.join(format!("{}-{}", &key[..16], base))
    }

    fn header(&self, prefix: &str, first: bool) -> String {
        format!("// slc kernel-check cache (statements only; see `slc kernel-check --no-cache`)\n// checker {}\n// prefix {}\n// first {}\n", self.checker, prefix, first)
    }

    /// f's statements, if its entry holds
    fn lookup(&self, f: &std::path::Path, prefix: &str, first: bool) -> Option<String> {
        if self.checker.is_empty() {
            return None;
        }
        let e = self.entry(f);
        let (tf, te) = (std::fs::metadata(f).ok()?.modified().ok()?, std::fs::metadata(&e).ok()?.modified().ok()?);
        if tf > te {
            return None;
        }
        let text = std::fs::read_to_string(&e).ok()?;
        text.strip_prefix(&self.header(prefix, first)).map(|s| s.to_string())
    }

    /// writes f's entry, dated as f when read (`modified`): a change of f
    /// while it was checked makes f newer
    fn store(&self, f: &std::path::Path, prefix: &str, first: bool, stmts: &str, modified: std::time::SystemTime) {
        if self.checker.is_empty() || std::fs::create_dir_all(&self.dir).is_err() {
            return;
        }
        let e = self.entry(f);
        let tmp = e.with_extension(format!("tmp{}", std::process::id()));
        let ok = std::fs::write(&tmp, format!("{}{}", self.header(prefix, first), stmts)).is_ok()
            && std::fs::File::options().write(true).open(&tmp).and_then(|h| h.set_modified(modified)).is_ok();
        if !ok || std::fs::rename(&tmp, &e).is_err() {
            let _ = std::fs::remove_file(&tmp);
        }
    }
}

/// A checked file's statements: its proofs replaced by `cached` (with the
/// open lemmas a conditional theorem rests on)
fn statements(env: &Env, src: &str, rep: &syntax::LoadReport) -> String {
    let mut out = String::new();
    let mut at = 0;
    for (name, s, e) in &rep.proofs {
        out.push_str(&src[at..*s]);
        out.push_str("cached");
        if let Some((_, q)) = env.open.conditional.iter().find(|(n, _)| n == name) {
            out.push_str(&format!(" rests({})", q.open().join(", ")));
        }
        out.push('\n');
        at = *e;
    }
    out.push_str(&src[at..]);
    out
}

pub fn kernel_check(args: &[String]) -> CResult {
    let no_cache = args.iter().any(|a| a == "--no-cache");
    let files: Vec<PathBuf> = args.iter().filter(|a| *a != "--no-cache").map(PathBuf::from).collect();
    if files.is_empty() {
        return Err("no files".into());
    }
    let cache = if no_cache { None } else { Some(Cache::new()) };
    let mut env = Env::new();
    let mut prover = sl_proof::ScriptProver;
    // (the hash of the statements of the files so far)
    let mut prefix = String::new();
    for (i, f) in files.iter().enumerate() {
        let first = i == 0;
        let hit = cache.as_ref().and_then(|c| c.lookup(f, &prefix, first));
        let cached = hit.is_some();
        let (rep, stmts) = match hit {
            Some(stmts) => {
                let rep = syntax::load_cached(&mut env, &stmts, first)
                    .map_err(|e| format!("{} (its cache entry): {} -- check with --no-cache", f.display(), e))?;
                (rep, stmts)
            }
            None => {
                let modified = std::fs::metadata(f).and_then(|m| m.modified()).map_err(|e| format!("{}: {}", f.display(), e))?;
                let src = std::fs::read_to_string(f).map_err(|e| format!("{}: {}", f.display(), e))?;
                let rep = syntax::load_with(&mut env, &src, first, Some(&mut prover)).map_err(|e| format!("{}: {}", f.display(), e))?;
                let stmts = statements(&env, &src, &rep);
                if let Some(c) = &cache {
                    c.store(f, &prefix, first, &stmts, modified);
                }
                (rep, stmts)
            }
        };
        prefix = crate::sha256::hex(format!("{}\n{}\n{}", prefix, first, stmts).as_bytes());
        println!(
            "{}: {} constants, {} axioms, {} definitions, {} theorems, {} conditional theorems, {} open lemmas, {} claims{}",
            f.display(),
            rep.consts,
            rep.axioms.len(),
            rep.defs,
            rep.theorems.len(),
            rep.conditional.len(),
            rep.lemmas.len(),
            rep.claims.len(),
            if cached { " (cached)" } else { "" }
        );
    }
    // what the claims and conditional theorems still rest on
    let mut status = Vec::new();
    for (c, _) in &env.claims {
        let rest = sl_kernel::ext::facts::remaining(&env, c).map_err(|e| e.0)?;
        status.push(match rest.as_slice() {
            [] => format!("  claim {}: proven", c),
            [x] if x == c => format!("  claim {}: not proven", c),
            _ => format!("  claim {}: proven from {} open lemmas: {}", c, rest.len(), rest.join(", ")),
        });
    }
    for (l, _) in &env.open.lemmas {
        let rest = sl_kernel::ext::facts::remaining(&env, l).map_err(|e| e.0)?;
        status.push(match rest.as_slice() {
            [] => format!("  lemma {}: proven", l),
            [x] if x == l => format!("  lemma {}: open", l),
            _ => format!("  lemma {}: proven from open lemmas: {}", l, rest.join(", ")),
        });
    }
    if !status.is_empty() {
        println!("status:");
        for l in status {
            println!("{}", l);
        }
    }
    println!("ok: all declarations well-formed, definitions conservative, proofs checked, claims closed");
    Ok(())
}

pub fn repo_root() -> PathBuf {
    // `slc` is run from the repository or from `slc/`; find `core/prelude.core`
    let mut d = std::env::current_dir().unwrap();
    loop {
        if d.join("core/prelude.core").exists() {
            return d;
        }
        if !d.pop() {
            return std::env::current_dir().unwrap();
        }
    }
}

pub fn prelude_text() -> Result<String, String> {
    let p = repo_root().join("core/prelude.core");
    std::fs::read_to_string(&p).map_err(|e| format!("{}: {}", p.display(), e))
}

/// Splits `args` into paths and `-o OUT`.
fn paths_and_out(args: &[String]) -> (Vec<PathBuf>, Option<PathBuf>) {
    let mut paths = Vec::new();
    let mut out = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "-o" {
            out = it.next().map(PathBuf::from);
        } else {
            paths.push(PathBuf::from(a));
        }
    }
    if paths.is_empty() {
        let r = repo_root();
        paths = vec![r.join("spec"), r.join("layers")];
    }
    (paths, out)
}

pub fn parse_all(paths: &[PathBuf], sm: &mut sl_syntax::SourceMap) -> Result<Vec<sl_syntax::ast::File>, String> {
    let files = sl_syntax::collect_files(paths).map_err(|e| e.to_string())?;
    let (parsed, diags) = sl_syntax::parse_files(sm, &files);
    if !diags.is_empty() {
        for d in &diags {
            eprintln!("{}", d);
        }
        return Err(format!("{} parse error(s)", diags.len()));
    }
    Ok(parsed)
}

pub fn parse(args: &[String]) -> CResult {
    let (paths, _) = paths_and_out(args);
    let mut sm = sl_syntax::SourceMap::default();
    let files = parse_all(&paths, &mut sm)?;
    let decls: usize = files.iter().map(|f| f.decls.len()).sum();
    println!("parsed {} files, {} declarations", files.len(), decls);
    Ok(())
}

pub fn check(args: &[String]) -> CResult {
    elab_to(args, false)
}

pub fn elab(args: &[String]) -> CResult {
    elab_to(args, true)
}

fn elab_to(args: &[String], write: bool) -> CResult {
    let (paths, out) = paths_and_out(args);
    let mut sm = sl_syntax::SourceMap::default();
    let files = parse_all(&paths, &mut sm)?;
    let prelude = prelude_text()?;
    let el = sl_elab::elaborate(&prelude, files, &sm)?;
    for d in el.render_diags() {
        eprintln!("{}", d);
    }
    let n = el.errors();
    let defs = el.b.env.syms.len() - el.prelude_syms;
    println!("{} definitions, {} claims, {} errors, {} warnings", defs, el.claims.len(), n, el.diags.len() - n);
    if n > 0 {
        return Err("elaboration failed".into());
    }
    if write {
        let text = el.core_text();
        match out {
            Some(o) => {
                std::fs::write(&o, &text).map_err(|e| e.to_string())?;
                println!("wrote {} ({} bytes)", o.display(), text.len());
            }
            None => print!("{}", text),
        }
    }
    Ok(())
}

use sl_interp::elf::Elf;
use sl_interp::{Interp, V};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub(crate) fn load_spec_globals(sm: &mut sl_syntax::SourceMap) -> Result<sl_elab::globals::Globals, String> {
    let r = repo_root();
    let files = parse_all(&[r.join("spec"), r.join("layers")], sm)?;
    sl_elab::globals::Globals::build(files)
}

/// objdump's view: address -> (length, text)
fn objdump(path: &str) -> BTreeMap<u64, (usize, String)> {
    let mut out = BTreeMap::new();
    let o = match std::process::Command::new("objdump").args(["-d", "-w", "-M", "intel", "--no-addresses", path]).output() {
        Ok(_) => std::process::Command::new("objdump").args(["-d", "-w", "-M", "intel", path]).output(),
        Err(e) => Err(e),
    };
    let Ok(o) = o else { return out };
    for line in String::from_utf8_lossy(&o.stdout).lines() {
        // "  401a30:\tf3 0f 1e fa          \tendbr64"
        let mut parts = line.splitn(3, '\t');
        let (Some(a), Some(bytes)) = (parts.next(), parts.next()) else { continue };
        let a = a.trim().trim_end_matches(':');
        let Ok(addr) = u64::from_str_radix(a, 16) else { continue };
        let n = bytes.split_whitespace().count();
        let text = parts.next().unwrap_or("").trim().to_string();
        out.insert(addr, (n, text));
    }
    out
}

fn row_text(sm: &sl_syntax::SourceMap, it: &Interp, k: usize) -> String {
    let r = &it.rows[k].row;
    let t = sm.snippet(r.span).lines().next().unwrap_or("").trim().to_string();
    let consts: Vec<String> = it.rows[k].consts.iter().map(|(n, v)| format!("{}={}", n, v.render())).collect();
    if consts.is_empty() { t } else { format!("{}   [{}]", t, consts.join(", ")) }
}

pub fn decode(args: &[String]) -> CResult {
    if args.len() < 2 {
        return Err("usage: slc decode ELF SYMBOL".into());
    }
    let elf = Elf::parse(std::fs::read(&args[0]).map_err(|e| e.to_string())?)?;
    let sym = elf.symbol(&args[1]).ok_or_else(|| format!("no symbol `{}`", args[1]))?;
    let (start, size) = (sym.value, sym.size);
    let mut sm = sl_syntax::SourceMap::default();
    let g = load_spec_globals(&mut sm)?;
    let it = Interp::new(&g, "x86")?;
    let od = objdump(&args[0]);
    let mut addr = start;
    let (mut agree, mut unknown, mut disagree) = (0, 0, 0);
    while addr < start + size {
        let bytes = elf.bytes_at(addr, 15).unwrap_or(&[]);
        let ms = it.decode(bytes);
        let (olen, otext) = od.get(&addr).cloned().unwrap_or((0, "?".into()));
        match ms.first() {
            Some(m) => {
                let mark = if m.len == olen { agree += 1; " " } else { disagree += 1; "!" };
                let binds: Vec<String> = m.binds.iter().map(|(n, v)| format!("{}={}", n, v.render())).collect();
                println!("{}{:x}: {:<40} | {} {}{}", mark, addr, otext, row_text(&sm, &it, m.row), binds.join(" "),
                         if ms.len() > 1 { format!("   ({} rows match)", ms.len()) } else { String::new() });
                addr += m.len.max(1) as u64;
            }
            None => {
                unknown += 1;
                println!("?{:x}: {:<40} | UNMODELLED", addr, otext);
                addr += olen.max(1) as u64;
            }
        }
    }
    println!("-- {} instructions agree with objdump, {} disagree in length, {} unmodelled", agree, disagree, unknown);
    Ok(())
}

/// How control continues after an instruction (from the row's body).
#[derive(Debug, Clone, PartialEq)]
enum FlowK {
    Fall,
    Jump(sl_syntax::ast::Expr),
    CondJump(sl_syntax::ast::Expr),
    Call(sl_syntax::ast::Expr),
    IndirectCall,
    IndirectJump,
    Ret,
    Stop,
    Syscall,
}

fn classify(body: &sl_syntax::ast::Block) -> FlowK {
    use sl_syntax::ast::*;
    fn callee(e: &Expr) -> Option<(&str, &Vec<Expr>)> {
        match &e.kind {
            ExprKind::Call(f, args) => match &f.kind {
                ExprKind::Name(n) => Some((n.name.as_str(), args)),
                _ => None,
            },
            _ => None,
        }
    }
    for s in &body.stmts {
        match &s.kind {
            StmtKind::Expr(e) => match callee(e) {
                Some(("jump_rel", a)) => return FlowK::Jump(a[0].clone()),
                Some(("call_rel", a)) => return FlowK::Call(a[0].clone()),
                Some(("call_abs", _)) => return FlowK::IndirectCall,
                Some(("syscall", _)) => return FlowK::Syscall,
                _ => {}
            },
            StmtKind::If { then, .. } => {
                if let Some(StmtKind::Expr(e)) = then.stmts.first().map(|s| &s.kind) {
                    if let Some(("jump_rel", a)) = callee(e) {
                        return FlowK::CondJump(a[0].clone());
                    }
                }
            }
            StmtKind::Assign { target, value, .. } => {
                if matches!(&target.kind, ExprKind::Name(n) if n.name == "rip") {
                    return if matches!(callee(value), Some(("pop", _))) { FlowK::Ret } else { FlowK::IndirectJump };
                }
            }
            StmtKind::Raise(_) | StmtKind::Undefined => return FlowK::Stop,
            _ => {}
        }
    }
    FlowK::Fall
}

/// The kind of control flow of a table row: "fall", "jump", "condjump",
/// "call", "indcall", "indjump", "ret", "stop" or "syscall".
pub fn flow_kind(body: &sl_syntax::ast::Block) -> &'static str {
    match classify(body) {
        FlowK::Fall => "fall",
        FlowK::Jump(_) => "jump",
        FlowK::CondJump(_) => "condjump",
        FlowK::Call(_) => "call",
        FlowK::IndirectCall => "indcall",
        FlowK::IndirectJump => "indjump",
        FlowK::Ret => "ret",
        FlowK::Stop => "stop",
        FlowK::Syscall => "syscall",
    }
}

pub fn coverage(args: &[String]) -> CResult {
    if args.len() < 2 {
        return Err("usage: slc coverage ELF SYMBOL...".into());
    }
    let elf = Elf::parse(std::fs::read(&args[0]).map_err(|e| e.to_string())?)?;
    let mut sm = sl_syntax::SourceMap::default();
    let g = load_spec_globals(&mut sm)?;
    let it = Interp::new(&g, "x86")?;
    let od = objdump(&args[0]);
    let modelled_syscalls: BTreeSet<u64> = [0, 1, 9, 10, 11, 12, 158, 60, 202, 218, 231].into_iter().collect();
    let mut work: VecDeque<u64> = VecDeque::new();
    for s in &args[1..] {
        work.push_back(elf.symbol(s).ok_or_else(|| format!("no symbol `{}`", s))?.value);
    }
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    let mut unmodelled: BTreeMap<u64, String> = BTreeMap::new();
    let mut indirect: BTreeMap<u64, String> = BTreeMap::new();
    let mut syscalls: BTreeMap<u64, String> = BTreeMap::new();
    let mut funcs: BTreeSet<String> = BTreeSet::new();
    let mut rows_used: BTreeMap<usize, usize> = BTreeMap::new();
    let mut ninsn = 0;
    while let Some(addr) = work.pop_front() {
        if !seen.insert(addr) {
            continue;
        }
        if let Some(s) = elf.symbol_at(addr) {
            funcs.insert(s.name.clone());
        }
        let bytes = match elf.bytes_at(addr, 15) {
            Some(b) => b,
            None => continue,
        };
        ninsn += 1;
        let ms = it.decode(bytes);
        let (olen, otext) = od.get(&addr).cloned().unwrap_or((0, "?".into()));
        let loc = match elf.symbol_at(addr) {
            Some(s) => format!("{}+{:#x}", s.name, addr - s.value),
            None => String::new(),
        };
        let m = match ms.first() {
            Some(m) => m,
            None => {
                unmodelled.insert(addr, format!("{:<28} {}", loc, otext));
                // continue past it using objdump's length, to see what else is reachable
                if olen > 0 && !otext.starts_with("ret") && !otext.starts_with("jmp") {
                    work.push_back(addr + olen as u64);
                }
                continue;
            }
        };
        *rows_used.entry(m.row).or_default() += 1;
        let next = addr + m.len as u64;
        let target = |e: &sl_syntax::ast::Expr| -> Option<u64> {
            let v = it.eval_with(e, &m.binds).ok()?;
            match v {
                V::Num(n, _) => sl_interp::num::Int::from_i128(next as i128).add(&n).wrap(64).to_u64(),
                _ => None,
            }
        };
        match classify(&it.rows[m.row].row.body) {
            FlowK::Fall => work.push_back(next),
            FlowK::Jump(e) => work.extend(target(&e)),
            FlowK::CondJump(e) => {
                work.extend(target(&e));
                work.push_back(next)
            }
            FlowK::Call(e) => {
                work.extend(target(&e));
                work.push_back(next)
            }
            FlowK::IndirectCall => {
                indirect.insert(addr, format!("{:<28} {}", loc, otext));
                work.push_back(next)
            }
            FlowK::IndirectJump => {
                indirect.insert(addr, format!("{:<28} {}", loc, otext));
            }
            FlowK::Ret | FlowK::Stop => {}
            FlowK::Syscall => {
                // syscall number: the closest preceding `mov eax, imm`
                let nr = od.range(..addr).rev().take(6).find_map(|(_, (_, t))| {
                    let t = t.split_whitespace().collect::<Vec<_>>().join(" ");
                    t.strip_prefix("mov eax,").and_then(|x| {
                        let x = x.trim();
                        x.strip_prefix("0x").map(|h| u64::from_str_radix(h, 16).ok()).unwrap_or_else(|| x.parse().ok())
                    })
                });
                let note = match nr {
                    Some(n) if modelled_syscalls.contains(&n) => format!("syscall {} (modelled)", n),
                    Some(n) => format!("syscall {} (NOT MODELLED)", n),
                    None => "syscall with unknown number".into(),
                };
                syscalls.insert(addr, format!("{:<28} {}", loc, note));
                work.push_back(next)
            }
        }
    }
    println!("Coverage from {} in {}", args[1..].join(", "), args[0]);
    println!("  {} reachable instructions in {} functions: {}", ninsn, funcs.len(), funcs.iter().cloned().collect::<Vec<_>>().join(", "));
    println!("  {} distinct table rows used", rows_used.len());
    println!("\nUnmodelled instructions ({}):", unmodelled.len());
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for (a, t) in &unmodelled {
        println!("  {:x}  {}", a, t);
        let mn = t.split_whitespace().nth(1).unwrap_or("?").to_string();
        *kinds.entry(mn).or_default() += 1;
    }
    println!("\nUnmodelled instruction kinds: {}", kinds.iter().map(|(k, n)| format!("{} x{}", k, n)).collect::<Vec<_>>().join(", "));
    println!("\nSystem calls ({}):", syscalls.len());
    for (a, t) in &syscalls {
        println!("  {:x}  {}", a, t);
    }
    println!("\nIndirect jumps / calls ({}):", indirect.len());
    for (a, t) in &indirect {
        println!("  {:x}  {}", a, t);
    }
    Ok(())
}

