//! Lowering parsed GIMPLE to the normalized form of `layers/gimple.sl`,
//! printed as SL source: names numbered, memory references resolved to
//! base + offset + size with DWARF layouts, globals to their addresses,
//! inline assembly assembled.
//!
//! Nothing here is trusted: a mistake makes a proof about the machine code
//! fail, it cannot make a false claim provable.

use super::dump::{Block, Func, E, S};
use super::dwarf::{DType, Dwarf};
use std::collections::HashMap;
use std::fmt::Write;

pub mod readable;

/// Types of GIMPLE values and objects.
#[derive(Clone, Debug)]
pub enum RT {
    Int { prec: u64, signed: bool, size: u64 },
    Ptr(Box<RT>),
    Struct(u64),
    Array(Box<RT>, u64),
    Vector(u64, Box<RT>),
    Complex(Box<RT>),
    Void,
}

impl RT {
    fn int(prec: u64, signed: bool) -> RT {
        RT::Int { prec, signed, size: (prec + 7) / 8 }
    }
}

/// Global symbols: statics of this source file first, then global ones.
pub struct Symbols {
    pub local: HashMap<String, u64>,
    pub global: HashMap<String, u64>,
    /// the other local symbols (the linker's own, `__init_array_start`),
    /// none where several have the name
    pub other_local: HashMap<String, Option<u64>>,
    /// the object's weak undefined symbols the binary does not define: at
    /// address 0 (`_DYNAMIC` in a static binary)
    pub weak0: Vec<String>,
}

impl Symbols {
    /// From `readelf -sW` of the linked binary. The file's static symbols
    /// are those after the FILE symbol named `file` whose group contains
    /// `anchors` (the dump's functions), as file names repeat.
    pub fn read(elf: &str, file: &str, anchors: &[String]) -> Result<Symbols, String> {
        let out = std::process::Command::new("readelf").args(["-sW", elf]).output().map_err(|e| e.to_string())?;
        let text = String::from_utf8_lossy(&out.stdout);
        let mut groups: Vec<(String, HashMap<String, u64>)> = Vec::new();
        let mut global = HashMap::new();
        let mut other_local: HashMap<String, Option<u64>> = HashMap::new();
        for l in text.lines() {
            let f: Vec<&str> = l.split_whitespace().collect();
            if f.len() < 8 || !f[0].ends_with(':') {
                continue;
            }
            let (value, typ, bind, name) = (u64::from_str_radix(f[1], 16).unwrap_or(0), f[3], f[4], f[7]);
            if typ == "FILE" {
                groups.push((name.to_string(), HashMap::new()));
            } else if bind == "LOCAL" {
                other_local.entry(name.to_string()).and_modify(|v| *v = None).or_insert(Some(value));
                if let Some(g) = groups.last_mut() {
                    g.1.insert(name.to_string(), value);
                }
            } else {
                global.insert(name.to_string(), value);
            }
        }
        let mut cands: Vec<&(String, HashMap<String, u64>)> = groups.iter().filter(|g| g.0 == file).collect();
        cands.sort_by_key(|g| std::cmp::Reverse(anchors.iter().filter(|a| g.1.contains_key(*a)).count()));
        let local = cands.first().map(|g| g.1.clone()).unwrap_or_default();
        Ok(Symbols { local, global, other_local, weak0: Vec::new() })
    }

    /// The object's weak undefined symbols (`readelf -sW` of it) that the
    /// binary lacks: resolved to 0 by the linker.
    pub fn read_weak(&mut self, obj: &str) -> Result<(), String> {
        let out = std::process::Command::new("readelf").args(["-sW", obj]).output().map_err(|e| e.to_string())?;
        for l in String::from_utf8_lossy(&out.stdout).lines() {
            let f: Vec<&str> = l.split_whitespace().collect();
            if f.len() >= 8 && f[4] == "WEAK" && f[6] == "UND" && self.addr(f[7]).is_none() {
                self.weak0.push(f[7].to_string());
            }
        }
        Ok(())
    }

    fn addr(&self, n: &str) -> Option<u64> {
        self.local
            .get(n)
            .or_else(|| self.global.get(n))
            .copied()
            .or_else(|| self.other_local.get(n).copied().flatten())
            .or_else(|| self.weak0.iter().any(|w| w == n).then_some(0))
    }

    /// A `static` local `n` of the file: GCC's symbol `n.<number>` (it must
    /// be the only one of that name).
    fn static_local(&self, n: &str) -> Result<u64, String> {
        let found: Vec<u64> = self
            .local
            .iter()
            .filter(|(k, _)| k.strip_prefix(n).and_then(|r| r.strip_prefix('.')).is_some_and(|d| !d.is_empty() && d.chars().all(|c| c.is_ascii_digit())))
            .map(|(_, &v)| v)
            .collect();
        match found[..] {
            [a] => Ok(a),
            [] => Err(format!("no symbol for the static local `{}`", n)),
            _ => Err(format!("several symbols for the static local `{}`", n)),
        }
    }
}

/// String literals' addresses in the linked binary. Each relocation of an
/// object function's code into read-only data (`.rodata*`, `.LC*`) is
/// followed in the binary: at the function's address plus the relocation's
/// offset a 32-bit displacement from the next byte (as `lea` has); the
/// NUL-terminated bytes at its target are the literal. A literal's first
/// such target is its address.
pub fn string_literals(obj: &str, elf_path: &str, syms: &Symbols) -> Result<HashMap<String, u64>, String> {
    let bytes = std::fs::read(elf_path).map_err(|e| format!("{}: {}", elf_path, e))?;
    let elf = sl_interp::elf::Elf::parse(bytes)?;
    let out = std::process::Command::new("readelf").args(["-rW", obj]).output().map_err(|e| e.to_string())?;
    let text = String::from_utf8_lossy(&out.stdout);
    let mut lits = HashMap::new();
    let mut func: Option<u64> = None;
    for l in text.lines() {
        if let Some(rest) = l.strip_prefix("Relocation section '") {
            let sec = rest.split('\'').next().unwrap_or("");
            func = sec.strip_prefix(".rela.text.").and_then(|f| syms.addr(f));
            continue;
        }
        let Some(fa) = func else { continue };
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() < 5 || f[2] != "R_X86_64_PC32" || !(f[4].starts_with(".rodata") || f[4].starts_with(".LC")) {
            continue;
        }
        let Ok(off) = u64::from_str_radix(f[0], 16) else { continue };
        let p = fa + off;
        let Some(d) = elf.bytes_at(p, 4) else { continue };
        let t = (p as i64 + 4 + i32::from_le_bytes([d[0], d[1], d[2], d[3]]) as i64) as u64;
        let mut s = String::new();
        for k in 0..4096u64 {
            match elf.bytes_at(t + k, 1) {
                Some([0]) => {
                    lits.entry(s).or_insert(t);
                    break;
                }
                Some([b]) => s.push(char::from(*b)),
                _ => break,
            }
        }
    }
    Ok(lits)
}

/// Callees, numbered across a translated file.
#[derive(Default)]
pub struct Callees {
    pub names: Vec<String>,
}

impl Callees {
    fn index(&mut self, f: &str) -> usize {
        match self.names.iter().position(|n| n == f) {
            Some(i) => i,
            None => {
                self.names.push(f.to_string());
                self.names.len() - 1
            }
        }
    }
}

fn base_int(words: &str) -> Option<RT> {
    // integer types in any spelling: `signed long`, `long unsigned int` ...
    let ws: Vec<&str> = words.split_whitespace().collect();
    let kw = ["unsigned", "signed", "long", "short", "char", "int"];
    if !ws.is_empty() && ws.iter().all(|w| kw.contains(w)) {
        let unsigned = ws.contains(&"unsigned");
        let has_char = ws.contains(&"char");
        let bits = if has_char {
            8
        } else if ws.contains(&"short") {
            16
        } else if ws.contains(&"long") {
            64
        } else {
            32
        };
        // plain `char` is signed on x86-64
        return Some(RT::int(bits, !unsigned));
    }
    Some(match words {
        "char" | "signed char" => RT::int(8, true),
        "unsigned char" => RT::int(8, false),
        "short int" | "short" => RT::int(16, true),
        "short unsigned int" | "unsigned short" => RT::int(16, false),
        "int" | "signed int" => RT::int(32, true),
        "unsigned int" | "unsigned" => RT::int(32, false),
        "long int" | "long long int" | "ssizetype" => RT::int(64, true),
        "long unsigned int" | "long long unsigned int" | "sizetype" => RT::int(64, false),
        "_Bool" => RT::Int { prec: 1, signed: false, size: 1 },
        // standard typedefs (fixed by the x86-64 ABI), for when DWARF lacks them
        "int8_t" => RT::int(8, true),
        "uint8_t" => RT::int(8, false),
        "int16_t" => RT::int(16, true),
        "uint16_t" => RT::int(16, false),
        "int32_t" => RT::int(32, true),
        "uint32_t" => RT::int(32, false),
        "int64_t" | "intptr_t" | "ptrdiff_t" | "ssize_t" | "off_t" => RT::int(64, true),
        "uint64_t" | "uintptr_t" | "size_t" => RT::int(64, false),
        "void" => RT::Void,
        _ => return None,
    })
}

const REGS: &[(&str, [&str; 4])] = &[
    ("rax", ["al", "ax", "eax", "rax"]),
    ("rcx", ["cl", "cx", "ecx", "rcx"]),
    ("rdx", ["dl", "dx", "edx", "rdx"]),
    ("rbx", ["bl", "bx", "ebx", "rbx"]),
    ("rsi", ["sil", "si", "esi", "rsi"]),
    ("rdi", ["dil", "di", "edi", "rdi"]),
    ("r8", ["r8b", "r8w", "r8d", "r8"]),
    ("r9", ["r9b", "r9w", "r9d", "r9"]),
    ("r10", ["r10b", "r10w", "r10d", "r10"]),
    ("r11", ["r11b", "r11w", "r11d", "r11"]),
];

fn reg_text(reg: &str, prec: u64) -> String {
    let names = REGS.iter().find(|r| r.0 == reg).unwrap().1;
    let i = match prec {
        0..=8 => 0,
        9..=16 => 1,
        17..=32 => 2,
        _ => 3,
    };
    format!("%{}", names[i])
}

/// Assembles AT&T assembly text into bytes with `as`.
fn assemble(text: &str) -> Result<Vec<u8>, String> {
    let dir = std::env::temp_dir().join(format!("slc-as-{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let (s, o, b) = (dir.join("a.s"), dir.join("a.o"), dir.join("a.bin"));
    std::fs::write(&s, format!(".text\n{}\n", text)).map_err(|e| e.to_string())?;
    let run = |cmd: &str, args: &[&std::ffi::OsStr]| -> Result<(), String> {
        let st = std::process::Command::new(cmd).args(args).output().map_err(|e| format!("{}: {}", cmd, e))?;
        if !st.status.success() {
            return Err(format!("{} failed: {}", cmd, String::from_utf8_lossy(&st.stderr)));
        }
        Ok(())
    };
    run("as", &["--64".as_ref(), "-o".as_ref(), o.as_os_str(), s.as_os_str()])?;
    run("objcopy", &["-O".as_ref(), "binary".as_ref(), "--only-section=.text".as_ref(), o.as_os_str(), b.as_os_str()])?;
    std::fs::read(&b).map_err(|e| e.to_string())
}

fn wrap(v: i128, prec: u64) -> u128 {
    if prec >= 128 {
        v as u128
    } else {
        (v as u128) & ((1u128 << prec) - 1)
    }
}

pub struct Lower<'a> {
    pub dw: &'a Dwarf,
    pub syms: &'a Symbols,
    pub callees: &'a mut Callees,
    /// string literals' addresses (`string_literals`)
    pub lits: &'a HashMap<String, u64>,
}

/// The state of lowering one function.
struct Fx {
    names: HashMap<String, usize>,
    types: Vec<(u64, bool)>,
    /// declared types of params and locals
    decl: HashMap<String, RT>,
    /// memory locals: name -> (object index, type)
    objs: HashMap<String, (usize, RT)>,
    /// `static` locals: name -> address
    statics: HashMap<String, u64>,
    obj_list: Vec<(u64, u64)>,
    /// register variables (values, though not SSA names)
    regvars: Vec<String>,
    /// the function's return type
    ret: RT,
    /// statements of the current block
    out: Vec<String>,
}

fn ty_sl(prec: u64, signed: bool) -> String {
    format!("ty({}, {})", prec, signed)
}

fn is_ssa(s: &str) -> bool {
    let s = s.trim_end_matches("(D)");
    match s.rfind('_') {
        Some(i) => i + 1 < s.len() && s[i + 1..].chars().all(|c| c.is_ascii_digit()),
        None => false,
    }
}

fn ssa_base(s: &str) -> &str {
    let s = s.trim_end_matches("(D)");
    &s[..s.rfind('_').unwrap()]
}

impl<'a> Lower<'a> {
    // ---------------------------------------------------------------
    //  Types

    fn dwarf_rt(&self, t: u64) -> Result<RT, String> {
        let s = self.dw.strip(t).ok_or("unresolved DWARF type")?;
        Ok(match self.dw.dies.get(&s).ok_or("unknown DWARF type")? {
            DType::Base { name, size, signed } => {
                if name == "_Bool" {
                    RT::Int { prec: 1, signed: false, size: 1 }
                } else {
                    RT::Int { prec: size * 8, signed: *signed, size: *size }
                }
            }
            DType::Pointer { to } => RT::Ptr(Box::new(match to {
                Some(p) => self.dwarf_rt(*p).unwrap_or(RT::Void),
                None => RT::Void,
            })),
            DType::Struct { .. } => RT::Struct(s),
            DType::Array { elem, dims } => {
                let mut r = self.dwarf_rt(*elem)?;
                for d in dims.iter().rev() {
                    r = RT::Array(Box::new(r), *d);
                }
                r
            }
            DType::Enum { size } => RT::int(size * 8, false),
            _ => RT::Void,
        })
    }

    /// a type as written in the dump
    fn ty(&self, text: &str) -> Result<RT, String> {
        // a function pointer `int (*<T6a4>) (int, char * *)`, and pointers
        // to them (`void (*<T4e0>) (void) *`): a pointer (to code)
        if let Some(i) = text.find("(*") {
            let after = &text[text.rfind(')').map_or(i, |j| j + 1).max(i)..];
            let mut r = RT::Ptr(Box::new(RT::Void));
            for _ in 0..after.matches('*').count() {
                r = RT::Ptr(Box::new(r));
            }
            return Ok(r);
        }
        let t0 = text.replace("{ ref - all }", "").replace("{ref-all}", "");
        // `T[4][3] *`: pointer stars (outermost), then array dimensions; a
        // qualifier between stars (`volatile void * volatile *`) dropped
        let mut t = t0.trim().to_string();
        let mut stars = 0;
        loop {
            let u = t.trim_end();
            if let Some(v) = u.strip_suffix('*') {
                stars += 1;
                t = v.to_string();
            } else if let Some(v) = ["const", "volatile", "restrict", "__restrict"].iter().find_map(|q| {
                u.strip_suffix(q).filter(|v| v.ends_with(|c: char| c.is_whitespace() || c == '*'))
            }) {
                t = v.to_string();
            } else {
                t = u.to_string();
                break;
            }
        }
        let mut dims = Vec::new();
        while t.trim_end().ends_with(']') {
            let i = t.rfind('[').ok_or("bad array type")?;
            let j = t[i..].find(']').ok_or("bad array type")? + i;
            let d = t[i + 1..j].trim();
            // `[0:]`: unknown length (a flexible array member)
            dims.push(if d.ends_with(':') { 0 } else { d.parse::<u64>().map_err(|_| format!("array size in `{}`", text))? });
            t = t[..i].to_string();
        }
        let words: Vec<&str> = t
            .split_whitespace()
            .filter(|w| !matches!(*w, "const" | "volatile" | "restrict" | "__restrict" | "register" | "static"))
            .collect();
        let w = words.join(" ");
        let mut r = if let Some(rest) = w.strip_prefix("vector ( ").or_else(|| w.strip_prefix("vector(")) {
            let (n, e) = rest.split_once(')').ok_or("vector type")?;
            RT::Vector(n.trim().parse().map_err(|_| "vector lanes")?, Box::new(self.ty(e.trim())?))
        } else if let Some(e) = w.strip_prefix("complex ").or_else(|| w.strip_prefix("__complex__ ")) {
            RT::Complex(Box::new(self.ty(e)?))
        } else if let Some(n) = w.strip_prefix("struct ").or_else(|| w.strip_prefix("union ")) {
            // (`struct Phdr`: GIMPLE's name for a typedef of an untagged struct)
            match (self.dw.structs.get(n.trim()), self.dw.typedefs.get(n.trim())) {
                (Some(&s), _) => RT::Struct(s),
                (None, Some(&td)) => self.dwarf_rt(td)?,
                (None, None) => return Err(format!("unknown struct `{}`", n)),
            }
        } else if let Some(b) = w.strip_prefix("<unnamed-unsigned:") {
            RT::int(b.trim_end_matches('>').parse().map_err(|_| "bitfield width")?, false)
        } else if let Some(b) = w.strip_prefix("<unnamed-signed:") {
            RT::int(b.trim_end_matches('>').parse().map_err(|_| "bitfield width")?, true)
        } else if let Some(r) = base_int(&w) {
            r
        } else if let Some(&td) = self.dw.typedefs.get(&w) {
            self.dwarf_rt(td)?
        } else {
            return Err(format!("unknown type `{}`", text));
        };
        // T[4][3]: dims were collected as [3, 4], the innermost first
        for d in dims.into_iter() {
            r = RT::Array(Box::new(r), d);
        }
        for _ in 0..stars {
            r = RT::Ptr(Box::new(r));
        }
        Ok(r)
    }

    fn size(&self, t: &RT) -> Result<u64, String> {
        Ok(match t {
            RT::Int { size, .. } => *size,
            RT::Ptr(_) => 8,
            RT::Struct(s) => self.dw.size(*s).ok_or("struct size")?,
            RT::Array(e, n) => self.size(e)? * n,
            RT::Vector(n, e) => self.size(e)? * n,
            RT::Complex(e) => 2 * self.size(e)?,
            RT::Void => return Err("size of void".into()),
        })
    }

    fn scalar(&self, t: &RT) -> Result<(u64, bool), String> {
        Ok(match t {
            RT::Int { prec, signed, .. } => (*prec, *signed),
            RT::Ptr(_) => (64, false),
            RT::Vector(..) | RT::Complex(_) | RT::Array(..) | RT::Struct(_) => (8 * self.size(t)?, false),
            RT::Void => (64, false),
        })
    }

    // ---------------------------------------------------------------
    //  Names, objects, globals

    fn name_ty(&self, fx: &Fx, s: &str) -> Result<RT, String> {
        let bare = s.trim_end_matches("(D)");
        if let Some(t) = fx.decl.get(bare) {
            return Ok(t.clone());
        }
        if is_ssa(s) {
            if let Some(t) = fx.decl.get(ssa_base(s)) {
                return Ok(t.clone());
            }
        }
        if let Some(&t) = self.dw.vars.get(bare) {
            return self.dwarf_rt(t);
        }
        Err(format!("no type for `{}`", s))
    }

    /// the number of an SSA name (or temporary)
    fn name(&self, fx: &mut Fx, s: &str) -> Result<usize, String> {
        if let Some(&i) = fx.names.get(s) {
            return Ok(i);
        }
        let t = self.name_ty(fx, s)?;
        let sc = self.scalar(&t)?;
        fx.names.insert(s.to_string(), fx.types.len());
        fx.types.push(sc);
        Ok(fx.types.len() - 1)
    }

    fn temp(&self, fx: &mut Fx, prec: u64, signed: bool) -> usize {
        let n = format!("$t{}", fx.types.len());
        fx.names.insert(n, fx.types.len());
        fx.types.push((prec, signed));
        fx.types.len() - 1
    }

    fn is_value_name(&self, fx: &Fx, s: &str) -> bool {
        (is_ssa(s) && (fx.decl.contains_key(s.trim_end_matches("(D)")) || fx.decl.contains_key(ssa_base(s)))) || fx.regvars.iter().any(|r| r == s)
    }

    // ---------------------------------------------------------------
    //  Expressions

    /// a function's name as a value (`stage2 = libc_start_main_stage2`,
    /// `_init` as an argument): its address -- a symbol not a value, local
    /// or variable
    fn function_addr(&self, fx: &Fx, s: &str) -> Option<u64> {
        if self.is_value_name(fx, s) || fx.objs.contains_key(s) || fx.statics.contains_key(s) || fx.decl.contains_key(s) {
            return None;
        }
        // (DWARF's functions: with a parameter list; its variables too have
        // a type, functions one for their result)
        if self.dw.params.contains_key(s) || !self.dw.vars.contains_key(s) { self.syms.addr(s) } else { None }
    }

    /// a string literal's address
    fn lit_addr(&self, s: &str) -> Result<u64, String> {
        self.lits.get(s).copied().ok_or_else(|| format!("no address for the string literal {:?}", s))
    }

    /// the type of an operand or memory reference
    fn type_of(&self, fx: &Fx, e: &E) -> Result<RT, String> {
        Ok(match e {
            E::Name(s) if self.function_addr(fx, s).is_some() => RT::Ptr(Box::new(RT::Void)),
            E::Name(s) => match fx.objs.get(s) {
                Some((_, t)) => t.clone(),
                None => self.name_ty(fx, s)?,
            },
            E::Num(_) => RT::int(64, true),
            E::Str(_) => RT::Ptr(Box::new(RT::int(8, true))),
            E::Addr(r) => RT::Ptr(Box::new(self.type_of(fx, r)?)),
            E::Deref(p) => match self.type_of(fx, p)? {
                RT::Ptr(t) => *t,
                t => return Err(format!("dereferencing a {:?}", t)),
            },
            E::Mem { acc, ptr_ty, .. } => match acc {
                Some(a) => self.ty(a)?,
                None => match self.ty(ptr_ty)? {
                    RT::Ptr(t) => *t,
                    t => return Err(format!("MEM through {:?}", t)),
                },
            },
            E::Field(r, f) => self.member(&self.type_of(fx, r)?, f)?.1,
            E::Arrow(p, f) => self.member(&self.type_of(fx, &E::Deref(p.clone()))?, f)?.1,
            E::Index(r, _) => match self.type_of(fx, r)? {
                RT::Array(e, _) => *e,
                t => return Err(format!("indexing a {:?}", t)),
            },
            E::BitRef(_, bits, _) => RT::int(*bits, false),
            E::Cast(t, _) => self.ty(t)?,
            _ => return Err(format!("no type for {:?}", e)),
        })
    }

    /// (bit offset, type, bitfield width) of a struct member
    fn member(&self, t: &RT, f: &str) -> Result<(u64, RT, Option<u64>), String> {
        let RT::Struct(s) = t else { return Err(format!("field `{}` of a {:?}", f, t)) };
        let Some(DType::Struct { members, .. }) = self.dw.dies.get(s) else { return Err("struct".into()) };
        let m = members.iter().find(|m| m.name == f).ok_or_else(|| format!("no field `{}`", f))?;
        let mut ty = self.dwarf_rt(m.ty)?;
        if let Some(b) = m.bit_size {
            let signed = matches!(ty, RT::Int { signed: true, .. });
            ty = RT::int(b, signed);
        }
        Ok((m.bit_off, ty, m.bit_size))
    }

    /// an operand for a value of type (prec, signed)
    fn opnd(&mut self, fx: &mut Fx, e: &E, prec: u64) -> Result<String, String> {
        match e {
            E::Num(n) => Ok(format!("cst({})", wrap(*n, prec))),
            E::Str(s) => Ok(format!("cst({})", self.lit_addr(s)?)),
            E::Name(s) if self.is_value_name(fx, s) => Ok(format!("ssa({})", self.name(fx, s)?)),
            E::Name(s) if self.function_addr(fx, s).is_some() => Ok(format!("cst({})", self.function_addr(fx, s).unwrap_or(0))),
            E::Addr(r) => {
                let (b, off) = self.address(fx, r)?;
                Ok(self.add_off(fx, b, off))
            }
            _ => {
                // a memory reference: load it
                let t = self.type_of(fx, e)?;
                let (p, s) = self.scalar(&t)?;
                let x = self.temp(fx, p, s);
                let loc = self.loc(fx, e)?;
                fx.out.push(format!("load({}, {}, {})", x, loc, ty_sl(p, s)));
                Ok(format!("ssa({})", x))
            }
        }
    }

    /// base + constant offset as one operand
    fn add_off(&mut self, fx: &mut Fx, base: Base, off: i128) -> String {
        match base {
            Base::Addr(a) => format!("cst({})", wrap(a as i128 + off, 64)),
            Base::Op(b) if off == 0 => b,
            Base::Op(b) => {
                let x = self.temp(fx, 64, false);
                fx.out.push(format!("assign({}, binary(ptr_add, {}, {}, cst({})))", x, ty_sl(64, false), b, wrap(off, 64)));
                format!("ssa({})", x)
            }
        }
    }

    /// the address of a memory reference: a base and a constant offset
    fn address(&mut self, fx: &mut Fx, e: &E) -> Result<(Base, i128), String> {
        match e {
            E::Name(s) => {
                if let Some((k, _)) = fx.objs.get(s) {
                    return Ok((Base::Op(format!("obj({})", k)), 0));
                }
                if let Some(&a) = fx.statics.get(s) {
                    return Ok((Base::Addr(a), 0));
                }
                if self.is_value_name(fx, s) {
                    return Err(format!("the address of value `{}`", s));
                }
                let a = self.syms.addr(s).ok_or_else(|| format!("no symbol `{}`", s))?;
                Ok((Base::Addr(a), 0))
            }
            E::Mem { base, off, .. } => {
                let (b, o) = match &**base {
                    E::Addr(r) => self.address(fx, r)?,
                    other => (Base::Op(self.opnd(fx, other, 64)?), 0),
                };
                Ok((b, o + off))
            }
            E::Deref(p) => Ok((Base::Op(self.opnd(fx, p, 64)?), 0)),
            E::Field(r, f) => {
                let t = self.type_of(fx, r)?;
                let (bit, _, bf) = self.member(&t, f)?;
                if bf.is_some() {
                    return Err(format!("the address of bitfield `{}`", f));
                }
                let (b, o) = self.address(fx, r)?;
                Ok((b, o + (bit / 8) as i128))
            }
            E::Arrow(p, f) => self.address(fx, &E::Field(Box::new(E::Deref(p.clone())), f.clone())),
            E::Index(r, ix) => {
                let et = match self.type_of(fx, r)? {
                    RT::Array(e, _) => *e,
                    t => return Err(format!("indexing a {:?}", t)),
                };
                let size = self.size(&et)?;
                let (b, o) = self.address(fx, r)?;
                if let E::Num(n) = &**ix {
                    return Ok((b, o + n * size as i128));
                }
                // dynamic index: base + (sign-extended index) * size
                let it = self.type_of(fx, ix)?;
                let (ip, is) = self.scalar(&it)?;
                let i = self.opnd(fx, ix, ip)?;
                let x = self.temp(fx, 64, true);
                fx.out.push(format!("assign({}, convert({}, {}, {}))", x, ty_sl(ip, is), ty_sl(64, true), i));
                let y = self.temp(fx, 64, true);
                fx.out.push(format!("assign({}, binary(mul, {}, ssa({}), cst({})))", y, ty_sl(64, true), x, size));
                let base = self.add_off(fx, b, o);
                let z = self.temp(fx, 64, false);
                fx.out.push(format!("assign({}, binary(ptr_add, {}, {}, ssa({})))", z, ty_sl(64, false), base, y));
                Ok((Base::Op(format!("ssa({})", z)), 0))
            }
            _ => Err(format!("not a memory reference: {:?}", e)),
        }
    }

    /// a memory reference as a `Loc`
    fn loc(&mut self, fx: &mut Fx, e: &E) -> Result<String, String> {
        let (b, o, size, bitpos, bits) = match e {
            E::BitRef(r, bits, pos) => {
                let (b, o) = self.address(fx, r)?;
                if bits % 8 == 0 && pos % 8 == 0 {
                    (b, o + (pos / 8) as i128, bits / 8, 0, 0)
                } else {
                    (b, o + (pos / 8) as i128, (pos % 8 + bits + 7) / 8, pos % 8, *bits)
                }
            }
            E::Field(r, f) | E::Arrow(r, f) => {
                let base_ref = if matches!(e, E::Arrow(..)) { E::Deref(r.clone()) } else { (**r).clone() };
                let t = self.type_of(fx, &base_ref)?;
                let (bit, mt, bf) = self.member(&t, f)?;
                let (b, o) = self.address(fx, &base_ref)?;
                match bf {
                    Some(n) => (b, o + (bit / 8) as i128, (bit % 8 + n + 7) / 8, bit % 8, n),
                    None => (b, o + (bit / 8) as i128, self.size(&mt)?, 0, 0),
                }
            }
            _ => {
                let t = self.type_of(fx, e)?;
                let (b, o) = self.address(fx, e)?;
                (b, o, self.size(&t)?, 0, 0)
            }
        };
        let base = match b {
            Base::Addr(a) => format!("cst({})", a),
            Base::Op(s) => s,
        };
        Ok(format!("Loc {{ base: {}, off: {}, size: {}, align: 1, bitpos: {}, bits: {} }}", base, wrap(o, 64), size, bitpos, bits))
    }

    fn arg_list(&mut self, fx: &mut Fx, f: &str, args: &[E]) -> Result<String, String> {
        let ptys: Vec<RT> = self.dw.params.get(f).map(|ps| ps.iter().filter_map(|&t| self.dwarf_rt(t).ok()).collect()).unwrap_or_default();
        let mut v = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let t = match (ptys.get(i), a) {
                (Some(t), _) => t.clone(),
                (None, E::Num(_)) => RT::int(64, false),
                (None, a) => self.type_of(fx, a)?,
            };
            let (p, s) = self.scalar(&t)?;
            let o = self.opnd(fx, a, p)?;
            v.push(format!("({}, {})", o, ty_sl(p, s)));
        }
        Ok(format!("[{}]", v.join(", ")))
    }

    // ---------------------------------------------------------------
    //  Statements

    fn stmt(&mut self, fx: &mut Fx, s: &S) -> Result<Option<String>, String> {
        match s {
            S::Assign(lhs, rhs) => {
                self.assign(fx, lhs, rhs)?;
                Ok(None)
            }
            S::Call(lhs, f, args) if f.starts_with('.') => {
                let lhs = lhs.as_ref().ok_or("internal function without result")?;
                let x = self.name(fx, match lhs {
                    E::Name(n) => n,
                    _ => return Err("internal function into memory".into()),
                })?;
                let (xp, xs) = fx.types[x];
                let at = self.type_of(fx, &args[0])?;
                let (ap, a_s) = self.scalar(&at)?;
                let (ifn, ty) = match f.as_str() {
                    ".CTZ" => ("ctz".to_string(), (ap, a_s)),
                    ".SAT_SUB" => ("sat_sub".to_string(), (xp, xs)),
                    ".MUL_OVERFLOW" => ("mul_overflow".to_string(), (ap, a_s)),
                    ".REDUC_IOR" => match at {
                        RT::Vector(n, e) => (format!("reduc_ior({})", n), self.scalar(&e)?),
                        _ => return Err("REDUC_IOR of a non-vector".into()),
                    },
                    other => return Err(format!("internal function {}", other)),
                };
                let mut ops = Vec::new();
                for a in args {
                    ops.push(self.opnd(fx, a, ty.0)?);
                }
                fx.out.push(format!("assign({}, internal({}, {}, [{}]))", x, ifn, ty_sl(ty.0, ty.1), ops.join(", ")));
                Ok(None)
            }
            S::Call(lhs, f, args) => {
                let k = self.callees.index(f);
                let al = self.arg_list(fx, f, args)?;
                match lhs {
                    None => fx.out.push(format!("call([], {}, {})", k, al)),
                    Some(E::Name(n)) if self.is_value_name(fx, n) => {
                        let x = self.name(fx, n)?;
                        let (p, s) = fx.types[x];
                        fx.out.push(format!("call([({}, {})], {}, {})", x, ty_sl(p, s), k, al));
                    }
                    Some(m) => {
                        // a small struct returned in rax:rdx, stored to memory
                        let size = self.size(&self.type_of(fx, m)?)?;
                        if size > 16 {
                            return Err("struct result larger than 16 bytes".into());
                        }
                        let (x, y) = (self.temp(fx, 64, false), self.temp(fx, 64, false));
                        fx.out.push(format!("call([({}, {}), ({}, {})], {}, {})", x, ty_sl(64, false), y, ty_sl(64, false), k, al));
                        let (b, o) = self.address(fx, m)?;
                        let base = self.add_off(fx, b, 0);
                        fx.out.push(format!("store(Loc {{ base: {}, off: {}, size: 8, align: 1, bitpos: 0, bits: 0 }}, ssa({}))", base, wrap(o, 64), x));
                        fx.out.push(format!("store(Loc {{ base: {}, off: {}, size: {}, align: 1, bitpos: 0, bits: 0 }}, ssa({}))", base, wrap(o + 8, 64), size - 8, y));
                    }
                }
                Ok(None)
            }
            S::Asm { tmpl, outs, ins } => {
                self.asm(fx, tmpl, outs, ins)?;
                Ok(None)
            }
            S::Return(None) => Ok(Some("ret([])".into())),
            S::Return(Some(e)) => {
                let t = fx.ret.clone();
                if let RT::Struct(_) = t {
                    // a small struct: its two words in rax:rdx
                    let size = self.size(&t)?;
                    let (b, o) = self.address(fx, e)?;
                    let base = self.add_off(fx, b, 0);
                    let (x, y) = (self.temp(fx, 64, false), self.temp(fx, 64, false));
                    fx.out.push(format!("load({}, Loc {{ base: {}, off: {}, size: 8, align: 1, bitpos: 0, bits: 0 }}, {})", x, base, wrap(o, 64), ty_sl(64, false)));
                    fx.out.push(format!("load({}, Loc {{ base: {}, off: {}, size: {}, align: 1, bitpos: 0, bits: 0 }}, {})", y, base, wrap(o + 8, 64), size - 8, ty_sl(64, false)));
                    return Ok(Some(format!("ret([(ssa({}), {}), (ssa({}), {})])", x, ty_sl(64, false), y, ty_sl(64, false))));
                }
                let (p, s) = self.scalar(&t)?;
                let o = self.opnd(fx, e, p)?;
                Ok(Some(format!("ret([({}, {})])", o, ty_sl(p, s))))
            }
            _ => Err("control flow in the middle of a block".into()),
        }
    }

    fn assign(&mut self, fx: &mut Fx, lhs: &E, rhs: &E) -> Result<(), String> {
        let value_lhs = matches!(lhs, E::Name(n) if self.is_value_name(fx, n));
        if !value_lhs {
            // a store
            let t = self.type_of(fx, lhs)?;
            let loc = self.loc(fx, lhs)?;
            match rhs {
                E::Ctor(vals) => {
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
                    let data: Vec<String> = bytes.iter().map(|b| b.to_string()).collect();
                    fx.out.push(format!("store_bytes({}, [{}])", loc, data.join(", ")));
                }
                _ => {
                    let (p, _) = self.scalar(&t)?;
                    let v = self.opnd(fx, rhs, p)?;
                    fx.out.push(format!("store({}, {})", loc, v));
                }
            }
            return Ok(());
        }
        let E::Name(xn) = lhs else { unreachable!() };
        let x = self.name(fx, xn)?;
        let (xp, xs) = fx.types[x];
        let tx = ty_sl(xp, xs);
        let is_ptr = matches!(self.name_ty(fx, xn)?, RT::Ptr(_));
        let rhs_s = match rhs {
            E::Bin(op, a, b) => {
                let cmp = ["==", "!=", "<", "<=", ">", ">="].contains(&op.as_str());
                let (p, s) = if cmp {
                    let t = if matches!(**a, E::Num(_)) { self.type_of(fx, b)? } else { self.type_of(fx, a)? };
                    self.scalar(&t)?
                } else {
                    (xp, xs)
                };
                let name = match op.as_str() {
                    "+" if is_ptr => "ptr_add",
                    "+" => "add",
                    "-" => "sub",
                    "*" => "mul",
                    "/" => "div",
                    "%" => "mod",
                    "&" => "band",
                    "|" => "bor",
                    "^" => "bxor",
                    "<<" => "shl",
                    ">>" => "shr",
                    "==" => "eq",
                    "!=" => "ne",
                    "<" => "lt",
                    "<=" => "le",
                    ">" => "gt",
                    ">=" => "ge",
                    o => return Err(format!("operator {}", o)),
                };
                let bp = if name == "ptr_add" || name == "shl" || name == "shr" {
                    match &**b {
                        E::Num(_) => 64,
                        other => self.scalar(&self.type_of(fx, other)?)?.0,
                    }
                } else {
                    p
                };
                let ao = self.opnd(fx, a, p)?;
                let bo = self.opnd(fx, b, bp)?;
                format!("binary({}, {}, {}, {})", name, ty_sl(p, s), ao, bo)
            }
            E::Code(c, args) if c == "MIN_EXPR" || c == "MAX_EXPR" => {
                let ao = self.opnd(fx, &args[0], xp)?;
                let bo = self.opnd(fx, &args[1], xp)?;
                format!("binary({}, {}, {}, {})", if c == "MIN_EXPR" { "min" } else { "max" }, tx, ao, bo)
            }
            E::Code(c, args) if c == "IMAGPART_EXPR" || c == "REALPART_EXPR" => {
                let t = self.type_of(fx, &args[0])?;
                let a = self.opnd(fx, &args[0], self.scalar(&t)?.0)?;
                format!("unary({}, {}, {})", if c == "IMAGPART_EXPR" { "imagpart" } else { "realpart" }, tx, a)
            }
            E::Neg(a) => format!("unary(neg, {}, {})", tx, self.opnd(fx, a, xp)?),
            E::Not(a) => format!("unary(bnot, {}, {})", tx, self.opnd(fx, a, xp)?),
            E::Cast(_, a) => {
                let (fp, fs) = match &**a {
                    E::Num(_) => (xp, xs),
                    other => self.scalar(&self.type_of(fx, other)?)?,
                };
                let ao = self.opnd(fx, a, fp)?;
                format!("convert({}, {}, {})", ty_sl(fp, fs), tx, ao)
            }
            E::Num(_) => format!("unary(copy, {}, {})", tx, self.opnd(fx, rhs, xp)?),
            E::Name(n) if self.is_value_name(fx, n) => format!("unary(copy, {}, {})", tx, self.opnd(fx, rhs, xp)?),
            E::Addr(_) => format!("unary(copy, {}, {})", tx, self.opnd(fx, rhs, 64)?),
            E::Code(c, _) => return Err(format!("{} not supported", c)),
            _ => {
                // a load
                let loc = self.loc(fx, rhs)?;
                fx.out.push(format!("load({}, {}, {})", x, loc, tx));
                return Ok(());
            }
        };
        fx.out.push(format!("assign({}, {})", x, rhs_s));
        Ok(())
    }

    fn asm(&mut self, fx: &mut Fx, tmpl: &str, outs: &[(String, E)], ins: &[(String, E)]) -> Result<(), String> {
        let all: Vec<(String, E, bool)> =
            outs.iter().map(|(c, e)| (c.clone(), e.clone(), true)).chain(ins.iter().map(|(c, e)| (c.clone(), e.clone(), false))).collect();
        let fixed = |c: &str| match c {
            "a" => Some("rax"),
            "b" => Some("rbx"),
            "c" => Some("rcx"),
            "d" => Some("rdx"),
            "S" => Some("rsi"),
            "D" => Some("rdi"),
            _ => None,
        };
        let mut used: Vec<&str> = all.iter().filter_map(|(c, _, _)| fixed(c.trim_start_matches(['=', '+', '&']))).collect();
        let pool = ["rdx", "rcx", "rsi", "rdi", "r8", "r9", "r10", "r11"];
        let mut texts = Vec::new();
        let mut in_regs = Vec::new();
        let mut out_regs = Vec::new();
        for (c, e, is_out) in &all {
            let c = c.trim_start_matches(['=', '+', '&']);
            let pick = |used: &mut Vec<&'static str>| -> Result<&'static str, String> {
                let r = *pool.iter().find(|r| !used.contains(r)).ok_or("out of registers for asm")?;
                used.push(r);
                Ok(r)
            };
            if c == "m" {
                // a memory operand: its address in a register
                let E::Deref(p) = e else { return Err("asm memory operand".into()) };
                let r = pick(&mut used)?;
                let a = self.opnd(fx, p, 64)?;
                in_regs.push(format!("({}, {})", r, a));
                texts.push(format!("({})", reg_text(r, 64)));
                continue;
            }
            let r = match fixed(c) {
                Some(r) => r,
                None if c == "r" || c == "q" => pick(&mut used)?,
                None => return Err(format!("asm constraint `{}`", c)),
            };
            let (p, s) = match e {
                E::Num(_) => (64, false),
                other => self.scalar(&self.type_of(fx, other)?)?,
            };
            texts.push(reg_text(r, p));
            if *is_out {
                let E::Name(n) = e else { return Err("asm output into memory".into()) };
                let x = self.name(fx, n)?;
                out_regs.push(format!("({}, {}, {})", x, ty_sl(p, s), r));
            } else {
                let a = self.opnd(fx, e, p)?;
                in_regs.push(format!("({}, {})", r, a));
            }
        }
        // %N -> operand text, %% -> %
        let mut text = String::new();
        let cs: Vec<char> = tmpl.chars().collect();
        let mut i = 0;
        while i < cs.len() {
            if cs[i] == '%' && i + 1 < cs.len() && cs[i + 1].is_ascii_digit() {
                let n = cs[i + 1].to_digit(10).unwrap() as usize;
                text.push_str(texts.get(n).ok_or("asm operand number")?);
                i += 2;
            } else if cs[i] == '%' && i + 1 < cs.len() && cs[i + 1] == '%' {
                text.push('%');
                i += 2;
            } else {
                text.push(cs[i]);
                i += 1;
            }
        }
        let code = assemble(&text.replace(';', "\n"))?;
        let code: Vec<String> = code.iter().map(|b| b.to_string()).collect();
        fx.out.push(format!("asm([{}], [{}], [{}])", code.join(", "), in_regs.join(", "), out_regs.join(", ")));
        Ok(())
    }

    // ---------------------------------------------------------------
    //  Functions

    pub fn function(&mut self, f: &Func) -> Result<String, String> {
        let (mut fx, bare) = self.frame(f)?;
        // parameters: their default definitions (`p_2(D)`), as the body names them
        let mut params = Vec::new();
        for (n, _) in &f.params {
            let dd = bare.iter().find(|b| b.ends_with("(D)") && is_ssa(b) && ssa_base(b) == n).cloned().unwrap_or(format!("{}_0(D)", n));
            let x = self.name(&mut fx, &dd)?;
            let (p, s) = fx.types[x];
            params.push(format!("({}, {})", x, ty_sl(p, s)));
        }
        self.function_body(f, fx, params)
    }

    /// The declarations of a function: its names' types, stack objects and
    /// static locals; and the names its statements use.
    fn frame(&mut self, f: &Func) -> Result<(Fx, Vec<String>), String> {
        let ret = self.ty(&f.ret)?;
        let mut fx = Fx {
            names: HashMap::new(),
            types: Vec::new(),
            decl: HashMap::new(),
            objs: HashMap::new(),
            statics: HashMap::new(),
            obj_list: Vec::new(),
            regvars: f.hard_regs.iter().map(|(n, _)| n.clone()).collect(),
            ret,
            out: Vec::new(),
        };
        for (n, t) in &f.params {
            fx.decl.insert(n.clone(), self.ty(t)?);
        }
        for (n, t) in &f.decls {
            fx.decl.insert(n.clone(), self.ty(t)?);
        }
        for (n, t) in &f.statics {
            fx.decl.insert(n.clone(), self.ty(t)?);
            fx.statics.insert(n.clone(), self.syms.static_local(n)?);
        }
        // locals used without an SSA version live in memory
        let mut bare: Vec<String> = Vec::new();
        for b in &f.blocks {
            for s in &b.stmts {
                collect_names_s(s, &mut bare);
            }
        }
        for (n, _) in &f.decls {
            // (a register variable lives in its register: no object)
            if !is_ssa(n) && bare.contains(n) && !f.hard_regs.iter().any(|(r, _)| r == n) {
                let t = fx.decl[n].clone();
                let size = self.size(&t)?;
                let align = size.clamp(1, 16).next_power_of_two().min(16);
                fx.objs.insert(n.clone(), (fx.obj_list.len(), t));
                fx.obj_list.push((size, align));
            }
        }
        Ok((fx, bare))
    }

    fn function_body(&mut self, f: &Func, mut fx: Fx, params: Vec<String>) -> Result<String, String> {
        let index: HashMap<u64, usize> = f.blocks.iter().enumerate().map(|(i, b)| (b.num, i)).collect();
        let bi = |n: u64| index.get(&n).copied().ok_or_else(|| format!("no block {}", n));
        let mut blocks = Vec::new();
        let mut all_stmts: Vec<String> = Vec::new();
        for (bn, b) in f.blocks.iter().enumerate() {
            fx.out.clear();
            let phis = self.phis(&mut fx, b, &bi)?;
            all_stmts.extend(phis.iter().cloned());
            let mut jump = None;
            for (k, s) in b.stmts.iter().enumerate() {
                let last = k + 1 == b.stmts.len();
                let ctx = |e: String| format!("{}, block {}: {}: {:?}", f.name, b.num, e, s);
                match s {
                    S::Goto(t) if last => jump = Some(format!("goto({})", bi(*t).map_err(ctx)?)),
                    S::If { op, a, b: c, yes, no } if last => {
                        let t = if matches!(a, E::Num(_)) { self.type_of(&fx, c) } else { self.type_of(&fx, a) }.map_err(ctx)?;
                        let (p, sg) = self.scalar(&t).map_err(ctx)?;
                        let name = match op.as_str() {
                            "==" => "eq",
                            "!=" => "ne",
                            "<" => "lt",
                            "<=" => "le",
                            ">" => "gt",
                            ">=" => "ge",
                            o => return Err(ctx(format!("condition {}", o))),
                        };
                        let ao = self.opnd(&mut fx, a, p).map_err(ctx)?;
                        let co = self.opnd(&mut fx, c, p).map_err(ctx)?;
                        jump = Some(format!("branch({}, {}, {}, {}, {}, {})", name, ty_sl(p, sg), ao, co, bi(*yes).map_err(ctx)?, bi(*no).map_err(ctx)?));
                    }
                    _ => {
                        if let Some(j) = self.stmt(&mut fx, s).map_err(ctx)? {
                            jump = Some(j);
                        }
                    }
                }
            }
            let jump = match jump {
                Some(j) => j,
                None if bn + 1 < f.blocks.len() => format!("goto({})", bn + 1), // falls through
                None => return Err(format!("{}: block {} has no successor", f.name, b.num)),
            };
            all_stmts.extend(fx.out.iter().cloned());
            blocks.push(format!(
                "    Block {{\n      phis: [{}],\n      body: [\n        {}\n      ],\n      jump: {}\n    }}",
                phis.join(", "),
                fx.out.join(",\n        "),
                jump
            ));
        }
        // every name used is defined: a parameter, a statement's or phi's
        // target, or one of GCC's default definitions (uninitialized)
        let mut defined: std::collections::HashSet<usize> = fx.names.iter().filter(|(n, _)| n.ends_with("(D)")).map(|(_, &i)| i).collect();
        for st in &all_stmts {
            defined.extend(targets(st));
        }
        for part in blocks.join("\n").split("ssa(").skip(1) {
            let n: usize = part.split(')').next().unwrap_or("").parse().map_err(|_| "bad ssa")?;
            if !defined.contains(&n) {
                let name = fx.names.iter().find(|(_, &i)| i == n).map(|(s, _)| s.clone()).unwrap_or_default();
                return Err(format!("{}: `{}` (name {}) is used but never defined", f.name, name, n));
            }
        }
        let types: Vec<String> = fx.types.iter().map(|(p, s)| ty_sl(*p, *s)).collect();
        let objs: Vec<String> = fx.obj_list.iter().map(|(s, a)| format!("({}, {})", s, a)).collect();
        let mut s = String::new();
        writeln!(s, "// {} {}", f.ret, f.name).unwrap();
        writeln!(s, "fn gimple_{}() -> Function = Function {{", f.name).unwrap();
        writeln!(s, "  params: [{}],", params.join(", ")).unwrap();
        writeln!(s, "  types:  (x: Name) => [{}][x],", types.join(", ")).unwrap();
        writeln!(s, "  objs:   [{}],", objs.join(", ")).unwrap();
        writeln!(s, "  blocks: [\n{}\n  ],", blocks.join(",\n")).unwrap();
        writeln!(s, "  entry:  0\n}}").unwrap();
        Ok(s)
    }

    fn phis(&mut self, fx: &mut Fx, b: &Block, bi: &dyn Fn(u64) -> Result<usize, String>) -> Result<Vec<String>, String> {
        let mut out = Vec::new();
        for p in &b.phis {
            let x = self.name(fx, &p.dst)?;
            let prec = fx.types[x].0;
            let mut args = Vec::new();
            for (e, from) in &p.args {
                let saved = std::mem::take(&mut fx.out);
                let o = self.opnd(fx, e, prec)?;
                if !fx.out.is_empty() {
                    return Err(format!("phi argument needing statements: {:?}", e));
                }
                fx.out = saved;
                args.push(format!("({}, {})", bi(*from)?, o));
            }
            out.push(format!("Phi {{ dst: {}, args: [{}] }}", x, args.join(", ")));
        }
        Ok(out)
    }
}

enum Base {
    /// a constant address (a global)
    Addr(u64),
    /// an operand
    Op(String),
}

fn collect_names_e(e: &E, out: &mut Vec<String>) {
    match e {
        E::Name(n) => out.push(n.clone()),
        E::Num(_) | E::Str(_) => {}
        E::Addr(x) | E::Deref(x) | E::Neg(x) | E::Not(x) | E::Cast(_, x) | E::Field(x, _) | E::Arrow(x, _) | E::BitRef(x, _, _) => collect_names_e(x, out),
        E::Index(a, b) | E::Bin(_, a, b) => {
            collect_names_e(a, out);
            collect_names_e(b, out);
        }
        E::Mem { base, .. } => collect_names_e(base, out),
        E::Call(_, v) | E::Code(_, v) | E::Ctor(v) => v.iter().for_each(|x| collect_names_e(x, out)),
    }
}

fn collect_names_s(s: &S, out: &mut Vec<String>) {
    match s {
        S::Assign(a, b) => {
            collect_names_e(a, out);
            collect_names_e(b, out);
        }
        S::Call(l, _, args) => {
            if let Some(l) = l {
                collect_names_e(l, out);
            }
            args.iter().for_each(|a| collect_names_e(a, out));
        }
        S::Asm { outs, ins, .. } => outs.iter().chain(ins.iter()).for_each(|(_, e)| collect_names_e(e, out)),
        S::Return(Some(e)) => collect_names_e(e, out),
        S::If { a, b, .. } => {
            collect_names_e(a, out);
            collect_names_e(b, out);
        }
        _ => {}
    }
}

/// the names a printed statement or phi defines
fn targets(st: &str) -> Vec<usize> {
    let num = |t: &str| t.trim_start_matches(|c: char| c == '(' || c == ' ').split(|c: char| !c.is_ascii_digit()).next().and_then(|d| d.parse().ok());
    if let Some(r) = st.strip_prefix("assign(").or_else(|| st.strip_prefix("load(")).or_else(|| st.strip_prefix("Phi { dst: ")) {
        return num(r).into_iter().collect();
    }
    if let Some(r) = st.strip_prefix("call([") {
        // call([(x, ty(..)), (y, ty(..))], k, args)
        let dsts = r.split("], ").next().unwrap_or("");
        return dsts.split("), (").filter_map(num).collect();
    }
    if st.starts_with("asm(") {
        // asm([code], [ins], [(x, ty(..), reg), ...])
        let outs = st.rsplit("], [").next().unwrap_or("");
        return outs.split("), (").filter_map(num).collect();
    }
    Vec::new()
}
