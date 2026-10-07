//! Text format of the background logic ("core" files).
//!
//! ```text
//! const in(a, b)                          // primitive constant
//! const ex(x. p)                          // argument binding one variable
//! axiom ex_intro(a, x. p): p(a) -> ex(x. p(x))
//! def all(x. p) := !ex(x. !p(x))
//! abbrev sq(a) := int_mul(a, a)           // read sq(t) as int_mul(t, t)
//! claim c: all x. x = x
//! lemma l(a): a -> a                      // open lemma: to be proven later
//! theorem t(a): a -> a                    // proof checked by the `Prover`
//! proof
//!   ...
//! qed
//! theorem l                               // proves the lemma or claim `l`
//! proof
//!   ...
//! qed
//! ```
//!
//! Parameters of `axiom` / `def` are schematic variables; `x y. p` declares
//! `p` with arity 2. Operators map to fixed symbol names, which must be
//! declared: `->` imp, `<->` iff, `||` or, `&&` and, `!` not, `=` eq,
//! `!=` ne, `in` in. `all x y. P` and `ex x. P` are binder sugar for the
//! symbols `all` / `ex`. Literals: `123`, `0xff`, `"text"`, `bytes"00ff"`.

use crate::env::{Env, KResult, KernelError, SymKind};
use crate::ext::{facts, Seq};
use crate::nat::Nat;
use crate::term::{Node, Term, VarId};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    Num(Nat),
    Str(Vec<u8>),
    Bytes(Vec<u8>),
    Sym(&'static str),
    Eof,
}

const SYMS: &[&str] = &[":=", "<->", "->", "||", "&&", "!=", "(", ")", ",", ".", ":", "=", "!"];

struct Lexer<'a> {
    src: &'a [u8],
    pos: usize,
    line: usize,
}

impl<'a> Lexer<'a> {
    fn error<T>(&self, msg: &str) -> KResult<T> {
        Err(KernelError(format!("line {}: {}", self.line, msg)))
    }

    fn skip_ws(&mut self) {
        loop {
            match self.src.get(self.pos) {
                Some(b'\n') => {
                    self.line += 1;
                    self.pos += 1
                }
                Some(c) if c.is_ascii_whitespace() => self.pos += 1,
                Some(b'/') if self.src.get(self.pos + 1) == Some(&b'/') => {
                    while self.pos < self.src.len() && self.src[self.pos] != b'\n' {
                        self.pos += 1
                    }
                }
                _ => return,
            }
        }
    }

    fn string(&mut self) -> KResult<Vec<u8>> {
        self.pos += 1; // opening quote
        let mut out = Vec::new();
        loop {
            match self.src.get(self.pos) {
                None => return self.error("unterminated string"),
                Some(b'"') => {
                    self.pos += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    let c = *self.src.get(self.pos + 1).unwrap_or(&0);
                    self.pos += 2;
                    match c {
                        b'n' => out.push(b'\n'),
                        b'"' => out.push(b'"'),
                        b'\\' => out.push(b'\\'),
                        b'x' => {
                            let h = std::str::from_utf8(self.src.get(self.pos..self.pos + 2).unwrap_or(b""))
                                .ok()
                                .and_then(|h| u8::from_str_radix(h, 16).ok());
                            match h {
                                Some(v) => out.push(v),
                                None => return self.error("bad \\x escape"),
                            }
                            self.pos += 2;
                        }
                        _ => return self.error("bad escape"),
                    }
                }
                Some(&c) => {
                    out.push(c);
                    self.pos += 1
                }
            }
        }
    }

    fn next(&mut self) -> KResult<Tok> {
        self.skip_ws();
        let c = match self.src.get(self.pos) {
            None => return Ok(Tok::Eof),
            Some(&c) => c,
        };
        if c == b'"' {
            return Ok(Tok::Str(self.string()?));
        }
        if c.is_ascii_digit() {
            let start = self.pos;
            while self.pos < self.src.len() && (self.src[self.pos].is_ascii_alphanumeric() || self.src[self.pos] == b'_') {
                self.pos += 1
            }
            let s = std::str::from_utf8(&self.src[start..self.pos]).unwrap();
            return match Nat::parse(s) {
                Some(n) => Ok(Tok::Num(n)),
                None => self.error(&format!("bad number `{}`", s)),
            };
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = self.pos;
            while self.pos < self.src.len()
                && (self.src[self.pos].is_ascii_alphanumeric() || matches!(self.src[self.pos], b'_' | b'\'' | b'.' | b'$'))
            {
                self.pos += 1
            }
            // a trailing dot belongs to binder syntax (`x. p`), not the name
            while self.src[self.pos - 1] == b'.' {
                self.pos -= 1
            }
            let s = std::str::from_utf8(&self.src[start..self.pos]).unwrap().to_string();
            if s == "bytes" && self.src.get(self.pos) == Some(&b'"') {
                let raw = self.string()?;
                let hex = std::str::from_utf8(&raw).map_err(|_| KernelError("bad bytes literal".into()))?;
                if hex.len() % 2 != 0 {
                    return self.error("odd number of hex digits in bytes literal");
                }
                let mut out = Vec::with_capacity(hex.len() / 2);
                for i in (0..hex.len()).step_by(2) {
                    match u8::from_str_radix(&hex[i..i + 2], 16) {
                        Ok(v) => out.push(v),
                        Err(_) => return self.error("bad hex in bytes literal"),
                    }
                }
                return Ok(Tok::Bytes(out));
            }
            return Ok(Tok::Ident(s));
        }
        for s in SYMS {
            if self.src[self.pos..].starts_with(s.as_bytes()) {
                self.pos += s.len();
                return Ok(Tok::Sym(s));
            }
        }
        self.error(&format!("unexpected character `{}`", c as char))
    }
}

/// Parser state for one statement: bound-variable scopes and schematic params.
struct Parser<'a, 'e> {
    lex: Lexer<'a>,
    tok: Tok,
    env: &'e mut Env,
    scopes: Vec<String>,                  // bound variables, innermost last
    params: HashMap<String, VarId>,       // schematic variables of the statement
}

impl<'a, 'e> Parser<'a, 'e> {
    fn bump(&mut self) -> KResult<Tok> {
        let t = std::mem::replace(&mut self.tok, Tok::Eof);
        self.tok = self.lex.next()?;
        Ok(t)
    }

    fn error<T>(&self, msg: &str) -> KResult<T> {
        self.lex.error(msg)
    }

    fn expect(&mut self, s: &'static str) -> KResult<()> {
        if self.tok == Tok::Sym(s) {
            self.bump()?;
            Ok(())
        } else {
            self.error(&format!("expected `{}`, found {:?}", s, self.tok))
        }
    }

    fn ident(&mut self) -> KResult<String> {
        match self.bump()? {
            Tok::Ident(s) => Ok(s),
            t => self.error(&format!("expected a name, found {:?}", t)),
        }
    }

    fn is_sym(&self, s: &str) -> bool {
        matches!(&self.tok, Tok::Sym(x) if *x == s)
    }

    fn sym_named(&self, name: &str) -> KResult<u32> {
        match self.env.sym_by_name.get(name) {
            Some(s) => Ok(*s),
            None => self.error(&format!("unknown symbol `{}`", name)),
        }
    }

    /// Looks ahead: `NAME+ '.'` starts a binding argument.
    fn binding_names(&mut self) -> KResult<Option<Vec<String>>> {
        let save_pos = self.lex.pos;
        let save_line = self.lex.line;
        let save_tok = self.tok.clone();
        let mut names = Vec::new();
        // `all x. P` / `ex x. P` are binder sugar, not binding names
        if matches!(&self.tok, Tok::Ident(n) if n == "all" || n == "ex") {
            return Ok(None);
        }
        while let Tok::Ident(n) = &self.tok {
            names.push(n.clone());
            self.bump()?;
        }
        if !names.is_empty() && self.is_sym(".") {
            self.bump()?;
            return Ok(Some(names));
        }
        self.lex.pos = save_pos;
        self.lex.line = save_line;
        self.tok = save_tok;
        Ok(None)
    }

    fn term(&mut self) -> KResult<Term> {
        let a = self.imp()?;
        if self.is_sym("<->") {
            self.bump()?;
            let b = self.imp()?;
            return Ok(Term::app(self.sym_named("iff")?, vec![a, b]));
        }
        Ok(a)
    }

    fn imp(&mut self) -> KResult<Term> {
        let a = self.or()?;
        if self.is_sym("->") {
            self.bump()?;
            let b = self.imp()?;
            return Ok(self.env.mk_imp(a, b));
        }
        Ok(a)
    }

    fn or(&mut self) -> KResult<Term> {
        let mut a = self.and()?;
        while self.is_sym("||") {
            self.bump()?;
            let b = self.and()?;
            a = Term::app(self.sym_named("or")?, vec![a, b]);
        }
        Ok(a)
    }

    fn and(&mut self) -> KResult<Term> {
        let mut a = self.unary()?;
        while self.is_sym("&&") {
            self.bump()?;
            let b = self.unary()?;
            a = Term::app(self.sym_named("and")?, vec![a, b]);
        }
        Ok(a)
    }

    fn unary(&mut self) -> KResult<Term> {
        if self.is_sym("!") {
            self.bump()?;
            let a = self.unary()?;
            return Ok(Term::app(self.sym_named("not")?, vec![a]));
        }
        let a = self.atom()?;
        let op = match &self.tok {
            Tok::Sym("=") => "eq",
            Tok::Sym("!=") => "ne",
            Tok::Ident(s) if s == "in" => "in",
            _ => return Ok(a),
        };
        self.bump()?;
        let b = self.atom()?;
        if op == "eq" {
            return Ok(self.env.mk_eq(a, b));
        }
        Ok(Term::app(self.sym_named(op)?, vec![a, b]))
    }

    fn binder_body(&mut self, sym: &str, names: Vec<String>) -> KResult<Term> {
        let s = self.sym_named(sym)?;
        let n = names.len();
        self.scopes.extend(names);
        let mut body = self.term()?;
        self.scopes.truncate(self.scopes.len() - n);
        for _ in 0..n {
            body = Term::app(s, vec![body]);
        }
        Ok(body)
    }

    fn atom(&mut self) -> KResult<Term> {
        match self.bump()? {
            Tok::Num(n) => Ok(Term::nat(n)),
            Tok::Str(s) | Tok::Bytes(s) => Ok(Term::bytes(&s)),
            Tok::Sym("(") => {
                let t = self.term()?;
                self.expect(")")?;
                Ok(t)
            }
            Tok::Ident(name) if (name == "all" || name == "ex") && matches!(self.tok, Tok::Ident(_)) => {
                let mut names = Vec::new();
                while let Tok::Ident(n) = &self.tok {
                    names.push(n.clone());
                    self.bump()?;
                }
                self.expect(".")?;
                self.binder_body(&name, names)
            }
            Tok::Ident(name) => self.name_or_app(name),
            t => self.error(&format!("unexpected {:?}", t)),
        }
    }

    fn name_or_app(&mut self, name: String) -> KResult<Term> {
        if let Some(i) = self.scopes.iter().rev().position(|s| *s == name) {
            return Ok(Term::bvar(i as u32));
        }
        let mut args = Vec::new();
        let mut arg_binders = Vec::new();
        if self.is_sym("(") {
            self.bump()?;
            if !self.is_sym(")") {
                loop {
                    let names = self.binding_names()?.unwrap_or_default();
                    let n = names.len();
                    self.scopes.extend(names);
                    args.push(self.term()?);
                    self.scopes.truncate(self.scopes.len() - n);
                    arg_binders.push(n as u32);
                    if self.is_sym(",") {
                        self.bump()?;
                    } else {
                        break;
                    }
                }
            }
            self.expect(")")?;
        }
        if let Some(&v) = self.params.get(&name) {
            if arg_binders.iter().any(|&b| b > 0) {
                return self.error("arguments of a schematic variable cannot bind variables");
            }
            return Ok(Term::var(v, args));
        }
        if let Some((k, body)) = self.env.abbrevs.get(&name) {
            if *k != args.len() || arg_binders.iter().any(|&b| b > 0) {
                return self.error(&format!("`{}`: an abbreviation of {} arguments (binding none)", name, k));
            }
            return Ok(body.instantiate_params(&args, &self.env.binders_fn()));
        }
        let s = self.sym_named(&name)?;
        let expected = &self.env.syms[s as usize].binders;
        if *expected != arg_binders {
            return self.error(&format!(
                "`{}`: expected arguments binding {:?} variables, got {:?}",
                name, expected, arg_binders
            ));
        }
        Ok(Term::app(s, args))
    }

    /// `(a, x. p, x y. q)` -> names with arities
    fn param_list(&mut self) -> KResult<Vec<(String, u32)>> {
        let mut out = Vec::new();
        if !self.is_sym("(") {
            return Ok(out);
        }
        self.bump()?;
        if !self.is_sym(")") {
            loop {
                let bound = self.binding_names()?.map(|v| v.len()).unwrap_or(0);
                out.push((self.ident()?, bound as u32));
                if self.is_sym(",") {
                    self.bump()?;
                } else {
                    break;
                }
            }
        }
        self.expect(")")?;
        Ok(out)
    }

    fn bind_params(&mut self, ps: &[(String, u32)]) -> Vec<VarId> {
        self.params.clear();
        ps.iter()
            .map(|(n, k)| {
                let v = self.env.new_var(n, *k);
                self.params.insert(n.clone(), v);
                v
            })
            .collect()
    }
}

/// Declares an abbreviation: `body` with its `k` parameters as its outer
/// bound variables. (A name of a symbol cannot be one.)
pub fn define_abbrev(env: &mut Env, name: &str, k: usize, body: Term) -> KResult<()> {
    if env.sym_by_name.contains_key(name) {
        return Err(KernelError(format!("`{}` is a symbol", name)));
    }
    env.check_wf(&body, k as u32)?;
    env.abbrevs.insert(name.to_string(), (k, body));
    Ok(())
}

/// Statistics of a loaded file.
#[derive(Default, Debug)]
pub struct LoadReport {
    pub abbrevs: usize,
    pub consts: usize,
    pub axioms: Vec<String>,
    pub defs: usize,
    pub claims: Vec<String>,
    pub theorems: Vec<String>,
    /// open lemmas declared
    pub lemmas: Vec<String>,
    /// theorems proven from open lemmas
    pub conditional: Vec<String>,
    /// each proof's text in the source, `proof` to the line of its `qed`
    /// (byte offsets), with its theorem's name
    pub proofs: Vec<(String, usize, usize)>,
}

/// A proof checker for `theorem ... proof ... qed`, supplied by the caller of
/// `load_with`. It is not trusted: it can only produce a sequent through the
/// kernel's and the extensions' rules, and the loader checks that it is
/// exactly the stated theorem, without hypotheses (resting on open lemmas
/// only if it names them; see `ext::facts`).
pub trait Prover {
    fn prove(&mut self, env: &mut Env, req: &ProofRequest) -> KResult<Seq>;
}

/// What a proof has to establish.
pub struct ProofRequest {
    pub name: String,
    /// the statement's schematic variables, by name
    pub params: Vec<(String, VarId)>,
    pub statement: Term,
    /// the text between `proof` and `qed`
    pub text: String,
    pub line: usize,
}

/// Parses a term, with `scope` giving the schematic variables by name.
pub fn parse_term(env: &mut Env, text: &str, scope: &[(String, VarId)]) -> KResult<Term> {
    parse_value(env, text, scope, 0)
}

/// Parses a value for a variable of arity `k`: `x1 .. xk. body` (just a
/// term for k = 0).
pub fn parse_value(env: &mut Env, text: &str, scope: &[(String, VarId)], k: u32) -> KResult<Term> {
    let mut lex = Lexer { src: text.as_bytes(), pos: 0, line: 1 };
    let tok = lex.next()?;
    let mut p = Parser { lex, tok, env, scopes: Vec::new(), params: scope.iter().cloned().collect() };
    if k > 0 {
        let names = match p.binding_names()? {
            Some(n) if n.len() == k as usize => n,
            _ => return p.error(&format!("expected {} bound names and `.`", k)),
        };
        p.scopes.extend(names);
    }
    let t = p.term()?;
    if p.tok != Tok::Eof {
        return p.error(&format!("unexpected {:?} after the term", p.tok));
    }
    Ok(t)
}

/// Loads a core file into `env`. With `allow_axioms = false`, any `const`
/// or `axiom` is rejected (only definitions and claims).
pub fn load(env: &mut Env, src: &str, allow_axioms: bool) -> KResult<LoadReport> {
    load_with(env, src, allow_axioms, None)
}

/// `load`, also accepting `theorem NAME(params): statement proof ... qed`,
/// whose proofs `prover` checks.
pub fn load_with(env: &mut Env, src: &str, allow_axioms: bool, prover: Option<&mut dyn Prover>) -> KResult<LoadReport> {
    load_mode(env, src, allow_axioms, prover, false)
}

/// Loads a cache file of `slc kernel-check` (`ext::cache`): a checked file
/// whose theorems end in `cached` (`cached rests(a, b)`: resting on those
/// open lemmas) instead of their proofs, recorded without them.
pub fn load_cached(env: &mut Env, src: &str, allow_axioms: bool) -> KResult<LoadReport> {
    load_mode(env, src, allow_axioms, None, true)
}

fn load_mode(env: &mut Env, src: &str, allow_axioms: bool, mut prover: Option<&mut dyn Prover>, cached: bool) -> KResult<LoadReport> {
    let mut lex = Lexer { src: src.as_bytes(), pos: 0, line: 1 };
    let tok = lex.next()?;
    let mut p = Parser { lex, tok, env, scopes: Vec::new(), params: HashMap::new() };
    let mut rep = LoadReport::default();
    loop {
        let kw = match p.bump()? {
            Tok::Eof => return Ok(rep),
            Tok::Ident(k) => k,
            t => return p.error(&format!("expected a declaration, found {:?}", t)),
        };
        let line = p.lex.line;
        let name = p.ident()?;
        let ctx = |e: KernelError| KernelError(format!("line {} (`{}`): {}", line, name, e.0));
        match kw.as_str() {
            "const" | "axiom" if !allow_axioms => return p.error(&format!("`{}` not allowed in this file", kw)),
            "const" => {
                let ps = p.param_list()?;
                p.env.declare_const(&name, ps.iter().map(|x| x.1).collect()).map_err(ctx)?;
                rep.consts += 1;
            }
            "axiom" => {
                let ps = p.param_list()?;
                p.bind_params(&ps);
                p.expect(":")?;
                let t = p.term()?;
                p.env.add_axiom(&name, t).map_err(ctx)?;
                rep.axioms.push(name);
            }
            "def" => {
                let ps = p.param_list()?;
                let vs = p.bind_params(&ps);
                p.expect(":=")?;
                let t = p.term()?;
                p.env.define(&name, vs, t).map_err(ctx)?;
                rep.defs += 1;
            }
            // abbrev NAME(a, b) := term: read NAME(s, t) as term[a := s, b := t]
            "abbrev" => {
                let ps = p.param_list()?;
                if ps.iter().any(|(_, k)| *k > 0) {
                    return p.error("an abbreviation's parameters are terms (binding none)");
                }
                p.expect(":=")?;
                p.params.clear();
                let n = ps.len();
                p.scopes.extend(ps.into_iter().map(|(x, _)| x));
                let body = p.term();
                p.scopes.truncate(p.scopes.len() - n);
                let body = body?;
                if p.env.abbrevs.contains_key(&name) {
                    return Err(ctx(KernelError("abbreviation already declared".into())));
                }
                define_abbrev(p.env, &name, n, body).map_err(ctx)?;
                rep.abbrevs += 1;
            }
            "claim" => {
                p.params.clear();
                p.expect(":")?;
                let t = p.term()?;
                facts::check_new(p.env, &name).map_err(ctx)?;
                p.env.add_claim(&name, t).map_err(ctx)?;
                rep.claims.push(name);
            }
            "lemma" => {
                let ps = p.param_list()?;
                p.bind_params(&ps);
                p.expect(":")?;
                let t = p.term()?;
                facts::add_lemma(p.env, &name, t).map_err(ctx)?;
                rep.lemmas.push(name);
            }
            "theorem" => {
                // `theorem NAME proof`: proves the open lemma or claim NAME
                let known = facts::statement_of(p.env, &name);
                let (params, t) = match (&p.tok, known) {
                    (Tok::Ident(k), Some(t)) if k == "proof" || (cached && k == "cached") => {
                        let mut vs = Vec::new();
                        t.vars(&mut vs);
                        (vs.iter().map(|v| (p.env.vars[*v as usize].name.clone(), *v)).collect::<Vec<_>>(), t)
                    }
                    (_, known) => {
                        let ps = p.param_list()?;
                        let vs = p.bind_params(&ps);
                        p.expect(":")?;
                        let t = p.term()?;
                        if known.is_some_and(|k| k != t) {
                            return Err(ctx(KernelError(
                                "the statement differs from the open lemma or claim of this name (omit it: `theorem NAME proof`)".into(),
                            )));
                        }
                        (ps.iter().map(|(n, _)| n.clone()).zip(vs).collect(), t)
                    }
                };
                // (a cache file's theorem: its statement, `cached`)
                if cached {
                    if !matches!(&p.tok, Tok::Ident(k) if k == "cached") {
                        return p.error("expected `cached`");
                    }
                    p.bump()?;
                    let mut open = Vec::new();
                    if matches!(&p.tok, Tok::Ident(k) if k == "rests") {
                        p.bump()?;
                        p.expect("(")?;
                        loop {
                            open.push(p.ident()?);
                            if !p.is_sym(",") {
                                break;
                            }
                            p.bump()?;
                        }
                        p.expect(")")?;
                    }
                    let conditional = !open.is_empty();
                    crate::ext::cache::admit(p.env, &name, t, open).map_err(ctx)?;
                    if conditional {
                        rep.conditional.push(name);
                    } else {
                        rep.theorems.push(name);
                    }
                    continue;
                }
                if !matches!(&p.tok, Tok::Ident(k) if k == "proof") {
                    return p.error("expected `proof`");
                }
                // the proof text runs to the line holding just the matching
                // `qed` (sub-proofs: a line ending in `proof` opens one)
                let start = p.lex.pos;
                let rest = &src[start..];
                let mut off = 0;
                let mut end = None;
                let mut nest = 1;
                for l in rest.split_inclusive('\n') {
                    let t = l.split("//").next().unwrap_or("").trim();
                    if t == "qed" {
                        nest -= 1;
                        if nest == 0 {
                            end = Some((off, off + l.len()));
                            break;
                        }
                    } else if off > 0 && (t == "proof" || t.ends_with(" proof")) {
                        nest += 1;
                    }
                    off += l.len();
                }
                let Some((stop, after)) = end else { return p.error("`proof` without `qed`") };
                let text = rest[..stop].to_string();
                rep.proofs.push((name.clone(), start - "proof".len(), start + after));
                p.lex.line += rest[..after].matches('\n').count();
                p.lex.pos = start + after;
                p.tok = p.lex.next()?;
                let Some(pr) = prover.as_deref_mut() else {
                    return Err(ctx(KernelError("theorems need a proof checker".into())));
                };
                let req = ProofRequest {
                    name: name.clone(),
                    params,
                    statement: t.clone(),
                    text,
                    line,
                };
                let s = pr.prove(p.env, &req).map_err(ctx)?;
                if s.concl() != &t || !s.hyps().is_empty() {
                    return Err(ctx(KernelError(format!("the proof shows `{}`, not the statement `{}`", s.show(p.env), Printer::new(p.env).term(&t)))));
                }
                let conditional = !s.open().is_empty();
                facts::record(p.env, &name, s).map_err(ctx)?;
                if conditional {
                    rep.conditional.push(name);
                } else {
                    rep.theorems.push(name);
                }
            }
            _ => return p.error(&format!("unknown declaration `{}`", kw)),
        }
    }
}

// ----------------------------------------------------------------------
//  Printing

const OPS: &[(&str, &str, u8)] = &[("iff", "<->", 1), ("imp", "->", 2), ("or", "||", 3), ("and", "&&", 4)];

pub struct Printer<'e> {
    env: &'e Env,
}

impl<'e> Printer<'e> {
    pub fn new(env: &'e Env) -> Self {
        Printer { env }
    }

    fn name(&self, s: u32) -> &str {
        &self.env.syms[s as usize].name
    }

    pub fn term(&self, t: &Term) -> String {
        let mut out = String::new();
        self.go(t, &mut Vec::new(), 0, &mut out);
        out
    }

    /// `t` with k loose bound variables, as the binder `x0 .. xk-1. t`
    /// (`BVar(0)` the last)
    pub fn lambda(&self, k: usize, t: &Term) -> String {
        let mut scope: Vec<String> = (0..k).map(|i| format!("x{}", i)).collect();
        let mut out = scope.join(" ");
        if k > 0 {
            out.push_str(". ");
        }
        self.go(t, &mut scope, 0, &mut out);
        out
    }

    fn fresh(&self, scope: &[String]) -> String {
        format!("x{}", scope.len())
    }

    fn go(&self, t: &Term, scope: &mut Vec<String>, prec: u8, out: &mut String) {
        match t.node() {
            Node::BVar(i) => out.push_str(&scope[scope.len() - 1 - *i as usize]),
            Node::Nat(n) => out.push_str(&n.to_string()),
            Node::Bytes(b) => {
                if b.iter().all(|c| (0x20..0x7f).contains(c) && *c != b'"' && *c != b'\\') && !b.is_empty() {
                    out.push('"');
                    out.push_str(std::str::from_utf8(b).unwrap());
                    out.push('"');
                } else {
                    out.push_str("bytes\"");
                    for c in b.iter() {
                        out.push_str(&format!("{:02x}", c));
                    }
                    out.push('"');
                }
            }
            Node::Var(v, args) => {
                // (variables made up by tools, e.g. the simplifier's path variables)
                match self.env.vars.get(*v as usize) {
                    Some(info) => out.push_str(&info.name),
                    None => out.push_str(&format!("?v{}", v)),
                }
                if !args.is_empty() {
                    out.push('(');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        self.go(a, scope, 0, out);
                    }
                    out.push(')');
                }
            }
            Node::App(s, args) => {
                let name = self.name(*s).to_string();
                if let Some(&(_, op, p)) = OPS.iter().find(|o| o.0 == name) {
                    if args.len() == 2 {
                        let paren = p < prec || (p == prec && p != 2);
                        if paren {
                            out.push('(');
                        }
                        // `->` is right associative; the others are printed with parentheses when nested
                        self.go(&args[0], scope, p + 1, out);
                        out.push_str(&format!(" {} ", op));
                        self.go(&args[1], scope, if p == 2 { p } else { p + 1 }, out);
                        if paren {
                            out.push(')');
                        }
                        return;
                    }
                }
                if (name == "eq" || name == "ne" || name == "in") && args.len() == 2 {
                    let op = match name.as_str() {
                        "eq" => "=",
                        "ne" => "!=",
                        _ => "in",
                    };
                    if prec > 5 {
                        out.push('(');
                    }
                    self.go(&args[0], scope, 6, out);
                    out.push_str(&format!(" {} ", op));
                    self.go(&args[1], scope, 6, out);
                    if prec > 5 {
                        out.push(')');
                    }
                    return;
                }
                if name == "not" && args.len() == 1 {
                    out.push('!');
                    self.go(&args[0], scope, 6, out);
                    return;
                }
                let binders = &self.env.syms[*s as usize].binders;
                if (name == "all" || name == "ex") && binders == &[1] {
                    if prec > 0 {
                        out.push('(');
                    }
                    let v = self.fresh(scope);
                    out.push_str(&format!("{} {}. ", name, v));
                    scope.push(v);
                    self.go(&args[0], scope, 0, out);
                    scope.pop();
                    if prec > 0 {
                        out.push(')');
                    }
                    return;
                }
                out.push_str(&name);
                if !args.is_empty() {
                    out.push('(');
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        let k = binders[i] as usize;
                        for _ in 0..k {
                            let v = self.fresh(scope);
                            out.push_str(&v);
                            out.push(' ');
                            scope.push(v);
                        }
                        if k > 0 {
                            out.pop();
                            out.push_str(". ");
                        }
                        self.go(a, scope, 0, out);
                        scope.truncate(scope.len() - k);
                    }
                    out.push(')');
                }
            }
        }
    }

    /// Prints a defined symbol as a `def` line (used for the summary).
    pub fn def_line(&self, s: u32) -> Option<String> {
        match &self.env.syms[s as usize].kind {
            SymKind::Defined { params, body } => {
                let ps: Vec<String> = params
                    .iter()
                    .map(|v| {
                        let info = &self.env.vars[*v as usize];
                        let bs: Vec<String> = (0..info.arity).map(|i| format!("y{}", i)).collect();
                        if bs.is_empty() {
                            info.name.clone()
                        } else {
                            format!("{}. {}", bs.join(" "), info.name)
                        }
                    })
                    .collect();
                Some(format!("def {}({}) := {}", self.name(s), ps.join(", "), self.term(body)))
            }
            _ => None,
        }
    }
}
