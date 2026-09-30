//! Recursive-descent parser for SL.

use crate::ast::*;
use crate::lexer::{Tok, Token};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
}

type PResult<T> = Result<T, ParseError>;

const KEYWORDS: &[&str] = &[
    "let", "var", "if", "else", "match", "while", "for", "in", "loop", "break", "return", "raise", "try", "catch",
    "either", "havoc", "where", "require", "guard", "undefined", "emit", "ghost", "fn", "pred", "proc", "view", "type",
    "enum", "record", "state", "const", "exception", "decoder", "notations", "table", "using", "with", "param", "law",
    "theorem", "uses", "extends", "all", "ex", "sum", "any", "true", "false", "self", "is", "notin",
    "refines", "do",
];

const DECL_KEYWORDS: &[&str] = &[
    "type", "enum", "record", "state", "const", "exception", "fn", "pred", "proc", "view", "decoder", "notations",
    "table", "param", "law", "theorem",
];

pub struct Parser<'n> {
    toks: Vec<Token>,
    pos: usize,
    no_struct: bool,
    /// notation blocks known so far (by block name)
    pub notations: &'n mut HashMap<String, Vec<Notation>>,
    pub errors: Vec<ParseError>,
}

fn join(a: Span, b: Span) -> Span {
    Span { file: a.file, lo: a.lo.min(b.lo), hi: a.hi.max(b.hi) }
}

impl<'n> Parser<'n> {
    pub fn new(toks: Vec<Token>, notations: &'n mut HashMap<String, Vec<Notation>>) -> Self {
        Parser { toks, pos: 0, no_struct: false, notations, errors: Vec::new() }
    }

    // ------------------------------------------------------------------
    //  Token helpers

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, k: usize) -> &Tok {
        &self.toks[(self.pos + k).min(self.toks.len() - 1)].tok
    }
    fn span(&self) -> Span {
        self.toks[self.pos].span
    }
    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn at(&self, p: &str) -> bool {
        self.peek().is_punct(p)
    }
    fn at_kw(&self, k: &str) -> bool {
        self.peek().is_ident(k)
    }
    fn eat(&mut self, p: &str) -> bool {
        if self.at(p) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn eat_kw(&mut self, k: &str) -> bool {
        if self.at_kw(k) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn err<T>(&self, msg: impl Into<String>) -> PResult<T> {
        Err(ParseError { msg: msg.into(), span: self.span() })
    }
    fn expect(&mut self, p: &str) -> PResult<Span> {
        if self.at(p) {
            Ok(self.bump().span)
        } else {
            self.err(format!("expected `{}`, found `{}`", p, self.peek().text()))
        }
    }
    fn expect_kw(&mut self, k: &str) -> PResult<()> {
        if self.eat_kw(k) {
            Ok(())
        } else {
            self.err(format!("expected `{}`, found `{}`", k, self.peek().text()))
        }
    }
    fn skip_nl(&mut self) {
        while matches!(self.peek(), Tok::Newline) || self.at(";") {
            self.bump();
        }
    }
    /// Skips newlines only if the next real token is the keyword `k`.
    fn nl_then_kw(&mut self, k: &str) -> bool {
        let mut j = self.pos;
        while matches!(self.toks[j].tok, Tok::Newline) {
            j += 1;
        }
        if self.toks[j].tok.is_ident(k) {
            self.pos = j;
            true
        } else {
            false
        }
    }
    fn nl_then_punct(&mut self, p: &str) -> bool {
        let mut j = self.pos;
        while matches!(self.toks[j].tok, Tok::Newline) {
            j += 1;
        }
        if self.toks[j].tok.is_punct(p) {
            self.pos = j;
            true
        } else {
            false
        }
    }

    fn ident(&mut self) -> PResult<Ident> {
        match self.peek().clone() {
            Tok::Ident(s) if !KEYWORDS.contains(&s.as_str()) => {
                let sp = self.bump().span;
                Ok(Ident { name: s, span: sp })
            }
            t => self.err(format!("expected a name, found `{}`", t.text())),
        }
    }

    /// Any identifier, including keywords (for notation tokens etc.).
    fn any_ident(&mut self) -> PResult<Ident> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                let sp = self.bump().span;
                Ok(Ident { name: s, span: sp })
            }
            t => self.err(format!("expected a name, found `{}`", t.text())),
        }
    }

    /// A `.` directly followed by a name (no space): field access or a
    /// qualified name. A binder's `.` is followed by whitespace.
    fn adjacent_dot(&self) -> bool {
        let d = self.toks[self.pos].span;
        let n = self.toks[(self.pos + 1).min(self.toks.len() - 1)].span;
        d.hi == n.lo
    }

    fn with_struct<T>(&mut self, allowed: bool, f: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        let saved = self.no_struct;
        self.no_struct = !allowed;
        let r = f(self);
        self.no_struct = saved;
        r
    }

    // ------------------------------------------------------------------
    //  File and declarations

    pub fn file(&mut self) -> PResult<File> {
        self.skip_nl();
        let kind = if self.eat_kw("spec") {
            ModuleKind::Spec
        } else if self.eat_kw("layer") {
            ModuleKind::Layer
        } else {
            return self.err("a file must start with `spec NAME` or `layer NAME`");
        };
        let module = self.ident()?;
        let mut uses = Vec::new();
        if self.eat_kw("uses") {
            uses.push(self.ident()?);
            while self.eat(",") {
                uses.push(self.ident()?);
            }
        }
        let mut decls = Vec::new();
        loop {
            self.skip_nl();
            if matches!(self.peek(), Tok::Eof) {
                break;
            }
            match self.decl() {
                Ok(d) => decls.push(d),
                Err(e) => {
                    self.errors.push(e);
                    self.recover();
                }
            }
        }
        Ok(File { kind, module, uses, decls })
    }

    /// Skip to the next line that starts a declaration at top level.
    fn recover(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::Eof => return,
                Tok::Punct("{") | Tok::Punct("(") | Tok::Punct("[") => depth += 1,
                Tok::Punct("}") | Tok::Punct(")") | Tok::Punct("]") => depth -= 1,
                Tok::Newline if depth <= 0 => {
                    if let Tok::Ident(s) = self.peek_at(1) {
                        if DECL_KEYWORDS.contains(&s.as_str()) {
                            self.bump();
                            return;
                        }
                    }
                }
                _ => {}
            }
            self.bump();
        }
    }

    fn decl(&mut self) -> PResult<Decl> {
        let start = self.span();
        let kw = match self.peek().clone() {
            Tok::Ident(s) => s,
            t => return self.err(format!("expected a declaration, found `{}`", t.text())),
        };
        let kind = match kw.as_str() {
            "type" => {
                self.bump();
                self.type_decl()?
            }
            "enum" => {
                self.bump();
                self.enum_decl()?
            }
            "record" => {
                self.bump();
                let name = self.ident()?;
                let fields = self.fields(true)?;
                DeclKind::Record { name, fields }
            }
            "state" => {
                self.bump();
                let name = self.ident()?;
                let extends = if self.eat_kw("extends") { Some(self.ty()?) } else { None };
                let fields = self.fields(true)?;
                DeclKind::State { name, extends, fields }
            }
            "const" => {
                self.bump();
                let name = self.ident()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect("=")?;
                let value = self.expr()?;
                DeclKind::Const { name, ty, value }
            }
            "exception" => {
                self.bump();
                let name = self.ident()?;
                let params = if self.at("(") { self.params()? } else { Vec::new() };
                DeclKind::Exception { name, params }
            }
            "fn" | "pred" => {
                self.bump();
                DeclKind::Fn(self.fn_decl(if kw == "fn" { FnKind::Fn } else { FnKind::Pred })?)
            }
            "decoder" => {
                self.bump();
                if self.eat_kw("context") {
                    DeclKind::DecoderContext(self.ty()?)
                } else {
                    DeclKind::Fn(self.fn_decl(FnKind::Decoder)?)
                }
            }
            "proc" => {
                self.bump();
                DeclKind::Proc(self.proc_decl()?)
            }
            "view" => {
                self.bump();
                self.view_decl()?
            }
            "notations" => {
                self.bump();
                self.notations_decl()?
            }
            "table" => {
                self.bump();
                DeclKind::Table(self.table_decl()?)
            }
            "param" => {
                self.bump();
                if self.eat_kw("pred") {
                    let name = self.ident()?;
                    let params = self.params()?;
                    DeclKind::ParamPred { name, params }
                } else if self.eat_kw("fn") {
                    let name = self.ident()?;
                    let params = self.params()?;
                    self.expect("->")?;
                    let ret = self.ty()?;
                    DeclKind::ParamFn { name, params, ret }
                } else {
                    return self.err("expected `pred` or `fn` after `param`");
                }
            }
            "law" => {
                self.bump();
                let name = self.ident()?;
                let params = if self.at("(") { self.params()? } else { Vec::new() };
                self.expect(":")?;
                let prop = self.expr()?;
                DeclKind::Law { name, params, prop }
            }
            "theorem" => {
                self.bump();
                let name = self.ident()?;
                let generics = self.generics()?;
                let params = if self.at("(") { self.params()? } else { Vec::new() };
                self.expect(":")?;
                let prop = self.expr()?;
                DeclKind::Theorem { name, generics, params, prop }
            }
            _ => return self.err(format!("expected a declaration, found `{}`", kw)),
        };
        let span = join(start, self.prev_span());
        if !matches!(self.peek(), Tok::Newline | Tok::Eof) && !self.at(";") {
            return self.err(format!("unexpected `{}` after declaration", self.peek().text()));
        }
        Ok(Decl { kind, span })
    }

    fn generics(&mut self) -> PResult<Vec<Generic>> {
        let mut out = Vec::new();
        if !self.eat("[") {
            return Ok(out);
        }
        loop {
            let name = self.ident()?;
            let kind = if self.eat(":") { Some(self.ty()?) } else { None };
            out.push(Generic { name, kind });
            if !self.eat(",") {
                break;
            }
        }
        self.expect("]")?;
        Ok(out)
    }

    fn params(&mut self) -> PResult<Vec<Param>> {
        self.expect("(")?;
        let mut out = Vec::new();
        if !self.at(")") {
            loop {
                let name = self.ident()?;
                self.expect(":")?;
                let ty = self.ty()?;
                out.push(Param { name, ty });
                if !self.eat(",") {
                    break;
                }
            }
        }
        self.expect(")")?;
        Ok(out)
    }

    fn type_decl(&mut self) -> PResult<DeclKind> {
        let name = self.ident()?;
        let generics = self.generics()?;
        self.expect("=")?;
        if self.looks_like_sum() {
            let mut variants = vec![self.variant()?];
            while self.nl_then_punct("|") {
                self.bump();
                variants.push(self.variant()?);
            }
            return Ok(DeclKind::TypeDecl { name, generics, def: TypeDef::Sum(variants) });
        }
        let ty = self.ty()?;
        Ok(DeclKind::TypeDecl { name, generics, def: TypeDef::Alias(ty) })
    }

    /// `a | ...` or `a(..) | ...` (possibly with the `|` on the next line)
    fn looks_like_sum(&self) -> bool {
        let mut j = self.pos;
        if !matches!(self.toks[j].tok, Tok::Ident(_)) {
            return false;
        }
        j += 1;
        if self.toks[j].tok.is_punct("(") {
            let mut depth = 0;
            loop {
                match &self.toks[j].tok {
                    Tok::Punct("(") => depth += 1,
                    Tok::Punct(")") => {
                        depth -= 1;
                        if depth == 0 {
                            j += 1;
                            break;
                        }
                    }
                    Tok::Eof => return false,
                    _ => {}
                }
                j += 1;
            }
        }
        while matches!(self.toks[j].tok, Tok::Newline) {
            j += 1;
        }
        self.toks[j].tok.is_punct("|")
    }

    fn variant(&mut self) -> PResult<Variant> {
        let name = self.ident()?;
        let mut params = Vec::new();
        if self.eat("(") {
            let mut i = 0;
            loop {
                // `name: T` or just `T`
                let named = matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1).is_punct(":");
                let (pname, ty) = if named {
                    let n = self.ident()?;
                    self.expect(":")?;
                    (n, self.ty()?)
                } else {
                    let sp = self.span();
                    (Ident { name: format!("_{}", i), span: sp }, self.ty()?)
                };
                params.push(Param { name: pname, ty });
                i += 1;
                if !self.eat(",") {
                    break;
                }
            }
            self.expect(")")?;
        }
        Ok(Variant { name, params })
    }

    fn enum_decl(&mut self) -> PResult<DeclKind> {
        let name = self.ident()?;
        let repr = if self.eat(":") { Some(self.ty()?) } else { None };
        self.expect("{")?;
        let mut items = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                break;
            }
            let n = self.ident()?;
            let value = if self.eat("=") { Some(self.expr()?) } else { None };
            items.push(EnumItem { name: n, value });
            self.skip_nl();
            if !self.eat(",") {
                self.skip_nl();
                self.expect("}")?;
                break;
            }
        }
        Ok(DeclKind::Enum { name, repr, items })
    }

    /// `{ a, b: T, c: U \n ghost d: V }`
    fn fields(&mut self, allow_mods: bool) -> PResult<Vec<Field>> {
        self.expect("{")?;
        let mut out = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                break;
            }
            let ghost = allow_mods && self.eat_kw("ghost");
            // `trace` is contextual: `trace f: T` (but a field may be named `trace`)
            let trace = allow_mods && self.at_kw("trace") && !self.peek_at(1).is_punct(":") && {
                self.bump();
                true
            };
            let mut names = vec![self.ident()?];
            while self.eat(",") {
                names.push(self.ident()?);
            }
            self.expect(":")?;
            let ty = self.ty()?;
            for n in names {
                out.push(Field { name: n, ty: ty.clone(), ghost, trace });
            }
            self.eat(",");
        }
        Ok(out)
    }

    fn fn_decl(&mut self, kind: FnKind) -> PResult<FnDecl> {
        let name = self.ident()?;
        let generics = self.generics()?;
        let params = self.params()?;
        let ret = if self.eat("->") { Some(self.ty()?) } else { None };
        let body = self.body()?;
        Ok(FnDecl { kind, name, generics, params, ret, body })
    }

    fn body(&mut self) -> PResult<Body> {
        if self.eat("=") {
            Ok(Body::Expr(self.expr()?))
        } else {
            Ok(Body::Block(self.block()?))
        }
    }

    fn proc_decl(&mut self) -> PResult<ProcDecl> {
        let state = if self.eat("[") {
            let t = self.ty()?;
            self.expect("]")?;
            Some(t)
        } else {
            None
        };
        let name = self.ident()?;
        let generics = self.generics()?;
        let params = self.params()?;
        let ret = if self.eat("->") { Some(self.ty()?) } else { None };
        let body = self.body()?;
        Ok(ProcDecl { name, state, generics, params, ret, body })
    }

    fn view_decl(&mut self) -> PResult<DeclKind> {
        let state = if self.eat("[") {
            let t = self.ty()?;
            self.expect("]")?;
            Some(t)
        } else {
            None
        };
        let name = self.ident()?;
        let params = if self.at("(") { self.params()? } else { Vec::new() };
        self.expect(":")?;
        let ty = self.ty()?;
        self.expect("{")?;
        self.skip_nl();
        if !self.eat_kw("get") {
            return self.err("expected `get` in view");
        }
        let get = if self.eat("=") {
            ViewGet::Expr(self.expr()?)
        } else {
            ViewGet::Block(self.block()?)
        };
        self.skip_nl();
        if !self.eat_kw("set") {
            return self.err("expected `set(v) { ... }` in view");
        }
        self.expect("(")?;
        let set_var = self.ident()?;
        self.expect(")")?;
        let set = self.block()?;
        self.skip_nl();
        self.expect("}")?;
        Ok(DeclKind::View { name, state, params, ty, get, set_var, set })
    }

    fn notations_decl(&mut self) -> PResult<DeclKind> {
        let name = self.ident()?;
        self.expect("{")?;
        let mut notations = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                break;
            }
            let start = self.span();
            let mut pattern = Vec::new();
            while !self.at("~>") {
                if matches!(self.peek(), Tok::Newline | Tok::Eof) {
                    return self.err("expected `~>` in notation");
                }
                // hole: `(name: kind)`
                if self.at("(") && matches!(self.peek_at(1), Tok::Ident(_)) && self.peek_at(2).is_punct(":") {
                    self.bump();
                    let h = self.any_ident()?;
                    self.expect(":")?;
                    let k = self.any_ident()?;
                    let kind = match k.name.as_str() {
                        "nat" => HoleKind::Nat,
                        "byte" => HoleKind::Byte,
                        "ident" => HoleKind::Ident,
                        "type" => HoleKind::Type,
                        _ => return self.err(format!("unknown hole kind `{}`", k.name)),
                    };
                    self.expect(")")?;
                    pattern.push(PatTok::Hole(h.name, kind));
                } else {
                    pattern.push(PatTok::Tok(self.bump().tok.text()));
                }
            }
            self.expect("~>")?;
            let mut expansion = Vec::new();
            while !matches!(self.peek(), Tok::Newline | Tok::Eof) && !self.at("}") {
                expansion.push(self.bump());
            }
            notations.push(Notation { pattern, expansion, span: join(start, self.prev_span()) });
        }
        self.notations.insert(name.name.clone(), notations.clone());
        Ok(DeclKind::Notations { name, notations })
    }

    // ------------------------------------------------------------------
    //  Tables

    fn table_decl(&mut self) -> PResult<Table> {
        let name = self.ident()?;
        let mut using = Vec::new();
        if self.eat_kw("using") {
            using.push(self.ident()?);
            while self.eat(",") {
                using.push(self.ident()?);
            }
        }
        let mut nots: Vec<Notation> = Vec::new();
        for u in &using {
            match self.notations.get(&u.name) {
                Some(ns) => nots.extend(ns.iter().cloned()),
                None => {
                    return Err(ParseError { msg: format!("unknown notations `{}` (must be declared earlier)", u.name), span: u.span })
                }
            }
        }
        // longest patterns first
        nots.sort_by(|a, b| b.pattern.len().cmp(&a.pattern.len()));
        self.expect("{")?;
        let mut context = None;
        let mut before = Vec::new();
        let mut after = Vec::new();
        let mut entries = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                break;
            }
            if self.at_kw("context") || matches!(self.peek(), Tok::Ident(s) if s == "context") {
                self.bump();
                context = Some(self.expr()?);
            } else if matches!(self.peek(), Tok::Ident(s) if s == "before") {
                self.bump();
                let toks = self.tokens_until_newline();
                before = self.items(&toks, &nots)?;
            } else if matches!(self.peek(), Tok::Ident(s) if s == "after") {
                self.bump();
                let toks = self.tokens_until_newline();
                after = self.items(&toks, &nots)?;
            } else {
                entries.push(self.table_entry(&nots)?);
            }
        }
        let context = match context {
            Some(c) => c,
            None => return self.err("table without `context`"),
        };
        Ok(Table { name, using, context, before, after, entries })
    }

    fn tokens_until_newline(&mut self) -> Vec<Token> {
        let mut out = Vec::new();
        while !matches!(self.peek(), Tok::Newline | Tok::Eof) {
            out.push(self.bump());
        }
        out
    }

    fn table_entry(&mut self, nots: &[Notation]) -> PResult<TableEntry> {
        if self.eat_kw("with") {
            let pat = self.pattern()?;
            self.expect("=")?;
            let item = self.with_struct(false, |p| p.postfix_expr())?;
            let entries = self.table_block(nots)?;
            return Ok(TableEntry::With { pat, item, entries });
        }
        if self.eat_kw("for") {
            let var = self.ident()?;
            self.expect_kw("in")?;
            let ty = self.ident()?;
            let mut except = Vec::new();
            if self.eat_kw("except") {
                except.push(self.ident()?);
                while self.eat(",") {
                    except.push(self.ident()?);
                }
            }
            let entries = self.table_block(nots)?;
            return Ok(TableEntry::For { var, ty, except, entries });
        }
        let start = self.span();
        let mut toks = Vec::new();
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::Punct("=>") if depth == 0 => break,
                Tok::Newline | Tok::Eof if depth == 0 => return self.err("expected `=>` in table row"),
                Tok::Punct("(") | Tok::Punct("[") | Tok::Punct("{") => depth += 1,
                Tok::Punct(")") | Tok::Punct("]") | Tok::Punct("}") => depth -= 1,
                _ => {}
            }
            toks.push(self.bump());
        }
        self.expect("=>")?;
        let items = self.items(&toks, nots)?;
        let body = if self.at("{") {
            self.block()?
        } else {
            let s = self.stmt()?;
            Block { span: s.span, stmts: vec![s] }
        };
        Ok(TableEntry::Row(Row { items, body, span: join(start, self.prev_span()) }))
    }

    fn table_block(&mut self, nots: &[Notation]) -> PResult<Vec<TableEntry>> {
        self.expect("{")?;
        let mut out = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                return Ok(out);
            }
            out.push(self.table_entry(nots)?);
        }
    }

    /// Parses table items from a token slice, expanding notations.
    fn items(&mut self, toks: &[Token], nots: &[Notation]) -> PResult<Vec<Item>> {
        // 1. expand notations (textually) into a new token list
        let mut expanded: Vec<Token> = Vec::new();
        let mut i = 0;
        'outer: while i < toks.len() {
            for n in nots {
                if let Some((len, subst)) = match_notation(&n.pattern, &toks[i..]) {
                    let sp = toks[i].span;
                    for t in &n.expansion {
                        match &t.tok {
                            Tok::Ident(s) if subst.contains_key(s) => {
                                expanded.extend(subst[s].iter().map(|x| Token { tok: x.tok.clone(), span: sp }))
                            }
                            other => expanded.push(Token { tok: other.clone(), span: sp }),
                        }
                    }
                    expanded.push(Token { tok: Tok::Punct(";"), span: sp });
                    i += len;
                    continue 'outer;
                }
            }
            expanded.push(toks[i].clone());
            i += 1;
        }
        // 2. parse the generic item forms with a sub-parser
        let end = toks.last().map(|t| t.span).unwrap_or_default();
        expanded.push(Token { tok: Tok::Eof, span: end });
        let mut dummy = HashMap::new();
        let mut sub = Parser::new(expanded, &mut dummy);
        let mut items = Vec::new();
        loop {
            while sub.eat(";") {}
            if matches!(sub.peek(), Tok::Eof) {
                break;
            }
            items.push(sub.item()?);
        }
        Ok(items)
    }

    fn item(&mut self) -> PResult<Item> {
        if self.eat_kw("if") {
            // a guard extends to the end of the items
            return Ok(Item::Guard(self.with_struct(false, |p| p.expr())?));
        }
        if let Tok::Num(n) = self.peek().clone() {
            let sp = self.bump().span;
            return Ok(Item::Byte(Expr { kind: ExprKind::Num(n), span: sp }));
        }
        if self.eat("{") {
            let e = self.expr()?;
            self.expect("}")?;
            return Ok(Item::Byte(e));
        }
        // `x = d(..)`, `(a, b) = d(..)` or `d(..)`
        let save = self.pos;
        if self.at("(") || (matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1).is_punct("=")) {
            if let Ok(pat) = self.pattern() {
                if self.eat("=") {
                    let e = self.with_struct(false, |p| p.postfix_expr())?;
                    return Ok(Item::Bind(pat, e));
                }
            }
            self.pos = save;
        }
        let e = self.with_struct(false, |p| p.postfix_expr())?;
        Ok(Item::Run(e))
    }

    // ------------------------------------------------------------------
    //  Types

    pub fn ty(&mut self) -> PResult<Type> {
        let a = self.ty_and()?;
        if self.eat("->") {
            let b = self.ty()?;
            return Ok(Type::Map(Box::new(a), Box::new(b)));
        }
        Ok(a)
    }

    fn ty_and(&mut self) -> PResult<Type> {
        let mut a = self.ty_atom()?;
        while self.eat("&") {
            let b = self.ty_atom()?;
            a = Type::And(Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn ty_atom(&mut self) -> PResult<Type> {
        if self.eat("(") {
            let mut ts = Vec::new();
            if !self.at(")") {
                loop {
                    ts.push(self.ty()?);
                    if !self.eat(",") {
                        break;
                    }
                }
            }
            self.expect(")")?;
            if ts.len() == 1 {
                return Ok(ts.pop().unwrap());
            }
            return Ok(Type::Tuple(ts));
        }
        if self.eat("{") {
            let v = self.ident()?;
            self.expect(":")?;
            let t = self.ty()?;
            self.expect("|")?;
            let p = self.expr()?;
            self.expect("}")?;
            return Ok(Type::Refine(v, Box::new(t), Box::new(p)));
        }
        if self.eat_kw("proc") {
            let state = if self.eat("[") {
                let t = self.ty()?;
                self.expect("]")?;
                Some(Box::new(t))
            } else {
                None
            };
            self.expect("(")?;
            let mut params = Vec::new();
            if !self.at(")") {
                loop {
                    params.push(self.ty()?);
                    if !self.eat(",") {
                        break;
                    }
                }
            }
            self.expect(")")?;
            let ret = if self.eat("->") { Some(Box::new(self.ty_and()?)) } else { None };
            return Ok(Type::Proc { state, params, ret });
        }
        if self.eat_kw("enum") {
            let t = self.ty_atom()?;
            return match t {
                Type::Named(n, args) if n.name == "bits" && args.len() == 1 => match &args[0] {
                    GenArg::Expr(e) => Ok(Type::EnumKind(Box::new(e.clone()))),
                    _ => self.err("expected `enum bits[k]`"),
                },
                _ => self.err("expected `enum bits[k]`"),
            };
        }
        let mut name = self.ident()?;
        while self.at(".") && matches!(self.peek_at(1), Tok::Ident(_)) && self.adjacent_dot() {
            self.bump();
            let rest = self.ident()?;
            name = Ident { name: format!("{}.{}", name.name, rest.name), span: join(name.span, rest.span) };
        }
        let mut args = Vec::new();
        if self.eat("[") {
            loop {
                if name.name == "bits" {
                    args.push(GenArg::Expr(self.expr()?));
                } else {
                    args.push(GenArg::Type(self.ty()?));
                }
                if !self.eat(",") {
                    break;
                }
            }
            self.expect("]")?;
        }
        Ok(Type::Named(name, args))
    }

    // ------------------------------------------------------------------
    //  Statements

    pub fn block(&mut self) -> PResult<Block> {
        let start = self.expect("{")?;
        let mut stmts = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                break;
            }
            stmts.push(self.stmt()?);
            if !(matches!(self.peek(), Tok::Newline) || self.at(";") || self.at("}")) {
                return self.err(format!("expected end of statement, found `{}`", self.peek().text()));
            }
        }
        Ok(Block { stmts, span: join(start, self.prev_span()) })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.span();
        let kind = self.stmt_kind()?;
        Ok(Stmt { kind, span: join(start, self.prev_span()) })
    }

    fn at_stmt_end(&self) -> bool {
        matches!(self.peek(), Tok::Newline | Tok::Eof) || self.at(";") || self.at("}") || self.at(",")
    }

    fn stmt_kind(&mut self) -> PResult<StmtKind> {
        let kw = match self.peek() {
            Tok::Ident(s) => s.clone(),
            Tok::Punct("{") => return Ok(StmtKind::Block(self.block()?)),
            _ => String::new(),
        };
        match kw.as_str() {
            "let" => {
                self.bump();
                let pat = self.pattern()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect("=")?;
                let value = self.expr()?;
                Ok(StmtKind::Let { pat, ty, value })
            }
            "var" => {
                self.bump();
                let name = self.ident()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect("=")?;
                let value = self.expr()?;
                Ok(StmtKind::Var { name, ty, value })
            }
            "ghost" => {
                self.bump();
                let target = self.expr()?;
                self.expect(":=")?;
                let value = self.expr()?;
                Ok(StmtKind::Assign { ghost: true, target, value })
            }
            "emit" => {
                self.bump();
                let target = self.with_struct(false, |p| p.postfix_expr())?;
                let event = self.expr()?;
                Ok(StmtKind::Emit { target, event })
            }
            "if" => {
                self.bump();
                let cond = self.with_struct(false, |p| p.expr())?;
                let then = self.block()?;
                let els = if self.nl_then_kw("else") {
                    self.bump();
                    if self.at_kw("if") {
                        let s = self.stmt()?;
                        Some(Block { span: s.span, stmts: vec![s] })
                    } else {
                        Some(self.block()?)
                    }
                } else {
                    None
                };
                Ok(StmtKind::If { cond, then, els })
            }
            "match" => {
                self.bump();
                let scrut = self.with_struct(false, |p| p.expr())?;
                let arms = self.arms()?;
                Ok(StmtKind::Match { scrut, arms })
            }
            "while" => {
                self.bump();
                let cond = self.with_struct(false, |p| p.expr())?;
                Ok(StmtKind::While { cond, body: self.block()? })
            }
            "for" => {
                self.bump();
                let var = self.ident()?;
                self.expect_kw("in")?;
                let iter = self.with_struct(false, |p| p.expr())?;
                Ok(StmtKind::For { var, iter, body: self.block()? })
            }
            "loop" => {
                self.bump();
                Ok(StmtKind::Loop(self.block()?))
            }
            "break" => {
                self.bump();
                Ok(StmtKind::Break)
            }
            "return" => {
                self.bump();
                if self.at_stmt_end() {
                    Ok(StmtKind::Return(None))
                } else {
                    Ok(StmtKind::Return(Some(self.expr()?)))
                }
            }
            "raise" => {
                self.bump();
                Ok(StmtKind::Raise(self.expr()?))
            }
            "try" => {
                self.bump();
                let body = self.block()?;
                let mut catches = Vec::new();
                while self.nl_then_kw("catch") {
                    self.bump();
                    let p = self.pattern()?;
                    catches.push((p, self.block()?));
                }
                if catches.is_empty() {
                    return self.err("`try` without `catch`");
                }
                Ok(StmtKind::Try { body, catches })
            }
            "either" => {
                self.bump();
                let mut blocks = vec![self.block()?];
                while self.nl_then_kw("or") {
                    self.bump();
                    blocks.push(self.block()?);
                }
                if blocks.len() < 2 {
                    return self.err("`either` needs at least one `or`");
                }
                Ok(StmtKind::Either(blocks))
            }
            "havoc" => {
                self.bump();
                let maybe = self.eat("?");
                let mut targets = vec![self.postfix_expr()?];
                while self.eat(",") {
                    targets.push(self.postfix_expr()?);
                }
                let cond = if self.eat_kw("where") { Some(self.expr()?) } else { None };
                // (`else` may start the next line)
                let els = if self.nl_then_kw("else") {
                    self.bump();
                    Some(self.block()?)
                } else {
                    None
                };
                if els.is_some() && cond.is_none() {
                    return self.err("`havoc ... else` needs a `where` condition");
                }
                if maybe && els.is_none() {
                    return self.err("`havoc?` needs an `else` block");
                }
                Ok(StmtKind::Havoc { targets, cond, maybe, els })
            }
            "require" => {
                self.bump();
                Ok(StmtKind::Require(self.expr()?))
            }
            "guard" => {
                self.bump();
                Ok(StmtKind::Guard(self.expr()?))
            }
            "undefined" => {
                self.bump();
                Ok(StmtKind::Undefined)
            }
            _ => {
                let e = self.expr()?;
                if self.eat(":=") {
                    let value = self.expr()?;
                    return Ok(StmtKind::Assign { ghost: false, target: e, value });
                }
                if self.at("==") {
                    return self.err("`==` is not SL: equality is `=`, assignment is `:=`");
                }
                Ok(StmtKind::Expr(e))
            }
        }
    }

    fn arms(&mut self) -> PResult<Vec<Arm>> {
        self.expect("{")?;
        let mut arms = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                return Ok(arms);
            }
            let start = self.span();
            let mut pats = vec![self.pattern()?];
            while self.eat(",") {
                pats.push(self.pattern()?);
            }
            self.expect("=>")?;
            let body = if self.at("{") {
                self.block()?
            } else {
                let s = self.stmt()?;
                Block { span: s.span, stmts: vec![s] }
            };
            arms.push(Arm { pats, body, span: join(start, self.prev_span()) });
            self.eat(",");
        }
    }

    // ------------------------------------------------------------------
    //  Patterns

    pub fn pattern(&mut self) -> PResult<Pattern> {
        let sp = self.span();
        match self.peek().clone() {
            Tok::Num(n) => {
                self.bump();
                Ok(Pattern::Num(n, sp))
            }
            Tok::Punct("(") => {
                self.bump();
                let mut ps = Vec::new();
                if !self.at(")") {
                    loop {
                        ps.push(self.pattern()?);
                        if !self.eat(",") {
                            break;
                        }
                    }
                }
                self.expect(")")?;
                if ps.len() == 1 {
                    return Ok(ps.pop().unwrap());
                }
                Ok(Pattern::Tuple(ps, join(sp, self.prev_span())))
            }
            Tok::Ident(s) if s == "_" => {
                self.bump();
                Ok(Pattern::Wild(sp))
            }
            Tok::Ident(s) if s == "true" || s == "false" => {
                self.bump();
                Ok(Pattern::Bool(s == "true", sp))
            }
            Tok::Ident(_) => {
                let name = self.ident()?;
                if self.eat("(") {
                    let mut ps = Vec::new();
                    if !self.at(")") {
                        loop {
                            ps.push(self.pattern()?);
                            if !self.eat(",") {
                                break;
                            }
                        }
                    }
                    self.expect(")")?;
                    return Ok(Pattern::Ctor(name, ps));
                }
                Ok(Pattern::Name(name))
            }
            t => self.err(format!("expected a pattern, found `{}`", t.text())),
        }
    }

    // ------------------------------------------------------------------
    //  Expressions (precedence climbing)

    pub fn expr(&mut self) -> PResult<Expr> {
        self.expr_iff()
    }

    fn mk(&self, kind: ExprKind, start: Span) -> Expr {
        Expr { kind, span: join(start, self.prev_span()) }
    }

    fn bin(&self, op: BinOp, a: Expr, b: Expr) -> Expr {
        let span = join(a.span, b.span);
        Expr { kind: ExprKind::Binary(op, Box::new(a), Box::new(b)), span }
    }

    fn expr_iff(&mut self) -> PResult<Expr> {
        let a = self.expr_imp()?;
        if self.eat("<->") {
            let b = self.expr_imp()?;
            return Ok(self.bin(BinOp::Iff, a, b));
        }
        Ok(a)
    }

    fn expr_imp(&mut self) -> PResult<Expr> {
        let a = self.expr_or()?;
        if self.eat("->") {
            let b = self.expr_imp()?;
            return Ok(self.bin(BinOp::Imp, a, b));
        }
        Ok(a)
    }

    fn expr_or(&mut self) -> PResult<Expr> {
        let mut a = self.expr_and()?;
        while self.eat("||") {
            let b = self.expr_and()?;
            a = self.bin(BinOp::Or, a, b);
        }
        Ok(a)
    }

    fn expr_and(&mut self) -> PResult<Expr> {
        let mut a = self.expr_cmp()?;
        while self.eat("&&") {
            let b = self.expr_cmp()?;
            a = self.bin(BinOp::And, a, b);
        }
        Ok(a)
    }

    fn expr_cmp(&mut self) -> PResult<Expr> {
        let a = self.expr_range()?;
        let op = match self.peek() {
            Tok::Punct("=") => BinOp::Eq,
            Tok::Punct("!=") => BinOp::Ne,
            Tok::Punct("<") => BinOp::Lt,
            Tok::Punct("<=") => BinOp::Le,
            Tok::Punct(">") => BinOp::Gt,
            Tok::Punct(">=") => BinOp::Ge,
            Tok::Punct("<s") => BinOp::SLt,
            Tok::Punct("<=s") => BinOp::SLe,
            Tok::Punct(">s") => BinOp::SGt,
            Tok::Punct(">=s") => BinOp::SGe,
            Tok::Punct("==") => return self.err("`==` is not SL: equality is `=`"),
            Tok::Ident(s) if s == "in" => BinOp::In,
            Tok::Ident(s) if s == "refines" => BinOp::Refines,
            Tok::Ident(s) if s == "notin" => BinOp::NotIn,
            Tok::Ident(s) if s == "is" => {
                self.bump();
                let p = self.pattern()?;
                let span = join(a.span, self.prev_span());
                return Ok(Expr { kind: ExprKind::Is(Box::new(a), p), span });
            }
            _ => return Ok(a),
        };
        self.bump();
        let b = self.expr_range()?;
        Ok(self.bin(op, a, b))
    }

    fn expr_range(&mut self) -> PResult<Expr> {
        let a = self.expr_bor()?;
        if self.at("..") {
            // `a..` (open) only inside index brackets
            if self.peek_at(1).is_punct("]") {
                return Ok(a);
            }
            self.bump();
            let b = self.expr_bor()?;
            return Ok(self.bin(BinOp::Range, a, b));
        }
        Ok(a)
    }

    fn expr_bor(&mut self) -> PResult<Expr> {
        let mut a = self.expr_bxor()?;
        while self.at("|") {
            self.bump();
            let b = self.expr_bxor()?;
            a = self.bin(BinOp::BOr, a, b);
        }
        Ok(a)
    }

    fn expr_bxor(&mut self) -> PResult<Expr> {
        let mut a = self.expr_band()?;
        while self.at_kw("xor") && !self.peek_at(1).is_punct("=>") && !self.peek_at(1).is_punct(",") {
            self.bump();
            let b = self.expr_band()?;
            a = self.bin(BinOp::BXor, a, b);
        }
        Ok(a)
    }

    fn expr_band(&mut self) -> PResult<Expr> {
        let mut a = self.expr_shift()?;
        while self.at("&") {
            self.bump();
            let b = self.expr_shift()?;
            a = self.bin(BinOp::BAnd, a, b);
        }
        Ok(a)
    }

    fn expr_shift(&mut self) -> PResult<Expr> {
        let mut a = self.expr_add()?;
        loop {
            let op = match self.peek() {
                Tok::Punct("<<") => BinOp::Shl,
                Tok::Punct(">>") => BinOp::Shr,
                Tok::Punct(">>s") => BinOp::Sar,
                _ => return Ok(a),
            };
            self.bump();
            let b = self.expr_add()?;
            a = self.bin(op, a, b);
        }
    }

    fn expr_add(&mut self) -> PResult<Expr> {
        let mut a = self.expr_mul()?;
        loop {
            let op = match self.peek() {
                Tok::Punct("+") => BinOp::Add,
                Tok::Punct("-") => BinOp::Sub,
                Tok::Punct("++") => BinOp::Concat,
                _ => return Ok(a),
            };
            self.bump();
            let b = self.expr_mul()?;
            a = self.bin(op, a, b);
        }
    }

    fn expr_mul(&mut self) -> PResult<Expr> {
        let mut a = self.expr_unary()?;
        loop {
            let op = match self.peek() {
                Tok::Punct("*") => BinOp::Mul,
                Tok::Punct("/") => BinOp::Div,
                Tok::Punct("%") => BinOp::Mod,
                Tok::Punct("/s") => BinOp::SDiv,
                Tok::Punct("%s") => BinOp::SMod,
                _ => return Ok(a),
            };
            self.bump();
            let b = self.expr_unary()?;
            a = self.bin(op, a, b);
        }
    }

    fn expr_unary(&mut self) -> PResult<Expr> {
        let start = self.span();
        let op = match self.peek() {
            Tok::Punct("!") => UnOp::Not,
            Tok::Punct("-") => UnOp::Neg,
            Tok::Punct("~") => UnOp::BNot,
            _ => return self.expr_pow(),
        };
        self.bump();
        let a = self.expr_unary()?;
        Ok(self.mk(ExprKind::Unary(op, Box::new(a)), start))
    }

    fn expr_pow(&mut self) -> PResult<Expr> {
        let a = self.postfix_expr()?;
        if self.eat("^") {
            let b = self.expr_unary()?; // right associative
            return Ok(self.bin(BinOp::Pow, a, b));
        }
        Ok(a)
    }

    pub fn postfix_expr(&mut self) -> PResult<Expr> {
        let start = self.span();
        let mut e = self.primary()?;
        loop {
            if self.at("(") {
                self.bump();
                let args = self.with_struct(true, |p| p.expr_list(")"))?;
                e = self.mk(ExprKind::Call(Box::new(e), args), start);
            } else if self.at("[") {
                self.bump();
                e = self.with_struct(true, |p| p.index_suffix(e, start))?;
            } else if self.at(".") && (self.adjacent_dot() || self.peek_at(1).is_punct("{")) {
                self.bump();
                if self.eat("{") {
                    let mut fs = vec![self.ident()?];
                    while self.eat(",") {
                        fs.push(self.ident()?);
                    }
                    self.expect("}")?;
                    e = self.mk(ExprKind::FieldSet(Box::new(e), fs), start);
                } else {
                    let f = self.ident()?;
                    e = self.mk(ExprKind::Field(Box::new(e), f), start);
                }
            } else if self.at_kw("with") && self.peek_at(1).is_punct("{") {
                self.bump();
                let fields = self.with_struct(true, |p| p.field_inits())?;
                e = self.mk(ExprKind::With(Box::new(e), fields), start);
            } else {
                return Ok(e);
            }
        }
    }

    fn index_suffix(&mut self, e: Expr, start: Span) -> PResult<Expr> {
        let a = self.expr()?;
        if self.eat(":") {
            let b = self.expr()?;
            self.expect("]")?;
            return Ok(self.mk(ExprKind::Slice(Box::new(e), Box::new(a), Box::new(b)), start));
        }
        if self.at("..") && self.peek_at(1).is_punct("]") {
            self.bump();
            self.bump();
            return Ok(self.mk(ExprKind::From(Box::new(e), Box::new(a)), start));
        }
        let mut idx = vec![a];
        while self.eat(",") {
            idx.push(self.expr()?);
        }
        self.expect("]")?;
        Ok(self.mk(ExprKind::Index(Box::new(e), idx), start))
    }

    fn expr_list(&mut self, close: &str) -> PResult<Vec<Expr>> {
        let mut out = Vec::new();
        if self.eat(close) {
            return Ok(out);
        }
        loop {
            out.push(self.expr()?);
            if !self.eat(",") {
                break;
            }
        }
        self.expect(close)?;
        Ok(out)
    }

    /// `{ f: e, g, ... }` (a bare `g` means `g: g`)
    fn field_inits(&mut self) -> PResult<Vec<(Ident, Expr)>> {
        self.expect("{")?;
        let mut out = Vec::new();
        loop {
            self.skip_nl();
            if self.eat("}") {
                break;
            }
            let f = self.ident()?;
            let v = if self.eat(":") {
                self.expr()?
            } else {
                Expr { kind: ExprKind::Name(f.clone()), span: f.span }
            };
            out.push((f, v));
            self.skip_nl();
            if !self.eat(",") {
                self.skip_nl();
                self.expect("}")?;
                break;
            }
        }
        Ok(out)
    }

    fn binder_vars(&mut self) -> PResult<Vec<(Ident, Option<Type>)>> {
        let mut vars = Vec::new();
        loop {
            let v = self.ident()?;
            let t = if self.eat(":") { Some(self.ty()?) } else { None };
            vars.push((v, t));
            if !self.eat(",") {
                break;
            }
        }
        Ok(vars)
    }

    fn primary(&mut self) -> PResult<Expr> {
        let start = self.span();
        let tok = self.peek().clone();
        match tok {
            Tok::Num(n) => {
                self.bump();
                Ok(self.mk(ExprKind::Num(n), start))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(self.mk(ExprKind::Str(s), start))
            }
            Tok::Punct("(") => self.paren_or_lambda(),
            Tok::Punct("[") => {
                self.bump();
                if self.eat("]") {
                    return Ok(self.mk(ExprKind::List(Vec::new()), start));
                }
                let first = self.with_struct(true, |p| p.expr())?;
                if self.eat_kw("for") {
                    let pat = self.pattern()?;
                    self.expect_kw("in")?;
                    let iter = self.with_struct(false, |p| p.expr())?;
                    let cond = if self.eat_kw("if") { Some(Box::new(self.expr()?)) } else { None };
                    self.expect("]")?;
                    return Ok(self.mk(
                        ExprKind::ListComp { elem: Box::new(first), pat, iter: Box::new(iter), cond },
                        start,
                    ));
                }
                let mut items = vec![first];
                while self.eat(",") {
                    items.push(self.expr()?);
                }
                self.expect("]")?;
                Ok(self.mk(ExprKind::List(items), start))
            }
            Tok::Punct("{") => {
                self.bump();
                if self.eat("}") {
                    return Ok(self.mk(ExprKind::Set(Vec::new()), start));
                }
                if matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1).is_punct(":") {
                    let var = self.ident()?;
                    self.expect(":")?;
                    let ty = self.ty()?;
                    self.expect("|")?;
                    let cond = self.with_struct(true, |p| p.expr())?;
                    self.expect("}")?;
                    return Ok(self.mk(ExprKind::SetBuilder { var, ty, cond: Box::new(cond) }, start));
                }
                let items = self.with_struct(true, |p| p.expr_list("}"))?;
                Ok(self.mk(ExprKind::Set(items), start))
            }
            Tok::Ident(s) => match s.as_str() {
                "true" | "false" => {
                    self.bump();
                    Ok(self.mk(ExprKind::Bool(s == "true"), start))
                }
                "self" => {
                    self.bump();
                    Ok(self.mk(ExprKind::SelfState, start))
                }
                "do" => {
                    self.bump();
                    let st = if self.eat("[") {
                        let t = self.ty()?;
                        self.expect("]")?;
                        Some(t)
                    } else {
                        None
                    };
                    let b = self.block()?;
                    Ok(self.mk(ExprKind::Do(st, b), start))
                }
                "with" => {
                    self.bump();
                    let v = self.with_struct(false, |p| p.postfix_expr())?;
                    let b = self.block()?;
                    Ok(self.mk(ExprKind::WithView(Box::new(v), b), start))
                }
                "if" => {
                    self.bump();
                    let c = self.with_struct(false, |p| p.expr())?;
                    let a = self.block()?;
                    if !self.nl_then_kw("else") {
                        return self.err("`if` expression needs `else`");
                    }
                    self.bump();
                    let b = if self.at_kw("if") {
                        let e = self.primary()?;
                        Block { span: e.span, stmts: vec![Stmt { span: e.span, kind: StmtKind::Expr(e) }] }
                    } else {
                        self.block()?
                    };
                    Ok(self.mk(ExprKind::If(Box::new(c), a, Box::new(b)), start))
                }
                "match" => {
                    self.bump();
                    let scrut = self.with_struct(false, |p| p.expr())?;
                    let arms = self.arms()?;
                    Ok(self.mk(ExprKind::Match(Box::new(scrut), arms), start))
                }
                "all" | "ex" => {
                    self.bump();
                    let vars = self.binder_vars()?;
                    self.expect(".")?;
                    let body = self.expr()?;
                    let kind = if s == "all" { BinderKind::All } else { BinderKind::Ex };
                    Ok(self.mk(ExprKind::Binder { kind, vars, domain: None, body: Box::new(body) }, start))
                }
                "sum" => {
                    self.bump();
                    let v = self.ident()?;
                    self.expect_kw("in")?;
                    let dom = self.expr_range()?;
                    self.expect(".")?;
                    let body = self.expr()?;
                    Ok(self.mk(
                        ExprKind::Binder { kind: BinderKind::Sum, vars: vec![(v, None)], domain: Some(Box::new(dom)), body: Box::new(body) },
                        start,
                    ))
                }
                "any" => {
                    self.bump();
                    let maybe = self.eat("?");
                    let var = if matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1).is_punct(":") {
                        let v = self.ident()?;
                        self.expect(":")?;
                        Some(v)
                    } else {
                        None
                    };
                    let ty = self.ty()?;
                    let cond = if self.eat_kw("where") { Some(Box::new(self.expr()?)) } else { None };
                    // (`else` may start the next line)
                    let els = if self.nl_then_kw("else") {
                        self.bump();
                        Some(Box::new(self.block()?))
                    } else {
                        None
                    };
                    if els.is_some() && cond.is_none() {
                        return self.err("`any ... else` needs a `where` condition");
                    }
                    if maybe && els.is_none() {
                        return self.err("`any?` needs an `else` block");
                    }
                    Ok(self.mk(ExprKind::Any { var, ty, cond, maybe, els }, start))
                }
                _ => {
                    let name = self.ident()?;
                    if self.at("{") && !self.no_struct {
                        let fields = self.field_inits()?;
                        return Ok(self.mk(ExprKind::Record { name, fields }, start));
                    }
                    Ok(self.mk(ExprKind::Name(name), start))
                }
            },
            t => self.err(format!("expected an expression, found `{}`", t.text())),
        }
    }

    fn paren_or_lambda(&mut self) -> PResult<Expr> {
        let start = self.span();
        // lambda: `(x: T, ...) =>`
        if matches!(self.peek_at(1), Tok::Ident(_)) && self.peek_at(2).is_punct(":") {
            let mut j = self.pos;
            let mut depth = 0;
            loop {
                match &self.toks[j].tok {
                    Tok::Punct("(") => depth += 1,
                    Tok::Punct(")") => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    Tok::Eof => break,
                    _ => {}
                }
                j += 1;
            }
            if self.toks.get(j + 1).map(|t| t.tok.is_punct("=>")).unwrap_or(false) {
                let params = self.params()?;
                self.expect("=>")?;
                let body = if self.at("{") {
                    self.block()?
                } else {
                    let e = self.expr()?;
                    Block { span: e.span, stmts: vec![Stmt { span: e.span, kind: StmtKind::Expr(e) }] }
                };
                return Ok(self.mk(ExprKind::Lambda(params, Box::new(body)), start));
            }
        }
        self.bump();
        if self.eat(")") {
            return Ok(self.mk(ExprKind::Tuple(Vec::new()), start));
        }
        let first = self.with_struct(true, |p| p.expr())?;
        if self.eat(")") {
            return Ok(Expr { kind: first.kind, span: join(start, self.prev_span()) });
        }
        let mut items = vec![first];
        while self.eat(",") {
            items.push(self.with_struct(true, |p| p.expr())?);
        }
        self.expect(")")?;
        Ok(self.mk(ExprKind::Tuple(items), start))
    }
}

/// Matches a notation pattern at the start of `toks`; returns the number of
/// tokens consumed and the hole substitution.
fn match_notation(pat: &[PatTok], toks: &[Token]) -> Option<(usize, HashMap<String, Vec<Token>>)> {
    let mut subst = HashMap::new();
    let mut i = 0;
    for p in pat {
        let t = toks.get(i)?;
        match p {
            PatTok::Tok(s) => {
                if t.tok.text() != *s || matches!(t.tok, Tok::Str(_)) {
                    return None;
                }
            }
            PatTok::Hole(name, kind) => {
                let ok = match (kind, &t.tok) {
                    (HoleKind::Nat, Tok::Num(_)) => true,
                    (HoleKind::Byte, Tok::Num(n)) => n.to_u64().map(|v| v < 256).unwrap_or(false),
                    (HoleKind::Ident, Tok::Ident(_)) | (HoleKind::Type, Tok::Ident(_)) => true,
                    _ => false,
                };
                if !ok {
                    return None;
                }
                subst.insert(name.clone(), vec![t.clone()]);
            }
        }
        i += 1;
    }
    Some((i, subst))
}

/// Parses one file. `notations` carries notation blocks between files of a module.
pub fn parse_file(
    src: &str,
    file_id: u32,
    notations: &mut HashMap<String, Vec<Notation>>,
) -> Result<File, Vec<ParseError>> {
    let toks = match crate::lexer::lex(src, file_id) {
        Ok(t) => t,
        Err(e) => return Err(vec![ParseError { msg: e.msg, span: e.span }]),
    };
    let mut p = Parser::new(toks, notations);
    match p.file() {
        Ok(f) if p.errors.is_empty() => Ok(f),
        Ok(_) => Err(p.errors),
        Err(e) => {
            let mut errs = p.errors;
            errs.push(e);
            Err(errs)
        }
    }
}
