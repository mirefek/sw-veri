//! A parser for GCC's GIMPLE dumps (`-fdump-tree-optimized`): functions,
//! declarations, basic blocks, phis, statements and expressions, kept close
//! to the text.

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Id(String),
    Num(i128),
    Str(String),
    P(String),
}

pub fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let c: Vec<char> = s.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    let is_id = |ch: char| ch.is_ascii_alphanumeric() || ch == '_' || ch == '$';
    while i < c.len() {
        let ch = c[i];
        if ch.is_whitespace() {
            i += 1;
        } else if ch == '"' {
            let mut j = i + 1;
            let mut t = String::new();
            while j < c.len() && c[j] != '"' {
                if c[j] == '\\' && j + 1 < c.len() {
                    j += 1;
                }
                t.push(c[j]);
                j += 1;
            }
            out.push(Tok::Str(t));
            i = j + 1;
        } else if s[c[..i].iter().collect::<String>().len()..].starts_with("<unnamed-") {
            // <unnamed-unsigned:5>
            let j = (i..c.len()).find(|&j| c[j] == '>').ok_or("unterminated <unnamed-...>")?;
            out.push(Tok::Id(c[i..=j].iter().collect()));
            i = j + 1;
        } else if ch.is_ascii_digit() {
            let mut j = i;
            while j < c.len() && c[j].is_ascii_digit() {
                j += 1;
            }
            let v: i128 = c[i..j].iter().collect::<String>().parse().map_err(|_| "number")?;
            // suffixes: 16B (bytes), 1U, 1UL ...
            while j < c.len() && matches!(c[j], 'B' | 'U' | 'L') {
                j += 1;
            }
            out.push(Tok::Num(v));
            i = j;
        } else if is_id(ch) || (ch == '.' && i + 1 < c.len() && c[i + 1].is_ascii_uppercase() && out.last().map_or(true, |t| !matches!(t, Tok::Id(_)))) {
            // identifiers, including GCC's `p.3_1`, `D.4671`, `mi$len_12`, and `.CTZ`
            let mut j = i + 1;
            while j < c.len() && (is_id(c[j]) || (c[j] == '.' && j + 1 < c.len() && c[j + 1].is_ascii_digit())) {
                j += 1;
            }
            out.push(Tok::Id(c[i..j].iter().collect()));
            i = j;
        } else {
            let two: String = c[i..(i + 2).min(c.len())].iter().collect();
            let p = if ["->", "<<", ">>", "==", "!=", "<=", ">=", "&&", "||"].contains(&two.as_str()) { two } else { ch.to_string() };
            i += p.chars().count();
            out.push(Tok::P(p));
        }
    }
    // `x_3(D)`: a default definition, part of the name
    let mut r: Vec<Tok> = Vec::new();
    let mut k = 0;
    while k < out.len() {
        if let Tok::Id(n) = &out[k] {
            if out.get(k + 1) == Some(&Tok::P("(".into())) && out.get(k + 2) == Some(&Tok::Id("D".into())) && out.get(k + 3) == Some(&Tok::P(")".into())) {
                r.push(Tok::Id(format!("{}(D)", n)));
                k += 4;
                continue;
            }
        }
        r.push(out[k].clone());
        k += 1;
    }
    Ok(r)
}

/// Expressions as they appear in the dump.
#[derive(Clone, Debug)]
pub enum E {
    Name(String),
    Num(i128),
    Addr(Box<E>),
    Deref(Box<E>),
    Field(Box<E>, String),
    Arrow(Box<E>, String),
    Index(Box<E>, Box<E>),
    /// MEM <acc> [(ptr_ty) base + off]
    Mem { acc: Option<String>, ptr_ty: String, base: Box<E>, off: i128 },
    Cast(String, Box<E>),
    Neg(Box<E>),
    Not(Box<E>),
    Bin(String, Box<E>, Box<E>),
    Call(String, Vec<E>),
    /// MIN_EXPR <a, b>, IMAGPART_EXPR <a> ...
    Code(String, Vec<E>),
    /// BIT_FIELD_REF <obj, bits, pos>
    BitRef(Box<E>, u64, u64),
    Ctor(Vec<E>),
}

#[derive(Clone, Debug)]
pub enum S {
    Assign(E, E),
    Call(Option<E>, String, Vec<E>),
    Asm { tmpl: String, outs: Vec<(String, E)>, ins: Vec<(String, E)> },
    Return(Option<E>),
    Goto(u64),
    If { op: String, a: E, b: E, yes: u64, no: u64 },
}

#[derive(Clone, Debug)]
pub struct Phi {
    pub dst: String,
    pub args: Vec<(E, u64)>,
}

#[derive(Clone, Debug, Default)]
pub struct Block {
    pub num: u64,
    pub phis: Vec<Phi>,
    pub stmts: Vec<S>,
}

#[derive(Clone, Debug, Default)]
pub struct Func {
    pub name: String,
    pub ret: String,
    pub params: Vec<(String, String)>,
    /// local declarations: name -> type text (with array dims)
    pub decls: Vec<(String, String)>,
    /// `static` local declarations (global objects)
    pub statics: Vec<(String, String)>,
    pub blocks: Vec<Block>,
}

struct P<'a> {
    t: &'a [Tok],
    i: usize,
}

const BINOPS: &[&str] = &["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "==", "!=", "<", "<=", ">", ">="];

impl<'a> P<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.t.get(self.i)
    }
    fn at(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::P(x)) if x == p)
    }
    fn eat(&mut self, p: &str) -> bool {
        if self.at(p) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.eat(p) { Ok(()) } else { Err(format!("expected `{}` at {:?}", p, self.peek())) }
    }
    fn id(&mut self) -> Result<String, String> {
        match self.peek() {
            Some(Tok::Id(s)) => {
                let s = s.clone();
                self.i += 1;
                Ok(s)
            }
            t => Err(format!("expected a name, got {:?}", t)),
        }
    }
    fn num(&mut self) -> Result<i128, String> {
        let neg = self.eat("-");
        match self.peek() {
            Some(Tok::Num(n)) => {
                let n = *n;
                self.i += 1;
                Ok(if neg { -n } else { n })
            }
            t => Err(format!("expected a number, got {:?}", t)),
        }
    }
    /// the tokens up to the matching `close`, as type text
    fn type_until(&mut self, close: &str) -> Result<String, String> {
        let open = if close == ")" { "(" } else { "<" };
        let mut depth = 0;
        let mut parts = Vec::new();
        loop {
            match self.peek() {
                None => return Err("unterminated type".into()),
                Some(Tok::P(p)) if p == close && depth == 0 => {
                    self.i += 1;
                    return Ok(parts.join(" "));
                }
                Some(t) => {
                    if matches!(t, Tok::P(p) if p == open) {
                        depth += 1;
                    }
                    if matches!(t, Tok::P(p) if p == close) {
                        depth -= 1;
                    }
                    parts.push(match t {
                        Tok::Id(s) | Tok::P(s) => s.clone(),
                        Tok::Num(n) => n.to_string(),
                        Tok::Str(s) => s.clone(),
                    });
                    self.i += 1;
                }
            }
        }
    }
    fn is_type_start(&self) -> bool {
        // `(T) x`: a cast, if `(` starts a type and `)` is followed by an operand
        let words = ["unsigned", "signed", "int", "long", "short", "char", "struct", "union", "const", "void", "_Bool", "sizetype", "volatile", "vector", "complex", "enum"];
        let mut j = self.i + 1;
        let mut depth = 0;
        let mut first = true;
        while let Some(t) = self.t.get(j) {
            match t {
                Tok::P(p) if p == ")" && depth == 0 => {
                    return !first && matches!(self.t.get(j + 1), Some(Tok::Id(_)) | Some(Tok::Num(_)) | Some(Tok::P(_)))
                        && !matches!(self.t.get(j + 1), Some(Tok::P(p)) if p == ";" || p == "," || p == ")" || BINOPS.contains(&p.as_str()) && p != "-" && p != "&" && p != "*");
                }
                Tok::P(p) if p == "(" => depth += 1,
                Tok::P(p) if p == ")" => depth -= 1,
                Tok::Id(s) if first => {
                    if !(words.contains(&s.as_str()) || s.ends_with("_t") || s.starts_with("<unnamed") || s == "T") {
                        return false;
                    }
                }
                Tok::P(p) if first && p != "*" => return false,
                _ => {}
            }
            first = false;
            j += 1;
        }
        false
    }

    fn unary(&mut self) -> Result<E, String> {
        if self.eat("-") {
            if let Some(Tok::Num(n)) = self.peek() {
                let n = *n;
                self.i += 1;
                return Ok(E::Num(-n));
            }
            return Ok(E::Neg(Box::new(self.unary()?)));
        }
        if self.eat("~") {
            return Ok(E::Not(Box::new(self.unary()?)));
        }
        if self.eat("&") {
            return Ok(E::Addr(Box::new(self.postfix()?)));
        }
        if self.eat("*") {
            return Ok(E::Deref(Box::new(self.postfix()?)));
        }
        if self.at("(") && self.is_type_start() {
            self.i += 1;
            let ty = self.type_until(")")?;
            return Ok(E::Cast(ty, Box::new(self.unary()?)));
        }
        self.postfix()
    }

    fn postfix(&mut self) -> Result<E, String> {
        let mut e = self.primary()?;
        loop {
            if self.eat(".") {
                e = E::Field(Box::new(e), self.id()?);
            } else if self.eat("->") {
                e = E::Arrow(Box::new(e), self.id()?);
            } else if self.at("[") {
                self.i += 1;
                let ix = self.unary()?;
                self.expect("]")?;
                e = E::Index(Box::new(e), Box::new(ix));
            } else {
                return Ok(e);
            }
        }
    }

    fn args(&mut self, close: &str) -> Result<Vec<E>, String> {
        let mut v = Vec::new();
        if self.eat(close) {
            return Ok(v);
        }
        loop {
            v.push(self.unary()?);
            if self.eat(close) {
                return Ok(v);
            }
            self.expect(",")?;
        }
    }

    fn primary(&mut self) -> Result<E, String> {
        match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.i += 1;
                Ok(E::Num(n))
            }
            Some(Tok::P(p)) if p == "{" => {
                self.i += 1;
                Ok(E::Ctor(self.args("}")?))
            }
            Some(Tok::P(p)) if p == "(" => {
                self.i += 1;
                let e = self.unary()?;
                self.expect(")")?;
                Ok(e)
            }
            Some(Tok::Id(s)) if s == "MEM" => {
                self.i += 1;
                let acc = if self.eat("<") { Some(self.type_until(">")?) } else { None };
                self.expect("[")?;
                self.expect("(")?;
                let ptr_ty = self.type_until(")")?;
                let base = self.unary()?;
                let off = if self.eat("+") { self.num()? } else { 0 };
                self.expect("]")?;
                Ok(E::Mem { acc, ptr_ty, base: Box::new(base), off })
            }
            Some(Tok::Id(s)) if s == "BIT_FIELD_REF" => {
                self.i += 1;
                self.expect("<")?;
                let o = self.unary()?;
                self.expect(",")?;
                let bits = self.num()? as u64;
                self.expect(",")?;
                let pos = self.num()? as u64;
                self.expect(">")?;
                Ok(E::BitRef(Box::new(o), bits, pos))
            }
            Some(Tok::Id(s)) if s.ends_with("_EXPR") => {
                self.i += 1;
                self.expect("<")?;
                Ok(E::Code(s, self.args(">")?))
            }
            Some(Tok::Id(s)) => {
                self.i += 1;
                if self.at("(") && !s.ends_with("(D)") {
                    self.i += 1;
                    return Ok(E::Call(s, self.args(")")?));
                }
                Ok(E::Name(s))
            }
            t => Err(format!("unexpected {:?}", t)),
        }
    }

    /// right-hand side: `a OP b` or a unary expression
    fn rhs(&mut self) -> Result<E, String> {
        let a = self.unary()?;
        if let Some(Tok::P(p)) = self.peek() {
            if BINOPS.contains(&p.as_str()) {
                let op = p.clone();
                self.i += 1;
                let b = self.unary()?;
                return Ok(E::Bin(op, Box::new(a), Box::new(b)));
            }
        }
        Ok(a)
    }
}

fn parse_with<T>(s: &str, f: impl FnOnce(&mut P) -> Result<T, String>) -> Result<T, String> {
    let toks = lex(s)?;
    let mut p = P { t: &toks, i: 0 };
    let r = f(&mut p)?;
    // allow a trailing `;`
    p.eat(";");
    if p.i != toks.len() {
        return Err(format!("unexpected {:?} in `{}`", &toks[p.i], s.trim()));
    }
    Ok(r)
}

fn bb_num(s: &str) -> Option<u64> {
    let i = s.find("<bb ")?;
    s[i + 4..].split('>').next()?.trim().parse().ok()
}

fn parse_asm(s: &str) -> Result<S, String> {
    // __asm__ __volatile__("tmpl" : "=a" x, "=m" *p : "a" y, "r" z : "memory");
    let toks = lex(s)?;
    let mut p = P { t: &toks, i: 0 };
    while !p.at("(") {
        p.i += 1;
        if p.i >= toks.len() {
            return Err("bad asm".into());
        }
    }
    p.i += 1;
    let tmpl = match p.peek() {
        Some(Tok::Str(t)) => t.clone(),
        t => return Err(format!("asm template expected, got {:?}", t)),
    };
    p.i += 1;
    let mut lists: Vec<Vec<(String, E)>> = Vec::new();
    while p.eat(":") {
        let mut l = Vec::new();
        while let Some(Tok::Str(c)) = p.peek().cloned() {
            p.i += 1;
            // clobbers are strings without an operand
            if p.at(",") || p.at(":") || p.at(")") {
                l.push((c, E::Num(0)));
            } else {
                l.push((c, p.unary()?));
            }
            p.eat(",");
        }
        lists.push(l);
    }
    let outs = lists.first().cloned().unwrap_or_default();
    let ins = lists.get(1).cloned().unwrap_or_default();
    Ok(S::Asm { tmpl, outs, ins })
}

fn parse_stmt(s: &str) -> Result<Option<S>, String> {
    // `={v}`: a volatile access, the same as `=` for a single thread
    let s = s.replace("={v}", "=");
    // `x = {CLOBBER(eos)};`: the end of a local's lifetime, no effect on memory
    if s.contains("{CLOBBER") {
        return Ok(None);
    }
    parse_stmt1(&s).map(Some)
}

fn parse_stmt1(s: &str) -> Result<S, String> {
    let s = s.split(" [tail call]").next().unwrap().trim();
    let s = s.split(" [return slot optimization]").next().unwrap().trim();
    if s.starts_with("__asm__") {
        return parse_asm(s);
    }
    if s == "return;" {
        return Ok(S::Return(None));
    }
    if let Some(r) = s.strip_prefix("return ") {
        return Ok(S::Return(Some(parse_with(r, |p| p.unary())?)));
    }
    if s.starts_with("goto ") {
        return Ok(S::Goto(bb_num(s).ok_or("goto")?));
    }
    parse_with(s, |p| {
        let lhs = p.unary()?;
        if !p.eat("=") {
            return match lhs {
                E::Call(f, args) => Ok(S::Call(None, f, args)),
                e => Err(format!("not a statement: {:?}", e)),
            };
        }
        let rhs = p.rhs()?;
        Ok(match rhs {
            E::Call(f, args) => S::Call(Some(lhs), f, args),
            r => S::Assign(lhs, r),
        })
    })
}

/// Parses all functions of an optimized dump.
pub fn parse_dump(text: &str) -> Result<Vec<Func>, String> {
    let lines: Vec<&str> = text.lines().collect();
    let mut funcs = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if !lines[i].starts_with(";; Function ") {
            i += 1;
            continue;
        }
        // the header line is the one before `{`
        let mut j = i + 1;
        while j < lines.len() && lines[j] != "{" {
            j += 1;
        }
        let header = lines[j - 1];
        let mut f = parse_header(header).map_err(|e| format!("{}: {}", header, e))?;
        j += 1;
        let mut cur: Option<Block> = None;
        while j < lines.len() && lines[j] != "}" {
            let l = lines[j].trim();
            let line_no = j + 1;
            let ctx = |e: String| format!("line {}: `{}`: {}", line_no, l, e);
            let is_label = l.ends_with(':') && !l.contains(' ') && !l.starts_with("<bb");
            if l.is_empty() || l.starts_with("# DEBUG") || l.starts_with("//") || (cur.is_some() && is_label) {
                // labels (from C `goto`s) carry nothing in GIMPLE; comments
                // (branch predictions, in -O0 dumps) neither
            } else if l.starts_with("<bb ") {
                if let Some(b) = cur.take() {
                    f.blocks.push(b);
                }
                cur = Some(Block { num: bb_num(l).ok_or_else(|| ctx("block".into()))?, ..Default::default() });
            } else if cur.is_none() {
                // a declaration: `type name;` or `type name[dims];`, maybe
                // with an initializer: an automatic variable is initialized
                // by statements (the dump just shows it), a `static` one is
                // a global object
                let d = l.trim_end_matches(';');
                let d = d.find(" = ").map_or(d, |k| &d[..k]);
                match d.strip_prefix("static ") {
                    Some(sd) => {
                        let (ty, name) = split_decl(sd).ok_or_else(|| ctx("declaration".into()))?;
                        f.statics.push((name, ty));
                    }
                    None => {
                        let (ty, name) = split_decl(d).ok_or_else(|| ctx("declaration".into()))?;
                        f.decls.push((name, ty));
                    }
                }
            } else if let Some(r) = l.strip_prefix("# ") {
                // # x = PHI <a(3), b(4)>
                let (dst, rest) = r.split_once(" = PHI <").ok_or_else(|| ctx("phi".into()))?;
                let body = rest.trim_end_matches('>');
                let toks = lex(body).map_err(ctx)?;
                let mut p = P { t: &toks, i: 0 };
                let mut args = Vec::new();
                while p.i < toks.len() {
                    let e = p.unary().map_err(ctx)?;
                    // the predecessor block in parentheses: parsed as a call on names, as `(n)` after numbers
                    let (e, b) = match e {
                        E::Call(n, a) => match a.as_slice() {
                            [E::Num(b)] => (E::Name(n), *b as u64),
                            _ => return Err(ctx("phi argument".into())),
                        },
                        other => {
                            p.expect("(").map_err(ctx)?;
                            let b = p.num().map_err(ctx)? as u64;
                            p.expect(")").map_err(ctx)?;
                            (other, b)
                        }
                    };
                    args.push((e, b));
                    p.eat(",");
                }
                cur.as_mut().unwrap().phis.push(Phi { dst: dst.trim().to_string(), args });
            } else if let Some(c) = l.strip_prefix("if (") {
                // if (a OP b) / goto <bb y>; / else / goto <bb n>;
                let cond = c.rsplit_once(')').ok_or_else(|| ctx("if".into()))?.0;
                let e = parse_with(cond, |p| p.rhs()).map_err(ctx)?;
                let (op, a, b) = match e {
                    E::Bin(op, a, b) => (op, *a, *b),
                    _ => return Err(ctx("condition".into())),
                };
                let yes = bb_num(lines[j + 1]).ok_or_else(|| ctx("then".into()))?;
                let no = bb_num(lines[j + 3]).ok_or_else(|| ctx("else".into()))?;
                cur.as_mut().unwrap().stmts.push(S::If { op, a, b, yes, no });
                j += 3;
            } else {
                // a statement may continue on following lines until `;`
                let mut text = l.to_string();
                while !text.trim_end().ends_with(';') && !text.contains("; [") && j + 1 < lines.len() {
                    j += 1;
                    text.push(' ');
                    text.push_str(lines[j].trim());
                }
                if let Some(st) = parse_stmt(&text).map_err(ctx)? {
                    cur.as_mut().unwrap().stmts.push(st);
                }
            }
            j += 1;
        }
        if let Some(b) = cur.take() {
            f.blocks.push(b);
        }
        funcs.push(f);
        i = j;
    }
    Ok(funcs)
}

/// `type name` or `type name[4][3]` -> (type with dims, name)
fn split_decl(d: &str) -> Option<(String, String)> {
    let d = d.trim();
    // array dimensions after the name: the trailing `[...]` groups
    let mut k = d.len();
    while d[..k].ends_with(']') {
        k = d[..k].rfind('[')?;
    }
    let (head, dims) = (&d[..k], &d[k..]);
    let k = head.rfind(|c: char| c == ' ' || c == '*')?;
    let name = head[k + 1..].to_string();
    let ty = format!("{}{}", head[..k + 1].trim(), dims);
    Some((ty.trim().to_string(), name))
}

fn parse_header(h: &str) -> Result<Func, String> {
    // `struct meta * get_meta (const unsigned char * p)`
    let open = h.find(" (").ok_or("no parameter list")?;
    let (head, params) = (&h[..open], &h[open + 2..h.rfind(')').ok_or("no `)`")?]);
    let (ret, name) = split_decl(head).ok_or("bad header")?;
    let mut f = Func { name, ret, ..Default::default() };
    for p in params.split(',').map(str::trim).filter(|p| !p.is_empty() && *p != "void") {
        let (ty, n) = split_decl(p).ok_or("bad parameter")?;
        f.params.push((n, ty));
    }
    Ok(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DUMP: &str = r#"
;; Function f (f, funcdef_no=0, decl_uid=1, cgraph_uid=1, symbol_order=0)

Removing basic block 5
int f (struct meta * m, int i)
{
  struct mapinfo mi;
  int _1;
  <unnamed-unsigned:5> _2;
  unsigned char[0:] * _3;

  <bb 2> [local count: 1073741824]:
  _1 ={v} m_4(D)->avail_mask;
  _2 = m_4(D)->last_idx;
  MEM[(uint16_t *)m_4(D) + -2B] = 0;
  mi = g (m_4(D), i_5(D)); [tail call]
  __asm__ __volatile__("lock ; or %1, %0" : "=m" *_3 : "r" _1 : "memory");
  mi ={v} {CLOBBER(eos)};
  if (_1 != 0)
    goto <bb 3>; [50.00%]
  else
    goto <bb 4>; [50.00%]

  <bb 3> [local count: 1]:
done:
  _6 = BIT_FIELD_REF <*m_4(D), 64, 256>;

  <bb 4> [local count: 1]:
  # _7 = PHI <_1(2), 5(3)>
  return _7;

}
"#;

    #[test]
    fn parses_the_forms_used_by_mallocng() {
        let fs = parse_dump(DUMP).unwrap();
        assert_eq!(fs.len(), 1);
        let f = &fs[0];
        assert_eq!(f.params, vec![("m".into(), "struct meta *".into()), ("i".into(), "int".into())]);
        assert!(f.decls.iter().any(|(n, t)| n == "_3" && t == "unsigned char[0:] *"));
        assert_eq!(f.blocks.len(), 3);
        // volatile read, bitfield read, store, struct call, asm (the clobber is dropped), if
        assert_eq!(f.blocks[0].stmts.len(), 6);
        assert!(matches!(&f.blocks[0].stmts[2], S::Assign(E::Mem { off: -2, .. }, E::Num(0))));
        assert!(matches!(&f.blocks[0].stmts[3], S::Call(Some(E::Name(n)), g, a) if n == "mi" && g == "g" && a.len() == 2));
        assert!(matches!(&f.blocks[0].stmts[4], S::Asm { outs, ins, .. } if outs.len() == 1 && ins.len() == 1));
        assert!(matches!(&f.blocks[0].stmts[5], S::If { yes: 3, no: 4, .. }));
        // the label is skipped
        assert!(matches!(&f.blocks[1].stmts[0], S::Assign(_, E::BitRef(_, 64, 256))));
        assert_eq!(f.blocks[2].phis[0].args.len(), 2);
        assert!(matches!(&f.blocks[2].phis[0].args[1], (E::Num(5), 3)));
    }

    #[test]
    fn lexes_gcc_names() {
        let t = lex("p.3_1 = .CTZ (mi$len_12, 32); x_2(D)").unwrap();
        assert_eq!(t[0], Tok::Id("p.3_1".into()));
        assert_eq!(t[2], Tok::Id(".CTZ".into()));
        assert_eq!(t[4], Tok::Id("mi$len_12".into()));
        assert_eq!(t[t.len() - 1], Tok::Id("x_2(D)".into()));
    }
}
