//! Lexer.
//!
//! Newlines: a `Newline` token is produced at the end of a line when
//! (1) the innermost open bracket is a `{` (or there is none), and
//! (2) the last token can end a statement: a name, a literal, `)`, `]`, `}`.
//! So a line ending in an operator or `,` continues, and newlines inside
//! `(...)` and `[...]` never end anything.
//!
//! Signed operators `<s <=s >s >=s /s %s >>s` are single tokens when the `s`
//! is not followed by a name character (write `a /s b`, but `a / s`).

use crate::ast::Span;
use sl_kernel::Nat;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Num(Nat),
    Str(String),
    Punct(&'static str),
    Newline,
    Eof,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct LexError {
    pub msg: String,
    pub span: Span,
}

const PUNCTS: &[&str] = &[
    ">>s", "<=s", ">=s", "<->", "...", ":=", "=>", "~>", "->", "<=", ">=", "<s", ">s", "/s", "%s", "==", "!=", "&&", "||",
    "++", "<<", ">>", "..", "(", ")", "[", "]", "{", "}", ",", ";", ":", ".", "=", "<", ">", "+", "-", "*", "/", "%",
    "^", "&", "|", "!", "~", "?", "@",
];

fn is_name_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

pub fn lex(src: &str, file: u32) -> Result<Vec<Token>, LexError> {
    let b = src.as_bytes();
    let mut out: Vec<Token> = Vec::new();
    let mut stack: Vec<u8> = Vec::new(); // open brackets
    let mut i = 0usize;
    let span = |lo: usize, hi: usize| Span { file, lo: lo as u32, hi: hi as u32 };
    let ends_stmt = |t: &Tok| match t {
        Tok::Ident(_) | Tok::Num(_) | Tok::Str(_) => true,
        Tok::Punct(p) => matches!(*p, ")" | "]" | "}"),
        _ => false,
    };
    while i < b.len() {
        let c = b[i];
        if c == b'\n' {
            let brace_ctx = matches!(stack.last(), None | Some(b'{'));
            if brace_ctx && out.last().map(|t| ends_stmt(&t.tok)).unwrap_or(false) {
                out.push(Token { tok: Tok::Newline, span: span(i, i + 1) });
            }
            i += 1;
            continue;
        }
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'/' && b.get(i + 1) == Some(&b'/') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        if c.is_ascii_digit() {
            while i < b.len() && is_name_char(b[i]) {
                i += 1;
            }
            let s = &src[start..i];
            let n = Nat::parse(s).ok_or_else(|| LexError { msg: format!("bad number `{}`", s), span: span(start, i) })?;
            out.push(Token { tok: Tok::Num(n), span: span(start, i) });
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            while i < b.len() && is_name_char(b[i]) {
                i += 1;
            }
            out.push(Token { tok: Tok::Ident(src[start..i].to_string()), span: span(start, i) });
            continue;
        }
        if c == b'"' {
            i += 1;
            let mut s = String::new();
            while i < b.len() && b[i] != b'"' {
                if b[i] == b'\\' && i + 1 < b.len() {
                    s.push(match b[i + 1] {
                        b'n' => '\n',
                        other => other as char,
                    });
                    i += 2;
                } else {
                    s.push(b[i] as char);
                    i += 1;
                }
            }
            if i >= b.len() {
                return Err(LexError { msg: "unterminated string".into(), span: span(start, i) });
            }
            i += 1;
            out.push(Token { tok: Tok::Str(s), span: span(start, i) });
            continue;
        }
        let mut matched = None;
        for p in PUNCTS {
            if src[i..].starts_with(p) {
                // signed operators: the `s` must not start a name
                if p.len() >= 2 && p.ends_with('s') && b.get(i + p.len()).map(|&c| is_name_char(c)).unwrap_or(false) {
                    continue;
                }
                matched = Some(*p);
                break;
            }
        }
        let p = match matched {
            Some(p) => p,
            None => {
                // non-ASCII (e.g. a stray Unicode operator) or unknown character
                let ch = src[i..].chars().next().unwrap();
                return Err(LexError { msg: format!("unexpected character `{}`", ch), span: span(i, i + ch.len_utf8()) });
            }
        };
        match p {
            "(" | "[" | "{" => stack.push(p.as_bytes()[0]),
            ")" | "]" | "}" => {
                stack.pop();
            }
            _ => {}
        }
        i += p.len();
        out.push(Token { tok: Tok::Punct(p), span: span(start, i) });
    }
    out.push(Token { tok: Tok::Newline, span: span(b.len(), b.len()) });
    out.push(Token { tok: Tok::Eof, span: span(b.len(), b.len()) });
    Ok(out)
}

impl Tok {
    pub fn is_punct(&self, p: &str) -> bool {
        matches!(self, Tok::Punct(q) if *q == p)
    }
    pub fn is_ident(&self, s: &str) -> bool {
        matches!(self, Tok::Ident(q) if q == s)
    }
    /// Source-like rendering (for notation patterns and messages).
    pub fn text(&self) -> String {
        match self {
            Tok::Ident(s) => s.clone(),
            Tok::Num(n) => n.to_string(),
            Tok::Str(s) => format!("{:?}", s),
            Tok::Punct(p) => p.to_string(),
            Tok::Newline => "newline".into(),
            Tok::Eof => "end of file".into(),
        }
    }
}
