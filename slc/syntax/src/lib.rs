//! SL surface syntax: lexer, AST, parser, source map.

pub mod ast;
pub mod lexer;
pub mod parser;

use ast::{File, Notation, Span};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// All loaded source files, for turning spans into `file:line:col`.
#[derive(Default)]
pub struct SourceMap {
    pub files: Vec<(PathBuf, String)>,
}

impl SourceMap {
    pub fn add(&mut self, path: PathBuf, text: String) -> u32 {
        self.files.push((path, text));
        (self.files.len() - 1) as u32
    }

    pub fn position(&self, span: Span) -> String {
        match self.files.get(span.file as usize) {
            None => "<unknown>".into(),
            Some((path, text)) => {
                let lo = (span.lo as usize).min(text.len());
                let line = text[..lo].matches('\n').count() + 1;
                let col = lo - text[..lo].rfind('\n').map(|i| i + 1).unwrap_or(0) + 1;
                format!("{}:{}:{}", path.display(), line, col)
            }
        }
    }

    pub fn snippet(&self, span: Span) -> &str {
        match self.files.get(span.file as usize) {
            None => "",
            Some((_, text)) => &text[(span.lo as usize).min(text.len())..(span.hi as usize).min(text.len())],
        }
    }
}

/// A parse error with its position.
#[derive(Debug)]
pub struct Diagnostic {
    pub pos: String,
    pub msg: String,
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}: {}", self.pos, self.msg)
    }
}

/// Collects `*.sl` files under the given paths (files or directories),
/// sorted for a deterministic order.
pub fn collect_files(paths: &[PathBuf]) -> std::io::Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    fn walk(p: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        if p.is_dir() {
            let mut entries: Vec<_> = std::fs::read_dir(p)?.filter_map(|e| e.ok().map(|e| e.path())).collect();
            entries.sort();
            for e in entries {
                walk(&e, out)?;
            }
        } else if p.extension().map(|e| e == "sl").unwrap_or(false) {
            out.push(p.to_path_buf());
        }
        Ok(())
    }
    for p in paths {
        walk(p, &mut out)?;
    }
    Ok(out)
}

/// Parses files, sharing notation blocks across them in order.
pub fn parse_files(sm: &mut SourceMap, paths: &[PathBuf]) -> (Vec<File>, Vec<Diagnostic>) {
    let mut notations: HashMap<String, Vec<Notation>> = HashMap::new();
    let mut files = Vec::new();
    let mut diags = Vec::new();
    for p in paths {
        let text = match std::fs::read_to_string(p) {
            Ok(t) => t,
            Err(e) => {
                diags.push(Diagnostic { pos: p.display().to_string(), msg: e.to_string() });
                continue;
            }
        };
        let id = sm.add(p.clone(), text);
        let src = sm.files[id as usize].1.clone();
        match parser::parse_file(&src, id, &mut notations) {
            Ok(f) => files.push(f),
            Err(errs) => {
                for e in errs {
                    diags.push(Diagnostic { pos: sm.position(e.span), msg: e.msg });
                }
            }
        }
    }
    (files, diags)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    #[test]
    fn parses_all_spec_and_layer_files() {
        let paths = collect_files(&[repo().join("spec"), repo().join("layers")]).unwrap();
        assert!(paths.len() >= 7);
        let mut sm = SourceMap::default();
        let (files, diags) = parse_files(&mut sm, &paths);
        for d in &diags {
            eprintln!("{}", d);
        }
        assert!(diags.is_empty(), "{} parse errors", diags.len());
        assert_eq!(files.len(), paths.len());
    }

    #[test]
    fn newline_rules() {
        let src = "spec t\nfn f(a: nat, b: nat) -> nat =\n  a +\n  b\nfn g(a: nat) -> nat = h(a,\n  a)\n";
        let mut n = HashMap::new();
        let f = parser::parse_file(src, 0, &mut n).unwrap();
        assert_eq!(f.decls.len(), 2);
    }

    #[test]
    fn binder_dot_vs_field_dot() {
        let src = "spec t\npred p(v: nat) = ex q: nat. q.x = v.y\n";
        let mut n = HashMap::new();
        let f = parser::parse_file(src, 0, &mut n).unwrap();
        assert_eq!(f.decls.len(), 1);
    }
}
