//! Elaboration of SL into the background logic.

pub mod build;
pub mod decl;
pub mod elab;
pub mod expr;
pub mod globals;
pub mod stmt;
pub mod ty;

pub use elab::{Diag, Elab};

use sl_kernel::{syntax, Env, SymKind};
use sl_syntax::{ast::File, SourceMap};

/// Loads the prelude and elaborates all files.
pub fn elaborate<'s>(prelude: &str, files: Vec<File>, sm: &'s SourceMap) -> Result<Elab<'s>, String> {
    let mut env = Env::new();
    syntax::load(&mut env, prelude, true).map_err(|e| format!("prelude: {}", e))?;
    let g = globals::Globals::build(files)?;
    let mut el = Elab::new(env, g, sm);
    el.run();
    Ok(el)
}

impl<'s> Elab<'s> {
    /// Diagnostics as `file:line:col: message` lines.
    pub fn render_diags(&self) -> Vec<String> {
        self.diags
            .iter()
            .map(|d| format!("{}: {}{}", self.sm.position(d.span), if d.warning { "warning: " } else { "error: " }, d.msg))
            .collect()
    }

    pub fn errors(&self) -> usize {
        self.diags.iter().filter(|d| !d.warning).count()
    }

    /// The elaborated definitions and claims, in core syntax.
    pub fn core_text(&self) -> String {
        let p = syntax::Printer::new(&self.b.env);
        let mut out = String::new();
        out.push_str("// Elaborated by slc. Load after core/prelude.core.\n\n");
        for s in self.prelude_syms..self.b.env.syms.len() {
            if let SymKind::Defined { .. } = self.b.env.syms[s].kind {
                out.push_str(&p.def_line(s as u32).unwrap());
                out.push_str("\n\n");
            }
        }
        for (n, c) in &self.claims {
            out.push_str(&format!("claim {}: {}\n\n", n, p.term(c)));
        }
        out
    }
}
