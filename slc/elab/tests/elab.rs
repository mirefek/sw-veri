//! Elaborator tests: the real spec, and small programs that must be rejected.

use sl_elab::elaborate;
use sl_syntax::{collect_files, parse_files, SourceMap};
use std::path::{Path, PathBuf};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn prelude() -> String {
    std::fs::read_to_string(repo().join("core/prelude.core")).unwrap()
}

#[test]
fn spec_and_layers_elaborate_and_recheck() {
    let paths = collect_files(&[repo().join("spec"), repo().join("layers")]).unwrap();
    let mut sm = SourceMap::default();
    let (files, diags) = parse_files(&mut sm, &paths);
    assert!(diags.is_empty());
    let el = elaborate(&prelude(), files, &sm).unwrap();
    for d in el.render_diags() {
        eprintln!("{}", d);
    }
    assert_eq!(el.errors(), 0);
    // the kernel re-reads the printed definitions
    let mut env = sl_kernel::Env::new();
    sl_kernel::syntax::load(&mut env, &prelude(), true).unwrap();
    let rep = sl_kernel::syntax::load(&mut env, &el.core_text(), false).unwrap();
    assert!(rep.defs > 300);
    assert_eq!(rep.claims, vec!["abi.call_rule".to_string(), "abi.call_rule_at".to_string()]);
    // labelled conjuncts (`name: P`) carried into the definitions
    let wm = el.core_text().lines().find(|l| l.starts_with("def abi.world_matches(")).unwrap().to_string();
    assert!(wm.contains(" := ((((top: ") && wm.contains("&& bytes: (all"), "{}", wm);
}

/// Elaborates one module (with a minimal state) and returns the error messages.
fn errors_of(src: &str) -> Vec<String> {
    let mut sm = SourceMap::default();
    let dir = std::env::temp_dir().join(format!("slc-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("t{}.sl", src.len()));
    std::fs::write(&path, src).unwrap();
    let (files, diags) = parse_files(&mut sm, &[path]);
    assert!(diags.is_empty(), "{:?}", diags);
    let el = elaborate(&prelude(), files, &sm).unwrap();
    el.diags.iter().filter(|d| !d.warning).map(|d| d.msg.clone()).collect()
}

const HEADER: &str = "spec t\nstate S { x: bits[8], y: nat, b: bool }\n";

#[test]
fn accepts_a_small_program() {
    let e = errors_of(&format!("{}proc p() {{ x := x + 1; if b {{ y := y * 2 }} }}\n", HEADER));
    assert!(e.is_empty(), "{:?}", e);
}

#[test]
fn rejects_literal_width_mismatch() {
    let e = errors_of(&format!("{}proc p() {{ x := bits[16](1) }}\n", HEADER));
    assert!(e.iter().any(|m| m.contains("width mismatch")), "{:?}", e);
}

#[test]
fn rejects_bool_into_bits() {
    let e = errors_of(&format!("{}proc p() {{ x := b }}\n", HEADER));
    assert!(e.iter().any(|m| m.contains("cannot assign")), "{:?}", e);
}

#[test]
fn rejects_nondeterminism_in_functions() {
    let e = errors_of(&format!("{}fn f() -> nat = any nat\n", HEADER));
    assert!(e.iter().any(|m| m.contains("only in procedures")), "{:?}", e);
}

#[test]
fn rejects_program_as_number() {
    let e = errors_of(&format!("{}proc q() -> nat = 1\nfn f() -> nat = q()\n", HEADER));
    assert!(e.iter().any(|m| m.contains("returns nat")), "{:?}", e);
}

#[test]
fn ghost_fields_need_ghost_statements() {
    let src = "layer g\nstate S { x: nat }\nstate T extends S { ghost h: nat }\n\
               proc[T] bad() { h := 1 }\nproc[T] good() { ghost h := 1 }\nproc[T] bad2() { ghost x := 1 }\n";
    let e = errors_of(src);
    assert!(e.iter().any(|m| m.contains("needs `ghost`")), "{:?}", e);
    assert!(e.iter().any(|m| m.contains("non-ghost")), "{:?}", e);
    assert_eq!(e.len(), 2, "{:?}", e);
}

#[test]
fn rejects_recursion() {
    let e = errors_of(&format!("{}fn f(n: nat) -> nat = f(n)\n", HEADER));
    assert!(e.iter().any(|m| m.contains("in terms of itself")), "{:?}", e);
}

#[test]
fn rejects_non_boolean_conditions() {
    // a binder's body extends as far as possible: this sums booleans
    let e = errors_of(&format!("{}fn f(x: nat) -> bool = if sum i in 0..4. i != x {{ true }} else {{ false }}\n", HEADER));
    assert!(e.iter().any(|m| m.contains("expected nat, got bool")), "{:?}", e);
}

/// A GIMPLE program written in the GIMPLE layer, and the statement that
/// machine code implements it, elaborate with the real spec and layers.
#[test]
fn gimple_programs_elaborate() {
    // musl's `void free (void *p) { __libc_free (p); [tail call] }`
    let example = r#"layer gimple_example uses gimple, abi, x86_64_linux

fn p64() -> Ty = Ty { prec: 64, signed: false }

fn free_gimple() -> Function = Function {
  params: [(0, p64())],
  types:  (x: Name) => p64(),
  objs:   [],
  blocks: [Block { phis: [], body: [call([], 0, [(ssa(0), p64())])], jump: ret([]) }],
  entry:  0
}

// the machine code at free_at implements it, if __libc_free (callee 0) is `libc_free`
pred free_compiled(free_at: Addr, libc_free: CFun2[World]) =
  implements2(free_at, gimple_fun(free_gimple(), (k: nat) => libc_free))
"#;
    let dir = std::env::temp_dir().join(format!("slc-gimple-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let extra = dir.join("gimple_example.sl");
    std::fs::write(&extra, example).unwrap();
    let mut paths = collect_files(&[repo().join("spec"), repo().join("layers")]).unwrap();
    paths.push(extra);
    let mut sm = SourceMap::default();
    let (files, diags) = parse_files(&mut sm, &paths);
    assert!(diags.is_empty(), "{:?}", diags);
    let el = elaborate(&prelude(), files, &sm).unwrap();
    let errs: Vec<String> = el.render_diags();
    assert_eq!(el.errors(), 0, "{:?}", errs);
    let mut env = sl_kernel::Env::new();
    sl_kernel::syntax::load(&mut env, &prelude(), true).unwrap();
    sl_kernel::syntax::load(&mut env, &el.core_text(), false).unwrap();
}

#[test]
fn havoc_and_any_take_an_else() {
    let ok = format!(
        "{}proc p() -> nat {{\n  havoc y where y > 3 else {{ y := 0 }}\n  havoc? x where x != 0 else {{ b := false }}\n  \
         let a = any nat where a > y else {{ return 0 }}\n  let c = any? nat where c < a else {{ return 1 }}\n  return c\n}}\n",
        HEADER
    );
    let e = errors_of(&ok);
    assert!(e.is_empty(), "{:?}", e);
    // the else of `let x = any` must leave: x would be unbound after it
    let e = errors_of(&format!("{}proc p() -> nat {{\n  let a = any nat where a > y else {{ y := 0 }}\n  return a\n}}\n", HEADER));
    assert!(e.iter().any(|m| m.contains("must end with `return` or `raise`")), "{:?}", e);
    // only as a `let`
    let e = errors_of(&format!("{}proc p() {{ y := any nat where y > 1 else {{ return }} }}\n", HEADER));
    assert!(e.iter().any(|m| m.contains("only in `let x = any")), "{:?}", e);
}
