//! The kernel-check cache's identities of the checker's parts (see
//! `commands.rs`, `Cache`): a hash of each part's sources -- the trusted
//! kernel with the cache's own format, the proof scripts' automation, the
//! C1 engine. A part's change invalidates the entries that rest on it, and
//! only those.

use std::hash::{Hash, Hasher};
use std::path::Path;

fn hash_tree(paths: &[&str]) -> String {
    hash_tree_but(paths, &[])
}

/// the sources under `paths` but those under `but`
fn hash_tree_but(paths: &[&str], but: &[&str]) -> String {
    let mut files = Vec::new();
    for p in paths {
        println!("cargo:rerun-if-changed={}", p);
        collect(Path::new(p), &mut files);
    }
    files.retain(|f| !but.iter().any(|b| f.starts_with(b)));
    files.sort();
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for f in files {
        f.to_string_lossy().hash(&mut h);
        std::fs::read(&f).unwrap_or_default().hash(&mut h);
    }
    format!("{:016x}", h.finish())
}

fn collect(p: &Path, out: &mut Vec<std::path::PathBuf>) {
    if p.is_dir() {
        if let Ok(rd) = std::fs::read_dir(p) {
            for e in rd.flatten() {
                collect(&e.path(), out);
            }
        }
    } else if p.extension().is_some_and(|x| x == "rs") {
        out.push(p.to_path_buf());
    }
}

fn main() {
    println!("cargo:rustc-env=SLC_ID_KERNEL={}", hash_tree(&["../kernel/src", "src/commands.rs"]));
    println!("cargo:rustc-env=SLC_ID_PROOF={}", hash_tree(&["../proof/src"]));
    // (the engines of src/c1, each its own: `c1` lines the C1 engine (all
    // but gref and contract), `refines` lines gref (all but contract: it
    // uses the C1 engine's terms and reducer, and the structuring its cut
    // points come from), `contract` lines contract.rs and the dispatch)
    println!("cargo:rustc-env=SLC_ID_C1={}", hash_tree_but(&["src/c1"], &["src/c1/gref.rs", "src/c1/gref", "src/c1/contract.rs"]));
    println!("cargo:rustc-env=SLC_ID_GREF={}", hash_tree_but(&["src/c1", "src/gimple/structure.rs"], &["src/c1/contract.rs"]));
    println!("cargo:rustc-env=SLC_ID_CONTRACT={}", hash_tree(&["src/c1/contract.rs", "src/c1/mod.rs"]));
}
