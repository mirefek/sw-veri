//! End to end: translate musl's optimized GIMPLE for mallocng/free.c and
//! elaborate it with the GIMPLE layer. Needs the artifacts of
//! `scripts/dump-gimple.sh` (and the musl build); skipped without them.

use std::path::Path;
use std::process::Command;

#[test]
fn mallocng_free_translates_and_elaborates() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let g = root.join("build/gimple");
    let (dump, obj, elf) = (g.join("src_malloc_mallocng_free.c.optimized"), g.join("src_malloc_mallocng_free.c.o"), root.join("build/test_malloc"));
    if !dump.exists() || !obj.exists() || !elf.exists() {
        eprintln!("skipped: run scripts/dump-gimple.sh src/malloc/mallocng/free.c first");
        return;
    }
    let out = std::env::temp_dir().join(format!("slc-gimple-free-{}.sl", std::process::id()));
    let slc = env!("CARGO_BIN_EXE_slc");
    let t = Command::new(slc)
        .args(["gimple", "--elf"]).arg(&elf).arg("--obj").arg(&obj).args(["--source", "free.c"]).arg(&dump).arg("-o").arg(&out)
        .output()
        .unwrap();
    assert!(t.status.success(), "{}{}", String::from_utf8_lossy(&t.stdout), String::from_utf8_lossy(&t.stderr));
    let c = Command::new(slc).current_dir(&root).args(["check", "spec", "layers"]).arg(&out).output().unwrap();
    let text = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && text.contains(" 0 errors"), "{}{}", text, String::from_utf8_lossy(&c.stderr));
    let _ = std::fs::remove_file(&out);
}
