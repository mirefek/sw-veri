//! The mallocng invariant on real heaps (`slc heapcheck`): the checker finds
//! corruptions it is shown (self-test), and the invariant holds on a short
//! stress run. Needs `build/stress_malloc`, built with musl:
//!   build/musl/bin/musl-gcc -static -O2 -o build/stress_malloc tests/stress_malloc.c
//! Slow (three or four minutes): `cargo test --release -- --ignored`.

fn heapcheck(args: &[&str]) -> (bool, String) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let o = std::process::Command::new(env!("CARGO_BIN_EXE_slc"))
        .arg("heapcheck")
        .args(args)
        .current_dir(&root)
        .output()
        .expect("run slc heapcheck");
    (o.status.success(), format!("{}\n{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr)))
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
#[ignore]
fn the_checker_reports_corruptions() {
    let (ok, out) = heapcheck(&["--selftest", "build/stress_malloc", "20"]);
    assert!(ok && out.contains("selftest passed"), "{}", out);
}

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
#[ignore]
fn the_invariant_holds_on_a_short_run() {
    let (ok, out) = heapcheck(&["--every", "5", "build/stress_malloc", "40"]);
    assert!(ok && !out.contains("FAIL"), "{}", out);
}
