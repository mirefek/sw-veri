//! Differential test: every testable row of the spec's instruction table is
//! executed on this CPU and by the spec interpreter, on sampled inputs
//! (`slc cputest`). The rows and their encodings come from the spec, so the
//! test follows spec changes. Run with more samples by hand:
//! `slc cputest --n 200 [--rows K,..] [--seed S] [--verbose]`.

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn spec_agrees_with_cpu() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let o = std::process::Command::new(env!("CARGO_BIN_EXE_slc"))
        .args(["cputest", "--n", "40", "--limits", "tests/cputest-limits.txt"])
        .current_dir(&root)
        .output()
        .expect("run slc cputest");
    let out = String::from_utf8_lossy(&o.stdout);
    assert!(o.status.success(), "{}\n{}", out, String::from_utf8_lossy(&o.stderr));
}
