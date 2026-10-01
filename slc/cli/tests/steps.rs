//! `slc steps`: the step theorems of get_slot_index (-O0 build) are
//! generated and prove. Needs `scripts/build-musl.sh -O0`; skipped without.

use std::path::Path;
use std::process::Command;

/// The facts about the x86 model (proofs/x86.core) check, among them that
/// the closed-form memory write means the same as the byte loop.
#[test]
fn x86_model_facts_check() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let claim = root.join("build/musl_malloc_O0.core");
    if !claim.exists() {
        eprintln!("skipped: run scripts/build-musl.sh -O0 first");
        return;
    }
    let c = Command::new(env!("CARGO_BIN_EXE_slc"))
        .current_dir(&root)
        .args(["kernel-check", "core/prelude.core", "core/logic.core", "core/sets.core", "core/records.core"])
        .arg(&claim)
        .arg("proofs/x86.core")
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && out.contains("proofs/x86.core: 0 constants, 0 axioms, 0 definitions, 10 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
}

/// Loaded code (proofs/x86_code.core): fetched, and kept by every access
/// and store of the program (stack growth maps only unmapped pages).
#[test]
fn loaded_code_facts_check() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let claim = root.join("build/musl_malloc_O0.core");
    if !claim.exists() {
        eprintln!("skipped: run scripts/build-musl.sh -O0 first");
        return;
    }
    let c = Command::new(env!("CARGO_BIN_EXE_slc"))
        .current_dir(&root)
        .args(["kernel-check", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core"])
        .arg(&claim)
        .args(["proofs/x86.core", "proofs/x86_code.core"])
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && out.contains("proofs/x86_code.core: 0 constants, 0 axioms, 0 definitions, 38 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
}

#[test]
fn step_theorems_of_get_slot_index_prove() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let (elf, claim) = (root.join("build/test_malloc_O0"), root.join("build/musl_malloc_O0.core"));
    if !elf.exists() || !claim.exists() {
        eprintln!("skipped: run scripts/build-musl.sh -O0 first");
        return;
    }
    let out = std::env::temp_dir().join(format!("slc-steps-{}.core", std::process::id()));
    let slc = env!("CARGO_BIN_EXE_slc");
    let g = Command::new(slc).current_dir(&root).args(["steps"]).arg(&elf).arg(&claim).args(["get_slot_index", "-o"]).arg(&out).output().unwrap();
    let msg = String::from_utf8_lossy(&g.stdout);
    assert!(g.status.success() && msg.contains("7 instructions, 7 distinct encodings, 7 theorems, 7 outcomes"), "{}{}", msg, String::from_utf8_lossy(&g.stderr));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(text.contains("theorem x86.step_4883e803(m, o)"), "{}", text);
    // the outcome of `ret`: rip from the stack, rsp past it
    assert!(text.contains("theorem get_slot_index.ok_40211a"), "{}", text);
    let c = Command::new(slc)
        .current_dir(&root)
        .args(["kernel-check", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core", "core/loop.core"])
        .arg(&claim)
        .args(["proofs/x86.core", "proofs/x86_code.core"])
        .arg(&out)
        .args(["proofs/get_slot_index_run.core"])
        .output()
        .unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // 7 step theorems, and per instruction where a step from it goes and
    // its outcome; the function's run from them (resting on the open lemma
    // while_unroll: the loop of run_to_return is unrolled)
    assert!(
        c.status.success()
            && checked.contains("1 definitions, 21 theorems")
            && checked.contains("get_slot_index_run.core: 0 constants, 0 axioms, 0 definitions, 0 theorems, 1 conditional theorems"),
        "{}{}",
        checked,
        String::from_utf8_lossy(&c.stderr)
    );
    let _ = std::fs::remove_file(&out);
}
