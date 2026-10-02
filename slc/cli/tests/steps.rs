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
    assert!(c.status.success() && out.contains("proofs/x86.core: 0 constants, 0 axioms, 1 definitions, 20 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
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

/// C1 for get_slot_index, upgradelock, resetlock and a_ctz_32: their
/// machine code implements their readable GIMPLE under the ABI
/// (`gsi.implements`, `ug.implements`, `rl.implements`, `ac.implements`),
/// resting only on the open loop lemmas. Needs the -O0 build and its readable GIMPLE
/// (`slc gimple --readable`).
#[test]
fn get_slot_index_implements_its_gimple() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let (elf, claim, sl) = (root.join("build/test_malloc_O0"), root.join("build/musl_malloc_O0.core"), root.join("build/gimple-O0/sl/c_mallocng_malloc.sl"));
    if !elf.exists() || !claim.exists() || !sl.exists() {
        eprintln!("skipped: run scripts/build-musl.sh -O0 and slc gimple --readable first");
        return;
    }
    let slc = env!("CARGO_BIN_EXE_slc");
    let tmp = std::env::temp_dir();
    let (steps, gimple) = (tmp.join(format!("slc-gsi-steps-{}.core", std::process::id())), tmp.join(format!("slc-gsi-gimple-{}.core", std::process::id())));
    let g = Command::new(slc).current_dir(&root).args(["steps"]).arg(&elf).arg(&claim).args(["get_slot_index", "upgradelock", "resetlock", "a_ctz_32", "is_bouncing", "get_stride", "step_seq", "-o"]).arg(&steps).output().unwrap();
    assert!(g.status.success(), "{}", String::from_utf8_lossy(&g.stderr));
    let e = Command::new(slc).current_dir(&root).args(["elab", "spec", "layers"]).arg(&sl).arg("-o").arg(&gimple).output().unwrap();
    assert!(e.status.success(), "{}", String::from_utf8_lossy(&e.stderr));
    let c = Command::new(slc)
        .current_dir(&root)
        .args(["kernel-check", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core", "core/list.core", "core/loop.core"])
        .arg(&gimple)
        .args(["proofs/x86.core", "proofs/x86_code.core"])
        .arg(&steps)
        .args([
            "proofs/get_slot_index_run.core",
            "proofs/abi.core",
            "proofs/abi_restore.core",
            "proofs/abi_glue.core",
            "proofs/gimple.core",
            "proofs/get_slot_index.core",
            "proofs/abi_stack.core",
            "proofs/get_slot_index_abi.core",
            "proofs/abi_loop.core",
            "proofs/abi_bridge.core",
            "proofs/upgradelock.core",
            "proofs/resetlock.core",
            "proofs/a_ctz_32.core",
            "proofs/is_bouncing.core",
            "proofs/get_stride.core",
        ])
        .output()
        .unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    assert!(
        c.status.success()
            && checked.contains("get_slot_index_abi.core: 0 constants, 0 axioms, 0 definitions, 0 theorems, 1 conditional theorems, 0 open lemmas")
            && checked.contains("upgradelock.core: 0 constants, 0 axioms, 0 definitions, 1 theorems, 2 conditional theorems")
            && checked.contains("resetlock.core: 0 constants, 0 axioms, 0 definitions, 2 theorems, 3 conditional theorems")
            && checked.contains("abi_stack.core: 0 constants, 0 axioms, 0 definitions, 8 theorems, 0 conditional theorems")
            && checked.contains("a_ctz_32.core: 0 constants, 0 axioms, 0 definitions, 6 theorems, 3 conditional theorems")
            && checked.contains("is_bouncing.core: 0 constants, 0 axioms, 0 definitions, 4 theorems, 3 conditional theorems")
            && checked.contains("get_stride.core: 0 constants, 0 axioms, 0 definitions, 11 theorems, 2 conditional theorems")
            && checked.contains("lemma while_unroll: open"),
        "{}{}",
        checked,
        String::from_utf8_lossy(&c.stderr)
    );
    let _ = std::fs::remove_file(&steps);
    let _ = std::fs::remove_file(&gimple);
}
