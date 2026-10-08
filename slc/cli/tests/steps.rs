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
        .args(["kernel-check", "--no-cache", "core/prelude.core", "core/logic.core", "core/sets.core", "core/records.core"])
        .arg(&claim)
        .arg("proofs/x86.core")
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && out.contains("proofs/x86.core: 0 constants, 0 axioms, 1 definitions, 25 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
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
        .args(["kernel-check", "--no-cache", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core"])
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
    assert!(g.status.success() && msg.contains("7 instructions, 7 distinct encodings, 7 theorems"), "{}{}", msg, String::from_utf8_lossy(&g.stderr));
    let text = std::fs::read_to_string(&out).unwrap();
    assert!(text.contains("theorem x86.step_4883e803(m, o)"), "{}", text);
    // the decode fact of `ret`
    assert!(text.contains("theorem get_slot_index.at_40211a"), "{}", text);
    let c = Command::new(slc)
        .current_dir(&root)
        .args(["kernel-check", "--no-cache", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core", "core/loop.core"])
        .arg(&claim)
        .args(["proofs/x86.core", "proofs/x86_code.core"])
        .arg(&out)
        .output()
        .unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // 7 step theorems, and per instruction where a step from it goes
    assert!(
        c.status.success() && checked.contains("1 definitions, 14 theorems"),
        "{}{}",
        checked,
        String::from_utf8_lossy(&c.stderr)
    );
    let _ = std::fs::remove_file(&out);
}

/// C1 for a_ctz_32, is_bouncing, get_slot_index, get_stride, step_seq,
/// upgradelock, resetlock, decay_bounces and a_clz_32 (calling a_ctz_32, its
/// contract a premise; linked with a_ctz_32's in proofs/mallocng_link.core)
/// by translation: `slc translate` writes the
/// certificates (the committed proofs/FN_tr.core, unchanged), and they
/// check with proofs/translate.core's, proofs/translate_frame.core's, proofs/translate_store_loop.core's
/// and proofs/translate_call.core's rules. Needs the -O0 build and its
/// readable GIMPLE.
#[test]
fn translations_are_generated_and_check() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let (elf, claim, sl) = (root.join("build/test_malloc_O0"), root.join("build/musl_malloc_O0.core"), root.join("build/gimple-O0/sl/c_mallocng_malloc.sl"));
    if !elf.exists() || !claim.exists() || !sl.exists() {
        eprintln!("skipped: run scripts/build-musl.sh -O0 and slc gimple --readable first");
        return;
    }
    let slc = env!("CARGO_BIN_EXE_slc");
    let tmp = std::env::temp_dir();
    let id = std::process::id();
    let (steps, gimple) = (tmp.join(format!("slc-tr-steps-{}.core", id)), tmp.join(format!("slc-tr-gimple-{}.core", id)));
    let g = Command::new(slc).current_dir(&root).args(["steps"]).arg(&elf).arg(&claim).args(["a_ctz_32", "is_bouncing", "get_slot_index", "get_stride", "step_seq", "upgradelock", "resetlock", "decay_bounces", "a_clz_32", "-o"]).arg(&steps).output().unwrap();
    assert!(g.status.success(), "{}", String::from_utf8_lossy(&g.stderr));
    let e = Command::new(slc).current_dir(&root).args(["elab", "spec", "layers"]).arg(&sl).arg("-o").arg(&gimple).output().unwrap();
    assert!(e.status.success(), "{}", String::from_utf8_lossy(&e.stderr));
    // the libraries, the spec, the decode facts, the rules
    let mut files: Vec<std::ffi::OsString> = ["core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core", "core/list.core", "core/loop.core"]
        .iter()
        .map(|f| f.into())
        .collect();
    files.push(gimple.clone().into());
    files.extend(["proofs/x86.core", "proofs/x86_code.core", "proofs/x86_stack.core", "proofs/x86_insn.core"].iter().map(|f| f.into()));
    files.push(steps.clone().into());
    files.extend(
        ["proofs/abi.core", "proofs/abi_restore.core", "proofs/abi_glue.core", "proofs/gimple.core", "proofs/gimple_call.core", "proofs/abi_stack.core", "proofs/abi_loop.core", "proofs/abi_bridge.core", "proofs/translate.core", "proofs/translate_frame.core", "proofs/translate_store_loop.core", "proofs/translate_call.core", "proofs/translate_effects.core"]
            .iter()
            .map(|f| f.into()),
    );
    let mut certs = Vec::new();
    for (f, prefix) in [("a_ctz_32", "act"), ("is_bouncing", "ibt"), ("get_slot_index", "gsit"), ("get_stride", "gst"), ("step_seq", "sst"), ("upgradelock", "ugt"), ("resetlock", "rlt"), ("decay_bounces", "dbt"), ("a_clz_32", "aclz")] {
        let cert = tmp.join(format!("slc-tr-{}-{}.core", f, id));
        let t = Command::new(slc)
            .current_dir(&root)
            .args(["translate", f, &format!("c_src_malloc_mallocng_malloc.{}_fun", f), prefix, "-o"])
            .arg(&cert)
            .args(&files)
            .output()
            .unwrap();
        assert!(t.status.success(), "{}", String::from_utf8_lossy(&t.stderr));
        let kept = format!("proofs/{}_tr.core", f);
        let (made, k) = (std::fs::read_to_string(&cert).unwrap(), std::fs::read_to_string(root.join(&kept)).unwrap());
        assert!(made == k, "{} differs from the generated {}", kept, cert.display());
        certs.push(cert);
    }
    // and a_clz_32 linked with a_ctz_32 (proofs/mallocng_link.core)
    let c = Command::new(slc).current_dir(&root).args(["kernel-check", "--no-cache"]).args(&files).args(&certs).arg("proofs/mallocng_link.core").output().unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // each certificate's theorems unconditional: nothing in the chain rests
    // on an open lemma (the storing functions' statics' range defined)
    let expect = [
        ("a_ctz_32", "0 definitions, 7 theorems"),
        ("is_bouncing", "0 definitions, 6 theorems"),
        ("get_slot_index", "0 definitions, 6 theorems"),
        ("get_stride", "0 definitions, 11 theorems"),
        ("step_seq", "0 definitions, 8 theorems"),
        ("upgradelock", "0 definitions, 6 theorems"),
        ("resetlock", "0 definitions, 6 theorems"),
        ("decay_bounces", "0 definitions, 6 theorems"),
        ("a_clz_32", "0 definitions, 3 theorems"),
    ];
    let each = expect.iter().all(|(f, n)| checked.contains(&format!("slc-tr-{}-{}.core: 0 constants, 0 axioms, {}, 0 conditional theorems, 0 open lemmas", f, id, n)))
        && checked.contains("proofs/mallocng_link.core: 0 constants, 0 axioms, 0 definitions, 3 theorems, 0 conditional theorems, 0 open lemmas");
    assert!(c.status.success() && each && !checked.contains("lemma "), "{}{}", checked, String::from_utf8_lossy(&c.stderr));
    for f in certs.iter().chain([&steps, &gimple]) {
        let _ = std::fs::remove_file(f);
    }
}
