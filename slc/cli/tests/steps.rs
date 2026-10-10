//! `slc steps`: the step theorems of get_slot_index (-O0 build) are
//! generated and prove. Needs `scripts/build-musl.sh -O0`; skipped without.

use std::path::Path;
use std::process::Command;

/// A test without its build: skipped, or (SLC_REQUIRE_BUILD set) failed.
fn skip(why: &str) {
    assert!(std::env::var_os("SLC_REQUIRE_BUILD").is_none(), "SLC_REQUIRE_BUILD set, but: {}", why);
    eprintln!("skipped: {}", why);
}

/// The facts about the x86 model (proofs/x86.core) check, among them that
/// the closed-form memory write means the same as the byte loop.
#[test]
fn x86_model_facts_check() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let claim = root.join("build/musl_malloc_O0.core");
    if !claim.exists() {
        return skip("run scripts/build-musl.sh -O0 first");
    }
    let c = Command::new(env!("CARGO_BIN_EXE_slc"))
        .current_dir(&root)
        .args(["kernel-check", "--no-cache", "core/prelude.core", "core/logic.core", "core/sets.core", "core/records.core"])
        .arg(&claim)
        .arg("proofs/x86.core")
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && out.contains("proofs/x86.core: 0 constants, 0 axioms, 1 definitions, 24 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
}

/// Loaded code (proofs/x86_code.core): fetched, and kept by every access
/// and store of the program (stack growth maps only unmapped pages).
#[test]
fn loaded_code_facts_check() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let claim = root.join("build/musl_malloc_O0.core");
    if !claim.exists() {
        return skip("run scripts/build-musl.sh -O0 first");
    }
    let c = Command::new(env!("CARGO_BIN_EXE_slc"))
        .current_dir(&root)
        .args(["kernel-check", "--no-cache", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core"])
        .arg(&claim)
        .args(["proofs/x86.core", "proofs/x86_code.core"])
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && out.contains("proofs/x86_code.core: 0 constants, 0 axioms, 0 definitions, 37 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
}

/// The claim's top (proofs/musl_malloc.core from its open lemmas), the
/// invariant's laws (proofs/mallocng.core) and the client facts
/// (proofs/malloc_client.core) check against the claim.
#[test]
fn claim_proofs_check() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let claim = root.join("build/musl_malloc.core");
    if !claim.exists() {
        return skip("run scripts/build-musl.sh first");
    }
    let slc = env!("CARGO_BIN_EXE_slc");
    for files in [
        vec!["core/prelude.core", "core/logic.core", "core/sets.core", "CLAIM", "proofs/mallocng.core", "proofs/musl_malloc.core"],
        vec!["core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/list.core", "core/loop.core", "core/records.core", "CLAIM", "proofs/malloc_client.core"],
    ] {
        let mut c = Command::new(slc);
        c.current_dir(&root).args(["kernel-check", "--no-cache"]);
        for f in files {
            if f == "CLAIM" {
                c.arg(&claim);
            } else {
                c.arg(f);
            }
        }
        let o = c.output().unwrap();
        assert!(o.status.success(), "{}{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr));
    }
}

#[test]
fn step_theorems_of_get_slot_index_prove() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let (elf, claim) = (root.join("build/test_malloc_O0"), root.join("build/musl_malloc_O0.core"));
    if !elf.exists() || !claim.exists() {
        return skip("run scripts/build-musl.sh -O0 first");
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
/// upgradelock, resetlock, decay_bounces, dequeue and a_clz_32 (calling a_ctz_32, its
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
        return skip("run scripts/build-musl.sh -O0 and slc gimple --readable first");
    }
    let slc = env!("CARGO_BIN_EXE_slc");
    let tmp = std::env::temp_dir();
    let id = std::process::id();
    let (steps, gimple, text) = (tmp.join(format!("slc-tr-steps-{}.core", id)), tmp.join(format!("slc-tr-gimple-{}.core", id)), tmp.join(format!("slc-tr-text-{}.core", id)));
    // (malloc.c's copies of the static functions also in other files: by address)
    let g = Command::new(slc)
        .current_dir(&root)
        .args(["steps"])
        .arg(&elf)
        .arg(&claim)
        .args(["a_ctz_32", "is_bouncing", "get_slot_index", "get_stride", "step_seq", "upgradelock", "resetlock", "decay_bounces", "a_clz_32", "dequeue=402f49", "dequeue_head", "a_crash=402c6e", "queue=402e8c", "free_meta=403014", "size_to_class", "set_size", "-o"])
        .arg(&steps)
        .arg("--text")
        .arg(&text)
        .output()
        .unwrap();
    assert!(g.status.success(), "{}", String::from_utf8_lossy(&g.stderr));
    let e = Command::new(slc).current_dir(&root).args(["elab", "spec", "layers"]).arg(&sl).arg("-o").arg(&gimple).output().unwrap();
    assert!(e.status.success(), "{}", String::from_utf8_lossy(&e.stderr));
    // the libraries, the spec, the decode facts, the rules
    let mut files: Vec<std::ffi::OsString> = ["core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core", "core/list.core", "core/loop.core", "core/bits.core"]
        .iter()
        .map(|f| f.into())
        .collect();
    files.push(gimple.clone().into());
    files.extend(["proofs/x86.core", "proofs/x86_code.core", "proofs/x86_stack.core", "proofs/x86_insn.core"].iter().map(|f| f.into()));
    files.push(steps.clone().into());
    files.extend(
        ["proofs/abi.core", "proofs/abi_restore.core", "proofs/abi_glue.core", "proofs/gimple.core", "proofs/gimple_call.core", "proofs/abi_stack.core", "proofs/abi_loop.core", "proofs/abi_bridge.core", "proofs/translate.core", "proofs/translate_frame.core", "proofs/translate_store_loop.core", "proofs/translate_call.core", "proofs/gimple_inv.core", "proofs/translate_effects.core", "proofs/translate_zero.core"]
            .iter()
            .map(|f| f.into()),
    );
    // (the program text: the code every contract assumes loaded)
    files.push(text.clone().into());
    let mut certs = Vec::new();
    for (f, prefix) in [("a_ctz_32", "act"), ("is_bouncing", "ibt"), ("get_slot_index", "gsit"), ("get_stride", "gst"), ("step_seq", "sst"), ("upgradelock", "ugt"), ("resetlock", "rlt"), ("decay_bounces", "dbt"), ("a_clz_32", "aclz"), ("dequeue", "dqt"), ("dequeue_head", "dqht"), ("queue", "qut"), ("free_meta", "fmt"), ("size_to_class", "stct"), ("set_size", "ssz")] {
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
    // and the callers linked with their callees (proofs/mallocng_link.core)
    // and the C2 proofs (readable GIMPLE refines the specs of layers/mallocng_specs.sl;
    // the memory rules' views and frames, proofs/mallocng_mem.core; the bit
    // counts' C2 on the bit library, proofs/mallocng_bits.core; the slots',
    // proofs/mallocng_slots.core)
    let c = Command::new(slc)
        .current_dir(&root)
        .args(["kernel-check", "--no-cache"])
        .args(&files)
        .arg("proofs/a_crash.core")
        .args(&certs)
        .args(["proofs/mallocng_link.core", "proofs/mallocng_mem.core", "proofs/mallocng_c2.core", "proofs/mallocng_bits.core", "proofs/mallocng_slots.core"])
        .output()
        .unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // each certificate's theorems unconditional: nothing in the chain rests
    // on an open lemma (the storing functions' statics' range defined)
    let expect = [
        ("a_ctz_32", "0 definitions, 7 theorems"),
        ("is_bouncing", "0 definitions, 6 theorems"),
        ("get_slot_index", "0 definitions, 6 theorems"),
        ("get_stride", "0 definitions, 10 theorems"),
        ("step_seq", "0 definitions, 8 theorems"),
        ("upgradelock", "0 definitions, 6 theorems"),
        ("resetlock", "0 definitions, 6 theorems"),
        ("decay_bounces", "0 definitions, 6 theorems"),
        ("a_clz_32", "0 definitions, 6 theorems"),
        ("dequeue", "0 definitions, 10 theorems"),
        ("dequeue_head", "0 definitions, 6 theorems"),
        ("queue", "0 definitions, 10 theorems"),
        ("free_meta", "0 definitions, 6 theorems"),
        ("size_to_class", "0 definitions, 7 theorems"),
        ("set_size", "0 definitions, 6 theorems"),
    ];
    let each = expect.iter().all(|(f, n)| checked.contains(&format!("slc-tr-{}-{}.core: 0 constants, 0 axioms, {}, 0 conditional theorems, 0 open lemmas", f, id, n)))
        && checked.contains("proofs/mallocng_link.core: 0 constants, 0 axioms, 0 definitions, 20 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/translate_zero.core: 0 constants, 0 axioms, 3 definitions, 19 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_inv.core: 0 constants, 0 axioms, 1 definitions, 48 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/a_crash.core: 0 constants, 0 axioms, 0 definitions, 5 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_mem.core: 0 constants, 0 axioms, 0 definitions, 7 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_c2.core: 0 constants, 0 axioms, 0 definitions, 50 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_bits.core: 0 constants, 0 axioms, 0 definitions, 14 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_slots.core: 0 constants, 0 axioms, 0 definitions, 9 theorems, 0 conditional theorems, 0 open lemmas");
    assert!(c.status.success() && each && !checked.contains("lemma "), "{}{}", checked, String::from_utf8_lossy(&c.stderr));
    for f in certs.iter().chain([&steps, &gimple, &text]) {
        let _ = std::fs::remove_file(f);
    }
}
