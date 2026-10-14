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
        .args(["kernel-check", "--no-cache", "core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core"])
        .arg(&claim)
        .arg("proofs/x86.core")
        .output()
        .unwrap();
    let out = String::from_utf8_lossy(&c.stdout);
    assert!(c.status.success() && out.contains("proofs/x86.core: 0 constants, 0 axioms, 1 definitions, 26 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
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
    let elf = root.join("build/test_malloc");
    if !elf.exists() {
        return skip("run scripts/build-musl.sh first");
    }
    let slc = env!("CARGO_BIN_EXE_slc");
    // (the claim from the current layers)
    let claim = std::env::temp_dir().join(format!("slc-claim-{}.core", std::process::id()));
    let g = Command::new(slc).current_dir(&root).args(["claim", "malloc", "--elf"]).arg(&elf).arg("-o").arg(&claim).output().unwrap();
    assert!(g.status.success(), "{}", String::from_utf8_lossy(&g.stderr));
    for files in [
        vec!["core/prelude.core", "core/logic.core", "core/sets.core", "CLAIM", "proofs/mallocng.core", "proofs/musl_malloc.core"],
        vec!["core/prelude.core", "core/logic.core", "core/sets.core", "core/nat.core", "core/records.core", "core/list.core", "core/loop.core", "CLAIM", "proofs/malloc_client.core"],
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
    let _ = std::fs::remove_file(&claim);
    let _ = std::fs::remove_file(claim.with_extension("summary.txt"));
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

/// C1 of the -O0 functions by the checker's C1 engine: the `c1` lines of
/// proofs/mallocng_c1.core, each function's theorems from its decode facts
/// and its spec by proofs/translate*.core's rules (a caller's callee
/// contracts premises, linked in proofs/mallocng_link.core). Needs the -O0
/// build and its readable GIMPLE.
#[test]
fn c1_engine_checks() {
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
        .args(["a_ctz_32", "is_bouncing=403842", "get_slot_index=4030dd", "get_stride=403350", "step_seq=40370a", "upgradelock", "resetlock", "decay_bounces", "a_clz_32", "dequeue=402f49", "dequeue_head", "a_crash=402c6e", "queue=402e8c", "free_meta=403014", "size_to_class", "set_size", "enframe", "account_bounce", "get_meta=4030f5", "activate_group=40304f", "__malloc_allzerop", "alloc_slot", "try_avail", "alloc_group=403ee6", "a_cas=402c47", "size_overflows", "__malloc_alloc_meta", "get_random_secret", "__syscall1=402cf9", "__mmap", "__mprotect", "__errno_location", "-o"])
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
        ["proofs/abi.core", "proofs/abi_restore.core", "proofs/abi_glue.core", "proofs/gimple.core", "proofs/gimple_call.core", "proofs/abi_stack.core", "proofs/abi_loop.core", "proofs/abi_bridge.core", "proofs/translate.core", "proofs/translate_nf.core", "proofs/translate_frame.core", "proofs/translate_store_loop.core", "proofs/translate_flags.core", "proofs/translate_call.core", "proofs/gimple_inv.core", "proofs/translate_effects.core", "proofs/translate_zero.core", "proofs/translate_loop.core", "proofs/translate_cfg.core", "proofs/gimple_cfg.core", "proofs/gimple_cut.core", "proofs/gimple_loop.core", "proofs/translate_bitfield.core", "proofs/translate_block.core"]
            .iter()
            .map(|f| f.into()),
    );
    // (the program text: the code every contract assumes loaded; the
    // locals' homes, scripts/locmap.py, if made: the C1 engine's guide)
    files.push(text.clone().into());
    if root.join("build/locmap_O0.core").exists() {
        files.push("build/locmap_O0.core".into());
    }
    // and the callers linked with their callees (proofs/mallocng_link.core)
    // and the C2 proofs (readable GIMPLE refines the specs of layers/mallocng_specs.sl;
    // the memory rules' views and frames, proofs/mallocng_mem.core; the bit
    // counts' C2 on the bit library, proofs/mallocng_bits.core; the slots',
    // proofs/mallocng_slots.core; the context's counters' and the lock's,
    // proofs/mallocng_ctx.core), and the two composed per function
    // (proofs/mallocng_compose.core)
    let c = Command::new(slc)
        .current_dir(&root)
        .args(["kernel-check", "--no-cache"])
        .args(&files)
        .arg("proofs/a_crash.core")
        .arg("proofs/mallocng_c1.core")
        .args(["proofs/mallocng_link.core", "proofs/mallocng_mem.core", "proofs/mallocng_c2.core", "proofs/mallocng_bits.core", "proofs/mallocng_slots.core", "proofs/mallocng_ctx.core", "proofs/mallocng_compose.core"])
        .output()
        .unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // the C1 theorems unconditional: nothing in the chain rests on an open
    // lemma (the storing functions' statics' range defined)
    let each = checked.contains("proofs/mallocng_c1.core: 0 constants, 0 axioms, 0 definitions, 214 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_link.core: 0 constants, 0 axioms, 0 definitions, 24 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/translate_zero.core: 0 constants, 0 axioms, 3 definitions, 19 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/translate_loop.core: 0 constants, 0 axioms, 11 definitions, 35 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/translate_cfg.core: 0 constants, 0 axioms, 2 definitions, 9 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_cfg.core: 0 constants, 0 axioms, 2 definitions, 53 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_inv.core: 0 constants, 0 axioms, 1 definitions, 54 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/a_crash.core: 0 constants, 0 axioms, 0 definitions, 6 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_mem.core: 0 constants, 0 axioms, 0 definitions, 7 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_c2.core: 0 constants, 0 axioms, 0 definitions, 44 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_bits.core: 0 constants, 0 axioms, 0 definitions, 21 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_slots.core: 0 constants, 0 axioms, 2 definitions, 32 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_ctx.core: 0 constants, 0 axioms, 0 definitions, 30 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_compose.core: 0 constants, 0 axioms, 0 definitions, 10 theorems, 0 conditional theorems, 0 open lemmas");
    assert!(c.status.success() && each && !checked.contains("lemma "), "{}{}", checked, String::from_utf8_lossy(&c.stderr));
    for f in [&steps, &gimple, &text] {
        let _ = std::fs::remove_file(f);
    }
}

/// C1 of the -O0 functions on GIMPLE's control-flow graph (`slc gimple
/// --readable --cfg`; slc/cli/src/c1/cfg.rs, proofs/translate_cfg.core):
/// the `c1` lines on the CFG form (proofs/mallocng_c1_cfg.core), each block
/// walked once from its cut point; the CFG form refining the structured
/// one and composed with the structured form's C2 (proofs/mallocng_cfg.core;
/// both forms elaborated together).
#[test]
fn c1_cfg_engine_checks() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let (elf, claim, sl) = (root.join("build/test_malloc_O0"), root.join("build/musl_malloc_O0.core"), root.join("build/gimple-O0/sl/c_mallocng_malloc.sl"));
    let (dump, obj) = (root.join("build/gimple-O0/src_malloc_mallocng_malloc.c.optimized"), root.join("build/gimple-O0/src_malloc_mallocng_malloc.c.o"));
    if !elf.exists() || !claim.exists() || !sl.exists() || !dump.exists() || !obj.exists() {
        return skip("run scripts/build-musl.sh -O0 and scripts/dump-gimple.sh first");
    }
    let slc = env!("CARGO_BIN_EXE_slc");
    let tmp = std::env::temp_dir();
    let id = std::process::id();
    let (steps, gimple, text) = (tmp.join(format!("slc-cfg-steps-{}.core", id)), tmp.join(format!("slc-cfg-gimple-{}.core", id)), tmp.join(format!("slc-cfg-text-{}.core", id)));
    // (malloc.c's copies of the static functions also in other files: by address)
    let g = Command::new(slc)
        .current_dir(&root)
        .args(["steps"])
        .arg(&elf)
        .arg(&claim)
        .args(["a_ctz_32", "is_bouncing=403842", "get_slot_index=4030dd", "get_stride=403350", "step_seq=40370a", "upgradelock", "resetlock", "decay_bounces", "a_clz_32", "dequeue=402f49", "dequeue_head", "a_crash=402c6e", "queue=402e8c", "free_meta=403014", "size_to_class", "set_size", "enframe", "account_bounce", "get_meta=4030f5", "activate_group=40304f", "__malloc_allzerop", "alloc_slot", "try_avail", "alloc_group=403ee6", "a_cas=402c47", "size_overflows", "__malloc_alloc_meta", "get_random_secret", "__syscall1=402cf9", "__mmap", "__mprotect", "__errno_location", "-o"])
        .arg(&steps)
        .arg("--text")
        .arg(&text)
        .output()
        .unwrap();
    assert!(g.status.success(), "{}", String::from_utf8_lossy(&g.stderr));
    // (the readable CFG, from the dump)
    let cfg_sl = tmp.join(format!("slc-cfg-{}.sl", id));
    let gc = Command::new(slc)
        .current_dir(&root)
        .args(["gimple", "--readable", "--cfg", "--elf"])
        .arg(&elf)
        .arg("--obj")
        .arg(&obj)
        .args(["--source", "malloc.c"])
        .arg(&dump)
        .arg("-o")
        .arg(&cfg_sl)
        .output()
        .unwrap();
    assert!(gc.status.success(), "{}", String::from_utf8_lossy(&gc.stderr));
    let e = Command::new(slc).current_dir(&root).args(["elab", "spec", "layers"]).arg(&sl).arg(&cfg_sl).arg("-o").arg(&gimple).output().unwrap();
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
        ["proofs/abi.core", "proofs/abi_restore.core", "proofs/abi_glue.core", "proofs/gimple.core", "proofs/gimple_call.core", "proofs/abi_stack.core", "proofs/abi_loop.core", "proofs/abi_bridge.core", "proofs/translate.core", "proofs/translate_nf.core", "proofs/translate_frame.core", "proofs/translate_store_loop.core", "proofs/translate_flags.core", "proofs/translate_call.core", "proofs/gimple_inv.core", "proofs/translate_effects.core", "proofs/translate_zero.core", "proofs/translate_loop.core", "proofs/translate_cfg.core", "proofs/gimple_cfg.core", "proofs/gimple_cut.core", "proofs/gimple_loop.core", "proofs/translate_bitfield.core", "proofs/translate_block.core"]
            .iter()
            .map(|f| f.into()),
    );
    // (the program text: the code every contract assumes loaded; the
    // locals' homes, scripts/locmap.py, if made: the C1 engine's guide)
    files.push(text.clone().into());
    if root.join("build/locmap_O0.core").exists() {
        files.push("build/locmap_O0.core".into());
    }
    // and the structured form's C2 proofs up to the context's
    // (proofs/mallocng_ctx.core), the CFG form refining the structured
    // one and the three composed (proofs/mallocng_cfg.core); the ABI's
    // contract with ghost state (proofs/abi_ghost.core); specs with ghost
    // state refined (proofs/gimple_ghost.core) and the machine code of
    // set_size, enframe, dequeue, dequeue_head, get_slot_index, get_meta,
    // get_stride and __malloc_allzerop implementing their purpose specs
    // (proofs/mallocng_purpose.core)
    let c = Command::new(slc)
        .current_dir(&root)
        .args(["kernel-check", "--no-cache"])
        .args(&files)
        .arg("proofs/a_crash.core")
        .arg("proofs/mallocng_c1_cfg.core")
        .args(["proofs/mallocng_mem.core", "proofs/mallocng_c2.core", "proofs/mallocng_bits.core", "proofs/mallocng_slots.core", "proofs/mallocng_ctx.core", "proofs/mallocng_cfg.core"])
        .args(["proofs/abi_ghost.core", "proofs/gimple_ghost.core", "proofs/mallocng_abs.core", "proofs/mallocng_purpose.core"])
        .output()
        .unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // the C1 theorems unconditional: nothing in the chain rests on an open
    // lemma (the storing functions' statics' range defined)
    let each = checked.contains("proofs/mallocng_c1_cfg.core: 0 constants, 0 axioms, 0 definitions, 226 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_cfg.core: 0 constants, 0 axioms, 0 definitions, 62 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/abi_ghost.core: 0 constants, 0 axioms, 0 definitions, 28 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_ghost.core: 0 constants, 0 axioms, 0 definitions, 10 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_abs.core: 0 constants, 0 axioms, 0 definitions, 73 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/mallocng_purpose.core: 0 constants, 0 axioms, 0 definitions, 42 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/translate_cfg.core: 0 constants, 0 axioms, 2 definitions, 9 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_cfg.core: 0 constants, 0 axioms, 2 definitions, 53 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_cut.core: 0 constants, 0 axioms, 0 definitions, 11 theorems, 0 conditional theorems, 0 open lemmas")
        && checked.contains("proofs/gimple_loop.core: 0 constants, 0 axioms, 1 definitions, 52 theorems, 0 conditional theorems, 0 open lemmas");
    assert!(c.status.success() && each && !checked.contains("lemma "), "{}{}", checked, String::from_utf8_lossy(&c.stderr));
    for f in [&steps, &gimple, &text, &cfg_sl] {
        let _ = std::fs::remove_file(f);
    }
}
