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
    assert!(c.status.success() && out.contains("proofs/x86_code.core: 0 constants, 0 axioms, 0 definitions, 36 theorems"), "{}{}", out, String::from_utf8_lossy(&c.stderr));
}

/// The claim's top (proofs/mallocng/claim.core from its open lemmas), the
/// invariant's laws (proofs/mallocng/laws.core) and the client facts
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
        vec!["core/prelude.core", "core/logic.core", "core/sets.core", "CLAIM", "proofs/mallocng/laws.core", "proofs/mallocng/claim.core"],
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

/// C1 of the -O0 functions on GIMPLE's control-flow graph (`slc gimple
/// --readable --cfg`; slc/cli/src/c1/cfg.rs, proofs/translate_cfg.core):
/// the `c1` lines on the CFG form (proofs/mallocng/machine/c1.core), each
/// block walked once from its cut point; the CFG form refining the
/// structured one and composed with the structured form's C2
/// (proofs/mallocng/machine/cfg.core; both forms elaborated together); the
/// rest of the chain (proofs/chain) after them.
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
        .args(["a_ctz_32", "is_bouncing=403842", "get_slot_index=4030dd", "get_stride=403350", "step_seq=40370a", "upgradelock", "resetlock", "decay_bounces", "a_clz_32", "dequeue=402f49", "dequeue_head", "a_crash=402c6e", "queue=402e8c", "free_meta=403014", "size_to_class", "set_size", "enframe", "account_bounce", "get_meta=4030f5", "activate_group=40304f", "__malloc_allzerop", "alloc_slot", "try_avail", "alloc_group=403ee6", "a_cas=402c47", "size_overflows", "__malloc_alloc_meta", "get_random_secret", "__syscall1=402cf9", "__mmap", "__mprotect", "__errno_location", "__get_tp=40569a", "__syscall3=404bde", "__syscall6=404a8c", "__syscall_ret", "dummy=404ada", "memcpy", "__stack_chk_fail", "-o"])
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
    // (the leaves' translation units -- errno, the syscall and mman
    // wrappers -- their structured and CFG forms, as scripts/check.sh's)
    let mut leaf_sl = Vec::new();
    for (src, name, base) in [
        ("src_errno___errno_location", "c_errno_location", "__errno_location.c"),
        ("src_internal_syscall_ret", "c_syscall_ret", "syscall_ret.c"),
        ("src_mman_mprotect", "c_mman_mprotect", "mprotect.c"),
        ("src_mman_mmap", "c_mman_mmap", "mmap.c"),
    ] {
        let (d, o) = (root.join(format!("build/gimple-O0/{src}.c.optimized")), root.join(format!("build/gimple-O0/{src}.c.o")));
        for cfg in [false, true] {
            let out = tmp.join(format!("slc-{}{}-{}.sl", name, if cfg { "-cfg" } else { "" }, id));
            let mut a = vec!["gimple", "--readable"];
            if cfg {
                a.push("--cfg");
            }
            let r = Command::new(slc).current_dir(&root).args(&a).arg("--elf").arg(&elf).arg("--obj").arg(&o).args(["--source", base]).arg(&d).arg("-o").arg(&out).output().unwrap();
            assert!(r.status.success(), "{}", String::from_utf8_lossy(&r.stderr));
            leaf_sl.push(out);
        }
    }
    let e = Command::new(slc).current_dir(&root).args(["elab", "spec", "layers"]).arg(&sl).arg(&cfg_sl).args(&leaf_sl).arg("-o").arg(&gimple).output().unwrap();
    assert!(e.status.success(), "{}", String::from_utf8_lossy(&e.stderr));
    // the chain (proofs/chain): the libraries, the spec, the decode facts,
    // the rules, the program text (the code every contract assumes loaded),
    // the locals' homes if made (scripts/locmap.py: the C1 engine's guide),
    // then mallocng -- its C1 and CFG compositions, its code's runs, its
    // invariant, its functions by their purpose
    let chain = std::fs::read_to_string(root.join("proofs/chain")).unwrap();
    let mut files: Vec<std::ffi::OsString> = Vec::new();
    let mut proofs: Vec<String> = Vec::new();
    for l in chain.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        match l {
            "@gimple" => files.push(gimple.clone().into()),
            "@steps" => files.push(steps.clone().into()),
            "@text" => files.push(text.clone().into()),
            "@locmap" => {
                if root.join("build/locmap_O0.core").exists() {
                    files.push("build/locmap_O0.core".into());
                }
            }
            f => {
                if f.starts_with("proofs/") {
                    proofs.push(f.to_string());
                }
                files.push(f.into());
            }
        }
    }
    let c = Command::new(slc).current_dir(&root).args(["kernel-check", "--no-cache"]).args(&files).output().unwrap();
    let checked = String::from_utf8_lossy(&c.stdout);
    // every proof file checked, with no axiom and nothing resting on an open
    // lemma (the C1 theorems unconditional: the storing functions' statics'
    // range defined)
    let each = proofs.iter().all(|f| {
        checked.lines().any(|l| l.starts_with(&format!("{}: ", f)) && l.contains(" 0 axioms,") && l.contains(" 0 conditional theorems, 0 open lemmas"))
    });
    assert!(c.status.success() && each && !checked.contains("lemma "), "{}{}", checked, String::from_utf8_lossy(&c.stderr));
    for f in [&steps, &gimple, &text, &cfg_sl] {
        let _ = std::fs::remove_file(f);
    }
}
