//! Proofs in core files: the library checks, and unsound steps are rejected.

use sl_kernel::syntax::{load, load_with};
use sl_kernel::Env;
use sl_proof::ScriptProver;
use std::path::Path;

fn core_file(name: &str) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../core").join(name)).unwrap()
}

/// Loads the prelude, then `src` with proofs; the error message, if any.
fn check(src: &str) -> Result<usize, String> {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    load_with(&mut env, src, false, Some(&mut ScriptProver)).map(|r| r.theorems.len()).map_err(|e| e.0)
}

#[test]
fn the_logic_library_checks() {
    let n = check(&core_file("logic.core")).unwrap();
    assert!(n >= 10);
}

fn rejected(src: &str, why: &str) {
    match check(src) {
        Ok(_) => panic!("accepted: {}", src),
        Err(e) => assert!(e.contains(why), "expected `{}`, got: {}", why, e),
    }
}

#[test]
fn a_proof_of_another_statement_is_rejected() {
    rejected("theorem bad(a): a\nproof\n  show imp_weaken[a := a, b := a]\nqed\n", "not the statement");
}

#[test]
fn classical_steps_apply_to_any_term() {
    // valid for any a: `true -> a` is a proposition interderivable with a
    // (dne_any in core/logic.core proves it from basic steps)
    assert_eq!(check("theorem ok(a): !!a -> a\nproof\n  assume h: !!a\n  show a by taut(h)\nqed\n"), Ok(1));
    assert_eq!(check("theorem ok(z): (all x. x) -> z\nproof\n  assume h: all x. x\n  show all_elim(h, {z})\nqed\n"), Ok(1));
}

#[test]
fn discharging_needs_an_assumption() {
    rejected("theorem bad(a): a -> a\nproof\n  have r := eq_refl[a := a]\n  show discharge(r, r)\nqed\n", "not an assumption");
}

#[test]
fn generalizing_over_a_variable_in_a_hypothesis_is_rejected() {
    rejected(
        "theorem bad: all x. x = false\nproof\n  fix x\n  assume h: x = false\n  show gen(h, x)\nqed\n",
        "occurs in a hypothesis",
    );
}

#[test]
fn non_tautologies_are_rejected() {
    rejected("theorem bad: false\nproof\n  show false by taut()\nqed\n", "not a tautology");
    rejected("theorem bad(x, y): x = y -> y = x\nproof\n  assume h: x = y\n  show y = x by taut(h)\nqed\n", "not a tautology");
}

#[test]
fn wrong_witnesses_and_rewrites_are_rejected() {
    rejected("theorem bad: ex x. x = true\nproof\n  show ex x. x = true by ex_intro({false}, refl({false}))\nqed\n", "not `false = true`");
    rejected("theorem bad(a, b): a = b -> b = b\nproof\n  assume h: a = b\n  show rewrite(h, refl({b}))\nqed\n", "does not occur");
}

#[test]
fn theorems_need_a_proof_checker() {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    let e = load(&mut env, "theorem t(a): a -> a\nproof\n  show imp_refl[a := a]\nqed\n", false).unwrap_err();
    assert!(e.0.contains("proof checker"));
}

/// Loads the prelude and `src`; the environment.
fn env_of(src: &str) -> Result<Env, String> {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    load_with(&mut env, src, false, Some(&mut ScriptProver)).map_err(|e| e.0)?;
    Ok(env)
}

fn remaining(env: &Env, name: &str) -> Vec<String> {
    sl_kernel::ext::facts::remaining(env, name).unwrap()
}

const LEMMAS: &str = "\
lemma l1(a): a -> a
lemma l2: false -> false
theorem t: false -> false
proof
  show l1[a := false]
qed
theorem u: (false -> false) = (false -> false)
proof
  have x := t
  show refl({false -> false})
qed
theorem v: false -> false
proof
  show t
qed
";

#[test]
fn proofs_from_open_lemmas_are_conditional() {
    let env = env_of(LEMMAS).unwrap();
    // t and v rest on l1 (v through t); u does not use t
    assert!(env.fact("t").is_none() && env.fact("v").is_none());
    assert!(env.fact("u").is_some());
    assert_eq!(remaining(&env, "v"), vec!["l1"]);
    assert_eq!(remaining(&env, "l2"), vec!["l2"]);
}

#[test]
fn proving_the_open_lemmas_proves_what_rests_on_them() {
    let src = format!("{}theorem l1\nproof\n  show imp_refl_ax\nqed\n", LEMMAS.replace("lemma l2", "axiom_free_placeholder"));
    // a proof of l1 from the axioms (the logic library is not loaded here)
    let src = src.replace("axiom_free_placeholder: false -> false\n", "").replace(
        "  show imp_refl_ax\n",
        "  show mp(mp(imp_chain[a := a, b := a -> a, c := a], imp_weaken[a := a, b := a -> a]), imp_weaken[a := a, b := a])\n",
    );
    let env = env_of(&src).unwrap();
    assert!(env.fact("l1").is_some());
    assert_eq!(remaining(&env, "v"), Vec::<String>::new());
}

#[test]
fn circular_proofs_are_rejected() {
    let src = "lemma a1: false -> false\nlemma a2: false -> false\n\
               theorem a1\nproof\n  show a2\nqed\n\
               theorem a2\nproof\n  show a1\nqed\n";
    let e = env_of(src).err().unwrap();
    assert!(e.contains("circular"), "{}", e);
    let e = env_of("lemma a1: false -> false\ntheorem a1\nproof\n  show a1\nqed\n").err().unwrap();
    assert!(e.contains("circular"), "{}", e);
}

#[test]
fn a_lemma_is_proven_with_its_own_statement() {
    let e = env_of("lemma a1: false -> false\ntheorem a1: false = false\nproof\n  show refl({false})\nqed\n").err().unwrap();
    assert!(e.contains("differs"), "{}", e);
    let e = env_of("lemma eq_refl: false -> false\n").err().unwrap();
    assert!(e.contains("already exists"), "{}", e);
}

#[test]
fn unfolding_needs_the_named_definitions() {
    // not(false) unfolds to false -> false
    assert!(env_of("theorem ok: !false\nproof\n  show by defs(imp_refl_free, not)\nqed\n").is_err());
    let ok = "lemma i: false -> false\ntheorem ok: !false\nproof\n  show by defs(i, not)\nqed\n";
    assert!(env_of(ok).is_ok());
    // without naming `not`, the statements differ
    rejected("lemma i: false -> false\ntheorem bad: !false\nproof\n  show by defs(i, true)\nqed\n", "differ after unfolding");
}

#[test]
fn a_claim_or_lemma_after_a_theorem_of_its_name_is_rejected() {
    let e = env_of("theorem c: false = false\nproof\n  show refl({false})\nqed\nclaim c: false\n").err().unwrap();
    assert!(e.contains("already exists"), "{}", e);
    let e = env_of("theorem c: false = false\nproof\n  show refl({false})\nqed\nlemma c: false\n").err().unwrap();
    assert!(e.contains("already exists"), "{}", e);
}

#[test]
fn the_set_library_checks() {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    load_with(&mut env, &core_file("logic.core"), false, Some(&mut ScriptProver)).unwrap();
    let r = load_with(&mut env, &core_file("sets.core"), false, Some(&mut ScriptProver)).unwrap();
    assert!(r.theorems.len() >= 20);
    assert!(env.fact("pair_inj").is_some() && env.fact("app_fn_build").is_some());
}

#[test]
fn an_obtained_witness_cannot_escape() {
    // the obtained x is a particular (unknown) object: the result may not mention it
    rejected("theorem bad: false = false\nproof\n  obtain x, hx from ex_intro({false}, {x. x = x}, refl({false}))\n  show refl({x})\nqed\n", "occurs in the result");
    let ok = "theorem ok: false = false\nproof\n  obtain x, hx from ex_intro({false}, {x. x = x}, refl({false}))\n  show refl({false})\nqed\n";
    assert_eq!(check(ok), Ok(1));
}

#[test]
fn set_select_membership_steps() {
    let src = "theorem ok(s, z): z in set_select(s, x. x = x) -> z in s\nproof\n  assume h: z in set_select(s, x. x = x)\n  show z in s by taut(unsel(h))\nqed\n\
               theorem ok2(s, z): z in s -> z in set_select(s, x. x = x)\nproof\n  assume h: z in s\n  show z in set_select(s, x. x = x) by sel(taut(h, refl({z})))\nqed\n";
    assert_eq!(check(src), Ok(2));
}

/// Loads the prelude and the libraries up to core/nat.core, then `src`.
fn check_nat(src: &str) -> Result<usize, String> {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    for f in ["logic.core", "sets.core", "nat.core"] {
        load_with(&mut env, &core_file(f), false, Some(&mut ScriptProver)).unwrap();
    }
    load_with(&mut env, src, false, Some(&mut ScriptProver)).map(|r| r.theorems.len()).map_err(|e| e.0)
}

fn arith_ok(stmt: &str, hyps: &[(&str, &str)]) -> Result<usize, String> {
    let assumes: String = hyps.iter().map(|(n, t)| format!("  assume {}: {}\n", n, t)).collect();
    let names: Vec<&str> = hyps.iter().map(|(n, _)| *n).collect();
    check_nat(&format!("theorem t(a, b, x): {}\nproof\n{}  show by arith({})\nqed\n", stmt, assumes, names.join(", ")))
}

#[test]
fn arithmetic_is_proven() {
    let na = ("ha", "a in omega");
    let nb = ("hb", "b in omega");
    assert_eq!(arith_ok("a in omega -> b in omega -> nat_lt(a, b) -> nat_le(nat_add(a, 1), b)", &[na, nb, ("h", "nat_lt(a, b)")]), Ok(1));
    assert_eq!(arith_ok("a in omega -> b in omega -> a in b -> nat_lt(a, b)", &[na, nb, ("h", "a in b")]), Ok(1));
    // `-` where it is defined
    assert_eq!(
        arith_ok("a in omega -> b in omega -> nat_le(b, a) -> nat_add(nat_sub(a, b), b) = a", &[na, nb, ("h", "nat_le(b, a)")]),
        Ok(1)
    );
    // division by a constant
    assert_eq!(arith_ok("a in omega -> nat_lt(nat_mod(a, 4), 4)", &[na]), Ok(1));
    assert_eq!(arith_ok("a in omega -> nat_le(nat_mul(4, nat_div(a, 4)), a)", &[na]), Ok(1));
    // a term equated to a number is a number
    assert_eq!(arith_ok("x = 3 -> nat_lt(x, 4)", &[("h", "x = 3")]), Ok(1));
    // numbers built from numbers are in omega
    assert_eq!(arith_ok("a in omega -> nat_add(nat_mul(3, a), 2) in omega", &[na]), Ok(1));
}

#[test]
fn unsound_arithmetic_is_rejected() {
    let na = ("ha", "a in omega");
    let nb = ("hb", "b in omega");
    let bad = |stmt: &str, hyps: &[(&str, &str)]| {
        let r = arith_ok(stmt, hyps);
        assert!(r.as_ref().is_err_and(|e| e.contains("arith")), "accepted: {} ({:?})", stmt, r);
    };
    bad("a in omega -> nat_lt(a, a)", &[na]);
    bad("a in omega -> b in omega -> nat_lt(a, b)", &[na, nb]);
    // not known to be numbers
    bad("nat_add(a, b) = nat_add(b, a)", &[]);
    bad("a in omega -> nat_le(0, x)", &[na]);
    // `-` below zero is not a number
    bad("a in omega -> b in omega -> nat_add(nat_sub(a, b), b) = a", &[na, nb]);
    bad("a in omega -> b in omega -> nat_sub(a, b) in omega", &[na, nb]);
    // division facts that do not hold
    bad("a in omega -> nat_lt(nat_mod(a, 4), 3)", &[na]);
    // products of variables are not linear: this true fact is not proven
    bad("a in omega -> nat_le(0, nat_mul(a, a))", &[na]);
}

#[test]
fn recursion_equations_need_their_premise() {
    let src = |h: &str| {
        format!("theorem t(m): m in omega -> nat_rec(0, k v. succ(v), nat_add(m, 1)) = succ(nat_rec(0, k v. succ(v), m))\nproof\n  assume hm: m in omega\n  show rec({{nat_rec(0, k v. succ(v), nat_add(m, 1))}}{})\nqed\n", h)
    };
    assert_eq!(check_nat(&src(", hm")), Ok(1));
    let e = check_nat(&src("")).unwrap_err();
    assert!(e.contains("m in omega"), "{}", e);
    // a proof of membership for another term does not do
    let e = check_nat(&src(", refl({m})")).unwrap_err();
    assert!(e.contains("m in omega"), "{}", e);
}

#[test]
fn induction_checks_base_and_step() {
    // (core/nat.core, loaded by check_nat, proves dbl(n) = 2 n by induction)
    // a wrong base case
    let e = check_nat(
        "theorem t: all n. n in omega -> nat_lt(0, n)\nproof\n  have base: nat_lt(0, 0) by arith()\n  show by induct(base, base)\nqed\n",
    )
    .unwrap_err();
    assert!(e.contains("arith"), "{}", e);
}

#[test]
fn sub_proofs_are_closed_at_their_qed() {
    // the block proves `a -> a`; the outer proof uses it
    let ok = "theorem t(a): (a -> a) && (a -> a)\nproof\n  have i: a -> a proof\n    assume h: a\n    show h\n  qed\n  show by taut(i)\nqed\n";
    assert_eq!(check(ok), Ok(1));
    // nested blocks, and `show proof` for the current goal
    let nested = "theorem t(a, b): a -> b -> a\nproof\n  show proof\n    assume h: a\n    have k: b -> a proof\n      assume g: b\n      show h\n    qed\n    show k\n  qed\nqed\n";
    assert_eq!(check(nested), Ok(1));
    // a block must prove what it states: here it shows `a -> a`, not `a`
    rejected("theorem t(a): a -> a\nproof\n  have x: a proof\n    assume h: a\n    show h\n  qed\n  show imp_weaken[a := a, b := a]\nqed\n", "this proves");
    // a variable fixed inside a block is generalized there, not visible outside
    rejected("theorem t: all x. x = x\nproof\n  have e: all y. y = y proof\n    fix y\n    show refl({y})\n  qed\n  show refl({y})\nqed\n", "y");
}
