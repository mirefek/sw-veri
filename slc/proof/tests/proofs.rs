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
    assert_eq!(arith_ok("a in omega -> b in omega -> int_lt(a, b) -> int_le(int_add(a, 1), b)", &[na, nb, ("h", "int_lt(a, b)")]), Ok(1));
    assert_eq!(arith_ok("a in omega -> b in omega -> a in b -> int_lt(a, b)", &[na, nb, ("h", "a in b")]), Ok(1));
    // integers: `-` everywhere
    assert_eq!(arith_ok("a in omega -> b in omega -> int_add(int_sub(a, b), b) = a", &[na, nb]), Ok(1));
    // arithmetic is total: laws of the integers for any sets
    assert_eq!(arith_ok("int_add(a, b) = int_add(b, a)", &[]), Ok(1));
    assert_eq!(arith_ok("int_sub(int_add(x, 5), x) = 5", &[]), Ok(1));
    // division by a constant
    assert_eq!(arith_ok("a in omega -> int_lt(int_mod(a, 4), 4)", &[na]), Ok(1));
    assert_eq!(arith_ok("a in omega -> int_le(int_mul(4, int_div(a, 4)), a)", &[na]), Ok(1));
    // a term equated to a number is a number
    assert_eq!(arith_ok("x = 3 -> int_lt(x, 4)", &[("h", "x = 3")]), Ok(1));
    // numbers built from numbers are in omega
    assert_eq!(arith_ok("a in omega -> int_add(int_mul(3, a), 2) in omega", &[na]), Ok(1));
}

#[test]
fn unsound_arithmetic_is_rejected() {
    let na = ("ha", "a in omega");
    let nb = ("hb", "b in omega");
    let bad = |stmt: &str, hyps: &[(&str, &str)]| {
        let r = arith_ok(stmt, hyps);
        assert!(r.as_ref().is_err_and(|e| e.contains("arith")), "accepted: {} ({:?})", stmt, r);
    };
    bad("a in omega -> int_lt(a, a)", &[na]);
    bad("a in omega -> b in omega -> int_lt(a, b)", &[na, nb]);
    // sets with equal values need not be equal (a, b not known integers)
    bad("int_le(a, b) -> int_le(b, a) -> a = b", &[("h1", "int_le(a, b)"), ("h2", "int_le(b, a)")]);
    bad("int_add(a, 0) = a", &[]);
    // not known to be naturals
    bad("a in omega -> int_le(0, x)", &[na]);
    bad("a in omega -> b in omega -> int_sub(a, b) in omega", &[na, nb]);
    // division facts that do not hold
    bad("a in omega -> int_lt(int_mod(a, 4), 3)", &[na]);
    // products of variables are not linear: this true fact is not proven
    bad("a in omega -> int_le(0, int_mul(a, a))", &[na]);
}

#[test]
fn recursion_equations_need_their_premise() {
    let src = |h: &str| {
        format!("theorem t(m): m in omega -> nat_rec(0, k v. succ(v), int_add(m, 1)) = succ(nat_rec(0, k v. succ(v), m))\nproof\n  assume hm: m in omega\n  show rec({{nat_rec(0, k v. succ(v), int_add(m, 1))}}{})\nqed\n", h)
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
        "theorem t: all n. n in omega -> int_lt(0, n)\nproof\n  have base: int_lt(0, 0) by arith()\n  show by induct(base, base)\nqed\n",
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

/// Loads the libraries up to core/list.core, then `src`.
fn check_list(src: &str) -> Result<usize, String> {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    for f in ["logic.core", "sets.core", "nat.core", "list.core"] {
        load_with(&mut env, &core_file(f), false, Some(&mut ScriptProver)).unwrap();
    }
    load_with(&mut env, src, false, Some(&mut ScriptProver)).map(|r| r.theorems.len()).map_err(|e| e.0)
}

#[test]
fn the_list_library_checks() {
    assert!(check_list("").is_ok());
}

#[test]
fn unsound_list_steps_are_rejected() {
    let bad = |src: &str, why: &str| match check_list(src) {
        Ok(_) => panic!("accepted: {}", src),
        Err(e) => assert!(e.contains(why), "expected `{}`, got: {}", why, e),
    };
    let lists2 = "  assume ha: a in list_type(t)\n  assume hb: b in list_type(t)\n";
    // ++ is not commutative
    bad(&format!("theorem x(a, b, t): a in list_type(t) -> b in list_type(t) -> seq_concat(a, b) = seq_concat(b, a)\nproof\n{}  show by lists(ha, hb)\nqed\n", lists2), "different pieces");
    // different elements
    bad("theorem x(p, q): seq_one(p) = seq_one(q)\nproof\n  show by lists()\nqed\n", "different pieces");
    // a term not known to be a list
    bad("theorem x(a): seq_concat(a, empty) = a\nproof\n  show by lists()\nqed\n", "known lists");
    // lengths of unknown terms are not numbers
    bad("theorem x(a): int_le(0, seq_len(a))\nproof\n  show by arith()\nqed\n", "arith");
    // an index past the end
    bad("theorem x(p, q): app(seq_concat(seq_one(p), seq_one(q)), 2) = q\nproof\n  show at({app(seq_concat(seq_one(p), seq_one(q)), 2)})\nqed\n", "cannot place");
    // an index whose piece is not determined by what is known
    bad(&format!("theorem x(a, b, t, i): a in list_type(t) -> b in list_type(t) -> i in omega -> app(seq_concat(a, b), i) = app(a, i)\nproof\n{}  assume hi: i in omega\n  show at({{app(seq_concat(a, b), i)}}, ha, hb, hi)\nqed\n", lists2), "cannot place");
    // extensionality needs the lengths of these two lists
    bad("theorem x(a, b, c, t): a in list_type(t) -> b in list_type(t) -> seq_len(a) = seq_len(c) -> (all i. i in omega -> int_lt(i, seq_len(a)) -> app(a, i) = app(b, i)) -> a = b\nproof\n  assume ha: a in list_type(t)\n  assume hb: b in list_type(t)\n  assume hl: seq_len(a) = seq_len(c)\n  assume he: all i. i in omega -> int_lt(i, seq_len(a)) -> app(a, i) = app(b, i)\n  show list_ext(ha, hb, hl, he)\nqed\n", "third premise");
}

#[test]
fn simp_executes_programs() {
    let src = "\
def prog(p) := mkprog(s o. ex x. ((p = 0 && x = exc(pair(s, empty), pair(\"ret\", empty))) || (!(p = 0) && x = ok(pair(s, empty), empty))) &&
  ((fst(x) = 0 && o = ok(fst(out_state(x)), 7)) || (fst(x) = 1 && fst(out_value(x)) = \"ret\" && o = ok(fst(out_state(x)), snd(out_value(x))))))
theorem t0(s, o): runs(prog(0), s, o) -> o = ok(s, empty)
proof
  assume h: runs(prog(0), s, o)
  show by simp(h)
qed
theorem t1(s, o, p): runs(prog(p), s, o) -> !(p = 0) -> ex v. o = ok(s, v) && v = 7
proof
  assume h: runs(prog(p), s, o)
  assume n: !(p = 0)
  show by simp(h, n)
qed
theorem t2(a, b, c, d): (ok(a, b) = exc(c, d) -> false) && (ok(a, b) = ok(c, d) -> a = c) && letin(3, x. x = 3)
proof
  show by simp()
qed
";
    assert_eq!(check(src), Ok(3));
}

#[test]
fn simp_does_not_overreach() {
    // running a program cannot be concluded without typing (univ membership)
    rejected("theorem x(a, b): runs(mkprog(s o. true), a, b)\nproof\n  show by simp()\nqed\n", "simp");
    // nor from a negated `runs` (the one-way step is not used there)
    rejected("theorem x(a, b): !runs(mkprog(s o. true), a, b) -> false\nproof\n  assume h: !runs(mkprog(s o. true), a, b)\n  show by simp(h)\nqed\n", "simp");
    // equal literals are not distinct; constructor arguments are not mixed up
    rejected("theorem x: \"ab\" = \"ab\" -> false\nproof\n  assume h: \"ab\" = \"ab\"\n  show by simp(h)\nqed\n", "simp");
    rejected("theorem x(a, b, c, d): pair(a, b) = pair(c, d) -> a = d\nproof\n  assume h: pair(a, b) = pair(c, d)\n  show by simp(h)\nqed\n", "simp");
    // a path that does not imply the goal is reported
    rejected("theorem x(p, o, s): runs(mkprog(s o. o = ok(s, 1) || o = ok(s, 2)), s, o) -> o = ok(s, 1)\nproof\n  assume h: runs(mkprog(s o. o = ok(s, 1) || o = ok(s, 2)), s, o)\n  show by simp(h)\nqed\n", "1 path left");
}

#[test]
fn simp_uses_equations_and_negated_existentials() {
    // `r = ok(a, 1)` and `r = ok(b, v)` on a path: v = 1
    let src = "\
theorem t0(r, a, b, v): (r = ok(a, 1) || r = exc(a, 2)) -> r = ok(b, v) -> v = 1
proof
  assume h: r = ok(a, 1) || r = exc(a, 2)
  assume hr: r = ok(b, v)
  show by simp(h, hr)
qed
theorem t1(f, x, y): (all z. !(ex p. pair(p, z) in f && p = x)) -> pair(x, y) in f -> false
proof
  assume hn: all z. !(ex p. pair(p, z) in f && p = x)
  assume h: pair(x, y) in f
  show by simp(hn, h)
qed
";
    assert_eq!(check(src), Ok(2));
    // an instance must match every conjunct
    rejected("theorem x(f, g, x, y): (all z. !(ex p. pair(p, z) in f && p in g)) -> pair(x, y) in f -> false\nproof\n  assume hn: all z. !(ex p. pair(p, z) in f && p in g)\n  assume h: pair(x, y) in f\n  show by simp(hn, h)\nqed\n", "simp");
    // different values: v is not determined to be 1
    rejected("theorem x(r, a, b, v): (r = ok(a, 1) || r = ok(a, 2)) -> r = ok(b, v) -> v = 1\nproof\n  assume h: r = ok(a, 1) || r = ok(a, 2)\n  assume hr: r = ok(b, v)\n  show by simp(h, hr)\nqed\n", "1 path left");
}

#[test]
fn the_record_library_checks() {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    for f in ["logic.core", "sets.core"] {
        load_with(&mut env, &core_file(f), false, Some(&mut ScriptProver)).unwrap();
    }
    let n = load_with(&mut env, &core_file("records.core"), false, Some(&mut ScriptProver)).unwrap().theorems.len();
    assert!(n >= 10, "{}", n);
}

#[test]
fn the_loop_library_checks() {
    let n = check_nat(&core_file("loop.core")).unwrap();
    assert_eq!(n, 5);
}

/// A loop counting to 3 (the loop state: the program state and the counter).
const COUNT: &str = "def count := mkprog(s o. while_rel(pair(s, 0), l. int_lt(snd(l), 3), l o. o = ok(pair(fst(l), int_add(snd(l), 1)), empty), l. empty, o))\n";

fn count_thm(goal: &str, hints: &str) -> String {
    format!(
        "{}theorem t(s, o): runs(count, s, o) -> {}\nproof\n  assume h: runs(count, s, o)\n  show by simp(h{})\nqed\n",
        COUNT, goal, hints
    )
}

#[test]
fn loops_are_executed_with_invariants() {
    let inv = ", {l0 l. snd(l) in omega && int_le(snd(l), 3) && fst(l) = fst(l0)}";
    // with a variant: the loop ends, with the counter at 3
    let src = count_thm("ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 3", &format!("{}, {{l. int_sub(3, snd(l))}}", inv));
    assert_eq!(check_nat(&src), Ok(1));
    // without one: ends so, or diverges
    let src = count_thm("(ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 3) || (ex t. o = diverge(t))", inv);
    assert_eq!(check_nat(&src), Ok(1));
}

#[test]
fn wrong_loop_invariants_are_rejected() {
    let bad = |goal: &str, hints: &str, why: &str| match check_nat(&count_thm(goal, hints)) {
        Ok(_) => panic!("accepted: {} {}", goal, hints),
        Err(e) => assert!(e.contains(why), "expected `{}`, got: {}", why, e),
    };
    let ends = "ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 3";
    // no invariant: the loop stays
    bad(ends, "", "needs its invariant");
    // without a variant, divergence is possible
    bad(ends, ", {l0 l. snd(l) in omega && int_le(snd(l), 3) && fst(l) = fst(l0)}", "path left");
    // not true at the start, not preserved
    bad(ends, ", {l0 l. snd(l) = 1}, {l. int_sub(3, snd(l))}", "at the start");
    bad(ends, ", {l0 l. snd(l) in omega && int_le(snd(l), 2)}, {l. int_sub(3, snd(l))}", "after an iteration");
    // a variant that grows, or is not a natural number
    bad(ends, ", {l0 l. snd(l) in omega && int_le(snd(l), 3)}, {l. snd(l)}", "the variant decreases");
    bad(ends, ", {l0 l. snd(l) in omega && int_le(snd(l), 3)}, {l. int_sub(2, snd(l))}", "the variant is a natural number");
    // a variant alone
    bad(ends, ", {l. int_sub(3, snd(l))}", "must follow its invariant");
}

/// A theorem `hyps -> goal` proven by `simp` from its hypotheses h0, h1, ..
fn simp_thm(hyps: &[&str], goal: &str) -> String {
    let stmt: String = hyps.iter().map(|h| format!("({}) -> ", h)).collect();
    let assumes: String = hyps.iter().enumerate().map(|(i, h)| format!("  assume h{}: {}\n", i, h)).collect();
    let names: Vec<String> = (0..hyps.len()).map(|i| format!("h{}", i)).collect();
    format!("theorem t(f, g, x): {}{}\nproof\n{}  show by simp({})\nqed\n", stmt, goal, assumes, names.join(", "))
}

#[test]
fn facts_are_used_as_rules() {
    // a rule whose hypothesis is on the path
    assert_eq!(check(&simp_thm(&["all y. y in f -> y in g", "x in f"], "x in g")), Ok(1));
    // a hypothesis that is not a literal, shown by arithmetic
    assert_eq!(check_nat(&simp_thm(&["all y. y in omega -> int_lt(y, 5) -> y in g", "x in omega", "int_lt(x, 3)"], "x in g")), Ok(1));
    // an equation, its variables from the goal's terms, rewriting the goal
    assert_eq!(check(&simp_thm(&["all a. app(f, a) = pair(a, a)"], "fst(app(f, x)) = x")), Ok(1));
    // chained: the conclusion of one rule is the hypothesis of the next
    assert_eq!(check(&simp_thm(&["all y. y in f -> y in g", "all y. y in g -> app(g, y) = y", "x in f"], "app(g, x) = x")), Ok(1));
    // a variable only in the conclusion: from the goal
    assert_eq!(check(&simp_thm(&["all y z. y in f -> pair(y, z) in g", "x in f"], "pair(x, x) in g")), Ok(1));
    // an instance of a universal fact, in the goal (a conjunct) or refuted
    assert_eq!(check(&simp_thm(&["all y. app(f, y) in g", "x in f"], "x in f && app(f, x) in g")), Ok(1));
    assert_eq!(check(&simp_thm(&["all y. app(f, y) in g", "!(app(f, x) in g)"], "false")), Ok(1));
}

#[test]
fn address_arithmetic_is_total() {
    // (x + 5) - x = 5 and x - x = 0 in 64 bits, for any set x (arithmetic
    // reads x as its value)
    assert_eq!(check_nat("theorem t(x): bits_sub(64, bits_add(64, x, 5), x) = 5\nproof\n  show by simp()\nqed\n"), Ok(1));
    assert_eq!(check_nat("theorem t(x): bits_sub(64, x, x) = 0\nproof\n  show by simp()\nqed\n"), Ok(1));
    // but x + 0 is x only for a 64-bit x
    let src = "theorem t(x): x in bits(64) -> bits_add(64, x, 0) = x\nproof\n  assume h: x in bits(64)\n  show by simp(h)\nqed\n";
    assert_eq!(check_nat(src), Ok(1));
    rejected("theorem t(x): bits_add(64, x, 0) = x\nproof\n  show by simp()\nqed\n", "simp");
    // words with the same base and different offsets differ
    assert_eq!(check_nat("theorem t(x): x in bits(64) -> x = bits_add(64, x, 8) -> false\nproof\n  assume h: x in bits(64)\n  assume e: x = bits_add(64, x, 8)\n  show by simp(h, e)\nqed\n"), Ok(1));
    // ... but a set that is not known to be a word may be anything
    rejected("theorem t(x): x = bits_add(64, x, 0) -> false\nproof\n  assume e: x = bits_add(64, x, 0)\n  show by simp(e)\nqed\n", "simp");
}

#[test]
fn rules_do_not_overreach() {
    let left = |src: String| match check_nat(&src) {
        Ok(_) => panic!("accepted: {}", src),
        Err(e) => assert!(e.contains("1 path left") && e.contains("path 1: "), "{}", e),
    };
    // a hypothesis that does not hold
    left(simp_thm(&["all y. y in omega -> int_lt(y, 2) -> y in g", "x in omega", "int_lt(x, 3)"], "x in g"));
    // a variable bound by nothing on the path (nor by the goal)
    left(simp_thm(&["all y z. y in f -> pair(y, z) in g", "x in f"], "pair(x, x) in f"));
    // the other direction of an implication
    left(simp_thm(&["all y. y in f -> y in g", "x in g"], "x in f"));
    // an equation used left to right only
    left(simp_thm(&["all a. pair(a, a) = app(f, a)"], "fst(app(f, x)) = x"));
}

#[test]
fn leftover_paths_are_reported_as_facts() {
    let src = "theorem t(p, o, s): runs(mkprog(s o. o = ok(s, 1) || o = ok(s, 2) || o = ok(s, 3)), s, o) -> o = ok(s, 1)\nproof\n  assume h: runs(mkprog(s o. o = ok(s, 1) || o = ok(s, 2) || o = ok(s, 3)), s, o)\n  show by simp(h)\nqed\n";
    let e = check(src).unwrap_err();
    assert!(e.contains("2 paths left"), "{}", e);
    assert!(e.contains("path 1: o = ok(s, ") && e.contains("path 2: "), "{}", e);
}

#[test]
fn simp_computes_on_numerals() {
    let src = "theorem t: int_add(3, 4) = 7 && bits_and(8, 195, 15) = 3 && bits_add(64, 18446744073709551615, 2) = 1 && int_lt(3, 4) && !int_le(5, 4) && bit(5, 2) && 255 in bits(8) && !(256 in bits(8)) && 3 in set_select(omega, x. int_lt(x, 5))\nproof\n  show by simp()\nqed\n";
    assert_eq!(check(src), Ok(1));
    // negative integers, Euclidean division, words of negatives
    let src = "theorem t: int_sub(3, 5) = int_neg(2) && int_lt(int_neg(2), 0) && int_div(int_neg(7), 2) = int_neg(4) && int_mod(int_neg(7), 2) = 1 && bits_of_int(8, int_neg(1)) = 255 && sint(8, 255) = int_neg(1) && !(int_neg(1) in omega)\nproof\n  show by simp()\nqed\n";
    assert_eq!(check(src), Ok(1));
    for bad in ["int_add(3, 4) = 8", "bits_and(8, 195, 15) = 4", "bit(5, 1)", "256 in bits(8)", "7 in set_select(omega, x. int_lt(x, 5))", "int_mod(int_neg(7), 2) = int_neg(1)"] {
        rejected(&format!("theorem x: {}\nproof\n  show by simp()\nqed\n", bad), "simp");
    }
}

#[test]
fn members_of_sets_are_evaluated() {
    // the fact `members` gives, used: exactly 1 and 3
    let src = "theorem t: all x. x in set_select(omega, x. (x = 1 || x = 3 || x = 2) && !(x = 2)) <-> x = 1 || x = 3\nproof\n  show members({set_select(omega, x. (x = 1 || x = 3 || x = 2) && !(x = 2))})\nqed\n";
    assert_eq!(check(src), Ok(1));
    // not another set of members
    rejected("theorem t: all x. x in set_select(omega, x. x = 1 || x = 3) <-> x = 1\nproof\n  show members({set_select(omega, x. x = 1 || x = 3)})\nqed\n", "");
    // below a numeral: each one
    let src = "theorem t: all x. x in set_select(omega, x. int_lt(x, 3)) <-> x = 0 || x = 1 || x = 2\nproof\n  show members({set_select(omega, x. int_lt(x, 3))})\nqed\n";
    assert_eq!(check(src), Ok(1));
    // an unknown not determined: no answer rather than a guess
    rejected("theorem t(y): true\nproof\n  have h := members({set_select(omega, x. int_lt(x, y))})\n  show by taut()\nqed\n", "eval: unsolved");
}

#[test]
fn loops_can_be_unrolled() {
    // counting to 3 without an invariant: three iterations, then the exit
    // (a divergence would continue as one from the next iteration, which
    // runs out when the loop stops)
    let src = count_thm("ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 3", ", unroll");
    assert_eq!(check_nat(&src), Ok(1));
    match check_nat(&count_thm("ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 2", ", unroll")) {
        Ok(_) => panic!("wrong exit accepted"),
        Err(e) => assert!(e.contains("path"), "{}", e),
    }
}

#[test]
fn arithmetic_modulo_large_powers() {
    // equalities are substituted exactly; `x in bits(k)` bounds x; 2^64 fits
    let m = "18446744073709551616";
    let bits = ("ha", "a in bits(64)");
    assert_eq!(arith_ok(&format!("a in bits(64) -> int_mod(a, {}) = a", m), &[bits]), Ok(1));
    assert_eq!(arith_ok(&format!("a in bits(64) -> int_div(a, {}) = 0", m), &[bits]), Ok(1));
    assert_eq!(arith_ok("a in bits(8) -> int_lt(a, 256)", &[("ha", "a in bits(8)")]), Ok(1));
    // and not more
    assert!(arith_ok(&format!("a in bits(65) -> int_mod(a, {}) = a", m), &[("ha", "a in bits(65)")]).is_err());
    assert!(arith_ok("a in bits(8) -> int_lt(a, 255)", &[("ha", "a in bits(8)")]).is_err());
    assert!(arith_ok("a in omega -> int_mod(a, 256) = a", &[("ha", "a in omega")]).is_err());
}

#[test]
fn differences_are_naturals_when_not_negative() {
    let (ha, hb) = (("ha", "a in omega"), ("hb", "b in omega"));
    assert_eq!(arith_ok("a in omega -> b in omega -> int_le(b, a) -> int_add(int_sub(a, b), 1) in omega", &[ha, hb, ("h", "int_le(b, a)")]), Ok(1));
    assert!(arith_ok("a in omega -> b in omega -> int_sub(a, b) in omega", &[ha, hb]).is_err());
    assert!(arith_ok("a in omega -> b in omega -> int_lt(a, b) -> int_sub(a, b) in omega", &[ha, hb, ("h", "int_lt(a, b)")]).is_err());
}
