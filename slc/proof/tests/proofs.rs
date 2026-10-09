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

/// `abbrev` and `let` are read as their expansions; `apply` instantiates a
/// fact by matching its premises; a `let` ends with its block.
#[test]
fn abbreviations_let_and_apply() {
    let src = "abbrev self_imp(a) := imp(a, a)\n\
theorem t1(p): self_imp(p)\nproof\n  assume h: p\n  show h\nqed\n\
theorem t2(p, q): p -> (p -> q) -> q\nproof\n  assume h: p\n  assume g: p -> q\n  let r := q\n  have x: r := apply(g, h)\n  show x\nqed\n\
theorem t3(p, q): (all x. x -> q) -> p -> q\nproof\n  assume g: all x. x -> q\n  assume h: p\n  show apply(g, h)\nqed\n";
    assert_eq!(check(src), Ok(3));
    // a `let` of one proof is unknown in the next
    rejected(
        "theorem t1(p): p -> p\nproof\n  let r := p\n  assume h: r\n  show h\nqed\ntheorem t2(p): p -> p\nproof\n  assume h: r\n  show h\nqed\n",
        "unknown symbol `r`",
    );
}

/// rsimp: rewriting left to right with the facts given (an equation, a
/// proposition as `true`, a negation's proposition as `false`), the
/// definitions given, and the registered rules (core/logic.core's
/// propositional ones, `ite_t` with its premise from a fact); numerals
/// evaluated; also under binders; on a fact, and as a step.
#[test]
fn rsimp_rewrites_left_to_right() {
    let lib = format!("{}{}", core_file("logic.core"), core_file("sets.core"));
    let base = check(&lib).unwrap();
    let ok = [
        "theorem t(x, q): x in q -> (true && x in q) || q = 1\nproof\n  assume h\n  show by rsimp(h)\nqed\n",
        "theorem t(x, y): x = 3 -> y = x -> y = 3\nproof\n  assume h g\n  show by rsimp(g, h)\nqed\n",
        "theorem t(c, a, b): c -> ite(c, a, b) = a\nproof\n  assume h\n  show by rsimp(h)\nqed\n",
        "def both(a, b) := a && b\ntheorem t(x, s, q): x in s -> both(x in s, q = 1) = (q = 1)\nproof\n  assume h\n  show by rsimp(both, h)\nqed\n",
        "theorem t(x, s, q): x in s -> !(q = 1) -> (x in s && !(q = 1)) || false\nproof\n  assume h g\n  rsimp h, g\nqed\n",
        "theorem t(x): x = 3 -> all z. z = x -> z = 3\nproof\n  assume h\n  show by rsimp(h)\nqed\n",
        "theorem t(a, b, c): a = b -> b = c -> a = c\nproof\n  assume h g\n  have k := rsimp(h, g)\n  show k\nqed\n",
        "theorem t: int_lt(int_add(pow2(3), 1), 10) && int_mod(17, 5) = 2\nproof\n  show by rsimp()\nqed\n",
    ];
    for t in ok {
        assert_eq!(check(&format!("{}{}", lib, t)), Ok(base + 1), "{}", t);
    }
    // only the rules given (`only`); what is left is shown
    rejected(&format!("{}theorem t(x, y): x = y -> true && x = y\nproof\n  assume h\n  show by rsimp(only, h)\nqed\n", lib), "the goal simplifies to `true && y = y`");
}

/// Small conveniences: messages fold a proof's `let`s back (and implicit
/// unfolding gives up on arithmetic's definitions quickly); `..` ends a
/// destructuring (`r..` names the rest); taut takes an equation as its flip
/// (also `!=`).
#[test]
fn folded_messages_rest_patterns_and_symmetric_taut() {
    let logic = core_file("logic.core");
    let base = check(&logic).unwrap();
    rejected(
        &format!("{}theorem f(a, b, c): int_add(int_mul(a, b), c) = c -> int_add(int_mul(a, b), c) = int_add(c, 1)\nproof\n  let P := int_mul(a, b)\n  let S(x) := int_add(P, x)\n  assume h\n  show h\nqed\n", logic),
        "this proves `S(c) = c -> S(c) = c`, not `S(c) = c -> S(c) = int_add(c, 1)`",
    );
    let ok = [
        "theorem t(a, b, c): a = 1 && b = 2 && c = 3 && a = c -> b = 2\nproof\n  assume h\n  have x y .. := h\n  show y\nqed\n",
        "theorem t(a, b, c): a = 1 && b = 2 && c = 3 && a = c -> c = 3 && a = c\nproof\n  assume h\n  have x y r.. := h\n  show r\nqed\n",
        "theorem t(m, n, p): !(m = n) -> p -> p && !(n = m)\nproof\n  assume h g\n  show by taut(h, g)\nqed\n",
        "theorem t(m, n): m != n -> !(n = m)\nproof\n  assume h\n  show by taut(h)\nqed\n",
    ];
    for t in ok {
        assert_eq!(check(&format!("{}{}", logic, t)), Ok(base + 1), "{}", t);
    }
}

/// Words and integers: arith reads word operations of a symbolic width
/// (their definitions, the remainder of a small value); rsimp turns a word
/// sum without wrap-around into the integer one (`bits_add_nowrap`), its
/// bounds shown by arith from the facts about its terms.
#[test]
fn words_and_integers() {
    let lib = format!("{}{}{}", core_file("logic.core"), core_file("sets.core"), core_file("nat.core"));
    let base = check(&lib).unwrap();
    let ok = [
        "theorem t(n, a, b): n in omega -> a in bits(n) -> b in bits(n) -> bits_add(n, a, b) in bits(n)\nproof\n  assume hn ha hb\n  show by arith(hn, ha, hb)\nqed\n",
        "theorem t(n, a, b): a in bits(n) -> b in bits(n) -> int_le(b, a) -> bits_sub(n, a, b) = int_sub(a, b)\nproof\n  assume ha hb hl\n  show by arith(ha, hb, hl)\nqed\n",
        "theorem t(p): p in bits(64) -> int_lt(p, 1000) -> bits_add(64, p, 8) = int_add(p, 8)\nproof\n  assume hp hl\n  show by rsimp()\nqed\n",
        "theorem t(p): p in bits(64) -> int_lt(int_add(p, 8), int_pow(2, 64)) -> int_add(p, 8) in bits(64)\nproof\n  assume hp hl\n  show by arith(hp, hl)\nqed\n",
    ];
    for t in ok {
        assert_eq!(check(&format!("{}{}", lib, t)), Ok(base + 1), "{}", t);
    }
}

/// flip: an equation or disequation the other way round -- a fact (also
/// under `all`s and premises) or, as a step, the goal / a fact h.
#[test]
fn flip_turns_equations_around() {
    let lib = format!("{}{}", core_file("logic.core"), core_file("sets.core"));
    let base = check(&lib).unwrap();
    let ok = [
        "theorem t(a, b): a = b -> b = a\nproof\n  assume h\n  show flip(h)\nqed\n",
        "theorem t(a, b): a != b -> b != a\nproof\n  assume h\n  show flip(h)\nqed\n",
        "theorem t(a, b): !(a = b) -> !(b = a)\nproof\n  assume h\n  show flip(h)\nqed\n",
        "theorem t(c): (all x y. x in c -> int_add(x, y) = int_add(y, x)) -> all x y. x in c -> int_add(y, x) = int_add(x, y)\nproof\n  assume h\n  show flip(h)\nqed\n",
        "theorem t(a, b): a = b -> b = a\nproof\n  assume h\n  flip\n  show h\nqed\n",
        "theorem t(x, y): y = 3 -> y = x -> 3 = x\nproof\n  assume h g\n  flip in g\n  flip\n  show by rsimp(g, h)\nqed\n",
    ];
    for t in ok {
        assert_eq!(check(&format!("{}{}", lib, t)), Ok(base + 1), "{}", t);
    }
    rejected(&format!("{}theorem t(a): a in a -> a in a\nproof\n  assume h\n  show flip(h)\nqed\n", lib), "flip: not an equation or disequation");
}

/// Implicit unfolding: a definition is unfolded where the fact and the goal
/// differ (a defined goal under `assume` / `fix`, a stated premise, a
/// premise of `mp` / `apply`, a destructured fact) -- not an `irreducible`
/// one, which `unfold` still unfolds.
#[test]
fn implicit_and_explicit_unfolding() {
    let logic = core_file("logic.core");
    let base = check(&logic).unwrap();
    let defs = format!("{}def self_imp(a) := a -> a\ndef both(a, b) := a && b\ndef every(x. p) := all x. p(x)\n", logic);
    let ok = [
        // the goal's head unfolded by `assume` / `fix`
        "theorem t(p): self_imp(p)\nproof\n  assume h\n  show h\nqed\n",
        "theorem t: every(x. self_imp(x))\nproof\n  fix x\n  assume h\n  show h\nqed\n",
        // a stated premise, unfolded
        "theorem t(p, q): self_imp(p) -> q -> q\nproof\n  assume h: p -> p\n  assume g: q\n  show g\nqed\n",
        // the conclusion: the goal up to unfolding
        "theorem t(p, q): p -> q -> both(p, q)\nproof\n  assume h g\n  have c: p && q by taut(h, g)\n  show c\nqed\n",
        // modus ponens with a folded premise; destructuring a defined fact
        "theorem t(p, q): both(p, q) -> (p && q -> q) -> q\nproof\n  assume h k\n  show mp(k, h)\nqed\n",
        "theorem t(p, q): both(p, q) -> q\nproof\n  assume h\n  have a b := h\n  show b\nqed\n",
        // the explicit step, on the goal and on a fact
        "theorem t(p, q): both(p, q) -> both(q, p)\nproof\n  assume h\n  unfold both in h\n  unfold both\n  show by taut(h)\nqed\n",
    ];
    for t in ok {
        assert_eq!(check(&format!("{}{}", defs, t)), Ok(base + 1), "{}", t);
    }
    // irreducible: left folded implicitly, unfolded explicitly
    let irr = format!("{}irreducible both\n", defs);
    rejected(&format!("{}theorem t(p, q): p -> q -> both(p, q)\nproof\n  assume h g\n  have c: p && q by taut(h, g)\n  show c\nqed\n", irr), "not `p -> q -> both(p, q)`");
    assert_eq!(check(&format!("{}theorem t(p, q): p -> q -> both(p, q)\nproof\n  assume h g\n  unfold both\n  show by taut(h, g)\nqed\n", irr)), Ok(base + 1));
}

#[test]
fn a_proof_of_another_statement_is_rejected() {
    rejected("theorem bad(a): a\nproof\n  show imp_weaken[a := a, b := a]\nqed\n", "this proves `a -> a -> a`, not `a`");
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

/// With the loop library: (theorems, theorems resting on open lemmas).
fn check_loop(src: &str) -> Result<(usize, Vec<String>), String> {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    for f in ["logic.core", "sets.core", "nat.core", "loop.core"] {
        load_with(&mut env, &core_file(f), false, Some(&mut ScriptProver)).unwrap();
    }
    load_with(&mut env, src, false, Some(&mut ScriptProver)).map(|r| (r.theorems.len(), r.conditional)).map_err(|e| e.0)
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
    // products as monomials (the ring laws), nonnegative products
    assert_eq!(arith_ok("int_mul(a, int_add(b, x)) = int_add(int_mul(x, a), int_mul(b, a))", &[]), Ok(1));
    assert_eq!(arith_ok("a in omega -> b in omega -> int_le(0, int_mul(a, b))", &[na, nb]), Ok(1));
    // division by a symbolic divisor: x = m q + r
    assert_eq!(arith_ok("a in omega -> int_lt(0, b) -> a = int_add(int_mul(b, int_div(a, b)), int_mod(a, b))", &[na, ("h", "int_lt(0, b)")]), Ok(1));
    // pow2(k + 1) is 2 pow2(k)
    assert_eq!(arith_ok("a in omega -> int_mul(x, pow2(int_add(a, 1))) = int_mul(2, int_mul(pow2(a), x))", &[na]), Ok(1));
    // equals for equals (the premises' equations), also inside products
    assert_eq!(arith_ok("a = b -> int_mul(x, a) = int_mul(x, b)", &[("h", "a = b")]), Ok(1));
}

/// With the libraries up to core/loop.core: `src`'s error, if any.
fn check_all(src: &str) -> Result<usize, String> {
    let mut env = Env::new();
    load(&mut env, &core_file("prelude.core"), true).unwrap();
    for f in ["logic.core", "sets.core", "nat.core", "records.core", "list.core", "loop.core"] {
        load_with(&mut env, &core_file(f), false, Some(&mut ScriptProver)).unwrap();
    }
    load_with(&mut env, src, false, Some(&mut ScriptProver)).map(|r| r.theorems.len()).map_err(|e| e.0)
}

#[test]
fn extension_soundness_holes_stay_closed() {
    // (each found in a review: a derivation of `false`, or of a false statement)
    let bad = [
        // a name the extensions rely on, redefined: rejected
        "def x86_64_linux.store_le(b, a, n, v) := empty\n",
        "def gimple.bytes_at(vm, a, n) := 7\n",
        // simp's matching: no bound variable escapes
        "theorem cap(x y. r): (all x. ex y. r(x, y)) -> ex y. r(y, y)\nproof\n  assume h\n  show by simp(h)\nqed\n",
        "theorem refl_le: all z. int_le(z, z)\nproof\n  fix z\n  show by arith()\nqed\ntheorem c2: ex x. all z. int_le(x, z)\nproof\n  show by simp(refl_le)\nqed\n",
        // bits of a negative width: empty
        "theorem b: ex x. x in bits(int_neg(1))\nproof\n  show by simp()\nqed\n",
        // a store's bytes: at addresses (64 bits) only
        "def x86_64_linux.store_le(b, a, n, v) := fn_build(bits(64), x. ite(int_lt(bits_sub(64, x, a), n), bits_of_int(8, int_div(v, int_pow(256, bits_sub(64, x, a)))), app(b, x)))\ntheorem r: app(x86_64_linux.store_le(empty, 0, 1, 1), 18446744073709551616) = 1\nproof\n  show by simp()\nqed\n",
        // sign extension to fewer bits, a slice beyond the word
        "theorem s: bits_sext(16, 8, 300) = 300\nproof\n  show by simp()\nqed\n",
        "theorem s: bits_set_slice(8, 0, 15, 0, 300) = 300\nproof\n  show by simp()\nqed\n",
        // a set that holds is not `true`
        "theorem l(x): x -> x = true\nproof\n  assume h\n  show by simp(h)\nqed\n",
        // ok(s, v) is a pair (members' matching)
        "theorem m: false\nproof\n  have m := members({set_select(omega, n. n = 0 && (ex a b. ok(5, 6) = pair(a, b)))})\n  have i := all_elim(m, {0})\n  have e: ok(5, 6) = pair(0, pair(5, 6)) by defs(refl({pair(0, pair(5, 6))}), ok, tag)\n  have x: ex a b. ok(5, 6) = pair(a, b) by ex_intro({0}, {pair(5, 6)}, e)\n  have o: 0 in omega by simp()\n  have z: 0 in set_select(omega, n. n = 0 && (ex a b. ok(5, 6) = pair(a, b))) by sel(taut(o, refl({0}), x))\n  show by taut(i, z)\nqed\n",
    ];
    for src in bad {
        assert!(check_all(src).is_err(), "accepted:\n{}", src);
    }
}

#[test]
fn arithmetic_failures_name_what_was_not_read() {
    // an equation of a term not known to be an integer: a mere proposition
    let r = arith_ok("int_le(a, 3) -> int_le(3, a) -> a = 3", &[("h1", "int_le(a, 3)"), ("h2", "int_le(3, a)")]);
    let e = r.unwrap_err();
    assert!(e.contains("a = 3 = false") && e.contains("`a` not known to be an integer"), "{}", e);
}

#[test]
fn arithmetic_with_many_atoms() {
    // a chain of 80 comparisons: no limit on the atoms, cases split as needed
    let n = 80;
    let hyps: Vec<(String, String)> = (0..n).map(|k| (format!("h{}", k), format!("int_le(a{}, a{})", k, k + 1))).collect();
    let params: Vec<String> = (0..=n).map(|k| format!("a{}", k)).collect();
    let stmt = format!("{} -> int_le(a0, a{})", hyps.iter().map(|(_, t)| t.as_str()).collect::<Vec<_>>().join(" -> "), n);
    let assumes: String = hyps.iter().map(|(h, t)| format!("  assume {}: {}\n", h, t)).collect();
    let names: Vec<&str> = hyps.iter().map(|(h, _)| h.as_str()).collect();
    let src = format!("theorem t({}): {}\nproof\n{}  show by arith({})\nqed\n", params.join(", "), stmt, assumes, names.join(", "));
    assert_eq!(check_nat(&src), Ok(1));
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
    // a square's sign needs its factor's: this true fact is not proven
    bad("int_le(0, int_mul(x, x))", &[]);
    // products: no ordering of factors assumed
    bad("a in omega -> b in omega -> int_le(int_mul(a, b), int_mul(a, a))", &[na, nb]);
    bad("int_mul(a, b) = int_mul(a, a)", &[]);
    // equals for equals only: other products not equal
    bad("a = b -> int_mul(x, a) = int_mul(a, b)", &[("h", "a = b")]);
    // coefficients beyond i128: no constraint (not a contradiction)
    bad("!int_lt(int_neg(int_pow(4, 63)), int_pow(4, 63))", &[]);
    let big = "int_add(int_mul(int_neg(int_pow(4, 63)), int_mul(2, x)), int_neg(b)) in omega";
    bad(&format!("{} -> false", big), &[("h", big)]);
    // a remainder is a value: x itself only if x is an integer
    bad("int_le(0, x) -> int_lt(x, a) -> int_mod(x, a) = x", &[("h1", "int_le(0, x)"), ("h2", "int_lt(x, a)")]);
    // a bits_build word of a width not known natural: not known an integer
    bad("bits_and(a, x, b) = int_add(bits_and(a, x, b), 0)", &[]);
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
    // records: updates at the same keys compare field by field; an update
    // on one side only is not the identity (the base may lack the key)
    assert_eq!(check("theorem x(s, a, b, c): fn_update(fn_update(fn_update(s, \"x\", a), \"y\", b), \"x\", c) = fn_update(fn_update(s, \"y\", b), \"x\", c)\nproof\n  show by simp()\nqed\n"), Ok(1));
    rejected("theorem x(s, a): fn_update(s, \"x\", a) = fn_update(fn_update(s, \"x\", a), \"y\", app(s, \"y\"))\nproof\n  show by simp()\nqed\n", "simp");
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
fn the_bit_library_checks() {
    let n = check_nat(&core_file("bits.core")).unwrap();
    assert_eq!(n, 45);
}

#[test]
fn the_loop_library_checks() {
    let n = check_nat(&core_file("loop.core")).unwrap();
    assert_eq!(n, 22);
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
    // -- by the theorem while_unroll (core/loop.core), which an unrolling
    // step uses: without the loop library, refused
    let src = count_thm("ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 3", ", unroll");
    assert_eq!(check_loop(&src), Ok((1, vec![])));
    assert!(check_nat(&src).unwrap_err().contains("while_unroll"));
    match check_loop(&count_thm("ex l. o = ok(l, empty) && fst(l) = s && snd(l) = 2", ", unroll")) {
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

/// `assume h1 h2` (the goal's premises), `fix x y`, conjuncts by position
/// (`h.k`, `R(..).k`), `have a b := P` / `obtain x y, a b from P` naming
/// conjuncts as written (`_` none), a line continued by `:=`.
#[test]
fn premises_conjuncts_and_witnesses() {
    let ok = "theorem t1(a, b, c): a && b && c -> b && a\nproof\n  assume h\n  show b && a by taut(h.2, h.1)\nqed\n\
theorem t2(a, b, c): a -> b -> c -> a && c\nproof\n  assume ha hb hc\n  show a && c by taut(ha, hc)\nqed\n\
theorem t3: (ex x y. x = 1 && y = x && 2 = 2) -> ex y. y = 1\nproof\n  assume h\n  obtain x y, hx hy _ from h\n  have e: y = 1\n    := trans(hy, hx)\n  show ex_intro({y}, {z. z = 1}, e)\nqed\n\
theorem t4: all x y. x = y -> y = x\nproof\n  fix x y\n  assume h\n  show := sym(h)\nqed\n\
theorem t5(a, b): (a && b) && (b && a) -> a\nproof\n  assume h\n  show := h.3.2\nqed\n\
theorem t6(a, b, c): a && b && c -> c && a\nproof\n  assume h\n  have ha _ hc := h\n  show c && a by taut(ha, hc)\nqed\n\
theorem t7(a, b): a && b -> b\nproof\n  assume h\n  show := mp(imp_refl[a := a && b], h).2\nqed\n";
    assert_eq!(check_nat(ok), Ok(7));
    // a premise from the goal: only where the goal is an implication
    rejected("theorem b(a): a\nproof\n  assume h\n  show := h\nqed\n", "not known to be an implication");
    // conjuncts: in range; names: one per conjunct
    rejected("theorem b(a, b): a && b -> a\nproof\n  assume h\n  show := h.3\nqed\n", "has conjuncts 1 to 2");
    rejected("theorem b: (ex x. x = 1 && x = 1) -> 1 = 1\nproof\n  assume h\n  obtain x, p q r from h\n  show := refl({1})\nqed\n", "3 names for 2 conjuncts");
}

/// Labelled conjuncts (`name: φ`, term metadata): selected by `h.name` (a
/// definition at the head unfolded), `R(args).name`, `have {a, x = b} :=
/// P`, `obtain x, {a} from P` -- in a definition, a theorem's statement,
/// an `ex` body; a labelled group counts as one conjunct.
#[test]
fn labelled_conjuncts() {
    let ok = "def P(x, y) := px: x = 1 && grp: (x = x && y = y) && py: y = 2\n\
theorem t1(a, b): P(a, b) -> b = 2 && a = 1\nproof\n  assume h\n  show by taut(h.py, h.px)\nqed\n\
theorem t2(a, b): P(a, b) -> a = a\nproof\n  assume h\n  have {grp, q = py} := h\n  show := grp.1\nqed\n\
theorem t3(a): (ex x. one: x = a && two: a = x) -> ex y. y = a\nproof\n  assume h\n  obtain x, {one} from h\n  show by ex_intro({x}, one)\nqed\n\
theorem t4(a, b): a = b -> lft: a = b && rgt: b = a\nproof\n  assume h\n  show by taut(h, sym(h))\nqed\n\
theorem t5(a, b): a = b -> b = a\nproof\n  assume h\n  show := mp(t4[a := a, b := b], h).rgt\nqed\n";
    assert_eq!(check_nat(ok), Ok(5));
    // an unknown label: the ones there are
    rejected("def P(x) := px: x = 1 && qx: x = x\ntheorem b(a): P(a) -> a = 1\nproof\n  assume h\n  show := h.rx\nqed\n", "its labels: px, qx");
    // labels are not logic: a statement with them is the one without
    assert_eq!(check_nat("theorem e(a): a = a -> l: a = a\nproof\n  assume h\n  show := h\nqed\n"), Ok(1));
}

/// A mismatch names the first differing subterm and its path: premises by
/// number, conjuncts however nested, arguments of the symbols on the way.
#[test]
fn mismatches_point_at_the_difference() {
    rejected(
        "theorem r(a, b, c): (a -> b -> c) -> a -> b -> c\nproof\n  assume h: a -> c -> c\n  show := h\nqed\n",
        "first difference at: premise 1 (also differing: premise 3) > premise 2\n    expected: b\n    given:    c",
    );
    rejected(
        "theorem m(a, b): a -> (a -> b = a) -> b = a\nproof\n  assume h: a\n  assume k: a -> a = b\n  show := mp(k, h)\nqed\n",
        "first difference at: premise 2 (also differing: the conclusion) > conclusion > eq, argument 1 (also differing: argument 2)\n    expected: b\n    given:    a",
    );
}

/// Goal rules inline (`(φ by R(args))`), lemmas instantiated by binder
/// name (`l[x := t]`, the other leading `all`s kept), `conj(p1, .., pn)`.
#[test]
fn inline_goals_instances_and_conj() {
    let ok = "theorem t(a, b): a && b -> b && a\nproof\n  assume h\n  show by taut((a by taut(h)), (b by taut(h)))\nqed\n\
theorem l1: all x y. x = y -> y = x\nproof\n  fix x y\n  assume h\n  show := sym(h)\nqed\n\
theorem t1(a): a = 1 -> 1 = a\nproof\n  assume h\n  show := mp(l1[x := a, y := 1], h)\nqed\n\
theorem t2(a): all x. a = x -> x = a\nproof\n  show := l1[x := a]\nqed\n\
theorem t3(a): all x. x = a -> a = x\nproof\n  show := l1[y := a]\nqed\n\
theorem t4(a, b, c): a -> b -> c -> a && b && c\nproof\n  assume ha hb hc\n  show := conj(ha, hb, hc)\nqed\n";
    assert_eq!(check(&format!("{}{}", core_file("logic.core"), ok)), Ok(check(&core_file("logic.core")).unwrap() + 6));
    rejected(&format!("{}theorem f(a, b): a -> b -> b && a\nproof\n  assume ha hb\n  show := conj(ha, hb)\nqed\n", core_file("logic.core")), "");
}

/// simp normalizes its equations by each other: chains of equations.
#[test]
fn simp_chains_equations() {
    let ok = "theorem t7(c, m, w, p): app(p, app(c, \"os\")) = 1 -> app(c, \"os\") = app(m, \"os\") -> app(w, \"os\") = app(m, \"os\") -> app(p, app(w, \"os\")) = 1\nproof\n  assume h e1 e2\n  show by simp(h, e1, e2)\nqed\n";
    assert_eq!(check_nat(ok), Ok(1));
}

/// rewrite / expand: every occurrence, or the chosen ones (`{k}`, outer
/// before inner, left to right); an equation under `all`s rewrites its
/// instances also under binders -- its variables matched only by terms
/// without the variables bound inside the instance.
#[test]
fn rewrite_and_expand_occurrences() {
    let ok = "def twice(x) := int_add(x, x)\n\
theorem r1(a, f): a = 1 -> app(f, a) = a -> app(f, 1) = a\nproof\n  assume e h\n  show := rewrite(e, h, {1})\nqed\n\
theorem r2(a, f): a = 1 -> app(f, a) = a -> app(f, a) = 1\nproof\n  assume e h\n  show := rewrite(e, h, {2})\nqed\n\
theorem comm: all x y. int_add(x, y) = int_add(y, x)\nproof\n  fix x y\n  show by arith()\nqed\n\
theorem r3(s): (all z. int_add(z, 1) in s) -> (all z. int_add(1, z) in s)\nproof\n  assume h\n  show := rewrite(comm, h)\nqed\n\
theorem r4(a, b): twice(a) = twice(b) -> int_add(a, a) = twice(b)\nproof\n  assume h\n  show := expand(h, twice, {1})\nqed\n\
theorem r5(a, b): twice(a) = twice(b) -> twice(a) = int_add(b, b)\nproof\n  assume h\n  show := expand(h, twice, {2})\nqed\n\
theorem c1: (all p. (ex x. p) = p) -> (all y. ex x. y = 1) -> (all y. y = 1)\nproof\n  assume e h\n  show := rewrite(e, h)\nqed\n";
    assert_eq!(check_nat(ok), Ok(7));
    rejected(
        "theorem comm: all x y. int_add(x, y) = int_add(y, x)\nproof\n  fix x y\n  show by arith()\nqed\n\
theorem r6(s): (all z. int_add(z, 1) in s) -> (all z. int_add(1, z) in s)\nproof\n  assume h\n  show := rewrite(comm, h, {2})\nqed\n",
        "no instance 2 of the left side",
    );
    // `p` cannot take `x = 1`: x is bound by the equation's own `ex`
    rejected(
        "theorem c2: (all p. (ex x. p) = p) -> (ex x. x = 1) -> 1 = 1\nproof\n  assume e h\n  have g := rewrite(e, h)\n  show by taut()\nqed\n",
        "no instance of the left side",
    );
}

/// Function parameters of lemmas (`v` in `x. v`) are found by matching:
/// `apply` against its premises, `show :=` / `defs` against the goal --
/// a parameter applied to bound variables matches a term over them.
#[test]
fn higher_order_parameters_matched() {
    let ok = "theorem t1(a): runs(app(fn_build(omega, x. mkprog(s o. o = ok(s, x))), a), 0, ok(0, a)) -> a in omega\nproof\n  assume h\n  have k := apply(runs_fn_build, h)\n  show := k.1\nqed\n\
theorem l(x. f): fn_build(omega, x. f(x)) = fn_build(omega, x. f(x))\nproof\n  show := refl({fn_build(omega, x. f(x))})\nqed\n\
theorem t2: fn_build(omega, x. succ(x)) = fn_build(omega, x. succ(x))\nproof\n  show := l\nqed\n";
    assert_eq!(check_nat(ok), Ok(3));
    // a bound variable the parameter does not take: no match
    rejected("theorem l(f): (ex x. f = x) -> true\nproof\n  assume h\n  show by taut()\nqed\n\
theorem t(a): (ex x. x = x) -> true\nproof\n  assume h\n  show := apply(l, h)\nqed\n", "does not match");
}

/// Unfolding a definition with a function parameter (`letin(a, x. f)`)
/// whose argument mentions variables bound around the occurrence: the
/// argument's parameters take the call's arguments, its other variables
/// stay bound where they were.
#[test]
fn unfolding_under_binders_with_function_arguments() {
    let ok = "theorem t1(v): (ex z. z = v) -> (ex z. letin(v, x. z = x))\nproof\n  assume h\n  show by defs(h, letin)\nqed\n\
theorem t2(v): (all y. ex z. app(z, y) = v) -> (all y. ex z. letin(v, x. letin(y, u. app(z, u) = x)))\nproof\n  assume h\n  show by defs(h, letin)\nqed\n\
theorem t3(v): (ex z. all y. z = y) -> (ex z. letin(v, x. all y. letin(y, u. z = u)))\nproof\n  assume h\n  show by defs(h, letin)\nqed\n";
    assert_eq!(check(ok), Ok(3));
    // the variables kept apart: z = v is not v = z
    rejected("theorem b(v): (ex z. z = v) -> (ex z. letin(v, x. x = z))\nproof\n  assume h\n  show by defs(h, letin)\nqed\n", "differ after unfolding");
}
