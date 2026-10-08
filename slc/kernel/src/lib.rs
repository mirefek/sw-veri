//! The trusted kernel: terms, inference rules, and the core file format.

pub mod env;
pub mod ext;
pub mod nat;
pub mod syntax;
pub mod term;

pub use env::{Env, KResult, KernelError, SymKind, Thm};
pub use nat::Nat;
pub use term::{Node, SymId, Term, VarId};

#[cfg(test)]
mod tests {
    use super::*;

    const MINI: &str = r#"
        const false
        def not(a) := a -> false
        def true := not(false)
        def or(a, b) := !a -> b
        def and(a, b) := !(!a || !b)
        def iff(a, b) := (a -> b) && (b -> a)
        const ex(x. p)
        axiom ex_intro(a, x. p): p(a) -> ex(x. p(x))
        def all(x. p) := !ex(x. !p(x))
        axiom eq_refl(a): a = a
        claim c1: all x. ex y. x = y
    "#;

    fn mini() -> Env {
        let mut env = Env::new();
        syntax::load(&mut env, MINI, true).expect("mini prelude loads");
        env
    }

    #[test]
    fn load_and_print() {
        let env = mini();
        assert_eq!(env.claims.len(), 1);
        let p = syntax::Printer::new(&env);
        assert_eq!(p.term(&env.claims[0].1), "all x0. ex x1. x0 = x1");
        let all = env.sym_by_name["all"];
        assert_eq!(p.def_line(all).unwrap(), "def all(y0. p) := !(ex x0. !p(x0))");
    }

    #[test]
    fn instantiate_second_order() {
        let mut env = mini();
        let (_, ax) = env.axioms.iter().find(|a| a.0 == "ex_intro").unwrap().clone();
        // p := (y. y = y), a := 7
        let vars: Vec<VarId> = { let mut v = Vec::new(); ax.prop().vars(&mut v); v };
        let (a, p) = (vars[1], vars[0]); // order of occurrence: p first, then a
        let eq = env.builtins.eq;
        let value = Term::app(eq, vec![Term::bvar(0), Term::bvar(0)]);
        let t1 = env.instantiate(&ax, p, &value).unwrap();
        let t2 = env.instantiate(&t1, a, &Term::nat(Nat::from_u64(7))).unwrap();
        let pr = syntax::Printer::new(&env);
        assert_eq!(pr.term(t2.prop()), "7 = 7 -> (ex x0. x0 = x0)");
        // modus ponens with eq_refl instantiated at 7
        let (_, refl) = env.axioms.iter().find(|a| a.0 == "eq_refl").unwrap().clone();
        let mut rv = Vec::new();
        refl.prop().vars(&mut rv);
        let r7 = env.instantiate(&refl, rv[0], &Term::nat(Nat::from_u64(7))).unwrap();
        let concl = env.modus_ponens(&t2, &r7).unwrap();
        assert_eq!(pr.term(concl.prop()), "ex x0. x0 = x0");
        let _ = env.new_var("unused", 0);
    }

    #[test]
    fn rejects_bad_input() {
        let mut env = mini();
        // loose variable in a definition
        assert!(syntax::load(&mut env, "def bad := q", false).is_err());
        // wrong binder arity
        assert!(syntax::load(&mut env, "claim bad2: ex(7)", false).is_err());
        // axioms are refused when not allowed
        assert!(syntax::load(&mut env, "axiom bad3: false", false).is_err());
        // redefinition
        assert!(syntax::load(&mut env, "def not(a) := a", false).is_err());
    }

    #[test]
    fn cached_theorems_only_from_a_cache_file() {
        let mut env = mini();
        // a source file cannot claim a theorem without its proof
        assert!(syntax::load(&mut env, "theorem t: all x. x = x cached", false).is_err());
        assert!(env.fact("t").is_none());
        // a cache file's statement is recorded as proven
        let rep = syntax::load_cached(&mut env, "theorem t: all x. x = x cached", false).unwrap();
        assert_eq!(rep.theorems, vec!["t".to_string()]);
        assert!(env.fact("t").is_some());
        // still no axioms in it
        assert!(syntax::load_cached(&mut env, "axiom bad: false", false).is_err());
    }

    #[test]
    fn labels_are_metadata() {
        let mut env = mini();
        syntax::load(&mut env, "def p(a, b) := l: a = b && r: b = a", false).unwrap();
        let p = env.sym_by_name["p"];
        let SymKind::Defined { params, body } = env.syms[p as usize].kind.clone() else { panic!() };
        let Node::App(_, parts) = body.node() else { panic!() };
        assert_eq!(parts[1].label(), Some("r"));
        // equal to the unlabelled term, labels kept through substitution
        let bare = parts[1].with_label(None);
        assert_eq!(parts[1], bare);
        let seven = Term::nat(Nat::from_u64(7));
        let inst = parts[1].subst_var(params[0], &seven, &env.binders_fn());
        assert_eq!(inst.label(), Some("r"));
        // the outer label wins at a substitution site
        let lv = Term::var(params[0], vec![]).with_label(Some("outer".into()));
        let lab = seven.with_label(Some("inner".into()));
        assert_eq!(lv.subst_var(params[0], &lab, &env.binders_fn()).label(), Some("outer"));
        // printed, and read back
        let pr = syntax::Printer::new(&env);
        assert_eq!(pr.term(&body), "l: a = b && r: b = a");
    }

    #[test]
    fn literals() {
        let env = mini();
        let b = &env.builtins;
        let big = Term::nat(Nat::pow2(64));
        let one = Term::nat(Nat::from_u64(1));
        let t = env.lit_compute(b.lit_sub, &big, &one).unwrap();
        let pr = syntax::Printer::new(&env);
        assert_eq!(pr.term(t.prop()), "lit_sub(0x10000000000000000, 1) = 18446744073709551615");
        assert!(env.lit_compute(b.lit_sub, &one, &big).is_err());
        let bytes = Term::bytes(&[0x7f, b'E', b'L', b'F']);
        let t = env.bytes_at(&bytes, &one).unwrap();
        assert_eq!(pr.term(t.prop()), "bytes_at(bytes\"7f454c46\", 1) = 69");
    }
}
