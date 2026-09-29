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
