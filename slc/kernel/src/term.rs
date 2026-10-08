//! Terms of the background logic.
//!
//! A single universe: terms denote sets (propositions are the sets `false`
//! and `true`). A constant takes arguments, each of which may bind a fixed
//! number of variables (de Bruijn indices). Schematic variables are
//! second-order: a variable of arity k is applied to k terms, and is
//! instantiated by a term with k parameters.
//!
//! Binder convention: an argument binding `x0 .. x{k-1}` sees `x{k-1}` as
//! `BVar(0)` and `x0` as `BVar(k-1)`. A value for a variable of arity k uses
//! the same convention for its parameters.

use crate::nat::Nat;
use std::rc::Rc;

pub type SymId = u32;
pub type VarId = u32;

/// A term, with an optional label: metadata for proofs (`name: φ`, a
/// conjunct named), not part of the logic -- equality and hashing ignore
/// it, and no rule looks at it. Rebuilding a node keeps its label; where a
/// variable is substituted, the variable's label (the outer one) wins over
/// the value's.
#[derive(Clone, Debug)]
pub struct Term(Rc<Inner>);

#[derive(Debug)]
struct Inner {
    node: Node,
    label: Option<Rc<str>>,
    /// (metadata too) the name written at an `all`/`ex` binder, for
    /// instantiating it by name
    bind: Option<Rc<str>>,
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || self.0.node == other.0.node
    }
}

impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.node.hash(state)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Node {
    App(SymId, Box<[Term]>),
    Var(VarId, Box<[Term]>),
    BVar(u32),
    Nat(Nat),
    Bytes(Rc<[u8]>),
}

impl Term {
    fn mk(node: Node) -> Term {
        Term(Rc::new(Inner { node, label: None, bind: None }))
    }
    pub fn app(s: SymId, args: Vec<Term>) -> Term {
        Term::mk(Node::App(s, args.into_boxed_slice()))
    }
    pub fn var(v: VarId, args: Vec<Term>) -> Term {
        Term::mk(Node::Var(v, args.into_boxed_slice()))
    }
    pub fn bvar(i: u32) -> Term {
        Term::mk(Node::BVar(i))
    }
    pub fn nat(n: Nat) -> Term {
        Term::mk(Node::Nat(n))
    }
    pub fn bytes(b: &[u8]) -> Term {
        Term::mk(Node::Bytes(b.into()))
    }
    pub fn node(&self) -> &Node {
        &self.0.node
    }

    /// The term's label (metadata, see `Term`).
    pub fn label(&self) -> Option<&str> {
        self.0.label.as_deref()
    }

    /// The same term labelled `label` (None: unlabelled).
    pub fn with_label(&self, label: Option<Rc<str>>) -> Term {
        if self.0.label == label {
            return self.clone();
        }
        Term(Rc::new(Inner { node: self.0.node.clone(), label, bind: self.0.bind.clone() }))
    }

    /// The name written at this `all`/`ex` binder (metadata, see `Term`).
    pub fn binder_name(&self) -> Option<&str> {
        self.0.bind.as_deref()
    }

    /// The same term with the binder name `bind`.
    pub fn with_binder_name(&self, bind: Option<Rc<str>>) -> Term {
        if self.0.bind == bind {
            return self.clone();
        }
        Term(Rc::new(Inner { node: self.0.node.clone(), label: self.0.label.clone(), bind }))
    }

    /// `self` with `outer`'s label, if it has one (the outer label wins).
    fn labelled_as(self, outer: &Term) -> Term {
        match &outer.0.label {
            Some(l) => self.with_label(Some(l.clone())),
            None => self,
        }
    }

    /// a rebuilt `old`: its label and binder name kept
    fn rebuilt_from(self, old: &Term) -> Term {
        let t = self.labelled_as(old);
        match &old.0.bind {
            Some(b) => t.with_binder_name(Some(b.clone())),
            None => t,
        }
    }

    /// The same node (not just an equal one).
    pub fn ptr_eq(&self, other: &Term) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    /// This application (or variable) with the arguments `args`: the term
    /// itself, not a rebuilt copy, when every argument is the old one (so
    /// unchanged terms stay shared, and equal terms often pointer-equal).
    pub fn with_args(&self, args: Vec<Term>) -> Term {
        match self.node() {
            Node::App(s, old) => {
                if old.len() == args.len() && old.iter().zip(&args).all(|(a, b)| a.ptr_eq(b)) {
                    self.clone()
                } else {
                    Term::app(*s, args).rebuilt_from(self)
                }
            }
            Node::Var(v, old) => {
                if old.len() == args.len() && old.iter().zip(&args).all(|(a, b)| a.ptr_eq(b)) {
                    self.clone()
                } else {
                    Term::var(*v, args).rebuilt_from(self)
                }
            }
            _ => self.clone(),
        }
    }

    /// Number of enclosing binders needed to make the term closed
    /// (0 = no loose bound variables). `binders(s, i)` gives the number of
    /// variables bound by argument `i` of symbol `s`.
    pub fn loose_depth(&self, binders: &dyn Fn(SymId, usize) -> u32) -> u32 {
        match self.node() {
            Node::BVar(i) => i + 1,
            Node::Nat(_) | Node::Bytes(_) => 0,
            Node::Var(_, args) => args.iter().map(|a| a.loose_depth(binders)).max().unwrap_or(0),
            Node::App(s, args) => args
                .iter()
                .enumerate()
                .map(|(i, a)| a.loose_depth(binders).saturating_sub(binders(*s, i)))
                .max()
                .unwrap_or(0),
        }
    }

    /// Collects schematic variables occurring in the term.
    pub fn vars(&self, out: &mut Vec<VarId>) {
        match self.node() {
            Node::Var(v, args) => {
                if !out.contains(v) {
                    out.push(*v);
                }
                args.iter().for_each(|a| a.vars(out));
            }
            Node::App(_, args) => args.iter().for_each(|a| a.vars(out)),
            _ => {}
        }
    }

    /// Adds `d` to every bound variable with index >= `cutoff`.
    pub fn shift(&self, d: u32, cutoff: u32, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
        if d == 0 {
            return self.clone();
        }
        match self.node() {
            Node::BVar(i) if *i >= cutoff => Term::bvar(i + d).labelled_as(self),
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => self.clone(),
            Node::Var(_, args) => self.with_args(args.iter().map(|a| a.shift(d, cutoff, binders)).collect()),
            Node::App(s, args) => self.with_args(
                args.iter()
                    .enumerate()
                    .map(|(i, a)| a.shift(d, cutoff + binders(*s, i), binders))
                    .collect(),
            ),
        }
    }

    /// Replaces the parameters of a k-ary value (`BVar(k-1-i)` = parameter
    /// `i`, see module docs) by `args`, which live in the context of the
    /// substitution site. The value must have no other loose variables.
    pub fn instantiate_params(&self, args: &[Term], binders: &dyn Fn(SymId, usize) -> u32) -> Term {
        self.inst_params_at(args, 0, binders)
    }

    fn inst_params_at(&self, args: &[Term], depth: u32, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
        let k = args.len() as u32;
        match self.node() {
            Node::BVar(i) if *i >= depth => {
                let j = i - depth;
                debug_assert!(j < k, "value has loose variables beyond its parameters");
                args[(k - 1 - j) as usize].shift(depth, 0, binders).labelled_as(self)
            }
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => self.clone(),
            Node::Var(_, a) => self.with_args(a.iter().map(|x| x.inst_params_at(args, depth, binders)).collect()),
            Node::App(s, a) => self.with_args(
                a.iter()
                    .enumerate()
                    .map(|(i, x)| x.inst_params_at(args, depth + binders(*s, i), binders))
                    .collect(),
            ),
        }
    }

    /// Substitutes schematic variable `v` (arity k) by `value` (k parameters).
    pub fn subst_var(&self, v: VarId, value: &Term, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
        match self.node() {
            Node::Var(w, args) => {
                let args: Vec<Term> = args.iter().map(|a| a.subst_var(v, value, binders)).collect();
                if *w == v {
                    value.instantiate_params(&args, binders).labelled_as(self)
                } else {
                    self.with_args(args)
                }
            }
            Node::App(_, args) => self.with_args(args.iter().map(|a| a.subst_var(v, value, binders)).collect()),
            _ => self.clone(),
        }
    }
}
