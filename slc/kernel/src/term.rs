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

/// A hasher for keys of node addresses and small integers (memo tables of
/// one walk): a multiply and rotate per word, not SipHash -- the keys are
/// no input an adversary chooses.
#[derive(Default, Clone, Copy)]
pub struct PtrHasher(u64);
impl std::hash::Hasher for PtrHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(*b as u64);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64)
    }
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64)
    }
}
pub type PtrMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<PtrHasher>>;
pub type PtrSet<K> = std::collections::HashSet<K, std::hash::BuildHasherDefault<PtrHasher>>;

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
    /// the node's hash, computed once (its children's are theirs): equal
    /// terms hash alike, unequal hashes are unequal terms
    hash: u64,
    /// the variables in it, as bits v mod 64 (none set: no variable v in
    /// it -- a substitution or a search for variables skips it)
    vbits: u64,
    /// one more than the largest bound-variable index in it, as written
    /// (binders not subtracted: a bound on its loose depth -- 0: no
    /// bound variable at all). A walk replacing or shifting the bound
    /// variables from some depth d up skips a subterm with bmax <= d.
    bmax: u32,
    label: Option<Rc<str>>,
    /// (metadata too) the name written at an `all`/`ex` binder, for
    /// instantiating it by name; at another binding symbol (`letin(a, x.
    /// f)`), the names its arguments bind, in order, separated by spaces
    bind: Option<Rc<str>>,
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        Rc::ptr_eq(&self.0, &other.0) || (self.0.hash == other.0.hash && self.0.node == other.0.node)
    }
}

impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash)
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
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        node.hash(&mut h);
        let hash = h.finish();
        // (an equal node alive, unlabelled: that node -- see `intern`)
        if let Some(t) = intern::find(hash, &node) {
            return t;
        }
        let vbits = match &node {
            Node::Var(v, args) => args.iter().fold(1u64 << (v % 64), |b, a| b | a.0.vbits),
            Node::App(_, args) => args.iter().fold(0, |b, a| b | a.0.vbits),
            _ => 0,
        };
        let bmax = match &node {
            Node::BVar(i) => i + 1,
            Node::Var(_, args) | Node::App(_, args) => args.iter().map(|a| a.0.bmax).max().unwrap_or(0),
            _ => 0,
        };
        let t = Term(Rc::new(Inner { node, hash, vbits, bmax, label: None, bind: None }));
        intern::add(&t);
        t
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

    /// The term's structural hash (the same in every run: an order for a
    /// hash table's entries that does not depend on the table's seed).
    pub fn shash(&self) -> u64 {
        self.0.hash
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
        Term(Rc::new(Inner { node: self.0.node.clone(), hash: self.0.hash, vbits: self.0.vbits, bmax: self.0.bmax, label, bind: self.0.bind.clone() }))
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
        Term(Rc::new(Inner { node: self.0.node.clone(), hash: self.0.hash, vbits: self.0.vbits, bmax: self.0.bmax, label: self.0.label.clone(), bind }))
    }

    /// `self` with `outer`'s label, if it has one (the outer label wins).
    pub(crate) fn labelled_as(self, outer: &Term) -> Term {
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

    /// Held more than once (by several parents, or a parent and a caller):
    /// a walk over the DAG may reach it again; a node held once is reached
    /// again only through a parent reached again. Memo tables of a walk
    /// need only the shared nodes.
    pub fn shared(&self) -> bool {
        Rc::strong_count(&self.0) > 1
    }

    /// The same node (not just an equal one).
    pub fn ptr_eq(&self, other: &Term) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    /// The node's identity (its address), for memo tables of one pass.
    pub fn ptr_id(&self) -> usize {
        Rc::as_ptr(&self.0) as usize
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
        if self.0.bmax == 0 {
            return 0;
        }
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
        // (in the order of first occurrence; a shared node visited once --
        // its variables are out after its first visit)
        fn go(t: &Term, out: &mut Vec<VarId>, seen: &mut PtrSet<usize>) {
            if t.0.vbits == 0 || (t.shared() && !seen.insert(t.ptr_id())) {
                return;
            }
            match t.node() {
                Node::Var(v, args) => {
                    if !out.contains(v) {
                        out.push(*v);
                    }
                    args.iter().for_each(|a| go(a, out, seen));
                }
                Node::App(_, args) => args.iter().for_each(|a| go(a, out, seen)),
                _ => {}
            }
        }
        go(self, out, &mut PtrSet::default())
    }

    /// Adds `d` to every bound variable with index >= `cutoff`.
    pub fn shift(&self, d: u32, cutoff: u32, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
        // (no bound variable from cutoff up: itself)
        if d == 0 || self.0.bmax <= cutoff {
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
        self.inst_params_at(args, 0, binders, &mut PtrMap::default())
    }

    /// (`memo`: a shared node's instance at a depth made once -- terms are
    /// DAGs, a walk as a tree repeats a shared part per path; keyed by the
    /// node, as equal terms may carry other labels. A part with no bound
    /// variable from `depth` up is itself.)
    fn inst_params_at(&self, args: &[Term], depth: u32, binders: &dyn Fn(SymId, usize) -> u32, memo: &mut PtrMap<(usize, u32), Term>) -> Term {
        if self.0.bmax <= depth {
            return self.clone();
        }
        let k = args.len() as u32;
        match self.node() {
            Node::BVar(i) if *i >= depth => {
                let j = i - depth;
                debug_assert!(j < k, "value has loose variables beyond its parameters");
                args[(k - 1 - j) as usize].shift(depth, 0, binders).labelled_as(self)
            }
            Node::BVar(_) | Node::Nat(_) | Node::Bytes(_) => self.clone(),
            Node::Var(_, a) | Node::App(_, a) => {
                let key = (self.ptr_id(), depth);
                let sh = self.shared();
                if sh {
                    if let Some(r) = memo.get(&key) {
                        return r.clone();
                    }
                }
                let r = match self.node() {
                    Node::App(s, _) => self.with_args(a.iter().enumerate().map(|(i, x)| x.inst_params_at(args, depth + binders(*s, i), binders, memo)).collect()),
                    _ => self.with_args(a.iter().map(|x| x.inst_params_at(args, depth, binders, memo)).collect()),
                };
                if sh {
                    memo.insert(key, r.clone());
                }
                r
            }
        }
    }

    /// v possibly in it (false: certainly not)
    pub fn may_contain_var(&self, v: VarId) -> bool {
        self.0.vbits & (1u64 << (v % 64)) != 0
    }

    /// every variable of `other` possibly in it (false: `other` certainly
    /// not a part of it)
    pub fn may_contain_vars_of(&self, other: &Term) -> bool {
        self.0.vbits & other.0.vbits == other.0.vbits
    }

    /// Substitutes schematic variable `v` (arity k) by `value` (k parameters).
    pub fn subst_var(&self, v: VarId, value: &Term, binders: &dyn Fn(SymId, usize) -> u32) -> Term {
        // (no variable v in it: itself)
        if self.0.vbits & (1u64 << (v % 64)) == 0 {
            return self.clone();
        }
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

/// Hash-consing: an equal node alive, made by `Term::mk` (unlabelled, no
/// binder name), is reused instead of a new one. Equality stays as it is
/// (`Term::eq`: the same node, or equal hash and node); with equal terms
/// mostly one node, it is mostly a pointer compare, and a node's children
/// compare by pointer. Not part of the logic: a term is the same term
/// either way. The table holds weak references (a term lives as long as
/// its users keep it); the dead ones are dropped when the table has
/// doubled since the last purge.
mod intern {
    use super::{Inner, Node, Term};
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::{Rc, Weak};

    /// (the key is the node's hash already: not hashed again)
    #[derive(Default)]
    struct Id(u64);
    impl std::hash::Hasher for Id {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, _: &[u8]) {
            unreachable!("Id hashes u64 keys only")
        }
        fn write_u64(&mut self, x: u64) {
            self.0 = x;
        }
    }

    /// (one node per key: keys of other nodes colliding, the later kept --
    /// a lost share, not a wrong term: `find` checks the node)
    #[derive(Default)]
    struct Table {
        map: HashMap<u64, Weak<Inner>, std::hash::BuildHasherDefault<Id>>,
        /// the entries at the last purge
        at_purge: usize,
    }

    thread_local! {
        static T: RefCell<Table> = RefCell::new(Table::default());
    }

    /// (the same node: its children the same nodes -- not just equal ones,
    /// which may carry other labels, and labels must stay where they are)
    fn same(a: &Node, b: &Node) -> bool {
        match (a, b) {
            (Node::App(s, x), Node::App(t, y)) => s == t && x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| p.ptr_eq(q)),
            (Node::Var(v, x), Node::Var(w, y)) => v == w && x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| p.ptr_eq(q)),
            (Node::App(..) | Node::Var(..), _) | (_, Node::App(..) | Node::Var(..)) => false,
            _ => a == b,
        }
    }

    /// the table's key: the node's identity -- its hash with its children's
    /// addresses (equal nodes whose children are other nodes, e.g.
    /// labelled ones, have other keys: a bucket holds the same nodes only,
    /// not every equal one)
    fn key(hash: u64, node: &Node) -> u64 {
        match node {
            Node::App(_, a) | Node::Var(_, a) => a.iter().fold(hash, |h, x| (h ^ x.ptr_id() as u64).wrapping_mul(0x100000001b3).rotate_left(29)),
            _ => hash,
        }
    }

    pub(super) fn find(hash: u64, node: &Node) -> Option<Term> {
        T.with(|t| {
            let t = t.borrow();
            // (an upgraded node not the same is dropped again: another
            // holder keeps it, no node is freed while the table is borrowed)
            let rc = t.map.get(&key(hash, node))?.upgrade()?;
            same(&rc.node, node).then_some(Term(rc))
        })
    }

    pub(super) fn add(term: &Term) {
        T.with(|t| {
            let mut t = t.borrow_mut();
            t.map.insert(key(term.0.hash, &term.0.node), Rc::downgrade(&term.0));
            // (the dead entries dropped when the table has grown 4 times
            // since the last purge: a weak entry keeps its node's
            // allocation)
            if t.map.len() > 4 * t.at_purge.max(1 << 16) {
                t.map.retain(|_, w| w.strong_count() > 0);
                t.at_purge = t.map.len();
            }
        })
    }
}
