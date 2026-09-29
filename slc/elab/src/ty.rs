//! Types of the checker. Widths and set-valued type parameters are kernel
//! terms, so dependent types (`bits[8*n]`) substitute naturally.

use sl_kernel::Term;

#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    /// no information yet (e.g. an untyped numeric literal)
    Unknown,
    Bool,
    Nat,
    Int,
    NatInf,
    Str,
    Unit,
    Bits(Term),
    Tuple(Vec<Ty>),
    Map(Box<Ty>, Box<Ty>),
    List(Box<Ty>),
    Seq(Box<Ty>),
    Set(Box<Ty>),
    Opt(Box<Ty>),
    /// record / enum / sum declared with this qualified name
    Rec(String),
    Enum(String),
    Sum(String),
    /// the instruction type of a table
    Insn(String),
    State(StateTy),
    /// a refinement: base type and the set term
    Refine(Box<Ty>, Term),
    /// proc values: functions from arguments to programs
    Proc { state: Box<Ty>, params: Vec<Ty>, ret: Box<Ty> },
    /// a program (a proc applied to its arguments)
    Prog(Box<Ty>, Box<Ty>),
    Outcome(Box<Ty>, Box<Ty>),
    Exc,
    /// a type parameter (its set is `term`)
    Param(String, Term),
}

/// A state type: a declared base state plus extensions (ghost fields of a
/// derived state, or a state type parameter).
#[derive(Clone, Debug, PartialEq)]
pub struct StateTy {
    pub base: String,
    pub ext: Vec<Ext>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Ext {
    /// the own fields of a `state X extends ...` declaration
    Fields(String),
    Param(String, Term),
}

impl Ty {
    pub fn strip(&self) -> &Ty {
        match self {
            Ty::Refine(b, _) => b.strip(),
            t => t,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self.strip(), Ty::Nat | Ty::Int | Ty::NatInf | Ty::Bits(_) | Ty::Enum(_) | Ty::Unknown)
    }

    pub fn describe(&self) -> String {
        match self {
            Ty::Unknown => "?".into(),
            Ty::Bool => "bool".into(),
            Ty::Nat => "nat".into(),
            Ty::Int => "int".into(),
            Ty::NatInf => "natinf".into(),
            Ty::Str => "string".into(),
            Ty::Unit => "()".into(),
            Ty::Bits(_) => "bits[..]".into(),
            Ty::Tuple(ts) => format!("({})", ts.iter().map(|t| t.describe()).collect::<Vec<_>>().join(", ")),
            Ty::Map(a, b) => format!("{} -> {}", a.describe(), b.describe()),
            Ty::List(t) => format!("List[{}]", t.describe()),
            Ty::Seq(t) => format!("Seq[{}]", t.describe()),
            Ty::Set(t) => format!("Set[{}]", t.describe()),
            Ty::Opt(t) => format!("Option[{}]", t.describe()),
            Ty::Rec(n) | Ty::Enum(n) | Ty::Sum(n) | Ty::Insn(n) => n.clone(),
            Ty::State(s) => {
                let mut out = s.base.clone();
                for e in &s.ext {
                    match e {
                        Ext::Fields(n) => out.push_str(&format!(" & {}.ghost", n)),
                        Ext::Param(n, _) => out.push_str(&format!(" & {}", n)),
                    }
                }
                out
            }
            Ty::Refine(b, _) => format!("{{{}| ..}}", b.describe()),
            Ty::Proc { .. } => "proc".into(),
            Ty::Prog(..) => "program".into(),
            Ty::Outcome(..) => "Outcome".into(),
            Ty::Exc => "exception".into(),
            Ty::Param(n, _) => n.clone(),
        }
    }
}
