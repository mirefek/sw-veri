//! Abstract syntax of SL.
//!
//! Types that occur inside expressions (`bits[64](x)`, `modrm_enum[E]()`,
//! `sext[w](v)`) are parsed as expressions; the checker interprets them.

use sl_kernel::Nat;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Hash)]
pub struct Span {
    pub file: u32,
    pub lo: u32,
    pub hi: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

// ---------------------------------------------------------------------
//  Types

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// `Name` or `Name[args]` (`Option[Reg]`, `CFun[World & G]`, `bits[8*n]`)
    Named(Ident, Vec<GenArg>),
    /// `A -> B` (total map)
    Map(Box<Type>, Box<Type>),
    /// `(A, B)`; `()` is the unit type
    Tuple(Vec<Type>),
    /// `{x: T | P}`
    Refine(Ident, Box<Type>, Box<Expr>),
    /// `proc[S](A, B) -> R`
    Proc { state: Option<Box<Type>>, params: Vec<Type>, ret: Option<Box<Type>> },
    /// `S & G` (state with extra fields)
    And(Box<Type>, Box<Type>),
    /// `enum bits[k]` (kind of a generic parameter)
    EnumKind(Box<Expr>),
}

/// Generic argument: a type (`Option[Reg]`) or a value (`bits[8*n]`).
#[derive(Clone, Debug, PartialEq)]
pub enum GenArg {
    Type(Type),
    Expr(Expr),
}

// ---------------------------------------------------------------------
//  Expressions

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,  // !
    Neg,  // -
    BNot, // ~
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    SLt,
    SLe,
    SGt,
    SGe,
    In,
    NotIn,
    BOr,
    BXor,
    BAnd,
    Shl,
    Shr,
    Sar,
    Add,
    Sub,
    Concat, // ++
    Mul,
    Div,
    Mod,
    SDiv,
    SMod,
    Pow,
    Range, // a..b
    Refines,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinderKind {
    All,
    Ex,
    Sum,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Num(Nat),
    Bool(bool),
    Str(String),
    Name(Ident),
    SelfState,
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    /// `e[a]`, `e[a, b]` (also generic instantiation `f[w]`, conversion `bits[64]`)
    Index(Box<Expr>, Vec<Expr>),
    /// `e[hi:lo]`
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `e[a..]`
    From(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, Ident),
    /// `flags.{af, pf}` (lvalues only)
    FieldSet(Box<Expr>, Vec<Ident>),
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    /// `[elem for pat in iter if cond]`
    ListComp { elem: Box<Expr>, pat: Pattern, iter: Box<Expr>, cond: Option<Box<Expr>> },
    Set(Vec<Expr>),
    /// `{x: T | P}`
    SetBuilder { var: Ident, ty: Type, cond: Box<Expr> },
    /// `Name { f: e, g }`
    Record { name: Ident, fields: Vec<(Ident, Expr)> },
    /// `e with { f: e2 }`
    With(Box<Expr>, Vec<(Ident, Expr)>),
    If(Box<Expr>, Block, Box<Block>),
    Match(Box<Expr>, Vec<Arm>),
    /// `all x: T. P`, `ex x: T. P`, `sum i in a..b. e`
    Binder { kind: BinderKind, vars: Vec<(Ident, Option<Type>)>, domain: Option<Box<Expr>>, body: Box<Expr> },
    /// `any x: T where P`, `any T where P` (var bound by the enclosing `let`)
    /// `any [x:] T [where P] [else S]`; `any?` (maybe) may also take S when
    /// P has solutions. `else` only in `let x = any ...`, and S must leave.
    Any { var: Option<Ident>, ty: Type, cond: Option<Box<Expr>>, maybe: bool, els: Option<Box<Block>> },
    /// `(x: T, y: U) => body`
    Lambda(Vec<Param>, Box<Block>),
    /// `e is pat`
    Is(Box<Expr>, Pattern),
    /// a block in expression position (`if`/`match` arms, lambda bodies)
    Block(Block),
    /// `do[S] { stmts }`: a program as a value
    Do(Option<Type>, Block),
    /// `with view(args) { stmts }`: run a proc of the view's state through the view
    WithView(Box<Expr>, Block),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Arm {
    pub pats: Vec<Pattern>, // alternatives
    pub body: Block,        // single statement arms are one-element blocks
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Wild(Span),
    /// a name: a binding, or a nullary constructor / enum value (resolved later)
    Name(Ident),
    Ctor(Ident, Vec<Pattern>),
    Num(Nat, Span),
    Bool(bool, Span),
    Tuple(Vec<Pattern>, Span),
}

// ---------------------------------------------------------------------
//  Statements

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum StmtKind {
    Let { pat: Pattern, ty: Option<Type>, value: Expr },
    Var { name: Ident, ty: Option<Type>, value: Expr },
    Assign { ghost: bool, target: Expr, value: Expr },
    Emit { target: Expr, event: Expr },
    If { cond: Expr, then: Block, els: Option<Block> },
    Match { scrut: Expr, arms: Vec<Arm> },
    While { cond: Expr, body: Block },
    For { var: Ident, iter: Expr, body: Block },
    Loop(Block),
    Break,
    Return(Option<Expr>),
    Raise(Expr),
    Try { body: Block, catches: Vec<(Pattern, Block)> },
    Either(Vec<Block>),
    /// `havoc targets [where P] [else S]`: S runs if P has no solution;
    /// `havoc?` (maybe) may also run S when it has one
    Havoc { targets: Vec<Expr>, cond: Option<Expr>, maybe: bool, els: Option<Block> },
    Require(Expr),
    Guard(Expr),
    Undefined,
    Expr(Expr),
    Block(Block),
}

// ---------------------------------------------------------------------
//  Declarations

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Generic {
    pub name: Ident,
    pub kind: Option<Type>, // `[w: Width]`, `[E: enum bits[3]]`, `[G]`
}

#[derive(Clone, Debug, PartialEq)]
pub enum Body {
    Expr(Expr),
    Block(Block),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub name: Ident,
    pub ty: Type,
    pub ghost: bool,
    pub trace: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Variant {
    pub name: Ident,
    pub params: Vec<Param>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumItem {
    pub name: Ident,
    pub value: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeDef {
    Alias(Type),
    Sum(Vec<Variant>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum ViewGet {
    Expr(Expr),
    Block(Block),
}

#[derive(Clone, Debug, PartialEq)]
pub enum FnKind {
    Fn,
    Pred,
    Decoder,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FnDecl {
    pub kind: FnKind,
    pub name: Ident,
    pub generics: Vec<Generic>,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub body: Body,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ProcDecl {
    pub name: Ident,
    pub state: Option<Type>,
    pub generics: Vec<Generic>,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub body: Body,
}

/// One item of a table row.
#[derive(Clone, Debug, PartialEq)]
pub enum Item {
    /// the next byte must equal the value
    Byte(Expr),
    /// run a decoder, binding (a pattern of) its result
    Bind(Pattern, Expr),
    /// run a decoder, ignoring its result
    Run(Expr),
    /// guard on bound values
    Guard(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    pub items: Vec<Item>,
    pub body: Block,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TableEntry {
    Row(Row),
    With { pat: Pattern, item: Expr, entries: Vec<TableEntry> },
    /// `for x in E except a, b { ... }`: one copy per item of enum E (but a, b)
    For { var: Ident, ty: Ident, except: Vec<Ident>, entries: Vec<TableEntry> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Table {
    pub name: Ident,
    pub using: Vec<Ident>,
    pub context: Expr,
    pub before: Vec<Item>,
    pub after: Vec<Item>,
    pub entries: Vec<TableEntry>,
}

/// Hole category of a notation pattern.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HoleKind {
    Nat,
    Byte,
    Ident,
    Type,
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatTok {
    Tok(String),
    Hole(String, HoleKind),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Notation {
    pub pattern: Vec<PatTok>,
    /// expansion, as source tokens (holes are substituted textually)
    pub expansion: Vec<crate::lexer::Token>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclKind {
    TypeDecl { name: Ident, generics: Vec<Generic>, def: TypeDef },
    Enum { name: Ident, repr: Option<Type>, items: Vec<EnumItem> },
    Record { name: Ident, fields: Vec<Field> },
    State { name: Ident, extends: Option<Type>, fields: Vec<Field> },
    Const { name: Ident, ty: Option<Type>, value: Expr },
    Exception { name: Ident, params: Vec<Param> },
    Fn(FnDecl),
    Proc(ProcDecl),
    View { name: Ident, state: Option<Type>, params: Vec<Param>, ty: Type, get: ViewGet, set_var: Ident, set: Block },
    DecoderContext(Type),
    Notations { name: Ident, notations: Vec<Notation> },
    Table(Table),
    ParamPred { name: Ident, params: Vec<Param> },
    ParamFn { name: Ident, params: Vec<Param>, ret: Type },
    Law { name: Ident, params: Vec<Param>, prop: Expr },
    Theorem { name: Ident, generics: Vec<Generic>, params: Vec<Param>, prop: Expr },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Decl {
    pub kind: DeclKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleKind {
    Spec,
    Layer,
}

#[derive(Clone, Debug, PartialEq)]
pub struct File {
    pub kind: ModuleKind,
    pub module: Ident,
    pub uses: Vec<Ident>,
    pub decls: Vec<Decl>,
}

impl Decl {
    pub fn name(&self) -> Option<&Ident> {
        Some(match &self.kind {
            DeclKind::TypeDecl { name, .. }
            | DeclKind::Enum { name, .. }
            | DeclKind::Record { name, .. }
            | DeclKind::State { name, .. }
            | DeclKind::Const { name, .. }
            | DeclKind::Exception { name, .. }
            | DeclKind::View { name, .. }
            | DeclKind::Notations { name, .. }
            | DeclKind::ParamPred { name, .. }
            | DeclKind::ParamFn { name, .. }
            | DeclKind::Law { name, .. }
            | DeclKind::Theorem { name, .. } => name,
            DeclKind::Fn(f) => &f.name,
            DeclKind::Proc(p) => &p.name,
            DeclKind::Table(t) => &t.name,
            DeclKind::DecoderContext(_) => return None,
        })
    }
}
