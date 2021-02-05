use crate::codespan_reporting::diagnostic::Label;
use std::ops::Fn;
use std::rc::Rc;

use crate::{
    context::{
        Context, Diagnostic, DisplayContext, DisplayWithContext, FileID, IsDiagnostic, Location,
        StringID,
    },
    lexer::Token,
    lexer::TokenType,
    core::types::BuiltinType,
};
use std::fmt;
use TokenType::*;

/// This is used to differentiatate different kinds of raw nodes.
///
/// When creating a raw node, we always attach the correct tag.
#[derive(Clone, Copy, Debug)]
#[repr(u8)]
enum Tag {
    IntLitExpr,
    BinExprAdd,
    BinExprMul,
    BinExprSub,
    BinExprDiv,
    BinExprOr,
    BinExprAnd,
    BinExprBitOr,
    BinExprBitAnd,
    BinExprEqual,
    BinExprNotEqual,
    BinExprLess,
    BinExprLessEqual,
    BinExprGreater,
    BinExprGreaterEqual,
    UnaryExprNegate,
    UnaryExprNot,
    VarExpr,
    AssignExpr,
    AssignExprAdd,
    AssignExprMul,
    AssignExprSub,
    AssignExprDiv,
    AssignExprBitOr,
    AssignExprBitAnd,
    FunctionExpr,
    ExprStatement,
    ReturnStatement,
    ReturnEmptyStatement,
    VarStatement,
    IfStatement,
    IfElseStatement,
    BlockStatement,
    AST,
    Function,
    Name,
    Type,
}

/// Represents the kind of shape that a node can have.
///
/// We need this, because everything we have is stored in this unified
/// node type, and we need to handle terminal things like strings and literals.
#[derive(Clone, Debug)]
enum NodeShape {
    /// This node is a terminal reference to a string
    String(StringID),
    /// This node is a terminal reference to an integer
    IntLit(u32),
    /// This node is a termainl reference to a builtin type
    Type(BuiltinType),
    /// This node branches off to contain other nodes
    Branch(Vec<Rc<Node>>),
    /// This node doesn't branch off
    Empty,
}

/// Represents a single raw Node in our AST.
///
/// Our overall AST structure is based on representing things
/// with our plain untyped representation, and then using a typed outer layer
/// for actually manipulating things.
#[derive(Clone, Debug)]
struct Node {
    /// The location of this node in the original file
    location: Location,
    /// A tag associated with this node
    tag: Tag,
    /// The shape of this node
    shape: NodeShape,
}

impl Node {
    fn string(&self) -> StringID {
        match &self.shape {
            NodeShape::String(s) => *s,
            other => panic!("expected string, found: {:?}", other),
        }
    }

    fn int_lit(&self) -> u32 {
        match &self.shape {
            NodeShape::IntLit(v) => *v,
            other => panic!("expected int lit, found: {:?}", other),
        }
    }

    fn typ(&self) -> BuiltinType {
        match &self.shape {
            NodeShape::Type(t) => *t,
            other => panic!("expected type, found: {:?}", other),
        }
    }

    fn branch(&self) -> &[Rc<Node>] {
        match &self.shape {
            NodeShape::Branch(v) => v,
            other => panic!("expected branch, found: {:?}", other),
        }
    }
}

/// A trait allowing us to query the location of some AST node.
pub trait HasLocation {
    fn location(&self) -> &Location;
}

// We use this macro, since every ast type has an easily accessible underlying node
macro_rules! impl_has_location {
    ($x:ident) => {
        impl HasLocation for $x {
            fn location(&self) -> &Location {
                &self.0.location
            }
        }
    };
    ($x:ident, $y:ident) => {
        impl HasLocation for $x {
            fn location(&self) -> &Location {
                &self.$y.location
            }
        }
    };
}

// We use this macro, since we have this kind of variant pattern so often
macro_rules! impl_variant {
    ($typ:ident, $variant:ident) => {
        impl Into<$typ> for $variant {
            fn into(self) -> $typ {
                $typ::$variant(self)
            }
        }
    };
}

/// Represents a strongly typed enumeration of expressions.
#[derive(Clone, Debug)]
pub enum ExprKind {
    /// An single int as an expression
    IntLitExpr(IntLitExpr),
    /// A single variable as an expression
    VarExpr(VarExpr),
    /// An assignment to a variable, as an expression
    AssignExpr(AssignExpr),
    /// Binary operators, as an expression
    BinExpr(BinExpr),
    /// Unary operators, as an expression
    UnaryExpr(UnaryExpr),
    /// A function call, as an expression
    FunctionExpr(FunctionExpr),
}

impl DisplayWithContext for ExprKind {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExprKind::IntLitExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::VarExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::AssignExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::BinExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::UnaryExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::FunctionExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
        }
    }
}

/// Represents a generic kind of expression
#[derive(Clone, Debug)]
pub struct Expr(Rc<Node>);

impl Expr {
    /// Get a strongly typed variant from this expression
    pub fn kind(&self) -> ExprKind {
        match &self.0.tag {
            Tag::VarExpr => VarExpr(self.0.clone()).into(),
            Tag::IntLitExpr => IntLitExpr(self.0.clone()).into(),
            Tag::BinExprAdd => BinExpr {
                op: BinOp::Add,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprSub => BinExpr {
                op: BinOp::Sub,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprMul => BinExpr {
                op: BinOp::Mul,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprDiv => BinExpr {
                op: BinOp::Div,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprAnd => BinExpr {
                op: BinOp::And,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprOr => BinExpr {
                op: BinOp::Or,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprBitAnd => BinExpr {
                op: BinOp::BitAnd,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprBitOr => BinExpr {
                op: BinOp::BitOr,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprEqual => BinExpr {
                op: BinOp::Equal,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprNotEqual => BinExpr {
                op: BinOp::NotEqual,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprGreater => BinExpr {
                op: BinOp::Greater,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprGreaterEqual => BinExpr {
                op: BinOp::GreaterEqual,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprLess => BinExpr {
                op: BinOp::Less,
                node: self.0.clone(),
            }
            .into(),
            Tag::BinExprLessEqual => BinExpr {
                op: BinOp::LessEqual,
                node: self.0.clone(),
            }
            .into(),
            Tag::UnaryExprNegate => UnaryExpr {
                op: UnaryOp::Negate,
                node: self.0.clone(),
            }
            .into(),
            Tag::UnaryExprNot => UnaryExpr {
                op: UnaryOp::Not,
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExpr => AssignExpr {
                op: None,
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExprAdd => AssignExpr {
                op: Some(BinOp::Add),
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExprSub => AssignExpr {
                op: Some(BinOp::Sub),
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExprMul => AssignExpr {
                op: Some(BinOp::Mul),
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExprDiv => AssignExpr {
                op: Some(BinOp::Div),
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExprBitOr => AssignExpr {
                op: Some(BinOp::BitOr),
                node: self.0.clone(),
            }
            .into(),
            Tag::AssignExprBitAnd => AssignExpr {
                op: Some(BinOp::BitAnd),
                node: self.0.clone(),
            }
            .into(),
            Tag::FunctionExpr => FunctionExpr(self.0.clone()).into(),
            other => panic!("unexpected tag {:?}", other),
        }
    }
}

impl DisplayWithContext for Expr {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind().fmt_with(ctx, f)
    }
}

impl_has_location!(Expr);

/// A function call, used as an expressi0on
#[derive(Clone, Debug)]
pub struct FunctionExpr(Rc<Node>);

impl FunctionExpr {
    /// Get the function name of this expression
    pub fn function(&self) -> StringID {
        self.0.branch()[0].string()
    }

    /// The number of parameters passed to this function
    pub fn param_count(&self) -> usize {
        self.0.branch().len() - 1
    }

    /// The ith param passed to this function
    pub fn param(&self, i: usize) -> Expr {
        Expr(self.0.branch()[i + 1].clone())
    }
}

impl DisplayWithContext for FunctionExpr {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(call {}", ctx.ctx.get_string(self.function()))?;
        for i in 0..self.param_count() {
            write!(f, " {}", self.param(i).with_ctx(ctx))?;
        }
        write!(f, ")")
    }
}

impl_variant!(ExprKind, FunctionExpr);
impl_has_location!(FunctionExpr);

/// An integer literal, used as an expression
#[derive(Clone, Debug)]
pub struct IntLitExpr(Rc<Node>);

impl IntLitExpr {
    /// The underlying integer composing this expression
    pub fn int_lit(&self) -> u32 {
        self.0.int_lit()
    }
}

impl DisplayWithContext for IntLitExpr {
    fn fmt_with(&self, _ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.int_lit())
    }
}

impl_variant!(ExprKind, IntLitExpr);
impl_has_location!(IntLitExpr);

/// A reference to a variable, used as an expression
#[derive(Clone, Debug)]
pub struct VarExpr(Rc<Node>);

impl VarExpr {
    /// The string that composes this variable name
    pub fn var(&self) -> StringID {
        self.0.string()
    }
}

impl DisplayWithContext for VarExpr {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", ctx.ctx.get_string(self.var()))
    }
}

impl_variant!(ExprKind, VarExpr);
impl_has_location!(VarExpr);

/// An assignment to a variable, as an expression
#[derive(Clone, Debug)]
pub struct AssignExpr {
    pub op: Option<BinOp>,
    node: Rc<Node>,
}

impl AssignExpr {
    pub fn var_location(&self) -> Location {
        self.node.branch()[0].location
    }

    pub fn var(&self) -> StringID {
        self.node.branch()[0].string()
    }

    pub fn expr(&self) -> Expr {
        Expr(self.node.branch()[1].clone())
    }
}

impl DisplayWithContext for AssignExpr {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        match self.op {
            None => write!(f, "(=")?,
            Some(op) => write!(f, "({}=", op)?,
        };
        write!(
            f,
            " {} {})",
            ctx.ctx.get_string(self.var()),
            self.expr().with_ctx(ctx)
        )
    }
}

impl_variant!(ExprKind, AssignExpr);
impl_has_location!(AssignExpr, node);

/// The kind of binary operation we're using
#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    /// Add two integers together
    Add,
    /// Multiply two integers
    Mul,
    /// Subtract two integers
    Sub,
    /// Divide two integers
    Div,
    /// Bitwise or
    BitOr,
    /// Bitwise and
    BitAnd,
    /// Boolean or
    Or,
    /// Boolean And
    And,
    /// Equality
    Equal,
    /// Inequality
    NotEqual,
    /// Less than
    Less,
    /// Less than or equal
    LessEqual,
    /// Greater than
    Greater,
    /// Greater than or equal
    GreaterEqual,
}

impl BinOp {
    pub fn types(&self) -> (Option<BuiltinType>, Option<BuiltinType>, BuiltinType) {
        use BinOp::*;
        use BuiltinType::*;

        match self {
            Add | Mul | Sub | Div | BitOr | BitAnd => (Some(I32), Some(I32), I32),
            Or | And => (Some(Bool), Some(Bool), Bool),
            Equal | NotEqual => (None, None, Bool),
            Less | LessEqual | Greater | GreaterEqual => (Some(I32), Some(I32), Bool),
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Div => write!(f, "/"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::Or => write!(f, "||"),
            BinOp::And => write!(f, "&&"),
            BinOp::Equal => write!(f, "=="),
            BinOp::NotEqual => write!(f, "!="),
            BinOp::Less => write!(f, "<"),
            BinOp::LessEqual => write!(f, "<="),
            BinOp::Greater => write!(f, ">"),
            BinOp::GreaterEqual => write!(f, ">="),
        }
    }
}

/// An expression applying a binary operator to two expressions
#[derive(Clone, Debug)]
pub struct BinExpr {
    /// The operator being used
    pub op: BinOp,
    node: Rc<Node>,
}

impl BinExpr {
    /// The left expression for this operator
    pub fn lhs(&self) -> Expr {
        Expr(self.node.branch()[0].clone())
    }

    /// The right expression for this operator
    pub fn rhs(&self) -> Expr {
        Expr(self.node.branch()[1].clone())
    }
}

impl DisplayWithContext for BinExpr {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({} {} {})",
            self.op,
            self.lhs().with_ctx(ctx),
            self.rhs().with_ctx(ctx)
        )
    }
}

impl_variant!(ExprKind, BinExpr);
impl_has_location!(BinExpr, node);

/// A unary operator of some kind
#[derive(Clone, Debug)]
pub enum UnaryOp {
    /// Negation of an integer
    Negate,
    /// The opposite of a boolean
    Not,
}

impl fmt::Display for UnaryOp {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnaryOp::Negate => write!(f, "-"),
            UnaryOp::Not => write!(f, "!"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct UnaryExpr {
    /// The operator being used
    pub op: UnaryOp,
    node: Rc<Node>,
}

impl UnaryExpr {
    pub fn expr(&self) -> Expr {
        Expr(self.node.branch()[0].clone())
    }
}

impl DisplayWithContext for UnaryExpr {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.op, self.expr().with_ctx(ctx))
    }
}

impl_variant!(ExprKind, UnaryExpr);
impl_has_location!(UnaryExpr, node);

/// Represents a strongly typed kind of statement
#[derive(Clone, Debug)]
pub enum StatementKind {
    /// A return statement
    ReturnStatement(ReturnStatement),
    /// The creation of a new variable
    VarStatement(VarStatement),
    /// A block containing multiple statements
    BlockStatement(BlockStatement),
    /// An if statement, possibly containing an else
    IfStatement(IfStatement),
    /// An expression, used as a statement
    ExprStatement(ExprStatement),
}

impl DisplayWithContext for StatementKind {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            StatementKind::ReturnStatement(s) => s.fmt_with(ctx, f),
            StatementKind::VarStatement(s) => s.fmt_with(ctx, f),
            StatementKind::BlockStatement(s) => s.fmt_with(ctx, f),
            StatementKind::IfStatement(s) => s.fmt_with(ctx, f),
            StatementKind::ExprStatement(s) => s.fmt_with(ctx, f),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Statement(Rc<Node>);

impl Statement {
    pub fn kind(&self) -> StatementKind {
        match &self.0.tag {
            Tag::ReturnStatement => ReturnStatement::new(false, self.0.clone()).into(),
            Tag::ReturnEmptyStatement => ReturnStatement::new(true, self.0.clone()).into(),
            Tag::VarStatement => VarStatement(self.0.clone()).into(),
            Tag::BlockStatement => BlockStatement(self.0.clone()).into(),
            Tag::IfStatement => IfStatement::new(false, self.0.clone()).into(),
            Tag::IfElseStatement => IfStatement::new(true, self.0.clone()).into(),
            Tag::ExprStatement => ExprStatement(self.0.clone()).into(),
            other => panic!("unexpected tag {:?}", other),
        }
    }
}

impl DisplayWithContext for Statement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind().fmt_with(ctx, f)
    }
}

impl_has_location!(Statement);

/// A statement returning the value of some expression
#[derive(Clone, Debug)]
pub struct ReturnStatement {
    empty: bool,
    node: Rc<Node>,
}

impl ReturnStatement {
    fn new(empty: bool, node: Rc<Node>) -> Self {
        ReturnStatement { empty, node }
    }

    /// The underlying expression being returned
    pub fn expr(&self) -> Option<Expr> {
        if self.empty {
            None
        } else {
            Some(Expr(self.node.branch()[0].clone()))
        }
    }
}

impl DisplayWithContext for ReturnStatement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expr() {
            None => write!(f, "(return)"),
            Some(e) => write!(f, "(return {})", e.with_ctx(ctx)),
        }
    }
}

impl_variant!(StatementKind, ReturnStatement);
impl_has_location!(ReturnStatement, node);

/// A statement defining a new variable
#[derive(Clone, Debug)]
pub struct VarStatement(Rc<Node>);

impl VarStatement {
    /// The string of the variable being declared
    pub fn var(&self) -> StringID {
        self.0.branch()[0].string()
    }

    /// The type of the variable being declared
    pub fn typ(&self) -> BuiltinType {
        self.0.branch()[1].typ()
    }

    /// The expression value for the variable
    pub fn expr(&self) -> Expr {
        Expr(self.0.branch()[2].clone())
    }
}

impl DisplayWithContext for VarStatement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(var {} {} {})",
            ctx.ctx.get_string(self.var()),
            self.typ(),
            self.expr().with_ctx(ctx)
        )
    }
}

impl_variant!(StatementKind, VarStatement);
impl_has_location!(VarStatement);

/// A block statement is composed of multiple statements together
#[derive(Clone, Debug)]
pub struct BlockStatement(Rc<Node>);

impl BlockStatement {
    /// The number of statements in this block
    pub fn len(&self) -> usize {
        self.0.branch().len()
    }

    /// The ith statement in this block
    pub fn statement(&self, i: usize) -> Statement {
        Statement(self.0.branch()[i].clone())
    }
}

impl DisplayWithContext for BlockStatement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(block\n")?;
        let block_ctx = ctx.indented();
        for i in 0..self.len() {
            block_ctx.blank_space(f)?;
            write!(f, "{}\n", self.statement(i).with_ctx(block_ctx))?;
        }
        ctx.blank_space(f)?;
        write!(f, ")")
    }
}

impl_variant!(StatementKind, BlockStatement);
impl_has_location!(BlockStatement);

/// Represents a conditional statement.
///
/// We might have an optional else branch as well.
#[derive(Clone, Debug)]
pub struct IfStatement {
    has_else: bool,
    node: Rc<Node>,
}

impl IfStatement {
    fn new(has_else: bool, node: Rc<Node>) -> Self {
        IfStatement { has_else, node }
    }

    /// The expression making up the condition of this statement
    pub fn cond(&self) -> Expr {
        Expr(self.node.branch()[0].clone())
    }

    /// The branch to use when the condition holds
    pub fn if_branch(&self) -> Statement {
        Statement(self.node.branch()[1].clone())
    }

    /// The branch to use when the condition fails
    pub fn else_branch(&self) -> Option<Statement> {
        if self.has_else {
            Some(Statement(self.node.branch()[2].clone()))
        } else {
            None
        }
    }
}

impl DisplayWithContext for IfStatement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(else_part) = self.else_branch() {
            write!(
                f,
                "(if-else {} {} {})",
                self.cond().with_ctx(ctx),
                self.if_branch().with_ctx(ctx),
                else_part.with_ctx(ctx)
            )
        } else {
            write!(
                f,
                "(if {} {})",
                self.cond().with_ctx(ctx),
                self.if_branch().with_ctx(ctx)
            )
        }
    }
}

impl_variant!(StatementKind, IfStatement);
impl_has_location!(IfStatement, node);

/// A statement evaluating an expression.
///
/// This might seem useless, but keep in mind that this may include function
/// calls, and those side effects may be important.
#[derive(Clone, Debug)]
pub struct ExprStatement(Rc<Node>);

impl ExprStatement {
    /// The expression making up this statement
    pub fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl DisplayWithContext for ExprStatement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        self.expr().fmt_with(ctx, f)
    }
}

impl_variant!(StatementKind, ExprStatement);
impl_has_location!(ExprStatement);

/// A definition of a new function
#[derive(Clone, Debug)]
pub struct Function(Rc<Node>);

impl Function {
    /// The name of this function, as a string
    pub fn name(&self) -> StringID {
        self.0.branch()[0].string()
    }

    /// The return type for this function
    pub fn return_type(&self) -> BuiltinType {
        let branch = self.0.branch();
        branch[branch.len() - 2].typ()
    }

    /// The body of this function
    pub fn body(&self) -> BlockStatement {
        BlockStatement(self.0.branch().last().unwrap().clone())
    }

    /// The number of parameters to this function
    pub fn param_count(&self) -> usize {
        (self.0.branch().len() - 3) / 2
    }

    /// The ith parameter to this function
    pub fn param(&self, i: usize) -> (StringID, BuiltinType) {
        let j = 2 * i + 1;
        let string = self.0.branch()[j].string();
        let typ = self.0.branch()[j + 1].typ();
        (string, typ)
    }
}

impl DisplayWithContext for Function {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(fn {}", ctx.ctx.get_string(self.name()))?;
        for i in 0..self.param_count() {
            let (s, typ) = self.param(i);
            write!(f, " (: {} {})", ctx.ctx.get_string(s), typ)?;
        }
        write!(f, " {} {})", self.return_type(), self.body().with_ctx(ctx))
    }
}

impl_has_location!(Function);

#[derive(Clone, Debug)]
pub struct AST(Rc<Node>);

impl AST {
    /// The number of functions in this tree
    pub fn function_count(&self) -> usize {
        self.0.branch().len()
    }

    /// The nth function in this tree
    pub fn function(&self, i: usize) -> Function {
        Function(self.0.branch()[i].clone())
    }
}

impl DisplayWithContext for AST {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(ast\n\n")?;
        let ctx = ctx.indented();
        for i in 0..self.function_count() {
            ctx.blank_space(f)?;
            write!(f, "{}\n\n", self.function(i).with_ctx(ctx))?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, Copy, Debug)]
enum Unexpected {
    EndOfInput,
    Token(TokenType),
}

impl DisplayWithContext for Unexpected {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        use Unexpected::*;

        match self {
            EndOfInput => write!(f, "end of input"),
            Token(token) => write!(f, "token: {}", token.with_ctx(ctx)),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum ErrorType {
    Expected(TokenType, Unexpected),
    ExpectedName(Unexpected),
    ExpectedType(Unexpected),
    ExpectedExpr(Unexpected),
    ExpectedStatement(Unexpected),
}

impl ErrorType {
    fn at(self, location: Location) -> Error {
        Error {
            location,
            error: self,
        }
    }

    fn unexpected(&self) -> Unexpected {
        use ErrorType::*;

        match self {
            Expected(_, u) => *u,
            ExpectedName(u) => *u,
            ExpectedType(u) => *u,
            ExpectedExpr(u) => *u,
            ExpectedStatement(u) => *u,
        }
    }
}

#[derive(Debug)]
pub struct Error {
    location: Location,
    error: ErrorType,
}

impl IsDiagnostic for Error {
    fn diagnostic(&self, ctx: &Context) -> Diagnostic {
        use ErrorType::*;

        let unexpected = self.error.unexpected();

        let notes = match self.error {
            Expected(tok, _) => vec![format!("expected {} instead", tok.with_ctx(ctx))],
            ExpectedName(_) => vec![format!("expected name instead")],
            ExpectedType(_) => vec![format!("expected type instead")],
            ExpectedExpr(_) => vec![
                format!("trying to parse an expression"),
                format!("expected an integer, or a name instead"),
            ],
            ExpectedStatement(_) => vec![format!("trying to parse a statement")],
        };
        Diagnostic::error()
            .with_message(format!("Unexpected {}", unexpected.with_ctx(ctx)))
            .with_labels(vec![Label::primary(self.location.file, self.location)])
            .with_notes(notes)
    }
}

pub type ParseResult<T> = Result<T, Error>;

/// Return the binding power of some token, if it's an operator.
///
/// For tokens for which this doesn't make sense, this returns None.
fn binding_power(token: TokenType) -> Option<(u8, u8, Tag)> {
    match token {
        Equals => Some((2, 1, Tag::AssignExpr)),
        PlusEqual => Some((2, 1, Tag::AssignExprAdd)),
        MinusEqual => Some((2, 1, Tag::AssignExprSub)),
        TimesEqual => Some((2, 1, Tag::AssignExprMul)),
        DivEqual => Some((2, 1, Tag::AssignExprDiv)),
        AndEqual => Some((2, 1, Tag::AssignExprBitAnd)),
        OrEqual => Some((2, 1, Tag::AssignExprBitOr)),
        OrOr => Some((3, 4, Tag::BinExprOr)),
        AndAnd => Some((5, 6, Tag::BinExprAnd)),
        Or => Some((7, 8, Tag::BinExprBitOr)),
        And => Some((9, 10, Tag::BinExprBitAnd)),
        EqualsEquals => Some((11, 12, Tag::BinExprEqual)),
        BangEquals => Some((11, 12, Tag::BinExprNotEqual)),
        Less => Some((13, 14, Tag::BinExprLess)),
        LessEqual => Some((13, 14, Tag::BinExprLessEqual)),
        Greater => Some((13, 14, Tag::BinExprGreater)),
        GreaterEqual => Some((13, 14, Tag::BinExprGreaterEqual)),
        Plus => Some((15, 16, Tag::BinExprAdd)),
        Minus => Some((15, 16, Tag::BinExprSub)),
        Times => Some((17, 18, Tag::BinExprMul)),
        Div => Some((19, 20, Tag::BinExprDiv)),
        _ => None,
    }
}

/// The binding power of some operator as a prefix unary operator
///
/// If this token isn't a prefix operaotr, this returns None
fn prefix_binding_power(token: TokenType) -> Option<((), u8, Tag)> {
    match token {
        Minus => Some(((), 22, Tag::UnaryExprNegate)),
        Bang => Some(((), 22, Tag::UnaryExprNot)),
        _ => None,
    }
}

/// Represents a parser, advancing over a series of tokens
#[derive(Debug)]
struct Parser {
    tokens: Vec<Token>,
    errors: Vec<Error>,
    file: FileID,
    file_size: usize,
    pos: usize,
}

impl Parser {
    fn new(file: FileID, file_size: usize, tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            errors: Vec::new(),
            file,
            file_size,
            pos: 0,
        }
    }

    fn end_location(&self) -> Location {
        Location::new(self.file, self.file_size, self.file_size)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn done(&self) -> bool {
        self.peek().is_none()
    }

    fn prev(&self) -> &Token {
        &self.tokens[self.pos - 1]
    }

    fn next(&mut self) -> &Token {
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        self.prev()
    }

    fn check(&self, token: TokenType) -> bool {
        self.peek().map(|x| x.token) == Some(token)
    }

    fn expect(&mut self, token: TokenType) -> ParseResult<Location> {
        match self.peek() {
            Some(right) if right.token == token => {
                let ret = right.location;
                self.next();
                Ok(ret)
            }
            Some(wrong) => {
                let loc = wrong.location;
                Err(ErrorType::Expected(token, Unexpected::Token(wrong.token)).at(loc))
            }
            None => {
                let loc = self.end_location();
                Err(ErrorType::Expected(token, Unexpected::EndOfInput).at(loc))
            }
        }
    }

    fn extract<T, F, E>(&mut self, make_error: E, matcher: F) -> ParseResult<(Location, T)>
    where
        F: Fn(TokenType) -> Option<T>,
        E: Fn(Unexpected) -> ErrorType,
    {
        match self.peek() {
            Some(maybe) => match matcher(maybe.token) {
                Some(ok) => {
                    let loc = maybe.location;
                    self.next();
                    Ok((loc, ok))
                }
                None => {
                    let loc = maybe.location;
                    Err(make_error(Unexpected::Token(maybe.token)).at(loc))
                }
            },
            None => {
                let loc = self.end_location();
                Err(make_error(Unexpected::EndOfInput).at(loc))
            }
        }
    }

    fn extract_name(&mut self) -> ParseResult<(Location, StringID)> {
        self.extract(ErrorType::ExpectedName, |tok| match tok {
            TokenType::VarName(n) => Some(n),
            _ => None,
        })
    }

    fn extract_type(&mut self) -> ParseResult<(Location, BuiltinType)> {
        self.extract(ErrorType::ExpectedType, |tok| match tok {
            TokenType::BuiltinTypeName(n) => Some(n),
            _ => None,
        })
    }

    fn function_call(&mut self, function: StringID, start: Location) -> ParseResult<Rc<Node>> {
        let mut params = vec![Rc::new(Node {
            location: start,
            tag: Tag::Name,
            shape: NodeShape::String(function),
        })];
        self.expect(OpenParens)?;

        if !self.check(CloseParens) {
            params.push(self.expr()?);

            while self.check(Comma) {
                self.next();
                params.push(self.expr()?);
            }
        }
        let end = self.expect(CloseParens)?;

        Ok(Rc::new(Node {
            location: start.to(&end),
            tag: Tag::FunctionExpr,
            shape: NodeShape::Branch(params),
        }))
    }

    fn atom(&mut self) -> ParseResult<Rc<Node>> {
        let (location, res) = self.extract(ErrorType::ExpectedExpr, |tok| match tok {
            TokenType::VarName(n) => Some(Err(n)),
            TokenType::IntLit(i) => Some(Ok(i)),
            _ => None,
        })?;
        let node = match res {
            Err(n) => {
                if self.check(OpenParens) {
                    self.function_call(n, location)?
                } else {
                    Rc::new(Node {
                        location,
                        tag: Tag::VarExpr,
                        shape: NodeShape::String(n),
                    })
                }
            }
            Ok(i) => Rc::new(Node {
                location,
                tag: Tag::IntLitExpr,
                shape: NodeShape::IntLit(i),
            }),
        };
        Ok(node)
    }

    fn bin_expr(&mut self, min_prec: u8) -> ParseResult<Rc<Node>> {
        let mut lhs = if self.check(OpenParens) {
            self.next();
            let lhs = self.bin_expr(0)?;
            self.expect(CloseParens)?;
            lhs
        } else if let Some(((), r_bp, tag)) =
            self.peek().and_then(|tok| prefix_binding_power(tok.token))
        {
            let start_loc = self.next().location;
            let rhs = self.bin_expr(r_bp)?;
            Rc::new(Node {
                location: start_loc.to(&rhs.location),
                tag,
                shape: NodeShape::Branch(vec![rhs]),
            })
        } else {
            self.atom()?
        };

        loop {
            let (l_bp, r_bp, tag) = match self.peek().and_then(|tok| binding_power(tok.token)) {
                None => break,
                Some((l, r, tag)) => (l, r, tag),
            };

            if l_bp < min_prec {
                break;
            }

            self.next();

            let rhs = self.bin_expr(r_bp)?;

            lhs = Rc::new(Node {
                location: lhs.location.to(&rhs.location),
                tag,
                shape: NodeShape::Branch(vec![lhs, rhs]),
            })
        }

        Ok(lhs)
    }

    fn expr(&mut self) -> ParseResult<Rc<Node>> {
        self.bin_expr(0)
    }

    fn expr_statement(&mut self) -> ParseResult<Rc<Node>> {
        let expr = self.expr()?;
        let end_loc = self.expect(TokenType::Semicolon)?;
        Ok(Rc::new(Node {
            location: expr.location.to(&end_loc),
            tag: Tag::ExprStatement,
            shape: NodeShape::Branch(vec![expr]),
        }))
    }

    fn var_statement(&mut self) -> ParseResult<Rc<Node>> {
        let start = self.expect(Var)?;
        let mut branch = Vec::new();
        let (name_loc, name) = self.extract_name()?;
        branch.push(Rc::new(Node {
            location: name_loc,
            tag: Tag::Name,
            shape: NodeShape::String(name),
        }));
        self.expect(Colon)?;
        let (typ_loc, typ) = self.extract_type()?;
        branch.push(Rc::new(Node {
            location: typ_loc,
            tag: Tag::Type,
            shape: NodeShape::Type(typ),
        }));
        self.expect(Equals)?;
        branch.push(self.expr()?);
        let end_loc = self.expect(Semicolon)?;
        Ok(Rc::new(Node {
            location: start.to(&end_loc),
            tag: Tag::VarStatement,
            shape: NodeShape::Branch(branch),
        }))
    }

    fn return_statement(&mut self) -> ParseResult<Rc<Node>> {
        let start = self.expect(Return)?;
        let expr = if self.check(Semicolon) {
            None
        } else {
            Some(self.expr()?)
        };
        let end = self.expect(Semicolon)?;
        let (tag, shape) = match expr {
            None => (Tag::ReturnEmptyStatement, NodeShape::Empty),
            Some(expr) => (Tag::ReturnStatement, NodeShape::Branch(vec![expr])),
        };
        Ok(Rc::new(Node {
            location: start.to(&end),
            tag,
            shape,
        }))
    }

    fn if_statement(&mut self) -> ParseResult<Rc<Node>> {
        let mut branch = Vec::new();

        let start = self.expect(If)?;

        self.expect(OpenParens)?;
        let cond = self.expr()?;
        self.expect(CloseParens)?;
        branch.push(cond);

        let statement = self.statement()?;
        let statement_loc = statement.location;
        branch.push(statement);

        if self.check(Else) {
            self.next();
            let else_part = self.statement()?;
            let location = start.to(&else_part.location);
            branch.push(else_part);
            Ok(Rc::new(Node {
                location,
                tag: Tag::IfElseStatement,
                shape: NodeShape::Branch(branch),
            }))
        } else {
            Ok(Rc::new(Node {
                location: start.to(&statement_loc),
                tag: Tag::IfStatement,
                shape: NodeShape::Branch(branch),
            }))
        }
    }

    fn statement(&mut self) -> ParseResult<Rc<Node>> {
        match self.peek() {
            Some(Token { token: Var, .. }) => self.var_statement(),
            Some(Token {
                token: OpenBrace, ..
            }) => self.block(),
            Some(Token { token: Return, .. }) => self.return_statement(),
            Some(Token { token: If, .. }) => self.if_statement(),
            Some(_) => self.expr_statement(),
            None => {
                let loc = self.end_location();
                Err(ErrorType::ExpectedStatement(Unexpected::EndOfInput).at(loc))
            }
        }
    }

    fn next_statement(&mut self) -> ParseResult<Rc<Node>> {
        loop {
            match self.statement() {
                Ok(s) => return Ok(s),
                Err(e) => loop {
                    match self.peek() {
                        None => return Err(e),
                        Some(Token {
                            token: CloseBrace, ..
                        }) => return Err(e),
                        Some(Token {
                            token: Semicolon, ..
                        }) => {
                            self.next();
                            // Don't attempt recovery if we're at the end of the block
                            if self.check(CloseBrace) {
                                return Err(e);
                            }
                            self.errors.push(e);
                            break;
                        }
                        _ => {
                            self.next();
                        }
                    }
                },
            }
        }
    }

    fn block(&mut self) -> ParseResult<Rc<Node>> {
        let start_loc = self.expect(OpenBrace)?;
        let mut statements = Vec::new();
        while !self.check(CloseBrace) {
            statements.push(self.next_statement()?);
        }
        let end_loc = self.expect(CloseBrace)?;
        let node = Node {
            location: start_loc.to(&end_loc),
            tag: Tag::BlockStatement,
            shape: NodeShape::Branch(statements),
        };
        Ok(Rc::new(node))
    }

    fn single_param(&mut self, buf: &mut Vec<Rc<Node>>) -> ParseResult<()> {
        let (name_loc, name) = self.extract_name()?;
        buf.push(Rc::new(Node {
            location: name_loc,
            tag: Tag::Name,
            shape: NodeShape::String(name),
        }));
        self.expect(Colon)?;
        let (typ_loc, typ) = self.extract_type()?;
        buf.push(Rc::new(Node {
            location: typ_loc,
            tag: Tag::Type,
            shape: NodeShape::Type(typ),
        }));
        Ok(())
    }

    fn params(&mut self, buf: &mut Vec<Rc<Node>>) -> ParseResult<()> {
        self.expect(OpenParens)?;
        if !self.check(CloseParens) {
            self.single_param(buf)?;
            while self.check(Comma) {
                self.next();
                self.single_param(buf)?;
            }
        }
        self.expect(CloseParens)?;
        Ok(())
    }

    fn function(&mut self) -> ParseResult<Rc<Node>> {
        let start_loc = self.expect(Fn)?;
        let mut branch = Vec::new();

        let (name_loc, name) = self.extract_name()?;
        branch.push(Rc::new(Node {
            location: name_loc,
            tag: Tag::Name,
            shape: NodeShape::String(name),
        }));

        self.params(&mut branch)?;

        self.expect(TokenType::Colon)?;
        let (typ_loc, typ) = self.extract_type()?;
        branch.push(Rc::new(Node {
            location: typ_loc,
            tag: Tag::Type,
            shape: NodeShape::Type(typ),
        }));

        let block = self.block()?;
        branch.push(block.clone());

        let node = Node {
            location: start_loc.to(&block.location),
            tag: Tag::Function,
            shape: NodeShape::Branch(branch),
        };
        Ok(Rc::new(node))
    }

    fn ast(&mut self) -> AST {
        let mut functions = Vec::new();
        let mut start = None;
        let mut end = 0;
        while self.check(Fn) {
            let function = match self.function() {
                Ok(f) => f,
                Err(e) => {
                    self.errors.push(e);
                    while !self.check(Fn) && !self.done() {
                        self.next();
                    }
                    continue;
                }
            };
            let location = &function.location;
            if let None = start {
                start = Some(location.start);
            }
            end = location.end;

            functions.push(function);
        }
        let location = Location::new(self.file, start.unwrap_or(end), end);
        let node = Node {
            location,
            tag: Tag::AST,
            shape: NodeShape::Branch(functions),
        };
        AST(Rc::new(node))
    }
}

pub fn parse(tokens: Vec<Token>, file: FileID, file_size: usize) -> Result<AST, Vec<Error>> {
    let mut parser = Parser::new(file, file_size, tokens);
    let ast = parser.ast();
    if parser.errors.is_empty() {
        Ok(ast)
    } else {
        Err(parser.errors)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::context::Context;
    use crate::lexer::lex;

    fn should_parse(input: &str) {
        let mut ctx = Context::empty();

        let mut tokens = Vec::new();
        for res in lex(input, &mut ctx) {
            match res {
                Err(e) => assert!(false, "failed to lex {:?}", e),
                Ok(t) => tokens.push(t),
            }
        }

        if let Err(e) = parse(tokens, FileID::dummy(), input.len()) {
            assert!(false, "failed ot parse {:?}", e)
        }
    }

    #[test]
    fn empty_functions_parse() {
        should_parse(
            r#"
        fn foo(): Unit {}

        fn bar(x: I32): I32 {}

        fn baz(x: I32, y: I32): Unit {}

        fn boo(x: Bool): Bool {}
        "#,
        )
    }

    #[test]
    fn statements_parse() {
        should_parse(
            r#"
        fn foo(): Unit {
            var x: I32 = 3;
            {
                var y: I32 = 4;
                4;
            }
        }
        "#,
        )
    }

    #[test]
    fn if_else_parses() {
        should_parse(
            r#"
        fn foo(): Unit {
            if (1) {
                0;
            } else {
                0;
            }

            if (1) {
                0;
            }
        }
        "#,
        )
    }

    #[test]
    fn operators_parse() {
        should_parse(
            r#"
        fn foo(): Unit {
            2 + 3 * (3 + 4 / 5) - 5;
        }
        "#,
        );
    }

    #[test]
    fn calls_parse() {
        should_parse(
            r#"
        fn foo(): Unit {
            foo(1, 2);
            bar(x, y, z);
            bar();
        }
        "#,
        );
    }

    #[test]
    fn boolean_operators_parse() {
        should_parse(
            r#"
        fn foo(): Bool {
            1 != 2 & 3 && 4 || 5 > 6 < 7 <= 8 >= 9 == 10;
            !3;
            -4;
        }
        "#,
        );
    }

    #[test]
    fn empty_return_should_parse() {
        should_parse(
            r#"
        fn foo(): Unit {
            return;
        }
        "#,
        )
    }

    #[test]
    fn assignments_should_parse() {
        should_parse(
            r#"
        fn foo(): Unit {
            var x: I32 = 3;
            x += x += x *= x /= x -= x |= x;
            x -= x;
            x /= x;
            x |= x;
            x &= x;
        }
        "#,
        )
    }
}
