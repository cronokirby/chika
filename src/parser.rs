use crate::codespan_reporting::diagnostic::{Diagnostic, Label};
use std::{ops::Range, rc::Rc};

use crate::{
    context::{Context, DisplayWithContext, FileID, Location, Printable, Printer, StringID},
    errors,
    lexer::Token,
    lexer::TokenType,
    types::BuiltinType,
};
use std::fmt;

/// This is used to differentiatate different kinds of raw nodes.
///
/// When creating a raw node, we always attach the correct tag.
#[derive(Debug)]
#[repr(u8)]
enum Tag {
    IntLitExpr,
    BinExprAdd,
    BinExprMul,
    BinExprSub,
    BinExprDiv,
    VarExpr,
    Expr,
    ReturnStatement,
    VarStatement,
    IfStatement,
    IfElseStatement,
    ExprStatement,
    BlockStatement,
    Statement,
    Function,
    FunctionName,
}

/// Represents the kind of shape that a node can have.
///
/// We need this, because everything we have is stored in this unified
/// node type, and we need to handle terminal things like strings and literals.
#[derive(Debug)]
enum NodeShape {
    /// This node is a terminal reference to a string
    String(StringID),
    /// This node is a terminal reference to an integer
    IntLit(u32),
    /// This node is a termainl reference to a builtin type
    Type(BuiltinType),
    /// This node branches off to contain other nodes
    Branch(Vec<Rc<Node>>),
}

/// Represents a single raw Node in our AST.
///
/// Our overall AST structure is based on representing things
/// with our plain untyped representation, and then using a typed outer layer
/// for actually manipulating things.
#[derive(Debug)]
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
#[derive(Debug)]
pub enum ExprKind {
    /// An single int as an expression
    IntLitExpr(IntLitExpr),
    /// A single variable as an expression
    VarExpr(VarExpr),
    /// Binary arithmetic, as an expression
    BinExpr(BinExpr),
}

/// Represents a generic kind of expression
#[derive(Debug)]
pub struct Expr(Rc<Node>);

impl Expr {
    /// Get a strongly typed variant from this expression
    pub fn kind(&self) -> ExprKind {
        match &self.0.tag {
            Tag::VarExpr => VarExpr(self.0.clone()).into(),
            Tag::IntLitExpr => IntLitExpr(self.0.clone()).into(),
            Tag::BinExprAdd => BinExpr::add(self.0.clone()).into(),
            Tag::BinExprSub => BinExpr::sub(self.0.clone()).into(),
            Tag::BinExprMul => BinExpr::mul(self.0.clone()).into(),
            Tag::BinExprDiv => BinExpr::div(self.0.clone()).into(),
            other => panic!("unexpected tag {:?}", other),
        }
    }
}

impl_has_location!(Expr);

/// An integer literal, used as an expression
#[derive(Debug)]
pub struct IntLitExpr(Rc<Node>);

impl IntLitExpr {
    /// The underlying integer composing this expression
    pub fn int_lit(&self) -> u32 {
        self.0.int_lit()
    }
}

impl_variant!(ExprKind, IntLitExpr);
impl_has_location!(IntLitExpr);

/// A reference to a variable, used as an expression
#[derive(Debug)]
pub struct VarExpr(Rc<Node>);

impl VarExpr {
    /// The string that composes this variable name
    pub fn var(&self) -> StringID {
        self.0.string()
    }
}

impl_variant!(ExprKind, VarExpr);
impl_has_location!(VarExpr);

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
}

/// An expression applying a binary operator to two expressions
#[derive(Debug)]
pub struct BinExpr {
    /// The operator being used
    pub op: BinOp,
    node: Rc<Node>,
}

impl BinExpr {
    fn add(node: Rc<Node>) -> Self {
        BinExpr {
            op: BinOp::Add,
            node,
        }
    }

    fn sub(node: Rc<Node>) -> Self {
        BinExpr {
            op: BinOp::Sub,
            node,
        }
    }

    fn mul(node: Rc<Node>) -> Self {
        BinExpr {
            op: BinOp::Mul,
            node,
        }
    }

    fn div(node: Rc<Node>) -> Self {
        BinExpr {
            op: BinOp::Div,
            node,
        }
    }

    /// The left expression for this operator
    pub fn lhs(&self) -> Expr {
        Expr(self.node.branch()[0].clone())
    }

    /// The right expression for this operator
    pub fn rhs(&self) -> Expr {
        Expr(self.node.branch()[1].clone())
    }
}

impl_variant!(ExprKind, BinExpr);
impl_has_location!(BinExpr, node);

/// Represents a strongly typed kind of statement
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

pub struct Statement(Rc<Node>);

impl Statement {
    fn kind(&self) -> StatementKind {
        match &self.0.tag {
            Tag::ReturnStatement => ReturnStatement(self.0.clone()).into(),
            Tag::VarStatement => VarStatement(self.0.clone()).into(),
            Tag::BlockStatement => BlockStatement(self.0.clone()).into(),
            Tag::IfStatement => IfStatement::new(false, self.0.clone()).into(),
            Tag::IfElseStatement => IfStatement::new(false, self.0.clone()).into(),
            Tag::ExprStatement => ExprStatement(self.0.clone()).into(),
            other => panic!("unexpected tag {:?}", other),
        }
    }
}

impl_has_location!(Statement);

/// A statement returning the value of some expression
pub struct ReturnStatement(Rc<Node>);

impl ReturnStatement {
    /// The underlying expression being returned
    pub fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl_variant!(StatementKind, ReturnStatement);
impl_has_location!(ReturnStatement);

/// A statement defining a new variable
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
        Expr(self.0.branch()[0].clone())
    }
}

impl_variant!(StatementKind, VarStatement);
impl_has_location!(VarStatement);

/// A block statement is composed of multiple statements together
pub struct BlockStatement(Rc<Node>);

impl BlockStatement {
    /// The number of statements in this block
    pub fn len(&self) -> usize {
        self.0.branch().len()
    }

    /// The ith statement in this block
    fn statement(&self, i: usize) -> Statement {
        Statement(self.0.branch()[i].clone())
    }
}

impl_variant!(StatementKind, BlockStatement);
impl_has_location!(BlockStatement);

/// Represents a conditional statement.
///
/// We might have an optional else branch as well.
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

impl_variant!(StatementKind, IfStatement);
impl_has_location!(IfStatement, node);

/// A statement evaluating an expression.
///
/// This might seem useless, but keep in mind that this may include function
/// calls, and those side effects may be important.
pub struct ExprStatement(Rc<Node>);

impl ExprStatement {
    /// The expression making up this statement
    pub fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl_variant!(StatementKind, ExprStatement);
impl_has_location!(ExprStatement);

/// A definition of a new function
pub struct Function(Rc<Node>);

impl Function {
    /// The name of this function, as a string
    pub fn name(&self) -> StringID {
        self.0.branch()[0].string()
    }

    /// The return type for this function
    pub fn return_type(&self) -> BuiltinType {
        self.0.branch()[1].typ()
    }

    /// The body of this function
    fn body(&self) -> BlockStatement {
        BlockStatement(self.0.branch()[2].clone())
    }

    /// The number of parameters to this function
    fn param_count(&self) -> usize {
        (self.0.branch().len() - 3) / 2
    }

    /// The ith parameter to this function
    fn param(&self, i: usize) -> (StringID, BuiltinType) {
        let j = i - 3;
        let string = self.0.branch()[j].string();
        let typ = self.0.branch()[j + 1].typ();
        (string, typ)
    }
}

impl_has_location!(Function);

#[derive(Debug)]
pub struct AST(Rc<Node>);

impl AST {
    pub fn name(&self) -> StringID {
        self.0.string()
    }
}

#[derive(Clone, Copy, Debug)]
enum Unexpected {
    EndOfInput,
    Token(TokenType),
}

impl DisplayWithContext for Unexpected {
    fn fmt_with(&self, ctx: &Context, f: &mut fmt::Formatter) -> fmt::Result {
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
    ExpectedIntLit(Unexpected),
    ExpectedType(Unexpected),
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
            ExpectedIntLit(u) => *u,
            ExpectedType(u) => *u,
        }
    }
}

#[derive(Debug)]
pub struct Error {
    location: Location,
    error: ErrorType,
}

impl Printable for Error {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> errors::Result<()> {
        use ErrorType::*;

        let unexpected = self.error.unexpected();

        let note = match self.error {
            Expected(tok, _) => format!("expected {} instead", tok.with_ctx(printer.ctx)),
            ExpectedName(_) => format!("expected name instead"),
            ExpectedIntLit(_) => format!("expected integer instead"),
            ExpectedType(_) => format!("expected type instead"),
        };
        let diagnostic = Diagnostic::error()
            .with_message(format!("Unexpected {}", unexpected.with_ctx(printer.ctx)))
            .with_labels(vec![Label::primary(
                self.location.file,
                self.location.range.clone(),
            )])
            .with_notes(vec![note]);
        printer.write_diagnostic(diagnostic)
    }
}

pub type ParseResult<T> = Result<T, Error>;

/// Represents a parser, advancing over a series of tokens
#[derive(Debug)]
struct Parser {
    tokens: Vec<Token>,
    file: FileID,
    file_size: usize,
    pos: usize,
}

impl Parser {
    fn new(file: FileID, file_size: usize, tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            file,
            file_size,
            pos: 0,
        }
    }

    fn location(&self, range: Range<usize>) -> Location {
        Location::new(self.file, range)
    }

    fn end_location(&self) -> Location {
        self.location(self.file_size..self.file_size)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
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

    fn expect(&mut self, token: TokenType) -> ParseResult<()> {
        match self.peek() {
            Some(right) if right.token == token => {
                self.next();
                Ok(())
            }
            Some(wrong) => {
                let loc = self.location(wrong.range.clone());
                Err(ErrorType::Expected(wrong.token, Unexpected::Token(token)).at(loc))
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
                    let loc = self.location(maybe.range.clone());
                    Ok((loc, ok))
                }
                None => {
                    let loc = self.location(maybe.range.clone());
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

    fn ast(&mut self) -> ParseResult<AST> {
        let (loc, s) = self.extract_name()?;
        let node = Node {
            location: loc,
            tag: Tag::FunctionName,
            shape: NodeShape::String(s),
        };
        Ok(AST(Rc::new(node)))
    }
}

pub fn parse(tokens: Vec<Token>, file: FileID, file_size: usize) -> ParseResult<AST> {
    let mut parser = Parser::new(file, file_size, tokens);
    parser.ast()
}
