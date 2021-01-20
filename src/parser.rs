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
    types::BuiltinType,
};
use std::fmt;
use TokenType::*;

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
    ExprStatement,
    ReturnStatement,
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

impl DisplayWithContext for ExprKind {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExprKind::IntLitExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::VarExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
            ExprKind::BinExpr(e) => write!(f, "{}", e.with_ctx(ctx)),
        }
    }
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

impl DisplayWithContext for Expr {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind().fmt_with(ctx, f)
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

impl DisplayWithContext for IntLitExpr {
    fn fmt_with(&self, _ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.int_lit())
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

impl DisplayWithContext for VarExpr {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", ctx.ctx.get_string(self.var()))
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

impl DisplayWithContext for BinOp {
    fn fmt_with(&self, _ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Div => write!(f, "/"),
        }
    }
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

impl DisplayWithContext for BinExpr {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({} {} {})",
            self.op.with_ctx(ctx),
            self.lhs().with_ctx(ctx),
            self.rhs().with_ctx(ctx)
        )
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

pub struct Statement(Rc<Node>);

impl Statement {
    fn kind(&self) -> StatementKind {
        match &self.0.tag {
            Tag::ReturnStatement => ReturnStatement(self.0.clone()).into(),
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
pub struct ReturnStatement(Rc<Node>);

impl ReturnStatement {
    /// The underlying expression being returned
    pub fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl DisplayWithContext for ReturnStatement {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(return {})", self.expr().with_ctx(ctx))
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
    fn body(&self) -> BlockStatement {
        BlockStatement(self.0.branch().last().unwrap().clone())
    }

    /// The number of parameters to this function
    fn param_count(&self) -> usize {
        (self.0.branch().len() - 3) / 2
    }

    /// The ith parameter to this function
    fn param(&self, i: usize) -> (StringID, BuiltinType) {
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

#[derive(Debug)]
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
            Expected(tok, _) => vec![format!("expected {} instead", tok.with_ctx(ctx.into()))],
            ExpectedName(_) => vec![format!("expected name instead")],
            ExpectedType(_) => vec![format!("expected type instead")],
            ExpectedExpr(_) => vec![
                format!("trying to parse an expression"),
                format!("expected an integer, or a name instead"),
            ],
            ExpectedStatement(_) => vec![format!("trying to parse a statement")],
        };
        Diagnostic::error()
            .with_message(format!("Unexpected {}", unexpected.with_ctx(ctx.into())))
            .with_labels(vec![Label::primary(self.location.file, self.location)])
            .with_notes(notes)
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

    fn end_location(&self) -> Location {
        Location::new(self.file, self.file_size, self.file_size)
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

    fn expr(&mut self) -> ParseResult<Rc<Node>> {
        match self.peek() {
            Some(Token {
                token: IntLit(u),
                location,
            }) => {
                let ret = Rc::new(Node {
                    location: *location,
                    tag: Tag::IntLitExpr,
                    shape: NodeShape::IntLit(*u),
                });
                self.next();
                Ok(ret)
            }
            Some(Token {
                token: VarName(s),
                location,
            }) => {
                let ret = Rc::new(Node {
                    location: *location,
                    tag: Tag::VarExpr,
                    shape: NodeShape::String(*s),
                });
                self.next();
                Ok(ret)
            }
            Some(other) => {
                Err(ErrorType::ExpectedExpr(Unexpected::Token(other.token)).at(other.location))
            }
            None => {
                let loc = self.end_location();
                Err(ErrorType::ExpectedExpr(Unexpected::EndOfInput).at(loc))
            }
        }
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
        let expr = self.expr()?;
        let end = self.expect(Semicolon)?;
        Ok(Rc::new(Node {
            location: start.to(&end),
            tag: Tag::ReturnStatement,
            shape: NodeShape::Branch(vec![expr]),
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

    fn block(&mut self) -> ParseResult<Rc<Node>> {
        let start_loc = self.expect(OpenBrace)?;
        let mut statements = Vec::new();
        while !self.check(CloseBrace) {
            statements.push(self.statement()?);
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

    fn ast(&mut self) -> ParseResult<AST> {
        let mut functions = Vec::new();
        let mut start = None;
        let mut end = 0;
        while self.check(Fn) {
            let function = self.function()?;
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
        Ok(AST(Rc::new(node)))
    }
}

pub fn parse(tokens: Vec<Token>, file: FileID, file_size: usize) -> ParseResult<AST> {
    let mut parser = Parser::new(file, file_size, tokens);
    parser.ast()
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
}
