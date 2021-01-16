use std::rc::Rc;

use crate::{
    context::{Location, StringID},
    types::BuiltinType,
};

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

trait HasLocation {
    fn location(&self) -> &Location;
}

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

macro_rules! impl_variant {
    ($typ:ident, $variant:ident) => {
        impl Into<$typ> for $variant {
            fn into(self) -> $typ {
                $typ::$variant(self)
            }
        }
    };
}

#[derive(Debug)]
pub enum ExprKind {
    IntLitExpr(IntLitExpr),
    VarExpr(VarExpr),
    BinExpr(BinExpr),
}

#[derive(Debug)]
pub struct Expr(Rc<Node>);

impl Expr {
    fn kind(&self) -> ExprKind {
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

#[derive(Debug)]
pub struct IntLitExpr(Rc<Node>);

impl IntLitExpr {
    pub fn int_lit(&self) -> u32 {
        self.0.int_lit()
    }
}

impl_variant!(ExprKind, IntLitExpr);
impl_has_location!(IntLitExpr);

#[derive(Debug)]
pub struct VarExpr(Rc<Node>);

impl VarExpr {
    pub fn var(&self) -> StringID {
        self.0.string()
    }
}

impl_variant!(ExprKind, VarExpr);
impl_has_location!(VarExpr);

#[derive(Clone, Copy, Debug)]
pub enum BinOp {
    Add,
    Mul,
    Sub,
    Div,
}

#[derive(Debug)]
pub struct BinExpr {
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

    fn lhs(&self) -> Expr {
        Expr(self.node.branch()[0].clone())
    }

    fn rhs(&self) -> Expr {
        Expr(self.node.branch()[1].clone())
    }
}

impl_variant!(ExprKind, BinExpr);
impl_has_location!(BinExpr, node);

enum StatementKind {
    ReturnStatement(ReturnStatement),
    VarStatement(VarStatement),
    BlockStatement(BlockStatement),
    IfStatement(IfStatement),
    ExprStatement(ExprStatement),
}

struct Statement(Rc<Node>);

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

struct ReturnStatement(Rc<Node>);

impl ReturnStatement {
    fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl_variant!(StatementKind, ReturnStatement);
impl_has_location!(ReturnStatement);

struct VarStatement(Rc<Node>);

impl VarStatement {
    fn var(&self) -> StringID {
        self.0.branch()[0].string()
    }

    fn typ(&self) -> BuiltinType {
        self.0.branch()[1].typ()
    }

    fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl_variant!(StatementKind, VarStatement);
impl_has_location!(VarStatement);

struct BlockStatement(Rc<Node>);

impl BlockStatement {
    fn len(&self) -> usize {
        self.0.branch().len()
    }

    fn statement(&self, i: usize) -> Statement {
        Statement(self.0.branch()[i].clone())
    }
}

impl_variant!(StatementKind, BlockStatement);
impl_has_location!(BlockStatement);

struct IfStatement {
    has_else: bool,
    node: Rc<Node>,
}

impl IfStatement {
    fn new(has_else: bool, node: Rc<Node>) -> Self {
        IfStatement { has_else, node }
    }

    fn cond(&self) -> Expr {
        Expr(self.node.branch()[0].clone())
    }

    fn if_branch(&self) -> Statement {
        Statement(self.node.branch()[1].clone())
    }

    fn else_branch(&self) -> Option<Statement> {
        if self.has_else {
            Some(Statement(self.node.branch()[2].clone()))
        } else {
            None
        }
    }
}

impl_variant!(StatementKind, IfStatement);
impl_has_location!(IfStatement, node);

struct ExprStatement(Rc<Node>);

impl ExprStatement {
    fn expr(&self) -> Expr {
        Expr(self.0.branch()[0].clone())
    }
}

impl_variant!(StatementKind, ExprStatement);
impl_has_location!(ExprStatement);

struct Function(Rc<Node>);

impl Function {
    fn name(&self) -> StringID {
        self.0.branch()[0].string()
    }

    fn return_type(&self) -> BuiltinType {
        self.0.branch()[1].typ()
    }

    fn body(&self) -> BlockStatement {
        BlockStatement(self.0.branch()[2].clone())
    }

    fn param_count(&self) -> usize {
        (self.0.branch().len() - 3) / 2
    }

    fn param(&self, i: usize) -> (StringID, BuiltinType) {
        let j = i - 3;
        let string = self.0.branch()[j].string();
        let typ = self.0.branch()[j + 1].typ();
        (string, typ)
    }
}

impl_has_location!(Function);
