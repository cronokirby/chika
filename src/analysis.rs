use crate::parser;
use crate::{context::StringID, types::BuiltinType};
use parser::{BinOp, UnaryOp};
use std::ops::Index;

/// Represents the information we have about some function
#[derive(Clone, Debug)]
pub struct Function {
    /// The original name of this function
    pub name: StringID,
    /// The return type of this function
    pub return_type: BuiltinType,
    /// The types of the arguments, if any.
    ///
    /// This also serves as a way of storing the number of arguments, as well
    pub arg_types: Vec<BuiltinType>,
}

impl Function {
    fn new(name: StringID, return_type: BuiltinType, arg_types: Vec<BuiltinType>) -> Self {
        Function {
            name,
            return_type,
            arg_types,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FunctionID(u32);

#[derive(Debug)]
pub struct FunctionTable {
    functions: Vec<Function>,
}

impl FunctionTable {
    fn new() -> Self {
        FunctionTable {
            functions: Vec::new(),
        }
    }

    fn add_function(&mut self, function: Function) -> FunctionID {
        let id = FunctionID(self.functions.len() as u32);
        self.functions.push(function);
        id
    }
}

impl Index<FunctionID> for FunctionTable {
    type Output = Function;

    fn index(&self, index: FunctionID) -> &Self::Output {
        &self.functions[index.0 as usize]
    }
}

/// The information we have about a variable in the program
#[derive(Clone, Debug)]
pub struct Variable {
    /// The original name the variable had
    pub name: StringID,
    /// The type of this variable
    pub typ: BuiltinType,
}

impl Variable {
    fn new(name: StringID, typ: BuiltinType) -> Self {
        Variable { name, typ }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct VariableID(u32);

#[derive(Debug)]
pub struct VariableTable {
    variables: Vec<Variable>,
}

impl VariableTable {
    fn new() -> Self {
        VariableTable {
            variables: Vec::new(),
        }
    }

    fn add_variable(&mut self, variable: Variable) -> VariableID {
        let id = VariableID(self.variables.len() as u32);
        self.variables.push(variable);
        id
    }
}

impl Index<VariableID> for VariableTable {
    type Output = Variable;

    fn index(&self, index: VariableID) -> &Self::Output {
        &self.variables[index.0 as usize]
    }
}

/// Represents a kind of expression in our language
#[derive(Debug)]
pub enum Expr {
    /// Calling a function, with a list of arguments
    FunctionCall(FunctionID, Vec<Expr>),
    /// Applying some binary operator to two expressions
    BinExpr(BinOp, Box<Expr>, Box<Expr>),
    /// Applying some unary operator to some expression
    UnaryExpr(UnaryOp, Box<Expr>),
    /// Referencing a variable, to form an expression
    VarExpr(VariableID),
    /// An integer literal as an expression
    IntExpr(u32),
}

/// Represents a kind of statement in our language
#[derive(Debug)]
pub enum Statement {
    /// A sequence of statements, forming a block
    Block(Vec<Statement>),
    /// An expression, using as a statement
    Expr(Expr),
    /// Return the value of an expression
    Return(Expr),
    /// An if statement, with a possible else branch
    If(Expr, Box<Statement>, Option<Box<Statement>>),
    /// Define a new variable, with a given expression as its value
    Var(VariableID, Expr),
}

/// A function definition in our AST
#[derive(Debug)]
pub struct FunctionDef {
    /// The identifier for this function
    pub id: FunctionID,
    /// The body of this function
    pub body: Statement,
}

/// Our syntax tree, which is composed of a sequence of function definitions
#[derive(Debug)]
pub struct AST {
    /// The functions defined in our AST
    pub functions: Vec<FunctionDef>,
}
