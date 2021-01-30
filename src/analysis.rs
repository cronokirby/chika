use crate::parser;
use crate::{context::StringID, types::BuiltinType};
use parser::{BinOp, UnaryOp};
use std::collections::HashMap;
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
    /// Information about the functions in our program
    pub function_table: FunctionTable,
    /// Information about the variables in our program
    pub variable_table: VariableTable,
}

/// A list of nested scopes, allowing us to track variable IDs
///
/// The idea is that we're going to keep track of which names map to which
/// variables in the current scope.
///
/// Since we have a nested system of scopes, we can correctly handle temporary shadowing,
/// where a variable in a scope shadows a variable in an outer scope.
#[derive(Debug)]
struct Scopes {
    scopes: Vec<HashMap<StringID, VariableID>>,
}

impl Scopes {
    fn new() -> Self {
        Scopes { scopes: Vec::new() }
    }

    /// Enter a new scope, allowing us to temporarily shadow variables
    fn enter(&mut self) {
        self.scopes.push(HashMap::new())
    }

    /// Exit the current scope
    fn exit(&mut self) {
        self.scopes.pop();
    }

    /// Get the variable ID we've assigned to some name.
    ///
    /// This will look through all of the scopes to find that value.
    fn get(&self, string: StringID) -> Option<VariableID> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(&string) {
                return Some(*v);
            }
        }
        None
    }

    /// Assign an ID to some name in the current scope
    fn put(&mut self, string: StringID, var: VariableID) {
        let last = self.scopes.last_mut().expect("No active scope");
        last.insert(string, var);
    }
}

/// Represents an error that can occurr when analyzing the parsed AST
pub enum AnalysisError {
    FunctionRedefinition(StringID),
}

/// A result type containing an error from analysis
pub type AnalysisResult<T> = Result<T, AnalysisError>;

struct Analyzer {
    function_ids: HashMap<StringID, FunctionID>,
    function_table: FunctionTable,
    variable_table: VariableTable,
    scopes: Scopes,
}

impl Analyzer {
    fn new() -> Self {
        Analyzer {
            function_ids: HashMap::new(),
            function_table: FunctionTable::new(),
            variable_table: VariableTable::new(),
            scopes: Scopes::new(),
        }
    }

    fn function(&mut self, function: parser::Function) -> AnalysisResult<FunctionDef> {
        let name = function.name();
        if self.function_ids.contains_key(&name) {
            return Err(AnalysisError::FunctionRedefinition(name));
        }
        self.scopes.enter();
        let mut arg_types = Vec::new();
        // This scheme allows parameters to shadow preceding ones.
        // The rationale is that this is similar to var statements inside a function
        for i in 0..function.param_count() {
            let (name, typ) = function.param(i);
            let var = Variable::new(name, typ);
            let var_id = self.variable_table.add_variable(var);
            self.scopes.put(name, var_id);
            arg_types.push(typ);
        }
        let ret_type = function.return_type();
        let id = self
            .function_table
            .add_function(Function::new(name, ret_type, arg_types));
        self.function_ids.insert(name, id);
        self.scopes.exit();
        Ok(FunctionDef {
            id,
            body: unimplemented!(),
        })
    }

    fn run(mut self, ast: &parser::AST) -> AnalysisResult<AST> {
        let mut functions = Vec::new();
        for i in 0..ast.function_count() {
            let function = ast.function(i);
            functions.push(self.function(function)?);
        }
        Ok(AST {
            functions,
            function_table: self.function_table,
            variable_table: self.variable_table,
        })
    }
}

pub fn analyze(ast: &parser::AST) -> AnalysisResult<AST> {
    Analyzer::new().run(ast)
}
