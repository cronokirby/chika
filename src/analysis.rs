use crate::{
    context::{Context, Diagnostic, IsDiagnostic, Location},
    parser,
};
use crate::{
    context::{DisplayContext, DisplayWithContext, StringID},
    types::BuiltinType,
};
use codespan_reporting::diagnostic::Label;
use core::fmt;
use parser::{BinOp, ExprKind, HasLocation, StatementKind, UnaryOp};
use std::collections::HashMap;
use std::ops::Index;
use BuiltinType::*;

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

impl DisplayWithContext for Function {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "fn {}(", ctx.ctx.get_string(self.name))?;
        let mut first = true;
        for arg in &self.arg_types {
            if first {
                first = false;
                write!(f, "{}", arg)?;
            } else {
                write!(f, ", {}", arg)?;
            }
        }
        write!(f, "): {}", self.return_type)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FunctionID(u32);

impl fmt::Display for FunctionID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "f{}", self.0)
    }
}

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

impl DisplayWithContext for FunctionTable {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, function) in self.functions.iter().enumerate() {
            let id = FunctionID(i as u32);
            writeln!(f, "{}: {}", id, function.with_ctx(ctx))?;
        }
        Ok(())
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

impl DisplayWithContext for Variable {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", ctx.ctx.get_string(self.name), self.typ)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct VariableID(u32);

impl fmt::Display for VariableID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

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

impl DisplayWithContext for VariableTable {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, variable) in self.variables.iter().enumerate() {
            let id = VariableID(i as u32);
            writeln!(f, "{}: {}", id, variable.with_ctx(ctx))?;
        }
        Ok(())
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

impl fmt::Display for Expr {
    fn fmt<'a>(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::IntExpr(i) => write!(f, "{}", i),
            Expr::BinExpr(op, l, r) => {
                write!(f, "({} {} {})", op, l, r)
            }
            Expr::UnaryExpr(op, e) => write!(f, "({} {})", op, e),
            Expr::VarExpr(v) => write!(f, "{}", v),
            Expr::FunctionCall(func, params) => {
                write!(f, "({}", func)?;
                for p in params {
                    write!(f, " {}", p)?;
                }
                write!(f, ")")
            }
        }
    }
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

impl DisplayWithContext for Statement {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::Expr(e) => write!(f, "{}", e),
            Statement::Return(e) => write!(f, "return {}", e),
            Statement::Var(v, e) => write!(f, "var {} = {}", v, e),
            Statement::If(cond, if_branch, else_branch) => match else_branch {
                None => write!(f, "(if {} {})", cond, if_branch.with_ctx(ctx)),
                Some(branch) => write!(
                    f,
                    "(if {} {} {})",
                    cond,
                    if_branch.with_ctx(ctx),
                    branch.with_ctx(ctx)
                ),
            },
            Statement::Block(statements) => {
                write!(f, "{{\n")?;
                let new_ctx = ctx.indented();
                for s in statements {
                    new_ctx.blank_space(f)?;
                    write!(f, "{};\n", s.with_ctx(new_ctx))?;
                }
                ctx.blank_space(f)?;
                write!(f, "}}\n")?;
                ctx.blank_space(f)
            }
        }
    }
}

/// A function definition in our AST
#[derive(Debug)]
pub struct FunctionDef {
    /// The identifier for this function
    pub id: FunctionID,
    /// The arguments passed to this function
    pub args: Vec<VariableID>,
    /// The body of this function
    pub body: Statement,
}

impl DisplayWithContext for FunctionDef {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "fn {}(", self.id)?;
        let mut first = true;
        for arg in &self.args {
            if first {
                first = false;
                write!(f, "{}", arg)?;
            } else {
                write!(f, ", {}", arg)?;
            }
        }
        write!(f, ") {}", self.body.with_ctx(ctx))
    }
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

impl DisplayWithContext for AST {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        for func in &self.functions {
            writeln!(f, "{}", func.with_ctx(ctx))?;
        }
        writeln!(f, "Functions:\n{}", self.function_table.with_ctx(ctx))?;
        writeln!(f, "Variables:\n{}", self.variable_table.with_ctx(ctx))
    }
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

/// Represents a kind of constraint we generate when checking types
enum ConstraintType {
    /// A function must have a certain return type
    ReturnType(FunctionID, BuiltinType),
    /// A function must be able to never return a value
    NoReturn(FunctionID),
    /// We've detected that two types must match up
    SameType(BuiltinType, BuiltinType),
}

impl ConstraintType {
    fn at(self, location: Location) -> Constraint {
        Constraint {
            location,
            constraint: self,
        }
    }
}

/// A constraint annotated with a location.
///
/// The location is to be able to present better error messages.
struct Constraint {
    location: Location,
    constraint: ConstraintType,
}

/// Represents an error that can occurr when analyzing the parsed AST
enum ErrorType {
    FunctionRedefinition(StringID),
    UndefinedVar(StringID),
    UndefinedFunction(StringID),
    TypeMismatch(BuiltinType, BuiltinType),
    NoReturnInFunction(StringID, BuiltinType),
    BadReturnType(StringID, BuiltinType, BuiltinType),
}

impl ErrorType {
    fn at(self, location: Location) -> Error {
        Error {
            location,
            error: self,
        }
    }
}

pub struct Error {
    location: Location,
    error: ErrorType,
}

impl IsDiagnostic for Error {
    fn diagnostic(&self, ctx: &Context) -> Diagnostic {
        use ErrorType::*;

        match self.error {
            FunctionRedefinition(name) => Diagnostic::error()
                .with_message(format!(
                    "Redefinition of function `{}`",
                    ctx.get_string(name)
                ))
                .with_labels(vec![Label::primary(self.location.file, self.location)]),
            UndefinedVar(name) => Diagnostic::error()
                .with_message(format!("Undefined variable `{}`", ctx.get_string(name)))
                .with_labels(vec![Label::primary(self.location.file, self.location)]),
            UndefinedFunction(name) => Diagnostic::error()
                .with_message(format!("Undefined function `{}`", ctx.get_string(name)))
                .with_labels(vec![Label::primary(self.location.file, self.location)]),
            TypeMismatch(expected, actual) => Diagnostic::error()
                .with_message("Type mismatch")
                .with_labels(vec![Label::primary(self.location.file, self.location)
                    .with_message(format!(
                        "this has type `{}` instead of `{}`",
                        actual, expected
                    ))])
                .with_notes(vec![format!(
                    "found `{}` instead of `{}`",
                    actual, expected
                )]),
            NoReturnInFunction(name, typ) => Diagnostic::error()
                .with_message("Control reached end of function")
                .with_labels(vec![Label::primary(self.location.file, self.location)
                    .with_message("control ends here")])
                .with_notes(vec![
                    format!("Inside of function `{}`", ctx.get_string(name)),
                    format!("This function returns type `{}`, and not `Unit`", typ),
                ]),
            BadReturnType(name, expected, actual) => Diagnostic::error()
                .with_message("Incorrect return value")
                .with_labels(vec![Label::primary(self.location.file, self.location)
                    .with_message(format!(
                        "this has type `{}` instead of `{}`",
                        actual, expected
                    ))])
                .with_notes(vec![
                    format!("inside function `{}`", ctx.get_string(name)),
                    format!("this function should return type `{}`", expected),
                ]),
        }
    }
}

/// A result type containing an error from analysis
type AnalysisResult<T> = Result<T, Error>;

fn function_doesnt_return(function: parser::Function) -> Option<Location> {
    fn block_statement_returns(block: parser::BlockStatement) -> bool {
        for i in 0..block.len() {
            if returns(block.statement(i)) {
                return true;
            }
        }
        false
    }

    /// True if control flow always exits after running this statement
    fn returns(statement: parser::Statement) -> bool {
        match statement.kind() {
            StatementKind::ReturnStatement(_) => true,
            StatementKind::IfStatement(statement) => {
                returns(statement.if_branch()) && statement.else_branch().map_or(false, returns)
            }
            StatementKind::BlockStatement(statement) => block_statement_returns(statement),
            _ => false,
        }
    }

    let body = function.body();
    if block_statement_returns(body.clone()) {
        return None;
    }
    if body.len() == 0 {
        Some(body.location().clone())
    } else {
        let last = body.statement(body.len() - 1);
        Some(last.location().clone())
    }
}

struct Analyzer {
    function_ids: HashMap<StringID, FunctionID>,
    function_table: FunctionTable,
    variable_table: VariableTable,
    scopes: Scopes,
    constraints: Vec<Constraint>,
    current_function: Option<FunctionID>,
}

impl Analyzer {
    fn new() -> Self {
        Analyzer {
            function_ids: HashMap::new(),
            function_table: FunctionTable::new(),
            variable_table: VariableTable::new(),
            scopes: Scopes::new(),
            constraints: Vec::new(),
            current_function: None,
        }
    }

    fn bin_expr(&mut self, expr: parser::BinExpr) -> AnalysisResult<(Expr, BuiltinType)> {
        let (lhs, l_typ) = self.expr(expr.lhs())?;
        let (rhs, r_typ) = self.expr(expr.rhs())?;
        let typ = match expr.op {
            BinOp::Add | BinOp::Div | BinOp::Mul | BinOp::Sub | BinOp::BitOr | BinOp::BitAnd => {
                self.constraints
                    .push(ConstraintType::SameType(I32, l_typ).at(expr.lhs().location().clone()));
                self.constraints
                    .push(ConstraintType::SameType(I32, r_typ).at(expr.rhs().location().clone()));
                I32
            }
            BinOp::And | BinOp::Or => {
                self.constraints
                    .push(ConstraintType::SameType(Bool, l_typ).at(expr.lhs().location().clone()));
                self.constraints
                    .push(ConstraintType::SameType(Bool, r_typ).at(expr.rhs().location().clone()));
                Bool
            }
            BinOp::Less | BinOp::LessEqual | BinOp::Greater | BinOp::GreaterEqual => {
                self.constraints
                    .push(ConstraintType::SameType(I32, l_typ).at(expr.lhs().location().clone()));
                self.constraints
                    .push(ConstraintType::SameType(I32, r_typ).at(expr.rhs().location().clone()));
                Bool
            }
            BinOp::Equal | BinOp::NotEqual => {
                self.constraints
                    .push(ConstraintType::SameType(l_typ, r_typ).at(expr.rhs().location().clone()));
                Bool
            }
        };
        Ok((Expr::BinExpr(expr.op, Box::new(lhs), Box::new(rhs)), typ))
    }

    fn function_expr(&mut self, expr: parser::FunctionExpr) -> AnalysisResult<(Expr, BuiltinType)> {
        let name = expr.function();
        let &id = self
            .function_ids
            .get(&name)
            .ok_or(ErrorType::UndefinedFunction(name).at(expr.location().clone()))?;
        let function = self.function_table[id].clone();
        let mut params = Vec::new();
        for i in 0..expr.param_count() {
            let (param, typ) = self.expr(expr.param(i))?;
            self.constraints.push(
                ConstraintType::SameType(function.arg_types[i], typ)
                    .at(expr.param(i).location().clone()),
            );
            params.push(param);
        }
        let typ = function.return_type;
        Ok((Expr::FunctionCall(id, params), typ))
    }

    fn int_lit_expr(&mut self, expr: parser::IntLitExpr) -> AnalysisResult<(Expr, BuiltinType)> {
        Ok((Expr::IntExpr(expr.int_lit()), I32))
    }

    fn unary_expr(&mut self, expr: parser::UnaryExpr) -> AnalysisResult<(Expr, BuiltinType)> {
        let (operand, operand_typ) = self.expr(expr.expr())?;
        let typ = match expr.op {
            UnaryOp::Negate => {
                self.constraints
                    .push(ConstraintType::SameType(I32, operand_typ).at(expr.location().clone()));
                I32
            }
            UnaryOp::Not => {
                self.constraints
                    .push(ConstraintType::SameType(Bool, operand_typ).at(expr.location().clone()));
                Bool
            }
        };
        Ok((Expr::UnaryExpr(expr.op, Box::new(operand)), typ))
    }

    fn var_expr(&mut self, expr: parser::VarExpr) -> AnalysisResult<(Expr, BuiltinType)> {
        let name = expr.var();
        let id = self
            .scopes
            .get(name)
            .ok_or(ErrorType::UndefinedVar(name).at(expr.location().clone()))?;
        let var_typ = self.variable_table[id].typ;
        Ok((Expr::VarExpr(id), var_typ))
    }

    fn expr(&mut self, expr: parser::Expr) -> AnalysisResult<(Expr, BuiltinType)> {
        match expr.kind() {
            ExprKind::BinExpr(expr) => self.bin_expr(expr),
            ExprKind::FunctionExpr(expr) => self.function_expr(expr),
            ExprKind::IntLitExpr(expr) => self.int_lit_expr(expr),
            ExprKind::UnaryExpr(expr) => self.unary_expr(expr),
            ExprKind::VarExpr(expr) => self.var_expr(expr),
        }
    }

    fn block_statement(&mut self, block: parser::BlockStatement) -> AnalysisResult<Statement> {
        self.scopes.enter();
        let mut statements = Vec::new();
        for i in 0..block.len() {
            let statement = self.statement(block.statement(i))?;
            statements.push(statement);
        }
        self.scopes.exit();
        Ok(Statement::Block(statements))
    }

    fn expr_statement(&mut self, statement: parser::ExprStatement) -> AnalysisResult<Statement> {
        let (expr, _) = self.expr(statement.expr())?;
        Ok(Statement::Expr(expr))
    }

    fn if_statement(&mut self, statement: parser::IfStatement) -> AnalysisResult<Statement> {
        let (cond, typ) = self.expr(statement.cond())?;
        self.constraints
            .push(ConstraintType::SameType(Bool, typ).at(statement.cond().location().clone()));
        let if_branch = self.statement(statement.if_branch())?;
        let else_branch = match statement.else_branch() {
            None => None,
            Some(branch) => Some(Box::new(self.statement(branch)?)),
        };
        Ok(Statement::If(cond, Box::new(if_branch), else_branch))
    }

    fn var_statement(&mut self, statement: parser::VarStatement) -> AnalysisResult<Statement> {
        let var = statement.var();
        let typ = statement.typ();
        let id = self.variable_table.add_variable(Variable::new(var, typ));
        self.scopes.put(var, id);
        let (expr, expr_typ) = self.expr(statement.expr())?;
        self.constraints
            .push(ConstraintType::SameType(typ, expr_typ).at(statement.expr().location().clone()));
        Ok(Statement::Var(id, expr))
    }

    fn return_statement(
        &mut self,
        statement: parser::ReturnStatement,
    ) -> AnalysisResult<Statement> {
        let (expr, typ) = self.expr(statement.expr())?;
        let function = self.current_function.unwrap();
        self.constraints.push(
            ConstraintType::ReturnType(function, typ).at(statement.expr().location().clone()),
        );
        Ok(Statement::Return(expr))
    }

    fn statement(&mut self, statement: parser::Statement) -> AnalysisResult<Statement> {
        match statement.kind() {
            StatementKind::BlockStatement(block) => self.block_statement(block),
            StatementKind::ExprStatement(expr) => self.expr_statement(expr),
            StatementKind::IfStatement(statement) => self.if_statement(statement),
            StatementKind::VarStatement(statement) => self.var_statement(statement),
            StatementKind::ReturnStatement(statement) => self.return_statement(statement),
        }
    }

    fn function(&mut self, function: parser::Function) -> AnalysisResult<FunctionDef> {
        self.scopes.enter();
        let mut args = Vec::new();
        // This scheme allows parameters to shadow preceding ones.
        // The rationale is that this is similar to var statements inside a function
        for i in 0..function.param_count() {
            let (name, typ) = function.param(i);
            let var = Variable::new(name, typ);
            let var_id = self.variable_table.add_variable(var);
            self.scopes.put(name, var_id);
            args.push(var_id);
        }
        let id = self.function_ids[&function.name()];
        self.current_function = Some(id);
        let body = self.block_statement(function.body())?;
        self.scopes.exit();

        if let Some(location) = function_doesnt_return(function.clone()) {
            self.constraints
                .push(ConstraintType::NoReturn(id).at(location));
        }

        Ok(FunctionDef { id, args, body })
    }

    fn gather_function(&mut self, function: parser::Function) -> AnalysisResult<()> {
        let name = function.name();
        if self.function_ids.contains_key(&name) {
            return Err(ErrorType::FunctionRedefinition(name).at(function.location().clone()));
        }
        let mut arg_types = Vec::new();
        for i in 0..function.param_count() {
            let (_, typ) = function.param(i);
            arg_types.push(typ);
        }
        let ret_type = function.return_type();
        let id = self
            .function_table
            .add_function(Function::new(name, ret_type, arg_types));
        self.function_ids.insert(name, id);
        Ok(())
    }

    fn run(&mut self, ast: &parser::AST) -> AnalysisResult<Vec<FunctionDef>> {
        let mut functions = Vec::new();
        for i in 0..ast.function_count() {
            self.gather_function(ast.function(i))?;
        }
        for i in 0..ast.function_count() {
            functions.push(self.function(ast.function(i))?);
        }
        Ok(functions)
    }
}

fn solve_constraints(functions: &FunctionTable, constraints: Vec<Constraint>) -> Vec<Error> {
    let mut errors = Vec::new();
    for constraint in constraints {
        match constraint.constraint {
            ConstraintType::SameType(expected, actual) => {
                if expected != actual {
                    errors.push(ErrorType::TypeMismatch(expected, actual).at(constraint.location))
                }
            }
            ConstraintType::NoReturn(id) => {
                let function = &functions[id];
                let ret_type = function.return_type;
                if ret_type != Unit {
                    errors.push(
                        ErrorType::NoReturnInFunction(function.name, ret_type)
                            .at(constraint.location),
                    );
                }
            }
            ConstraintType::ReturnType(id, actual) => {
                let function = &functions[id];
                let ret_type = function.return_type;
                if ret_type != actual {
                    errors.push(
                        ErrorType::BadReturnType(function.name, ret_type, actual)
                            .at(constraint.location),
                    )
                }
            }
        }
    }
    errors
}

pub fn analyze(ast: &parser::AST) -> Result<AST, Vec<Error>> {
    let mut analyzer = Analyzer::new();
    let functions = match analyzer.run(ast) {
        Err(e) => return Err(vec![e]),
        Ok(ast) => ast,
    };
    let errors = solve_constraints(&analyzer.function_table, analyzer.constraints);
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(AST {
        functions,
        function_table: analyzer.function_table,
        variable_table: analyzer.variable_table,
    })
}
