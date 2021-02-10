use crate::analysis::{
    Expr, FunctionDef, FunctionID, FunctionTable, Statement, VariableID, VariableTable, AST,
};
use crate::builtin::{BuiltinFunction, Type};
use crate::errors::Error;
use io::Write;
use std::fmt;
use std::io;

struct CType {
    typ: Type,
}

impl CType {
    fn new(typ: Type) -> Self {
        CType { typ }
    }
}

impl fmt::Display for CType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.typ {
            Type::Bool => write!(f, "bool"),
            Type::I32 => write!(f, "int32_t"),
            Type::Unit => write!(f, "void"),
        }
    }
}

struct FunctionName {
    id: FunctionID,
}

impl FunctionName {
    fn new(id: FunctionID) -> Self {
        FunctionName { id }
    }
}

impl fmt::Display for FunctionName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "chika_{}", self.id)
    }
}

/// A struct capable of writing things out to a C file.
///
/// This houses utilities and context making things code generation a bit easier.
struct Writer<'a> {
    writer: &'a mut dyn io::Write,
    variable_table: &'a VariableTable,
    function_table: &'a FunctionTable,
}

impl<'a> Writer<'a> {
    fn new(
        writer: &'a mut dyn io::Write,
        variable_table: &'a VariableTable,
        function_table: &'a FunctionTable,
    ) -> Self {
        Writer {
            writer,
            variable_table,
            function_table,
        }
    }

    fn includes(&mut self) -> Result<(), Error> {
        writeln!(self, "#include <stdbool.h>")?;
        writeln!(self, "#include <stdint.h>")?;
        writeln!(self, "#include <stdio.h>")?;
        Ok(())
    }

    fn function_declarations(&mut self) -> Result<(), Error> {
        for (id, function) in self.function_table.iter() {
            write!(
                self,
                "{} {}(",
                CType::new(function.return_type),
                FunctionName::new(id)
            )?;
            let mut first = true;
            for typ in &function.arg_types {
                if *typ == Type::Unit {
                    continue;
                }
                if first {
                    first = false;
                } else {
                    write!(self, ", ")?;
                }
                write!(self, "{}", CType::new(*typ))?;
            }
            writeln!(self, ");")?;
        }
        Ok(())
    }

    fn var_is_unit(&self, var_id: VariableID) -> bool {
        self.variable_table[var_id].typ == Type::Unit
    }

    fn expr(&mut self, expr: &Expr) -> Result<(), Error> {
        match expr {
            Expr::AssignExpr(var_id, expr) if !self.var_is_unit(*var_id) => {
                write!(self, "{} = ", var_id)?;
                self.expr(expr)?;
            }
            Expr::BinExpr(op, e1, e2) => {
                write!(self, "(")?;
                self.expr(e1)?;
                write!(self, ") {} (", op)?;
                self.expr(e2)?;
                write!(self, ")")?;
            }
            Expr::BuiltinFunctionCall(BuiltinFunction::PrintI32, args) => {
                write!(self, "printf(\"%d\\n\", ")?;
                self.expr(&args[0])?;
                write!(self, ")")?;
            }
            Expr::FunctionCall(func, args) => {
                write!(self, "{}(", FunctionName::new(*func))?;
                let function = &self.function_table[*func];
                let mut first = true;
                for (arg, typ) in args.iter().zip(&function.arg_types) {
                    if *typ == Type::Unit {
                        continue;
                    }
                    if first {
                        first = false;
                    } else {
                        write!(self, ", ")?;
                    }
                    self.expr(arg)?;
                }
                write!(self, ")")?;
            }
            Expr::IntExpr(u) => {
                write!(self, "{}", u)?;
            }
            Expr::UnaryExpr(op, expr) => {
                write!(self, "{}(", op)?;
                self.expr(expr)?;
                write!(self, ")")?;
            }
            Expr::VarExpr(var_id) if !self.var_is_unit(*var_id) => {
                write!(self, "{}", var_id)?;
            }
            _ => {}
        };
        Ok(())
    }

    fn statement(&mut self, statement: &Statement) -> Result<(), Error> {
        match statement {
            Statement::Block(statements) => {
                writeln!(self, "{{")?;
                for statement in statements {
                    self.statement(statement)?;
                }
                writeln!(self, "}}")?;
            }
            Statement::Expr(expr) => {
                self.expr(expr)?;
                writeln!(self, ";")?;
            }
            Statement::If(cond, if_branch, maybe_else) => {
                write!(self, "if (")?;
                self.expr(cond)?;
                writeln!(self, ")")?;
                self.statement(if_branch)?;
                if let Some(else_branch) = maybe_else {
                    writeln!(self, "else")?;
                    self.statement(else_branch)?;
                }
            }
            Statement::Return(maybe_expr) => {
                write!(self, "return ")?;
                if let Some(expr) = maybe_expr {
                    self.expr(expr)?;
                }
                writeln!(self, ";")?;
            }
            Statement::Var(var_id, expr) => {
                let variable = &self.variable_table[*var_id];
                if variable.typ != Type::Unit {
                    write!(self, "{} {} = ", CType::new(variable.typ), var_id)?;
                    self.expr(expr)?;
                    writeln!(self, ";")?;
                }
            }
        };
        Ok(())
    }

    fn function(&mut self, function_def: &FunctionDef) -> Result<(), Error> {
        let function = &self.function_table[function_def.id];
        write!(
            self,
            "{} {}(",
            CType::new(function.return_type),
            FunctionName::new(function_def.id)
        )?;
        let mut first = true;
        for (typ, var_id) in function.arg_types.iter().zip(&function_def.args) {
            if *typ == Type::Unit {
                continue;
            }
            if first {
                first = false
            } else {
                write!(self, ", ")?;
            }
            write!(self, "{} {}", CType::new(*typ), var_id)?;
        }
        writeln!(self, ")")?;
        self.statement(&function_def.body)
    }

    fn functions(&mut self, functions: &[FunctionDef]) -> Result<(), Error> {
        for function in functions {
            self.function(function)?;
            writeln!(self, "")?;
        }
        Ok(())
    }

    fn main_function(&mut self, main_id: FunctionID) -> Result<(), Error> {
        writeln!(self, "int main() {{")?;
        writeln!(self, "  {}();", FunctionName::new(main_id))?;
        writeln!(self, "  return 0;")?;
        writeln!(self, "}}")?;
        Ok(())
    }

    fn generate(&mut self, functions: &[FunctionDef]) -> Result<(), Error> {
        self.includes()?;
        writeln!(self, "")?;
        self.function_declarations()?;
        writeln!(self, "")?;
        self.functions(&functions)?;
        let main_id = functions.last().unwrap().id;
        self.main_function(main_id)
    }
}

impl<'a> io::Write for Writer<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.writer.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

pub fn generate(writer: &mut dyn io::Write, ast: AST) -> Result<(), Error> {
    Writer::new(writer, &ast.variable_table, &ast.function_table).generate(&ast.functions)
}
