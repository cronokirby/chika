use crate::analysis::{FunctionDef, FunctionID, FunctionTable, AST};
use crate::builtin::Type;
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
}

impl<'a> Writer<'a> {
    fn new(writer: &'a mut dyn io::Write) -> Self {
        Writer { writer }
    }

    fn includes(&mut self) -> Result<(), Error> {
        writeln!(self, "#include <stdbool.h>")?;
        writeln!(self, "#include <stdint.h>")?;
        writeln!(self, "#include <stdio.h>")?;
        Ok(())
    }

    fn function_declarations(&mut self, function_table: &FunctionTable) -> Result<(), Error> {
        for (id, function) in function_table.iter() {
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

    fn function(&mut self, table: &FunctionTable, function_def: &FunctionDef) -> Result<(), Error> {
        let function = &table[function_def.id];
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
        writeln!(self, ") {{\n}}\n")?;
        Ok(())
    }

    fn functions(&mut self, table: &FunctionTable, functions: &[FunctionDef]) -> Result<(), Error> {
        for function in functions {
            self.function(table, function)?;
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

    fn generate(&mut self, ast: AST) -> Result<(), Error> {
        self.includes()?;
        writeln!(self, "")?;
        self.function_declarations(&ast.function_table)?;
        writeln!(self, "")?;
        self.functions(&ast.function_table, &ast.functions)?;
        let main_id = ast.functions.last().unwrap().id;
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
    Writer::new(writer).generate(ast)
}
