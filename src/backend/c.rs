use crate::analysis::AST;
use crate::errors::Error;
use io::Write;
use std::io;

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

    fn generate(&mut self, _ast: AST) -> Result<(), Error> {
        writeln!(self, "#include <stdio.h>\n")?;
        writeln!(self, "int main() {{")?;
        writeln!(self, "  puts(\"Hello from Chika!\");")?;
        writeln!(self, "  return 0;")?;
        writeln!(self, "}}")?;
        Ok(())
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
