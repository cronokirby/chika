use crate::analysis::AST;
use crate::errors::Error;
use std::io;

pub fn generate(writer: &mut dyn io::Write, _ast: AST) -> Result<(), Error> {
    writeln!(writer, "#include <stdio.h>\n")?;
    writeln!(writer, "int main() {{")?;
    writeln!(writer, "  puts(\"Hello from Chika!\");")?;
    writeln!(writer, "  return 0;")?;
    writeln!(writer, "}}")?;
    Ok(())
}
