mod c;
use crate::analysis::AST;
use crate::errors::Error;
use std::io;

pub fn generate_c(writer: &mut dyn io::Write, ast: AST) -> Result<(), Error> {
    c::generate(writer, ast)
}
