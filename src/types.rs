use crate::printer::{Printable, Printer};
use std::io;
use std::io::Write;

/// Represents a kind of builtin type we know about
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BuiltinType {
    /// The builtin 32 bit signed integer type
    I32,
    /// The unit, or void type
    Unit,
}

impl Printable for BuiltinType {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> io::Result<()> {
        use BuiltinType::*;

        match self {
            I32 => write!(printer, "I32"),
            Unit => write!(printer, "Unit"),
        }
    }
}
