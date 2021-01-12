use std::fmt;

use crate::interner::StringTable;

pub struct Printer<'a> {
    buf: &'a mut dyn fmt::Write,
    pub table: &'a StringTable,
}

impl<'a> fmt::Write for Printer<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.buf.write_str(s)
    }
}

pub trait Printable {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> fmt::Result;
}
