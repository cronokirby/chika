use std::io;

use crate::interner::StringTable;

/// A struct that we can use to print the outputs of our compiler.
///
/// This has some buffer we can write to, usually the terminal,
/// but also references a string table, so that we can print String IDs in a nice
/// way for end-users.
pub struct Printer<'a> {
    buf: &'a mut dyn io::Write,
    pub table: &'a StringTable,
}

impl<'a> Printer<'a> {
    /// Create a new printer from an output buffer and a table
    pub fn new(buf: &'a mut dyn io::Write, table: &'a StringTable) -> Self {
        Self { buf, table }
    }
}

impl<'a> io::Write for Printer<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.buf.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.buf.flush()
    }
}

/// A trait for things that are printable using a Printer.
///
/// This is commonly used for things that benefit from having access to this context,
/// so that they can print String IDs with actual strings, for example.
pub trait Printable {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> io::Result<()>;
}
