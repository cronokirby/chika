use std::io;

use crate::interner::StringTable;

pub struct Printer<'a> {
    buf: &'a mut dyn io::Write,
    pub table: &'a StringTable,
}

impl<'a> Printer<'a> {
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

pub trait Printable {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> io::Result<()>;
}
