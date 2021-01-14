use std::io;

use codespan_reporting::files::SimpleFile;

use crate::codespan_reporting::diagnostic::Diagnostic;
use crate::codespan_reporting::term;
use crate::interner::StringTable;
use term::termcolor::ColorSpec;
use term::termcolor::WriteColor;

/// A struct that we can use to print the outputs of our compiler.
///
/// This has some buffer we can write to, usually the terminal,
/// but also references a string table, so that we can print String IDs in a nice
/// way for end-users.
pub struct Printer<'a> {
    buf: &'a mut dyn WriteColor,
    pub table: &'a StringTable,
    files: &'a SimpleFile<String, String>,
}

impl<'a> Printer<'a> {
    /// Create a new printer from an output buffer and a table
    pub fn new(
        buf: &'a mut dyn WriteColor,
        table: &'a StringTable,
        files: &'a SimpleFile<String, String>,
    ) -> Self {
        Self { buf, table, files }
    }

    pub fn write_diagnostic(&mut self, diagnostic: Diagnostic<()>) {
        let config = term::Config::default();
        term::emit(self.buf, &config, self.files, &diagnostic).unwrap();
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

impl<'a> WriteColor for Printer<'a> {
    fn supports_color(&self) -> bool {
        self.buf.supports_color()
    }

    fn set_color(&mut self, spec: &ColorSpec) -> io::Result<()> {
        self.buf.set_color(spec)
    }

    fn reset(&mut self) -> io::Result<()> {
        self.buf.reset()
    }
}

/// A trait for things that are printable using a Printer.
///
/// This is commonly used for things that benefit from having access to this context,
/// so that they can print String IDs with actual strings, for example.
pub trait Printable {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> io::Result<()>;
}
