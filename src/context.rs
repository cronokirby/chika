use std::io;

use codespan_reporting::files::SimpleFile;

use crate::codespan_reporting::diagnostic::Diagnostic;
use crate::codespan_reporting::term;
use term::termcolor::ColorSpec;
use term::termcolor::WriteColor;

/// A String ID can be used in place of a string basically everywhere.
///
/// The idea is that each unique String ID corresponds to an original string
/// in the source code. The advantage of using IDs is that comparison is much faster,
/// and they use up much less space.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct StringID(u32);

#[derive(Debug)]
pub struct Context {
    table: Vec<String>,
}

impl Context {
    pub fn new() -> Self {
        Context { table: Vec::new() }
    }

    pub fn add_string(&mut self, string: String) -> StringID {
        let id = StringID(self.table.len() as u32);
        self.table.push(string);
        id
    }

    pub fn get_string(&self, id: StringID) -> &str {
        &self.table[id.0 as usize]
    }
}

/// A struct that we can use to print the outputs of our compiler.
///
/// This has some buffer we can write to, usually the terminal,
/// but also references a string table, so that we can print String IDs in a nice
/// way for end-users.
pub struct Printer<'a> {
    buf: &'a mut dyn WriteColor,
    pub ctx: &'a Context,
    files: &'a SimpleFile<String, String>,
}

impl<'a> Printer<'a> {
    /// Create a new printer from an output buffer and a table
    pub fn new(
        buf: &'a mut dyn WriteColor,
        ctx: &'a Context,
        files: &'a SimpleFile<String, String>,
    ) -> Self {
        Self { buf, ctx, files }
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
