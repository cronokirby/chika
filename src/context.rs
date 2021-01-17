use std::fs;
use std::io;
use std::ops::Range;
use std::path::Path;

use codespan_reporting::files;

use crate::{codespan_reporting::diagnostic::Diagnostic, errors::Error};
use crate::{codespan_reporting::term, errors};
use term::termcolor::ColorSpec;
use term::termcolor::WriteColor;

#[derive(Debug)]
struct File {
    name: String,
    source: String,
    line_starts: Vec<usize>,
}

impl File {
    fn from_path(path: &Path) -> io::Result<Self> {
        let source = fs::read_to_string(path)?;
        let name = path.to_string_lossy().to_string();

        let mut line_starts = vec![0];
        let mut pos = 0;
        for c in source.bytes() {
            pos += 1;
            if c == b'\n' {
                line_starts.push(pos);
            }
        }
        line_starts.push(pos);

        Ok(File {
            name,
            source,
            line_starts,
        })
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn source(&self) -> &str {
        &self.source
    }

    fn line_index(&self, byte_index: usize) -> Result<usize, files::Error> {
        match self.line_starts.binary_search(&byte_index) {
            Ok(line) => Ok(line),
            Err(next_line) => Ok(next_line - 1),
        }
    }

    fn line_range(&self, index: usize) -> Result<Range<usize>, files::Error> {
        let max = self.line_starts.len() - 2;
        if index > max {
            return Err(files::Error::LineTooLarge { given: index, max });
        }
        let start = self.line_starts[index];
        let end = self.line_starts[index + 1];
        Ok(start..end)
    }
}

/// A String ID can be used in place of a string basically everywhere.
///
/// The idea is that each unique String ID corresponds to an original string
/// in the source code. The advantage of using IDs is that comparison is much faster,
/// and they use up much less space.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct StringID(u32);

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FileID(usize);

#[derive(Debug)]
pub struct Context {
    table: Vec<String>,
    files: Vec<File>,
    pub main_file: FileID,
}

impl Context {
    pub fn empty() -> Self {
        Context {
            table: Vec::new(),
            files: Vec::new(),
            main_file: FileID(0),
        }
    }

    pub fn with_main_file(path: &Path) -> io::Result<Self> {
        let mut ctx = Self::empty();
        ctx.main_file = ctx.add_file(path)?;
        Ok(ctx)
    }

    pub fn add_string(&mut self, string: String) -> StringID {
        let id = StringID(self.table.len() as u32);
        self.table.push(string);
        id
    }

    pub fn get_string(&self, id: StringID) -> &str {
        &self.table[id.0 as usize]
    }

    pub fn add_file(&mut self, path: &Path) -> io::Result<FileID> {
        let file = File::from_path(path)?;
        let id = FileID(self.files.len());
        self.files.push(file);
        Ok(id)
    }

    fn get_file(&self, id: FileID) -> Result<&File, files::Error> {
        self.files.get(id.0).ok_or(files::Error::FileMissing)
    }

    pub fn file_size(&self, id: FileID) -> Result<usize, files::Error> {
        Ok(self.get_file(id)?.source.len())
    }
}

impl<'a> files::Files<'a> for Context {
    type FileId = FileID;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        Ok(self.get_file(id)?.name())
    }

    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        Ok(self.get_file(id)?.source())
    }

    fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, files::Error> {
        self.get_file(id)?.line_index(byte_index)
    }

    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<Range<usize>, files::Error> {
        self.get_file(id)?.line_range(line_index)
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
}

impl<'a> Printer<'a> {
    /// Create a new printer from an output buffer and a table
    pub fn new(buf: &'a mut dyn WriteColor, ctx: &'a Context) -> Self {
        Self { buf, ctx }
    }

    pub fn write_diagnostic(&mut self, diagnostic: Diagnostic<FileID>) -> Result<(), Error> {
        let config = term::Config::default();
        term::emit(self.buf, &config, self.ctx, &diagnostic)?;
        Ok(())
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
    fn print<'a>(&self, printer: &mut Printer<'a>) -> errors::Result<()>;
}

/// A location of some item in the source code
#[derive(Debug)]
pub struct Location {
    /// The file this snippet originates from
    pub file: FileID,
    /// The range in bytes that this snippet occupies
    pub range: Range<usize>,
}

impl Location {
    /// Create a new location, from a file, and a range of bytes
    pub fn new(file: FileID, range: Range<usize>) -> Self {
        Location { file, range }
    }
}
