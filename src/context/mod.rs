mod files;

pub use files::{FileID, FileTable};
use std::fmt;
use std::io;
use std::ops::Range;
use std::path::Path;

use crate::codespan_reporting::term;
use crate::{codespan_reporting::diagnostic, errors::Error};
use term::termcolor::WriteColor;

/// A String ID can be used in place of a string basically everywhere.
///
/// The idea is that each unique String ID corresponds to an original string
/// in the source code. The advantage of using IDs is that comparison is much faster,
/// and they use up much less space.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StringID(u32);

/// A type of diagnostic we use for
pub type Diagnostic = diagnostic::Diagnostic<FileID>;

#[derive(Debug)]
pub struct Context {
    table: Vec<String>,
    pub files: FileTable,
    pub main_file: FileID,
    pub current_file: FileID,
}

impl Context {
    pub fn empty() -> Self {
        Context {
            table: Vec::new(),
            files: FileTable::new(),
            main_file: FileID::dummy(),
            current_file: FileID::dummy(),
        }
    }

    pub fn with_main_file(path: &Path) -> io::Result<Self> {
        let mut ctx = Self::empty();
        ctx.main_file = ctx.files.add_file(path)?;
        ctx.current_file = ctx.main_file;
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

    /// Print out a diagnostic to some terminal capable of writing colors
    pub fn emit_diagnostic(
        &self,
        writer: &mut dyn WriteColor,
        diagnostic: &Diagnostic,
    ) -> Result<(), Error> {
        let config = term::Config::default();
        term::emit(writer, &config, &self.files, diagnostic)?;
        Ok(())
    }
}

const INDENT_SIZE: usize = 2;

/// Represents the kind of context we use when displaying things
///
/// This has some information about indentation, and stuff like that
#[derive(Clone, Copy, Debug)]
pub struct DisplayContext<'a> {
    pub ctx: &'a Context,
    indent: usize,
}

impl<'a> DisplayContext<'a> {
    /// Create a new context, but further indented
    pub fn indented(self) -> DisplayContext<'a> {
        DisplayContext {
            ctx: self.ctx,
            indent: self.indent + INDENT_SIZE,
        }
    }

    /// Write out blank space according to the indentation of this context
    pub fn blank_space(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:<width$}", "", width = self.indent)
    }
}

impl<'a> From<&'a Context> for DisplayContext<'a> {
    fn from(ctx: &'a Context) -> Self {
        DisplayContext { ctx, indent: 0 }
    }
}

/// A trait for items that can be displayed, provided that they have a context.
///
/// The main purpose of this trait is to display items that need a context
/// to look up things like strings, etc.
pub trait DisplayWithContext {
    /// Format a given value using some context
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result;

    fn with_ctx<'a, I: Into<DisplayContext<'a>>>(&'a self, ctx: I) -> WithContext<'a, Self> {
        WithContext {
            val: self,
            ctx: ctx.into(),
        }
    }
}

/// Attach a context to some reference.
///
/// The main purpose of this is to implement Display for types implementing the
/// `DisplayWithContext` trait.
#[derive(Debug)]
pub struct WithContext<'a, T: ?Sized> {
    val: &'a T,
    ctx: DisplayContext<'a>,
}

impl<'a, T: DisplayWithContext> fmt::Display for WithContext<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.val.fmt_with(self.ctx, f)
    }
}

/// A trait for items convertible to diagnostics.
///
/// We don't use Into, simply because we usually need access to the compiler
/// context in order to perform this conversion.
pub trait IsDiagnostic {
    fn diagnostic(&self, ctx: &Context) -> Diagnostic;
}

/// A location of some item in the source code
#[derive(Clone, Copy, Debug)]
pub struct Location {
    /// The file this snippet originates from
    pub file: FileID,
    pub start: usize,
    pub end: usize,
}

impl Location {
    /// Create a new location, from a file, and a range of bytes
    pub fn new(file: FileID, start: usize, end: usize) -> Self {
        Location { file, start, end }
    }

    /// Create a new location spanning from this location to that location
    pub fn to(&self, that: &Location) -> Self {
        assert_eq!(self.file, that.file);
        Location::new(self.file, self.start, that.end)
    }
}

impl Into<Range<usize>> for Location {
    fn into(self) -> Range<usize> {
        self.start..self.end
    }
}
