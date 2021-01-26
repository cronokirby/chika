use codespan_reporting::files;
use std::fs;
use std::io;
use std::ops::Range;
use std::path::Path;

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

/// A unique identifier for each file you have when compiling
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FileID(usize);

impl FileID {
    /// A dummy file id to use for tests
    pub fn dummy() -> FileID {
        FileID(0xBAD)
    }
}

/// A table allowing us to interact with the files we have
#[derive(Debug)]
pub struct FileTable {
    files: Vec<File>,
}

impl FileTable {
    /// Create a new file table, with no files stored
    pub fn new() -> Self {
        FileTable { files: Vec::new() }
    }

    /// Read a file, and add it to this table
    pub fn add_file(&mut self, path: &Path) -> io::Result<FileID> {
        let file = File::from_path(path)?;
        let id = FileID(self.files.len());
        self.files.push(file);
        Ok(id)
    }

    fn get_file(&self, id: FileID) -> Result<&File, files::Error> {
        self.files.get(id.0).ok_or(files::Error::FileMissing)
    }

    /// Get the size of a given file.
    ///
    /// If this file doesn't exist, this will fail.
    pub fn file_size(&self, id: FileID) -> Result<usize, files::Error> {
        Ok(self.get_file(id)?.source.len())
    }
}

impl<'a> files::Files<'a> for FileTable {
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
