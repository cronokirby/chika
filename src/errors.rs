use crate::codespan_reporting::files;
use std::{fmt, io};

#[derive(Debug)]
pub enum Error {
    IO(io::Error),
}

impl From<files::Error> for Error {
    fn from(error: files::Error) -> Self {
        match error {
            files::Error::Io(e) => e.into(),
            other => panic!("Compiler Bug:\n{}", other),
        }
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error::IO(error)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::IO(e) => write!(f, "IO Error: {}", e),
        }
    }
}
