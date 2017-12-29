use parse::ParseError;
use compile::CompileError;

use std::io;

#[derive(Debug)]
pub enum Error {
    ParseError(ParseError),
    CompileError(CompileError),
    IoError(io::Error),
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        Error::ParseError(err)
    }
}

impl From<CompileError> for Error {
    fn from(err: CompileError) -> Error {
        Error::CompileError(err)
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IoError(err)
    }
}