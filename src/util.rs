use parser::ParseError;
use std::io;

#[derive(Debug)]
pub enum Error {
    ParseError(ParseError),
    IoError(io::Error),
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Error {
        Error::ParseError(err)
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error {
        Error::IoError(err)
    }
}