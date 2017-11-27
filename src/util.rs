use parser::ParseError;

pub enum Error {
    ParseError(ParseError),
}