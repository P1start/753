use std::collections::HashMap;
use util::Error;

#[derive(Debug)]
pub enum Token {
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LSqrBr,
    /// `]`
    RSqrBr,
    /// An integer (e.g., `-137`)
    Integer(i64), // TODO is it right to use i64 here?
    /// An identifier (e.g., `foo`)
    Ident(String),
}

#[derive(Debug)]
pub enum Expr {
    /// A call: something like `(foo: bar baz: qux)`
    SExpr(HashMap<String, Vec<Expr>>),
    /// An array literal: something like `[foo bar baz qux]`.
    Array(Vec<Expr>),
}

#[derive(Debug)]
pub enum ParseError {
    EndOfFile,
    UnknownChar(char),
}

/// The tokenizer: the part of the parsing pipeline that breaks up source code into `Token`s.
#[derive(Copy, Clone, Debug)]
pub struct Tokenizer<'src> {
    /// The contents of a single source file.
    src: &'src str,
}

impl<'src> Tokenizer<'src> {
    fn peek_char(&mut self) -> Result<char, ParseError> {
        self.src.chars().next().ok_or(ParseError::EndOfFile)
    }

    fn advance(&mut self) -> Result<char, ParseError> {
        let this_char = self.peek_char()?;
        let char_length = this_char.len_utf8();
        self.src = &self.src[char_length..];
        Ok(this_char)
    }

    fn is_ident_char(c: char) -> bool {
        match c {
            '0' ... '9' | 'a' ... 'z' | 'A' ... 'Z' | '-' | '_' => true,
            _ => false,
        }
    }

    pub fn eat_token(&mut self) -> Result<Token, ParseError> {
        // Skip whitespace
        loop {
            match self.peek_char() {
                Ok(s) if s.is_whitespace() => self.advance()?,
                _ => break,
            };
        }

        let this_char = self.advance()?;
        Ok(match this_char {
            '(' => Token::LParen,
            ')' => Token::RParen,
            '[' => Token::LSqrBr,
            ']' => Token::RSqrBr,
            c if Self::is_ident_char(c) => {
                let mut string = String::new();
                string.push(this_char);
                loop {
                    match self.peek_char() {
                        Ok(next_char) if Self::is_ident_char(next_char) => {
                            self.advance()?;
                            string.push(next_char);
                        },
                        _ => break,
                    }
                }
                match string.parse() {
                    Ok(value) => Token::Integer(value),
                    Err(_) => Token::Ident(string),
                }
            },
            c => return Err(ParseError::UnknownChar(c)),
        })
    }

    pub fn peek_token(&mut self) -> Result<Token, ParseError> {
        let old_src = self.src;
        let res = self.eat_token();
        self.src = old_src;
        res
    }
}

/// The parser.
#[derive(Debug)]
pub struct Parser<'src> {
    /// The tokenizer.
    tokenizer: Tokenizer<'src>,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_tokenizer() {
        let src1 = "(foo 1\n\t[2 3a])";
        let mut tok1 = Tokenizer { src: src1 };
        let mut i = 0;
        loop {
            match (i, tok1.eat_token()) {
                (0, Ok(Token::LParen)) => {},
                (1, Ok(Token::Ident(ref s))) if s == "foo" => {},
                (2, Ok(Token::Integer(1))) => {},
                (3, Ok(Token::LSqrBr)) => {},
                (4, Ok(Token::Integer(2))) => {},
                (5, Ok(Token::Ident(ref s))) if s == "3a" => {},
                (6, Ok(Token::RSqrBr)) => {},
                (7, Ok(Token::RParen)) => {},
                (8, Err(ParseError::EndOfFile)) => break,
                (i, res) => panic!("unexpected token {}: {:?}", i, res),
            }
            i += 1;
        }
    }
}