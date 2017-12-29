use std::fmt;
use codemap::{Span, FileId};

#[derive(Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
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
    /// The token at the end of a file.
    /// 
    /// This is generated endlessly by the tokenizer once it has reached the end of a file.
    Eof,
}

impl TokenKind {
    fn matching_bracket(&self) -> Option<TokenKind> {
        match *self {
            TokenKind::LParen => Some(TokenKind::RParen),
            TokenKind::LSqrBr => Some(TokenKind::RSqrBr),
            _ => None,
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TokenKind::LParen => f.write_str("("),
            TokenKind::RParen => f.write_str(")"),
            TokenKind::LSqrBr => f.write_str("["),
            TokenKind::RSqrBr => f.write_str("]"),
            TokenKind::Integer(i) => write!(f, "{}", i),
            TokenKind::Ident(ref s) => write!(f, "{}", s),
            TokenKind::Eof => f.write_str("eof"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct ExprId(i32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub id: ExprId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    /// An s-expression: something like `(foo bar baz)`.
    List(Vec<Expr>),
    /// An integer literal
    Integer(i64),
    /// An identifer: something like `foo`
    Ident(String),
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExprKind::List(ref exprs) => {
                write!(f, "(")?;
                let mut first = true;
                for expr in exprs {
                    if !first {
                        write!(f, " ")?;
                    }
                    first = false;
                    write!(f, "{}", expr.kind)?;
                }
                write!(f, ")")
            },
            ExprKind::Integer(i) => write!(f, "{}", i),
            ExprKind::Ident(ref s) => write!(f, "{}", s),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnknownChar(Span, char),
    ExpectedFoundToken(Span, String, TokenKind),
}

/// The parser.
#[derive(Debug)]
pub struct Parser<'src> {
    /// The contents of a single source file.
    src: &'src str,
    /// The byte position within the file.
    pos: usize,
    file: FileId,
    
    next_expr_id: i32,
}

impl<'src> Parser<'src> {
    pub fn from_source(src: &'src str, file: FileId) -> Self {
        Parser {
            src: src,
            pos: 0,
            file: file,
            next_expr_id: 0,
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let this_char = self.peek_char()?;
        let char_length = this_char.len_utf8();
        self.pos += char_length;
        Some(this_char)
    }

    fn is_ident_char(c: char) -> bool {
        match c {
            '0' ... '9' | 'a' ... 'z' | 'A' ... 'Z' | '-' | '_' => true,
            _ => false,
        }
    }

    fn span(&self, lo: usize, hi: usize) -> Span {
        Span::new(lo as _, hi as _, self.file)
    }

    fn skip_whitespace(&mut self) {
        loop {
            match self.peek_char() {
                Some(s) if s.is_whitespace() => self.advance(),
                _ => break,
            };
        }
    }

    pub fn parse_token(&mut self) -> Result<Token, ParseError> {
        self.skip_whitespace();

        let lo = self.pos;

        let this_char = self.advance();
        let result = match this_char {
            Some('(') => TokenKind::LParen,
            Some(')') => TokenKind::RParen,
            Some('[') => TokenKind::LSqrBr,
            Some(']') => TokenKind::RSqrBr,
            Some(c) if Self::is_ident_char(c) => {
                let mut string = String::new();
                string.push(c);
                loop {
                    match self.peek_char() {
                        Some(next_char) if Self::is_ident_char(next_char) => {
                            self.advance();
                            string.push(next_char);
                        },
                        _ => break,
                    }
                }
                match string.parse() {
                    Ok(value) => TokenKind::Integer(value),
                    Err(_) => TokenKind::Ident(string),
                }
            },
            Some(c) => {
                let hi = self.pos;
                let span = self.span(lo, hi);
                return Err(ParseError::UnknownChar(span, c))
            },
            None => TokenKind::Eof,
        };
        let hi = self.pos;
        self.skip_whitespace();
        let span = self.span(lo, hi);
        Ok(Token { kind: result, span: span })
    }

    pub fn peek_token(&mut self) -> Result<Token, ParseError> {
        let old_pos = self.pos;
        let res = self.parse_token();
        self.pos = old_pos;
        res
    }

    fn new_expr(&mut self, kind: ExprKind, span: Span) -> Expr {
        let id = ExprId(self.next_expr_id);
        self.next_expr_id += 1;
        Expr {
            kind, span, id
        }
    }

    pub fn is_at_end_of_file(&mut self) -> bool {
        match self.peek_token().map(|x| x.kind) {
            Ok(TokenKind::Eof) => true,
            _ => false,
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        let lo = self.pos;
        let tok = self.parse_token()?;
        let expr_kind = match tok.kind {
            token @ TokenKind::LParen | token @ TokenKind::LSqrBr => {
                let matching_bracket = token.matching_bracket().unwrap();
                let mut exprs = vec![];
                loop {
                    match self.peek_token()? {
                        Token { ref kind, .. } if *kind == matching_bracket => {
                            self.parse_token()?;
                            break
                        },
                        _ => {
                            exprs.push(self.parse_expr()?);
                        }
                    }
                }
                ExprKind::List(exprs)
            },
            TokenKind::Integer(i) => ExprKind::Integer(i),
            TokenKind::Ident(s) => ExprKind::Ident(s),
            token => return Err(ParseError::ExpectedFoundToken(tok.span, "expression".to_string(), token)),
        };
        let hi = self.pos;
        let span = self.span(lo, hi);
        Ok(self.new_expr(expr_kind, span))
    }
}

#[cfg(test)]
mod test {
    #![allow(unreachable_patterns, unused_variables)]
    use super::*;

    macro_rules! match_test {
        ($e:expr; $pat1:pat, $name1:expr; $($pat:pat, $name:expr);*) => {
            match $e {
                $pat1 => match_test!($name1; $($pat, $name);*),
                _ => panic!(),
            }
        };
        ($e: expr; $pat:pat, $name:expr) => {
            match $e {
                $pat => $name,
                _ => panic!(),
            }
        };
    }

    #[test]
    fn test_tokenization() {
        let src = "(foo 1\n\t[2 3a]) define";
        let mut tok = Parser::from_source(src, FileId(0));
        let mut i = 0;
        loop {
            match (i, tok.parse_token().map(|x| x.kind)) {
                (0, Ok(TokenKind::LParen)) => {},
                (1, Ok(TokenKind::Ident(ref s))) if s == "foo" => {},
                (2, Ok(TokenKind::Integer(1))) => {},
                (3, Ok(TokenKind::LSqrBr)) => {},
                (4, Ok(TokenKind::Integer(2))) => {},
                (5, Ok(TokenKind::Ident(ref s))) if s == "3a" => {},
                (6, Ok(TokenKind::RSqrBr)) => {},
                (7, Ok(TokenKind::RParen)) => {},
                (8, Ok(TokenKind::Ident(ref s))) if s == "define" => {},
                (9, Ok(TokenKind::Eof)) => break,
                (i, res) => panic!("unexpected token {}: {:?}", i, res),
            }
            i += 1;
        }
    }

    #[test]
    fn test_parser_matching_square_brackets() {
        let src = "[foo [1 baz]]";
        let mut parser = Parser::from_source(src, FileId(0));
        let actual = parser.parse_expr().unwrap();
        match_test! { actual.kind;
            ExprKind::List(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::List(ref v), v[1].kind;
            ExprKind::List(ref v), v[0].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::List(ref v), v[1].kind;
            ExprKind::List(ref v), v[1].kind;
            ExprKind::Ident(ref s), &**s;
            "baz", ()
        }
    }

    #[test]
    fn test_parser_matching_parentheses() {
        let src = "(foo [1 baz])";
        let mut parser = Parser::from_source(src, FileId(0));
        let actual = parser.parse_expr().unwrap();
        match_test! { actual.kind;
            ExprKind::List(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::List(ref v), v[1].kind;
            ExprKind::List(ref v), v[0].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::List(ref v), v[1].kind;
            ExprKind::List(ref v), v[1].kind;
            ExprKind::Ident(ref s), &**s;
            "baz", ()
        }
    }

    #[test]
    fn test_unmatched_brackets1() {
        let src = "(foo bar]";
        let mut parser = Parser::from_source(src, FileId(0));
        let expected_span = parser.span(8, 9);
        let expected = Err(ParseError::ExpectedFoundToken(expected_span, "expression".to_string(), TokenKind::RSqrBr));
        let actual = parser.parse_expr();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_unmatched_brackets2() {
        let src = "[baz qux)";
        let mut parser = Parser::from_source(src, FileId(0));
        let expected_span = parser.span(8, 9);
        let expected = Err(ParseError::ExpectedFoundToken(expected_span, "expression".to_string(), TokenKind::RParen));
        let actual = parser.parse_expr();
        assert_eq!(actual, expected);
    }
}