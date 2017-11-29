use std::fmt;

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LSqrBr,
    /// `]`
    RSqrBr,
    /// `defun`
    Defun,
    /// `let`
    Let,
    /// An integer (e.g., `-137`)
    Integer(i64), // TODO is it right to use i64 here?
    /// An identifier (e.g., `foo`)
    Ident(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Token::LParen => f.write_str("("),
            Token::RParen => f.write_str(")"),
            Token::LSqrBr => f.write_str("["),
            Token::RSqrBr => f.write_str("]"),
            Token::Defun => f.write_str("defun"),
            Token::Let => f.write_str("let"),
            Token::Integer(i) => write!(f, "{}", i),
            Token::Ident(ref s) => write!(f, "{}", s),
        }
    }
}

/// A top-level item. These visually look like expressions but are treated differently and
/// so warrant their own type.
#[derive(Debug, PartialEq, Eq)]
pub enum Item {
    /// A function definition: something like `(defun foo bar)`.
    Function(String, Expr),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    /// An s-expression: something like `(foo bar baz)`.
    SExpr(Vec<Expr>),
    /// A square-bracketed s-expression: something like `[foo bar baz qux]`
    SqExpr(Vec<Expr>),
    /// An integer literal
    Integer(i64),
    /// An identifer
    Ident(String),
    /// A `let` expression: something like `(let [x 1] expr)`
    Let(String, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub struct Ast {
    pub declarations: Vec<Expr>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    EndOfFile,
    UnknownChar(char),
    ExpectedFoundToken(String, Token),
}

/// The tokenizer: the part of the parsing pipeline that breaks up source code into `Token`s.
#[derive(Copy, Clone, Debug)]
pub struct Tokenizer<'src> {
    /// The contents of a single source file.
    src: &'src str,
}

pub fn is_keyword(s: &str) -> bool {
    match s {
        "defun" | "let" => true,
        _ => false,
    }
}

impl<'src> Tokenizer<'src> {
    pub fn from_source(src: &'src str) -> Self {
        Tokenizer {
            src: src,
        }
    }

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

    pub fn parse_token(&mut self) -> Result<Token, ParseError> {
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
                    Ok(value) => return Ok(Token::Integer(value)),
                    Err(_) => {},
                }
                match &*string {
                    "defun" => Token::Defun,
                    "let" => Token::Let,
                    _ => Token::Ident(string),
                }
            },
            c => return Err(ParseError::UnknownChar(c)),
        })
    }

    pub fn peek_token(&mut self) -> Result<Token, ParseError> {
        let old_src = self.src;
        let res = self.parse_token();
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

impl<'src> Parser<'src> {
    pub fn from_source(src: &'src str) -> Self {
        Parser {
            tokenizer: Tokenizer::from_source(src),
        }
    }

    fn parse_ident(&mut self) -> Result<String, ParseError> {
        match self.tokenizer.parse_token()? {
            Token::Ident(s) => Ok(s),
            tok => Err(ParseError::ExpectedFoundToken("identifier".to_string(), tok)),
        }
    }

    fn expect_token(&mut self, token: Token) -> Result<(), ParseError> {
        let actual = self.tokenizer.parse_token()?;
        if actual == token {
            Ok(())
        } else {
            Err(ParseError::ExpectedFoundToken(format!("`{}`", token), actual))
        }
    }

    pub fn parse_item(&mut self) -> Result<Item, ParseError> {
        self.expect_token(Token::LParen)?;
        Ok(match self.tokenizer.peek_token()? {
            Token::Defun => {
                self.tokenizer.parse_token()?;
                let defun_name = self.parse_ident()?;
                let body = self.parse_expr()?;
                self.expect_token(Token::RParen)?;
                Item::Function(defun_name, body)
            },
            tok => return Err(ParseError::ExpectedFoundToken("function declaration".to_string(), tok)),
        })
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        let token = self.tokenizer.parse_token()?;
        Ok(match token {
            Token::LParen => {
                match self.tokenizer.peek_token()? {
                    Token::Let => {
                        self.tokenizer.parse_token()?;
                        self.expect_token(Token::LSqrBr)?;
                        // TODO: support more than one name-value assignment
                        let name = self.parse_ident()?;
                        let value = self.parse_expr()?;
                        self.expect_token(Token::RSqrBr)?;
                        let rest = self.parse_expr()?;
                        return Ok(Expr::Let(name, Box::new(value), Box::new(rest)))
                    },
                    _ => {},
                }
                let mut exprs = vec![];
                loop {
                    let next_token = self.tokenizer.peek_token()?;
                    match next_token {
                        Token::RParen => {
                            self.tokenizer.parse_token()?;
                            break
                        },
                        _ => {
                            exprs.push(self.parse_expr()?);
                        }
                    }
                }
                Expr::SExpr(exprs)
            },
            Token::LSqrBr => {
                let mut exprs = vec![];
                loop {
                    let next_token = self.tokenizer.peek_token()?;
                    match next_token {
                        Token::RSqrBr => {
                            self.tokenizer.parse_token()?;
                            break
                        },
                        _ => {
                            exprs.push(self.parse_expr()?);
                        },
                    }
                }
                Expr::SqExpr(exprs)
            },
            Token::Integer(i) => Expr::Integer(i),
            Token::Ident(s) => Expr::Ident(s),
            token => return Err(ParseError::ExpectedFoundToken("expression".to_string(), token)),
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_tokenizer() {
        let src = "(foo 1\n\t[2 3a])";
        let mut tok = Tokenizer::from_source(src);
        let mut i = 0;
        loop {
            match (i, tok.parse_token()) {
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

    #[test]
    fn test_parser_sqexprs() {
        let src = "[foo [1 baz]]";
        let mut parser = Parser::from_source(src);
        let expected = Ok(Expr::SqExpr(vec![
            Expr::Ident("foo".to_string()),
            Expr::SqExpr(vec![
                Expr::Integer(1),
                Expr::Ident("baz".to_string()),
            ]),
        ]));
        let actual = parser.parse_expr();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_parser_sexprs() {
        let src = "(foo (bar baz)qux)";
        let mut parser = Parser::from_source(src);
        let expected = Ok(Expr::SExpr(
            vec![
                Expr::Ident("foo".to_string()),
                Expr::SExpr(
                    vec![
                        Expr::Ident("bar".to_string()),
                        Expr::Ident("baz".to_string()),
                    ],
                ),
                Expr::Ident("qux".to_string()),
            ],
        ));
        let actual= parser.parse_expr();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_definition() {
        let src = "(defun foo bar)";
        let mut parser = Parser::from_source(src);
        let expected = Ok(Item::Function(
            "foo".to_string(),
            Expr::Ident("bar".to_string()),
        ));
        let actual = parser.parse_item();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_let() {
        let src = "(let [foo (add 1 1)] bar)";
        let mut parser = Parser::from_source(src);
        let expected = Ok(Expr::Let(
            "foo".to_string(),
            Box::new(Expr::SExpr(vec![
                Expr::Ident("add".to_string()),
                Expr::Integer(1),
                Expr::Integer(1),
            ])),
            Box::new(Expr::Ident("bar".to_string())),
        ));
        let actual = parser.parse_expr();
        assert_eq!(actual, expected);
    }
}