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
    /// `defun`
    Defun,
    /// `let`
    Let,
    /// An integer (e.g., `-137`)
    Integer(i64), // TODO is it right to use i64 here?
    /// An identifier (e.g., `foo`)
    Ident(String),
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
            TokenKind::Defun => f.write_str("defun"),
            TokenKind::Let => f.write_str("let"),
            TokenKind::Integer(i) => write!(f, "{}", i),
            TokenKind::Ident(ref s) => write!(f, "{}", s),
        }
    }
}

/// A top-level item. These visually look like expressions but are treated differently and
/// so warrant their own type.
#[derive(Debug, PartialEq, Eq)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

impl Item {
    pub fn get_base_name(&self) -> &str {
        match self.kind {
            ItemKind::Function(ref s, _) => s,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ItemKind {
    /// A function definition: something like `(defun foo bar)`.
    Function(String, Expr),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct ExprId(u32);

#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub id: ExprId,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind {
    /// An s-expression: something like `(foo bar baz)`.
    SExpr(Vec<Expr>),
    /// An integer literal
    Integer(i64),
    /// An identifer
    Ident(String),
    /// A `let` expression: something like `(let [x 1] expr)`
    Let(String, Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    EndOfFile(Span),
    UnknownChar(Span, char),
    ExpectedFoundToken(Span, String, TokenKind),
}

/// The tokenizer: the part of the parsing pipeline that breaks up source code into `TokenKind`s.
#[derive(Copy, Clone, Debug)]
pub struct Tokenizer<'src> {
    /// The contents of a single source file.
    src: &'src str,
    /// The byte position within the file.
    pos: usize,
    file: FileId,
}

pub fn is_keyword(s: &str) -> bool {
    match s {
        "defun" | "let" => true,
        _ => false,
    }
}

impl<'src> Tokenizer<'src> {
    pub fn from_source(src: &'src str, file: FileId) -> Self {
        Tokenizer {
            src: src,
            pos: 0,
            file: file,
        }
    }

    fn peek_char(&mut self) -> Result<char, ParseError> {
        self.src[self.pos..].chars().next().ok_or_else(|| {
            let span = self.span(self.pos, self.pos);
            ParseError::EndOfFile(span)
        })
    }

    fn advance(&mut self) -> Result<char, ParseError> {
        let this_char = self.peek_char()?;
        let char_length = this_char.len_utf8();
        self.pos += char_length;
        Ok(this_char)
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

    pub fn parse_token(&mut self) -> Result<Token, ParseError> {
        // Skip whitespace
        loop {
            match self.peek_char() {
                Ok(s) if s.is_whitespace() => self.advance()?,
                _ => break,
            };
        }

        let lo = self.pos;

        let this_char = self.advance()?;
        let result = match this_char {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::LSqrBr,
            ']' => TokenKind::RSqrBr,
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
                    Ok(value) => TokenKind::Integer(value),
                    Err(_) => {
                        match &*string {
                            "defun" => TokenKind::Defun,
                            "let" => TokenKind::Let,
                            _ => TokenKind::Ident(string),
                        }
                    },
                }
            },
            c => {
                let hi = self.pos;
                let span = self.span(lo, hi);
                return Err(ParseError::UnknownChar(span, c))
            },
        };
        let hi = self.pos;
        let span = self.span(lo, hi);
        Ok(Token { kind: result, span: span })
    }

    pub fn peek_token(&mut self) -> Result<Token, ParseError> {
        let old_pos = self.pos;
        let res = self.parse_token();
        self.pos = old_pos;
        res
    }
}

/// The parser.
#[derive(Debug)]
pub struct Parser<'src> {
    /// The tokenizer.
    tokenizer: Tokenizer<'src>,
    
    next_expr_id: u32,
}

impl<'src> Parser<'src> {
    pub fn from_source(src: &'src str, file: FileId) -> Self {
        Parser {
            tokenizer: Tokenizer::from_source(src, file),
            next_expr_id: 0,
        }
    }

    fn new_expr(&mut self, kind: ExprKind, span: Span) -> Expr {
        let id = ExprId(self.next_expr_id);
        self.next_expr_id += 1;
        Expr {
            kind, span, id
        }
    }

    fn parse_ident(&mut self) -> Result<String, ParseError> {
        match self.tokenizer.parse_token()? {
            Token { kind: TokenKind::Ident(s), .. } => Ok(s),
            Token { kind, span } => Err(ParseError::ExpectedFoundToken(span, "identifier".to_string(), kind)),
        }
    }

    fn expect_token(&mut self, token: &TokenKind) -> Result<Span, ParseError> {
        let Token { kind: actual, span } = self.tokenizer.parse_token()?;
        if actual == *token {
            Ok(span)
        } else {
            Err(ParseError::ExpectedFoundToken(span, format!("`{}`", token), actual))
        }
    }

    pub fn parse_items(&mut self) -> Result<Vec<Item>, ParseError> {
        let mut items = vec![];
        loop {
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(ParseError::EndOfFile(_)) => break,
                Err(err) => return Err(err),
            }
        }
        Ok(items)
    }

    pub fn parse_item(&mut self) -> Result<Item, ParseError> {
        let lo = self.tokenizer.pos;
        let matching_bracket = self.parse_bracket()?;
        Ok(match self.tokenizer.peek_token()? {
            Token { kind: TokenKind::Defun, .. } => {
                self.tokenizer.parse_token()?;
                let defun_name = self.parse_ident()?;
                let body = self.parse_expr()?;
                self.expect_token(&matching_bracket)?;
                let kind = ItemKind::Function(defun_name, body);
                let hi = self.tokenizer.pos;
                let span = self.tokenizer.span(lo, hi);
                Item { kind, span }
            },
            Token { kind, span } => return Err(ParseError::ExpectedFoundToken(span, "function declaration".to_string(), kind)),
        })
    }

    fn parse_bracket(&mut self) -> Result<TokenKind, ParseError> {
        let token = self.tokenizer.parse_token()?;
        match (token.kind, token.span) {
            (tok @ TokenKind::LParen, _) | (tok @ TokenKind::LSqrBr, _) => {
                Ok(tok.matching_bracket().unwrap())
            },
            (tok, span) => Err(ParseError::ExpectedFoundToken(span, "`(` or `[`".to_string(), tok)),
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        let lo = self.tokenizer.pos;
        let tok = self.tokenizer.parse_token()?;
        let expr_kind = match tok.kind {
            token @ TokenKind::LParen | token @ TokenKind::LSqrBr => {
                let matching_bracket = token.matching_bracket().unwrap();
                match self.tokenizer.peek_token()? {
                    Token { kind: TokenKind::Let, .. } => {
                        self.tokenizer.parse_token()?;
                        let matching_bracket_inner = self.parse_bracket()?;
                        // TODO: support more than one name-value assignment
                        let name = self.parse_ident()?;
                        let value = self.parse_expr()?;
                        self.expect_token(&matching_bracket_inner)?;
                        let rest = self.parse_expr()?;
                        let expr_kind = ExprKind::Let(name, Box::new(value), Box::new(rest));
                        let hi = self.tokenizer.pos;
                        let span = self.tokenizer.span(lo, hi);
                        return Ok(self.new_expr(expr_kind, span))
                    },
                    _ => {},
                }
                let mut exprs = vec![];
                loop {
                    match self.tokenizer.peek_token()? {
                        Token { ref kind, .. } if *kind == matching_bracket => {
                            self.tokenizer.parse_token()?;
                            break
                        },
                        _ => {
                            exprs.push(self.parse_expr()?);
                        }
                    }
                }
                ExprKind::SExpr(exprs)
            },
            TokenKind::Integer(i) => ExprKind::Integer(i),
            TokenKind::Ident(s) => ExprKind::Ident(s),
            token => return Err(ParseError::ExpectedFoundToken(tok.span, "expression".to_string(), token)),
        };
        let hi = self.tokenizer.pos;
        let span = self.tokenizer.span(lo, hi);
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
    fn test_tokenizer() {
        let src = "(foo 1\n\t[2 3a]) defun";
        let mut tok = Tokenizer::from_source(src, FileId(0));
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
                (8, Ok(TokenKind::Defun)) => {},
                (9, Err(ParseError::EndOfFile(_))) => break,
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
            ExprKind::SExpr(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::SExpr(ref v), v[1].kind;
            ExprKind::SExpr(ref v), v[0].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::SExpr(ref v), v[1].kind;
            ExprKind::SExpr(ref v), v[1].kind;
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
            ExprKind::SExpr(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::SExpr(ref v), v[1].kind;
            ExprKind::SExpr(ref v), v[0].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::SExpr(ref v), v[1].kind;
            ExprKind::SExpr(ref v), v[1].kind;
            ExprKind::Ident(ref s), &**s;
            "baz", ()
        }
    }

    #[test]
    fn test_unmatched_brackets1() {
        let src = "(foo bar]";
        let mut parser = Parser::from_source(src, FileId(0));
        let expected_span = parser.tokenizer.span(8, 9);
        let expected = Err(ParseError::ExpectedFoundToken(expected_span, "expression".to_string(), TokenKind::RSqrBr));
        let actual = parser.parse_expr();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_unmatched_brackets2() {
        let src = "[baz qux)";
        let mut parser = Parser::from_source(src, FileId(0));
        let expected_span = parser.tokenizer.span(8, 9);
        let expected = Err(ParseError::ExpectedFoundToken(expected_span, "expression".to_string(), TokenKind::RParen));
        let actual = parser.parse_expr();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_unmatched_brackets3() {
        let src = "(defun foo bar]";
        let mut parser = Parser::from_source(src, FileId(0));
        let expected_span = parser.tokenizer.span(14, 15);
        let expected = Err(ParseError::ExpectedFoundToken(expected_span, "`)`".to_string(), TokenKind::RSqrBr));
        let actual = parser.parse_item();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_definition() {
        let src = "(defun foo bar)";
        let mut parser = Parser::from_source(src, FileId(0));
        let actual = parser.parse_item().unwrap();
        match_test! { actual.kind;
            ItemKind::Function(ref name, ref body), &**name;
            "foo", ()
        }
        match_test! { actual.kind;
            ItemKind::Function(ref name, ref body), body.kind;
            ExprKind::Ident(ref s), &**s;
            "bar", ()
        }
    }

    #[test]
    fn test_let() {
        let src = "(let [foo (add 1 1)] bar)";
        let mut parser = Parser::from_source(src, FileId(0));
        let actual = parser.parse_expr().unwrap();
        match_test! { actual.kind;
            ExprKind::Let(ref name, _, _), &**name;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, ref to, _), to.kind;
            ExprKind::SExpr(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "add", ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, ref to, _), to.kind;
            ExprKind::SExpr(ref v), v[1].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, ref to, _), to.kind;
            ExprKind::SExpr(ref v), v[2].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, _, ref rest), rest.kind;
            ExprKind::Ident(ref s), &**s;
            "bar", ()
        }
    }
}