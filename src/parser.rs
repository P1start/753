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
    /// `define`
    Define,
    /// `let`
    Let,
    /// `eval`
    Eval,
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
            TokenKind::Define => f.write_str("define"),
            TokenKind::Let => f.write_str("let"),
            TokenKind::Eval => f.write_str("eval"),
            TokenKind::Integer(i) => write!(f, "{}", i),
            TokenKind::Ident(ref s) => write!(f, "{}", s),
            TokenKind::Eof => f.write_str("eof"),
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
    /// A function definition: something like `(define (foo) bar)`.
    Function(String, Expr),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash)]
pub struct ExprId(i32);

#[derive(Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub id: ExprId,
}

impl Expr {
    pub fn find_toplevel_mut<'a, F, G>(&'a mut self, p: &mut F, action: &mut G)
        where F: FnMut(&Expr) -> bool,
              G: FnMut(&'a mut Expr),
    {
        if p(self) {
            action(self)
        } else {
            match self.kind {
                ExprKind::Call(ref mut exprs) => {
                    for expr in exprs {
                        expr.find_toplevel_mut(p, action);
                    }
                },
                ExprKind::Integer(_) | ExprKind::Ident(_) => {},
                ExprKind::Let(_, ref mut what, ref mut inner) => {
                    what.find_toplevel_mut(p, action);
                    inner.find_toplevel_mut(p, action);
                },
                ExprKind::Eval(ref mut inner) => {
                    inner.find_toplevel_mut(p, action);
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExprKind {
    /// An s-expression: something like `(foo bar baz)`.
    Call(Vec<Expr>),
    /// An integer literal
    Integer(i64),
    /// An identifer
    Ident(String),
    /// A `let` expression: something like `(let [x 1] expr)`
    Let(String, Box<Expr>, Box<Expr>),
    /// `eval`
    Eval(Box<Expr>),
}

impl fmt::Display for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExprKind::Call(ref exprs) => {
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
            ExprKind::Ident(ref s) => write!(f, "{}", s),
            ExprKind::Integer(i) => write!(f, "{}", i),
            ExprKind::Let(ref name, ref what, ref rest) => {
                write!(f, "(let [{} {}] {})", name, what.kind, rest.kind)
            },
            ExprKind::Eval(ref inner) => write!(f, "(eval {})", inner.kind),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
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
        "define" | "let" | "eval" => true,
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
                    Err(_) => {
                        match &*string {
                            "define" => TokenKind::Define,
                            "let" => TokenKind::Let,
                            "eval" => TokenKind::Eval,
                            _ => TokenKind::Ident(string),
                        }
                    },
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
    
    next_expr_id: i32,
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
                Err(err) => return Err(err),
            }
            self.tokenizer.skip_whitespace();
            if let Ok(TokenKind::Eof) = self.tokenizer.peek_token().map(|x| x.kind) {
                break
            }
        }
        Ok(items)
    }

    pub fn parse_item(&mut self) -> Result<Item, ParseError> {
        let lo = self.tokenizer.pos;
        let matching_bracket = self.parse_bracket()?;
        Ok(match self.tokenizer.parse_token()? {
            Token { kind: TokenKind::Define, .. } => {
                let matching_bracket_name = self.parse_bracket()?;
                let define_name = self.parse_ident()?;
                self.expect_token(&matching_bracket_name)?;
                let body = self.parse_expr()?;
                self.expect_token(&matching_bracket)?;
                let kind = ItemKind::Function(define_name, body);
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
                        self.expect_token(&matching_bracket)?;
                        let expr_kind = ExprKind::Let(name, Box::new(value), Box::new(rest));
                        let hi = self.tokenizer.pos;
                        let span = self.tokenizer.span(lo, hi);
                        return Ok(self.new_expr(expr_kind, span))
                    },
                    Token { kind: TokenKind::Eval, .. } => {
                        self.tokenizer.parse_token()?;
                        let inner = self.parse_expr()?;
                        self.expect_token(&matching_bracket)?;
                        let expr_kind = ExprKind::Eval(Box::new(inner));
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
                ExprKind::Call(exprs)
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
        let src = "(foo 1\n\t[2 3a]) define";
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
                (8, Ok(TokenKind::Define)) => {},
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
            ExprKind::Call(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::Call(ref v), v[1].kind;
            ExprKind::Call(ref v), v[0].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::Call(ref v), v[1].kind;
            ExprKind::Call(ref v), v[1].kind;
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
            ExprKind::Call(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "foo", ()
        }
        match_test! { actual.kind;
            ExprKind::Call(ref v), v[1].kind;
            ExprKind::Call(ref v), v[0].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::Call(ref v), v[1].kind;
            ExprKind::Call(ref v), v[1].kind;
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
        let src = "(define (foo) bar]";
        let mut parser = Parser::from_source(src, FileId(0));
        let expected_span = parser.tokenizer.span(17, 18);
        let expected = Err(ParseError::ExpectedFoundToken(expected_span, "`)`".to_string(), TokenKind::RSqrBr));
        let actual = parser.parse_item();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_definition() {
        let src = "(define (foo) bar)";
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
            ExprKind::Call(ref v), v[0].kind;
            ExprKind::Ident(ref s), &**s;
            "add", ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, ref to, _), to.kind;
            ExprKind::Call(ref v), v[1].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, ref to, _), to.kind;
            ExprKind::Call(ref v), v[2].kind;
            ExprKind::Integer(1), ()
        }
        match_test! { actual.kind;
            ExprKind::Let(_, _, ref rest), rest.kind;
            ExprKind::Ident(ref s), &**s;
            "bar", ()
        }
    }

    #[test]
    fn test_eval() {
        let src = "(eval 1)";
        let mut parser = Parser::from_source(src, FileId(0));
        let actual = parser.parse_expr().unwrap();
        match_test! { actual.kind;
            ExprKind::Eval(ref inner), inner.kind;
            ExprKind::Integer(1), ()
        }
    }

    #[test]
    fn test_parse_items() {
        let src = "(define (foo) 0)(define (bar) 1) \n\n";
        let mut parser = Parser::from_source(src, FileId(0));
        let actual = parser.parse_items().unwrap();
        assert_eq!(actual.len(), 2);
    }
}