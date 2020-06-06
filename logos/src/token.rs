use logos::{self, Logos};
use std::str::from_utf8;
use thiserror::Error;

use rug::{Integer, Rational};

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
pub enum Token {
    // Commands
    #[token(b"declare")]
    Declare,
    #[token(b"define")]
    Define,
    #[token(b"check")]
    Check,
    #[token(b"program")]
    Program,

    // Terms
    #[token(b"type")]
    Type,
    // Function-names
    #[token(b"%")]
    Percent,
    #[token(b"!")]
    Bang,
    #[token(b"@")]
    At,
    #[token(b":")]
    Colon,
    #[token(b"\\")]
    ReverseSolidus,
    #[token(b"^")]
    Caret,
    #[token(b"_")]
    Hole,
    // Program constructs
    #[token(b"let")]
    Let,
    #[token(b"~")]
    Tilde,
    #[token(b"do")]
    Do,
    #[token(b"match")]
    Match,
    #[token(b"default")]
    Default,
    #[token(b"mpz")]
    Mpz,
    #[token(b"mpq")]
    Mpq,
    #[token(b"mp_add")]
    MpAdd,
    #[token(b"mp_neg")]
    MpNeg,
    #[token(b"mp_div")]
    MpDiv,
    #[token(b"mp_mul")]
    MpMul,
    #[token(b"mp_ifneg")]
    MpIfNeg,
    #[token(b"mp_ifzero")]
    MpIfZero,
    #[token(b"mpz_to_mpq")]
    MpzToMpq,
    #[token(b"compare")]
    Compare,
    #[token(b"ifequal")]
    IfEqual,
    #[token(b"fail")]
    Fail,
    #[regex(br"markvar\d*")]
    MarkVar,
    #[regex(br"ifmarked\d*")]
    IfMarked,

    #[token(b"(")]
    Open,
    #[token(b")")]
    Close,

    #[regex(br"[0-9]*")]
    Natural,

    #[regex(br"[0-9]*/[0-9*]")]
    Rational,

    #[regex(br"[^%!@:~\\^()0-9 \t\n\f][^() \t\n\f]*")]
    Ident,

    // Logos requires one token variant to handle errors,
    // it can be named anything you wish.
    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[error]
    // Skip space
    #[regex(br"[ \t\n\f]+", logos::skip)]
    // Skip comments
    #[regex(br";[^\n]*\n", logos::skip)]
    TokenErr,
}

/// A peekable lexer
pub struct Lexer<'a> {
    inner: logos::Lexer<'a, Token>,
    peek: Option<Token>,
    peek_slice: &'a [u8],
}

impl<'a> std::convert::From<logos::Lexer<'a, Token>> for Lexer<'a> {
    fn from(mut inner: logos::Lexer<'a, Token>) -> Self {
        Self {
            peek: inner.next(),
            peek_slice: inner.slice(),
            inner,
        }
    }
}

#[derive(Error, Debug)]
pub enum TokenError {
    #[error("Reach end of file when expecting a token")]
    UnexpectedEof,
    #[error("Expect a {0:?}, but found token `{1:?}`")]
    WrongToken(Token, Token),
    #[error("Expect a {0}, but found token `{1:?}`")]
    UnexpectedToken(&'static str, Token),
}

impl<'a> Lexer<'a> {
    pub fn next(&mut self) -> Option<Token> {
        self.peek_slice = self.inner.slice();
        let n = std::mem::replace(&mut self.peek, self.inner.next());
        //println!(
        //    "Token: {:?}, Slice: {:?}",
        //    n,
        //    from_utf8(self.peek_slice).unwrap()
        //);
        n
    }
    pub fn require_next(&mut self) -> Result<Token, TokenError> {
        self.next().ok_or(TokenError::UnexpectedEof)
    }
    pub fn peek(&self) -> Option<Token> {
        self.peek
    }
    pub fn slice(&self) -> &'a [u8] {
        self.peek_slice
    }
    pub fn str(&self) -> &'a str {
        from_utf8(self.slice()).unwrap()
    }
    pub fn string(&self) -> String {
        self.str().to_owned()
    }
    pub fn nat(&self) -> Integer {
        Integer::from_str_radix(self.str(), 10).unwrap()
    }
    pub fn rat(&self) -> Rational {
        Rational::from_str_radix(self.str(), 10).unwrap()
    }
    pub fn consume_tok(&mut self, t: Token) -> Result<(), TokenError> {
        let f = self.require_next()?;
        if &f == &t {
            Ok(())
        } else {
            Err(TokenError::WrongToken(t, f))
        }
    }
    pub fn consume_ident(&mut self) -> Result<String, TokenError> {
        let t = self.require_next()?;
        if let Token::Ident = t {
            Ok(self.string())
        } else {
            Err(TokenError::WrongToken(Token::Ident, t))
        }
    }
}
