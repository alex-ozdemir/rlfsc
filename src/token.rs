use std::collections::VecDeque;
use std::ops::Range;
use std::path::PathBuf;
use std::str::from_utf8;

use crate::error::LfscError;

use logos::{self, Logos};
use rug::{Integer, Rational};

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
pub enum Token {
    // Commands
    #[token(b"declare")]
    Declare,
    #[token(b"opaque")]
    Opaque,
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
    #[token(b"#")]
    Pound,
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

    // Extension tokens
    #[token(b"id")]
    Id,
    #[token(b"->")]
    Arrow,
    #[token(b"Forall")]
    Forall,
    #[token(b"declare-rule")]
    DeclareRule,
    #[token(b"declare-type")]
    DeclareType,
    #[token(b"provided")]
    Provided,
    #[token(b"has-proof")]
    HasProof,
    #[token(b"assuming")]
    Assuming,

    #[regex(br"[^%!@:~\\^()0-9 \t\n\f][^() \t\n\f;]*")]
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

pub trait Lexer<'a> {
    fn new(bytes: &'a [u8], path: PathBuf) -> Self;
    fn next(&mut self) -> Option<Token>;
    fn peek(&self) -> Option<Token>;
    fn slice(&self) -> &'a [u8];
    fn span(&self) -> Range<usize>;
    fn path(&self) -> &PathBuf;
    fn bytes(&self) -> &'a [u8];

    fn require_next(&mut self) -> Result<Token, LfscError> {
        self.next().ok_or(LfscError::UnexpectedEof)
    }
    fn str(&self) -> &'a str {
        from_utf8(self.slice()).unwrap()
    }
    fn string(&self) -> String {
        self.str().to_owned()
    }
    fn nat(&self) -> Integer {
        Integer::from_str_radix(self.str(), 10).unwrap()
    }
    fn rat(&self) -> Rational {
        Rational::from_str_radix(self.str(), 10).unwrap()
    }
    fn consume_tok(&mut self, t: Token) -> Result<(), LfscError> {
        let f = self.require_next()?;
        if &f == &t {
            Ok(())
        } else {
            Err(LfscError::WrongToken(t, f))
        }
    }
    fn consume_ident(&mut self) -> Result<&'a str, LfscError> {
        let t = self.require_next()?;
        if let Token::Ident = t {
            Ok(self.str())
        } else {
            Err(LfscError::WrongToken(Token::Ident, t))
        }
    }
    fn current_line(&self) -> (&'a str, Position) {
        self.line_of(self.span().start)
    }
    /// For a given byte number, returns the line and the line number it lies in.
    fn line_of(&self, n: usize) -> (&'a str, Position) {
        let line_start = self.bytes()[..n]
            .iter()
            .rposition(|b| *b == b'\n')
            .map(|i| i + 1)
            .unwrap_or(0);
        let line_end = self.bytes()[n..]
            .iter()
            .position(|b| *b == b'\n')
            .map(|i| i + n)
            .unwrap_or(self.bytes().len());
        let col_no = n - line_start + 1;
        let line_no = self.bytes()[..line_start]
            .iter()
            .filter(|b| **b == b'\n')
            .count()
            + 1;
        (
            from_utf8(&self.bytes()[line_start..line_end]).unwrap(),
            Position {
                col_no,
                line_no,
                path: self.path().clone(),
            },
        )
    }
}

/// A peekable lexer
pub struct LogosLexer<'a> {
    inner: logos::Lexer<'a, Token>,
    bytes: &'a [u8],
    peek: Option<Token>,
    peek_slice: &'a [u8],
    filename: PathBuf,
}

/// The position of a token
pub struct Position {
    pub line_no: usize,
    pub col_no: usize,
    pub path: PathBuf,
}

impl<'a> Lexer<'a> for LogosLexer<'a> {
    fn new(bytes: &'a [u8], filename: PathBuf) -> Self {
        let mut inner = Token::lexer(bytes);
        Self {
            peek: inner.next(),
            peek_slice: inner.slice(),
            inner,
            bytes,
            filename,
        }
    }
    fn next(&mut self) -> Option<Token> {
        self.peek_slice = self.inner.slice();
        let n = std::mem::replace(&mut self.peek, self.inner.next());
        //println!(
        //    "Token: {:?}, Slice: {:?}",
        //    n,
        //    from_utf8(self.peek_slice).unwrap()
        //);
        n
    }
    fn peek(&self) -> Option<Token> {
        self.peek
    }
    fn slice(&self) -> &'a [u8] {
        self.peek_slice
    }
    fn span(&self) -> Range<usize> {
        self.inner.span()
    }
    fn bytes(&self) -> &'a [u8] {
        self.bytes
    }
    fn path(&self) -> &PathBuf {
        &self.filename
    }
}

/// # Overview
///
/// `DesugaringLexer` implements a streaming macro-expander of shorts.
///
/// It performs two kinds of expansions: substitutions and de-variadification.
///
/// ## Substitutions
///
/// These are simple enough. One token is taken is replaced by another. They are:
///    * `provided` with `^`
///    * `has-proof` with `:`
///    * `assuming` with `%`
///    * `Forall` with `!`
///
/// ## De-variadification
///
/// This is a more complex process. The idea is to replace certain variadic forms with non-variadic
/// forms. Each variadic form is indicated with a head keyword. The keywords are
///    * `->`
///    * `declare-rule`
///    * `declare-type`
///
/// The first is a *term* form. The latter two are *command* forms.
///
/// Let's give examples of the use of each, and their expansions:
///
///    * `(-> (a (id i b)) (k a i))` to `(! _ a (! i b (k a i)))`
///    * `(declare-rule and_pf ((id a bool) (id b bool) (holds a) (holds b)) (holds (and a b)))` to 
///      `(declare and_pf (! a bool (! b bool (! _ (holds a ) (! _ (holds b) (holds (and a b)))))))`.
///
/// (_ denotes an arbitrary name)
///
pub struct DesugaringLexer<'a> {
    inner: LogosLexer<'a>,
    out: VecDeque<(Token, &'a[u8], Range<usize>)>,
}

impl<'a> DesugaringLexer<'a> {
    fn pull(&mut self) {
        if self.out.len() == 0 {
            self.inner.peek().map(|t| {
                // Implement token substitutions
                let subbed_t = match t {
                    Token::Provided => Token::Caret,
                    Token::Assuming => Token::Percent,
                    Token::Forall => Token::Bang,
                    Token::HasProof => Token::Colon,
                    t => t,
                };
                self.out.push_back((subbed_t, self.inner.slice(), self.inner.span()));
                self.inner.next();
            });
        }
    }
}

impl<'a> Lexer<'a> for DesugaringLexer<'a> {
    fn new(bytes: &'a [u8], filename: PathBuf) -> Self {
        let inner = LogosLexer::new(bytes, filename);
        DesugaringLexer { inner, out: VecDeque::new() }
    }
    fn next(&mut self) -> Option<Token> {
        self.pull();
        let t = self.out.pop_front().map(|(a, _, _)| a);
        self.pull();
        t
    }
    fn peek(&self) -> Option<Token> {
        self.out.front().map(|(a, _, _)| a.clone())
    }
    fn slice(&self) -> &'a [u8] {
        self.out.front().map(|(_, a, _)| a.clone()).unwrap_or(&b""[..])
    }
    fn span(&self) -> Range<usize> {
        self.out.front().map(|(_, _, a)| a.clone()).expect("Missing range")
    }
    fn bytes(&self) -> &'a [u8] {
        self.inner.bytes()
    }
    fn path(&self) -> &PathBuf {
        self.inner.path()
    }
}
