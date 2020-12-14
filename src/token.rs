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
    // Aliases
    #[token(b"Forall")]
    Forall,
    #[token(b"provided")]
    Provided,
    #[token(b"lam")]
    Lam,
    // Proper extensions
    #[token(b"->")]
    Arrow,
    #[token(b"declare-rule")]
    DeclareRule,
    #[token(b"declare-type")]
    DeclareType,
    #[token(b"define-const")]
    DefineConst,
    #[token(b"check-assuming")]
    CheckAssuming,

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
    fn next(&mut self) -> Result<Option<SpanTok<'a>>, LfscError>;
    fn peek(&self) -> Option<SpanTok<'a>>;
    fn path(&self) -> &PathBuf;
    fn bytes(&self) -> &'a [u8];

    fn require_next(&mut self) -> Result<SpanTok<'a>, LfscError> {
        self.next()?.ok_or(LfscError::UnexpectedEof)
    }
    fn peek_token(&self) -> Option<Token> {
        self.peek().map(|r| r.tok)
    }
    fn consume_tok(&mut self, t: Token) -> Result<SpanTok<'a>, LfscError> {
        let f = self.require_next()?;
        if &f.tok == &t {
            Ok(f)
        } else {
            Err(LfscError::WrongToken(t, f.tok))
        }
    }
    fn consume_ident(&mut self) -> Result<&'a str, LfscError> {
        Ok(self.consume_tok(Token::Ident)?.str())
    }
    fn current_line(&self) -> (&'a str, Position) {
        self.line_of(
            self.peek()
                .map(|s| s.span.start)
                .unwrap_or_else(|| self.bytes().len() - 1),
        )
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
    peek: Option<SpanTok<'a>>,
    filename: PathBuf,
}

/// The position of a token
pub struct Position {
    pub line_no: usize,
    pub col_no: usize,
    pub path: PathBuf,
}

impl<'a> LogosLexer<'a> {
    fn inner_next(&mut self) -> Option<SpanTok<'a>> {
        let next = self.inner.next();
        let slice = self.inner.slice();
        let span = self.inner.span();
        next.map(|n| SpanTok::new(n, slice, span))
    }
}

impl<'a> Lexer<'a> for LogosLexer<'a> {
    fn new(bytes: &'a [u8], filename: PathBuf) -> Self {
        let inner = Token::lexer(bytes);
        let mut this = Self {
            peek: None,
            inner,
            bytes,
            filename,
        };
        this.peek = this.inner_next();
        this
    }
    fn next(&mut self) -> Result<Option<SpanTok<'a>>, LfscError> {
        let nxt_peek = self.inner_next();
        let old_peek = std::mem::replace(&mut self.peek, nxt_peek);
        // if let Some(n) = &old_peek {
        //     println!(
        //         "Token: {:?}, Slice: {:?}",
        //         n.tok,
        //         from_utf8(n.slice).unwrap()
        //     );
        // }
        Ok(old_peek)
    }
    fn peek(&self) -> Option<SpanTok<'a>> {
        self.peek.clone()
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
/// It performs one kinds of expansion: substitutions
///
/// ## Substitutions
///
/// These are simple enough. One token is taken is replaced by another. They are:
///    * `provided` with `^`
///    * `has-proof` with `:`
///    * `lam` with `\`
///    * `Forall` with `!`
///    * `let` with `@`
pub struct DesugaringLexer<'a> {
    inner: LogosLexer<'a>,
    // To be outputted
    out: VecDeque<SpanTok<'a>>,
}

#[derive(Debug)]
struct Level<'a> {
    n_children: usize,
    in_var_list: bool,
    // The head of the level.
    // The outer option captures that is may not be set.
    // The inner option captures that it may not exist.
    head: Option<Option<SpanTok<'a>>>,
    // Tokens to emit *before* closing the level.
    closing: Vec<SpanTok<'a>>,
}

/// Spanned token.
#[derive(Debug, Clone)]
pub struct SpanTok<'a> {
    pub tok: Token,
    pub slice: &'a [u8],
    pub span: Range<usize>,
}
impl<'a> SpanTok<'a> {
    pub fn new(tok: Token, slice: &'a [u8], span: Range<usize>) -> Self {
        SpanTok { tok, slice, span }
    }
    pub fn str(&self) -> &'a str {
        from_utf8(self.slice).unwrap()
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
}

impl<'a> DesugaringLexer<'a> {
    fn pull(&mut self) -> Result<(), LfscError> {
        while self.out.len() == 0 {
            if let Some(t) = self.inner.next()? {
                // Implement token substitutions
                let subbed_tok = match t.tok {
                    Token::Provided => Token::Caret,
                    Token::Lam => Token::ReverseSolidus,
                    Token::Let => Token::At,
                    Token::Forall => Token::Bang,
                    _ => t.tok,
                };
                let subbed_t = SpanTok::new(subbed_tok, t.slice, t.span);
                self.out.push_back(subbed_t);
            } else {
                return Ok(());
            }
        }
        Ok(())
    }
}

impl<'a> Lexer<'a> for DesugaringLexer<'a> {
    fn new(bytes: &'a [u8], filename: PathBuf) -> Self {
        let inner = LogosLexer::new(bytes, filename);
        DesugaringLexer {
            inner,
            out: VecDeque::new(),
        }
    }
    fn next(&mut self) -> Result<Option<SpanTok<'a>>, LfscError> {
        self.pull()?;
        let t = self.out.pop_front();
        // if let Some(t) = &t {
        //     println!(
        //         "Token: {:?}, Slice: {:?}",
        //         t.tok,
        //         from_utf8(t.slice).unwrap()
        //     );
        // }
        self.pull()?;
        Ok(t)
    }
    fn peek(&self) -> Option<SpanTok<'a>> {
        self.out.front().cloned()
    }
    fn bytes(&self) -> &'a [u8] {
        self.inner.bytes()
    }
    fn path(&self) -> &PathBuf {
        self.inner.path()
    }
}
