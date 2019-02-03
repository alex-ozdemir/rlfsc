#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(iter_unfold)]
extern crate bytes;
extern crate tokio;
extern crate ux;

use bytes::{BufMut, BytesMut};
use tokio::codec::{Decoder, Encoder, FramedRead};
use tokio::prelude::*;
use ux::u5;

use std::collections::BTreeMap;
use std::convert::From;
use std::error::Error;
use std::fmt::Display;
use std::io;
use std::iter::Peekable;
use std::str::FromStr;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum LfscKeyword {
    Declare,
    Define,
    Type,
    Check,
    Percent,
    Caret,
    Bang,
    At,
    Let,
    Colon,
    Tilde,
    Solidus,
    ReverseSolidus,
    Do,
    Match,
    MpAdd,
    MpNeg,
    MpDiv,
    MpMul,
    MpIfNeg,
    MpIfZero,
    IfEqual,
    Compare,
    Fail,
    MarkVar(u5),
    IfMarked(u5),
}

impl Display for LfscKeyword {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            LfscKeyword::Declare => write!(f, "declare"),
            LfscKeyword::Define => write!(f, "define"),
            LfscKeyword::Type => write!(f, "type"),
            LfscKeyword::Check => write!(f, "check"),
            LfscKeyword::Percent => write!(f, "%"),
            LfscKeyword::Caret => write!(f, "^"),
            LfscKeyword::Bang => write!(f, "!"),
            LfscKeyword::At => write!(f, "@"),
            LfscKeyword::Let => write!(f, "let"),
            LfscKeyword::Colon => write!(f, ":"),
            LfscKeyword::Tilde => write!(f, "~"),
            LfscKeyword::Solidus => write!(f, "/"),
            LfscKeyword::ReverseSolidus => write!(f, "\\"),
            LfscKeyword::Do => write!(f, "do"),
            LfscKeyword::Match => write!(f, "match"),
            LfscKeyword::MpAdd => write!(f, "mp_add"),
            LfscKeyword::MpNeg => write!(f, "mp_neg"),
            LfscKeyword::MpDiv => write!(f, "mp_div"),
            LfscKeyword::MpMul => write!(f, "mp_mul"),
            LfscKeyword::MpIfNeg => write!(f, "mp_ifneg"),
            LfscKeyword::MpIfZero => write!(f, "mp_ifzero"),
            LfscKeyword::IfEqual => write!(f, "ifequal"),
            LfscKeyword::Compare => write!(f, "compare"),
            LfscKeyword::Fail => write!(f, "fail"),
            LfscKeyword::IfMarked(u) => write!(f, "ifmarked{}", u16::from(u) + 1),
            LfscKeyword::MarkVar(u) => write!(f, "markvar{}", u16::from(u) + 1),
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
enum LispToken {
    Open,
    Close,
    Ident(String),
    Keyword(LfscKeyword),
}

impl std::fmt::Display for LispToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            LispToken::Open => write!(f, "("),
            LispToken::Close => write!(f, ")"),
            LispToken::Ident(s) => write!(f, "{}", s),
            LispToken::Keyword(k) => write!(f, "{}", k),
        }
    }
}

impl LispToken {
    /// Given a slice of non-grouping, non-whitespace characters, parses a LispToken
    fn from_ident(ident: &[u8]) -> Result<Self, io::Error> {
        Ok(match ident {
            b"declare" => LispToken::Keyword(LfscKeyword::Declare),
            b"define" => LispToken::Keyword(LfscKeyword::Define),
            b"type" => LispToken::Keyword(LfscKeyword::Type),
            b"check" => LispToken::Keyword(LfscKeyword::Check),
            b"%" => LispToken::Keyword(LfscKeyword::Percent),
            b"^" => LispToken::Keyword(LfscKeyword::Caret),
            b"!" => LispToken::Keyword(LfscKeyword::Bang),
            b"@" => LispToken::Keyword(LfscKeyword::At),
            b"let" => LispToken::Keyword(LfscKeyword::Let),
            b":" => LispToken::Keyword(LfscKeyword::Colon),
            b"~" => LispToken::Keyword(LfscKeyword::Tilde),
            b"/" => LispToken::Keyword(LfscKeyword::Solidus),
            b"\\" => LispToken::Keyword(LfscKeyword::ReverseSolidus),
            b"do" => LispToken::Keyword(LfscKeyword::Do),
            b"match" => LispToken::Keyword(LfscKeyword::Match),
            b"mp_add" => LispToken::Keyword(LfscKeyword::MpAdd),
            b"mp_neg" => LispToken::Keyword(LfscKeyword::MpNeg),
            b"mp_div" => LispToken::Keyword(LfscKeyword::MpDiv),
            b"mp_mul" => LispToken::Keyword(LfscKeyword::MpMul),
            b"mp_ifneg" => LispToken::Keyword(LfscKeyword::MpIfNeg),
            b"mp_ifzero" => LispToken::Keyword(LfscKeyword::MpIfZero),
            b"ifequal" => LispToken::Keyword(LfscKeyword::IfEqual),
            b"compare" => LispToken::Keyword(LfscKeyword::Compare),
            b"fail" => LispToken::Keyword(LfscKeyword::Fail),
            buf => {
                if buf.len() >= 8 && &buf[..8] == b"ifmarked" {
                    let s = std::str::from_utf8(&buf[8..]).map_err(bad_utf8)?;
                    let u = usize::from_str(s).map_err(bad_int)?;
                    if u >= 1 && u <= 32 {
                        LispToken::Keyword(LfscKeyword::IfMarked(u5::new(u as u8)))
                    } else {
                        return Err(bad_mark_num());
                    }
                } else if buf.len() >= 7 && &buf[..7] == b"markvar" {
                    let s = std::str::from_utf8(&buf[7..]).map_err(bad_utf8)?;
                    let u = usize::from_str(s).map_err(bad_int)?;
                    if u >= 1 && u <= 32 {
                        LispToken::Keyword(LfscKeyword::MarkVar(u5::new(u as u8)))
                    } else {
                        return Err(bad_mark_num());
                    }
                } else {
                    LispToken::Ident(std::str::from_utf8(&ident).map_err(bad_utf8)?.to_owned())
                }
            }
        })
    }
}

struct LispTokenCodec {
    last_token_was_an_identifier: bool,
    in_comment: bool,
}

impl LispTokenCodec {
    fn new() -> Self {
        Self {
            last_token_was_an_identifier: false,
            in_comment: false,
        }
    }
}

// Turns string errors into io::Error
fn bad_utf8<E>(_: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Unable to decode input as UTF8")
}

// Turns int parse into io::Error
fn bad_int<E>(_: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Unable to parse integer")
}

fn bad_mark_num() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Mark number is out of bounds")
}

fn expected_err<E: Display + ?Sized, F: Display + ?Sized>(expected: &E, found: &F) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("Expected `{}` but found `{}`", expected, found),
    )
}

fn mk_err<E: Into<Box<dyn Error + Send + Sync>>>(e: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, e)
}

impl Encoder for LispTokenCodec {
    type Item = LispToken;
    type Error = io::Error;

    fn encode(&mut self, token: Self::Item, buf: &mut BytesMut) -> Result<(), Self::Error> {
        match token {
            LispToken::Close => {
                buf.reserve(1);
                buf.put_u8(b')');
                self.last_token_was_an_identifier = false;
            }
            LispToken::Open => {
                buf.reserve(1);
                buf.put_u8(b'(');
                self.last_token_was_an_identifier = false;
            }
            LispToken::Ident(s) => {
                if self.last_token_was_an_identifier {
                    buf.reserve(1 + s.len());
                    buf.put_u8(b' ');
                    buf.put(s);
                } else {
                    buf.reserve(s.len());
                    buf.put(s);
                }
                self.last_token_was_an_identifier = true;
            }
            LispToken::Keyword(k) => {
                write!(buf.writer(), "{}", k).unwrap();
            }
        }
        Ok(())
    }
}

impl Decoder for LispTokenCodec {
    type Item = LispToken;
    type Error = io::Error;

    fn decode(&mut self, buf: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if self.in_comment {
            if let Some(first_newline) = buf.iter().position(|b| *b == b'\n') {
                buf.advance(first_newline + 1);
                self.in_comment = false;
            } else {
                buf.clear();
                return Ok(None);
            }
        }
        while let Some(first_non_whitespace) = buf.iter().position(|b| !b.is_ascii_whitespace()) {
            buf.advance(first_non_whitespace);
            if buf.len() > 0 {
                match buf[0] {
                    b'(' => {
                        buf.advance(1);
                        return Ok(Some(LispToken::Open));
                    }
                    b')' => {
                        buf.advance(1);
                        return Ok(Some(LispToken::Close));
                    }
                    b';' => {
                        if let Some(first_newline) = buf.iter().position(|b| *b == b'\n') {
                            buf.advance(first_newline + 1);
                        } else {
                            self.in_comment = true;
                            return Ok(None);
                        }
                    }
                    _ => {
                        if let Some(first_non_ident) = buf
                            .iter()
                            .position(|b| b.is_ascii_whitespace() || *b == b')' || *b == b'(')
                        {
                            let ident = buf.split_to(first_non_ident);
                            return Ok(Some(LispToken::from_ident(&ident)?));
                        } else {
                            return Ok(None);
                        }
                    }
                }
            } else {
                unreachable!()
            }
        }
        buf.clear();
        Ok(None)
    }

    fn decode_eof(&mut self, buf: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        Ok(match self.decode(buf)? {
            Some(f) => Some(f),
            None => {
                if buf.is_empty() {
                    None
                } else {
                    Some(LispToken::from_ident(&buf.take()[..])?)
                }
            }
        })
    }
}

#[allow(dead_code)]
fn count() {
    let stream = FramedRead::new(tokio::io::stdin(), LispTokenCodec::new());
    let future = stream
        .map_err(|e| {
            eprintln!("{:?}", e);
        })
        .fold(0, |a, _| Ok(a + 1))
        .map(|s| {
            println!("Number of tokens: {}", s);
        });

    tokio::run(future)
}

type Tokens = Peekable<stream::Wait<FramedRead<tokio::io::Stdin, LispTokenCodec>>>;

type Name = String;

enum Term {
    Ascription(Box<Term>, Box<Term>),
    Star,
    Var(Name),
    Apply(Box<Term>, Vec<Term>),
    Lambda(Name, Box<Term>),
    BigLambda(Name, Box<Term>, Box<Term>),
    Pi(Name, Box<Term>, Box<Term>),
    Let(Name, Box<Term>, Box<Term>),
}

impl Term {
    fn count(&self) -> usize {
        1 + match self {
            Term::Ascription(ref a, ref b) => a.count() + b.count(),
            Term::Star => 0,
            Term::Var(_) => 0,
            Term::Apply(ref a, ref args) => a.count() + args.iter().map(Term::count).sum::<usize>(),
            Term::Lambda(_, ref a) => a.count(),
            Term::BigLambda(_, ref a, ref b) => a.count() + b.count(),
            Term::Pi(_, ref a, ref b) => a.count() + b.count(),
            Term::Let(_, ref a, ref b) => a.count() + b.count(),
        }
    }
}

enum Command {
    Declare(Name, Term),
    Define(Name, Term),
    Check(Term),
}

struct Parser {
    tokens: Tokens,
}

type Program = Vec<Command>;

trait TokenStream {
    fn next(&mut self) -> io::Result<Option<LispToken>>;
    fn peek(&mut self) -> io::Result<Option<&LispToken>>;

    fn expect_next(&mut self) -> io::Result<LispToken> {
        self.next()?.ok_or_else(|| mk_err("unexpected EOF"))
    }

    fn expect_peek(&mut self) -> io::Result<&LispToken> {
        self.peek()?.ok_or_else(|| mk_err("unexpected EOF"))
    }

    fn expect_next_description<D: Display + ?Sized>(
        &mut self,
        description: &D,
    ) -> io::Result<LispToken> {
        self.next()?
            .ok_or_else(|| expected_err(&format!("{}", description), "EOF"))
    }
    fn expect_next_is(&mut self, expected_token: LispToken) -> io::Result<()> {
        let found = self.expect_next()?;
        if found == expected_token {
            Ok(())
        } else {
            Err(expected_err(&expected_token, &found))
        }
    }
}

impl TokenStream for Parser {
    fn next(&mut self) -> io::Result<Option<LispToken>> {
        self.tokens
            .next()
            .map_or(Ok(None), |result| result.map(Option::Some))
    }
    fn peek(&mut self) -> io::Result<Option<&LispToken>> {
        self.tokens.peek().map_or(Ok(None), |ref result| {
            result.as_ref().map(Option::Some).map_err(clone_err)
        })
    }
}

fn clone_err(e: &io::Error) -> io::Error {
    io::Error::new(e.kind(), e.description())
}

impl Parser {
    fn new(tokens: Tokens) -> Self {
        Self { tokens }
    }

    fn parse_term(&mut self) -> io::Result<Term> {
        match self.expect_next()? {
            LispToken::Open => {
                let ret = match self.expect_peek()? {
                    LispToken::Keyword(LfscKeyword::Colon) => {
                        self.expect_next()?;
                        let type_ = self.parse_term()?;
                        let value = self.parse_term()?;
                        self.expect_next_is(LispToken::Close)?;
                        Term::Ascription(box type_, box value)
                    }
                    LispToken::Keyword(LfscKeyword::Bang) => {
                        self.expect_next()?;
                        let id = self.parse_ident()?;
                        let domain = self.parse_term()?;
                        let range = self.parse_term()?;
                        Term::Pi(id, box domain, box range)
                    }
                    LispToken::Keyword(LfscKeyword::ReverseSolidus) => {
                        self.expect_next()?;
                        let id = self.parse_ident()?;
                        let value = self.parse_term()?;
                        Term::Lambda(id, box value)
                    }
                    LispToken::Keyword(LfscKeyword::Percent) => {
                        self.expect_next()?;
                        let id = self.parse_ident()?;
                        let domain = self.parse_term()?;
                        let range = self.parse_term()?;
                        Term::BigLambda(id, box domain, box range)
                    }
                    LispToken::Keyword(LfscKeyword::At) => {
                        self.expect_next()?;
                        let id = self.parse_ident()?;
                        let value = self.parse_term()?;
                        let in_ = self.parse_term()?;
                        Term::Let(id, box value, box in_)
                    }
                    LispToken::Ident(_) => {
                        if let LispToken::Ident(s) = self.expect_next()? {
                            let fn_ = Term::Var(s);
                            let mut args = Vec::new();
                            while self.expect_peek()? != &LispToken::Close {
                                args.push(self.parse_term()?);
                            }
                            Term::Apply(box fn_, args)
                        } else {
                            unreachable!()
                        }
                    }
                    LispToken::Open => {
                        let fn_ = self.parse_term()?;
                        let mut args = Vec::new();
                        while self.expect_peek()? != &LispToken::Close {
                            args.push(self.parse_term()?);
                        }
                        Term::Apply(box fn_, args)
                    }
                    _ => return Err(mk_err("invalid application")),
                };
                self.expect_next_is(LispToken::Close)?;
                Ok(ret)
            }
            LispToken::Keyword(LfscKeyword::Type) => Ok(Term::Star),
            LispToken::Ident(s) => Ok(Term::Var(s)),
            ref t => Err(expected_err("term", t)),
        }
    }

    fn parse_ident(&mut self) -> io::Result<Name> {
        match self.expect_next()? {
            LispToken::Ident(s) => Ok(s),
            ref t => Err(expected_err("identifier", t)),
        }
    }

    fn parse_command(&mut self) -> io::Result<Option<Command>> {
        match self.next()? {
            Some(LispToken::Open) => match self.expect_next()? {
                LispToken::Keyword(LfscKeyword::Declare) => {
                    let i = self.parse_ident()?;
                    let t = self.parse_term()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Some(Command::Declare(i, t)))
                }
                LispToken::Keyword(LfscKeyword::Define) => {
                    let i = self.parse_ident()?;
                    let t = self.parse_term()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Some(Command::Define(i, t)))
                }
                LispToken::Keyword(LfscKeyword::Check) => {
                    let t = self.parse_term()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Some(Command::Check(t)))
                }
                ref t => Err(expected_err("command", t)),
            },
            Some(ref t) => Err(expected_err(&LispToken::Open, t)),
            None => Ok(None),
        }
    }

    fn parse(&mut self) -> io::Result<Program> {
        let mut commands = Vec::new();
        while let Some(c) = self.parse_command()? {
            commands.push(c);
        }
        Ok(commands)
    }
}

struct Checker {
    tokens: Tokens,
    type_kinds: BTreeMap<String, Kind>,
    value_types: BTreeMap<String, String>,
}

struct Kind;

impl TokenStream for Checker {
    fn next(&mut self) -> io::Result<Option<LispToken>> {
        self.tokens
            .next()
            .map_or(Ok(None), |result| result.map(Option::Some))
    }
    fn peek(&mut self) -> io::Result<Option<&LispToken>> {
        self.tokens.peek().map_or(Ok(None), |ref result| {
            result.as_ref().map(Option::Some).map_err(clone_err)
        })
    }
}

impl Checker {
    fn new(tokens: Tokens) -> Self {
        Self {
            tokens,
            type_kinds: BTreeMap::new(),
            value_types: BTreeMap::new(),
        }
    }

    // The (declare should have already been consumed.
    fn check_declare(&mut self) -> io::Result<()> {
        let ident = self.expect_next_description("an identifier")?;
        let t_or_k = self.expect_next_description("a type or kind")?;
        self.expect_next_is(LispToken::Close)?;
        match (ident, t_or_k) {
            (LispToken::Ident(i), LispToken::Keyword(LfscKeyword::Type)) => {
                if self.type_kinds.contains_key(&i) {
                    return Err(mk_err(format!("Redefinition of `{}`", i)));
                }
                self.type_kinds.insert(i, Kind);
                Ok(())
            }
            (LispToken::Ident(i), LispToken::Ident(t)) => {
                if self.type_kinds.contains_key(&t) {
                    self.value_types.insert(i, t);
                    Ok(())
                } else {
                    Err(mk_err(format!("Unknown type `{}`", t)))
                }
            }
            (ident, t_or_k) => Err(mk_err(format!(
                "Bad declare (declare {} {})",
                ident, t_or_k
            ))),
        }
    }

    fn check(&mut self) -> io::Result<()> {
        while let Some(t) = self.tokens.next() {
            match t? {
                LispToken::Open => match self.expect_next()? {
                    LispToken::Keyword(LfscKeyword::Declare) => self.check_declare()?,
                    _ => unimplemented!(),
                },
                _ => unimplemented!(),
            }
        }
        Ok(())
    }
}

fn from_stdin() -> Tokens {
    FramedRead::new(tokio::io::stdin(), LispTokenCodec::new())
        .wait()
        .peekable()
}

#[allow(dead_code)]
fn check() {
    tokio::run(future::lazy(|| {
        let mut checker = Checker::new(from_stdin());
        let r = checker.check().map_err(|e| {
            eprintln!("{}", e);
        });
        println!(
            "There are now {} types and {} values",
            checker.type_kinds.len(),
            checker.value_types.len()
        );
        r
    }));
}

#[allow(dead_code)]
fn parse() {
    tokio::run(future::lazy(|| {
        let mut parser = Parser::new(from_stdin());
        parser
            .parse()
            .map_err(|e| {
                eprintln!("{}", e);
            })
            .map(|p| {
                println!(
                    "There are {} terms and {} commands",
                    p.iter()
                        .map(|c| match c {
                            Command::Check(ref t) => t.count(),
                            Command::Declare(_, ref t) => t.count(),
                            Command::Define(_, ref t) => t.count(),
                        })
                        .sum::<usize>(),
                    p.len()
                )
            }).iter().count();
        Ok(())
    }));
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("Hello, world!");
    count();
    Ok(())
}
