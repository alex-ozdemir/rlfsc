#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(iter_unfold)]
extern crate bytes;
extern crate num;
extern crate tokio;
extern crate ux;

use num::rational::BigRational;

use tokio::codec::FramedRead;
use tokio::prelude::*;

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::Display;
use std::io;
use std::iter::Peekable;

mod token;

use token::{LfscKeyword, LispToken, LispTokenCodec};

pub fn expected_err<E: Display + ?Sized, F: Display + ?Sized>(
    expected: &E,
    found: &F,
) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("Expected `{}` but found `{}`", expected, found),
    )
}

pub fn mk_err<E: Into<Box<dyn Error + Send + Sync>>>(e: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, e)
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
    Rational(BigRational),
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
            Term::Rational(_) => 0,
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
                    LispToken::Keyword(LfscKeyword::Caret) => unimplemented!(),
                    LispToken::Keyword(ref t) => return Err(expected_err("function", t)),
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
                    LispToken::Natural(u) => {
                        return Err(expected_err("a function", u));
                    }
                    LispToken::Open => {
                        let fn_ = self.parse_term()?;
                        let mut args = Vec::new();
                        while self.expect_peek()? != &LispToken::Close {
                            args.push(self.parse_term()?);
                        }
                        Term::Apply(box fn_, args)
                    }
                    LispToken::Close => {
                        return Err(expected_err("a function", ")"));
                    }
                };
                self.expect_next_is(LispToken::Close)?;
                Ok(ret)
            }
            LispToken::Keyword(LfscKeyword::Type) => Ok(Term::Star),
            LispToken::Ident(s) => Ok(Term::Var(s)),
            LispToken::Natural(n) => {
                if self.expect_peek()? == &LispToken::Keyword(LfscKeyword::Solidus) {
                    self.expect_next()?;
                    match self.expect_next()? {
                        LispToken::Natural(d) => {
                            Ok(Term::Rational(BigRational::new(n.into(), d.into())))
                        }
                        ref t => Err(expected_err("digits", t)),
                    }
                } else {
                    Ok(Term::Rational(BigRational::from_integer(n.into())))
                }
            }
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
            })
            .iter()
            .count();
        Ok(())
    }));
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("Hello, world!");
    parse();
    Ok(())
}
