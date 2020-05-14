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
use std::mem;

mod token;

use token::{LfscKeyword, LispToken, LispTokenCodec};

fn mk_rational_op_type() -> Type {
    Type::Pi(
        "_".to_owned(),
        box Type::Rational,
        box Type::Pi("_".to_owned(), box Type::Rational, box Type::Rational),
    )
}

type Tokens = Peekable<stream::Wait<FramedRead<tokio::io::Stdin, LispTokenCodec>>>;

type Name = String;

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum Builtin {
    Add,
    Div,
    Mul,
    Sub,
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum Term {
    Var(Name),
    Rational(BigRational),
    Builtin(Builtin),
    Lambda(Name, Box<Type>, Box<Term>),
    Apply(Box<Term>, Box<Term>),
}

impl Term {
    fn substitute_term(&self, param: &Name, term: &Term) -> Self {
        match self {
            t @ Term::Rational(_) => t.clone(),
            t @ Term::Builtin(_) => t.clone(),
            Term::Var(ref name) => {
                if name == param {
                    term.clone()
                } else {
                    Term::Var(name.clone())
                }
            }
            Term::Apply(box ref fn_, box ref arg) => Term::Apply(
                box fn_.substitute_term(param, term),
                box arg.substitute_term(param, term),
            ),
            Term::Lambda(ref name, box ref domain, box ref range) => Term::Lambda(
                name.clone(),
                box domain.substitute_term(param, term),
                if name == param {
                    box range.clone()
                } else {
                    box range.substitute_term(param, term)
                },
            ),
        }
    }
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum Type {
    Var(Name),
    Rational,
    Pi(Name, Box<Type>, Box<Type>),
    Apply(Box<Type>, Box<Term>),
}

impl Type {
    fn substitute_term(&self, param: &Name, term: &Term) -> Self {
        match self {
            Type::Rational => Type::Rational,
            Type::Var(ref name) => {
                if param == name {
                    panic!("Term placed into type!!")
                } else {
                    Type::Var(name.clone())
                }
            }
            Type::Pi(ref name, box ref domain, box ref range) => Type::Pi(
                name.clone(),
                box domain.substitute_term(param, term),
                if name == param {
                    box range.clone()
                } else {
                    box range.substitute_term(param, term)
                },
            ),
            Type::Apply(box ref fn_, box ref arg) => Type::Apply(
                box fn_.substitute_term(param, term),
                box arg.substitute_term(param, term),
            ),
        }
    }
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum Kind {
    Star,
    Family(Name, Box<Type>, Box<Kind>),
}

impl Kind {
    fn substitute_term(&self, param: &Name, term: &Term) -> Self {
        match self {
            Kind::Star => Kind::Star,
            Kind::Family(ref var, box ref domain, box ref range) => Kind::Family(
                var.clone(),
                box domain.substitute_term(param, term),
                box range.substitute_term(param, term),
            ),
        }
    }
}

#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum Command {
    Check(Term),
    Declare(Name, Kind),
    Define(Name, Term),
    Type(Name, Type),
}

type Program = Vec<Command>;

struct Parser {
    tokens: Tokens,
}

fn clone_err(e: &io::Error) -> io::Error {
    io::Error::new(e.kind(), e.description())
}

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

impl Parser {
    fn new(tokens: Tokens) -> Self {
        Self { tokens }
    }

    fn parse_kind(&mut self) -> io::Result<Kind> {
        match self.expect_next()? {
            LispToken::Open => match self.expect_peek()? {
                LispToken::Keyword(LfscKeyword::Bang) => {
                    self.expect_next()?;
                    let id = self.parse_ident()?;
                    let domain = self.parse_type()?;
                    let range = self.parse_kind()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Kind::Family(id, box domain, box range))
                }
                ref t => Err(expected_err("a kind family", t)),
            },
            LispToken::Keyword(LfscKeyword::Type) => Ok(Kind::Star),
            ref t => Err(expected_err("the start of a kind", t)),
        }
    }

    fn parse_type(&mut self) -> io::Result<Type> {
        match self.expect_next()? {
            LispToken::Open => {
                let ret = match self.expect_peek()? {
                    LispToken::Keyword(LfscKeyword::Bang) => {
                        self.expect_next()?;
                        let id = self.parse_ident()?;
                        let domain = self.parse_type()?;
                        let range = self.parse_type()?;
                        Type::Pi(id, box domain, box range)
                    }
                    _ => {
                        self.expect_next()?;
                        let fn_ = self.parse_type()?;
                        let arg = self.parse_term()?;
                        let mut ty = Type::Apply(box fn_, box arg);
                        while self.expect_peek()? != &LispToken::Close {
                            let arg = self.parse_term()?;
                            let old = mem::replace(&mut ty, Type::Rational);
                            ty = Type::Apply(box old, box arg);
                        }
                        ty
                    }
                };
                self.expect_next_is(LispToken::Close)?;
                Ok(ret)
            }
            LispToken::Ident(s) => {
                if s.as_str() == "mpq" {
                    Ok(Type::Rational)
                } else {
                    Ok(Type::Var(s))
                }
            }
            ref t => Err(expected_err("the start of a type", t)),
        }
    }

    fn parse_term(&mut self) -> io::Result<Term> {
        match self.expect_next()? {
            LispToken::Open => {
                let ret = match self.expect_peek()? {
                    LispToken::Keyword(LfscKeyword::ReverseSolidus) => {
                        self.expect_next()?;
                        let id = self.parse_ident()?;
                        let ty = self.parse_type()?;
                        let value = self.parse_term()?;
                        Term::Lambda(id, box ty, box value)
                    }
                    _ => {
                        let fn_ = self.parse_term()?;
                        let arg = self.parse_term()?;
                        let mut term = Term::Apply(box fn_, box arg);
                        while self.expect_peek()? != &LispToken::Close {
                            let arg = self.parse_term()?;
                            let old = mem::replace(&mut term, Term::Builtin(Builtin::Add));
                            term = Term::Apply(box old, box arg);
                        }
                        term
                    }
                };
                self.expect_next_is(LispToken::Close)?;
                Ok(ret)
            }
            LispToken::Ident(s) => Ok({
                match s.as_str() {
                    "+" => Term::Builtin(Builtin::Add),
                    "-" => Term::Builtin(Builtin::Sub),
                    "*" => Term::Builtin(Builtin::Mul),
                    "/" => Term::Builtin(Builtin::Div),
                    _ => Term::Var(s),
                }
            }),
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
            ref t => Err(expected_err("the start of a term", t)),
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
                    let t = self.parse_kind()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Some(Command::Declare(i, t)))
                }
                LispToken::Keyword(LfscKeyword::Define) => {
                    let i = self.parse_ident()?;
                    let t = self.parse_term()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Some(Command::Define(i, t)))
                }
                LispToken::Keyword(LfscKeyword::Type) => {
                    let i = self.parse_ident()?;
                    let t = self.parse_type()?;
                    self.expect_next_is(LispToken::Close)?;
                    Ok(Some(Command::Type(i, t)))
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
    kinds: BTreeMap<Name, Kind>,
    types: BTreeMap<Name, Type>,
    terms: BTreeMap<Name, Term>,
}

impl Checker {
    fn new() -> Self {
        Self {
            kinds: BTreeMap::new(),
            types: BTreeMap::new(),
            terms: BTreeMap::new(),
        }
    }
    fn check_program(&mut self, p: &Program) -> io::Result<()> {
        for c in p {
            match c {
                Command::Check(t) => {
                    let ty = self.check_type(t)?;
                    //println!("term {:?} has type {:?}", t, ty);
                }
                Command::Declare(ref name, ref kind) => {
                    if self.kinds.contains_key(name) {
                        return Err(mk_err(format!("Redefintion of type `{}`", name)));
                    } else {
                        self.kinds.insert(name.clone(), kind.clone());
                    }
                }
                Command::Define(ref name, ref term) => {
                    if self.types.contains_key(name) {
                        return Err(mk_err(format!("Redefintion of term `{}`", name)));
                    } else {
                        let term_ty = self.check_type(term)?;
                        self.types.insert(name.clone(), term_ty);
                        self.terms.insert(name.clone(), term.clone());
                    }
                }
                Command::Type(ref name, ref ty) => {
                    if self.types.contains_key(name) {
                        return Err(mk_err(format!("Redefintion of term `{}`", name)));
                    } else {
                        self.types.insert(name.clone(), ty.clone());
                    }
                }
            }
        }
        Ok(())
    }
    fn check_kind(&mut self, ty: &Type) -> io::Result<Kind> {
        match ty {
            Type::Rational => Ok(Kind::Star),
            Type::Pi(ref param, box ref domain, box ref range) => {
                let domain_k = self.check_kind(domain)?;
                if domain_k != Kind::Star {
                    return Err(mk_err(format!(
                        "Pi domains must be simple types, but I found one that had kind {:?}",
                        domain_k
                    )));
                }
                let old = self.types.insert(param.clone(), domain.clone());
                let range_k = self.check_kind(range)?;
                if range_k != Kind::Star {
                    return Err(mk_err(format!(
                        "All kinds must bottom out at `type`, but {:?} bottomed out at {:?}",
                        range, range_k
                    )));
                }
                if let Some(old_ty) = old {
                    self.types.insert(param.clone(), old_ty);
                } else {
                    self.types.remove(param);
                }
                Ok(Kind::Family(
                    param.clone(),
                    box domain.clone(),
                    box Kind::Star,
                ))
            }
            Type::Apply(box ref fn_, box ref arg) => match self.check_kind(fn_)? {
                Kind::Family(ref param, box ref domain, box ref range) => {
                    let arg_t = self.check_type(arg)?;
                    let () = self.check_equivalent_types(domain, &arg_t)?;
                    Ok(Kind::Family(
                        param.clone(),
                        box domain.clone(),
                        box range.substitute_term(param, arg),
                    ))
                }
                ref k => Err(mk_err(format!(
                    "A type function, {:?}, had kind {:?}, which is not a pi-kind.",
                    fn_, k
                ))),
            },
            Type::Var(ref name) => self
                .kinds
                .get(name)
                .cloned()
                .ok_or_else(|| mk_err(format!("Unknown type variable {}", name))),
        }
    }
    fn check_type(&mut self, term: &Term) -> io::Result<Type> {
        match term {
            Term::Builtin(Builtin::Add)
            | Term::Builtin(Builtin::Sub)
            | Term::Builtin(Builtin::Mul)
            | Term::Builtin(Builtin::Div) => Ok(mk_rational_op_type()),
            Term::Rational(_) => Ok(Type::Rational),
            Term::Var(ref name) => self
                .types
                .get(name)
                .cloned()
                .ok_or_else(|| mk_err(format!("Unknown variable {}", name))),
            Term::Lambda(ref name, box ref domain, box ref range) => {
                let domain_k = self.check_kind(domain)?;
                if domain_k == Kind::Star {
                    let old = self.types.insert(name.clone(), domain.clone());
                    let range_ty = self.check_type(range)?;
                    if let Some(old_ty) = old {
                        self.types.insert(name.clone(), old_ty);
                    } else {
                        self.types.remove(name);
                    }
                    Ok(Type::Pi(name.clone(), box domain.clone(), box range_ty))
                } else {
                    Err(mk_err(format!(
                        "The domain {:?} should have kind `type` but actually has kind {:?}",
                        domain, domain_k
                    )))
                }
            }
            Term::Apply(box ref fn_, box ref actual_arg) => {
                let fn_ty = self.check_type(fn_)?;
                if let Type::Pi(ref formal_arg, box ref formal_arg_ty, box ref range) = fn_ty {
                    let actual_arg_ty = self.check_type(actual_arg)?;
                    let () = self.check_equivalent_types(&actual_arg_ty, formal_arg_ty)?;
                    Ok(range.substitute_term(formal_arg, actual_arg))
                } else {
                    Err(mk_err(format!(
                        "The term {:?} has type {:?} but is used as a function in {:?}",
                        fn_, fn_ty, term
                    )))
                }
            }
        }
    }

    #[allow(unused_variables)]
    #[allow(dead_code)]
    fn check_equivalent_terms(&mut self, ty1: &Term, ty2: &Term) -> io::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    #[allow(dead_code)]
    fn check_equivalent_types(&mut self, ty1: &Type, ty2: &Type) -> io::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    #[allow(dead_code)]
    fn check_equivalent_kinds(&mut self, ty1: &Kind, ty2: &Kind) -> io::Result<()> {
        Ok(())
    }
}

fn from_stdin() -> Tokens {
    FramedRead::new(tokio::io::stdin(), LispTokenCodec::new())
        .wait()
        .peekable()
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("Hello, world!");
    tokio::run(future::lazy(|| {
        let mut parser = Parser::new(from_stdin());
        parser
            .parse()
            .map_err(|e| {
                eprintln!("{}", e);
            })
            .map(|p| {
                //println!("Parsed: {:#?}", p);
                let mut checker = Checker::new();
                println!("Check: {:?}", checker.check_program(&p));
            })
            .unwrap_or(());
        Ok(())
    }));
    Ok(())
}
