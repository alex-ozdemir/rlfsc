use std::convert::From;
use std::str::FromStr;
use thiserror::Error;

use crate::token::{Lexer, Token, TokenError};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Default,
    App(String, Vec<String>),
    Const(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Code {
    Match(Box<Code>, Vec<(Pattern, Code)>),
    Let(String, Box<Code>, Box<Code>),
    IfMarked(u8, Box<Code>, Box<Code>, Box<Code>),
    Mark(u8, Box<Code>),
    Do(Vec<Code>, Box<Code>),
    MpBin(MpBinOp, Box<Code>, Box<Code>),
    MpCond(MpCond, Box<Code>, Box<Code>, Box<Code>),
    MpNeg(Box<Code>),
    Fail(Box<Code>),
    Cond(Cond, Box<Code>, Box<Code>, Box<Code>, Box<Code>),
    NatToRat(Box<Code>),
    Var(String),
    NatLit(u64),
    RatLit(u64, u64),
    App(String, Vec<Code>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MpBinOp {
    Add,
    Mul,
    Div,
}

impl From<Token> for MpBinOp {
    fn from(other: Token) -> MpBinOp {
        match other {
            Token::MpAdd => MpBinOp::Add,
            Token::MpDiv => MpBinOp::Div,
            Token::MpMul => MpBinOp::Mul,
            _ => panic!("Not binop: {:?}", other),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MpCond {
    Neg,
    Zero,
}

impl From<Token> for MpCond {
    fn from(other: Token) -> MpCond {
        match other {
            Token::MpIfNeg => MpCond::Neg,
            Token::MpIfZero => MpCond::Zero,
            _ => panic!("Not mp condition: {:?}", other),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cond {
    Equal,
    LessThan,
}

impl From<Token> for Cond {
    fn from(other: Token) -> Cond {
        match other {
            Token::IfEqual => Cond::Equal,
            Token::Compare => Cond::LessThan,
            _ => panic!("Not condition: {:?}", other),
        }
    }
}

#[derive(Error, Debug)]
pub enum CodeParseError {
    #[error("No expression in a do form")]
    EmptyDo,
    #[error("No cases in a match form")]
    EmptyMatch,
    #[error("Expect a {0}, but found token `{1:?}`")]
    UnexpectedToken(&'static str, Token),
    #[error("TokenError: {0}")]
    TokenError(TokenError),
}

impl From<TokenError> for CodeParseError {
    fn from(o: TokenError) -> Self {
        Self::TokenError(o)
    }
}

pub fn parse_term(ts: &mut Lexer) -> Result<Code, CodeParseError> {
    use Token::*;
    match ts.require_next()? {
        Ident => Ok(Code::Var(ts.string())),
        Natural => Ok(Code::NatLit(ts.nat())),
        Rational => {
            let (n, d) = ts.rat();
            Ok(Code::RatLit(n, d))
        }
        Open => {
            let nxt = ts.require_next()?;
            let r = match nxt {
                Do => {
                    let mut terms = Vec::new();
                    while Some(Close) != ts.peek() {
                        terms.push(parse_term(ts)?);
                    }
                    if let Some(last) = terms.pop() {
                        Ok(Code::Do(terms, Box::new(last)))
                    } else {
                        Err(CodeParseError::EmptyDo)
                    }
                }
                Match => {
                    let disc = parse_term(ts)?;
                    let mut cases = Vec::new();
                    while Some(Close) != ts.peek() {
                        cases.push(parse_case(ts)?);
                    }
                    Ok(Code::Match(Box::new(disc), cases))
                }
                Fail => Ok(Code::Fail(Box::new(parse_term(ts)?))),
                MpAdd | MpMul | MpDiv => Ok(Code::MpBin(
                    MpBinOp::from(nxt),
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                )),
                MpNeg | Tilde => Ok(Code::MpNeg(Box::new(parse_term(ts)?))),
                MpIfNeg | MpIfZero => Ok(Code::MpCond(
                    MpCond::from(nxt),
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                )),
                MpzToMpq => Ok(Code::NatToRat(Box::new(parse_term(ts)?))),
                IfEqual | Compare => Ok(Code::Cond(
                    Cond::from(nxt),
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                )),
                Let => Ok(Code::Let(
                    ts.consume_ident()?,
                    Box::new(parse_term(ts)?),
                    Box::new(parse_term(ts)?),
                )),
                IfMarked => {
                    let n = if let "ifmarked" = ts.str() {
                        1
                    } else {
                        u8::from_str(&ts.str()["ifmarked".len()..]).unwrap()
                    };
                    Ok(Code::IfMarked(
                        n,
                        Box::new(parse_term(ts)?),
                        Box::new(parse_term(ts)?),
                        Box::new(parse_term(ts)?),
                    ))
                }
                MarkVar => {
                    let n = if let "markvar" = ts.str() {
                        1
                    } else {
                        u8::from_str(&ts.str()["markvar".len()..]).unwrap()
                    };
                    Ok(Code::Mark(n, Box::new(parse_term(ts)?)))
                }
                Ident => {
                    let fun_name = ts.string();
                    let mut args = Vec::new();
                    while Some(Token::Close) != ts.peek() {
                        args.push(parse_term(ts)?);
                    }
                    Ok(Code::App(fun_name, args))
                }
                t => Err(CodeParseError::from(TokenError::UnexpectedToken("term head", t))),
            }?;
            ts.consume_tok(Token::Close)?;
            Ok(r)
        }
        t => Err(CodeParseError::from(TokenError::UnexpectedToken("term", t))),
    }
}

fn parse_case(ts: &mut Lexer) -> Result<(Pattern, Code), CodeParseError> {
    ts.consume_tok(Token::Open)?;
    let r = match ts.require_next()? {
        Token::Open => {
            let fun_name = ts.consume_ident()?;
            let mut bindings = Vec::new();
            while Some(Token::Close) != ts.peek() {
                bindings.push(ts.consume_ident()?);
            }
            ts.consume_tok(Token::Close)?;
            Ok(Pattern::App(fun_name, bindings))
        }
        Token::Ident => Ok(Pattern::Const(ts.string())),
        Token::Default => Ok(Pattern::Default),
        t => Err(CodeParseError::from(CodeParseError::UnexpectedToken("case", t))),
    }?;
    let val = parse_term(ts)?;
    ts.consume_tok(Token::Close)?;
    Ok((r, val))
}
