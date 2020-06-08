use std::convert::From;
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;
use std::str::FromStr;
use thiserror::Error;

use rug::{Integer, Rational};

use crate::token::{Lexer, Token, TokenError};
use crate::error::LfscError;
use crate::expr::{Expr};
use crate::env::{Env, EnvEntry};

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
    NatLit(Integer),
    RatLit(Rational),
    App(String, Vec<Code>),
    Expr(Rc<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
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

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
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

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
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

impl Code {
    pub fn sub(&self, name: &str, value: &Rc<Expr>) -> Self {
        match self {
            &Code::Var(ref name_) => {
                if name == &**name_ {
                    Code::Expr(value.clone())
                } else {
                    self.clone()
                }
            }
            &Code::App(ref f, ref args) if f != name => Code::App(
                f.clone(),
                args.iter().map(|a| Code::sub(a, name, value)).collect(),
            ),
            &Code::MpNeg(ref f) => Code::MpNeg(Box::new(Code::sub(f, name, value))),
            &Code::Expr(ref r) => Code::Expr(Expr::sub(r, name, value)),
            &Code::MpBin(o, ref a, ref b) => Code::MpBin(
                o,
                Box::new(Code::sub(&a, name, value)),
                Box::new(Code::sub(&b, name, value)),
            ),
            &Code::NatLit(_) => self.clone(),
            &Code::RatLit(_) => self.clone(),
            _ => todo!("NYI: sub over {}", self),
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
        Rational => Ok(Code::RatLit(ts.rat())),
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
                    if cases.len() == 0 {
                        Err(CodeParseError::EmptyMatch)
                    } else {
                        Ok(Code::Match(Box::new(disc), cases))
                    }
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
                t => Err(CodeParseError::from(TokenError::UnexpectedToken(
                    "term head",
                    t,
                ))),
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
        t => Err(CodeParseError::from(CodeParseError::UnexpectedToken(
            "case", t,
        ))),
    }?;
    let val = parse_term(ts)?;
    ts.consume_tok(Token::Close)?;
    Ok((r, val))
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Pattern::Default => write!(f, "default"),
            Pattern::Const(c) => write!(f, "{}", c),
            Pattern::App(head, tail) => {
                write!(f, "({}", head)?;
                for t in tail {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for MpBinOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            MpBinOp::Add => write!(f, "mp_add"),
            MpBinOp::Div => write!(f, "mp_div"),
            MpBinOp::Mul => write!(f, "mp_mul"),
        }
    }
}

impl Display for MpCond {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            MpCond::Neg => write!(f, "mp_ifneg"),
            MpCond::Zero => write!(f, "mp_ifzero"),
        }
    }
}

impl Display for Cond {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Cond::Equal => write!(f, "ifequal"),
            Cond::LessThan => write!(f, "compare"),
        }
    }
}

impl Display for Code {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Code::*;
        match self {
            Match(c, cs) => {
                write!(f, "(match {}", c)?;
                for (p, e) in cs {
                    write!(f, " ({} {})", p, e)?;
                }
                write!(f, ")")
            }
            Let(name, v, body) => write!(f, "(let {} {} {})", name, v, body),
            IfMarked(n, a, b, c) => write!(f, "(ifmarked{} {} {} {})", n, a, b, c),
            Mark(n, a) => write!(f, "(markvar{} {})", n, a),
            Do(cs, c) => {
                write!(f, "(do")?;
                for x in cs {
                    write!(f, " {}", x)?;
                }
                write!(f, " {})", c)
            }
            MpBin(o, a, b) => write!(f, "({} {} {})", o, a, b),
            MpCond(o, a, b, c) => write!(f, "({} {} {} {})", o, a, b, c),
            MpNeg(c) => write!(f, "(mp_neg {})", c),
            Fail(c) => write!(f, "(fail {})", c),
            Cond(o, a, b, c, d) => write!(f, "({} {} {} {} {})", o, a, b, c, d),
            NatToRat(c) => write!(f, "(mpz_to_mpq {})", c),
            Expr(e) => write!(f, "{}", e),
            NatLit(u) => write!(f, "{}", u),
            RatLit(r) => write!(f, "{}/{}", r.numer(), r.denom()),
            Var(s) => write!(f, "{}", s),
            App(head, tail) => {
                write!(f, "({}", head)?;
                for t in tail {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
        }
    }
}

pub fn run_code(e: &mut Env, code: &Code) -> Result<Rc<Expr>, LfscError> {
    match code {
        Code::Var(s) => Ok(e.deref(e.expr_value(&s)?.clone())?),
        Code::App(ref fn_name, ref arg_terms) => {
            let args = arg_terms
                .iter()
                .map(|a| run_code(e, a))
                .collect::<Result<Vec<_>, _>>()?;
            match e.binding(fn_name)? {
                EnvEntry::Program(pgm) => {
                    let formal_args = pgm.val.args.clone();
                    let body = pgm.val.body.clone();
                    if formal_args.len() == args.len() {
                        let unbinds: Vec<_> = formal_args
                            .iter()
                            .zip(args.iter())
                            .map(|((name, _), a)| {
                                e.bind_expr(name.clone(), a.clone(), e.bot.clone())
                            })
                            .collect();
                        let r = run_code(e, body.as_ref())?;
                        for (u, (n, _)) in unbinds.into_iter().zip(formal_args.iter()) {
                            e.unbind(&n, u);
                        }
                        Ok(r)
                    } else {
                        Err(LfscError::WrongNumberOfArgs(
                            fn_name.clone(),
                            formal_args.len(),
                            args.len(),
                        ))
                    }
                }
                EnvEntry::Expr(expr) => Ok(Rc::new(Expr::App(expr.val.clone(), args))),
            }
        }
        Code::NatLit(i) => Ok(Rc::new(Expr::NatLit(i.clone()))),
        Code::RatLit(r) => Ok(Rc::new(Expr::RatLit(r.clone()))),
        Code::Do(xs, y) => {
            for x in xs {
                run_code(e, x)?;
            }
            run_code(e, y)
        }
        Code::Let(n, v, body) => {
            let vv = run_code(e, v)?;
            let o = e.bind_expr(n.clone(), vv, e.bot.clone());
            let r = run_code(e, body)?;
            e.unbind(&n, o);
            Ok(r)
        }
        Code::Cond(c, l, r, t, f) => {
            let ll = run_code(e, l)?;
            let rr = run_code(e, r)?;
            if match c {
                Cond::Equal => Rc::into_raw(ll) == Rc::into_raw(rr),
                Cond::LessThan => Rc::into_raw(ll) < Rc::into_raw(rr),
            } {
                run_code(e, t)
            } else {
                run_code(e, f)
            }
        }
        Code::NatToRat(i) => match run_code(e, i)?.as_ref() {
            Expr::NatLit(x) => Ok(Rc::new(Expr::RatLit(Rational::new() + x))),
            x => Err(LfscError::NotMpzInMpzToMpq((*x).clone())),
        },
        Code::Fail(i) => Err(LfscError::Fail((*run_code(e, i)?).clone())),
        Code::MpNeg(i) => run_code(e, i)?.as_ref().mp_neg().map(Rc::new),
        Code::MpBin(o, i, j) => run_code(e, i)?
            .as_ref()
            .mp_bin(*o, run_code(e, j)?.as_ref())
            .map(Rc::new),
        Code::MpCond(o, i, j, k) => match run_code(e, i)?.as_ref() {
            Expr::NatLit(x) => {
                if match o {
                    MpCond::Neg => x < &(0 as u64),
                    MpCond::Zero => x == &(0 as u64),
                } {
                    run_code(e, j)
                } else {
                    run_code(e, k)
                }
            }
            Expr::RatLit(x) => {
                if match o {
                    MpCond::Neg => x < &(0 as u64),
                    MpCond::Zero => x == &(0 as u64),
                } {
                    run_code(e, j)
                } else {
                    run_code(e, k)
                }
            }
            t => Err(LfscError::NotMpInMpCond(*o, t.clone())),
        },
        Code::Match(disc, cases) => {
            let d = Expr::deref_holes(run_code(e, disc)?);
            for (pat, v) in cases.iter() {
                match pat {
                    Pattern::Default => return run_code(e, v),
                    Pattern::Const(s) => {
                        if e.unify(e.expr_value(&s)?.clone(), d.clone()).is_ok() {
                            return run_code(e, v);
                        }
                    }
                    Pattern::App(head_name, vars) => {
                        let phead = e.expr_value(&head_name)?;
                        if let Expr::App(dhead, dargs) = d.as_ref() {
                            if e.unify(phead.clone(), dhead.clone()).is_ok() {
                                if dargs.len() == vars.len() {
                                    let unbinds: Vec<_> = vars
                                        .iter()
                                        .zip(dargs.iter())
                                        .map(|(name, a)| {
                                            e.bind_expr(name.clone(), a.clone(), e.bot.clone())
                                        })
                                        .collect();
                                    let r = run_code(e, v)?;
                                    for (u, n) in unbinds.into_iter().zip(vars.iter()) {
                                        e.unbind(&n, u);
                                    }
                                    return Ok(r);
                                } else {
                                    return Err(LfscError::WrongBindingCount((*d).clone(), dargs.len(), vars.len(), pat.clone()));
                                }
                            }
                        }
                    }
                }
            }
            Err(LfscError::NoPattern(
                (*d).clone(),
                cases.iter().map(|(p, _)| p.clone()).collect(),
            ))
        }
        Code::Mark(n, i) => {
            let v = run_code(e, i)?;
            e.toggle_mark(v.clone(), *n)
        }
        Code::IfMarked(n, c, t, f) => {
            let cond = run_code(e, c)?;
            if e.get_mark(cond, *n)? {
                run_code(e, t)
            } else {
                run_code(e, f)
            }
        }
        Code::Expr(ex) => {
            let r = e.deref(ex.clone())?;
            match r.as_ref() {
                &Expr::Hole(_) => Err(LfscError::UnfilledHole),
                _ => Ok(r),
            }
        }
    }
}

