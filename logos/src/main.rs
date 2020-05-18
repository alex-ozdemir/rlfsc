use logos::Logos;
use std::collections::HashMap;
use std::env::args;
use std::fs::read;
use std::str::{from_utf8, FromStr};

use anyhow::{anyhow, Error};
use thiserror::Error;

const BOT: &Expr = &Expr::Bot;

#[derive(Error, Debug)]
enum LfscError {
    #[error("Parsing error at `{0}`")]
    ParsingError(String),
    #[error("Got an unexpected EOF")]
    UnexpectedEof,
    #[error("Unknown identifier `{0}`")]
    UnknownIdentifier(String),
    #[error("Expect a {0}, but found token `{1:?}`")]
    WrongToken(&'static str, Token),
    #[error("Expect a {0:?}, but found token `{1:?}`")]
    WrongToken2(Token, Token),
    #[error("A Pi-binding's range must have type 'type' or 'kind', but it has type {0:?}")]
    InvalidPiRange(Expr),
    #[error("A lambda's type cannot be computed. It must be ascribed.")]
    UnascribedLambda,
    #[error("`{0:?}` is a {1:?}, which cannot be applied")]
    UntypableApplication(Expr, Expr),
    #[error("`{0:?}` has type `{1:?}`, but was expected to have `{2:?}`")]
    UnexpectedType(Expr, Expr, Expr),
    #[error("Expected a command, but got `{0}`")]
    NotACmd(String),
    #[error("Identifiers should be declare to have kind type or kind, but {0} was declared to be a `{1:?}`, which has kind `{2:?}`")]
    BadDeclare(String, Expr, Expr),
    #[error("There most be at least one case")]
    NoCases,
    #[error("Non-pi pattern head")]
    NonPiPatternHead,
    #[error("Types `{0:?}` and `{1:?}` do not match")]
    TypeMismatch(Expr, Expr),
    #[error("Run produced `{0:?}`, but was expected to produce `{1:?}`")]
    RunWrongResult(Expr, Expr),
    #[error("Input types to mp_* must be rational or natural, not {0:?}")]
    BadMqExpr(Expr),
}

#[derive(Logos, Debug, PartialEq, Clone, Copy)]
enum Token {
    // Commands
    #[token(b"declare")]
    Declare,
    #[token(b"define")]
    Define,
    #[token(b"cons_check")]
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

    #[regex(br"[^%!@:~\\^/()0-9 \t\n\f][^() \t\n\f]*")]
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
struct Lexer<'a> {
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

impl<'a> Lexer<'a> {
    fn next(&mut self) -> Option<Token> {
        self.peek_slice = self.inner.slice();
        let n = std::mem::replace(&mut self.peek, self.inner.next());
        println!(
            "Token: {:?}, Slice: {:?}",
            n,
            from_utf8(self.peek_slice).unwrap()
        );
        n
    }
    fn require_next(&mut self) -> Result<Token, LfscError> {
        self.next().ok_or(LfscError::UnexpectedEof)
    }
    fn peek(&self) -> Option<Token> {
        self.peek
    }
    fn slice(&self) -> &'a [u8] {
        self.peek_slice
    }
    fn str(&self) -> &'a str {
        from_utf8(self.slice()).unwrap()
    }
    fn string(&self) -> String {
        self.str().to_owned()
    }
    fn nat(&self) -> u64 {
        u64::from_str(self.str()).unwrap()
    }
    fn rat(&self) -> Expr {
        let s = self.str();
        let i = s.find("/").unwrap();
        let n = u64::from_str(&s[..i]).unwrap();
        let d = u64::from_str(&s[i + 1..]).unwrap();
        Expr::new_rat(n, d)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MpBinOp {
    Add,
    Mul,
    Div,
}

impl std::convert::From<Token> for MpBinOp {
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
enum MpCond {
    Neg,
    Zero,
}

impl std::convert::From<Token> for MpCond {
    fn from(other: Token) -> MpCond {
        match other {
            Token::MpIfNeg => MpCond::Neg,
            Token::MpIfZero => MpCond::Zero,
            _ => panic!("Not mp condition: {:?}", other),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Cond {
    Equal,
    LessThan,
}

impl std::convert::From<Token> for Cond {
    fn from(other: Token) -> Cond {
        match other {
            Token::IfEqual => Cond::Equal,
            Token::Compare => Cond::LessThan,
            _ => panic!("Not condition: {:?}", other),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Bot,
    Type,
    Kind,
    NatTy,
    NatLit(u64),
    RatTy,
    RatLit(u64, u64),
    Var(String),
    /// eval expression, name, type
    Run(Box<Expr>, String, Box<Expr>),
    Pi {
        var: String,
        dom: Box<Expr>,
        rng: Box<Expr>,
    },
    App(Box<Expr>, Vec<Expr>),
    /// Arguments, return type, body
    Program(Vec<(String, Expr)>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    Let(String, Box<Expr>, Box<Expr>),
    IfMarked(u8, Box<Expr>, Box<Expr>, Box<Expr>),
    Mark(u8, Box<Expr>),
    Do(Vec<Expr>),
    IfNeg(Box<Expr>, Box<Expr>, Box<Expr>),
    IfZero(Box<Expr>, Box<Expr>, Box<Expr>),
    MpBinExpr(MpBinOp, Box<Expr>, Box<Expr>),
    MpCondExpr(MpCond, Box<Expr>, Box<Expr>, Box<Expr>),
    MpNeg(Box<Expr>),
    Fail(Box<Expr>),
    CondExpr(Cond, Box<Expr>, Box<Expr>, Box<Expr>, Box<Expr>),
}

impl Expr {
    fn is_pi_run(&self) -> bool {
        if let Expr::Pi { dom, .. } = &self {
            match **dom {
                Expr::Run(..) => true,
                _ => false,
            }
        } else {
            false
        }
    }
    fn new_rat(numerator: u64, denominator: u64) -> Expr {
        fn gcd(mut a: u64, mut b: u64) -> u64 {
            if a < b {
                std::mem::swap(&mut a, &mut b);
            }
            while b != 0 {
                let new_b = a % b;
                a = b;
                b = new_b;
            }
            return a;
        }
        let g = gcd(numerator, denominator);
        Expr::RatLit(numerator / g, denominator / g)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Pattern {
    Default,
    App(String, Vec<String>),
    Const(String),
}

impl Expr {
    fn sub(&mut self, name: &str, value: &Expr) {
        use Expr::*;
        match self {
            Var(name_) => {
                if name == name_ {
                    *self = value.clone();
                }
            }
            App(f, ref mut args) => {
                f.sub(name, value);
                for a in args {
                    a.sub(name, value);
                }
            }
            Pi { var, dom, rng } => {
                if var != name {
                    dom.sub(name, value);
                    rng.sub(name, value);
                }
            }
            _ => {}
        }
    }
}

#[derive(Default, Debug)]
struct Env {
    // Map from identifiers to their values and types
    types: HashMap<String, (Expr, Expr)>,
}

type OldBinding = Option<(Expr, Expr)>;

impl Env {
    fn bind(&mut self, name: String, value: Expr, ty: Expr) -> OldBinding {
        self.types.insert(name, (value, ty))
    }
    fn unbind(&mut self, name: &str, o: OldBinding) {
        if let Some(p) = o {
            self.types.insert(name.to_owned(), p);
        } else {
            self.types.remove(name);
        }
    }
    fn binding(&self, name: &str) -> Result<&(Expr, Expr), LfscError> {
        self.types
            .get(name)
            .ok_or_else(|| LfscError::UnknownIdentifier(name.to_owned()))
    }
    fn binding_mut(&mut self, name: &str) -> Result<&mut (Expr, Expr), LfscError> {
        self.types
            .get_mut(name)
            .ok_or_else(|| LfscError::UnknownIdentifier(name.to_owned()))
    }
    fn value(&self, name: &str) -> Result<&Expr, LfscError> {
        self.binding(name).map(|p| &p.0)
    }
    fn ty(&self, name: &str) -> Result<&Expr, LfscError> {
        self.binding(name).map(|p| &p.1)
    }
}

fn consume_var(ts: &mut Lexer) -> Result<String, LfscError> {
    match ts.require_next()? {
        Token::Ident => Ok(from_utf8(ts.slice()).unwrap().to_owned()),
        t => Err(LfscError::WrongToken("variable name", t)),
    }
}

fn consume_tok(ts: &mut Lexer, t: Token) -> Result<(), LfscError> {
    let f = ts.require_next()?;
    if &f == &t {
        Ok(())
    } else {
        Err(LfscError::WrongToken2(t, f))
    }
}

fn cons_type_pi(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    let var = consume_var(ts)?;
    let domain = cons_check(ts, e, &Expr::Type)?;
    let old_binding = e.bind(var.clone(), Expr::Var(var.clone()), domain.clone());
    let (range, range_ty) = cons_type(ts, e)?;
    consume_tok(ts, Token::Close)?;
    e.unbind(&var, old_binding);
    if range_ty == Expr::Type || range_ty == Expr::Kind {
        Ok((
            Expr::Pi {
                var,
                dom: Box::new(domain),
                rng: Box::new(range),
            },
            range_ty,
        ))
    } else {
        Err(LfscError::InvalidPiRange(range_ty))
    }
}
fn cons_type_at(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    let var = consume_var(ts)?;
    let (val, ty) = cons_type(ts, e)?;
    let old_binding = e.bind(var.clone(), val, ty);
    let (v, t) = cons_type(ts, e)?;
    consume_tok(ts, Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn cons_type_ascription(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    let ty = cons_check(ts, e, &Expr::Type)?;
    let t = cons_check(ts, e, &ty)?;
    consume_tok(ts, Token::Close)?;
    Ok((t, ty))
}

fn cons_type_big_lambda(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    let var = consume_var(ts)?;
    let ty = cons_check(ts, e, &Expr::Type)?;
    let old_binding = e.bind(var.clone(), Expr::Var(var.clone()), ty);
    let (v, t) = cons_type(ts, e)?;
    consume_tok(ts, Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn mp_type<'a>(a: &Expr) -> Result<(), LfscError> {
    if a != &Expr::NatTy && a != &Expr::RatTy {
        Err(LfscError::BadMqExpr(a.clone()))
    } else {
        Ok(())
    }
}

fn same_2_types<'a>(a: &'a Expr, b: &'a Expr) -> Result<&'a Expr, LfscError> {
    same_types(std::iter::once(a).chain(std::iter::once(b)))
}

fn same_types<'a>(tys: impl IntoIterator<Item = &'a Expr>) -> Result<&'a Expr, LfscError> {
    let mut non_fails = tys.into_iter().filter(|t| *t != &Expr::Bot);
    if let Some(first) = non_fails.next() {
        for other in non_fails {
            if first != other {
                return Err(LfscError::TypeMismatch(first.clone(), other.clone()));
            }
        }
        Ok(first)
    } else {
        Ok(BOT)
    }
}

fn run_code(e: &mut Env, code: &Expr) -> Result<Expr, LfscError> {
    unimplemented!()
}

fn cons_type_app(ts: &mut Lexer, e: &mut Env, name: String) -> Result<(Expr, Expr), LfscError> {
    let (fun, mut ty) = e.binding(&name)?.clone();
    let mut args = Vec::new();

    while Some(Token::Close) != ts.peek() || ty.is_pi_run() {
        match &ty {
            &Expr::Pi {
                ref dom,
                ref rng,
                ref var,
            } => {
                if let Expr::Run(ref term, ref var, ref term_ty) = **dom {
                    let res = run_code(e, term)?;
                    let (bound_val, bound_ty) = e.binding(&var)?;
                    same_2_types(bound_ty, term_ty)?;
                    if bound_val != &res {
                        return Err(LfscError::RunWrongResult(res, bound_val.clone()));
                    }
                } else {
                    let (arg, arg_ty) = cons_type(ts, e)?;
                    same_2_types(&arg_ty, &**dom)?;
                    let mut new_ty = *rng.clone();
                    new_ty.sub(var, &arg);
                    ty = new_ty;
                    args.push(arg);
                }
            }
            _ => return Err(LfscError::UntypableApplication(fun, ty.clone())),
        }
    }
    consume_tok(ts, Token::Close)?;
    Ok((Expr::App(Box::new(fun), args), ty))
}

fn cons_type(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    use Token::*;
    match ts.require_next()? {
        Token::Type => Ok((Expr::Type, Expr::Kind)),
        Token::Mpz => Ok((Expr::NatTy, Expr::Type)),
        Token::Mpq => Ok((Expr::RatTy, Expr::Type)),
        Token::Natural => Ok((Expr::NatLit(ts.nat()), Expr::NatTy)),
        Token::Rational => Ok((ts.rat(), Expr::RatTy)),
        Ident => {
            let n = from_utf8(ts.slice()).unwrap();
            Ok(e.binding(n)?.clone())
        }
        Open => match ts.require_next()? {
            Bang => cons_type_pi(ts, e),
            At => cons_type_at(ts, e),
            Colon => cons_type_ascription(ts, e),
            Percent => cons_type_big_lambda(ts, e),
            ReverseSolidus => Err(LfscError::UnascribedLambda),
            Ident => {
                let n = from_utf8(ts.slice()).unwrap().to_owned();
                cons_type_app(ts, e, n)
            }
            Caret => {
                let (run_expr, ty) = type_term(ts, e)?;
                let run_res = consume_var(ts)?;
                consume_tok(ts, Close)?;
                Ok((
                    Expr::Run(Box::new(run_expr), run_res, Box::new(ty)),
                    Expr::Type,
                ))
            }
            t => Err(LfscError::WrongToken("a typeable term", t)),
        },
        t => Err(LfscError::WrongToken("a typeable term", t)),
    }
}

fn cons_check(ts: &mut Lexer, e: &mut Env, ex_ty: &Expr) -> Result<Expr, LfscError> {
    let (val, ty) = cons_type(ts, e)?;
    if &ty == ex_ty {
        Ok(val)
    } else {
        Err(LfscError::UnexpectedType(val, ty, ex_ty.clone()))
    }
}

fn check_case(
    ts: &mut Lexer,
    e: &mut Env,
    disc_ty: Expr,
) -> Result<((Pattern, Expr), Expr), LfscError> {
    consume_tok(ts, Token::Open)?;
    let r = match ts.require_next()? {
        Token::Open => {
            let fun_name = consume_var(ts)?;
            let mut fun_ty = e.ty(&fun_name)?.clone();
            let mut bound_vars = Vec::new();
            let mut unbinds = Vec::new();
            loop {
                match ts.require_next()? {
                    Token::Close => break,
                    Token::Ident => {
                        let arg_name = ts.string();
                        bound_vars.push(arg_name.clone());
                        if let Expr::Pi { dom, rng, .. } = fun_ty {
                            let old_binding =
                                e.bind(arg_name.clone(), Expr::Var(arg_name.clone()), *dom.clone());
                            fun_ty = *rng;
                            unbinds.push((arg_name, old_binding));
                        } else {
                            return Err(LfscError::NonPiPatternHead);
                        }
                    }
                    t => return Err(LfscError::WrongToken("variable name", t)),
                }
            }
            let (t, ty) = type_term(ts, e)?;
            for (n, ub) in unbinds {
                e.unbind(&n, ub);
            }
            Ok(((Pattern::App(fun_name, bound_vars), t), ty))
        }
        Token::Ident => {
            let name = ts.string();
            let old_binding = e.bind(name.clone(), Expr::Var(name.clone()), disc_ty);
            let (term, ty) = type_term(ts, e)?;
            e.unbind(&name, old_binding);
            Ok(((Pattern::Const(name), term), ty))
        }
        Token::Default => type_term(ts, e).map(|(term, ty)| ((Pattern::Default, term), ty)),
        t => return Err(LfscError::WrongToken("case", t)),
    }?;
    consume_tok(ts, Token::Close)?;
    Ok(r)
}

fn type_term(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    use Token::*;
    match ts.require_next()? {
        Ident => {
            let name = ts.str();
            let (_, ty) = e.binding(name)?;
            Ok((Expr::Var(name.to_owned()), ty.clone()))
        }
        Natural => {
            let n = u64::from_str(ts.str()).unwrap();
            Ok((Expr::NatLit(n), Expr::NatTy))
        }
        Open => {
            let nxt = ts.require_next()?;
            let r = match nxt {
                Do => {
                    let (a, mut ty) = type_term(ts, e)?;
                    let mut terms = vec![a];
                    while Some(Close) != ts.peek() {
                        let (nxt, nxt_ty) = type_term(ts, e)?;
                        ty = nxt_ty;
                        terms.push(nxt)
                    }
                    Ok((Expr::Do(terms), ty))
                }
                Match => {
                    let (disc, disc_ty) = type_term(ts, e)?;
                    let mut cases = Vec::new();
                    let mut tys = Vec::new();
                    while Some(Close) != ts.peek() {
                        let (case, ty) = check_case(ts, e, disc_ty.clone())?;
                        cases.push(case);
                        tys.push(ty);
                    }
                    same_types(tys.iter())?;
                    let ty = tys.pop().ok_or(LfscError::NoCases)?;
                    Ok((Expr::Match(Box::new(disc), cases), ty))
                }
                Fail => {
                    let (ty, ty_ty) = type_term(ts, e)?;
                    if ty_ty == Expr::Type {
                        Ok((Expr::Fail(Box::new(ty)), Expr::Bot))
                    } else {
                        Err(LfscError::UnexpectedType(ty, ty_ty, Expr::Type))
                    }
                }
                MpAdd | MpMul | MpDiv => {
                    let op = MpBinOp::from(nxt);
                    let (a, a_ty) = type_term(ts, e)?;
                    let (b, b_ty) = type_term(ts, e)?;
                    same_2_types(&a_ty, &b_ty)?;
                    mp_type(&a_ty)?;

                    Ok((Expr::MpBinExpr(op, Box::new(a), Box::new(b)), a_ty))
                }
                MpNeg | Tilde => {
                    let (a, a_ty) = type_term(ts, e)?;
                    mp_type(&a_ty)?;
                    Ok((Expr::MpNeg(Box::new(a)), a_ty))
                }
                MpIfNeg | MpIfZero => {
                    let cnd = MpCond::from(nxt);
                    let (disc, disc_ty) = type_term(ts, e)?;
                    mp_type(&disc_ty)?;
                    let (a, a_ty) = type_term(ts, e)?;
                    let (b, b_ty) = type_term(ts, e)?;
                    let ty = same_2_types(&a_ty, &b_ty)?;
                    Ok((
                        Expr::MpCondExpr(cnd, Box::new(disc), Box::new(a), Box::new(b)),
                        ty.clone(),
                    ))
                }
                IfEqual | Compare => {
                    let cnd = Cond::from(nxt);
                    let (disc_a, disc_a_ty) = type_term(ts, e)?;
                    let (disc_b, disc_b_ty) = type_term(ts, e)?;
                    same_2_types(&disc_a_ty, &disc_b_ty)?;
                    let (a, a_ty) = type_term(ts, e)?;
                    let (b, b_ty) = type_term(ts, e)?;
                    let ty = same_2_types(&a_ty, &b_ty)?;
                    Ok((
                        Expr::CondExpr(
                            cnd,
                            Box::new(disc_a),
                            Box::new(disc_b),
                            Box::new(a),
                            Box::new(b),
                        ),
                        ty.clone(),
                    ))
                }
                Let => {
                    let var = consume_var(ts)?;
                    let (val, ty) = type_term(ts, e)?;
                    let old_binding = e.bind(var.clone(), val.clone(), ty);
                    let r = type_term(ts, e)?;
                    e.unbind(&var, old_binding);
                    Ok(r)
                }
                IfMarked => {
                    let n = if let "ifmarked" = ts.str() {
                        1
                    } else {
                        u8::from_str(&ts.str()["ifmarked".len()..]).unwrap()
                    };
                    let (disc, _) = type_term(ts, e)?;
                    let (t, t_ty) = type_term(ts, e)?;
                    let (f, f_ty) = type_term(ts, e)?;
                    let ty = same_2_types(&t_ty, &f_ty)?;
                    Ok((
                        Expr::IfMarked(n, Box::new(disc), Box::new(t), Box::new(f)),
                        ty.clone(),
                    ))
                }
                MarkVar => {
                    let n = if let "markvar" = ts.str() {
                        1
                    } else {
                        u8::from_str(&ts.str()["markvar".len()..]).unwrap()
                    };
                    let (term, ty) = type_term(ts, e)?;
                    Ok((Expr::Mark(n, Box::new(term)), ty))
                }
                Ident => {
                    let name = ts.string();
                    let (fun, mut ty) = e.binding(&name)?.clone();
                    let mut args = Vec::new();

                    while Some(Token::Close) != ts.peek() {
                        let (arg, arg_ty) = type_term(ts, e)?;
                        if let &Expr::Pi {
                            ref dom,
                            ref rng,
                            ref var,
                        } = &ty
                        {
                            same_2_types(&arg_ty, &**dom)?;
                            let mut new_ty = *rng.clone();
                            new_ty.sub(var, &arg);
                            ty = new_ty;
                        } else {
                            return Err(LfscError::UntypableApplication(fun, ty.clone()));
                        };
                        args.push(arg);
                    }
                    Ok((Expr::App(Box::new(Expr::Var(name)), args), ty))
                }
                t => Err(LfscError::WrongToken("term head", t)),
            }?;
            consume_tok(ts, Token::Close)?;
            Ok(r)
        }
        t => Err(LfscError::WrongToken("term", t)),
    }
}

fn check_program(ts: &mut Lexer, e: &mut Env) -> Result<(Expr, Expr), LfscError> {
    let name = consume_var(ts)?;
    consume_tok(ts, Token::Open)?;
    let mut args = Vec::new();
    let mut unbinds = Vec::new();
    loop {
        match ts.require_next()? {
            Token::Close => break,
            Token::Open => {
                let (arg_name, arg_ty) = check_arg(ts, e)?;
                let old = e.bind(
                    arg_name.clone(),
                    Expr::Var(arg_name.clone()),
                    arg_ty.clone(),
                );
                unbinds.push((arg_name.clone(), old));
                args.push((arg_name, arg_ty));
            }
            t => return Err(LfscError::WrongToken("an argument", t)),
        }
    }
    let ret_ty = cons_check(ts, e, &Expr::Type)?;
    let pgm_ty = args
        .iter()
        .rev()
        .fold(ret_ty.clone(), |x, (n, t)| Expr::Pi {
            var: n.clone(),
            rng: Box::new(x),
            dom: Box::new(t.clone()),
        });
    e.bind(name.clone(), Expr::Var(name.clone()), pgm_ty.clone());
    let (body, body_ty) = type_term(ts, e)?;
    for (n, ub) in unbinds {
        e.unbind(&n, ub);
    }
    e.binding_mut(&name)?.0 = body.clone();
    let ret_ty = same_2_types(&body_ty, &ret_ty)?.clone();
    Ok((
        Expr::Program(args, Box::new(ret_ty), Box::new(body)),
        pgm_ty,
    ))
}

fn check_arg(ts: &mut Lexer, e: &mut Env) -> Result<(String, Expr), LfscError> {
    let name = consume_var(ts)?;
    let ty = cons_check(ts, e, &Expr::Type)?;
    consume_tok(ts, Token::Close)?;
    Ok((name, ty))
}

fn do_cmd(ts: &mut Lexer, e: &mut Env) -> Result<(), LfscError> {
    use Token::{Declare, Define, Program};
    match ts.require_next()? {
        Declare => {
            let name = consume_var(ts)?;
            let (ty, kind) = cons_type(ts, e)?;
            if kind != Expr::Type && kind != Expr::Kind {
                return Err(LfscError::BadDeclare(name, ty, kind));
            }
            e.bind(name.clone(), Expr::Var(name), ty);
        }
        Define => {
            let name = consume_var(ts)?;
            let (val, ty) = cons_type(ts, e)?;
            e.bind(name.clone(), val, ty);
        }
        Program => {
            check_program(ts, e)?;
        }
        _ => return Err(LfscError::NotACmd(ts.string())),
    }
    consume_tok(ts, Token::Close)?;
    Ok(())
}

fn do_cmds(ts: &mut Lexer, e: &mut Env) -> Result<(), LfscError> {
    while let Some(t) = ts.next() {
        match t {
            Token::Open => do_cmd(ts, e)?,
            _t => return Err(LfscError::NotACmd(ts.string())),
        }
        //println!("Env: {:#?}", e);
    }
    Ok(())
}

fn main() -> Result<(), LfscError> {
    let path = args().nth(1).unwrap();
    println!("Opening `{}`", path);
    let bytes = read(&path).unwrap();
    let mut lexer = Lexer::from(Token::lexer(&bytes));
    let mut env = Env::default();
    //    do_cmds(&mut lexer, &mut env)?;
    if let Err(e) = do_cmds(&mut lexer, &mut env) {
        println!("{:#?}", e);
    }
    Ok(())
}
