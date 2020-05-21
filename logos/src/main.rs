use logos::Logos;
use std::cell::RefCell;
use std::collections::HashMap;
use std::env::args;
use std::fs::read;
use std::rc::Rc;
use std::str::{from_utf8, FromStr};

use thiserror::Error;

#[derive(Error, Debug)]
enum LfscError {
    #[error("Got an unexpected EOF")]
    UnexpectedEof,
    #[error("Unknown identifier `{0}`")]
    UnknownIdentifier(String),
    #[error("Expect a {0}, but found token `{1:?}`")]
    UnexpectedToken(&'static str, Token),
    #[error("Expect a {0:?}, but found token `{1:?}`")]
    WrongToken(Token, Token),
    #[error("A Pi-binding's range must have type 'type' or 'kind', but it has type {0:?}")]
    InvalidPiRange(Rc<Expr>),
    #[error("A lambda's type cannot be computed. It must be ascribed.")]
    UnascribedLambda,
    #[error("`{0:?}` is a {1:?}, which cannot be applied")]
    UntypableApplication(Rc<Expr>, Rc<Expr>),
    #[error("`{0:?}` has type `{1:?}`, but was expected to have `{2:?}`")]
    UnexpectedType(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    #[error("Expected a command, but got `{0}`")]
    NotACmd(String),
    #[error("Identifiers should be declare to have kind type or kind, but {0} was declared to be a `{1:?}`, which has kind `{2:?}`")]
    BadDeclare(String, Rc<Expr>, Rc<Expr>),
    #[error("There most be at least one case")]
    NoCases,
    #[error("Non-pi pattern head")]
    NonPiPatternHead,
    #[error("Types `{0:?}` and `{1:?}` do not match")]
    TypeMismatch(Rc<Expr>, Rc<Expr>),
    #[error("Run produced `{0:?}`, but was expected to produce `{1:?}`")]
    RunWrongResult(Rc<Expr>, Rc<Expr>),
    #[error("Input types to mp_* must be rational or natural, not {0:?}")]
    BadMqExpr(Rc<Expr>),
    #[error("Misc error: {0}")]
    Misc(&'static str),
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
//        println!(
//            "Token: {:?}, Slice: {:?}",
//            n,
//            from_utf8(self.peek_slice).unwrap()
//        );
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
    NatToRat(Rc<Expr>),
    Var(Rc<String>),
    /// eval expression, name, type
    Run(Rc<Expr>, Rc<String>, Rc<Expr>),
    Pi {
        var: Rc<String>,
        dom: Rc<Expr>,
        rng: Rc<Expr>,
    },
    App(Rc<Expr>, Vec<Rc<Expr>>),
    /// Arguments, return type, body
    Program(Vec<(Rc<String>, Rc<Expr>)>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<(Pattern, Rc<Expr>)>),
    Let(Rc<String>, Rc<Expr>, Rc<Expr>),
    IfMarked(u8, Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Mark(u8, Rc<Expr>),
    Do(Vec<Rc<Expr>>),
    MpBinExpr(MpBinOp, Rc<Expr>, Rc<Expr>),
    MpCondExpr(MpCond, Rc<Expr>, Rc<Expr>, Rc<Expr>),
    MpNeg(Rc<Expr>),
    Fail(Rc<Expr>),
    CondExpr(Cond, Rc<Expr>, Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Hole(RefCell<Option<Rc<Expr>>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Pattern {
    Default,
    App(String, Vec<String>),
    Const(String),
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
    fn new_hole() -> Expr {
        Expr::Hole(RefCell::new(None))
    }

    fn deref_holes(mut r: Rc<Self>) -> Rc<Expr> {
        loop {
            let next = if let Expr::Hole(ref o) = r.as_ref() {
                if let Some(a) = o.borrow().as_ref() {
                    a.clone()
                } else {
                    break;
                }
            } else {
                break;
            };
            r = next;
        }
        r
    }

    fn unify(a: Rc<Self>, b: Rc<Self>) -> Result<Rc<Self>, LfscError> {
        if a == b {
            Ok(a.clone())
        } else {
            let aa = Expr::deref_holes(a).clone();
            let bb = Expr::deref_holes(b).clone();
            match (aa.as_ref(), bb.as_ref()) {
                (Expr::Hole(_), Expr::Hole(_)) => Err(LfscError::Misc("two holes in unify")),
                (Expr::Hole(i), _) => {
                    i.replace(Some(bb));
                    Ok(aa)
                }
                (_, Expr::Hole(i)) => {
                    i.replace(Some(aa));
                    Ok(bb)
                }
                (Expr::Bot, _) => Ok(aa),
                (_, Expr::Bot) => Ok(bb),
                (Expr::App(a_f, a_args), Expr::App(b_f, b_args)) => {
                    if a_args.len() == b_args.len() {
                        Expr::unify(a_f.clone(), b_f.clone())?;
                        for (x, y) in a_args.iter().cloned().zip(b_args.iter().cloned()) {
                            Expr::unify(x, y)?;
                        }
                        Ok(aa)
                    } else {
                        Err(LfscError::Misc("len mismatch"))
                    }
                }
                (Expr::Var(x), Expr::Var(y)) if x == y => Ok(aa),
                _ => Err(LfscError::TypeMismatch(aa, bb)),
            }
        }
    }

    fn sub(this: &Rc<Self>, name: &str, value: &Rc<Expr>) -> Rc<Self> {
        use Expr::*;
        match this.as_ref() {
            &Var(ref name_) => {
                if name == &**name_ {
                    value.clone()
                } else {
                    this.clone()
                }
            }
            &App(ref f, ref args) => Rc::new(App(
                Expr::sub(f, name, value),
                args.iter().map(|a| Expr::sub(a, name, value)).collect(),
            )),
            &Pi {
                ref var,
                ref dom,
                ref rng,
            } => {
                if &**var == name {
                    this.clone()
                } else {
                    Rc::new(Pi {
                        var: var.clone(),
                        dom: Expr::sub(dom, name, value),
                        rng: Expr::sub(rng, name, value),
                    })
                }
            }
            _ => this.clone(),
        }
    }
}

#[derive(Default, Debug)]
struct Env {
    // Map from identifiers to their values and types
    types: HashMap<String, (Rc<Expr>, Rc<Expr>)>,
}

type OldBinding = Option<(Rc<Expr>, Rc<Expr>)>;

impl Env {
    fn bind(&mut self, name: String, value: Rc<Expr>, ty: Rc<Expr>) -> OldBinding {
        self.types.insert(name, (value, ty))
    }
    fn unbind(&mut self, name: &str, o: OldBinding) {
        if let Some(p) = o {
            self.types.insert(name.to_owned(), p);
        } else {
            self.types.remove(name);
        }
    }
    fn binding(&self, name: &str) -> Result<&(Rc<Expr>, Rc<Expr>), LfscError> {
        self.types
            .get(name)
            .ok_or_else(|| LfscError::UnknownIdentifier(name.to_owned()))
    }
    fn binding_mut(&mut self, name: &str) -> Result<&mut (Rc<Expr>, Rc<Expr>), LfscError> {
        self.types
            .get_mut(name)
            .ok_or_else(|| LfscError::UnknownIdentifier(name.to_owned()))
    }
    fn value(&self, name: &str) -> Result<&Rc<Expr>, LfscError> {
        self.binding(name).map(|p| &p.0)
    }
    fn ty(&self, name: &str) -> Result<&Rc<Expr>, LfscError> {
        self.binding(name).map(|p| &p.1)
    }
}

fn consume_var(ts: &mut Lexer) -> Result<Rc<String>, LfscError> {
    match ts.require_next()? {
        Token::Ident => Ok(Rc::new(from_utf8(ts.slice()).unwrap().to_owned())),
        t => Err(LfscError::UnexpectedToken("variable name", t)),
    }
}

fn consume_tok(ts: &mut Lexer, t: Token) -> Result<(), LfscError> {
    let f = ts.require_next()?;
    if &f == &t {
        Ok(())
    } else {
        Err(LfscError::WrongToken(t, f))
    }
}

fn cons_type_pi(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let domain = cons_check(ts, e, &Expr::Type)?;
    let old_binding = e.bind(
        (*var).clone(),
        Rc::new(Expr::Var(var.clone())),
        domain.clone(),
    );
    let (range, range_ty) = cons_type(ts, e)?;
    consume_tok(ts, Token::Close)?;
    e.unbind(&var, old_binding);
    if *range_ty == Expr::Type || *range_ty == Expr::Kind {
        Ok((
            Rc::new(Expr::Pi {
                var,
                dom: domain,
                rng: range,
            }),
            range_ty,
        ))
    } else {
        Err(LfscError::InvalidPiRange(range_ty.clone()))
    }
}
fn cons_type_at(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let (val, ty) = cons_type(ts, e)?;
    let old_binding = e.bind((*var).clone(), val, ty);
    let (v, t) = cons_type(ts, e)?;
    consume_tok(ts, Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn cons_type_ascription(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let ty = cons_check(ts, e, &Expr::Type)?;
    let t = cons_check(ts, e, &ty)?;
    consume_tok(ts, Token::Close)?;
    Ok((t, ty))
}

fn cons_type_big_lambda(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let ty = cons_check(ts, e, &Expr::Type)?;
    let old_binding = e.bind((*var).clone(), Rc::new(Expr::Var(var.clone())), ty);
    let (v, t) = cons_type(ts, e)?;
    consume_tok(ts, Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn mp_type<'a>(a: &Expr) -> Result<(), LfscError> {
    if a != &Expr::NatTy && a != &Expr::RatTy {
        Err(LfscError::BadMqExpr(Rc::new(a.clone())))
    } else {
        Ok(())
    }
}

fn same_2_types(a: &Rc<Expr>, b: &Rc<Expr>) -> Result<Rc<Expr>, LfscError> {
    same_types(std::iter::once(a.clone()).chain(std::iter::once(b.clone())))
}

fn same_types(tys: impl IntoIterator<Item = Rc<Expr>>) -> Result<Rc<Expr>, LfscError> {
    let mut non_fails = tys.into_iter();
    if let Some(first) = non_fails.next() {
        non_fails.try_fold(first, Expr::unify)
    } else {
        Err(LfscError::NoCases)
    }
}

fn run_code(e: &mut Env, code: &Rc<Expr>) -> Result<Rc<Expr>, LfscError> {
    unimplemented!()
}

fn cons_type_app(
    ts: &mut Lexer,
    e: &mut Env,
    name: String,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let (fun, mut ty) = e.binding(&name)?.clone();
    let mut args = Vec::new();

    while Some(Token::Close) != ts.peek() || ty.is_pi_run() {
        match &*ty {
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
                    same_2_types(&arg_ty, dom)?;
                    ty = Expr::sub(rng, var, &arg);
                    args.push(arg);
                }
            }
            _ => return Err(LfscError::UntypableApplication(fun, ty.clone())),
        }
    }
    consume_tok(ts, Token::Close)?;
    Ok((Rc::new(Expr::App(fun, args)), ty))
}

fn cons_type(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    use Token::*;
    match ts.require_next()? {
        Token::Type => Ok((Rc::new(Expr::Type), Rc::new(Expr::Kind))),
        Token::Mpz => Ok((Rc::new(Expr::NatTy), Rc::new(Expr::Type))),
        Token::Mpq => Ok((Rc::new(Expr::RatTy), Rc::new(Expr::Type))),
        Token::Natural => Ok((Rc::new(Expr::NatLit(ts.nat())), Rc::new(Expr::NatTy))),
        Token::Rational => Ok((Rc::new(ts.rat()), Rc::new(Expr::RatTy))),
        Token::Hole => Ok((Rc::new(Expr::new_hole()), Rc::new(Expr::new_hole()))),
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
                    Rc::new(Expr::Run(run_expr, run_res, ty)),
                    Rc::new(Expr::Type),
                ))
            }
            t => Err(LfscError::UnexpectedToken("a typeable term", t)),
        },
        t => Err(LfscError::UnexpectedToken("a typeable term", t)),
    }
}

fn cons_check(ts: &mut Lexer, e: &mut Env, ex_ty: &Expr) -> Result<Rc<Expr>, LfscError> {
    let (val, ty) = cons_type(ts, e)?;
    if &*ty == ex_ty {
        Ok(val)
    } else {
        Err(LfscError::UnexpectedType(
            val.clone(),
            ty.clone(),
            Rc::new(ex_ty.clone()),
        ))
    }
}

fn check_case(
    ts: &mut Lexer,
    e: &mut Env,
    disc_ty: &Rc<Expr>,
) -> Result<((Pattern, Rc<Expr>), Rc<Expr>), LfscError> {
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
                        if let &Expr::Pi {
                            ref dom, ref rng, ..
                        } = fun_ty.as_ref()
                        {
                            let old_binding = e.bind(
                                arg_name.clone(),
                                Rc::new(Expr::Var(Rc::new(arg_name.clone()))),
                                dom.clone(),
                            );
                            fun_ty = rng.clone();
                            unbinds.push((arg_name, old_binding));
                        } else {
                            return Err(LfscError::NonPiPatternHead);
                        }
                    }
                    t => return Err(LfscError::UnexpectedToken("variable name", t)),
                }
            }
            let (t, ty) = type_term(ts, e)?;
            for (n, ub) in unbinds {
                e.unbind(&n, ub);
            }
            Ok(((Pattern::App((*fun_name).clone(), bound_vars), t), ty))
        }
        Token::Ident => {
            let name = ts.string();
            let old_binding = e.bind(
                name.clone(),
                Rc::new(Expr::Var(Rc::new(name.clone()))),
                disc_ty.clone(),
            );
            let (term, ty) = type_term(ts, e)?;
            e.unbind(&name, old_binding);
            Ok(((Pattern::Const(name), term), ty))
        }
        Token::Default => type_term(ts, e).map(|(term, ty)| ((Pattern::Default, term), ty)),
        t => return Err(LfscError::UnexpectedToken("case", t)),
    }?;
    consume_tok(ts, Token::Close)?;
    Ok(r)
}

fn type_term(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    use Token::*;
    match ts.require_next()? {
        Ident => {
            let name = Rc::new(ts.string());
            let (_, ty) = e.binding(&name)?;
            Ok((Rc::new(Expr::Var(name)), ty.clone()))
        }
        Natural => {
            let n = u64::from_str(ts.str()).unwrap();
            Ok((Rc::new(Expr::NatLit(n)), Rc::new(Expr::NatTy)))
        }
        Rational => {
            Ok((Rc::new(ts.rat()), Rc::new(Expr::RatTy)))
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
                        let (case, ty) = check_case(ts, e, &disc_ty)?;
                        cases.push(case);
                        tys.push(ty);
                    }
                    let ty = same_types(tys.iter().cloned())?;
                    Ok((Expr::Match(disc, cases), ty))
                }
                Fail => {
                    let (ty, ty_ty) = type_term(ts, e)?;
                    if *ty_ty == Expr::Type {
                        Ok((Expr::Fail(ty), Rc::new(Expr::Bot)))
                    } else {
                        Err(LfscError::UnexpectedType(ty, ty_ty, Rc::new(Expr::Type)))
                    }
                }
                MpAdd | MpMul | MpDiv => {
                    let op = MpBinOp::from(nxt);
                    let (a, a_ty) = type_term(ts, e)?;
                    let (b, b_ty) = type_term(ts, e)?;
                    same_2_types(&a_ty, &b_ty)?;
                    mp_type(&a_ty)?;

                    Ok((Expr::MpBinExpr(op, a, b), a_ty))
                }
                MpNeg | Tilde => {
                    let (a, a_ty) = type_term(ts, e)?;
                    mp_type(&a_ty)?;
                    Ok((Expr::MpNeg(a), a_ty))
                }
                MpIfNeg | MpIfZero => {
                    let cnd = MpCond::from(nxt);
                    let (disc, disc_ty) = type_term(ts, e)?;
                    mp_type(&disc_ty)?;
                    let (a, a_ty) = type_term(ts, e)?;
                    let (b, b_ty) = type_term(ts, e)?;
                    let ty = same_2_types(&a_ty, &b_ty)?;
                    Ok((Expr::MpCondExpr(cnd, disc, a, b), ty.clone()))
                }
                MpzToMpq => {
                    let (a, a_ty) = type_term(ts, e)?;
                    Expr::unify(a_ty, Rc::new(Expr::NatTy))?;
                    Ok((Expr::NatToRat(a), Rc::new(Expr::RatTy)))
                }
                IfEqual | Compare => {
                    let cnd = Cond::from(nxt);
                    let (disc_a, disc_a_ty) = type_term(ts, e)?;
                    let (disc_b, disc_b_ty) = type_term(ts, e)?;
                    same_2_types(&disc_a_ty, &disc_b_ty)?;
                    let (a, a_ty) = type_term(ts, e)?;
                    let (b, b_ty) = type_term(ts, e)?;
                    let ty = same_2_types(&a_ty, &b_ty)?;
                    Ok((Expr::CondExpr(cnd, disc_a, disc_b, a, b), ty.clone()))
                }
                Let => {
                    let var = consume_var(ts)?;
                    let (val, ty) = type_term(ts, e)?;
                    let old_binding = e.bind((*var).clone(), Rc::new(Expr::Var(var.clone())), ty);
                    let (body, body_ty) = type_term(ts, e)?;
                    e.unbind(&var, old_binding);
                    Ok((Expr::Let(var, val, body), body_ty))
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
                    Ok((Expr::IfMarked(n, disc, t, f), ty.clone()))
                }
                MarkVar => {
                    let n = if let "markvar" = ts.str() {
                        1
                    } else {
                        u8::from_str(&ts.str()["markvar".len()..]).unwrap()
                    };
                    let (term, ty) = type_term(ts, e)?;
                    Ok((Expr::Mark(n, term), ty))
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
                        } = &*ty
                        {
                            same_2_types(&arg_ty, dom)?;
                            ty = Expr::sub(rng, var, &arg);
                        } else {
                            return Err(LfscError::UntypableApplication(fun, ty.clone()));
                        };
                        args.push(arg);
                    }
                    Ok((Expr::App(Rc::new(Expr::Var(Rc::new(name))), args), ty))
                }
                t => Err(LfscError::UnexpectedToken("term head", t)),
            }?;
            consume_tok(ts, Token::Close)?;
            Ok((Rc::new(r.0), r.1))
        }
        t => Err(LfscError::UnexpectedToken("term", t)),
    }
}

fn check_program(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
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
                    (*arg_name).clone(),
                    Rc::new(Expr::Var(arg_name.clone())),
                    arg_ty.clone(),
                );
                unbinds.push((arg_name.clone(), old));
                args.push((arg_name, arg_ty));
            }
            t => return Err(LfscError::UnexpectedToken("an argument", t)),
        }
    }
    let ret_ty = cons_check(ts, e, &Expr::Type)?;
    let pgm_ty = args.iter().rev().fold(ret_ty.clone(), |x, (n, t)| {
        Rc::new(Expr::Pi {
            var: n.clone(),
            rng: x,
            dom: t.clone(),
        })
    });
    e.bind(
        (*name).clone(),
        Rc::new(Expr::Var(name.clone())),
        pgm_ty.clone(),
    );
    let (body, body_ty) = type_term(ts, e)?;
    for (n, ub) in unbinds {
        e.unbind(&n, ub);
    }
    e.binding_mut(&name)?.0 = body.clone();
    let ret_ty = same_2_types(&body_ty, &ret_ty)?.clone();
    Ok((Rc::new(Expr::Program(args, ret_ty, body)), pgm_ty))
}

fn check_arg(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<String>, Rc<Expr>), LfscError> {
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
            if *kind != Expr::Type && *kind != Expr::Kind {
                return Err(LfscError::BadDeclare((*name).clone(), ty, kind));
            }
            e.bind((*name).clone(), Rc::new(Expr::Var(name)), ty);
        }
        Define => {
            let name = consume_var(ts)?;
            let (val, ty) = cons_type(ts, e)?;
            e.bind((*name).clone(), val, ty);
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
    }
    Ok(())
}

fn main() -> Result<(), LfscError> {
    let path = args().nth(1).unwrap();
    let bytes = read(&path).unwrap();
    let mut lexer = Lexer::from(Token::lexer(&bytes));
    let mut env = Env::default();
    //    do_cmds(&mut lexer, &mut env)?;
    if let Err(e) = do_cmds(&mut lexer, &mut env) {
        println!("Error {:#?}", e);
        println!("Error {}", e);
        //println!("Error");
    }
    Ok(())
}
