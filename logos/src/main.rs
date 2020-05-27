use logos::Logos;
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::{From, Into};
use std::default::Default;
use std::env::args;
use std::fs::read;
use std::rc::Rc;
use std::fmt::{Formatter, Display, self};
use std::str::from_utf8;

use thiserror::Error;

mod code;
mod token;

use code::{parse_term, Code, CodeParseError, Cond, MpBinOp, MpCond, Pattern};
use token::{Lexer, Token, TokenError};

#[derive(Debug, PartialEq, Eq)]
struct Program {
    args: Vec<(String, Rc<Expr>)>,
    ret_ty: Rc<Expr>,
    body: Code,
}

#[derive(Error, Debug)]
enum LfscError {
    #[error("Got an unexpected EOF")]
    UnexpectedEof,
    #[error("Unknown identifier `{0}`")]
    UnknownIdentifier(String),
    #[error("Expect a {0}, but found token `{1:?}`")]
    UnexpectedToken(&'static str, Token),
    #[error("A Pi-binding's range must have type 'type' or 'kind', but it has type {0:?}")]
    InvalidPiRange(Rc<Expr>),
    #[error("A lambda's type cannot be computed. It must be ascribed.")]
    UnascribedLambda,
    #[error("a {0:?} cannot be applied")]
    UntypableApplication(Rc<Expr>),
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
    #[error("Types `{0}` and `{1}` do not match")]
    TypeMismatch(Rc<Expr>, Rc<Expr>),
    #[error("Run produced `{0:?}`, but was expected to produce `{1:?}`")]
    RunWrongResult(Rc<Expr>, Rc<Expr>),
    #[error("Input types to mp_* must be rational or natural, not {0:?}")]
    BadMqExpr(Rc<Expr>),
    #[error("Misc error: {0}")]
    Misc(&'static str),
    #[error("TokenError: {0}")]
    TokenError(TokenError),
    #[error("CodeParseError: {0}")]
    CodeParseError(CodeParseError),
    #[error("The identifier {2} is an {1} but should be a {0}")]
    WrongIdentifierType(&'static str, &'static str, String),
}

impl From<TokenError> for LfscError {
    fn from(o: TokenError) -> Self {
        Self::TokenError(o)
    }
}

impl From<CodeParseError> for LfscError {
    fn from(o: CodeParseError) -> Self {
        Self::CodeParseError(o)
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
    MpNeg(Rc<Expr>),
    RatLit(u64, u64),
    Var(Rc<String>),
    /// eval expression, name, type
    Run(Code, Rc<String>, Rc<Expr>),
    Pi {
        var: Rc<String>,
        dom: Rc<Expr>,
        rng: Rc<Expr>,
    },
    App(Rc<Expr>, Vec<Rc<Expr>>),
    /// Arguments, return type, body
    Hole(RefCell<Option<Rc<Expr>>>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Expr::*;
        match self {
            Bot => write!(f, "_|_"),
            Type => write!(f, "type"),
            Kind => write!(f, "kind"),
            NatTy => write!(f, "mpz"),
            RatTy => write!(f, "mpq"),
            NatLit(u) => write!(f, "{}", u),
            RatLit(n,d) => write!(f, "{}/{}", n, d),
            Var(s) => write!(f, "{}", s),
            MpNeg(s) => write!(f, "(~ {})", s),
            Run(c, n, e) => write!(f, "(^ ({:?} {}) {})", c, n, e),
            Pi{var, dom, rng} => write!(f, "(! {} {} {})", var, dom, rng),
            App(head, tail) => {
                write!(f, "({}", head)?;
                for t in tail {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Hole(c) => {
                if let Some(r) = c.borrow().as_ref() {
                    write!(f, "{}", r)
                } else {
                    write!(f, "_")
                }
            }
        }
    }
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
            Ok((match (aa.as_ref(), bb.as_ref()) {
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
                _ => Err(LfscError::TypeMismatch(aa.clone(), bb.clone())),
            })?)
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

#[derive(Debug, PartialEq, Eq)]
enum EnvEntry {
    Expr(ExprEnvEntry),
    Program(PgmEnvEntry),
}

impl From<EnvEntry> for Result<ExprEnvEntry, PgmEnvEntry> {
    fn from(e: EnvEntry) -> Self {
        match e {
            EnvEntry::Expr(a) => Ok(a),
            EnvEntry::Program(a) => Err(a),
        }
    }
}

impl From<ExprEnvEntry> for (Rc<Expr>, Rc<Expr>) {
    fn from(e: ExprEnvEntry) -> Self {
        (e.val, e.ty)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct ExprEnvEntry {
    val: Rc<Expr>,
    ty: Rc<Expr>,
}

#[derive(Debug, PartialEq, Eq)]
struct PgmEnvEntry {
    val: Program,
    ty: Rc<Expr>,
}

#[derive(Debug)]
struct Env {
    // Map from identifiers to their values and types
    types: HashMap<String, EnvEntry>,
    type_: Rc<Expr>,
    kind: Rc<Expr>,
    nat: Rc<Expr>,
    rat: Rc<Expr>,
    bot: Rc<Expr>,
}

impl Default for Env {
    fn default() -> Self {
        Self {
            types: Default::default(),
            type_: Rc::new(Expr::Type),
            kind: Rc::new(Expr::Kind),
            nat: Rc::new(Expr::NatTy),
            rat: Rc::new(Expr::RatTy),
            bot: Rc::new(Expr::Bot),
        }
    }
}

type OldBinding = Option<EnvEntry>;

impl Env {
    pub fn bind_expr(&mut self, name: String, val: Rc<Expr>, ty: Rc<Expr>) -> OldBinding {
        self.types
            .insert(name, EnvEntry::Expr(ExprEnvEntry { val, ty }))
    }
    pub fn unbind(&mut self, name: &str, o: OldBinding) {
        if let Some(p) = o {
            self.types.insert(name.to_owned(), p);
        } else {
            self.types.remove(name);
        }
    }
    pub fn binding(&self, name: &str) -> Result<&EnvEntry, LfscError> {
        self.types
            .get(name)
            .ok_or_else(|| LfscError::UnknownIdentifier(name.to_owned()))
    }
    pub fn expr_binding(&self, name: &str) -> Result<&ExprEnvEntry, LfscError> {
        match self.binding(name)? {
            EnvEntry::Expr(ref e) => Ok(e),
            _ => Err(LfscError::WrongIdentifierType(
                "expression",
                "side condition",
                name.to_owned(),
            )),
        }
    }
    pub fn expr_value(&self, name: &str) -> Result<&Rc<Expr>, LfscError> {
        self.expr_binding(name).map(|p| &p.val)
    }
    pub fn ty(&self, name: &str) -> Result<&Rc<Expr>, LfscError> {
        match self.binding(name)? {
            EnvEntry::Expr(ref e) => Ok(&e.ty),
            EnvEntry::Program(ref e) => Ok(&e.ty),
        }
    }
}

fn consume_var(ts: &mut Lexer) -> Result<Rc<String>, LfscError> {
    Ok(Rc::new(ts.consume_ident()?))
}

fn type_pi(ts: &mut Lexer, e: &mut Env) -> Result<Rc<Expr>, LfscError> {
    let var = consume_var(ts)?;
    let domain = cons_check(ts, e, e.type_.clone())?;
    let old_binding = e.bind_expr(
        (*var).clone(),
        Rc::new(Expr::Var(var.clone())),
        domain.clone(),
    );
    let (range, range_ty) = cons_type(ts, e)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(&var, old_binding);
    if *range_ty == Expr::Type || *range_ty == Expr::Kind {
        Ok(range_ty)
    } else {
        Err(LfscError::InvalidPiRange(range_ty.clone()))
    }
}

fn cons_type_pi(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let domain = cons_check(ts, e, e.type_.clone())?;
    let old_binding = e.bind_expr(
        (*var).clone(),
        Rc::new(Expr::Var(var.clone())),
        domain.clone(),
    );
    let (range, range_ty) = cons_type(ts, e)?;
    ts.consume_tok(Token::Close)?;
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
    let old_binding = e.bind_expr((*var).clone(), val, ty);
    let (v, t) = cons_type(ts, e)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn cons_type_ascription(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let ty = cons_check(ts, e, e.type_.clone())?;
    let t = cons_check(ts, e, ty.clone())?;
    ts.consume_tok(Token::Close)?;
    Ok((t, ty))
}

fn cons_type_big_lambda(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let ty = cons_check(ts, e, e.type_.clone())?;
    let old_binding = e.bind_expr((*var).clone(), Rc::new(Expr::Var(var.clone())), ty);
    let (v, t) = cons_type(ts, e)?;
    ts.consume_tok(Token::Close)?;
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

fn run_code(_e: &mut Env, _code: &Code) -> Result<Rc<Expr>, LfscError> {
    unimplemented!()
}

fn cons_type_app(
    ts: &mut Lexer,
    e: &mut Env,
    name: String,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let b = e.expr_binding(&name)?;
    let fun = b.val.clone();
    let mut ty = b.ty.clone();
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
                    let b = e.expr_binding(&var)?;
                    same_2_types(&b.ty, term_ty)?;
                    if &b.val != &res {
                        return Err(LfscError::RunWrongResult(res, b.val.clone()));
                    }
                } else {
                    let arg = cons_check(ts, e, dom.clone())?;
                    ty = Expr::sub(rng, var, &arg);
                    args.push(arg);
                }
            }
            _ => return Err(LfscError::UntypableApplication(ty.clone())),
        }
    }
    ts.consume_tok(Token::Close)?;
    Ok((Rc::new(Expr::App(fun, args)), ty))
}

fn cons_type(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    use Token::*;
    match ts.require_next()? {
        Token::Type => Ok((Rc::new(Expr::Type), Rc::new(Expr::Kind))),
        Token::Mpz => Ok((Rc::new(Expr::NatTy), Rc::new(Expr::Type))),
        Token::Mpq => Ok((Rc::new(Expr::RatTy), Rc::new(Expr::Type))),
        Token::Natural => Ok((Rc::new(Expr::NatLit(ts.nat())), Rc::new(Expr::NatTy))),
        Token::Rational => {
            let (n, d) = ts.rat();
            Ok((Rc::new(Expr::new_rat(n, d)), Rc::new(Expr::RatTy)))
        }
        Token::Hole => Ok((Rc::new(Expr::new_hole()), Rc::new(Expr::new_hole()))),
        Ident => {
            let n = from_utf8(ts.slice()).unwrap();
            Ok(e.expr_binding(n)?.clone().into())
        }
        Open => match ts.require_next()? {
            Bang => cons_type_pi(ts, e),
            At => cons_type_at(ts, e),
            Colon => cons_type_ascription(ts, e),
            Percent => cons_type_big_lambda(ts, e),
            Tilde => Ok({
                let (t, ty) = cons_type(ts, e)?;
                mp_type(&ty)?;
                ts.consume_tok(Close)?;
                (Rc::new(Expr::MpNeg(t)), ty)
            }),
            ReverseSolidus => Err(LfscError::UnascribedLambda),
            Ident => {
                let n = from_utf8(ts.slice()).unwrap().to_owned();
                cons_type_app(ts, e, n)
            }
            Caret => {
                let run_expr = parse_term(ts)?;
                let ty = type_code(&run_expr, e)?;
                let run_res = consume_var(ts)?;
                ts.consume_tok(Close)?;
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

fn cons_check(ts: &mut Lexer, e: &mut Env, ex_ty: Rc<Expr>) -> Result<Rc<Expr>, LfscError> {
    //println!("Ex: {}", ex_ty);
    match cons_type(ts, e) {
        Ok((val, ty)) => {
            let t = Expr::unify(ty, ex_ty)?;
            //println!(" => {}", t);
            Ok(val)
        }
        Err(LfscError::UnascribedLambda) => {
            if let &Expr::Pi {
                ref dom,
                ref rng,
                ..
            } = ex_ty.as_ref()
            {
                let var = consume_var(ts)?;
                let old_binding =
                    e.bind_expr((*var).clone(), Rc::new(Expr::Var(var.clone())), dom.clone());
                let res = cons_check(ts, e, rng.clone())?;
                ts.consume_tok(Token::Close)?;
                e.unbind(&var, old_binding);
                Ok(Rc::new(Expr::Pi {
                    var,
                    dom: dom.clone(),
                    rng: res,
                }))
            } else {
                Err(LfscError::Misc("Cannot type a lamda as a non-pi"))
            }
        }
        Err(e) => Err(e),
    }
}

fn type_program(ts: &mut Lexer, e: &mut Env) -> Result<(), LfscError> {
    let name = consume_var(ts)?;
    ts.consume_tok(Token::Open)?;
    let mut args = Vec::new();
    let mut unbinds = Vec::new();
    loop {
        match ts.require_next()? {
            Token::Close => break,
            Token::Open => {
                let (arg_name, arg_ty) = check_arg(ts, e)?;
                let old = e.bind_expr(
                    arg_name.clone(),
                    Rc::new(Expr::Var(Rc::new(arg_name.clone()))),
                    arg_ty.clone(),
                );
                unbinds.push((arg_name.clone(), old));
                args.push((arg_name, arg_ty));
            }
            t => return Err(LfscError::UnexpectedToken("an argument", t)),
        }
    }
    let ret_ty = cons_check(ts, e, e.type_.clone())?;
    let pgm_ty = args.iter().rev().fold(ret_ty.clone(), |x, (n, t)| {
        Rc::new(Expr::Pi {
            var: Rc::new(n.clone()),
            rng: x,
            dom: t.clone(),
        })
    });
    e.bind_expr(
        (*name).clone(),
        Rc::new(Expr::Var(name.clone())),
        pgm_ty.clone(),
    );
    let body = parse_term(ts)?;
    let body_ty = type_code(&body, e)?;
    Expr::unify(body_ty, ret_ty.clone())?;
    for (n, ub) in unbinds {
        e.unbind(&n, ub);
    }
    let pgm = Program { args, ret_ty, body };
    e.types.insert(
        (*name).clone(),
        EnvEntry::Program(PgmEnvEntry {
            val: pgm,
            ty: pgm_ty,
        }),
    );
    Ok(())
}

fn type_code(t: &Code, e: &mut Env) -> Result<Rc<Expr>, LfscError> {
    match t {
        Code::Var(n) => Ok(e.ty(&n)?.clone()),
        Code::NatLit(_) => Ok(e.nat.clone()),
        Code::RatLit(..) => Ok(e.rat.clone()),
        Code::NatToRat(ref i) => {
            Expr::unify(e.nat.clone(), type_code(&i, e)?)?;
            Ok(e.rat.clone())
        }
        Code::Let(ref name, ref val, ref body) => {
            let ty = type_code(val, e)?;
            let o = e.bind_expr(
                name.to_owned(),
                Rc::new(Expr::Var(Rc::new(name.to_owned()))),
                ty,
            );
            let r = type_code(body, e)?;
            e.unbind(name, o);
            Ok(r)
        }
        Code::IfMarked(_, _, ref tr, ref fa) => Expr::unify(type_code(tr, e)?, type_code(fa, e)?),
        Code::Mark(_, ref v) => type_code(v, e),
        Code::Do(ref init, ref last) => {
            for i in init {
                type_code(i, e)?;
            }
            type_code(last, e)
        }
        Code::MpBin(_, ref a, ref b) => {
            let ty = Expr::unify(type_code(a, e)?, type_code(b, e)?)?;
            mp_type(&ty)?;
            Ok(ty)
        }
        Code::MpCond(_, ref c, ref tr, ref fa) => {
            mp_type(type_code(c, e)?.as_ref())?;
            Expr::unify(type_code(tr, e)?, type_code(fa, e)?)
        }
        Code::MpNeg(ref i) => {
            let ty = type_code(i, e)?;
            mp_type(&ty)?;
            Ok(ty)
        }
        Code::Fail(ref i) => {
            let ty = type_code(i, e)?;
            Expr::unify(ty, e.type_.clone())?;
            Ok(e.bot.clone())
        }
        Code::Cond(_, ref a, ref b, ref tr, ref fa) => {
            Expr::unify(type_code(a, e)?, type_code(b, e)?)?;
            Expr::unify(type_code(tr, e)?, type_code(fa, e)?)
        }
        Code::App(ref fn_name, ref args) => {
            let mut ty = e.ty(fn_name)?.clone();
            let arg_tys: Vec<_> = args
                .into_iter()
                .map(|a| type_code(a, e))
                .collect::<Result<Vec<_>, _>>()?;
            for a in arg_tys {
                if let &Expr::Pi {
                    ref dom,
                    ref rng,
                    ref var,
                } = ty.as_ref()
                {
                    Expr::unify(a.clone(), dom.clone())?;
                    ty = Expr::sub(&rng, var.as_ref().as_str(), &a);
                } else {
                    return Err(LfscError::UntypableApplication(ty.clone()));
                }
            }
            Ok(ty)
        }
        Code::Match(ref disc, ref cases) => {
            let disc_ty = type_code(disc, e)?;
            let tys = cases
                .into_iter()
                .map(|(pat, val)| {
                    match pat {
                        Pattern::Default => type_code(val, e),
                        Pattern::Const(ref n) => {
                            Expr::unify(e.ty(n)?.clone(), disc_ty.clone())?;
                            type_code(val, e)
                        }
                        Pattern::App(ref n, ref vars) => {
                            let mut ty = e.ty(n)?.clone();
                            let mut unbinds = Vec::new();
                            for v in vars {
                                if let Expr::Pi {
                                    ref dom, ref rng, ..
                                } = ty.as_ref()
                                {
                                    let o = e.bind_expr(
                                        v.clone(),
                                        Rc::new(Expr::Var(Rc::new(v.clone()))),
                                        dom.clone(),
                                    );
                                    // TODO check for non-dependence
                                    ty = rng.clone();
                                    unbinds.push((v.clone(), o));
                                } else {
                                    return Err(LfscError::NonPiPatternHead);
                                }
                            }
                            Expr::unify(ty, disc_ty.clone())?;
                            type_code(val, e)
                        }
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            same_types(tys.into_iter())
        }
    }
}

fn check_arg(ts: &mut Lexer, e: &mut Env) -> Result<(String, Rc<Expr>), LfscError> {
    let name = ts.consume_ident()?;
    let ty = cons_check(ts, e, e.type_.clone())?;
    ts.consume_tok(Token::Close)?;
    Ok((name, ty))
}

fn do_cmd(ts: &mut Lexer, e: &mut Env) -> Result<(), LfscError> {
    use Token::{Check, Declare, Define, Program};
    match ts.require_next()? {
        Declare => {
            let name = consume_var(ts)?;
            let (ty, kind) = cons_type(ts, e)?;
            if *kind != Expr::Type && *kind != Expr::Kind {
                return Err(LfscError::BadDeclare((*name).clone(), ty, kind));
            }
            e.bind_expr((*name).clone(), Rc::new(Expr::Var(name)), ty);
        }
        Define => {
            let name = consume_var(ts)?;
            let (val, ty) = cons_type(ts, e)?;
            e.bind_expr((*name).clone(), val, ty);
        }
        Program => {
            // It binds the program internally
            type_program(ts, e)?;
        }
        Check => {
            cons_type(ts, e)?;
        }
        _ => return Err(LfscError::NotACmd(ts.string())),
    }
    ts.consume_tok(Token::Close)?;
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
        //println!("Error {:#?}", e);
        println!("Error {}", e);
        //println!("Error");
    }
    Ok(())
}
