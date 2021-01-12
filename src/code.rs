use std::cell::RefCell;
use std::convert::From;
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;
use std::str::FromStr;

use rug::{Integer, Rational};

use crate::env::{Consts, Env};
use crate::error::LfscError;
use crate::expr::{Expr, Ref};
use crate::expr_check::check_expr;
use crate::token::{Lexer, Token};

macro_rules! try_ {
    ($e:expr) => {
        match $e {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Binding {
    Var(Rc<Ref>),
    Hole,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Default,
    App(Rc<Expr>, Vec<Binding>),
    Const(Rc<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Code {
    Match(Box<Code>, Vec<(Pattern, Code)>),
    Let(Rc<Ref>, Box<Code>, Box<Code>),
    IfMarked(u8, Box<Code>, Box<Code>, Box<Code>),
    Mark(u8, Box<Code>),
    Do(Vec<Code>, Box<Code>),
    MpBin(MpBinOp, Box<Code>, Box<Code>),
    MpCond(MpCond, Box<Code>, Box<Code>, Box<Code>),
    MpNeg(Box<Code>),
    Fail(Box<Code>),
    Cond(Cond, Box<Code>, Box<Code>, Box<Code>, Box<Code>),
    NatToRat(Box<Code>),
    NatLit(Integer),
    RatLit(Rational),
    App(Rc<Expr>, Vec<Code>),
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
            &Code::App(ref f, ref args) => Code::App(
                Expr::sub(f, name, value),
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

fn consume_new_binding<'a, L: Lexer<'a>>(ts: &mut L) -> Result<Binding, LfscError> {
    let t = ts.require_next()?;
    match t.tok {
        Token::Hole => Ok(Binding::Hole),
        Token::Ident => Ok(Binding::Var(Rc::new(Ref::new(t.str().to_owned())))),
        t => Err(LfscError::WrongToken(Token::Ident, t)),
    }
}

fn consume_new_ref<'a, L: Lexer<'a>>(ts: &mut L) -> Result<Rc<Ref>, LfscError> {
    Ok(Rc::new(Ref::new(try_!(ts.consume_ident()).to_owned())))
}

pub fn parse_term<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
) -> Result<Code, LfscError> {
    use Token::*;
    let t = ts.require_next()?;
    match t.tok {
        Ident => Ok(Code::Expr(e.expr_value(t.str())?.clone())),
        Natural => Ok(Code::NatLit(t.nat())),
        Rational => Ok(Code::RatLit(t.rat())),
        Open => {
            let nxt = ts.require_next()?;
            let r = match nxt.tok {
                Do => {
                    let mut terms = Vec::new();
                    while Some(Close) != ts.peek_token() {
                        terms.push(parse_term(ts, e, cs)?);
                    }
                    if let Some(last) = terms.pop() {
                        Ok(Code::Do(terms, Box::new(last)))
                    } else {
                        Err(LfscError::EmptyDo)
                    }
                }
                Match => {
                    let disc = parse_term(ts, e, cs)?;
                    let mut cases = Vec::new();
                    while Some(Close) != ts.peek_token() {
                        cases.push(parse_case(ts, e, cs)?);
                    }
                    if cases.len() == 0 {
                        Err(LfscError::EmptyMatch)
                    } else {
                        Ok(Code::Match(Box::new(disc), cases))
                    }
                }
                Fail => Ok(Code::Fail(Box::new(parse_term(ts, e, cs)?))),
                MpAdd | MpMul | MpDiv => Ok(Code::MpBin(
                    MpBinOp::from(nxt.tok),
                    Box::new(parse_term(ts, e, cs)?),
                    Box::new(parse_term(ts, e, cs)?),
                )),
                MpNeg | Tilde => Ok(Code::MpNeg(Box::new(parse_term(ts, e, cs)?))),
                MpIfNeg | MpIfZero => Ok(Code::MpCond(
                    MpCond::from(nxt.tok),
                    Box::new(parse_term(ts, e, cs)?),
                    Box::new(parse_term(ts, e, cs)?),
                    Box::new(parse_term(ts, e, cs)?),
                )),
                MpzToMpq => Ok(Code::NatToRat(Box::new(parse_term(ts, e, cs)?))),
                IfEqual | Compare => Ok(Code::Cond(
                    Cond::from(nxt.tok),
                    Box::new(parse_term(ts, e, cs)?),
                    Box::new(parse_term(ts, e, cs)?),
                    Box::new(parse_term(ts, e, cs)?),
                    Box::new(parse_term(ts, e, cs)?),
                )),
                At => {
                    let n = consume_new_ref(ts)?;
                    let name = n.name.clone();
                    let ref_ = Rc::new(Expr::Ref(n.clone()));
                    let v = Box::new(parse_term(ts, e, cs)?);
                    let o = e.bind(name, ref_.clone(), cs.bot.clone());
                    let body = Box::new(parse_term(ts, e, cs)?);
                    e.unbind(o);
                    Ok(Code::Let(n, v, body))
                }
                IfMarked => {
                    let n = if let "ifmarked" = nxt.str() {
                        1
                    } else {
                        u8::from_str(&nxt.str()["ifmarked".len()..]).unwrap()
                    };
                    Ok(Code::IfMarked(
                        n,
                        Box::new(parse_term(ts, e, cs)?),
                        Box::new(parse_term(ts, e, cs)?),
                        Box::new(parse_term(ts, e, cs)?),
                    ))
                }
                MarkVar => {
                    let n = if let "markvar" = nxt.str() {
                        1
                    } else {
                        u8::from_str(&nxt.str()["markvar".len()..]).unwrap()
                    };
                    Ok(Code::Mark(n, Box::new(parse_term(ts, e, cs)?)))
                }
                Ident => {
                    // TODO(aozdemir) Lookup fun_name
                    let fun_name = nxt.str();
                    let fun = e.expr_value(fun_name)?.clone();
                    let mut args = Vec::new();
                    while Some(Token::Close) != ts.peek_token() {
                        args.push(parse_term(ts, e, cs)?);
                    }
                    Ok(Code::App(fun, args))
                }
                t => Err(LfscError::UnexpectedToken("term head", t)),
            }?;
            ts.consume_tok(Token::Close)?;
            Ok(r)
        }
        t => Err(LfscError::UnexpectedToken("term", t)),
    }
}

fn parse_case<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Pattern, Code), LfscError> {
    ts.consume_tok(Token::Open)?;
    let t = ts.require_next()?;
    let r = match t.tok {
        Token::Open => {
            let fun = e.expr_value(ts.consume_ident()?)?.clone();
            let mut bindings = Vec::new();
            while Some(Token::Close) != ts.peek_token() {
                bindings.push(consume_new_binding(ts)?);
            }
            ts.consume_tok(Token::Close)?;
            let os = bindings
                .iter()
                .filter_map(|v| {
                    if let Binding::Var(v) = v {
                        Some(e.bind(
                            v.name.clone(),
                            Rc::new(Expr::Ref(v.clone())),
                            cs.bot.clone(),
                        ))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            let r = Pattern::App(fun, bindings);
            let t = parse_term(ts, e, cs)?;
            for o in os {
                e.unbind(o);
            }
            Ok((r, t))
        }
        Token::Ident => Ok((
            Pattern::Const(e.expr_value(t.str())?.clone()),
            parse_term(ts, e, cs)?,
        )),
        Token::Default => Ok((Pattern::Default, parse_term(ts, e, cs)?)),
        t => Err(LfscError::UnexpectedToken("case", t)),
    }?;
    ts.consume_tok(Token::Close)?;
    Ok(r)
}

impl Display for Binding {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Binding::Hole => write!(f, "_"),
            Binding::Var(v) => write!(f, "{}", v),
        }
    }
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

pub fn run_code(e: &mut Env, cs: &Consts, code: &Code) -> Result<Rc<Expr>, LfscError> {
    if cs.trace_sc {
        for _ in 0..e.sc_depth {
            print!(" ");
        }
        println!("run [ {}", code);
        e.sc_depth += 1;
    }
    let r = try_!(match code {
        Code::App(ref fun, ref arg_terms) => {
            let args = try_!(arg_terms
                .iter()
                .map(|a| run_code(e, cs, a))
                .collect::<Result<Vec<_>, _>>());
            match fun.as_ref() {
                Expr::Program(pgm) => {
                    let formal_args = pgm.args.clone();
                    let body = pgm.body.borrow();
                    if formal_args.len() == args.len() {
                        let unbinds: Vec<_> = formal_args
                            .iter()
                            .zip(args.iter())
                            .map(|((ref_, _), a)| ref_.val.replace(Some(a.clone())))
                            .collect();
                        let r = try_!(run_code(e, cs, &body));
                        for (u, (n, _)) in unbinds.into_iter().zip(formal_args.into_iter()) {
                            n.val.replace(u);
                        }
                        Ok(r)
                    } else {
                        Err(LfscError::WrongNumberOfArgs(
                            (**fun).clone(),
                            formal_args.len(),
                            args.len(),
                        ))
                    }
                }
                _ => Ok(Rc::new(Expr::App(fun.clone(), args))),
            }
        }
        Code::NatLit(i) => Ok(Rc::new(Expr::NatLit(i.clone()))),
        Code::RatLit(r) => Ok(Rc::new(Expr::RatLit(r.clone()))),
        Code::Do(xs, y) => {
            for x in xs {
                try_!(run_code(e, cs, x));
            }
            run_code(e, cs, y)
        }
        Code::Let(n, v, body) => {
            let vv = try_!(run_code(e, cs, v));
            let o = n.val.replace(Some(vv));
            let r = try_!(run_code(e, cs, body));
            n.val.replace(o);
            Ok(r)
        }
        Code::Cond(c, l, r, t, f) => {
            let ll = Expr::weak_head_reduce(Expr::deref(try_!(run_code(e, cs, l))));
            let rr = Expr::weak_head_reduce(Expr::deref(try_!(run_code(e, cs, r))));
            if match c {
                Cond::Equal => Rc::into_raw(ll) == Rc::into_raw(rr),
                Cond::LessThan => Rc::into_raw(ll) < Rc::into_raw(rr),
            } {
                run_code(e, cs, t)
            } else {
                run_code(e, cs, f)
            }
        }
        Code::NatToRat(i) => match try_!(run_code(e, cs, i)).as_ref() {
            Expr::NatLit(x) => Ok(Rc::new(Expr::RatLit(Rational::new() + x))),
            x => Err(LfscError::NotMpzInMpzToMpq((*x).clone())),
        },
        Code::Fail(i) => Err(LfscError::Fail((*try_!(run_code(e, cs, i))).clone())),
        Code::MpNeg(i) => try_!(run_code(e, cs, i)).as_ref().mp_neg().map(Rc::new),
        Code::MpBin(o, i, j) => try_!(run_code(e, cs, i))
            .as_ref()
            .mp_bin(*o, try_!(run_code(e, cs, j)).as_ref())
            .map(Rc::new),
        Code::MpCond(o, i, j, k) => {
            match Expr::weak_head_reduce(Expr::deref(try_!(run_code(e, cs, i)))).as_ref() {
                Expr::NatLit(ref x) => {
                    if match o {
                        MpCond::Neg => x < &(0 as u64),
                        MpCond::Zero => x == &(0 as u64),
                    } {
                        run_code(e, cs, j)
                    } else {
                        run_code(e, cs, k)
                    }
                }
                Expr::RatLit(ref x) => {
                    if match o {
                        MpCond::Neg => x < &(0 as u64),
                        MpCond::Zero => x == &(0 as u64),
                    } {
                        run_code(e, cs, j)
                    } else {
                        run_code(e, cs, k)
                    }
                }
                t => Err(LfscError::NotMpInMpCond(*o, t.clone())),
            }
        }
        Code::Match(disc, cases) => {
            let d = Expr::weak_head_reduce(Expr::deref_holes(try_!(run_code(e, cs, disc))));
            let mut ret = None;
            for (pat, v) in cases.iter() {
                match pat {
                    Pattern::Default => {
                        ret = Some(run_code(e, cs, v));
                        break;
                    }
                    Pattern::Const(s) => {
                        if Expr::unify_test(s, &d) {
                            ret = Some(run_code(e, cs, v));
                            break;
                        }
                    }
                    Pattern::App(phead, vars) => {
                        if let Expr::App(dhead, dargs) = d.as_ref() {
                            if Expr::unify_test(phead, dhead) {
                                if dargs.len() == vars.len() {
                                    let unbinds: Vec<_> = vars
                                        .iter()
                                        .zip(dargs.iter())
                                        .filter_map(|(ref_, a)| match ref_ {
                                            Binding::Var(var) => {
                                                Some((var, var.val.replace(Some(a.clone()))))
                                            }
                                            Binding::Hole => None,
                                        })
                                        .collect();
                                    let r = try_!(run_code(e, cs, v));
                                    for (n, u) in unbinds.into_iter() {
                                        n.val.replace(u);
                                    }
                                    ret = Some(Ok(r));
                                    break;
                                } else {
                                    ret = Some(Err(LfscError::WrongBindingCount(
                                        (*d).clone(),
                                        dargs.len(),
                                        vars.len(),
                                        pat.clone(),
                                    )));
                                }
                            }
                        }
                    }
                }
            }
            ret.unwrap_or_else(|| {
                Err(LfscError::NoPattern(
                    (*d).clone(),
                    cases.iter().map(|(p, _)| p.clone()).collect(),
                ))
            })
        }
        Code::Mark(n, i) => {
            let v = try_!(run_code(e, cs, i));
            e.toggle_mark(v.clone(), *n)
        }
        Code::IfMarked(n, c, t, f) => {
            let cond = try_!(run_code(e, cs, c));
            if try_!(e.get_mark(cond, *n)) {
                run_code(e, cs, t)
            } else {
                run_code(e, cs, f)
            }
        }
        Code::Expr(ex) => {
            let r = Expr::deref(ex.clone());
            match r.as_ref() {
                &Expr::Hole(_) => Err(LfscError::UnfilledHole),
                _ => Ok(r),
            }
        }
    });
    if cs.trace_sc {
        e.sc_depth -= 1;
        for _ in 0..e.sc_depth {
            print!(" ");
        }
        println!("ret ] {}", r);
    }
    Ok(r)
}

pub fn type_code(t: &Code, e: &mut Env, cs: &Consts) -> Result<Rc<Expr>, LfscError> {
    let r = match t {
        Code::NatLit(_) => Ok(cs.nat.clone()),
        Code::RatLit(..) => Ok(cs.rat.clone()),
        Code::NatToRat(ref i) => {
            let c = type_code(&i, e, cs)?;
            e.unify(&cs.nat, &c)?;
            Ok(cs.rat.clone())
        }
        Code::Let(ref name, ref val, ref body) => {
            let ty = type_code(val, e, cs)?;
            let o = e.bind(name.name.clone(), cs.bot.clone(), ty);
            let r = type_code(body, e, cs)?;
            e.unbind(o);
            Ok(r)
        }
        Code::IfMarked(_, _, ref tr, ref fa) => {
            let a = type_code(tr, e, cs)?;
            let b = type_code(fa, e, cs)?;
            e.unify(&a, &b)
        }
        Code::Mark(_, ref v) => type_code(v, e, cs),
        Code::Do(ref init, ref last) => {
            for i in init {
                type_code(i, e, cs)?;
            }
            type_code(last, e, cs)
        }
        Code::MpBin(_, ref a, ref b) => {
            let a = type_code(a, e, cs)?;
            let b = type_code(b, e, cs)?;
            let ty = e.unify(&a, &b)?;
            ty.require_mp_ty()?;
            Ok(ty)
        }
        Code::MpCond(_, ref c, ref tr, ref fa) => {
            type_code(c, e, cs)?.require_mp_ty()?;
            let a = type_code(tr, e, cs)?;
            let b = type_code(fa, e, cs)?;
            e.unify(&a, &b)
        }
        Code::MpNeg(ref i) => {
            let ty = type_code(i, e, cs)?;
            ty.require_mp_ty()?;
            Ok(ty)
        }
        Code::Fail(ref i) => run_code(e, cs, i),
        Code::Cond(_, ref a, ref b, ref tr, ref fa) => {
            let a_ty = type_code(a, e, cs)?;
            let b_ty = type_code(b, e, cs)?;
            e.unify(&a_ty, &b_ty)?;
            let tr_ty = type_code(tr, e, cs)?;
            let fa_ty = type_code(fa, e, cs)?;
            e.unify(&tr_ty, &fa_ty)
        }
        Code::App(ref fun, ref args) => {
            let mut ty = check_expr(fun, e, cs)?;
            let arg_tys: Vec<_> = args
                .into_iter()
                .map(|a| type_code(a, e, cs))
                .collect::<Result<Vec<_>, _>>()?;
            for (aty, a) in arg_tys.into_iter().zip(args.iter()) {
                if let &Expr::Pi {
                    ref dom,
                    ref rng,
                    ref var,
                    ref dependent,
                } = ty.as_ref()
                {
                    e.unify(&aty, dom)?;
                    ty = if *dependent {
                        Expr::sub(rng, &var.name, &run_code(e, cs, a)?)
                    } else {
                        rng.clone()
                    };
                } else {
                    return Err(LfscError::UntypableApplication((*ty).clone()));
                }
            }
            Ok(ty)
        }
        Code::Match(ref disc, ref cases) => {
            let disc_ty = type_code(disc, e, cs)?;
            let tys = cases
                .into_iter()
                .map(|(pat, val)| {
                    match pat {
                        Pattern::Default => type_code(val, e, cs),
                        Pattern::Const(ref n) => {
                            let n_ty = check_expr(n, e, cs)?;
                            e.unify(&n_ty, &disc_ty)?;
                            type_code(val, e, cs)
                        }
                        Pattern::App(ref n, ref vars) => {
                            let mut ty = check_expr(n, e, cs)?;
                            let mut unbinds = Vec::new();
                            for v in vars {
                                if let Expr::Pi {
                                    ref dom,
                                    ref rng,
                                    ref dependent,
                                    ref var,
                                } = ty.as_ref()
                                {
                                    let expr = match v {
                                        Binding::Var(v) => {
                                            let expr = Rc::new(Expr::Ref(Rc::new(Ref::new(
                                                v.name.clone(),
                                            ))));
                                            let o =
                                                e.bind(v.name.clone(), expr.clone(), dom.clone());
                                            // TODO check for non-dependence
                                            unbinds.push(o);
                                            expr
                                        }
                                        Binding::Hole => Rc::new(Expr::Hole(RefCell::new(None))),
                                    };
                                    ty = if *dependent {
                                        Expr::sub(rng, &var.name, &expr)
                                    } else {
                                        rng.clone()
                                    };
                                } else {
                                    return Err(LfscError::NonPiPatternHead);
                                }
                            }
                            e.unify(&ty, &disc_ty)?;
                            let r = type_code(val, e, cs)?;
                            for u in unbinds {
                                e.unbind(u);
                            }
                            Ok(r)
                        }
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            e.unify_all(tys.into_iter())
        }
        Code::Expr(expr) => match expr.as_ref().name() {
            Ok(n) => Ok(e.ty(n)?.clone()),
            Err(_) => unimplemented!("Check {} in code", expr),
        },
    }?;
    Ok(r)
}
