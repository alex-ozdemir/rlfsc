#![feature(move_ref_pattern)]

use logos::Logos;
use std::convert::{From, Into};
use std::default::Default;
use std::env::args;
use std::fs::read;
use std::rc::Rc;
use std::str::from_utf8;

mod code;
mod env;
mod error;
mod expr;
mod token;

use code::{parse_term, Code, MpCond, Pattern};
use env::{Env, EnvEntry, PgmEnvEntry};
use error::LfscError;
use expr::{Expr, Program};
use rug::Rational;
use token::{Lexer, Token};

fn consume_var(ts: &mut Lexer) -> Result<Rc<String>, LfscError> {
    Ok(Rc::new(ts.consume_ident()?))
}

fn cons_type_pi(ts: &mut Lexer, e: &mut Env) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let domain = cons_check(ts, e, e.type_.clone())?;
    let old_binding = e.bind_expr(
        (*var).clone(),
        Rc::new(Expr::new_var(var.clone())),
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
        Err(LfscError::InvalidPiRange((*range_ty).clone()))
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
    let sym = Rc::new(e.new_symbol((*var).clone()));
    let old_binding = e.bind_expr((*var).clone(), sym, ty);
    let (v, t) = cons_type(ts, e)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn run_code(e: &mut Env, code: &Code) -> Result<Rc<Expr>, LfscError> {
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
                code::Cond::Equal => Rc::into_raw(ll) == Rc::into_raw(rr),
                code::Cond::LessThan => Rc::into_raw(ll) < Rc::into_raw(rr),
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
                if let Expr::Run(ref term, ref expected, _) = **dom {
                    let res = run_code(e, term)?;
                    if e.unify(res.clone(), expected.clone()).is_err() {
                        return Err(LfscError::RunWrongResult(
                            (*res).clone(),
                            (**expected).clone(),
                        ));
                    }
                    ty = rng.clone();
                } else {
                    let arg = cons_check(ts, e, dom.clone())?;
                    ty = Expr::sub(rng, var, &arg);
                    args.push(arg);
                }
            }
            _ => return Err(LfscError::UntypableApplication((*ty).clone())),
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
        Token::Rational => Ok((Rc::new(Expr::RatLit(ts.rat())), Rc::new(Expr::RatTy))),
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
                ty.require_mp_ty()?;
                ts.consume_tok(Close)?;
                (Rc::new(t.mp_neg()?), ty)
            }),
            ReverseSolidus => Err(LfscError::UnascribedLambda),
            Ident => {
                let n = from_utf8(ts.slice()).unwrap().to_owned();
                cons_type_app(ts, e, n)
            }
            Caret => {
                let run_expr = parse_term(ts)?;
                let ty = type_code(&run_expr, e)?;
                let run_res = cons_check(ts, e, ty.clone())?;
                //let run_res = consume_var(ts)?;
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
    let r = match cons_type(ts, e) {
        Ok((val, ty)) => {
            let _t = e.unify(ty, ex_ty.clone())?;
            Ok(val)
        }
        Err(LfscError::UnascribedLambda) => match ex_ty.as_ref() {
            &Expr::Pi {
                ref dom,
                ref rng,
                ref var,
            } => {
                let act_var = consume_var(ts)?;
                let sym = Rc::new(e.new_symbol((*act_var).clone()));
                let new_expected = Expr::sub(rng, &var, &sym);
                let old_binding = e.bind_expr((*act_var).clone(), sym, dom.clone());
                let res = cons_check(ts, e, new_expected)?;
                ts.consume_tok(Token::Close)?;
                e.unbind(&act_var, old_binding);
                Ok(Rc::new(Expr::Pi {
                    var: var.clone(),
                    dom: dom.clone(),
                    rng: res,
                }))
            }
            t => Err(LfscError::InvalidLambdaType(t.clone())),
        },
        Err(e) => Err(e),
    };
    r
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
                    Rc::new(Expr::new_var(Rc::new(arg_name.clone()))),
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
        Rc::new(Expr::new_var(name.clone())),
        pgm_ty.clone(),
    );
    let body = parse_term(ts)?;
    let body_ty = type_code(&body, e)?;
    e.unify(body_ty, ret_ty.clone())?;
    for (n, ub) in unbinds {
        e.unbind(&n, ub);
    }
    let pgm = Program {
        args,
        ret_ty,
        body: Rc::new(body),
    };
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
            let c = type_code(&i, e)?;
            e.unify(e.nat.clone(), c)?;
            Ok(e.rat.clone())
        }
        Code::Let(ref name, ref val, ref body) => {
            let ty = type_code(val, e)?;
            let o = e.bind_expr(
                name.to_owned(),
                Rc::new(Expr::new_var(Rc::new(name.to_owned()))),
                ty,
            );
            let r = type_code(body, e)?;
            e.unbind(name, o);
            Ok(r)
        }
        Code::IfMarked(_, _, ref tr, ref fa) => {
            let a = type_code(tr, e)?;
            let b = type_code(fa, e)?;
            e.unify(a, b)
        }
        Code::Mark(_, ref v) => type_code(v, e),
        Code::Do(ref init, ref last) => {
            for i in init {
                type_code(i, e)?;
            }
            type_code(last, e)
        }
        Code::MpBin(_, ref a, ref b) => {
            let a = type_code(a, e)?;
            let b = type_code(b, e)?;
            let ty = e.unify(a, b)?;
            ty.require_mp_ty()?;
            Ok(ty)
        }
        Code::MpCond(_, ref c, ref tr, ref fa) => {
            type_code(c, e)?.require_mp_ty()?;
            let a = type_code(tr, e)?;
            let b = type_code(fa, e)?;
            e.unify(a, b)
        }
        Code::MpNeg(ref i) => {
            let ty = type_code(i, e)?;
            ty.require_mp_ty()?;
            Ok(ty)
        }
        Code::Fail(ref i) => {
            let ty = type_code(i, e)?;
            e.unify(ty, e.type_.clone())?;
            Ok(e.bot.clone())
        }
        Code::Cond(_, ref a, ref b, ref tr, ref fa) => {
            let a_ty = type_code(a, e)?;
            let b_ty = type_code(b, e)?;
            e.unify(a_ty, b_ty)?;
            let tr_ty = type_code(tr, e)?;
            let fa_ty = type_code(fa, e)?;
            e.unify(tr_ty, fa_ty)
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
                    e.unify(a.clone(), dom.clone())?;
                    ty = Expr::sub(&rng, var.as_ref().as_str(), &a);
                } else {
                    return Err(LfscError::UntypableApplication((*ty).clone()));
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
                            e.unify(e.ty(n)?.clone(), disc_ty.clone())?;
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
                                        Rc::new(Expr::new_var(Rc::new(v.clone()))),
                                        dom.clone(),
                                    );
                                    // TODO check for non-dependence
                                    ty = rng.clone();
                                    unbinds.push((v.clone(), o));
                                } else {
                                    return Err(LfscError::NonPiPatternHead);
                                }
                            }
                            e.unify(ty, disc_ty.clone())?;
                            type_code(val, e)
                        }
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            e.unify_all(tys.into_iter())
        }
        Code::Expr(_) => unimplemented!("Cannot type the expression for of code"),
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
                return Err(LfscError::BadDeclare(
                    (*name).clone(),
                    (*ty).clone(),
                    (*kind).clone(),
                ));
            }
            let sym = Rc::new(e.new_symbol((*name).clone()));
            e.bind_expr((*name).clone(), sym, ty);
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
        println!("Error {}", e);
    }
    Ok(())
}
