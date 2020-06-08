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

use code::{parse_term, run_code, type_code};
use env::{Env, EnvEntry, PgmEnvEntry, Consts};
use error::LfscError;
use expr::{Expr, Program};
use token::{Lexer, Token};



fn consume_var(ts: &mut Lexer) -> Result<Rc<String>, LfscError> {
    Ok(Rc::new(ts.consume_ident()?))
}

fn cons_type_pi(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let domain = cons_check(ts, e, cs, &cs.type_)?;
    let old_binding = e.bind_expr(
        (*var).clone(),
        Rc::new(Expr::new_var(var.clone())),
        domain.clone(),
    );
    let (range, range_ty) = cons_type(ts, e, cs)?;
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

fn cons_type_at(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let (val, ty) = cons_type(ts, e, cs)?;
    let old_binding = e.bind_expr((*var).clone(), val, ty);
    let (v, t) = cons_type(ts, e, cs)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn cons_type_ascription(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let ty = cons_check(ts, e, cs, &cs.type_)?;
    let t = cons_check(ts, e, cs, &ty)?;
    ts.consume_tok(Token::Close)?;
    Ok((t, ty))
}

fn cons_type_big_lambda(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_var(ts)?;
    let ty = cons_check(ts, e, cs, &cs.type_)?;
    let sym = Rc::new(e.new_symbol((*var).clone()));
    let old_binding = e.bind_expr((*var).clone(), sym, ty);
    let (v, t) = cons_type(ts, e, cs)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn cons_type_app(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
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
                    let res = run_code(e, cs, term)?;
                    if e.unify(&res, expected).is_err() {
                        return Err(LfscError::RunWrongResult(
                            (*res).clone(),
                            (**expected).clone(),
                        ));
                    }
                    ty = rng.clone();
                } else {
                    let arg = cons_check(ts, e, cs, dom)?;
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

fn cons_type(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
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
            Bang => cons_type_pi(ts, e, cs),
            At => cons_type_at(ts, e, cs),
            Colon => cons_type_ascription(ts, e, cs),
            Percent => cons_type_big_lambda(ts, e, cs),
            Tilde => Ok({
                let (t, ty) = cons_type(ts, e, cs)?;
                ty.require_mp_ty()?;
                ts.consume_tok(Close)?;
                (Rc::new(t.mp_neg()?), ty)
            }),
            ReverseSolidus => Err(LfscError::UnascribedLambda),
            Ident => {
                let n = from_utf8(ts.slice()).unwrap().to_owned();
                cons_type_app(ts, e, cs, n)
            }
            Caret => {
                let run_expr = parse_term(ts)?;
                let ty = type_code(&run_expr, e, cs)?;
                let run_res = cons_check(ts, e, cs, &ty)?;
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

fn cons_check(ts: &mut Lexer, e: &mut Env, cs: &Consts, ex_ty: &Rc<Expr>) -> Result<Rc<Expr>, LfscError> {
    let r = match cons_type(ts, e, cs) {
        Ok((val, ty)) => {
            let _t = e.unify(&ty, ex_ty)?;
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
                let res = cons_check(ts, e, cs, &new_expected)?;
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

fn type_program(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    let name = consume_var(ts)?;
    ts.consume_tok(Token::Open)?;
    let mut args = Vec::new();
    let mut unbinds = Vec::new();
    loop {
        match ts.require_next()? {
            Token::Close => break,
            Token::Open => {
                let (arg_name, arg_ty) = check_arg(ts, e, cs)?;
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
    let ret_ty = cons_check(ts, e, cs, &cs.type_)?;
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
    let body_ty = type_code(&body, e, cs)?;
    e.unify(&body_ty, &ret_ty)?;
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

fn check_arg(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(String, Rc<Expr>), LfscError> {
    let name = ts.consume_ident()?;
    let ty = cons_check(ts, e, cs, &cs.type_)?;
    ts.consume_tok(Token::Close)?;
    Ok((name, ty))
}

fn do_cmd(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    use Token::{Check, Declare, Define, Program};
    match ts.require_next()? {
        Declare => {
            let name = consume_var(ts)?;
            let (ty, kind) = cons_type(ts, e, cs)?;
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
            let (val, ty) = cons_type(ts, e, cs)?;
            e.bind_expr((*name).clone(), val, ty);
        }
        Program => {
            // It binds the program internally
            type_program(ts, e, cs)?;
        }
        Check => {
            cons_type(ts, e, cs)?;
        }
        _ => return Err(LfscError::NotACmd(ts.string())),
    }
    ts.consume_tok(Token::Close)?;
    Ok(())
}

fn do_cmds(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    while let Some(t) = ts.next() {
        match t {
            Token::Open => do_cmd(ts, e, cs)?,
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
    let consts = Consts::default();
    //    do_cmds(&mut lexer, &mut env)?;
    if let Err(e) = do_cmds(&mut lexer, &mut env, &consts) {
        println!("Error {}", e);
    }
    Ok(())
}
