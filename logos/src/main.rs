#![feature(move_ref_pattern)]

use logos::Logos;
use std::convert::{From, Into};
use std::default::Default;
use std::env::args;
use std::fs::read;
use std::mem::drop;
use std::rc::Rc;

mod code;
mod env;
mod error;
mod expr;
mod token;

use code::{parse_term, run_code, type_code};
use env::{Consts, Env, EnvEntry, PgmEnvEntry};
use error::LfscError;
use expr::{Expr, Program, Var};
use token::{Lexer, Token};

fn consume_string(ts: &mut Lexer) -> Result<String, LfscError> {
    Ok(ts.consume_ident()?.to_owned())
}

fn consume_new_var(ts: &mut Lexer) -> Result<Rc<Var>, LfscError> {
    Ok(Rc::new(Var(ts.consume_ident()?.to_owned())))
}

fn consume_old_var<'a>(ts: &mut Lexer, e: &'a Env) -> Result<(&'a Rc<Var>, &'a Rc<Expr>), LfscError> {
    e.var_binding(ts.consume_ident()?)
}

fn cons_type_pi(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_new_var(ts)?;
    let (domain, _) = cons_type(ts, e, cs, Some(&cs.type_), true)?;
    let old_binding = e.bind_var(
        var.clone(),
        domain.clone(),
    );
    let (range, range_ty) = cons_type(ts, e, cs, None, true)?;
    ts.consume_tok(Token::Close)?;
    e.unbind_var(old_binding);
    // If there is only one reference to var now, then it must be free in the range.
    let dependent = Rc::strong_count(&var) > 1;
    if *range_ty == Expr::Type || *range_ty == Expr::Kind {
        Ok((
            Rc::new(Expr::Pi {
                var,
                dom: domain,
                rng: range,
                dependent,
            }),
            range_ty,
        ))
    } else {
        Err(LfscError::InvalidPiRange((*range_ty).clone()))
    }
}

fn cons_type_at(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_string(ts)?;
    let (val, ty) = cons_type(ts, e, cs, None, true)?;
    let old_binding = e.bind_expr(var.clone(), val, ty);
    let (v, t) = cons_type(ts, e, cs, None, true)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(&var, old_binding);
    Ok((v, t))
}

fn cons_type_ascription(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let ty = cons_type(ts, e, cs, Some(&cs.type_), true)?.0;
    let t = cons_type(ts, e, cs, Some(&ty), true)?.0;
    ts.consume_tok(Token::Close)?;
    Ok((t, ty))
}

fn cons_type_big_lambda(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    let var = consume_string(ts)?;
    let ty = cons_type(ts, e, cs, Some(&cs.type_), true)?.0;
    let sym = Rc::new(e.new_symbol(var.clone()));
    let old_binding = e.bind_expr(var.clone(), sym, ty);
    let (v, t) = cons_type(ts, e, cs, None, true)?;
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
                ref dependent,
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
                    let arg = cons_type(ts, e, cs, Some(dom), true)?.0;
                    ty = Expr::sub(rng, &var.0, &arg);
                    args.push(arg);
                }
            }
            _ => return Err(LfscError::UntypableApplication((*ty).clone())),
        }
    }
    ts.consume_tok(Token::Close)?;
    Ok((Rc::new(Expr::App(fun, args)), ty))
}

fn cons_type(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
    ex_ty: Option<&Rc<Expr>>,
    create: bool,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    use Token::*;
    let (ast, ty) = match ts.require_next()? {
        Token::Type => Ok((Rc::new(Expr::Type), Rc::new(Expr::Kind))),
        Token::Mpz => Ok((Rc::new(Expr::NatTy), Rc::new(Expr::Type))),
        Token::Mpq => Ok((Rc::new(Expr::RatTy), Rc::new(Expr::Type))),
        Token::Natural => Ok((Rc::new(Expr::NatLit(ts.nat())), Rc::new(Expr::NatTy))),
        Token::Rational => Ok((Rc::new(Expr::RatLit(ts.rat())), Rc::new(Expr::RatTy))),
        Token::Hole => Ok((Rc::new(Expr::new_hole()), Rc::new(Expr::new_hole()))),
        Ident => Ok(e.expr_binding(ts.str())?.clone().into()),
        Open => match ts.require_next()? {
            Bang => cons_type_pi(ts, e, cs),
            At => cons_type_at(ts, e, cs),
            Colon => cons_type_ascription(ts, e, cs),
            Percent => cons_type_big_lambda(ts, e, cs),
            Tilde => Ok({
                let (t, ty) = cons_type(ts, e, cs, None, true)?;
                ty.require_mp_ty()?;
                ts.consume_tok(Close)?;
                (Rc::new(t.mp_neg()?), ty)
            }),
            ReverseSolidus => match ex_ty.ok_or(LfscError::UnascribedLambda)?.as_ref() {
                &Expr::Pi {
                    ref dom,
                    ref rng,
                    ref var,
                    ref dependent,
                } => {
                    let act_var = consume_string(ts)?;
                    let sym = Rc::new(e.new_symbol(act_var.clone()));
                    let new_expected = Expr::sub(rng, &var.0, &sym);
                    let old_binding = e.bind_expr(act_var.clone(), sym, dom.clone());
                    let res = cons_type(ts, e, cs, Some(&new_expected), true)?.0;
                    ts.consume_tok(Token::Close)?;
                    e.unbind(&act_var, old_binding);
                    return Ok((
                        Rc::new(Expr::Pi {
                            var: var.clone(),
                            dom: dom.clone(),
                            rng: res,
                            dependent: *dependent,
                        }),
                        ex_ty.unwrap().clone(),
                    ))
                },
                t => Err(LfscError::InvalidLambdaType(t.clone())),
            },
            Ident => cons_type_app(ts, e, cs, ts.string()),
            Caret => {
                let run_expr = parse_term(ts)?;
                let ty = type_code(&run_expr, e, cs)?;
                let run_res = cons_type(ts, e, cs, Some(&ty), true)?.0;
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
    }?;
    match ex_ty {
        Some(ex_ty) => Ok((ast, e.unify(&ty, &ex_ty)?)),
        None => Ok((ast, ty)),
    }
}

fn type_program(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    let name = consume_string(ts)?;
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
                    Rc::new(Expr::new_var(arg_name.clone())),
                    arg_ty.clone(),
                );
                unbinds.push((arg_name.clone(), old));
                args.push((arg_name, arg_ty));
            }
            t => return Err(LfscError::UnexpectedToken("an argument", t)),
        }
    }
    let ret_ty = cons_type(ts, e, cs, Some(&cs.type_), true)?.0;
    let pgm_ty = args.iter().rev().fold(ret_ty.clone(), |x, (n, t)| {
        Rc::new(Expr::Pi {
            var: Rc::new(Var(n.clone())),
            rng: x,
            dom: t.clone(),
            dependent: false,
        })
    });
    e.bind_expr(
        name.clone(),
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
        name.clone(),
        EnvEntry::Program(PgmEnvEntry {
            val: pgm,
            ty: pgm_ty,
        }),
    );
    Ok(())
}

fn check_arg(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(String, Rc<Expr>), LfscError> {
    let name = ts.consume_ident()?;
    let ty = cons_type(ts, e, cs, Some(&cs.type_), true)?.0;
    ts.consume_tok(Token::Close)?;
    Ok((name.to_owned(), ty))
}

fn do_cmd(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    use Token::{Check, Declare, Define, Program};
    match ts.require_next()? {
        Declare => {
            let name = consume_string(ts)?;
            let (ty, kind) = cons_type(ts, e, cs, None, true)?;
            if *kind != Expr::Type && *kind != Expr::Kind {
                return Err(LfscError::BadDeclare(
                    name.clone(),
                    (*ty).clone(),
                    (*kind).clone(),
                ));
            }
            let sym = Rc::new(e.new_symbol(name.clone()));
            e.bind_expr(name.clone(), sym, ty);
        }
        Define => {
            let name = consume_string(ts)?;
            let (val, ty) = cons_type(ts, e, cs, None, true)?;
            e.bind_expr(name.clone(), val, ty);
        }
        Program => {
            // It binds the program internally
            type_program(ts, e, cs)?;
        }
        Check => {
            cons_type(ts, e, cs, None, true)?;
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
