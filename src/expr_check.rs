use std::cell::RefCell;
use std::rc::Rc;

use crate::code::{parse_term, run_code, type_code, Code};
use crate::env::{Consts, Env};
use crate::error::LfscError;
use crate::expr::{Expr, Program, Ref};
use crate::token::{Lexer, Token};

fn consume_new_ref<'a, L: Lexer<'a>>(ts: &mut L) -> Result<Rc<Ref>, LfscError> {
    Ok(Rc::new(Ref::new(ts.consume_ident()?.to_owned())))
}

fn check_ann_lambda<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let var = consume_new_ref(ts)?;
    let (domain, _) = check_create(ts, e, cs, Some(&cs.type_))?;
    let old_binding = e.bind(
        var.name.clone(),
        Rc::new(Expr::Ref(var.clone())),
        domain.clone(),
    );
    let (range, range_ty) = check(ts, e, cs, None, create)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(old_binding);
    // TODO: assert that var is not bound in range_ty.
    Ok((
        if create {
            // If there is only one reference to var now, then it must be free in the range.
            Some(Rc::new(Expr::Pi {
                var: var.clone(),
                dom: domain.clone(),
                rng: range.unwrap(),
                dependent: false,
            }))
        } else {
            None
        },
        Rc::new(Expr::Pi {
            var,
            dom: domain,
            rng: range_ty,
            dependent: false,
        }),
    ))
}

fn check_pi<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let var = consume_new_ref(ts)?;
    let (domain, _) = check_create(ts, e, cs, Some(&cs.type_))?;
    let old_binding = e.bind(
        var.name.clone(),
        Rc::new(Expr::Ref(var.clone())),
        domain.clone(),
    );
    let (range, range_ty) = check(ts, e, cs, None, create)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(old_binding);
    if *range_ty == Expr::Type || *range_ty == Expr::Kind {
        Ok((
            if create {
                // If there is only one reference to var now, then it must be free in the range.
                let dependent = Rc::strong_count(&var) > 1;
                Some(Rc::new(Expr::Pi {
                    var,
                    dom: domain,
                    rng: range.unwrap(),
                    dependent,
                }))
            } else {
                None
            },
            range_ty,
        ))
    } else {
        Err(LfscError::InvalidPiRange((*range_ty).clone()))
    }
}

fn check_let<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let name = ts.consume_ident()?.to_owned();
    let (val, ty) = check_create(ts, e, cs, None)?;
    let old_binding = e.bind(name, val, ty);
    let (v, t) = check(ts, e, cs, None, create)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(old_binding);
    Ok((v, t))
}

fn check_ascription<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let ty = check_create(ts, e, cs, Some(&cs.type_))?.0;
    let t = check(ts, e, cs, Some(&ty), create)?.0;
    ts.consume_tok(Token::Close)?;
    Ok((t, ty))
}

fn check_big_lambda<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let var = ts.consume_ident()?.to_owned();
    let ty = check_create(ts, e, cs, Some(&cs.type_))?.0;
    let sym = Rc::new(e.new_symbol(var.clone()));
    let old_binding = e.bind(var, sym, ty);
    let (v, t) = check(ts, e, cs, None, create)?;
    ts.consume_tok(Token::Close)?;
    e.unbind(old_binding);
    Ok((v, t))
}

fn check_app<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    name: String,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let b = e.expr_binding(&name)?;
    let fun = b.val.clone();
    let mut ty = b.ty.clone();
    let mut args = Vec::new();
    let mut nargs = 0;

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
                    let arg = check(ts, e, cs, Some(dom), create || *dependent)?.0;
                    ty = if *dependent {
                        Expr::sub(rng, &var.name, arg.as_ref().unwrap())
                    } else {
                        rng.clone()
                    };
                    if create {
                        args.push(arg.unwrap());
                    }
                }
            }
            _ => return Err(LfscError::TooManyArgsToIdent(name, nargs, (*ty).clone())),
        }
        nargs += 1;
    }
    ts.consume_tok(Token::Close)?;
    Ok((
        if create {
            Some(Rc::new(Expr::App(fun, args)))
        } else {
            None
        },
        ty,
    ))
}

pub fn check_create<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    ex_ty: Option<&Rc<Expr>>,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    check(ts, e, cs, ex_ty, true).map(|(a, b)| (a.unwrap(), b))
}

pub fn check<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    ex_ty: Option<&Rc<Expr>>,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    use Token::*;
    let (ast, ty) = match ts.require_next()? {
        Token::Type => Ok((Some(cs.type_.clone()), cs.kind.clone())),
        Token::Mpz => Ok((Some(cs.nat.clone()), cs.type_.clone())),
        Token::Mpq => Ok((Some(cs.rat.clone()), cs.type_.clone())),
        Token::Natural => Ok((Some(Rc::new(Expr::NatLit(ts.nat()))), cs.nat.clone())),
        Token::Rational => Ok((Some(Rc::new(Expr::RatLit(ts.rat()))), cs.rat.clone())),
        Token::Hole => Ok((Some(Rc::new(Expr::new_hole())), Rc::new(Expr::new_hole()))),
        Ident => Ok({
            let res = e.expr_binding(ts.str())?;
            if create {
                (Some(res.val.clone()), res.ty.clone())
            } else {
                (None, res.ty.clone())
            }
        }),
        Open => match ts.require_next()? {
            Bang => check_pi(ts, e, cs, create),
            Pound => check_ann_lambda(ts, e, cs, create),
            At => check_let(ts, e, cs, create),
            Colon => check_ascription(ts, e, cs, create),
            Percent => check_big_lambda(ts, e, cs, create),
            Tilde => Ok({
                let (t, ty) = check(ts, e, cs, None, create)?;
                ty.require_mp_ty()?;
                ts.consume_tok(Close)?;
                if create {
                    (Some(Rc::new(t.unwrap().mp_neg()?)), ty)
                } else {
                    (None, ty)
                }
            }),
            ReverseSolidus => match ex_ty.ok_or(LfscError::UnascribedLambda)?.as_ref() {
                &Expr::Pi {
                    ref dom,
                    ref rng,
                    ref var,
                    ref dependent,
                } => {
                    let act_var = ts.consume_ident()?.to_owned();
                    let sym = Rc::new(e.new_symbol(act_var.clone()));
                    let new_expected = Expr::sub(rng, &var.name, &sym);
                    let old_binding = e.bind(act_var, sym, dom.clone());
                    let res = check(ts, e, cs, Some(&new_expected), create)?.0;
                    ts.consume_tok(Token::Close)?;
                    e.unbind(old_binding);
                    return Ok((
                        if create {
                            Some(Rc::new(Expr::Pi {
                                var: var.clone(),
                                dom: dom.clone(),
                                rng: res.unwrap(),
                                dependent: *dependent,
                            }))
                        } else {
                            None
                        },
                        ex_ty.unwrap().clone(),
                    ));
                }
                t => Err(LfscError::InvalidLambdaType(t.clone())),
            },
            Ident => check_app(ts, e, cs, ts.string(), create),
            Caret => {
                let run_expr = parse_term(ts, e, cs)?;
                let ty = type_code(&run_expr, e, cs)?;
                let run_res = check_create(ts, e, cs, Some(&ty))?.0;
                //let run_res = consume_var(ts)?;
                ts.consume_tok(Close)?;
                Ok((
                    Some(Rc::new(Expr::Run(run_expr, run_res, ty))),
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

pub fn check_program<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
) -> Result<(), LfscError> {
    let name = ts.consume_ident()?.to_owned();
    ts.consume_tok(Token::Open)?;
    let mut args = Vec::new();
    let mut unbinds = Vec::new();
    loop {
        match ts.require_next()? {
            Token::Close => break,
            Token::Open => {
                let (arg_ref, arg_ty) = check_arg(ts, e, cs)?;
                let old = e.bind(
                    arg_ref.name.clone(),
                    Rc::new(Expr::Ref(arg_ref.clone())),
                    arg_ty.clone(),
                );
                unbinds.push(old);
                args.push((arg_ref, arg_ty));
            }
            t => return Err(LfscError::UnexpectedToken("an argument", t)),
        }
    }
    let ret_ty = check_create(ts, e, cs, Some(&cs.type_))?.0;
    let pgm_ty = args.iter().rev().fold(ret_ty.clone(), |x, (n, t)| {
        let dependent = x.free_vars().contains(&n.name);
        Rc::new(Expr::Pi {
            var: n.clone(),
            rng: x,
            dom: t.clone(),
            dependent,
        })
    });
    e.bind(
        name.clone(),
        Rc::new(Expr::Program(Program {
            name: name.clone(),
            args,
            ret_ty: ret_ty.clone(),
            body: RefCell::new(Code::NatLit(rug::Integer::new())),
        })),
        pgm_ty.clone(),
    );
    let body = parse_term(ts, e, cs)?;
    let body_ty = type_code(&body, e, cs)?;
    e.unify(&body_ty, &ret_ty)?;
    for u in unbinds {
        e.unbind(u);
    }
    if let Expr::Program(pgm) = e.expr_value(&name)?.as_ref() {
        pgm.body.replace(body);
    } else {
        unreachable!()
    }
    Ok(())
}

fn check_arg<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Rc<Ref>, Rc<Expr>), LfscError> {
    let name = consume_new_ref(ts)?;
    let ty = check_create(ts, e, cs, Some(&cs.type_))?.0;
    ts.consume_tok(Token::Close)?;
    Ok((name, ty))
}

pub fn check_expr(expr: &Rc<Expr>, env: &mut Env, cs: &Consts) -> Result<Rc<Expr>, LfscError> {
    let r = match expr.as_ref() {
        Expr::Bot => Ok(cs.bot.clone()),
        Expr::Type => Ok(cs.kind.clone()),
        Expr::Kind => Err(LfscError::CannotTypeKind),
        Expr::NatTy => Ok(cs.type_.clone()),
        Expr::NatLit(_) => Ok(cs.nat.clone()),
        Expr::RatTy => Ok(cs.type_.clone()),
        Expr::RatLit(_) => Ok(cs.rat.clone()),
        Expr::Run(..) => Ok(cs.type_.clone()),
        // TODO: perhaps we should check here?
        Expr::App(h, args) => {
            let mut h_ty = check_expr(h, env, cs)?;
            for a in args {
                match h_ty.as_ref() {
                    &Expr::Pi {
                        ref dom,
                        ref rng,
                        ref var,
                        ref dependent,
                    } => {
                        if let Expr::Run(ref term, ref expected, _) = **dom {
                            let res = run_code(env, cs, term)?;
                            if env.unify(&res, expected).is_err() {
                                return Err(LfscError::RunWrongResult(
                                    (*res).clone(),
                                    (**expected).clone(),
                                ));
                            }
                            h_ty = rng.clone();
                        } else {
                            let arg_ty = check_expr(a, env, cs)?;
                            env.unify(dom, &arg_ty)?;
                            h_ty = if *dependent {
                                Expr::sub(rng, &var.name, &a)
                            } else {
                                rng.clone()
                            };
                        }
                    }
                    _ => {
                        return Err(LfscError::TooManyArgs(
                            (**h).clone(),
                            args.len(),
                            (*h_ty).clone(),
                        ))
                    }
                }
            }
            Ok(h_ty)
        }
        Expr::Program(p) => env.ty(&p.name).map(|e| e.clone()),
        Expr::DeclaredSymbol(_, name, _) => env.ty(&name).map(|e| e.clone()),
        Expr::Ref(_) => Ok(Expr::deref(expr.clone())),
        Expr::Hole(_) => Ok(expr.clone()),
        Expr::Pi {
            ref dom,
            ref rng,
            ref var,
            ref dependent,
        } => {
            assert!(var.val.borrow().is_none());
            *var.val.borrow_mut() = Some(dom.clone());
            let rng2 = check_expr(rng, env, cs)?;
            *var.val.borrow_mut() = None;
            Ok(Rc::new(Expr::Pi {
                dom: dom.clone(),
                var: var.clone(),
                dependent: dependent.clone(),
                rng: rng2,
            }))
        }
    }?;
    Ok(r)
}
