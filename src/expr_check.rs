use std::cell::RefCell;
use std::rc::Rc;

use crate::code::{parse_term, run_code, type_code, Code};
use crate::env::{Consts, Env, OldBinding};
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
    build_macro(vec![(var, domain)], range, range_ty)
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
    build_validate_pi(vec![(var, domain)], range, range_ty, create)
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

// Consumes an entry from a declaration list.
fn check_list_decl<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
) -> Result<(Option<Rc<Ref>>, Rc<Expr>), LfscError> {
    if ts.peek_token() == Some(Token::Open) {
        ts.next()?;
        if ts.peek_token() == Some(Token::Colon) {
            ts.next()?;
            let var = consume_new_ref(ts)?;
            let (ty, _) = check_create(ts, e, cs, Some(&cs.type_))?;
            ts.consume_tok(Token::Close)?;
            Ok((Some(var), ty))
        } else {
            let ty = check_form(ts, e, cs, None, true)?.0.unwrap();
            Ok((None, ty))
        }
    } else {
        let (ty, _) = check_create(ts, e, cs, Some(&cs.type_))?;
        Ok((None, ty))
    }
}

pub fn check_decl_list<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Vec<(Rc<Ref>, Rc<Expr>)>, Vec<OldBinding>), LfscError> {
    let mut old_binds = Vec::new();
    let mut args = Vec::new();
    ts.consume_tok(Token::Open)?;
    while ts.peek_token() != Some(Token::Close) {
        let (var, ty) = check_list_decl(ts, e, cs)?;
        if let Some(var) = &var {
            old_binds.push(e.bind(
                var.name.clone(),
                Rc::new(Expr::Ref(var.clone())),
                ty.clone(),
            ));
        }
        if create {
            if let Some(var) = var {
                args.push((var, ty));
            } else {
                args.push((Rc::new(Ref::new("_".to_owned())), ty));
            }
        }
    }
    ts.next()?;
    Ok((args, old_binds))
}

fn check_arrow<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let (args, old_binds) = check_decl_list(ts, e, cs, create)?;
    let (ret, ret_kind) = check(ts, e, cs, None, create)?;
    e.unbind_all(old_binds);
    ts.consume_tok(Token::Close)?;
    build_validate_pi(args, ret, ret_kind, create)
}

pub fn build_validate_pi(
    args: Vec<(Rc<Ref>, Rc<Expr>)>,
    ret: Option<Rc<Expr>>,
    ret_kind: Rc<Expr>,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    if *ret_kind == Expr::Type || *ret_kind == Expr::Kind {
        Ok((
            if create {
                Some(
                    args.into_iter()
                        .rev()
                        .fold(ret.unwrap(), |rng, (var, dom)| {
                            let dependent = Rc::strong_count(&var) > 1;
                            Rc::new(Expr::Pi {
                                dom,
                                rng,
                                var,
                                dependent,
                            })
                        }),
                )
            } else {
                None
            },
            ret_kind,
        ))
    } else {
        Err(LfscError::InvalidPiRange((*ret.unwrap()).clone()))
    }
}

pub fn build_macro(
    args: Vec<(Rc<Ref>, Rc<Expr>)>,
    ret: Option<Rc<Expr>>,
    ret_kind: Rc<Expr>,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    Ok(args
        .into_iter()
        .rev()
        .fold((ret, ret_kind), |(retm, ret_kind), (var, dom)| {
            // Check that dependent is false
            (
                if let Some(ret) = retm {
                    Some(Rc::new(Expr::Pi {
                        var: var.clone(),
                        dom: dom.clone(),
                        rng: ret,
                        dependent: false,
                    }))
                } else {
                    None
                },
                Rc::new(Expr::Pi {
                    var,
                    dom,
                    rng: ret_kind,
                    dependent: false,
                }),
            )
        }))
}

fn check_app<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    head_val: Rc<Expr>,
    head_ty: Rc<Expr>,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let fun = head_val.clone();
    let mut ty = head_ty;
    let mut args = Vec::new();
    let mut nargs = 0;

    while Some(Token::Close) != ts.peek_token() || ty.is_pi_run() {
        match &*ty {
            &Expr::Pi {
                ref dom,
                ref rng,
                ref var,
                ref dependent,
            } => {
                if let Expr::Run(ref term, ref expected, _) = **dom {
                    if cs.trace_sc {
                        println!("Side-condition check at {}", ts.current_line().1);
                    }
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
            _ => {
                return Err(LfscError::TooManyArgs(
                    (*head_val).clone(),
                    nargs,
                    (*ty).clone(),
                ))
            }
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

// Assumes that the opening '(' has been consumed.
// Consumes the closing ')'
pub fn check_form<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    ex_ty: Option<&Rc<Expr>>,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    use Token::*;
    let t_head = ts.require_next()?;
    match t_head.tok {
        Bang => check_pi(ts, e, cs, create),
        Arrow => check_arrow(ts, e, cs, create),
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
        Ident => {
            let b = e.binding(t_head.str())?;
            let val = b.val.clone();
            let ty = b.ty.clone();
            check_app(ts, e, cs, val, ty, create)
        }
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
        Open => {
            let head = check_form(ts, e, cs, None, true)?;
            check_app(ts, e, cs, head.0.unwrap(), head.1, create)
        }
        t => Err(LfscError::UnexpectedToken("typeable term", t)),
    }
}

pub fn check<'a, L: Lexer<'a>>(
    ts: &mut L,
    e: &mut Env,
    cs: &Consts,
    ex_ty: Option<&Rc<Expr>>,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    use Token::*;
    let t = ts.require_next()?;
    let (ast, ty) = match t.tok {
        Token::Type => Ok((Some(cs.type_.clone()), cs.kind.clone())),
        Token::Mpz => Ok((Some(cs.nat.clone()), cs.type_.clone())),
        Token::Mpq => Ok((Some(cs.rat.clone()), cs.type_.clone())),
        Token::Natural => Ok((Some(Rc::new(Expr::NatLit(t.nat()))), cs.nat.clone())),
        Token::Rational => Ok((Some(Rc::new(Expr::RatLit(t.rat()))), cs.rat.clone())),
        Token::Hole => Ok((Some(Rc::new(Expr::new_hole())), Rc::new(Expr::new_hole()))),
        Ident => Ok({
            let res = e.expr_binding(t.str())?;
            if create {
                (Some(res.val.clone()), res.ty.clone())
            } else {
                (None, res.ty.clone())
            }
        }),
        Open => check_form(ts, e, cs, ex_ty, create),
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
        match ts.require_next()?.tok {
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
    e.unbind_all(unbinds);
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
