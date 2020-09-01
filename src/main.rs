use rlimit::{Resource, RLIM_INFINITY};
use structopt::StructOpt;
use yansi::Paint;

use std::cell::RefCell;
use std::default::Default;
use std::fs::read;
use std::path::PathBuf;
use std::rc::Rc;

mod code;
mod env;
mod error;
mod expr;
mod token;

use code::{parse_term, run_code, type_code, Code};
use env::{Consts, Env};
use error::LfscError;
use expr::{Expr, Program, Ref};
use token::{Lexer, Token};

fn consume_new_ref(ts: &mut Lexer) -> Result<Rc<Ref>, LfscError> {
    Ok(Rc::new(Ref::new(ts.consume_ident()?.to_owned())))
}

fn check_ann_lambda(
    ts: &mut Lexer,
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

fn check_pi(
    ts: &mut Lexer,
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

fn check_let(
    ts: &mut Lexer,
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

fn check_ascription(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
    let ty = check_create(ts, e, cs, Some(&cs.type_))?.0;
    let t = check(ts, e, cs, Some(&ty), create)?.0;
    ts.consume_tok(Token::Close)?;
    Ok((t, ty))
}

fn check_big_lambda(
    ts: &mut Lexer,
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

fn check_app(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
    name: String,
    create: bool,
) -> Result<(Option<Rc<Expr>>, Rc<Expr>), LfscError> {
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
            _ => return Err(LfscError::UntypableApplication((*ty).clone())),
        }
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

fn check_create(
    ts: &mut Lexer,
    e: &mut Env,
    cs: &Consts,
    ex_ty: Option<&Rc<Expr>>,
) -> Result<(Rc<Expr>, Rc<Expr>), LfscError> {
    check(ts, e, cs, ex_ty, true).map(|(a, b)| (a.unwrap(), b))
}

fn check(
    ts: &mut Lexer,
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

fn check_program(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
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

fn check_arg(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(Rc<Ref>, Rc<Expr>), LfscError> {
    let name = consume_new_ref(ts)?;
    let ty = check_create(ts, e, cs, Some(&cs.type_))?.0;
    ts.consume_tok(Token::Close)?;
    Ok((name, ty))
}

fn do_cmd(ts: &mut Lexer, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    use Token::{Check, Declare, Define, Program};
    match ts.require_next()? {
        Declare => {
            let name = ts.consume_ident()?.to_owned();
            let (ty, kind) = check_create(ts, e, cs, None)?;
            if *kind != Expr::Type && *kind != Expr::Kind {
                return Err(LfscError::BadDeclare(
                    name.clone(),
                    (*ty).clone(),
                    (*kind).clone(),
                ));
            }
            let sym = Rc::new(e.new_symbol(name.clone()));
            e.bind(name.clone(), sym, ty);
        }
        Define => {
            let name = ts.consume_ident()?.to_owned();
            let (val, ty) = check_create(ts, e, cs, None)?;
            e.bind(name.clone(), val, ty);
        }
        Program => {
            // It binds the program internally
            check_program(ts, e, cs)?;
        }
        Check => {
            check(ts, e, cs, None, false)?;
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

#[derive(StructOpt, Debug)]
#[structopt(name = "rlfsc")]
struct Args {
    /// Trace side condition executions
    #[structopt(short = "t", long)]
    trace_sc: bool,

    /// Files to type-check, in order.
    #[structopt(name = "FILE", parse(from_os_str))]
    files: Vec<PathBuf>,
}

fn main() -> Result<(), LfscError> {
    Resource::STACK
        .set(1 << 30, RLIM_INFINITY)
        .expect("Could not set stack size to 1GB");
    let args = Args::from_args();
    let mut env = Env::default();
    for path in &args.files {
        let bytes = read(path).unwrap();
        let mut lexer = Lexer::new(&bytes, path.clone());
        let consts = Consts::new(args.trace_sc);
        //    do_cmds(&mut lexer, &mut env)?;
        if let Err(e) = do_cmds(&mut lexer, &mut env, &consts) {
            let (line, pos) = lexer.current_line();
            println!(
                "{} near {}:{}:{}",
                Paint::red("error"),
                Paint::blue(pos.path.to_str().unwrap()),
                pos.line_no,
                pos.col_no
            );
            println!();
            let line_no_str = format!("{} {} ", Paint::blue(pos.line_no), Paint::blue("|"));
            println!("{} {}", line_no_str, line);
            for _ in 0..(pos.col_no + format!("{}   ", pos.line_no).len()) {
                print!(" ");
            }
            println!("^");
            println!();
            println!("Message: {}", Paint::red(e));
            std::process::exit(1);
        }
    }
    println!("{}", Paint::green("Proof checked!"));
    Ok(())
}
