use rlimit::{Resource, RLIM_INFINITY};
use structopt::clap::arg_enum;
use structopt::StructOpt;
use yansi::Paint;
use atty;

use std::default::Default;
use std::fs::read;
use std::path::PathBuf;
use std::rc::Rc;

mod code;
mod env;
mod error;
mod expr;
mod expr_check;
mod token;

use env::{Consts, Env};
use error::LfscError;
use expr::Expr;
use expr_check::{
    build_macro, build_validate_pi, check, check_create, check_decl_list, check_program,
};
use token::{DesugaringLexer, Lexer, Token};

fn do_cmd<'a, L: Lexer<'a>>(ts: &mut L, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    use Token::{Check, CheckAssuming, Declare, DeclareRule, DeclareType, DefineConst, Define, Opaque, Program};
    let t = ts.require_next()?;
    match t.tok {
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
        DeclareRule => {
            let name = ts.consume_ident()?.to_owned();
            let (args, old_binds) = check_decl_list(ts, e, cs, true)?;
            let (ret, ret_kind) = check_create(ts, e, cs, None)?;
            e.unbind_all(old_binds);
            let sym = Rc::new(e.new_symbol(name.clone()));
            let ty = build_validate_pi(args, Some(ret), ret_kind, true)?
                .0
                .unwrap();
            e.bind(name.clone(), sym, ty);
        }
        DeclareType => {
            let name = ts.consume_ident()?.to_owned();
            let (args, old_binds) = check_decl_list(ts, e, cs, true)?;
            e.unbind_all(old_binds);
            let sym = Rc::new(e.new_symbol(name.clone()));
            let ty = build_validate_pi(args, Some(cs.type_.clone()), cs.kind.clone(), true)?
                .0
                .unwrap();
            e.bind(name.clone(), sym, ty);
        }
        DefineConst => {
            let name = ts.consume_ident()?.to_owned();
            let (args, old_binds) = check_decl_list(ts, e, cs, true)?;
            let (ret, ret_kind) = check_create(ts, e, cs, None)?;
            let (value, ty) = build_macro(args, Some(ret), ret_kind)?;
            e.unbind_all(old_binds);
            e.bind(name, value.unwrap(), ty);
        }
        Define => {
            let name = ts.consume_ident()?.to_owned();
            let (val, ty) = check_create(ts, e, cs, None)?;
            e.bind(name.clone(), val, ty);
        }
        Opaque => {
            let name = ts.consume_ident()?.to_owned();
            let (_, ty) = check(ts, e, cs, None, false)?;
            let sym = Rc::new(e.new_symbol(name.clone()));
            e.bind(name.clone(), sym, ty);
        }
        Program => {
            // It binds the program internally
            check_program(ts, e, cs)?;
        }
        CheckAssuming => {
            let (_, old_binds) = check_decl_list(ts, e, cs, false)?;
            let ex_type = check(ts, e, cs, Some(&cs.type_), true)?.0.unwrap();
            let (_, _) = check(ts, e, cs, Some(&ex_type), false)?;
            e.unbind_all(old_binds);
        }
        Check => {
            check(ts, e, cs, None, false)?;
        }
        _ => return Err(LfscError::NotACmd(t.string())),
    }
    ts.consume_tok(Token::Close)?;
    Ok(())
}

fn do_cmds<'a, L: Lexer<'a>>(ts: &mut L, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
    while let Some(t) = ts.next()? {
        match t.tok {
            Token::Open => do_cmd(ts, e, cs)?,
            _ => return Err(LfscError::NotACmd(t.string())),
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

    /// Whether to use color ouput
    #[structopt(short = "c", long, possible_values = &ColorCfg::variants(), case_insensitive = true, default_value = "auto")]
    color: ColorCfg,

    /// Files to type-check, in order.
    #[structopt(name = "FILE", parse(from_os_str))]
    files: Vec<PathBuf>,
}

arg_enum! {
    #[derive(Debug, PartialEq, Eq)]
    enum ColorCfg {
        // Use color ouput
        On,
        // Use color output for ttys
        Auto,
        // Don't use color output
        Off,
    }
}

impl ColorCfg {
}

fn try_increase_stack() {
    let hard_limit = Resource::STACK
        .get()
        .expect("Could not fetch stack limit")
        .1;
    let desired_limit = 1 << 30;
    let actual_setting = if hard_limit == RLIM_INFINITY || hard_limit >= desired_limit {
        desired_limit
    } else {
        hard_limit
    };
    if actual_setting < desired_limit {
        eprintln!("Warning: could not increase stack size to {} bytes because of the hard limit. Setting it to {} instead", desired_limit, actual_setting);
    }
    Resource::STACK
        .set(actual_setting, hard_limit)
        .expect("Could not set stack size")
}

fn main() -> Result<(), LfscError> {
    try_increase_stack();
    let args = Args::from_args();
    if args.color == ColorCfg::Off || (args.color == ColorCfg::Auto && atty::isnt(atty::Stream::Stdout)) {
        Paint::disable();
    }
    let mut env = Env::default();
    for path in &args.files {
        let bytes = read(path).unwrap();
        let mut lexer = DesugaringLexer::new(&bytes, path.clone());
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
