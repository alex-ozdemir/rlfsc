use rlimit::{Resource, RLIM_INFINITY};
use structopt::StructOpt;
use yansi::Paint;

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
use expr_check::{check, check_create, check_program};
use token::{Lexer, Token, LogosLexer};

fn do_cmd<'a, L: Lexer<'a>>(ts: &mut L, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
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

fn do_cmds<'a, L: Lexer<'a>>(ts: &mut L, e: &mut Env, cs: &Consts) -> Result<(), LfscError> {
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
    let mut env = Env::default();
    for path in &args.files {
        let bytes = read(path).unwrap();
        let mut lexer = LogosLexer::new(&bytes, path.clone());
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
