use std::cell::{Cell, RefCell};
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

use rug::{Integer, Rational};

use crate::code::{Code, MpBinOp};
use crate::error::LfscError;

#[derive(Debug, PartialEq, Eq)]
pub struct Program {
    pub args: Vec<(String, Rc<Expr>)>,
    pub ret_ty: Rc<Expr>,
    pub body: Rc<Code>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Var(pub String);

impl Display for Var {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Bot,
    Type,
    Kind,
    NatTy,
    NatLit(Integer),
    RatTy,
    RatLit(Rational),
    DeclaredSymbol(u64, String, Cell<u32>),
    Var(Rc<Var>),
    /// eval expression, name, type
    Run(Code, Rc<Expr>, Rc<Expr>),
    Pi {
        var: Rc<Var>,
        dom: Rc<Expr>,
        rng: Rc<Expr>,
        dependent: bool,
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
            RatLit(r) => write!(f, "{}/{}", r.numer(), r.denom()),
            Var(s) => write!(f, "{}", s),
            DeclaredSymbol(id, s, marks) => {
                write!(f, "{}{{{}}}", s, id)?;
                if marks.get() != 0 {
                    f.debug_list()
                        .entries(
                            (0..31)
                                .filter(|i| (1u32 << i) & marks.get() != 0)
                                .map(|i| i + 1),
                        )
                        .finish()?;
                }
                Ok(())
            }
            Run(c, n, e) => write!(f, "(^ ({} {}) {})", c, n, e),
            Pi { var, dom, rng, .. } => write!(f, "(! {} {} {})", var, dom, rng),
            App(head, tail) => {
                write!(f, "({}", head)?;
                for t in tail {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Hole(c) => {
                if let Some(r) = c.borrow().as_ref() {
                    write!(f, "_\\{}", r)
                } else {
                    write!(f, "_")
                }
            }
        }
    }
}

impl Expr {
    pub fn is_pi_run(&self) -> bool {
        if let Expr::Pi { dom, .. } = &self {
            match **dom {
                Expr::Run(..) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    pub fn new_hole() -> Expr {
        Expr::Hole(RefCell::new(None))
    }

    pub fn new_var(s: String) -> Expr {
        Expr::Var(Rc::new(Var(s)))
    }

    pub fn deref_holes(mut r: Rc<Self>) -> Rc<Expr> {
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

    pub fn mp_neg(&self) -> Result<Expr, LfscError> {
        match self {
            Expr::NatLit(i) => Ok(Expr::NatLit(-i.clone())),
            Expr::RatLit(i) => Ok(Expr::RatLit(-i.clone())),
            a => Err(LfscError::NotMpInNeg(a.clone())),
        }
    }

    pub fn mp_bin(&self, op: MpBinOp, other: &Expr) -> Result<Expr, LfscError> {
        match (self, other) {
            (Expr::NatLit(x), Expr::NatLit(y)) => Ok(Expr::NatLit(match op {
                MpBinOp::Add => Integer::from(x + y),
                MpBinOp::Div => Integer::from(x / y),
                MpBinOp::Mul => Integer::from(x * y),
            })),
            (Expr::RatLit(x), Expr::RatLit(y)) => Ok(Expr::RatLit(match op {
                MpBinOp::Add => Rational::from(x + y),
                MpBinOp::Div => Rational::from(x / y),
                MpBinOp::Mul => Rational::from(x * y),
            })),
            (a, b) => Err(LfscError::NotMpInBin(op.clone(), a.clone(), b.clone())),
        }
    }

    pub fn sub(this: &Rc<Self>, name: &str, value: &Rc<Expr>) -> Rc<Self> {
        use Expr::*;
        //eprintln!("Sub: {}/{} in {}", value, name, this);
        match this.as_ref() {
            &Var(ref name_) => {
                if name == &name_.0 {
                    value.clone()
                } else {
                    this.clone()
                }
            }
            &App(ref f, ref args) => Rc::new(App(
                Expr::sub(f, name, value),
                args.iter().map(|a| Expr::sub(a, name, value)).collect(),
            )),
            &Run(ref code, ref var, ref body) => Rc::new(Run(
                code.sub(name, value),
                Expr::sub(var, name, value),
                Expr::sub(body, name, value),
            )),
            &Pi {
                ref var,
                ref dom,
                ref rng,
                ref dependent,
            } => {
                if &var.0 == name {
                    this.clone()
                } else {
                    Rc::new(Pi {
                        var: var.clone(),
                        dom: Expr::sub(dom, name, value),
                        rng: Expr::sub(rng, name, value),
                        dependent: *dependent,
                    })
                }
            }
            _ => this.clone(),
        }
    }
    pub fn require_mp_ty(&self) -> Result<(), LfscError> {
        if self != &Expr::NatTy && self != &Expr::RatTy {
            Err(LfscError::BadMqExpr(self.clone()))
        } else {
            Ok(())
        }
    }

}
