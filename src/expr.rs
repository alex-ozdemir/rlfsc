use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::iter::once;
use std::rc::Rc;

use rug::{Integer, Rational};

use crate::code::{Code, MpBinOp};
use crate::error::LfscError;

#[derive(Debug, PartialEq, Eq)]
pub struct Ref {
    pub name: String,
    pub val: RefCell<Option<Rc<Expr>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub name: String,
    /// A reference and type for each argument
    pub args: Vec<(Rc<Ref>, Rc<Expr>)>,
    /// The return type of the function
    pub ret_ty: Rc<Expr>,
    /// The body of the function
    pub body: RefCell<Code>,
}

impl Ref {
    pub fn new(name: String) -> Self {
        Self {
            name,
            val: RefCell::new(None),
        }
    }
}
impl Display for Ref {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        //if let Some(r) = self.val.borrow().as_ref() {
        //    write!(f, " (bound to {})", r)?;
        //}
        Ok(())
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
    Ref(Rc<Ref>),
    /// eval expression, name, type
    Run(Code, Rc<Expr>, Rc<Expr>),
    Pi {
        var: Rc<Ref>,
        dom: Rc<Expr>,
        rng: Rc<Expr>,
        dependent: bool,
    },
    App(Rc<Expr>, Vec<Rc<Expr>>),
    /// Arguments, return type, body
    Hole(RefCell<Option<Rc<Expr>>>),
    Program(Program),
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
            Ref(s) => write!(f, "{}", s),
            DeclaredSymbol(_id, s, _marks) => {
                write!(f, "{}", s)?;
                //if marks.get() != 0 {
                //    f.debug_list()
                //        .entries(
                //            (0..31)
                //                .filter(|i| (1u32 << i) & marks.get() != 0)
                //                .map(|i| i + 1),
                //        )
                //        .finish()?;
                //}
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
            Program(_) => write!(f, "<program>"),
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
        Expr::Ref(Rc::new(Ref::new(s)))
    }

    fn deref_once(r: &Rc<Expr>) -> Option<Rc<Expr>> {
        match r.as_ref() {
            Expr::Hole(x) => x.borrow().clone(),
            Expr::Ref(x) => x.as_ref().val.borrow().clone(),
            _ => None,
        }
    }

    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            Expr::Ref(r) => once(r.name.clone()).collect(),
            Expr::Pi { var, dom, rng, .. } => {
                let mut f: HashSet<_> = dom
                    .free_vars()
                    .into_iter()
                    .chain(rng.free_vars().into_iter())
                    .collect();
                f.remove(&var.name.clone());
                f
            }
            Expr::App(h, ts) => {
                let mut f = h.free_vars();
                for t in ts {
                    for a in t.free_vars() {
                        f.insert(a);
                    }
                }
                f
            }
            _ => HashSet::new(),
        }
    }

    pub fn deref(mut r: Rc<Expr>) -> Rc<Expr> {
        loop {
            let next = match Expr::deref_once(&r) {
                Some(ref_) => ref_.clone(),
                None => break,
            };
            if &next == &r {
                break;
            } else {
                r = next;
            }
        }
        r
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
        match this.as_ref() {
            &Ref(ref ref_) => {
                if name == &ref_.name {
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
                if &var.name == name {
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

    pub fn name(&self) -> Result<&str, LfscError> {
        match self {
            Expr::DeclaredSymbol(_, s, _) => Ok(&s),
            Expr::Ref(r) => Ok(&r.name),
            Expr::Program(p) => Ok(&p.name),
            _ => Err(LfscError::NoName(self.clone())),
        }
    }

    pub fn weak_head_reduce(a: Rc<Expr>) -> Rc<Expr> {
        fn get_head(a: Rc<Expr>) -> Rc<Expr> {
            let d = Expr::deref(a);
            match d.as_ref() {
                Expr::App(ref head, _) => get_head(head.clone()),
                _ => d,
            }
        }
        fn collect_args(a: Rc<Expr>) -> Vec<Rc<Expr>> {
            let d = Expr::deref(a);
            match d.as_ref() {
                Expr::App(ref head, ref args) => {
                    let mut a = collect_args(head.clone());
                    a.extend(args.iter().cloned());
                    a
                }
                _ => Vec::new(),
            }
        }
        let mut head = get_head(a.clone());
        match head.as_ref() {
            Expr::Pi { .. } => {
                let mut args = collect_args(a);
                args.reverse();
                while let Expr::Pi {
                    ref var, ref rng, ..
                } = head.as_ref()
                {
                    if let Some(a) = args.pop() {
                        head = Expr::sub(rng, &var.name, &a);
                    } else {
                        break;
                    }
                }
                if args.len() > 0 {
                    args.reverse();
                    Rc::new(Expr::App(head, args))
                } else {
                    head
                }
            }
            _ => a,
        }
    }

    pub fn unify_test(a: &Rc<Expr>, b: &Rc<Expr>) -> bool {
        if Rc::ptr_eq(&a, &b) {
            true
        } else {
            let aa = Expr::weak_head_reduce(Expr::deref(a.clone()));
            let bb = Expr::weak_head_reduce(Expr::deref(b.clone()));
            if aa == bb {
                true
            } else {
                match (aa.as_ref(), bb.as_ref()) {
                    (Expr::Hole(_), Expr::Hole(_)) => false,
                    (Expr::Hole(i), _) => {
                        debug_assert!(i.borrow().is_none());
                        i.replace(Some(bb));
                        true
                    }
                    (_, Expr::Hole(i)) => {
                        debug_assert!(i.borrow().is_none());
                        i.replace(Some(aa));
                        true
                    }
                    (Expr::Bot, _) => true,
                    (_, Expr::Bot) => true,
                    (Expr::App(a_f, a_args), Expr::App(b_f, b_args)) => {
                        if a_args.len() == b_args.len() {
                            if !Expr::unify_test(a_f, b_f) {
                                return false;
                            }
                            for (x, y) in a_args.iter().zip(b_args.iter()) {
                                if !Expr::unify_test(x, y) {
                                    return false;
                                }
                            }
                            true
                        } else {
                            false
                        }
                    }
                    (Expr::DeclaredSymbol(x, _, _), Expr::DeclaredSymbol(y, _, _)) if x == y => {
                        false
                    }
                    // TODO remove?
                    (Expr::Ref(x), Expr::Ref(y)) if &x.name == &y.name => true,
                    _ => false,
                }
            }
        }
    }
}
