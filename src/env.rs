use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::LfscError;
use crate::expr::{Expr};

impl From<ExprEnvEntry> for (Rc<Expr>, Rc<Expr>) {
    fn from(e: ExprEnvEntry) -> Self {
        (e.val, e.ty)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ExprEnvEntry {
    pub val: Rc<Expr>,
    pub ty: Rc<Expr>,
}

#[derive(Debug)]
pub struct Env {
    // Map from identifiers to their values and types
    pub types: HashMap<String, ExprEnvEntry>,
    next_symbol: u64,
    pub sc_depth: usize,
}

impl Default for Env {
    fn default() -> Self {
        Self {
            types: Default::default(),
            next_symbol: 0,
            sc_depth: 0,
        }
    }
}

type OldBinding = (String, Option<ExprEnvEntry>);

impl Env {
    pub fn bind(&mut self, name: String, val: Rc<Expr>, ty: Rc<Expr>) -> OldBinding {
        let name_cp = name.clone();
        let old = self.types.insert(name, ExprEnvEntry { val, ty });
        (name_cp, old)
    }
    pub fn unbind(&mut self, (name, o): OldBinding) {
        if let Some(val) = o {
            self.types.insert(name, val);
        } else {
            self.types.remove(&name);
        }
    }
    pub fn binding(&self, name: &str) -> Result<&ExprEnvEntry, LfscError> {
        self.types
            .get(name)
            .ok_or_else(|| LfscError::UnknownIdentifier(name.to_owned()))
    }
    pub fn expr_binding(&self, name: &str) -> Result<&ExprEnvEntry, LfscError> {
        self.binding(name)
    }
    pub fn expr_value(&self, name: &str) -> Result<&Rc<Expr>, LfscError> {
        self.expr_binding(name).map(|p| &p.val)
    }
    pub fn ty(&self, name: &str) -> Result<&Rc<Expr>, LfscError> {
        Ok(&self.binding(name)?.ty)
    }
    pub fn toggle_mark(&self, e: Rc<Expr>, m: u8) -> Result<Rc<Expr>, LfscError> {
        debug_assert!(m <= 32 && m >= 1);
        let d = Expr::deref(e);
        match d.as_ref() {
            Expr::DeclaredSymbol(_, _, marks) => {
                marks.set((1u32 << (m - 1)) ^ marks.get());
            }
            _ => return Err(LfscError::CannotMark((*d).clone())),
        }
        return Ok(d);
    }
    pub fn get_mark(&self, e: Rc<Expr>, m: u8) -> Result<bool, LfscError> {
        debug_assert!(m <= 32 && m >= 1);
        let d = Expr::deref(e);
        match d.as_ref() {
            Expr::DeclaredSymbol(_, _, marks) => {
                let r = (1u32 << (m - 1)) & marks.get() != 0;
                Ok(r)
            }
            _ => Err(LfscError::CannotMark((*d).clone())),
        }
    }
    pub fn new_symbol(&mut self, s: String) -> Expr {
        self.next_symbol += 1;
        Expr::DeclaredSymbol(self.next_symbol - 1, s, Cell::new(0))
    }
    pub fn unify(&self, a: &Rc<Expr>, b: &Rc<Expr>) -> Result<Rc<Expr>, LfscError> {
        //println!("unify {} {}", a, b);
        if Rc::ptr_eq(&a, &b) {
            Ok(a.clone())
        } else {
            let aa = Expr::weak_head_reduce(Expr::deref(a.clone()));
            let bb = Expr::weak_head_reduce(Expr::deref(b.clone()));
            if aa == bb {
                Ok(aa.clone())
            } else {
                Ok((match (aa.as_ref(), bb.as_ref()) {
                    (Expr::Hole(_), Expr::Hole(_)) => Err(LfscError::TwoHoles),
                    (Expr::Hole(i), _) => {
                        debug_assert!(i.borrow().is_none());
                        i.replace(Some(bb));
                        Ok(aa)
                    }
                    (_, Expr::Hole(i)) => {
                        debug_assert!(i.borrow().is_none());
                        i.replace(Some(aa));
                        Ok(bb)
                    }
                    (Expr::Bot, _) => Ok(aa),
                    (_, Expr::Bot) => Ok(bb),
                    (Expr::App(a_f, a_args), Expr::App(b_f, b_args)) => {
                        if a_args.len() == b_args.len() {
                            self.unify(a_f, b_f)?;
                            for (x, y) in a_args.iter().zip(b_args.iter()) {
                                self.unify(x, y)?;
                            }
                            Ok(aa)
                        } else {
                            Err(LfscError::AppArgcMismatch((*aa).clone(), (*bb).clone()))
                        }
                    }
                    (Expr::DeclaredSymbol(x, _, _), Expr::DeclaredSymbol(y, _, _)) if x == y => {
                        Ok(aa)
                    }
                    // TODO remove?
                    // (Expr::Ref(x), Expr::Ref(y)) if &x.name == &y.name => Ok(aa),
                    _ => Err(LfscError::TypeMismatch((*aa).clone(), (*bb).clone())),
                })?)
            }
        }
    }
    pub fn unify_all(
        &self,
        tys: impl IntoIterator<Item = Rc<Expr>>,
    ) -> Result<Rc<Expr>, LfscError> {
        let mut non_fails = tys.into_iter();
        if let Some(first) = non_fails.next() {
            non_fails.try_fold(first, |a, b| self.unify(&a, &b))
        } else {
            Err(LfscError::NoCases)
        }
    }
}

pub struct Consts {
    pub type_: Rc<Expr>,
    pub kind: Rc<Expr>,
    pub nat: Rc<Expr>,
    pub rat: Rc<Expr>,
    pub bot: Rc<Expr>,
    pub trace_sc: bool,
}

impl Consts {
    pub fn new(trace_sc: bool) -> Self {
        Self {
            type_: Rc::new(Expr::Type),
            kind: Rc::new(Expr::Kind),
            nat: Rc::new(Expr::NatTy),
            rat: Rc::new(Expr::RatTy),
            bot: Rc::new(Expr::Bot),
            trace_sc,
        }
    }
}
