
use crate::expr::Expr;
use crate::code::{MpBinOp, MpCond, Pattern};
use crate::token::{Token};

use thiserror::Error;

#[derive(Error, Debug)]
pub enum LfscError {
    #[error("Got an unexpected EOF")]
    UnexpectedEof,
    #[error("Unknown identifier `{0}`")]
    UnknownIdentifier(String),
    #[error("Expr `{0}` does not have a name")]
    NoName(Expr),
    #[error("Expect a {0}, but found token `{1:?}`")]
    UnexpectedToken(&'static str, Token),
    #[error("A Pi-binding's range must have type 'type' or 'kind', but it has type {0}")]
    InvalidPiRange(Expr),
    #[error("A lambda's type cannot be computed. It must be ascribed.")]
    UnascribedLambda,
    #[error("Terms of type `{0}` cannot be applied")]
    UntypableApplication(Expr),
    #[error("`{0}` has type\n\t{1}\n, but was expected to have\n\t{2}")]
    UnexpectedType(Expr, Expr, Expr),
    #[error("Expected a command, but got `{0}`")]
    NotACmd(String),
    #[error("Identifiers should be declare to have kind type or kind, but {0} was declared to be a `{1}`, which has kind `{2}`")]
    BadDeclare(String, Expr, Expr),
    #[error("There most be at least one case")]
    NoCases,
    #[error("Non-pi pattern head")]
    NonPiPatternHead,
    #[error("Types `{0}` and `{1}` do not match")]
    TypeMismatch(Expr, Expr),
    #[error("Run produced `{0}`, but was expected to produce `{1}`")]
    RunWrongResult(Expr, Expr),
    #[error("Input types to mp_* must be rational or natural, not {0:?}")]
    BadMqExpr(Expr),
    #[error("The identifier {2} is an {1} but should be a {0}")]
    WrongIdentifierType(&'static str, &'static str, String),
    #[error("{0:?} cannot be applied to {1} and {2}, because one is not arithmetic")]
    NotMpInBin(MpBinOp, Expr, Expr),
    #[error("{0} cannot be negated because it is not arithmetic")]
    NotMpInNeg(Expr),
    #[error("{1} cannot be the argument to {0} because it is not arithmetic")]
    NotMpInMpCond(MpCond, Expr),
    #[error("{0} converted to a rational because it is an integer")]
    NotMpzInMpzToMpq(Expr),
    #[error("The applications\n\t{0}\nand\n\t{1}\ncannot be equal because they have different numbers of arguments")]
    AppArgcMismatch(Expr, Expr),
    #[error("Cannot mark\n\t{0}\nbecause it is not a variable.")]
    CannotMark(Expr),
    #[error("Cannot unify two holes!")]
    TwoHoles,
    #[error("The function {0} requires {1} arguments, but got {2}")]
    WrongNumberOfArgs(Expr, usize, usize),
    #[error("Fail with type {0}")]
    Fail(Expr),
    #[error("Unfilled hole in code")]
    UnfilledHole,
    #[error("{0} cannot be the type of a lambda")]
    InvalidLambdaType(Expr),
    #[error("No pattern for {0} in {1:#?}")]
    NoPattern(Expr, Vec<Pattern>),
    #[error("{0} should be bound with {1} variables, but found {2} in {3}")]
    WrongBindingCount(Expr, usize, usize, Pattern),
    #[error("Expect a {0:?}, but found token `{1:?}`")]
    WrongToken(Token, Token),
    #[error("No expression in a do form")]
    EmptyDo,
    #[error("No cases in a match form")]
    EmptyMatch,
}

