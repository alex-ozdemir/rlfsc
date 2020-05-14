use std::fmt::Display;

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum LfscKeyword {
    // Commands
    Declare,
    Define,
    Check,
    // Terms
    Type,
    // Function-names
    Percent,
    Bang,
    At,
    Let,
    Colon,
    Tilde,
    ReverseSolidus,
    Caret,
    // Ew, rationals
    Solidus,
    // Program constructs
    Do,
    Match,
    MpAdd,
    MpNeg,
    MpDiv,
    MpMul,
    MpIfNeg,
    MpIfZero,
    IfEqual,
    Compare,
    Fail,
    MarkVar(u5),
    IfMarked(u5),
}

impl Display for LfscKeyword {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            LfscKeyword::Declare => write!(f, "declare"),
            LfscKeyword::Define => write!(f, "define"),
            LfscKeyword::Check => write!(f, "check"),
            LfscKeyword::Type => write!(f, "type"),
            LfscKeyword::Percent => write!(f, "%"),
            LfscKeyword::Caret => write!(f, "^"),
            LfscKeyword::Bang => write!(f, "!"),
            LfscKeyword::At => write!(f, "@"),
            LfscKeyword::Let => write!(f, "let"),
            LfscKeyword::Colon => write!(f, ":"),
            LfscKeyword::Tilde => write!(f, "~"),
            LfscKeyword::Solidus => write!(f, "/"),
            LfscKeyword::ReverseSolidus => write!(f, "\\"),
            LfscKeyword::Do => write!(f, "do"),
            LfscKeyword::Match => write!(f, "match"),
            LfscKeyword::MpAdd => write!(f, "mp_add"),
            LfscKeyword::MpNeg => write!(f, "mp_neg"),
            LfscKeyword::MpDiv => write!(f, "mp_div"),
            LfscKeyword::MpMul => write!(f, "mp_mul"),
            LfscKeyword::MpIfNeg => write!(f, "mp_ifneg"),
            LfscKeyword::MpIfZero => write!(f, "mp_ifzero"),
            LfscKeyword::IfEqual => write!(f, "ifequal"),
            LfscKeyword::Compare => write!(f, "compare"),
            LfscKeyword::Fail => write!(f, "fail"),
            LfscKeyword::IfMarked(u) => write!(f, "ifmarked{}", u16::from(u) + 1),
            LfscKeyword::MarkVar(u) => write!(f, "markvar{}", u16::from(u) + 1),
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
enum LispToken {
    Open,
    Close,
    Ident(String),
    Keyword(LfscKeyword),
}

impl std::fmt::Display for LispToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            LispToken::Open => write!(f, "("),
            LispToken::Close => write!(f, ")"),
            LispToken::Ident(s) => write!(f, "{}", s),
            LispToken::Keyword(k) => write!(f, "{}", k),
        }
    }
}

