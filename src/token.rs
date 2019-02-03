use bytes::{BufMut, BytesMut};
use tokio::codec::{Decoder, Encoder};

use crate::num::bigint::BigUint;
use std::fmt::Display;
use std::io::{self, Write};
use std::str::FromStr;
use ux::u5;

/// Turns string errors into io::Error
fn bad_utf8<E>(_: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Unable to decode input as UTF8")
}

/// Turns int parse into io::Error
fn bad_int<E>(_: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Unable to parse integer")
}

/// Use to indicate that a mark number is out-of-bounds
fn bad_mark_num() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Mark number is out of bounds")
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum LfscKeyword {
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
pub enum LispToken {
    Open,
    Close,
    Ident(String),
    Natural(BigUint),
    Keyword(LfscKeyword),
}

impl std::fmt::Display for LispToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            LispToken::Open => write!(f, "("),
            LispToken::Close => write!(f, ")"),
            LispToken::Ident(s) => write!(f, "{}", s),
            LispToken::Keyword(k) => write!(f, "{}", k),
            LispToken::Natural(u) => write!(f, "{}", u),
        }
    }
}

impl LispToken {
    /// Given a slice of non-grouping, non-whitespace characters, parses a LispToken
    fn from_ident(ident: &[u8]) -> Result<Self, io::Error> {
        Ok(match ident {
            b"declare" => LispToken::Keyword(LfscKeyword::Declare),
            b"define" => LispToken::Keyword(LfscKeyword::Define),
            b"type" => LispToken::Keyword(LfscKeyword::Type),
            b"check" => LispToken::Keyword(LfscKeyword::Check),
            b"%" => LispToken::Keyword(LfscKeyword::Percent),
            b"^" => LispToken::Keyword(LfscKeyword::Caret),
            b"!" => LispToken::Keyword(LfscKeyword::Bang),
            b"@" => LispToken::Keyword(LfscKeyword::At),
            b"let" => LispToken::Keyword(LfscKeyword::Let),
            b":" => LispToken::Keyword(LfscKeyword::Colon),
            b"~" => LispToken::Keyword(LfscKeyword::Tilde),
            b"/" => LispToken::Keyword(LfscKeyword::Solidus),
            b"\\" => LispToken::Keyword(LfscKeyword::ReverseSolidus),
            b"do" => LispToken::Keyword(LfscKeyword::Do),
            b"match" => LispToken::Keyword(LfscKeyword::Match),
            b"mp_add" => LispToken::Keyword(LfscKeyword::MpAdd),
            b"mp_neg" => LispToken::Keyword(LfscKeyword::MpNeg),
            b"mp_div" => LispToken::Keyword(LfscKeyword::MpDiv),
            b"mp_mul" => LispToken::Keyword(LfscKeyword::MpMul),
            b"mp_ifneg" => LispToken::Keyword(LfscKeyword::MpIfNeg),
            b"mp_ifzero" => LispToken::Keyword(LfscKeyword::MpIfZero),
            b"ifequal" => LispToken::Keyword(LfscKeyword::IfEqual),
            b"compare" => LispToken::Keyword(LfscKeyword::Compare),
            b"fail" => LispToken::Keyword(LfscKeyword::Fail),
            buf => {
                if buf.len() >= 8 && &buf[..8] == b"ifmarked" {
                    let s = std::str::from_utf8(&buf[8..]).map_err(bad_utf8)?;
                    let u = usize::from_str(s).map_err(bad_int)?;
                    if u >= 1 && u <= 32 {
                        LispToken::Keyword(LfscKeyword::IfMarked(u5::new(u as u8)))
                    } else {
                        return Err(bad_mark_num());
                    }
                } else if buf.len() >= 7 && &buf[..7] == b"markvar" {
                    let s = std::str::from_utf8(&buf[7..]).map_err(bad_utf8)?;
                    let u = usize::from_str(s).map_err(bad_int)?;
                    if u >= 1 && u <= 32 {
                        LispToken::Keyword(LfscKeyword::MarkVar(u5::new(u as u8)))
                    } else {
                        return Err(bad_mark_num());
                    }
                } else {
                    LispToken::Ident(std::str::from_utf8(&ident).map_err(bad_utf8)?.to_owned())
                }
            }
        })
    }
    fn natural_from_slice(slice: &[u8]) -> io::Result<Self> {
        Ok(LispToken::Natural(
                BigUint::from_str(std::str::from_utf8(slice).map_err(bad_utf8)?)
                .map_err(bad_int)?,
                ))
    }
}

pub struct LispTokenCodec {
    last_token_vulnerable: bool,
    in_comment: bool,
}

impl LispTokenCodec {
    pub fn new() -> Self {
        Self {
            last_token_vulnerable: false,
            in_comment: false,
        }
    }
}


/// NB(aozdemir): This code is totally untested, and has at least one bug.
impl Encoder for LispTokenCodec {
    type Item = LispToken;
    type Error = io::Error;

    fn encode(&mut self, token: Self::Item, buf: &mut BytesMut) -> Result<(), Self::Error> {
        match token {
            LispToken::Close => {
                buf.reserve(1);
                buf.put_u8(b')');
                self.last_token_vulnerable = false;
            }
            LispToken::Open => {
                buf.reserve(1);
                buf.put_u8(b'(');
                self.last_token_vulnerable = false;
            }
            LispToken::Ident(s) => {
                if self.last_token_vulnerable {
                    buf.reserve(1 + s.len());
                    buf.put_u8(b' ');
                    buf.put(s);
                } else {
                    buf.reserve(s.len());
                    buf.put(s);
                }
                self.last_token_vulnerable = true;
            }
            LispToken::Keyword(k) => {
                write!(buf.writer(), "{}", k).unwrap();
            }
            LispToken::Natural(u) => {
                if self.last_token_vulnerable {
                    write!(buf.writer(), " {}", u).unwrap();
                } else {
                    write!(buf.writer(), "{}", u).unwrap();
                }
                self.last_token_vulnerable = true;
            }
        }
        Ok(())
    }
}

impl Decoder for LispTokenCodec {
    type Item = LispToken;
    type Error = io::Error;

    fn decode(&mut self, buf: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if self.in_comment {
            if let Some(first_newline) = buf.iter().position(|b| *b == b'\n') {
                buf.advance(first_newline + 1);
                self.in_comment = false;
            } else {
                buf.clear();
                return Ok(None);
            }
        }
        while let Some(first_non_whitespace) = buf.iter().position(|b| !b.is_ascii_whitespace()) {
            buf.advance(first_non_whitespace);
            if buf.len() > 0 {
                match buf[0] {
                    b'(' => {
                        buf.advance(1);
                        return Ok(Some(LispToken::Open));
                    }
                    b')' => {
                        buf.advance(1);
                        return Ok(Some(LispToken::Close));
                    }
                    b'/' => {
                        buf.advance(1);
                        return Ok(Some(LispToken::Keyword(LfscKeyword::Solidus)));
                    }
                    b';' => {
                        if let Some(first_newline) = buf.iter().position(|b| *b == b'\n') {
                            buf.advance(first_newline + 1);
                        } else {
                            self.in_comment = true;
                            return Ok(None);
                        }
                    }
                    b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' | b'8' | b'9' => {
                        if let Some(first_non_digit) = buf.iter().position(|b| !b.is_ascii_digit())
                        {
                            let digits = buf.split_to(first_non_digit);
                            return Ok(Some(LispToken::natural_from_slice(&digits[..])?));
                        } else {
                            return Ok(None);
                        }
                    }
                    _ => {
                        if let Some(first_non_ident) = buf
                            .iter()
                                .position(|b| b.is_ascii_whitespace() || *b == b')' || *b == b'(')
                                {
                                    let ident = buf.split_to(first_non_ident);
                                    return Ok(Some(LispToken::from_ident(&ident)?));
                                } else {
                                    return Ok(None);
                                }
                    }
                }
            } else {
                unreachable!()
            }
        }
        buf.clear();
        Ok(None)
    }

    fn decode_eof(&mut self, buf: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        Ok(match self.decode(buf)? {
            Some(f) => Some(f),
            None => {
                if buf.is_empty() {
                    None
                } else {
                    Some(LispToken::from_ident(&buf.take()[..])?)
                }
            }
        })
    }
}
