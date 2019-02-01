extern crate bytes;
extern crate tokio;

use bytes::{BufMut, BytesMut};
use tokio::codec::{Decoder, Encoder, FramedRead};
use tokio::prelude::*;

use std::io;

#[derive(PartialEq, Eq, Debug)]
enum LispToken {
    Open,
    Close,
    Ident(String),
}

struct LispTokenCodec {
    last_token_was_an_identifier: bool,
    in_comment: bool,
}

impl LispTokenCodec {
    fn new() -> Self {
        Self {
            last_token_was_an_identifier: false,
            in_comment: false,
        }
    }
}

// Turns string errors into io::Error
fn bad_utf8<E>(_: E) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "Unable to decode input as UTF8")
}

impl Encoder for LispTokenCodec {
    type Item = LispToken;
    type Error = io::Error;

    fn encode(&mut self, token: Self::Item, buf: &mut BytesMut) -> Result<(), Self::Error> {
        match token {
            LispToken::Close => {
                buf.reserve(1);
                buf.put_u8(b')');
                self.last_token_was_an_identifier = false;
            }
            LispToken::Open => {
                buf.reserve(1);
                buf.put_u8(b'(');
                self.last_token_was_an_identifier = false;
            }
            LispToken::Ident(s) => {
                if self.last_token_was_an_identifier {
                    buf.reserve(1 + s.len());
                    buf.put_u8(b' ');
                    buf.put(s);
                } else {
                    buf.reserve(s.len());
                    buf.put(s);
                }
                self.last_token_was_an_identifier = true;
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
                    b';' => {
                        if let Some(first_newline) = buf.iter().position(|b| *b == b'\n') {
                            buf.advance(first_newline + 1);
                        } else {
                            self.in_comment = true;
                            return Ok(None);
                        }
                    }
                    _ => {
                        if let Some(first_non_ident) = buf
                            .iter()
                            .position(|b| b.is_ascii_whitespace() || *b == b')' || *b == b'(')
                        {
                            let ident = buf.split_to(first_non_ident);
                            return Ok(Some(LispToken::Ident(
                                std::str::from_utf8(&ident).map_err(bad_utf8)?.to_owned(),
                            )));
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
                    Some(LispToken::Ident(
                        std::str::from_utf8(&buf.take()[..])
                            .map_err(bad_utf8)?
                            .to_owned(),
                    ))
                }
            }
        })
    }
}

fn main() {
    println!("Hello, world!");
    let stream = FramedRead::new(tokio::io::stdin(), LispTokenCodec::new());
    let future = stream
        .map_err(|e| {
            eprintln!("{:?}", e);
        })
        .fold(0, |a, _| Ok(a + 1))
        .map(|s| {
            println!("Number of tokens: {}", s);
        });

    tokio::run(future)
}
