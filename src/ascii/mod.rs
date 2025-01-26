// TODO: Switch to `core::ascii::Char` if it ever gets stablized

use crate::{Error as PError, Failure, Input, Success};
use ascii::ToAsciiChar;

#[doc(inline)]
pub use ascii::{AsciiChar, AsciiStr};

#[cfg(feature = "alloc")]
pub use ascii::AsciiString;

/// Create an ASCII character or string, checked at compile time.
///
/// This macro takes a single literal argument and converts the value
/// to an [`AsciiChar`] or an [`&'static AsciiStr`](AsciiStr) depending
/// on the literal type. The argument can be an integer, character,
/// string, byte, or byte string literal. If the literal is not valid
/// ASCII, a compile error is emitted.
///
/// This macro can be used in `const` contexts.
///
/// # Example
/// ```
/// # use pars::ascii::{ascii, AsciiChar, AsciiStr};
/// assert_eq!(ascii!(0x41), AsciiChar::A);
/// assert_eq!(ascii!('A'), AsciiChar::A);
/// assert_eq!(ascii!(b'A'), AsciiChar::A);
/// assert_eq!(ascii!("ABC").as_slice(), &[AsciiChar::A, AsciiChar::B, AsciiChar::C]);
/// assert_eq!(ascii!(b"ABC").as_slice(), &[AsciiChar::A, AsciiChar::B, AsciiChar::C]);
/// ```
pub use pars_macros::ascii;

pub mod lossy;
pub mod prop;
pub mod strict;

mod loc;

pub use loc::*;

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorKind {
    NeedMoreInput,
    ExpectedEof,
    InvalidInput,
    NonAsciiChar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error<I: Input> {
    kind: ErrorKind,
    pos: I,
}

pub type PResult<T, I> = super::PResult<T, I, Error<I>>;

pub trait AsciiSymbol {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = Self>;

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = Self>;
}

pub trait AsciiInput: Input {
    fn parse_char(self) -> PResult<AsciiChar, Self>;

    fn parse_char_lossy(self) -> PResult<AsciiChar, Self>;
}

pub trait Property: core::fmt::Debug + Copy {
    fn contains(self, ch: AsciiChar) -> bool;
}

impl<I: Input> Error<I> {
    pub const fn new(kind: ErrorKind, pos: I) -> Self {
        Self { kind, pos }
    }

    pub const fn non_ascii_char(pos: I) -> Self {
        Self::new(ErrorKind::NonAsciiChar, pos)
    }

    pub const fn kind(&self) -> ErrorKind {
        self.kind
    }
}

impl<I: Input> crate::Error<I> for Error<I> {
    fn need_more_input(pos: I) -> Self {
        Self::new(ErrorKind::NeedMoreInput, pos)
    }

    fn expected_eof(pos: I) -> Self {
        Self::new(ErrorKind::ExpectedEof, pos)
    }

    fn invalid_input(pos: I) -> Self {
        Self::new(ErrorKind::InvalidInput, pos)
    }

    fn position(&self) -> &I {
        &self.pos
    }
}

impl<I: Input> crate::ErrorSeed<I, Error<I>> for ErrorKind {
    fn into_error(self, pos: I) -> Error<I> {
        Error::new(self, pos)
    }
}

impl<I> AsciiInput for I
where
    I: Input,
    I::Symbol: AsciiSymbol,
{
    fn parse_char(self) -> PResult<AsciiChar, Self> {
        <I::Symbol as AsciiSymbol>::parse_char(self)
    }

    fn parse_char_lossy(self) -> PResult<AsciiChar, Self> {
        <I::Symbol as AsciiSymbol>::parse_char_lossy(self)
    }
}

impl AsciiSymbol for AsciiChar {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = AsciiChar>,
    {
        use crate::basic::pop;
        pop(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = AsciiChar>,
    {
        use crate::basic::pop;
        pop(input)
    }
}

impl AsciiSymbol for char {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = char>,
    {
        ascii_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = char>,
    {
        ascii_char_lossy(input)
    }
}

impl AsciiSymbol for i8 {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = i8>,
    {
        ascii_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = i8>,
    {
        ascii_char_lossy(input)
    }
}

impl AsciiSymbol for u8 {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = u8>,
    {
        ascii_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = u8>,
    {
        ascii_char_lossy(input)
    }
}

impl AsciiSymbol for i16 {
    fn parse_char<I>(mut input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = i16>,
    {
        let orig_input = input.clone();
        let Some(ch) = input.next() else {
            return Err(Failure(Error::need_more_input(input), orig_input));
        };
        let Ok(ch) = (ch as u16).to_ascii_char() else {
            return Err(Failure(
                Error::non_ascii_char(orig_input.clone()),
                orig_input,
            ));
        };
        Ok(Success(ch, input))
    }

    fn parse_char_lossy<I>(mut input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = i16>,
    {
        let orig_input = input.clone();
        let Some(ch) = input.next() else {
            return Err(Failure(Error::need_more_input(input), orig_input));
        };
        let Ok(ch) = (ch as u16).to_ascii_char() else {
            return Ok(Success(AsciiChar::SUB, input));
        };
        Ok(Success(ch, input))
    }
}

impl AsciiSymbol for u16 {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = u16>,
    {
        ascii_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = u16>,
    {
        ascii_char_lossy(input)
    }
}

impl AsciiSymbol for i32 {
    fn parse_char<I>(mut input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = i32>,
    {
        let orig_input = input.clone();
        let Some(ch) = input.next() else {
            return Err(Failure(Error::need_more_input(input), orig_input));
        };
        let Ok(ch) = (ch as u32).to_ascii_char() else {
            return Err(Failure(
                Error::non_ascii_char(orig_input.clone()),
                orig_input,
            ));
        };
        Ok(Success(ch, input))
    }

    fn parse_char_lossy<I>(mut input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = i32>,
    {
        let orig_input = input.clone();
        let Some(ch) = input.next() else {
            return Err(Failure(Error::need_more_input(input), orig_input));
        };
        let Ok(ch) = (ch as u32).to_ascii_char() else {
            return Ok(Success(AsciiChar::SUB, input));
        };
        Ok(Success(ch, input))
    }
}

impl AsciiSymbol for u32 {
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = u32>,
    {
        ascii_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = u32>,
    {
        ascii_char_lossy(input)
    }
}

fn ascii_char<I>(mut input: I) -> PResult<AsciiChar, I>
where
    I: Input,
    I::Symbol: ToAsciiChar,
{
    let orig_input = input.clone();
    let Some(ch) = input.next() else {
        return Err(Failure(Error::need_more_input(input), orig_input));
    };
    let Ok(ch) = ch.to_ascii_char() else {
        return Err(Failure(
            Error::non_ascii_char(orig_input.clone()),
            orig_input,
        ));
    };
    Ok(Success(ch, input))
}

fn ascii_char_lossy<I>(mut input: I) -> PResult<AsciiChar, I>
where
    I: Input,
    I::Symbol: ToAsciiChar,
{
    let orig_input = input.clone();
    let Some(ch) = input.next() else {
        return Err(Failure(Error::need_more_input(input), orig_input));
    };
    let Ok(ch) = ch.to_ascii_char() else {
        return Ok(Success(AsciiChar::SUB, input));
    };
    Ok(Success(ch, input))
}
