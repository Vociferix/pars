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

/// An [`ErrorSeed`](crate::ErrorSeed) for errors raised while parsing an ASCII character stream.
///
/// See also [`Error`].
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorKind {
    /// End of input was reached when more characters were expected.
    NeedMoreInput,
    /// More input was available when the end of input was expected.
    ExpectedEof,
    /// Failed to parse due to an invalid character or value.
    InvalidInput,
    /// A non-ASCII character was encountered when strict ASCII was required.
    ///
    /// This variant is produced by parsers in the [`strict`] module when a
    /// character not in the ASCII range (`0x00`–`0x7F`) is encountered. The
    /// [`lossy`] module never produces this variant — instead it substitutes
    /// the character with [`AsciiChar::SUB`].
    NonAsciiChar,
}

/// An ASCII character stream parsing error.
///
/// See also [`ErrorKind`].
///
/// # Example
/// ```
/// use pars::ascii::{strict, ErrorKind, PResult};
/// use pars::prelude::*;
///
/// let err = strict::char.parse("é").unwrap_err().0;
/// assert_eq!(err.kind(), ErrorKind::NonAsciiChar);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error<I: Input> {
    kind: ErrorKind,
    pos: I,
}

/// The [`Result`](crate::PResult) type returned by ASCII character stream parsers.
pub type PResult<T, I> = super::PResult<T, I, Error<I>>;

/// Trait for input symbol types that can be interpreted as ASCII characters.
///
/// [`AsciiSymbol`] is implemented for common types from which an [`AsciiChar`] can
/// be extracted, including [`u8`], [`i8`], [`u16`], [`i16`], [`u32`], [`i32`], [`char`],
/// and [`AsciiChar`] itself.
///
/// There are two methods: [`parse_char`](AsciiSymbol::parse_char) which fails on
/// non-ASCII input, and [`parse_char_lossy`](AsciiSymbol::parse_char_lossy) which
/// replaces non-ASCII input with [`AsciiChar::SUB`].
pub trait AsciiSymbol {
    /// Extracts one [`AsciiChar`] from the input stream, failing on non-ASCII input.
    fn parse_char<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = Self>;

    /// Extracts one [`AsciiChar`] from the input stream, replacing non-ASCII with [`AsciiChar::SUB`].
    fn parse_char_lossy<I>(input: I) -> PResult<AsciiChar, I>
    where
        I: Input<Symbol = Self>;
}

/// An [`Input`] stream that can be parsed as ASCII characters.
///
/// [`AsciiInput`] is automatically implemented for any [`Input`] whose symbol type
/// implements [`AsciiSymbol`]. It provides convenience methods for extracting
/// [`AsciiChar`] values from the stream.
pub trait AsciiInput: Input {
    /// Extracts one [`AsciiChar`] from the input stream, failing on non-ASCII input.
    fn parse_char(self) -> PResult<AsciiChar, Self>;

    /// Extracts one [`AsciiChar`] from the input stream, replacing non-ASCII with [`AsciiChar::SUB`].
    fn parse_char_lossy(self) -> PResult<AsciiChar, Self>;
}

/// A predicate over [`AsciiChar`] values, used to classify characters.
///
/// Types implementing [`Property`] are used with parsers such as
/// [`strict::char_with_prop`] and
/// [`lossy::char_with_prop`] to match characters with
/// specific properties. The [`prop`] module provides a set of built-in property
/// types, and properties can be combined with `!`, `&`, and `|` operators.
///
/// # Example
/// ```
/// use pars::ascii::{prop::Digit, strict::char_with_prop, PResult};
/// use pars::prelude::*;
///
/// fn decimal_digit(input: &str) -> PResult<pars::ascii::AsciiChar, &str> {
///     char_with_prop(Digit).parse(input)
/// }
///
/// assert!(decimal_digit.parse("5").is_ok());
/// assert!(decimal_digit.parse("a").is_err());
/// ```
pub trait Property: core::fmt::Debug + Copy {
    /// Returns `true` if this property applies to `ch`.
    fn contains(self, ch: AsciiChar) -> bool;
}

impl<I: Input> Error<I> {
    /// Constructs a new [`Error`] from an [`ErrorKind`] and an input position.
    pub const fn new(kind: ErrorKind, pos: I) -> Self {
        Self { kind, pos }
    }

    /// Constructs a new error representing a non-ASCII character in the input.
    pub const fn non_ascii_char(pos: I) -> Self {
        Self::new(ErrorKind::NonAsciiChar, pos)
    }

    /// Returns the [`ErrorKind`] describing why parsing failed.
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
        let Ok(ch) = ch.cast_unsigned().to_ascii_char() else {
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
        let Ok(ch) = ch.cast_unsigned().to_ascii_char() else {
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
        let Ok(ch) = ch.cast_unsigned().to_ascii_char() else {
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
        let Ok(ch) = ch.cast_unsigned().to_ascii_char() else {
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
