//! Parsers and utilities for working with Unicode text.
//!
//! This module provides parsers for Unicode character streams, including
//! grapheme cluster segmentation, Unicode-aware line breaking, and character
//! property matching. Parsers are divided into two submodules: [`strict`] fails
//! on invalid Unicode encodings, while [`lossy`] replaces them with the Unicode
//! Replacement Character `U+FFFD`.
//!
//! The [`prop`] module provides Unicode character properties sourced from ICU
//! data tables, for use with [`strict::char_with_prop`] and
//! [`lossy::char_with_prop`]. The [`LocInput`] type wraps any [`UnicodeInput`]
//! to track line and column positions for use in diagnostic messages.
//!
//! Use this module when working with general Unicode text. For ASCII-only input,
//! the [`ascii`](crate::ascii) module may be more appropriate. For raw binary
//! data, use the [`bytes`](crate::bytes) module.

use crate::{Error as PError, Failure, Input, Success};

pub mod lossy;
pub mod prop;
pub mod strict;

mod loc;

pub use loc::*;

/// An [`ErrorSeed`](crate::ErrorSeed) for errors raised while parsing a Unicode character stream.
///
/// In addition to the three standard error kinds shared with other modules,
/// this enum includes variants for Unicode-specific failure modes.
///
/// See also [`Error`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorKind {
    /// End of input was reached when more characters were expected.
    NeedMoreInput,
    /// More input was available when the end of input was expected.
    ExpectedEof,
    /// Failed to parse due to an invalid character or value.
    InvalidInput,
    /// An invalid UTF-8 byte sequence was encountered.
    InvalidUtf8,
    /// An invalid UTF-16 code unit sequence was encountered.
    InvalidUtf16,
    /// A numeric value was not a valid Unicode code point.
    InvalidCodePoint,
}

/// A Unicode character stream parsing error.
///
/// See also [`ErrorKind`].
///
/// # Example
/// ```
/// use pars::unicode::{strict, ErrorKind, PResult};
/// use pars::prelude::*;
///
/// let err = strict::char.parse("").unwrap_err().0;
/// assert_eq!(err.kind(), ErrorKind::NeedMoreInput);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error<I: Input> {
    kind: ErrorKind,
    pos: I,
}

/// The [`Result`](crate::PResult) type returned by Unicode character stream parsers.
pub type PResult<T, I> = super::PResult<T, I, Error<I>>;

/// Trait for input symbol types that can be interpreted as Unicode characters.
///
/// [`UnicodeSymbol`] is implemented for common types from which a [`char`] can be
/// extracted, covering the main Unicode encodings:
///
/// - [`char`] — native Rust Unicode scalar values, always valid
/// - [`u8`] / [`i8`] — UTF-8 encoded bytes
/// - [`u16`] / [`i16`] — UTF-16 code units
/// - [`u32`] / [`i32`] — UTF-32 code points (one code point per element)
/// - [`AsciiChar`](crate::ascii::AsciiChar) — ASCII characters (always valid Unicode)
///
/// For each encoding there are two variants: a strict method that fails on invalid
/// input, and a lossy method that replaces invalid sequences with the Unicode
/// Replacement Character `U+FFFD`.
pub trait UnicodeSymbol {
    /// Extracts one [`char`] from the input, failing on invalid Unicode.
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = Self>;

    /// Extracts one [`char`] from the input, replacing invalid Unicode with `U+FFFD`.
    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = Self>;

    /// Extracts one character and writes its UTF-8 encoding into `buf`, failing on invalid Unicode.
    ///
    /// `buf` must be at least 4 bytes long.
    fn parse_utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char(input)?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    /// Extracts one character and writes its UTF-8 encoding into `buf`, replacing invalid Unicode with `U+FFFD`.
    ///
    /// `buf` must be at least 4 bytes long.
    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char_lossy(input)?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    /// Extracts one character and writes its UTF-16 encoding into `buf`, failing on invalid Unicode.
    ///
    /// `buf` must be at least 2 elements long.
    fn parse_utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char(input)?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }

    /// Extracts one character and writes its UTF-16 encoding into `buf`, replacing invalid Unicode with `U+FFFD`.
    ///
    /// `buf` must be at least 2 elements long.
    fn parse_utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char_lossy(input)?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }
}

/// An [`Input`] stream that can be parsed as Unicode characters.
///
/// [`UnicodeInput`] is automatically implemented for any [`Input`] whose symbol
/// type implements [`UnicodeSymbol`]. It provides convenience methods that
/// dispatch to the appropriate [`UnicodeSymbol`] implementation for the symbol
/// type.
pub trait UnicodeInput: Input {
    /// Extracts one [`char`] from the input, failing on invalid Unicode.
    fn parse_char(self) -> PResult<core::primitive::char, Self>;

    /// Extracts one [`char`] from the input, replacing invalid Unicode with `U+FFFD`.
    fn parse_char_lossy(self) -> PResult<core::primitive::char, Self>;

    /// Extracts one character and writes its UTF-8 encoding into `buf`, failing on invalid Unicode.
    ///
    /// `buf` must be at least 4 bytes long.
    fn parse_utf8(self, buf: &mut [u8]) -> PResult<&str, Self> {
        let Success(ch, rem) = self.parse_char()?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    /// Extracts one character and writes its UTF-8 encoding into `buf`, replacing invalid Unicode with `U+FFFD`.
    ///
    /// `buf` must be at least 4 bytes long.
    fn parse_utf8_lossy(self, buf: &mut [u8]) -> PResult<&str, Self> {
        let Success(ch, rem) = self.parse_char_lossy()?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    /// Extracts one character and writes its UTF-16 encoding into `buf`, failing on invalid Unicode.
    ///
    /// `buf` must be at least 2 elements long.
    fn parse_utf16(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        let Success(ch, rem) = self.parse_char()?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }

    /// Extracts one character and writes its UTF-16 encoding into `buf`, replacing invalid Unicode with `U+FFFD`.
    ///
    /// `buf` must be at least 2 elements long.
    fn parse_utf16_lossy(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        let Success(ch, rem) = self.parse_char_lossy()?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }
}

/// A predicate over [`char`] values, used to classify Unicode characters.
///
/// Types implementing [`Property`] are used with parsers such as
/// [`strict::char_with_prop`] and
/// [`lossy::char_with_prop`] to match characters with
/// specific properties. The [`prop`] module provides a large set of built-in
/// Unicode property types sourced from the ICU data tables, and properties can
/// be combined with `!`, `&`, and `|` operators.
///
/// # Example
/// ```
/// use pars::unicode::{prop::GeneralCategory, strict::char_with_prop, PResult};
/// use pars::prelude::*;
///
/// fn letter(input: &str) -> PResult<char, &str> {
///     char_with_prop(GeneralCategory::UppercaseLetter | GeneralCategory::LowercaseLetter)
///         .parse(input)
/// }
///
/// assert!(letter.parse("a").is_ok());
/// assert!(letter.parse("1").is_err());
/// ```
pub trait Property: core::fmt::Debug + Copy {
    /// Returns `true` if this property applies to `ch`.
    fn contains(self, ch: core::primitive::char) -> bool;
}

impl<I> UnicodeInput for I
where
    I: Input,
    I::Symbol: UnicodeSymbol,
{
    fn parse_char(self) -> PResult<core::primitive::char, Self> {
        <I::Symbol as UnicodeSymbol>::parse_char(self)
    }

    fn parse_char_lossy(self) -> PResult<core::primitive::char, Self> {
        <I::Symbol as UnicodeSymbol>::parse_char_lossy(self)
    }

    fn parse_utf8(self, buf: &mut [u8]) -> PResult<&str, Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf8(self, buf)
    }

    fn parse_utf8_lossy(self, buf: &mut [u8]) -> PResult<&str, Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf8_lossy(self, buf)
    }

    fn parse_utf16(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf16(self, buf)
    }

    fn parse_utf16_lossy(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf16_lossy(self, buf)
    }
}

impl UnicodeSymbol for core::primitive::char {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = core::primitive::char>,
    {
        use crate::basic::pop;
        pop(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = core::primitive::char>,
    {
        use crate::basic::pop;
        pop(input)
    }
}

impl UnicodeSymbol for u32 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u32>,
    {
        utf32_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u32>,
    {
        utf32_char_lossy(input)
    }
}

impl UnicodeSymbol for i32 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i32>,
    {
        utf32_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i32>,
    {
        utf32_char_lossy(input)
    }
}

impl UnicodeSymbol for u16 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u16>,
    {
        utf16_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u16>,
    {
        utf16_char_lossy(input)
    }

    fn parse_utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = u16>,
    {
        utf16(input, buf)
    }

    fn parse_utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = u16>,
    {
        utf16_lossy(input, buf)
    }
}

impl UnicodeSymbol for i16 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i16>,
    {
        utf16_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i16>,
    {
        utf16_char_lossy(input)
    }

    fn parse_utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = i16>,
    {
        utf16(input, buf)
    }

    fn parse_utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = i16>,
    {
        utf16_lossy(input, buf)
    }
}

impl UnicodeSymbol for u8 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8_char_lossy(input)
    }

    fn parse_utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8(input, buf)
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8_lossy(input, buf)
    }
}

impl UnicodeSymbol for i8 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8_char_lossy(input)
    }

    fn parse_utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8(input, buf)
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8_lossy(input, buf)
    }
}

#[cfg(feature = "ascii")]
impl UnicodeSymbol for crate::ascii::AsciiChar {
    fn parse_char<I>(mut input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        let ch = input.next();
        match ch {
            Some(ch) => Ok(Success(ch.into(), input)),
            None => Err(Failure(Error::need_more_input(input.clone()), input)),
        }
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        Self::parse_char(input)
    }

    fn parse_utf8<I>(mut input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        let ch = input.next();
        match ch {
            Some(ch) => {
                buf[0] = ch.into();
                Ok(Success(
                    unsafe { str::from_utf8_unchecked(&buf[..1]) },
                    input,
                ))
            }
            None => Err(Failure(Error::need_more_input(input.clone()), input)),
        }
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        Self::parse_utf8(input, buf)
    }
}

trait IntoU8 {
    fn into_u8(self) -> u8;
}

impl IntoU8 for u8 {
    fn into_u8(self) -> u8 {
        self
    }
}

impl IntoU8 for i8 {
    fn into_u8(self) -> u8 {
        self.cast_unsigned()
    }
}

trait IntoU16 {
    fn into_u16(self) -> u16;
}

impl IntoU16 for u16 {
    fn into_u16(self) -> u16 {
        self
    }
}

impl IntoU16 for i16 {
    fn into_u16(self) -> u16 {
        self.cast_unsigned()
    }
}

trait IntoU32 {
    fn into_u32(self) -> u32;
}

impl IntoU32 for u32 {
    fn into_u32(self) -> u32 {
        self
    }
}

impl IntoU32 for i32 {
    fn into_u32(self) -> u32 {
        self.cast_unsigned()
    }
}

fn utf32_char<I>(mut input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: IntoU32,
{
    if let Some(ch) = input.next() {
        if let Some(ch) = core::primitive::char::from_u32(ch.into_u32()) {
            Ok(Success(ch, input))
        } else {
            Err(Failure(Error::invalid_code_point(input.clone()), input))
        }
    } else {
        Err(Failure(Error::need_more_input(input.clone()), input))
    }
}

fn utf32_char_lossy<I>(mut input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: IntoU32,
{
    if let Some(ch) = input.next() {
        if let Some(ch) = core::primitive::char::from_u32(ch.into_u32()) {
            Ok(Success(ch, input))
        } else {
            Ok(Success('\u{fffd}', input))
        }
    } else {
        Err(Failure(Error::need_more_input(input.clone()), input))
    }
}

fn utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
where
    I: Input,
    I::Symbol: IntoU16,
{
    let mut len = 1usize;
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(IntoU16::into_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    buf[0] = c0;
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(IntoU16::into_u16) else {
            return Err(Failure(Error::need_more_input(rem), input));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            return Err(Failure(Error::invalid_utf16(tmp), input));
        }
        buf[1] = c1;
        len = 2;
        let c0 = u32::from(c0 & 0b0000_0011_1111_1111);
        let c1 = u32::from(c1 & 0b0000_0011_1111_1111);
        ((c0 << 10) | c1) + 0x10000
    } else {
        u32::from(c0)
    };
    if core::primitive::char::from_u32(ch).is_some() {
        Ok(Success(&buf[..len], rem))
    } else {
        Err(Failure(Error::invalid_code_point(input.clone()), input))
    }
}

fn utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
where
    I: Input,
    I::Symbol: IntoU16,
{
    let mut len = 1usize;
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(IntoU16::into_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    buf[0] = c0;
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(IntoU16::into_u16) else {
            buf[0] = 0xfffd;
            return Ok(Success(&buf[..1], rem));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            buf[0] = 0xfffd;
            return Ok(Success(&buf[..1], tmp));
        }
        buf[1] = c1;
        len = 2;
        let c0 = u32::from(c0 & 0b0000_0011_1111_1111);
        let c1 = u32::from(c1 & 0b0000_0011_1111_1111);
        ((c0 << 10) | c1) + 0x10000
    } else {
        u32::from(c0)
    };
    if core::primitive::char::from_u32(ch).is_some() {
        Ok(Success(&buf[..len], rem))
    } else {
        buf[0] = 0xfffd;
        Ok(Success(&buf[..1], input))
    }
}

fn utf16_char<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: IntoU16,
{
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(IntoU16::into_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(IntoU16::into_u16) else {
            return Err(Failure(Error::need_more_input(rem), input));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            return Err(Failure(Error::invalid_utf16(tmp), input));
        }
        let c0 = u32::from(c0 & 0b0000_0011_1111_1111);
        let c1 = u32::from(c1 & 0b0000_0011_1111_1111);
        ((c0 << 10) | c1) + 0x10000
    } else {
        u32::from(c0)
    };
    if let Some(ch) = core::primitive::char::from_u32(ch) {
        Ok(Success(ch, rem))
    } else {
        Err(Failure(Error::invalid_code_point(input.clone()), input))
    }
}

fn utf16_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: IntoU16,
{
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(IntoU16::into_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(IntoU16::into_u16) else {
            return Ok(Success('\u{fffd}', rem));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let c0 = u32::from(c0 & 0b0000_0011_1111_1111);
        let c1 = u32::from(c1 & 0b0000_0011_1111_1111);
        ((c0 << 10) | c1) + 0x10000
    } else {
        u32::from(c0)
    };
    if let Some(ch) = core::primitive::char::from_u32(ch) {
        Ok(Success(ch, rem))
    } else {
        Ok(Success('\u{fffd}', input))
    }
}

fn utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
where
    I: Input,
    I::Symbol: IntoU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(IntoU8::into_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if char::from_u32(b0.into()).is_some() {
        buf[0] = b0;
        Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..1]) }, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        buf[0] = b0;
        buf[1] = b1;
        let b0 = u32::from(b0) & 0b0001_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if char::from_u32(ch).is_some() {
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..2]) }, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        let b0 = u32::from(b0) & 0b0000_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if char::from_u32(ch).is_some() {
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        buf[3] = b3;
        let b0 = u32::from(b0) & 0b0000_0111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let b3 = u32::from(b3) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if char::from_u32(ch).is_some() {
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..4]) }, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else {
        Err(Failure(Error::invalid_utf8(input.clone()), input))
    }
}

fn utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
where
    I: Input,
    I::Symbol: IntoU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(IntoU8::into_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if char::from_u32(b0.into()).is_some() {
        buf[0] = b0;
        Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..1]) }, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        }
        buf[0] = b0;
        buf[1] = b1;
        let b0 = u32::from(b0) & 0b0001_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if char::from_u32(ch).is_some() {
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..2]) }, rem))
        } else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, rem))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        let b0 = u32::from(b0) & 0b0000_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if char::from_u32(ch).is_some() {
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, rem))
        } else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, rem))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(IntoU8::into_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        buf[3] = b3;
        let b0 = u32::from(b0) & 0b0000_0111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let b3 = u32::from(b3) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if char::from_u32(ch).is_some() {
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..4]) }, rem))
        } else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, rem))
        }
    } else {
        let mut tmp = rem.clone();
        while rem.next().map(IntoU8::into_u8).map(|b| b & 0b1100_0000) == Some(0b1000_0000) {
            tmp = rem.clone();
        }
        buf[0] = 0xef;
        buf[1] = 0xbf;
        buf[2] = 0xbd;
        Ok(Success(unsafe { str::from_utf8_unchecked(&buf[..3]) }, tmp))
    }
}

fn utf8_char<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: IntoU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(IntoU8::into_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if let Some(ch) = char::from_u32(b0.into()) {
        Ok(Success(ch, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let b0 = u32::from(b0) & 0b0001_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let b0 = u32::from(b0) & 0b0000_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(IntoU8::into_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let b0 = u32::from(b0) & 0b0000_0111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let b3 = u32::from(b3) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else {
        Err(Failure(Error::invalid_utf8(input.clone()), input))
    }
}

fn utf8_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: IntoU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(IntoU8::into_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if let Some(ch) = char::from_u32(b0.into()) {
        Ok(Success(ch, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let b0 = u32::from(b0) & 0b0001_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Ok(Success('\u{fffd}', rem))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let b0 = u32::from(b0) & 0b0000_1111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Ok(Success('\u{fffd}', rem))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(IntoU8::into_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(IntoU8::into_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(IntoU8::into_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let b0 = u32::from(b0) & 0b0000_0111;
        let b1 = u32::from(b1) & 0b0011_1111;
        let b2 = u32::from(b2) & 0b0011_1111;
        let b3 = u32::from(b3) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Ok(Success('\u{fffd}', rem))
        }
    } else {
        let mut tmp = rem.clone();
        while rem.next().map(IntoU8::into_u8).map(|b| b & 0b1100_0000) == Some(0b1000_0000) {
            tmp = rem.clone();
        }
        Ok(Success('\u{fffd}', tmp))
    }
}

impl<I: Input> Error<I> {
    /// Constructs a new [`Error`] from an [`ErrorKind`] and an input position.
    pub const fn new(kind: ErrorKind, pos: I) -> Self {
        Self { kind, pos }
    }

    /// Constructs a new error representing an invalid UTF-8 byte sequence.
    pub const fn invalid_utf8(pos: I) -> Self {
        Self::new(ErrorKind::InvalidUtf8, pos)
    }

    /// Constructs a new error representing an invalid UTF-16 code unit sequence.
    pub const fn invalid_utf16(pos: I) -> Self {
        Self::new(ErrorKind::InvalidUtf16, pos)
    }

    /// Constructs a new error representing a value that is not a valid Unicode code point.
    pub const fn invalid_code_point(pos: I) -> Self {
        Self::new(ErrorKind::InvalidCodePoint, pos)
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
