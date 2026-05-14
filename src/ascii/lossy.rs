//! Parsers that replace non-ASCII input with a substitute character.
//!
//! When a non-ASCII character is encountered in the input stream, these parsers
//! substitute it with [`AsciiChar::SUB`] (the ASCII substitute control character,
//! `0x1A`) and continue parsing. This allows parsing to succeed even in the
//! presence of non-ASCII characters, at the cost of potentially losing information.
//!
//! For applications that should reject non-ASCII input outright, use the
//! [`strict`](super::strict) module instead.

use super::{AsciiChar, AsciiInput, AsciiStr, Error, PResult, Property, ascii};
use crate::{
    Error as PError, Failure, IntoInput, Parse, ParseExt, Span, Success,
    basic::{alt, eof},
};
use core::marker::PhantomData;

/// Generates a parser that matches a regular expression over [`AsciiInput`].
///
/// Behaves like [`ascii::strict::regex`](super::strict::regex), but non-ASCII input is
/// treated as [`AsciiChar::SUB`] (the ASCII substitute character,
/// `0x1A`) rather than causing a parse failure. The regex is then matched against the
/// resulting character stream, which may include substitute characters where non-ASCII
/// input appeared.
///
/// The parsed value is `()`. Use [`recognize`](crate::ParseExt::recognize) to capture the
/// matched input span.
///
/// # Example
/// ```
/// use pars::ascii::lossy::regex;
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn digits(input: &str) -> PResult<&str, &str> {
///     regex!(r"\d+").recognize().ok_into().parse(input)
/// }
///
/// assert_eq!(digits.parse("123abc"), Ok(Success("123", "abc")));
/// assert!(digits.parse("abc").is_err());
/// ```
pub use pars_macros::regex_ascii_lossy as regex;

/// Parser that extracts one ASCII character from the input, replacing non-ASCII with [`AsciiChar::SUB`].
///
/// If the next symbol in the input is not a valid ASCII character, it is consumed
/// and replaced with [`AsciiChar::SUB`] (the ASCII substitute control character,
/// `0x1A`) rather than returning an error. This allows parsing to continue even
/// in the presence of non-ASCII input.
///
/// For strict behavior that fails on non-ASCII input, use [`strict::char`](super::strict::char).
///
/// # Example
/// ```
/// use pars::ascii::{lossy::char, AsciiChar};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// assert_eq!(char.parse("hello"), Ok(Success(AsciiChar::h, "ello")));
///
/// // Non-ASCII is replaced with SUB (0x1A)
/// assert_eq!(char.parse("é"), Ok(Success(AsciiChar::SUB, "")));
///
/// assert!(char.parse("").is_err()); // empty input still fails
/// ```
pub fn char<I: AsciiInput>(input: I) -> PResult<AsciiChar, I> {
    I::parse_char_lossy(input)
}

#[derive(Debug, Clone)]
struct VerbatimParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: AsRef<AsciiStr>,
    I: AsciiInput;

impl<P, I> Parse<I> for VerbatimParser<P, I>
where
    P: AsRef<AsciiStr>,
    I: AsciiInput,
{
    type Parsed = Span<I>;
    type Error = Error<I>;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        let expected = self.0.as_ref().chars();
        let mut rem = input.clone();

        for ex in expected {
            let tmp = rem.clone();
            match rem.parse_char_lossy() {
                Ok(Success(ch, new_rem)) => {
                    if ch != ex {
                        return Err(Failure(Error::invalid_input(tmp), input));
                    }
                    rem = new_rem;
                }
                Err(Failure(err, _)) => {
                    return Err(Failure(err, input));
                }
            }
        }

        Ok(Success(Span::new(input, rem.clone()), rem))
    }
}

/// Creates a parser that exactly matches an ASCII string in the input.
///
/// Behaves like [`strict::verbatim`](super::strict::verbatim), but uses
/// [`AsciiInput::parse_char_lossy`] to read each character. This means that
/// non-ASCII characters in the input stream are replaced with [`AsciiChar::SUB`]
/// before being compared against `pattern`. Consequently, this parser will never
/// return a [`NonAsciiChar`](super::ErrorKind::NonAsciiChar) error.
///
/// Note that this can cause surprising behavior: a non-ASCII byte in the input
/// that maps to [`AsciiChar::SUB`] will match a literal SUB character in `pattern`,
/// but not any other ASCII character.
///
/// # Example
/// ```
/// use pars::ascii::{lossy::verbatim, ascii};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn hello(input: &str) -> PResult<&str, &str> {
///     verbatim(ascii!("hello")).ok_into().parse(input)
/// }
///
/// assert_eq!(hello.parse("hello world"), Ok(Success("hello", " world")));
/// assert!(hello.parse("Hello World").is_err()); // still case-sensitive
/// ```
#[inline]
pub const fn verbatim<P, I>(pattern: P) -> impl Parse<I, Parsed = Span<I>, Error = Error<I>>
where
    P: AsRef<AsciiStr>,
    I: AsciiInput,
{
    VerbatimParser(pattern, PhantomData)
}

#[derive(Debug, Clone)]
struct CharWithPropParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Property,
    I: AsciiInput;

impl<P, I> Parse<I> for CharWithPropParser<P, I>
where
    P: Property,
    I: AsciiInput,
{
    type Parsed = AsciiChar;
    type Error = Error<I>;

    fn parse<N>(&self, input: N) -> PResult<AsciiChar, I>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match input.clone().parse_char_lossy() {
            Ok(Success(ch, rem)) if self.0.contains(ch) => Ok(Success(ch, rem)),
            Ok(_) => Err(Failure(PError::invalid_input(input.clone()), input)),
            Err(Failure(err, _)) => Err(Failure(err, input)),
        }
    }
}

/// Creates a parser that matches one ASCII character satisfying a property.
///
/// Behaves like [`strict::char_with_prop`](super::strict::char_with_prop), but uses
/// [`AsciiInput::parse_char_lossy`] to read the character. Non-ASCII input symbols
/// are replaced with [`AsciiChar::SUB`] before the property check is applied. If
/// the property does not match [`AsciiChar::SUB`], a non-ASCII character will
/// cause this parser to fail with [`ErrorKind::InvalidInput`](super::ErrorKind::InvalidInput).
///
/// # Example
/// ```
/// use pars::ascii::{prop::Digit, lossy::char_with_prop, AsciiChar};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn decimal_digit(input: &str) -> PResult<AsciiChar, &str> {
///     char_with_prop(Digit).parse(input)
/// }
///
/// assert_eq!(decimal_digit.parse("42"), Ok(Success(AsciiChar::_4, "2")));
/// assert!(decimal_digit.parse("abc").is_err());
/// assert!(decimal_digit.parse("é").is_err()); // non-ASCII → SUB → not a digit
/// ```
#[inline]
pub const fn char_with_prop<P, I>(
    property: P,
) -> impl Parse<I, Parsed = AsciiChar, Error = Error<I>>
where
    P: Property,
    I: AsciiInput,
{
    CharWithPropParser(property, PhantomData)
}

/// Parser that reads characters up to and including the next line terminator.
///
/// Behaves like [`strict::line`](super::strict::line), but uses
/// [`AsciiInput::parse_char_lossy`] to read each character. This means that
/// non-ASCII characters in the input stream are replaced with [`AsciiChar::SUB`]
/// rather than causing an error. Line terminators (CR, LF, CRLF) are still
/// recognized as ASCII characters and terminate the line normally.
///
/// The returned [`Span`] includes the line terminator if one was present, or
/// covers only the line content when the line ends at end of input. Fails on
/// completely empty input.
///
/// # Example
/// ```
/// use pars::ascii::lossy::line;
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn first_line(input: &str) -> PResult<&str, &str> {
///     line.ok_into().parse(input)
/// }
///
/// assert_eq!(first_line.parse("hello\nworld"), Ok(Success("hello\n", "world")));
/// assert_eq!(first_line.parse("no newline"), Ok(Success("no newline", "")));
/// assert!(first_line.parse("").is_err());
/// ```
pub fn line<I: AsciiInput>(input: I) -> PResult<Span<I>, I> {
    char.repeated_until(
        alt!(
            eof,
            verbatim(ascii!("\r\n")).with_value(()),
            verbatim(ascii!("\r")).with_value(()),
            verbatim(ascii!("\n")).with_value(()),
        ),
        |_| (),
    )
    .recognize()
    .verify(|span| !span.is_empty())
    .parse(input)
}
