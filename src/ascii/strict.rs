//! Parsers that treat non-ASCII input as a parse error.
//!
//! Every parser in this module is strict about the validity of the input. When a
//! non-ASCII character is encountered in the input stream, the parser immediately
//! returns an error with kind [`ErrorKind::NonAsciiChar`](super::ErrorKind::NonAsciiChar).
//!
//! For applications where non-ASCII characters should be silently skipped or
//! replaced rather than cause an error, use the [`lossy`](super::lossy) module
//! instead.

use super::{AsciiChar, AsciiInput, AsciiStr, Error, PResult, Property, ascii};
use crate::{
    Error as PError, Failure, IntoInput, Parse, ParseExt, Span, Success,
    basic::{alt, eof},
};
use core::marker::PhantomData;

/// Generates a parser that matches a regular expression over [`AsciiInput`](super::AsciiInput).
///
/// Behaves like [`bytes::regex`](crate::bytes::regex), but the generated parser works over
/// any [`AsciiInput`](super::AsciiInput). The regex is matched against the ASCII character
/// stream. If non-ASCII input is encountered, the parser fails with
/// [`ErrorKind::NonAsciiChar`](super::ErrorKind::NonAsciiChar), consistent with the rest of
/// this module.
///
/// The parsed value is `()`. Use [`recognize`](crate::ParseExt::recognize) to capture the
/// matched input span.
///
/// # Example
/// ```
/// use pars::ascii::strict::regex;
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
pub use pars_macros::regex_ascii_strict as regex;

/// Parser that extracts one ASCII character from the input.
///
/// Fails with [`ErrorKind::NonAsciiChar`](super::ErrorKind::NonAsciiChar) if the next
/// symbol in the input cannot be represented as an ASCII character.
///
/// # Example
/// ```
/// use pars::ascii::{strict::char, AsciiChar};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// assert_eq!(char.parse("hello"), Ok(Success(AsciiChar::h, "ello")));
/// assert!(char.parse("é").is_err()); // non-ASCII
/// assert!(char.parse("").is_err());  // empty input
/// ```
pub fn char<I: AsciiInput>(input: I) -> PResult<AsciiChar, I> {
    I::parse_char(input)
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
            match rem.parse_char() {
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
/// The returned parser succeeds if the input begins with exactly the sequence of
/// ASCII characters represented by `pattern`. On success, the matched input span
/// is returned as the parsed value. Fails if any character in the input does not
/// match the next character in `pattern`, or if `pattern` contains non-ASCII characters
/// (which, given the type constraint on `pattern`, can only arise through unsafe code).
///
/// Unlike [`basic::verbatim`](crate::basic::verbatim), this parser always uses
/// [`AsciiInput::parse_char`] for character extraction, so it strictly validates ASCII.
///
/// # Example
/// ```
/// use pars::ascii::{strict::verbatim, ascii};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn hello(input: &str) -> PResult<&str, &str> {
///     verbatim(ascii!("hello")).ok_into().parse(input)
/// }
///
/// assert_eq!(hello.parse("hello world"), Ok(Success("hello", " world")));
/// assert!(hello.parse("Hello World").is_err()); // case-sensitive
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
        match input.clone().parse_char() {
            Ok(Success(ch, rem)) if self.0.contains(ch) => Ok(Success(ch, rem)),
            Ok(_) => Err(Failure(PError::invalid_input(input.clone()), input)),
            Err(Failure(err, _)) => Err(Failure(err, input)),
        }
    }
}

/// Creates a parser that matches one ASCII character satisfying a property.
///
/// The returned parser reads one character from the input using
/// [`AsciiInput::parse_char`] and then checks whether the character satisfies
/// `property`. If the character does not satisfy the property, an
/// [`ErrorKind::InvalidInput`](super::ErrorKind::InvalidInput) error is returned.
/// If the input is non-ASCII, an error is returned as with [`char`].
///
/// # Example
/// ```
/// use pars::ascii::{prop::Digit, strict::char_with_prop, AsciiChar};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn decimal_digit(input: &str) -> PResult<AsciiChar, &str> {
///     char_with_prop(Digit).parse(input)
/// }
///
/// assert_eq!(decimal_digit.parse("42"), Ok(Success(AsciiChar::_4, "2")));
/// assert!(decimal_digit.parse("abc").is_err());
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
/// Reads ASCII characters until one of the following terminators is encountered:
/// CR (`\r`), LF (`\n`), CRLF (`\r\n`), or end of input. The returned [`Span`]
/// covers the entire line content including the terminator (if present). When the
/// line ends at end of input, the terminator is absent and the span covers only
/// the line content.
///
/// Fails if the input is completely empty (no characters and no terminator). An
/// input containing only a line terminator (e.g. `"\n"`) succeeds and returns a
/// span containing just the terminator.
///
/// # Example
/// ```
/// use pars::ascii::strict::line;
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn first_line(input: &str) -> PResult<&str, &str> {
///     line.ok_into().parse(input)
/// }
///
/// assert_eq!(first_line.parse("hello\nworld"), Ok(Success("hello\n", "world")));
/// assert_eq!(first_line.parse("no newline"), Ok(Success("no newline", "")));
/// assert!(first_line.parse("").is_err()); // empty input fails
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
