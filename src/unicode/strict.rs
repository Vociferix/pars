//! Parsers that treat any invalid Unicode as a parse error.
//!
//! Input that is not valid Unicode, such as invalid UTF-8 encodings or invalid code points,
//! immediately causes these parsers to fail.

use super::{
    Error, PResult, Property, UnicodeInput,
    prop::{
        ExtendedPictographic, GraphemeClusterBreak, IndicConjunctBreak, LineBreak, any, not, or,
    },
};
use crate::{
    Error as PError, Failure, IntoInput, Parse, ParseExt, Span, Success,
    basic::{alt, eof, seq},
};
use ::core::marker::PhantomData;

/// Generates a parser that matches a regular expression over [`UnicodeInput`](super::UnicodeInput).
///
/// Behaves like [`bytes::regex`](crate::bytes::regex), but the generated parser works over
/// any [`UnicodeInput`](super::UnicodeInput). The regex is matched against the Unicode
/// character stream. If the input encoding is invalid, the parser fails, consistent with
/// the rest of this module.
///
/// Full Unicode character classes and properties are supported, e.g. `\p{Letter}`,
/// `\p{Alphabetic}`, `\p{Script=Latin}`. The regex operates on Unicode code points, not
/// bytes.
///
/// The parsed value is `()`. Use [`recognize`](crate::ParseExt::recognize) to capture the
/// matched input span.
///
/// # Example
/// ```
/// use pars::unicode::strict::regex;
/// use pars::prelude::*;
/// use pars::unicode::PResult;
///
/// fn word(input: &str) -> PResult<&str, &str> {
///     regex!(r"\p{Alphabetic}+").recognize().ok_into().parse(input)
/// }
///
/// assert_eq!(word.parse("hello world"), Ok(Success("hello", " world")));
/// assert_eq!(word.parse("café"), Ok(Success("café", "")));
/// assert!(word.parse("123").is_err());
/// ```
pub use pars_macros::regex_unicode_strict as regex;

/// Parser that extracts one Unicode character from the input.
///
/// Fails if the input contains an invalid Unicode encoding (e.g. invalid UTF-8,
/// invalid UTF-16 surrogate pair, or an out-of-range code point). The exact error
/// kind returned depends on the encoding of the input.
///
/// For the equivalent parser that replaces invalid input with `U+FFFD`, see
/// [`lossy::char`](super::lossy::char).
///
/// # Example
/// ```
/// use pars::unicode::strict::char;
/// use pars::prelude::*;
/// use pars::unicode::PResult;
///
/// assert_eq!(char.parse("hello"), Ok(Success('h', "ello")));
/// assert_eq!(char.parse("😊 world"), Ok(Success('😊', " world")));
/// assert!(char.parse("").is_err()); // empty input
/// ```
pub fn char<I: UnicodeInput>(input: I) -> PResult<::core::primitive::char, I> {
    I::parse_char(input)
}

#[derive(Debug, Clone)]
struct CharWithPropParser<P, I>(P, PhantomData<I>)
where
    P: Property,
    I: UnicodeInput;

impl<P, I> Parse<I> for CharWithPropParser<P, I>
where
    P: Property,
    I: UnicodeInput,
{
    type Parsed = ::core::primitive::char;
    type Error = Error<I>;

    fn parse<N>(&self, input: N) -> PResult<::core::primitive::char, I>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match input.clone().parse_char() {
            Ok(Success(ch, rem)) if self.0.contains(ch) => Ok(Success(ch, rem)),
            Ok(_) => Err(Failure(Error::invalid_input(input.clone()), input)),
            Err(Failure(err, _)) => Err(Failure(err, input)),
        }
    }
}

/// Creates a parser that matches one Unicode character satisfying a property.
///
/// Reads one character from the input using [`UnicodeInput::parse_char`] and
/// checks whether it satisfies `property`. If the character does not satisfy the
/// property, an [`ErrorKind::InvalidInput`](super::ErrorKind::InvalidInput) error
/// is returned. If the input encoding is invalid, an error is returned as with
/// [`char`].
///
/// # Example
/// ```
/// use pars::unicode::{prop::Alphabetic, strict::char_with_prop, PResult};
/// use pars::prelude::*;
///
/// fn letter(input: &str) -> PResult<char, &str> {
///     char_with_prop(Alphabetic).parse(input)
/// }
///
/// assert_eq!(letter.parse("hello"), Ok(Success('h', "ello")));
/// assert!(letter.parse("123").is_err());
/// ```
#[inline]
pub const fn char_with_prop<P, I>(
    property: P,
) -> impl Parse<I, Parsed = ::core::primitive::char, Error = Error<I>>
where
    P: Property,
    I: UnicodeInput,
{
    CharWithPropParser(property, PhantomData)
}

#[derive(Debug, Clone)]
struct VerbatimParser<P, I>(P, PhantomData<I>)
where
    P: AsRef<str>,
    I: UnicodeInput;

impl<P, I> Parse<I> for VerbatimParser<P, I>
where
    P: AsRef<str>,
    I: UnicodeInput,
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

/// Creates a parser that exactly matches a Unicode string in the input.
///
/// The returned parser succeeds if the input begins with exactly the sequence of
/// Unicode characters in `pattern`. On success, the matched input span is returned
/// as the parsed value. Comparison is character-by-character (codepoint equality);
/// no Unicode normalization is performed. Fails if any character does not match or
/// if the input encoding is invalid.
///
/// # Example
/// ```
/// use pars::unicode::strict::verbatim;
/// use pars::prelude::*;
/// use pars::unicode::PResult;
///
/// fn hello(input: &str) -> PResult<&str, &str> {
///     verbatim("hello").ok_into().parse(input)
/// }
///
/// assert_eq!(hello.parse("hello world"), Ok(Success("hello", " world")));
/// assert!(hello.parse("Hello World").is_err()); // case-sensitive
/// ```
#[inline]
pub const fn verbatim<P, I>(pattern: P) -> impl Parse<I, Parsed = Span<I>, Error = Error<I>>
where
    P: AsRef<str>,
    I: UnicodeInput,
{
    VerbatimParser(pattern, PhantomData)
}

/// Parser that reads characters up to and including the next Unicode line terminator.
///
/// Reads Unicode characters until one of the following terminators is encountered:
/// any character with the `LineBreak=MandatoryBreak` property, CRLF (`\r\n`),
/// characters with `LineBreak=CarriageReturn`, `LineBreak=LineFeed`, or
/// `LineBreak=NextLine`, or end of input. The returned [`Span`] covers the entire
/// consumed input including the terminator (if present). When the line ends at end
/// of input, the terminator is absent and the span covers only the line content.
///
/// Fails if the input is completely empty (no characters and no terminator). Fails
/// on invalid Unicode encoding. An input containing only a line terminator succeeds
/// and returns a span containing just the terminator.
///
/// For lossy behavior that replaces invalid Unicode rather than failing, see
/// [`lossy::line`](super::lossy::line).
///
/// # Example
/// ```
/// use pars::unicode::strict::line;
/// use pars::prelude::*;
/// use pars::unicode::PResult;
///
/// fn first_line(input: &str) -> PResult<&str, &str> {
///     line.ok_into().parse(input)
/// }
///
/// assert_eq!(first_line.parse("hello\nworld"), Ok(Success("hello\n", "world")));
/// assert_eq!(first_line.parse("no newline"), Ok(Success("no newline", "")));
/// assert!(first_line.parse("").is_err());
/// ```
pub fn line<I: UnicodeInput>(input: I) -> PResult<Span<I>, I> {
    char.repeated_until(
        alt!(
            eof,
            char_with_prop(LineBreak::MandatoryBreak).with_value(()),
            seq!(
                char_with_prop(LineBreak::CarriageReturn).with_value(()),
                char_with_prop(LineBreak::LineFeed).with_value(()),
            )
            .with_value(()),
            char_with_prop(any!(
                LineBreak::CarriageReturn,
                LineBreak::LineFeed,
                LineBreak::NextLine
            ))
            .with_value(()),
        )
        .with_value(()),
        |_| (),
    )
    .recognize()
    .verify(|span| !span.is_empty())
    .parse(input)
}

fn l<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::L)
        .with_value(())
        .parse(input)
}

fn v<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::V)
        .with_value(())
        .parse(input)
}

fn lv<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::LV)
        .with_value(())
        .parse(input)
}

fn lvt<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::LVT)
        .with_value(())
        .parse(input)
}

fn t<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::T)
        .with_value(())
        .parse(input)
}

fn hangul_syllable<I: UnicodeInput>(input: I) -> PResult<(), I> {
    alt!(
        seq!(
            l.repeated(.., |_| ()),
            alt!(
                v.repeated(1.., |_| ()),
                seq!(lv, v.repeated(.., |_| ())).with_value(()),
                lvt,
            ),
            t.repeated(.., |_| ())
        )
        .with_value(()),
        l.repeated(1.., |_| ()),
        t.repeated(1.., |_| ()),
    )
    .parse(input)
}

fn cr<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::CR)
        .with_value(())
        .parse(input)
}

fn lf<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::LF)
        .with_value(())
        .parse(input)
}

fn crlf<I: UnicodeInput>(input: I) -> PResult<(), I> {
    alt!(seq!(cr, lf).with_value(()), cr, lf,).parse(input)
}

fn ri<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::RegionalIndicator)
        .with_value(())
        .parse(input)
}

fn ri_sequence<I: UnicodeInput>(input: I) -> PResult<(), I> {
    ri.then(ri).with_value(()).parse(input)
}

fn extend<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::Extend)
        .with_value(())
        .parse(input)
}

fn zwj<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::ZWJ)
        .with_value(())
        .parse(input)
}

fn xpicto_sequence<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(ExtendedPictographic)
        .with_value(())
        .then(
            seq!(
                extend.repeated(.., |_| ()),
                zwj,
                char_with_prop(ExtendedPictographic).with_value(()),
            )
            .repeated(.., |_| ()),
        )
        .with_value(())
        .parse(input)
}

fn conjunct_cluster<I: UnicodeInput>(input: I) -> PResult<(), I> {
    seq!(
        char_with_prop(IndicConjunctBreak::Consonant).with_value(()),
        seq!(
            char_with_prop(or(IndicConjunctBreak::Extend, IndicConjunctBreak::Linker))
                .repeated(.., |_| ()),
            char_with_prop(IndicConjunctBreak::Linker).with_value(()),
            char_with_prop(or(IndicConjunctBreak::Extend, IndicConjunctBreak::Linker))
                .repeated(.., |_| ()),
            char_with_prop(IndicConjunctBreak::Consonant).with_value(()),
        )
        .repeated(1.., |_| ())
    )
    .with_value(())
    .parse(input)
}

fn core<I: UnicodeInput>(input: I) -> PResult<(), I> {
    alt!(
        hangul_syllable,
        ri_sequence,
        xpicto_sequence,
        conjunct_cluster,
        char_with_prop(not(any!(
            GraphemeClusterBreak::Control,
            GraphemeClusterBreak::CR,
            GraphemeClusterBreak::LF
        )))
        .with_value(()),
    )
    .parse(input)
}

fn postcore<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(any!(
        GraphemeClusterBreak::Extend,
        GraphemeClusterBreak::ZWJ,
        GraphemeClusterBreak::SpacingMark
    ))
    .with_value(())
    .parse(input)
}

fn precore<I: UnicodeInput>(input: I) -> PResult<(), I> {
    char_with_prop(GraphemeClusterBreak::Prepend)
        .with_value(())
        .parse(input)
}

/// Parser that reads one Unicode extended grapheme cluster from the input.
///
/// A grapheme cluster is a user-perceived character, which may consist of multiple
/// Unicode code points. For example, a base character followed by combining marks,
/// emoji sequences with ZWJ, Hangul syllable sequences, and regional indicator pairs
/// (flag emoji) are each parsed as a single grapheme cluster.
///
/// The returned [`Span`] covers all the code points that form the cluster. The
/// segmentation algorithm follows Unicode Standard Annex #29 (Unicode Text
/// Segmentation), including support for extended grapheme cluster rules such as
/// Hangul, emoji, regional indicators, and Indic conjunct clusters.
///
/// Fails if the input is empty or contains an invalid Unicode encoding.
///
/// # Example
/// ```
/// use pars::unicode::strict::grapheme_cluster;
/// use pars::prelude::*;
/// use pars::unicode::PResult;
///
/// fn first_cluster(input: &str) -> PResult<&str, &str> {
///     grapheme_cluster.ok_into().parse(input)
/// }
///
/// // Simple ASCII character
/// assert_eq!(first_cluster.parse("hello"), Ok(Success("h", "ello")));
///
/// // Emoji with skin tone modifier (two code points, one cluster)
/// assert_eq!(first_cluster.parse("👋🏽 hi"), Ok(Success("👋🏽", " hi")));
/// ```
pub fn grapheme_cluster<I: UnicodeInput>(input: I) -> PResult<Span<I>, I> {
    alt!(
        crlf,
        char_with_prop(GraphemeClusterBreak::Control).with_value(()),
        seq!(
            precore.repeated(.., |_| ()),
            core,
            postcore.repeated(.., |_| ())
        )
        .with_value(()),
    )
    .recognize()
    .parse(input)
}
