//! Parsers that treat any invalid Unicode as a parse error.
//!
//! Input that is not valid Unicode, such as invalid UTF-8 encodings or invalid code points,
//! immediately causes these parsers to fail.

use super::{
    prop::{
        any, not, or, ExtendedPictographic, GraphemeClusterBreak, IndicConjunctBreak, LineBreak,
    },
    Error, PResult, Property, UnicodeInput,
};
use crate::{
    basic::{alt, eof, seq},
    Error as PError, Failure, IntoInput, Parse, Span, Success,
};
use ::core::marker::PhantomData;

pub use pars_macros::regex_unicode_strict as regex;

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
        let mut expected = self.0.as_ref().chars();
        let mut rem = input.clone();

        while let Some(ex) = expected.next() {
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

#[inline]
pub const fn verbatim<P, I>(pattern: P) -> impl Parse<I, Parsed = Span<I>, Error = Error<I>>
where
    P: AsRef<str>,
    I: UnicodeInput,
{
    VerbatimParser(pattern, PhantomData)
}

pub fn line<I: UnicodeInput>(input: I) -> PResult<Span<I>, I> {
    char.many_until(
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
            l.many0(|_| ()),
            alt!(
                v.many1(|_| ()),
                seq!(lv, v.many0(|_| ())).with_value(()),
                lvt,
            ),
            t.many0(|_| ())
        )
        .with_value(()),
        l.many1(|_| ()),
        t.many1(|_| ()),
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
                extend.many0(|_| ()),
                zwj,
                char_with_prop(ExtendedPictographic).with_value(()),
            )
            .many0(|_| ()),
        )
        .with_value(())
        .parse(input)
}

fn conjunct_cluster<I: UnicodeInput>(input: I) -> PResult<(), I> {
    seq!(
        char_with_prop(IndicConjunctBreak::Consonant).with_value(()),
        seq!(
            char_with_prop(or(IndicConjunctBreak::Extend, IndicConjunctBreak::Linker))
                .many0(|_| ()),
            char_with_prop(IndicConjunctBreak::Linker).with_value(()),
            char_with_prop(or(IndicConjunctBreak::Extend, IndicConjunctBreak::Linker))
                .many0(|_| ()),
            char_with_prop(IndicConjunctBreak::Consonant).with_value(()),
        )
        .many1(|_| ())
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

pub fn grapheme_cluster<I: UnicodeInput>(input: I) -> PResult<Span<I>, I> {
    alt!(
        crlf,
        char_with_prop(GraphemeClusterBreak::Control).with_value(()),
        seq!(precore.many0(|_| ()), core, postcore.many0(|_| ())).with_value(()),
    )
    .recognize()
    .parse(input)
}
