use super::{ascii, AsciiChar, AsciiInput, AsciiStr, Error, PResult, Property};
use crate::{
    basic::{alt, eof},
    Error as PError, Failure, IntoInput, Parse, Span, Success,
};
use core::marker::PhantomData;

pub use pars_macros::regex_ascii_strict as regex;

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

pub fn line<I: AsciiInput>(input: I) -> PResult<Span<I>, I> {
    char.many_until(
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
