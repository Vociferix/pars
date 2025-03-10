//! Generic parser and combinator building blocks.
//!
//! This module provides the majority of the combinators that will be used to
//! implement most parsers. Everything implemented in this module supports any
//! combination of input and error types. When using `pars`, it is best to become
//! familiar with the contents of this module, as the majority of parsing problems
//! should have a solution implemented here.
//!
//! Most functions that take a parser as a parameter and produce a transformed parser
//! (A.K.A. combinators) are also available as methods on the [`Parse`] trait.

use crate::{
    Error, ErrorSeed, Failure, Input, IntoInput, PResult, PResultExt, Parse, Span, Success,
};
use core::iter::FromIterator;
use core::marker::PhantomData;

/// Creates a parser that will match exactly one of its arguments.
///
/// [`alt`] will accept any number of parsers as arguments. The returned parser will
/// attempt to parse with each argument, preferring the first argument, then second,
/// and so on. Each alternate parser must produce the same output for a given type of
/// input.
///
/// [`alt`] will attempt to parse each alternate completely before moving on to the
/// next alternate. Thus, [`alt`] introduces backtracking into the parser. Depending
/// on how each alternate parses, [`alt`] can become quite expensive, since each
/// alternate may parse all the way to the end of input before returning a parse
/// failure. That said, most use cases are not likely to have this worst case
/// performance.
///
/// When backtracking is unacceptable, [`flat_map`] or [`try_flat_map`] may be a
/// viable alternative. See the examples
/// [`msgpack.rs`](https://github.com/Vociferix/pars/blob/master/src/msgpack.rs) and
/// [`msgpack_alt.rs`](https://github.com/Vociferix/pars/blob/master/src/msgpack_alt.rs)
/// for a comparison of using [`alt`] versus [`try_flat_map`].
///
/// Also see [`either`], which [`alt`] is essentially a variadic version of, and in fact,
/// is implemented in terms of.
///
/// # Example
///
/// ```
/// use pars::{
///     basic::alt,
///     unicode::{UnicodeInput as UInput, PResult, strict::verbatim},
///     Parse, Success,
/// };
///
/// fn my_parser<I: UInput>(input: I) -> PResult<(), I> {
///     // match "a", "b", or "c"
///     alt!(
///         verbatim("a").with_value(()),
///         verbatim("b").with_value(()),
///         verbatim("c").with_value(()),
///     )
///     .parse(input)
/// }
///
/// assert!(my_parser.parse("be kind") == Ok(Success((), "e kind")));
/// ```
pub use pars_macros::alt;

pub use pars_macros::permutation;

/// Creates a parser that matches a sequence of parsers.
///
/// [`seq`] will accept any number of parsers as arguments. The returned parser will
/// apply each parser in order. If all these parsers succeed, their output is returned
/// in a tuple with the elements in the same order that their corresponding parsers
/// were provided to [`seq`]. If any one of the parsers fails, the whole [`seq`] parser
/// immediately fails.
///
/// Also see [`pair`], which [`seq`] is essentially a variadic version of, and in fact,
/// is implemented in terms of.
///
/// # Example
///
/// ```
/// use pars::{
///     basic::seq,
///     bytes::{ByteInput as BInput, PResult, self},
///     Parse, Success,
/// };
///
/// fn my_parser<I: BInput>(input: I) -> PResult<(u8, u16, u8), I> {
///     seq!(
///         bytes::u8,
///         bytes::be::u16,
///         bytes::u8,
///     )
///     .parse(input)
/// }
///
/// assert!(
///     my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success((0x01, 0x0203, 0x04), b""))
/// );
/// ```
pub use pars_macros::seq;

#[derive(Debug, Clone)]
struct ErrorParser<F, T, I, E>(F, PhantomData<fn() -> (T, I, E)>)
where
    F: Fn(I) -> E,
    I: Input,
    E: Error<I>;

impl<F, T, I, E> Parse<I> for ErrorParser<F, T, I, E>
where
    F: Fn(I) -> E,
    I: Input,
    E: Error<I>,
{
    type Parsed = T;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<T, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        Err(Failure((self.0)(input.clone()), input))
    }
}

/// Creates a parser that unconditionally produces an error.
///
/// The provided function, `error_fn`, is called to construct an error each
/// time the returned parser is invoked.
///
/// # Example
/// ```
/// # use pars::{
/// #     ascii::{
/// #         prop::{Alphabetic, Punctuation},
/// #         strict::char_with_prop, PResult, AsciiChar,
/// #         Error, ErrorKind,
/// #     },
/// #     basic::{alt, error},
/// #     Parse,
/// #     Success,
/// #     Error as ErrorTrait,
/// # };
/// #
/// fn my_parser(input: &str) -> PResult<AsciiChar, &str> {
///     alt!(
///         char_with_prop(Alphabetic),
///         char_with_prop(Punctuation),
///         error(Error::invalid_input),
///     )
///     .parse(input)
/// }
///
/// let err = my_parser.parse("123").unwrap_err().0;
/// assert_eq!(err.kind(), ErrorKind::InvalidInput);
/// assert_eq!(*err.position(), "123");
/// ```
#[inline]
pub const fn error<F, T, I, E>(error_fn: F) -> impl Parse<I, Parsed = T, Error = E>
where
    F: Fn(I) -> E,
    I: Input,
    E: Error<I>,
{
    ErrorParser(error_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct ConstantParser<F, T, I, E>(F, PhantomData<fn() -> (T, I, E)>)
where
    F: Fn() -> T,
    I: Input,
    E: Error<I>;

impl<F, T, I, E> Parse<I> for ConstantParser<F, T, I, E>
where
    F: Fn() -> T,
    I: Input,
    E: Error<I>,
{
    type Parsed = T;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<T, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        Ok(Success((self.0)(), input))
    }
}

/// Creates a parser that unconditionally produces a specific value.
///
/// The provided function, `const_fn`, is called to construct a value each
/// time the returned parser is invoked. The parser does not consume any
/// input.
///
/// # Example
/// ```
/// # use pars::{
/// #     ascii::{
/// #         prop::{Alphabetic, Punctuation},
/// #         strict::char_with_prop, PResult, AsciiChar,
/// #     },
/// #     basic::{alt, constant},
/// #     Parse,
/// #     Success,
/// # };
/// #
/// fn my_parser(input: &str) -> PResult<AsciiChar, &str> {
///     alt!(
///         char_with_prop(Alphabetic),
///         char_with_prop(Punctuation),
///         constant(|| AsciiChar::Question),
///     )
///     .parse(input)
/// }
///
/// let ret = my_parser.parse("123").unwrap();
/// assert_eq!(ret, Success(AsciiChar::Question, "123"));
/// ```
#[inline]
pub const fn constant<F, T, I, E>(const_fn: F) -> impl Parse<I, Parsed = T, Error = E>
where
    F: Fn() -> T,
    I: Input,
    E: Error<I>,
{
    ConstantParser(const_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct MapParser<P, F, R, I>(P, F, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    I: Input,
    F: Fn(P::Parsed) -> R;

impl<P, F, R, I> Parse<I> for MapParser<P, F, R, I>
where
    P: Parse<I>,
    I: Input,
    F: Fn(P::Parsed) -> R,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        self.0.parse(input).map_parsed(&self.1)
    }
}

/// Creates a parser whose parsed result is transformed.
///
/// The provided function, `map_fn`, is applied to the parsed result of
/// `parser` if it parses successfully. The value returned from `map_fn`
/// is the parsed result of the new parser.
///
/// If the the mapping operation could fail, use [`try_map`] instead.
///
/// See also [`Parse::map`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::map;
/// fn inv_byte(input: &[u8]) -> PResult<u8, &[u8]> {
///     map(bytes::u8, |byte| !byte).parse(input)
/// }
///
/// assert_eq!(inv_byte.parse(b"\x0f").unwrap().0, 0xf0);
/// ```
#[inline]
pub const fn map<P, F, R, I>(parser: P, map_fn: F) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: Fn(P::Parsed) -> R,
{
    MapParser(parser, map_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TryMapParser<P, F, R, S, I>(P, F, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: Fn(P::Parsed) -> Result<R, S>;

impl<P, F, R, S, I> Parse<I> for TryMapParser<P, F, R, S, I>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: Fn(P::Parsed) -> Result<R, S>,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()).map_parsed(&self.1) {
            Ok(Success(Ok(val), rem)) => Ok(Success(val, rem)),
            Ok(Success(Err(kind), _)) => Err(Failure(kind.into_error(input.clone()), input)),
            Err(Failure(err, _)) => Err(Failure(err, input)),
        }
    }
}

/// Creates a parser whose parsed result is fallibly transformed.
///
/// The provided function, `map_fn`, is applied to the parsed result of
/// `parser` if it parses successfully. `map_fn` is permitted to fail,
/// which is signaled with an [`Err`] return value. In thise case the
/// new parser fails, and the contained error is converted to an
/// [`Error`] via [`ErrorSeed`]. If an [`Ok`] value is returned, the
/// contained value becomes the parsed result of the new parser.
///
/// If the mapping function cannot fail, use [`map`] instead.
///
/// See also [`Parse::try_map`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::try_map;
/// # use pars::ErrorKind;
/// fn inv_byte(input: &[u8]) -> PResult<u8, &[u8]> {
///     try_map(bytes::u8, |byte| {
///         if byte < 0x80 {
///             Ok(!byte)
///         } else {
///             Err(ErrorKind::InvalidInput)
///         }
///     }).parse(input)
/// }
///
/// assert_eq!(inv_byte.parse(b"\x0f").unwrap().0, 0xf0);
/// assert!(inv_byte.parse(b"\xf0").is_err());
/// ```
#[inline]
pub const fn try_map<P, F, R, S, I>(
    parser: P,
    try_map_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: Fn(P::Parsed) -> Result<R, S>,
{
    TryMapParser(parser, try_map_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct MapErrParser<P, F, R, I>(P, F, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    I: Input,
    F: Fn(P::Error) -> R,
    R: Error<I>;

impl<P, F, R, I> Parse<I> for MapErrParser<P, F, R, I>
where
    P: Parse<I>,
    I: Input,
    F: Fn(P::Error) -> R,
    R: Error<I>,
{
    type Parsed = P::Parsed;
    type Error = R;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(succ) => Ok(succ),
            Err(Failure(err, rem)) => Err(Failure((self.1)(err), rem)),
        }
    }
}

/// Creates a parser that transforms a parsing error.
///
/// The provided function, `map_err_fn`, is applied the parsing error of
/// `parser` if its parsing fails. The value returned from `map_err_fn`
/// becomes the parsing error of the new parser. Otherwise, if `parser`
/// succeeds, its parsed result is the parsed result of the new parser.
///
/// This combinator is most useful for converting between error types.
///
/// See also [`Parse::map_err`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::{bytes, unicode, PResult};
/// # use pars::basic::map_err;
/// fn my_parser(input: &[u8]) -> PResult<u8, &[u8], unicode::Error<&[u8]>> {
///     map_err(bytes::u8, |err: bytes::Error<&[u8]>| {
///         match err.kind() {
///             bytes::ErrorKind::NeedMoreInput => unicode::ErrorKind::NeedMoreInput,
///             bytes::ErrorKind::ExpectedEof => unicode::ErrorKind::ExpectedEof,
///             _ => unicode::ErrorKind::InvalidInput,
///         }.into_error(*err.position())
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"hello") == Ok(Success(b'h', b"ello")));
/// assert!(my_parser.parse(b"") == Err(Failure(
///     unicode::ErrorKind::NeedMoreInput.into_error(b"".as_slice()), b"")));
/// ```
#[inline]
pub const fn map_err<P, F, R, I>(
    parser: P,
    map_err_fn: F,
) -> impl Parse<I, Parsed = P::Parsed, Error = R>
where
    P: Parse<I>,
    I: Input,
    F: Fn(P::Error) -> R,
    R: Error<I>,
{
    MapErrParser(parser, map_err_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct MapResParser<P, F, R, E, I>(P, F, PhantomData<fn() -> (R, E, I)>)
where
    P: Parse<I>,
    I: Input,
    F: Fn(Result<P::Parsed, P::Error>) -> Result<R, E>,
    E: Error<I>;

impl<P, F, R, E, I> Parse<I> for MapResParser<P, F, R, E, I>
where
    P: Parse<I>,
    I: Input,
    F: Fn(Result<P::Parsed, P::Error>) -> Result<R, E>,
    E: Error<I>,
{
    type Parsed = R;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<R, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(val, rem)) => match (self.1)(Ok(val)) {
                Ok(val) => Ok(Success(val, rem)),
                Err(err) => Err(Failure(err, input)),
            },
            Err(Failure(err, rem)) => match (self.1)(Err(err)) {
                Ok(val) => Ok(Success(val, rem)),
                Err(err) => Err(Failure(err, input)),
            },
        }
    }
}

/// Creates a parser whose result is transformed.
///
/// The provided function, `map_res_fn`, accepts a [`Result`] containing either the
/// successfully parsed value of `parser` or the parsing error returned by `parser`.
/// `map_res_fn` then returns a new [`Result`], which will contain either the new
/// successful parsed value or a new parsing error.
///
/// Unlike [`map`] or [`map_err`], the mapping function may choose to convert an
/// [`Ok`] into and [`Err`] or an [`Err`] into an [`Ok`].
///
/// See also [`Parse::map_res`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::map_res;
/// # use pars::bytes::{self, PResult, Error, ErrorKind};
/// fn my_parser(input: &[u8]) -> PResult<u8, &[u8]> {
///     map_res(bytes::u8, |res| match res {
///         Ok(byte) if byte >= 0x80 => {
///             Err(ErrorKind::InvalidInput.into_error(b"".as_slice()))
///         },
///         Ok(byte) => Ok(byte),
///         Err(err) if err.kind() == ErrorKind::NeedMoreInput => Ok(0),
///         Err(err) => Err(err),
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"hello") == Ok(Success(b'h', b"ello")));
/// assert_eq!(
///     my_parser.parse(b"\xffhello").unwrap_err().0.kind(),
///     ErrorKind::InvalidInput,
/// );
/// assert!(my_parser.parse(b"") == Ok(Success(b'\x00', b"")));
/// ```
#[inline]
pub const fn map_res<P, F, R, E, I>(
    parser: P,
    map_res_fn: F,
) -> impl Parse<I, Parsed = R, Error = E>
where
    P: Parse<I>,
    I: Input,
    F: Fn(Result<P::Parsed, P::Error>) -> Result<R, E>,
    E: Error<I>,
{
    MapResParser(parser, map_res_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TakeParser<I, E>(usize, PhantomData<fn() -> (I, E)>)
where
    I: Input,
    E: Error<I>;

impl<I: Input, E: Error<I>> Parse<I> for TakeParser<I, E> {
    type Parsed = Span<I>;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<Span<I>, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let begin = input.clone();
        if input.advance_by(self.0) != self.0 {
            Err(Failure(E::need_more_input(input), begin))
        } else {
            Ok(Success(Span::new(begin, input.clone()), input))
        }
    }
}

/// Creates a parser that takes a number of symbols from the input.
///
/// The returned parser will take `count` symbols from its input and
/// return them as a [`Span`]. If there are not at least `count`
/// symbols in the input, an error is returned, constructed from
/// [`Error::need_more_input`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{PResult};
/// fn my_parser(input: &str) -> PResult<&str, &str> {
///     take(5).ok_into().parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello"), Ok(Success("hello", "")));
/// assert_eq!(my_parser.parse("hello world"), Ok(Success("hello", " world")));
/// assert!(my_parser.parse("hi").is_err());
/// ```
#[inline]
pub const fn take<I, E>(count: usize) -> impl Parse<I, Parsed = Span<I>, Error = E>
where
    I: Input,
    E: Error<I>,
{
    TakeParser(count, PhantomData)
}

#[derive(Debug, Clone)]
struct WithParser<P, F, T, I>(P, F, PhantomData<fn() -> (T, I)>)
where
    P: Parse<I>,
    I: Input,
    F: Fn() -> T;

impl<P, F, T, I> Parse<I> for WithParser<P, F, T, I>
where
    P: Parse<I>,
    I: Input,
    F: Fn() -> T,
{
    type Parsed = T;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(_, rem)) => Ok(Success((self.1)(), rem)),
            Err(fail) => Err(fail),
        }
    }
}

/// Converts a parser to produce a different return value.
///
/// If `parser` parses successfully, its returned value is immediately dropped.
/// `with_fn` is then called to produce the new value. If `parser` fails,
/// `with_fn` is not called.
///
/// See also [`Parse::with`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::with;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// #[derive(Debug, PartialEq)]
/// enum Token {
///     Begin,
///     End,
/// }
///
/// fn begin(input: &str) -> PResult<Token, &str> {
///     with(verbatim("BEGIN"), || Token::Begin).parse(input)
/// }
///
/// fn end(input: &str) -> PResult<Token, &str> {
///     with(verbatim("END"), || Token::End).parse(input)
/// }
///
/// assert_eq!(begin.parse("BEGIN hello"), Ok(Success(Token::Begin, " hello")));
/// assert_eq!(end.parse("END world"), Ok(Success(Token::End, " world")));
/// ```
#[inline]
pub const fn with<P, F, T, I>(parser: P, with_fn: F) -> impl Parse<I, Parsed = T, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: Fn() -> T,
{
    WithParser(parser, with_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct WithDefaultParser<P, T, I>(P, PhantomData<fn() -> (T, I)>)
where
    P: Parse<I>,
    I: Input,
    T: Default;

impl<P, T, I> Parse<I> for WithDefaultParser<P, T, I>
where
    P: Parse<I>,
    I: Input,
    T: Default,
{
    type Parsed = T;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<T, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(_, rem)) => Ok(Success(T::default(), rem)),
            Err(fail) => Err(fail),
        }
    }
}

/// Converts a parser to produce a different return value, via [`Default`].
///
/// If `parser` parses successfully, its returned value is immediately dropped.
/// The old returned value is replaced with a value of type `T`, produced by
/// calling [`Default::default()`].
///
/// `with_default(parser)` is equivalent to `with(parser, Default::default)`
/// (see [`with`]).
///
/// See also [`Parse::with_default`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::with_default;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// #[derive(Debug, PartialEq, Default)]
/// struct Token;
///
/// fn token(input: &str) -> PResult<Token, &str> {
///     with_default(verbatim("TOKEN")).parse(input)
/// }
///
/// assert_eq!(token.parse("TOKEN"), Ok(Success(Token, "")));
/// ```
#[inline]
pub const fn with_default<P, T, I>(parser: P) -> impl Parse<I, Parsed = T, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    T: Default,
{
    WithDefaultParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct WithValueParser<P, T, I>(P, T, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input,
    T: Clone;

impl<P, T, I> Parse<I> for WithValueParser<P, T, I>
where
    P: Parse<I>,
    T: Clone,
    I: Input,
{
    type Parsed = T;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<T, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        self.0.parse(input).map_parsed(|_| self.1.clone())
    }
}

/// Converts a parser to produce a different return value, via [`Clone`].
///
/// If `parser` parses successfully, its returned value is immediately dropped.
/// `value` is is cloned to replace the returned value.
///
/// See also [`Parse::with_value`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::with_value;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// #[derive(Debug, PartialEq, Clone)]
/// struct Token;
///
/// fn token(input: &str) -> PResult<Token, &str> {
///     with_value(verbatim("TOKEN"), Token).parse(input)
/// }
///
/// assert_eq!(token.parse("TOKEN"), Ok(Success(Token, "")));
/// ```
#[inline]
pub const fn with_value<P, T, I>(parser: P, value: T) -> impl Parse<I, Parsed = T, Error = P::Error>
where
    P: Parse<I>,
    T: Clone,
    I: Input,
{
    WithValueParser(parser, value, PhantomData)
}

#[derive(Debug, Clone)]
struct FlatMapParser<P, C, R, I>(P, C, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    C: Fn(P::Parsed) -> R,
    R: Parse<I, Error = P::Error>,
    I: Input;

impl<P, C, R, I> Parse<I> for FlatMapParser<P, C, R, I>
where
    P: Parse<I>,
    C: Fn(P::Parsed) -> R,
    R: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = R::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(arg, rem)) => match ((self.1)(arg)).parse(rem) {
                Ok(Success(ret, rem)) => Ok(Success(ret, rem)),
                Err(Failure(err, _)) => Err(Failure(err, input)),
            },
            Err(Failure(err, _)) => Err(Failure(err, input)),
        }
    }
}

/// Maps the result of a parser onto a combinator to produce a new parser.
///
/// If `parser` parses successfully, the result value is passed into
/// `combinator`. The remaining input after `parser` succeeds is then
/// parsed by the parser returned by `combinator`.
///
/// Generally, this combinator is useful for building a parser that should
/// parse differently depending on information earlier in the input stream.
///
/// See also [`Parse::flat_map`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::flat_map;
/// # use pars::bytes::{self, PResult};
/// // First byte is the length of the string, then that many
/// // more bytes is the string data.
/// fn pascal_str(input: &[u8]) -> PResult<&[u8], &[u8]> {
///     flat_map(bytes::u8.ok_into(), take).ok_into().parse(input)
/// }
///
/// assert!(pascal_str.parse(b"\x05hello") == Ok(Success(b"hello", b"")));
/// assert!(pascal_str.parse(b"\x05hi").is_err());
/// ```
#[inline]
pub const fn flat_map<P, C, R, I>(
    parser: P,
    combinator: C,
) -> impl Parse<I, Parsed = R::Parsed, Error = P::Error>
where
    P: Parse<I>,
    C: Fn(P::Parsed) -> R,
    R: Parse<I, Error = P::Error>,
    I: Input,
{
    FlatMapParser(parser, combinator, PhantomData)
}

#[derive(Debug, Clone)]
struct TryFlatMapParser<P, C, R, S, I>(P, C, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    S: ErrorSeed<I, P::Error>,
    C: Fn(P::Parsed) -> Result<R, S>,
    R: Parse<I, Error = P::Error>,
    I: Input;

impl<P, C, R, S, I> Parse<I> for TryFlatMapParser<P, C, R, S, I>
where
    P: Parse<I>,
    S: ErrorSeed<I, P::Error>,
    C: Fn(P::Parsed) -> Result<R, S>,
    R: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = R::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(arg, rem)) => match (self.1)(arg) {
                Ok(p) => match p.parse(rem) {
                    Ok(Success(ret, rem)) => Ok(Success(ret, rem)),
                    Err(Failure(err, _)) => Err(Failure(err, input)),
                },
                Err(e) => Err(Failure(e.into_error(input.clone()), input)),
            },
            Err(Failure(err, _)) => Err(Failure(err, input)),
        }
    }
}

/// Maps the result of a parser onto a combinator to produce a new parser.
///
/// If `parser` parses successfully, the result value is passed into
/// `combinator`. `combinator` then returns a `Result` containing either a
/// new parser or an error implementing [`ErrorSeed`]. If a parser is
/// returned, the remaining input from `parser` is passed to the new
/// parser. Otherwise, the error is converted to a parsing error and
/// returned.
///
/// See also [`Parse::try_flat_map`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_flat_map;
/// # use pars::bytes::{self, PResult, ErrorKind};
/// fn my_parser(input: &[u8]) -> PResult<&[u8], &[u8]> {
///     try_flat_map(bytes::u8, |value| {
///         if value < 10 {
///             Ok(take(value.into()).ok_into())
///         } else {
///             Err(ErrorKind::InvalidInput)
///         }
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x05hello") == Ok(Success(b"hello", b"")));
/// assert!(my_parser.parse(b"\x0bhello world").is_err());
/// ```
#[inline]
pub const fn try_flat_map<P, C, R, S, I>(
    parser: P,
    combinator: C,
) -> impl Parse<I, Parsed = R::Parsed, Error = P::Error>
where
    P: Parse<I>,
    S: ErrorSeed<I, P::Error>,
    C: Fn(P::Parsed) -> Result<R, S>,
    R: Parse<I, Error = P::Error>,
    I: Input,
{
    TryFlatMapParser(parser, combinator, PhantomData)
}

#[derive(Debug, Clone)]
struct VerbatimParser<P, I, E>(P, PhantomData<fn() -> (I, E)>)
where
    P: Input,
    I: Input,
    I::Symbol: PartialEq<P::Symbol>,
    E: Error<I>;

impl<P, I, E> Parse<I> for VerbatimParser<P, I, E>
where
    P: Input,
    I: Input,
    I::Symbol: PartialEq<P::Symbol>,
    E: Error<I>,
{
    type Parsed = Span<I>;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<Span<I>, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut pattern = self.0.clone();
        let orig_input = input.clone();
        while let Some(expected) = pattern.next() {
            let tmp = input.clone();
            let Some(symb) = input.next() else {
                return Err(Failure(E::need_more_input(input), orig_input));
            };
            if !PartialEq::eq(&symb, &expected) {
                return Err(Failure(E::invalid_input(tmp), orig_input));
            }
        }
        Ok(Success(Span::new(orig_input, input.clone()), input))
    }
}

/// Creates a parser that attempts to match input verbatim.
///
/// `pattern` is a sequence of input symbols. The returned parser will succeed if
/// the input begins with `pattern` exactly.
///
/// See also:
/// * [`bytes::verbatim`](../bytes/fn.verbatim.html)
/// * [`ascii::strict::verbatim`](../ascii/strict/fn.verbatim.html)
/// * [`ascii::lossy::verbatim`](../ascii/lossy/fn.verbatim.html)
/// * [`unicode::strict::verbatim`](../unicode/strict/fn.verbatim.html)
/// * [`unicode::lossy::verbatim`](../unicode/lossy/fn.verbatim.html)
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::verbatim;
/// # use pars::unicode::PResult;
/// fn hello(input: &str) -> PResult<&str, &str> {
///     verbatim("hello").ok_into().parse(input)
/// }
///
/// assert_eq!(hello.parse("hello world"), Ok(Success("hello", " world")));
/// assert!(hello.parse("Hello World").is_err());
/// ```
#[inline]
pub const fn verbatim<P, I, E>(pattern: P) -> impl Parse<I, Parsed = Span<I>, Error = E>
where
    P: Input,
    I: Input,
    I::Symbol: PartialEq<P::Symbol>,
    E: Error<I>,
{
    VerbatimParser(pattern, PhantomData)
}

/// A parser that extracts one symbol from the input stream.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::PResult;
/// fn my_parser(input: &str) -> PResult<char, &str> {
///    pop.parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
/// assert!(my_parser.parse("").is_err());
/// ```
pub fn pop<I: Input, E: Error<I>>(mut input: I) -> PResult<I::Symbol, I, E> {
    if let Some(symb) = input.next() {
        Ok(Success(symb, input))
    } else {
        Err(Failure(E::need_more_input(input.clone()), input))
    }
}

#[derive(Debug, Clone)]
struct OrValueParser<P, I>(P, P::Parsed, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Clone;

impl<P, I> Parse<I> for OrValueParser<P, I>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Clone,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(ret, rem)) => Ok(Success(ret, rem)),
            Err(Failure(_, rem)) => Ok(Success(self.1.clone(), rem)),
        }
    }
}

/// Creates a parser that returns a fallback value instead of an error.
///
/// If `parser` fails to parse, `value` is cloned and returned as a success
/// value. The new parser will never return a parsing error.
///
/// See also [`Parse::or_value`]
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::or_value;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<char, &str> {
///     or_value(unicode::strict::char, '\0').parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
/// assert_eq!(my_parser.parse(""), Ok(Success('\0', "")));
/// ```
#[inline]
pub const fn or_value<P, I>(
    parser: P,
    value: P::Parsed,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Clone,
{
    OrValueParser(parser, value, PhantomData)
}

#[derive(Debug, Clone)]
struct OrDefaultParser<P, I>(P, PhantomData<fn() -> I>);

impl<P, I> Parse<I> for OrDefaultParser<P, I>
where
    P: Parse<I>,
    P::Parsed: Default,
    I: Input,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(ret, rem)) => Ok(Success(ret, rem)),
            Err(Failure(_, rem)) => Ok(Success(Default::default(), rem)),
        }
    }
}

/// Creates a parser that returns a fallback value instead of an error.
///
/// If `parser` fails to parse, a default value is returned by calling
/// [`Default::default`] instead of returning the error. The new parser
/// will never return a parsing error.
///
/// See also [`Parse::or_default`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::or_default;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<char, &str> {
///     or_default(unicode::strict::char).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
/// assert_eq!(my_parser.parse(""), Ok(Success('\0', "")));
/// ```
#[inline]
pub const fn or_default<P, I>(parser: P) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    P::Parsed: Default,
    I: Input,
{
    OrDefaultParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct OrElseParser<P, F, I>(P, F, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input,
    F: Fn() -> P::Parsed;

impl<P, F, I> Parse<I> for OrElseParser<P, F, I>
where
    P: Parse<I>,
    I: Input,
    F: Fn() -> P::Parsed,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(ret, rem)) => Ok(Success(ret, rem)),
            Err(Failure(_, rem)) => Ok(Success((self.1)(), rem)),
        }
    }
}

/// Creates a parser that returns a fallback value instead of an error.
///
/// If `parser` fails to parse, `or_else_fn` is called and its return value
/// is returned as a success value. The new parser will never return a
/// parsing error.
///
/// See also [`Parse::or_else`]
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::or_else;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<char, &str> {
///     or_else(unicode::strict::char, || '\0').parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
/// assert_eq!(my_parser.parse(""), Ok(Success('\0', "")));
/// ```
#[inline]
pub const fn or_else<P, F, I>(
    parser: P,
    or_else_fn: F,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: Fn() -> P::Parsed,
{
    OrElseParser(parser, or_else_fn, PhantomData)
}

/// An [`Iterator`] over repeated applications of a parser.
///
/// When using the combinators [`many0`], [`try_many0`], and [`collect_many0`],
/// this iterator type is used as the interface into the repeated applications
/// of the provided parser. The [`Iterator::Item`] is the [`Parse::Parsed`]
/// type of the provided parser. Iteration stops only when the parser returns a
/// parsing error.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`Many0Iter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed (such as parsing
/// whitespace in text). For example, `parser.many0(|_| ())`.
///
/// See [`many0`], [`try_many0`], and [`collect_many0`] for examples.
#[derive(Debug)]
pub struct Many0Iter<'a, P, I>(&'a P, &'a mut I)
where
    P: Parse<I>,
    I: Input;

impl<'a, P, I> Iterator for Many0Iter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.0.parse(self.1.clone());
        match res {
            Ok(Success(ret, rem)) => {
                *self.1 = rem;
                Some(ret)
            }
            Err(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
struct Many0Parser<P, F, R, I>(P, F, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(Many0Iter<'a, P, I>) -> R;

impl<P, F, R, I> Parse<I> for Many0Parser<P, F, R, I>
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(Many0Iter<'a, P, I>) -> R,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let ret = (self.1)(Many0Iter(&self.0, &mut input));
        let _ = Many0Iter(&self.0, &mut input).count();
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated as many times as possible.
///
/// [`many0`] produces a parser that will apply `parser` repeatedly until
/// it returns a parsing error. The parsed values are passed to `collect_fn`
/// in the form of an iterator, [`Many0Iter`]. Whatever `collect_fn`
/// returns is the parsed value of the new parser.
///
/// Because [`many0`] permits any number of successful repetitions,
/// including zero, the returned parser will never produce a parsing error.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::many0`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::many0;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// fn count_spaces(input: &str) -> PResult<usize, &str> {
///     many0(verbatim(" "), |iter| iter.count()).parse(input)
/// }
///
/// assert_eq!(count_spaces.parse("    hello"), Ok(Success(4, "hello")));
/// assert_eq!(count_spaces.parse("hello"), Ok(Success(0, "hello")));
/// ```
#[inline]
pub const fn many0<P, F, R, I>(
    parser: P,
    collect_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(Many0Iter<'a, P, I>) -> R,
{
    Many0Parser(parser, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TryMany0Parser<P, F, R, S, I>(P, F, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(Many0Iter<'a, P, I>) -> Result<R, S>;

impl<P, F, R, S, I> Parse<I> for TryMany0Parser<P, F, R, S, I>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(Many0Iter<'a, P, I>) -> Result<R, S>,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let orig_input = input.clone();
        match (self.1)(Many0Iter(&self.0, &mut input)) {
            Ok(ret) => {
                let _ = Many0Iter(&self.0, &mut input).count();
                Ok(Success(ret, input))
            }
            Err(err) => Err(Failure(err.into_error(orig_input.clone()), orig_input)),
        }
    }
}

/// Creates a parser that is repeated as many times as possible.
///
/// [`try_many0`] produces a parser that will apply `parser` repeatedly until
/// it returns a parsing error. The parsed values are passed to `collect_fn`
/// in the form of an iterator, [`Many0Iter`]. If `collect_fn` returns an
/// [`Ok`] value, that becomes the parsed result of the new parser. If
/// `collect_fn` returns an [`Err`], the new parser returns a parsing error
/// by converting the contained value via [`ErrorSeed`].
///
/// Because [`try_many0`] permits any number of successful repetitions,
/// including zero, the returned parser will only return a parsing error if
/// `collect_fn` returns an [`Err`].
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::try_many0`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_many0;
/// # use pars::ErrorKind;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// // only allows an even number of spaces
/// fn count_spaces(input: &str) -> PResult<usize, &str> {
///     try_many0(verbatim(" "), |iter| {
///         let count = iter.count();
///         if count % 2 == 0 {
///             Ok(count)
///         } else {
///             Err(ErrorKind::InvalidInput)
///         }
///     }).parse(input)
/// }
///
/// assert_eq!(count_spaces.parse("    hello"), Ok(Success(4, "hello")));
/// assert_eq!(count_spaces.parse("hello"), Ok(Success(0, "hello")));
/// assert!(count_spaces.parse(" hello").is_err());
/// ```
#[inline]
pub const fn try_many0<P, F, R, S, I>(
    parser: P,
    collect_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(Many0Iter<'a, P, I>) -> Result<R, S>,
{
    TryMany0Parser(parser, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct CollectMany0Parser<P, C, I>(P, PhantomData<fn() -> (C, I)>)
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>;

impl<P, C, I> Parse<I> for CollectMany0Parser<P, C, I>
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    type Parsed = C;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<C, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let ret = C::from_iter(Many0Iter(&self.0, &mut input));
        let _ = Many0Iter(&self.0, &mut input).count();
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated as many times as possible.
///
/// [`collect_many0`] produces a parser that will apply `parser` repeatedly
/// until it returns a parsing error. The parsed values are collected via
/// the [`FromIterator`] trait implementation on the parsed type of the new
/// parser, which is generally deduced.
///
/// Because [`collect_many0`] permits any number of successful repetitions,
/// including zero, the returned parser will never produce a parsing error.
///
/// Note that the returned new parser does not allocate unless the
/// [`FromIterator`] implementation allocates.
///
/// See also [`Parse::collect_many0`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_many0;
/// # use pars::unicode::PResult;
/// use pars::unicode::{prop::Alphabetic, strict::char_with_prop};
///
/// fn word(input: &str) -> PResult<String, &str> {
///     collect_many0(char_with_prop(Alphabetic)).parse(input)
/// }
///
/// assert_eq!(word.parse("hello world"), Ok(Success(String::from("hello"), " world")));
/// assert_eq!(word.parse(""), Ok(Success(String::new(), "")));
/// assert_eq!(word.parse(" "), Ok(Success(String::new(), " ")));
/// ```
#[inline]
pub const fn collect_many0<P, C, I>(parser: P) -> impl Parse<I, Parsed = C, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    CollectMany0Parser(parser, PhantomData)
}

/// An [`Iterator`] over repeated applications of a parser.
///
/// When using the combinators [`many1`], [`try_many1`], and [`collect_many1`],
/// this iterator type is used as the interface into the repeated applications
/// of the provided parser. The [`Iterator::Item`] is the [`Parse::Parsed`]
/// type of the provided parser. Iteration stops only when the parser returns a
/// parsing error.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`Many1Iter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed (such as parsing
/// whitespace in text). For example, `parser.many1(|_| ())`.
///
/// See [`many1`], [`try_many1`], and [`collect_many1`] for examples.
#[derive(Debug)]
pub struct Many1Iter<'a, P, I>(&'a P, &'a mut I, &'a mut bool, &'a mut Option<P::Error>)
where
    P: Parse<I>,
    I: Input;

impl<'a, P, I> Iterator for Many1Iter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.0.parse(self.1.clone());
        match res {
            Ok(Success(ret, rem)) => {
                *self.2 = true;
                *self.1 = rem;
                Some(ret)
            }
            Err(Failure(e, _)) if !*self.2 => {
                *self.3 = Some(e);
                None
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
struct Many1Parser<P, F, R, I>(P, F, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(Many1Iter<'a, P, I>) -> R;

impl<P, F, R, I> Parse<I> for Many1Parser<P, F, R, I>
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(Many1Iter<'a, P, I>) -> R,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut parsed = false;
        let mut err = None;
        let orig_input = input.clone();
        let ret = (self.1)(Many1Iter(&self.0, &mut input, &mut parsed, &mut err));
        let _ = Many1Iter(&self.0, &mut input, &mut parsed, &mut err).count();
        if let Some(err) = err {
            return Err(Failure(err, orig_input));
        }
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated at least once.
///
/// [`many1`] produces a parser that will apply `parser` repeatedly until
/// it returns a parsing error. The parsed values are passed to `collect_fn`
/// in the form of an iterator, [`Many1Iter`]. Whatever `collect_fn`
/// returns is the parsed value of the new parser. If `parser` does not
/// successfully parse at least once, a parsing error is returned.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::many1`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::many1;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// fn count_spaces(input: &str) -> PResult<usize, &str> {
///     many1(verbatim(" "), |iter| iter.count()).parse(input)
/// }
///
/// assert_eq!(count_spaces.parse("    hello"), Ok(Success(4, "hello")));
/// assert!(count_spaces.parse("hello").is_err());
/// ```
#[inline]
pub const fn many1<P, F, R, I>(
    parser: P,
    collect_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(Many1Iter<'a, P, I>) -> R,
{
    Many1Parser(parser, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TryMany1Parser<P, F, R, S, I>(P, F, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(Many1Iter<'a, P, I>) -> Result<R, S>;

impl<P, F, R, S, I> Parse<I> for TryMany1Parser<P, F, R, S, I>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(Many1Iter<'a, P, I>) -> Result<R, S>,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut parsed = false;
        let mut err = None;
        let orig_input = input.clone();
        let ret = match (self.1)(Many1Iter(&self.0, &mut input, &mut parsed, &mut err)) {
            Ok(ret) => ret,
            Err(e) => {
                return Err(Failure(e.into_error(orig_input.clone()), orig_input));
            }
        };
        let _ = Many1Iter(&self.0, &mut input, &mut parsed, &mut err).count();
        if let Some(err) = err {
            return Err(Failure(err, orig_input));
        }
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated at least once.
///
/// [`try_many1`] produces a parser that will apply `parser` repeatedly until
/// it returns a parsing error. The parsed values are passed to `collect_fn`
/// in the form of an iterator, [`Many1Iter`]. If `collect_fn` returns an
/// [`Ok`] value, that becomes the parsed result of the new parser. If
/// `collect_fn` returns an [`Err`], the new parser returns a parsing error
/// by converting the contained value via [`ErrorSeed`]. If `parser` does not
/// successfully parse at least once, a parsing error is returned.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::try_many1`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_many1;
/// # use pars::ErrorKind;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// // only allows an odd number of spaces
/// fn count_spaces(input: &str) -> PResult<usize, &str> {
///     try_many1(verbatim(" "), |iter| {
///         let count = iter.count();
///         if count % 2 == 0 {
///             Err(ErrorKind::InvalidInput)
///         } else {
///             Ok(count)
///         }
///     }).parse(input)
/// }
///
/// assert_eq!(count_spaces.parse("   hello"), Ok(Success(3, "hello")));
/// assert!(count_spaces.parse("hello").is_err());
/// assert!(count_spaces.parse("  hello").is_err());
/// ```
#[inline]
pub const fn try_many1<P, F, R, S, I>(
    parser: P,
    collect_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(Many1Iter<'a, P, I>) -> Result<R, S>,
{
    TryMany1Parser(parser, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct CollectMany1Parser<P, C, I>(P, PhantomData<fn() -> (C, I)>)
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>;

impl<P, C, I> Parse<I> for CollectMany1Parser<P, C, I>
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    type Parsed = C;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<C, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut parsed = false;
        let mut err = None;
        let orig_input = input.clone();
        let ret = C::from_iter(Many1Iter(&self.0, &mut input, &mut parsed, &mut err));
        let _ = Many1Iter(&self.0, &mut input, &mut parsed, &mut err).count();
        if let Some(err) = err {
            return Err(Failure(err, orig_input));
        }
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated at east once.
///
/// [`collect_many1`] produces a parser that will apply `parser` repeatedly
/// until it returns a parsing error. The parsed values are collected via
/// the [`FromIterator`] trait implementation on the parsed type of the new
/// parser, which is generally deduced. If `parser` does not successfully
/// parse at least once, a parsing error is returned.
///
/// Note that the returned new parser does not allocate unless the
/// [`FromIterator`] implementation allocates.
///
/// See also [`Parse::collect_many1`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_many1;
/// # use pars::unicode::PResult;
/// use pars::unicode::{prop::Alphabetic, strict::char_with_prop};
///
/// fn word(input: &str) -> PResult<String, &str> {
///     collect_many1(char_with_prop(Alphabetic)).parse(input)
/// }
///
/// assert_eq!(word.parse("hello world"), Ok(Success(String::from("hello"), " world")));
/// assert!(word.parse("").is_err());
/// assert!(word.parse(" ").is_err());
/// ```
#[inline]
pub const fn collect_many1<P, C, I>(parser: P) -> impl Parse<I, Parsed = C, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    CollectMany1Parser(parser, PhantomData)
}

/// An [`Iterator`] over repeated applications of a parser.
///
/// When using the combinators [`repeated`], [`try_repeated`], and
/// [`collect_repeated`], this iterator type is used as the interface into the
/// repeated applications of the provided parser. The [`Iterator::Item`] is the
/// [`Parse::Parsed`] type of the provided parser. Iteration stops only when the
/// parser returns a parsing error.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`RepeatedIter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed. For example,
/// `parser.repeated(10, |_| ())`.
///
/// See [`repeated`], [`try_repeated`], and [`collect_repeated`] for examples.
#[derive(Debug)]
pub struct RepeatedIter<'a, P, I>(&'a P, &'a mut I, &'a mut usize, &'a mut Option<P::Error>)
where
    P: Parse<I>,
    I: Input;

impl<'a, P, I> Iterator for RepeatedIter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        if *self.2 == 0 {
            return None;
        }

        let res = self.0.parse(self.1.clone());
        match res {
            Ok(Success(ret, rem)) => {
                *self.2 -= 1;
                *self.1 = rem;
                Some(ret)
            }
            Err(Failure(e, _)) => {
                *self.3 = Some(e);
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(*self.2))
    }
}

#[derive(Debug, Clone)]
struct RepeatedParser<P, F, R, I>(P, usize, F, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> R;

impl<P, F, R, I> Parse<I> for RepeatedParser<P, F, R, I>
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> R,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut rem = self.1;
        let mut err = None;
        let orig_input = input.clone();
        let ret = (self.2)(RepeatedIter(&self.0, &mut input, &mut rem, &mut err));
        let _ = RepeatedIter(&self.0, &mut input, &mut rem, &mut err).count();
        if let Some(err) = err {
            return Err(Failure(err, orig_input));
        }
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated a set number of times.
///
/// [`repeated`] produces a parser that will apply `parser` `count` times.
/// The parsed values are passed to `collect_fn` in the form of an iterator,
/// [`RepeatedIter`]. Whatever `collect_fn` returns is the parsed value of
/// the new parser. If `parser` fails to parse before parsing `count` times,
/// a parsing error is returned.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::repeated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::repeated;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     repeated(bytes::u8, 4, |iter| {
///         iter.map(|byte| byte as u32).sum()
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") == Ok(Success(10, b"\x05")));
/// assert!(my_parser.parse(b"\x01\x02\x03").is_err());
/// ```
#[inline]
pub const fn repeated<P, F, R, I>(
    parser: P,
    count: usize,
    collect_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> R,
{
    RepeatedParser(parser, count, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TryRepeatedParser<P, F, R, S, I>(P, usize, F, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> Result<R, S>;

impl<P, F, R, S, I> Parse<I> for TryRepeatedParser<P, F, R, S, I>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> Result<R, S>,
{
    type Parsed = R;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<R, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut rem = self.1;
        let mut err = None;
        let orig_input = input.clone();
        let ret = match (self.2)(RepeatedIter(&self.0, &mut input, &mut rem, &mut err)) {
            Ok(ret) => ret,
            Err(e) => {
                return Err(Failure(e.into_error(orig_input.clone()), orig_input));
            }
        };
        let _ = RepeatedIter(&self.0, &mut input, &mut rem, &mut err).count();
        if let Some(err) = err {
            return Err(Failure(err, orig_input));
        }
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated a set number of times.
///
/// [`repeated`] produces a parser that will apply `parser` `count` times.
/// The parsed values are passed to `collect_fn` in the form of an iterator,
/// [`RepeatedIter`]. If `collect_fn` returns an [`Ok`] value, that value
/// becomes the parsed result of the new parser. If `collect_fn` returns an
/// [`Err`], the contained value becomes a parsing error via [`ErrorSeed`].
/// If `parser` fails to parse before parsing `count` times, a parsing error
/// is returned.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::try_repeated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_repeated;
/// # use pars::ErrorKind;
/// # use pars::bytes::{self, PResult};
/// // requires the resulting sum be even
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     try_repeated(bytes::u8, 4, |iter| {
///         let sum = iter.map(|byte| byte as u32).sum();
///         if sum % 2 == 0 {
///             Ok(sum)
///         } else {
///             Err(ErrorKind::InvalidInput)
///         }
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") == Ok(Success(10, b"\x05")));
/// assert!(my_parser.parse(b"\x00\x02\x03\x04").is_err());
/// assert!(my_parser.parse(b"\x01\x02\x03").is_err());
/// ```
#[inline]
pub const fn try_repeated<P, F, R, S, I>(
    parser: P,
    count: usize,
    collect_fn: F,
) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> Result<R, S>,
{
    TryRepeatedParser(parser, count, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct CollectRepeatedParser<P, C, I>(P, usize, PhantomData<fn() -> (C, I)>)
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>;

impl<P, C, I> Parse<I> for CollectRepeatedParser<P, C, I>
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    type Parsed = C;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<C, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut rem = self.1;
        let mut err = None;
        let orig_input = input.clone();
        let ret = C::from_iter(RepeatedIter(&self.0, &mut input, &mut rem, &mut err));
        let _ = RepeatedIter(&self.0, &mut input, &mut rem, &mut err).count();
        if let Some(err) = err {
            return Err(Failure(err, orig_input));
        }
        Ok(Success(ret, input))
    }
}

/// Creates a parser that is repeated a set number of times.
///
/// [`repeated`] produces a parser that will apply `parser` `count` times.
/// The parsed values are collected using the [`FromIterator`] trait
/// implementation on the parsed result type, which is usually deduced.
/// If `parser` fails to parse `count` times, a parsing error is returned.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// Note that the returned new parser does not allocate unless the
/// [`FromIterator`] implementation allocates.
///
/// See also [`Parse::repeated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_repeated;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<String, &str> {
///     collect_repeated(unicode::strict::char, 5).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello world"), Ok(Success(String::from("hello"), " world")));
/// assert!(my_parser.parse("hi").is_err());
/// ```
#[inline]
pub const fn collect_repeated<P, C, I>(
    parser: P,
    count: usize,
) -> impl Parse<I, Parsed = C, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    CollectRepeatedParser(parser, count, PhantomData)
}

/// An [`Iterator`] over repeated applications of a parser.
///
/// When using the combinators [`many_until`], [`try_many_until`], and
/// [`collect_many_until`], this iterator type is used as the interface into the
/// repeated applications of the provided parser. The [`Iterator::Item`] is the
/// [`Parse::Parsed`] type of the provided parser.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`ManyUntilIter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed. For example,
/// `parser.many_until(sentinel, |_| ())`.
///
/// See [`many_until`], [`try_many_until`], and [`collect_many_until`] for
/// examples.
#[derive(Debug)]
pub struct ManyUntilIter<'a, P, Q, I>(
    &'a P,
    &'a Q,
    &'a mut I,
    &'a mut Option<Result<Q::Parsed, P::Error>>,
)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input;

impl<'a, P, Q, I> Iterator for ManyUntilIter<'a, P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        if self.3.is_some() {
            return None;
        }

        match self.1.parse(self.2.clone()) {
            Ok(Success(sent, rem)) => {
                *self.3 = Some(Ok(sent));
                *self.2 = rem;
                None
            }
            Err(Failure(err, rem)) => match self.0.parse(rem) {
                Ok(Success(ret, rem)) => {
                    *self.2 = rem;
                    Some(ret)
                }
                Err(_) => {
                    *self.3 = Some(Err(err));
                    None
                }
            },
        }
    }
}

#[derive(Debug, Clone)]
struct ManyUntilParser<P, Q, F, R, I>(P, Q, F, PhantomData<fn() -> (R, I)>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    F: for<'a> Fn(ManyUntilIter<'a, P, Q, I>) -> R,
    I: Input;

impl<P, Q, F, R, I> Parse<I> for ManyUntilParser<P, Q, F, R, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    F: for<'a> Fn(ManyUntilIter<'a, P, Q, I>) -> R,
    I: Input,
{
    type Parsed = (R, Q::Parsed);
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut sentinel = None;
        let orig_input = input.clone();
        let ret = (self.2)(ManyUntilIter(&self.0, &self.1, &mut input, &mut sentinel));
        let _ = ManyUntilIter(&self.0, &self.1, &mut input, &mut sentinel).count();
        match sentinel {
            Some(Ok(sentinel)) => Ok(Success((ret, sentinel), input)),
            Some(Err(err)) => Err(Failure(err, orig_input)),
            None => unreachable!(),
        }
    }
}

/// Creates a parser that is repeated until a sentinel is parsed.
///
/// [`many_until`] produces a parser that will apply `parser` repeatedly until
/// `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it fails,
/// `parser` is applied before trying `sentinel_parser` again. If `sentinel_parser`
/// succeeds, parsing is complete.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of an
/// iterator, [`ManyUntilIter`]. The value returned by `collect_fn` and the parsed
/// value from `sentinel_parser` together as a 2-tuple become the parsed result of
/// the overall new parser. If `parser` returns a parsing error at any point, a
/// parsing error is returned from the overall new parser.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::many_until`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::many_until;
/// # use pars::bytes::{self, PResult};
/// fn c_str_len(input: &[u8]) -> PResult<usize, &[u8]> {
///     many_until(bytes::u8, bytes::verbatim(b"\x00"), |iter| iter.count())
///         .map(|(len, _)| len) // we only want the length
///         .parse(input)
/// }
///
/// assert!(c_str_len.parse(b"hello\x00world") == Ok(Success(5, b"world")));
/// assert!(c_str_len.parse(b"\x00") == Ok(Success(0, b"")));
/// assert!(c_str_len.parse(b"hello").is_err());
/// ```
#[inline]
pub const fn many_until<P, Q, F, R, I>(
    parser: P,
    sentinel_parser: Q,
    collect_fn: F,
) -> impl Parse<I, Parsed = (R, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    F: for<'a> Fn(ManyUntilIter<'a, P, Q, I>) -> R,
    I: Input,
{
    ManyUntilParser(parser, sentinel_parser, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TryManyUntilParser<P, Q, F, R, S, I>(P, Q, F, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(ManyUntilIter<'a, P, Q, I>) -> Result<R, S>,
    I: Input;

impl<P, Q, F, R, S, I> Parse<I> for TryManyUntilParser<P, Q, F, R, S, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(ManyUntilIter<'a, P, Q, I>) -> Result<R, S>,
    I: Input,
{
    type Parsed = (R, Q::Parsed);
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut sentinel = None;
        let orig_input = input.clone();
        let ret = match (self.2)(ManyUntilIter(&self.0, &self.1, &mut input, &mut sentinel)) {
            Ok(ret) => ret,
            Err(e) => {
                return Err(Failure(e.into_error(orig_input.clone()), orig_input));
            }
        };
        let _ = ManyUntilIter(&self.0, &self.1, &mut input, &mut sentinel).count();
        match sentinel {
            Some(Ok(sentinel)) => Ok(Success((ret, sentinel), input)),
            Some(Err(err)) => Err(Failure(err, orig_input)),
            None => unreachable!(),
        }
    }
}

/// Creates a parser that is repeated until a sentinel is parsed.
///
/// [`try_many_until`] produces a parser that will apply `parser` repeatedly until
/// `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it fails,
/// `parser` is applied before trying `sentinel_parser` again. If `sentinel_parser`
/// succeeds, parsing is complete.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of an
/// iterator, [`ManyUntilIter`]. If `collect_fn` returns an [`Ok`] value, that and
/// the value from `sentinel_parser` together as a 2-tuple become the parsed result
/// of the overall new parser. If `collect_fn` returns an [`Err`], a parsing error
/// is returned. If `parser` returns a parsing error at any point, a parsing error
/// is returned form the overall new parser.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::try_many_until`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_many_until;
/// # use pars::ErrorKind;
/// # use pars::bytes::{self, PResult};
/// fn c_str_len(input: &[u8]) -> PResult<usize, &[u8]> {
///     try_many_until(bytes::u8, bytes::verbatim(b"\x00"), |iter| {
///         let count = iter.count();
///         // disallow empty strings
///         if count == 0 {
///             Err(ErrorKind::InvalidInput)
///         } else {
///             Ok(count)
///         }
///     }).map(|(len, _)| len) // we only want the length
///         .parse(input)
/// }
///
/// assert!(c_str_len.parse(b"hello\x00world") == Ok(Success(5, b"world")));
/// assert!(c_str_len.parse(b"\x00").is_err());
/// assert!(c_str_len.parse(b"hello").is_err());
/// ```
#[inline]
pub const fn try_many_until<P, Q, F, R, S, I>(
    parser: P,
    sentinel_parser: Q,
    collect_fn: F,
) -> impl Parse<I, Parsed = (R, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(ManyUntilIter<'a, P, Q, I>) -> Result<R, S>,
    I: Input,
{
    TryManyUntilParser(parser, sentinel_parser, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct CollectManyUntilParser<P, Q, C, I>(P, Q, PhantomData<fn() -> (C, I)>)
where
    P: Parse<I>,
    Q: Parse<I>,
    I: Input,
    C: FromIterator<P::Parsed>;

impl<P, Q, C, I> Parse<I> for CollectManyUntilParser<P, Q, C, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    type Parsed = (C, Q::Parsed);
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let mut sentinel = None;
        let orig_input = input.clone();
        let ret = C::from_iter(ManyUntilIter(&self.0, &self.1, &mut input, &mut sentinel));
        let _ = ManyUntilIter(&self.0, &self.1, &mut input, &mut sentinel).count();
        match sentinel {
            Some(Ok(sentinel)) => Ok(Success((ret, sentinel), input)),
            Some(Err(err)) => Err(Failure(err, orig_input)),
            None => unreachable!(),
        }
    }
}

/// Creates a parser that is repeated until a sentinel is parsed.
///
/// [`collect_many_until`] produces a parser that will apply `parser` repeatedly
/// until `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it
/// fails, `parser` is applied before trying `sentinel_parser` again. If
/// `sentinel_parser` succeeds, parsing is complete.
///
/// The values produced by `parser` are collected using the [`FromIterator`] trait
/// implementation for the new parser's parsed result type, which is usually
/// deduced. This value together with the parsed value from `sentinel_parser` as a
/// 2-tuple become the parsed value for the overall new parser. If `parser` returns
/// a parsing error at any point, a parsing error is returned from the overall new
/// parser.
///
/// Note that the returned new parser does not allocate unless the
/// [`FromIterator`] implementation allocates.
///
/// See also [`Parse::collect_many_until`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_many_until;
/// # use pars::bytes::{self, PResult};
/// fn c_str(input: &[u8]) -> PResult<Vec<u8>, &[u8]> {
///     collect_many_until(bytes::u8, bytes::verbatim(b"\x00"))
///         .map(|(s, _)| s)
///         .parse(input)
/// }
///
/// assert!(c_str.parse(b"hello\x00world") == Ok(Success(Vec::from(b"hello"), b"world")));
/// assert!(c_str.parse(b"\x00") == Ok(Success(Vec::new(), b"")));
/// assert!(c_str.parse(b"hello").is_err());
/// ```
#[inline]
pub const fn collect_many_until<P, Q, C, I>(
    parser: P,
    sentinel: Q,
) -> impl Parse<I, Parsed = (C, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    CollectManyUntilParser(parser, sentinel, PhantomData)
}

/// An [`Iterator`] over repeated applications of a parser.
///
/// When using the combinators [`many`], [`try_many`], and [`collect_many`],
/// this iterator type is used as the interface into the repeated applications
/// of the provided parser. The [`Iterator::Item`] is the [`Parse::Parsed`]
/// type of the provided parser.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`ManyIter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed. For example,
/// `parser.many(3.., |_| ())`.
///
/// See [`many`], [`try_many`], and [`collect_many`] for examples.
#[derive(Debug)]
pub struct ManyIter<'a, P, I>(
    &'a P,
    Option<usize>,
    &'a mut I,
    &'a mut usize,
    &'a mut Option<P::Error>,
)
where
    P: Parse<I>,
    I: Input;

impl<'a, P, I> Iterator for ManyIter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(max_count) = self.1 {
            if *self.3 >= max_count {
                return None;
            }
        }

        match self.0.parse(self.2.clone()) {
            Ok(Success(ret, rem)) => {
                *self.3 += 1;
                *self.2 = rem;
                Some(ret)
            }
            Err(Failure(e, _)) => {
                *self.4 = Some(e);
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            0,
            if let Some(max_count) = self.1 {
                Some(max_count - *self.3)
            } else {
                None
            },
        )
    }
}

#[derive(Debug, Clone)]
struct ManyParser<P, R, F, O, I>(P, R, F, PhantomData<fn() -> (O, I)>)
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    F: for<'a> Fn(ManyIter<'a, P, I>) -> O,
    I: Input;

impl<P, R, F, O, I> Parse<I> for ManyParser<P, R, F, O, I>
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    F: for<'a> Fn(ManyIter<'a, P, I>) -> O,
    I: Input,
{
    type Parsed = O;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<O, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let max_count = match self.1.end_bound() {
            core::ops::Bound::Included(max_count) => Some(*max_count),
            core::ops::Bound::Excluded(&0) => Some(0),
            core::ops::Bound::Excluded(max_count) => Some(*max_count - 1),
            _ => None,
        };

        let mut count = 0usize;
        let mut err = None;
        let orig_input = input.clone();
        let ret = (self.2)(ManyIter(
            &self.0, max_count, &mut input, &mut count, &mut err,
        ));
        let _ = ManyIter(&self.0, max_count, &mut input, &mut count, &mut err).count();

        match self.1.start_bound() {
            core::ops::Bound::Included(min_count) if count < *min_count => {
                if let Some(err) = err {
                    Err(Failure(err, orig_input))
                } else {
                    unreachable!()
                }
            }
            core::ops::Bound::Excluded(min_count) if count <= *min_count => {
                if let Some(err) = err {
                    Err(Failure(err, orig_input))
                } else {
                    unreachable!()
                }
            }
            _ => Ok(Success(ret, input)),
        }
    }
}

/// Creates a parser that is repeated a number of times within a range.
///
/// [`many`] produces a parser that will apply `parser` repeatedly. The number
/// of times `parser` will be applied is defined by `range`. For example, if
/// `range` is `3..=5`, `parser` will be applied at least 3 times, and will be
/// applied up to 5 times if possible. If `parser` fails before parsing 3 times
/// (or whatever lower bound applies to `range`, if any), a parsing error is
/// returned from the new parser. Once the upper bound is met (again, if any)
/// parsing automatically ends successfully. `parser` returning a parsing error
/// after meeting the lower bound also ends parsing for the new parser.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of
/// an iterator, [`ManyIter`]. Whever `collect_fn` returns is the parsed value
/// of the new parser.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// Also note that [`many`] is a more generalized version of [`many0`],
/// [`many1`] and [`repeated`]. If `range` is `..`, the returned parser is
/// equivalent to a [`many0`] parser. If `range` is `1..`, the returned parser
/// is equivalent to a [`many1`] parser. If `range` is `count..=count`, the
/// returned parser is equivalent to a [`repeated`] parser with a size of
/// `count`.
///
/// See also [`Parse::many`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::many;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     many(bytes::u8, 2..=4, |iter| {
///         iter.map(|byte| byte as u32).sum()
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") == Ok(Success(10, b"\x05")));
/// assert!(my_parser.parse(b"\x01\x02\x03") == Ok(Success(6, b"")));
/// assert!(my_parser.parse(b"\x01\x02") == Ok(Success(3, b"")));
/// assert!(my_parser.parse(b"\x01").is_err());
/// assert!(my_parser.parse(b"").is_err());
/// ```
#[inline]
pub const fn many<P, R, F, O, I>(
    parser: P,
    range: R,
    collect_fn: F,
) -> impl Parse<I, Parsed = O, Error = P::Error>
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    F: for<'a> Fn(ManyIter<'a, P, I>) -> O,
    I: Input,
{
    ManyParser(parser, range, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct TryManyParser<P, R, F, O, S, I>(P, R, F, PhantomData<fn() -> (O, S, I)>)
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(ManyIter<'a, P, I>) -> Result<O, S>,
    I: Input;

impl<P, R, F, O, S, I> Parse<I> for TryManyParser<P, R, F, O, S, I>
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(ManyIter<'a, P, I>) -> Result<O, S>,
    I: Input,
{
    type Parsed = O;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<O, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let max_count = match self.1.end_bound() {
            core::ops::Bound::Included(max_count) => Some(*max_count),
            core::ops::Bound::Excluded(&0) => Some(0),
            core::ops::Bound::Excluded(max_count) => Some(*max_count - 1),
            _ => None,
        };

        let mut count = 0usize;
        let mut err = None;
        let orig_input = input.clone();
        let ret = match (self.2)(ManyIter(
            &self.0, max_count, &mut input, &mut count, &mut err,
        )) {
            Ok(ret) => ret,
            Err(e) => {
                return Err(Failure(e.into_error(orig_input.clone()), orig_input));
            }
        };
        let _ = ManyIter(&self.0, max_count, &mut input, &mut count, &mut err).count();

        match self.1.start_bound() {
            core::ops::Bound::Included(min_count) if count < *min_count => {
                if let Some(err) = err {
                    Err(Failure(err, orig_input))
                } else {
                    unreachable!()
                }
            }
            core::ops::Bound::Excluded(min_count) if count <= *min_count => {
                if let Some(err) = err {
                    Err(Failure(err, orig_input))
                } else {
                    unreachable!()
                }
            }
            _ => Ok(Success(ret, input)),
        }
    }
}

/// Creates a parser that is repeated a number of times within a range.
///
/// [`try_many`] produces a parser that will apply `parser` repeatedly. The
/// number of times `parser` will be applied is defined by `range`. For example,
/// if `range` is `3..=5`, `parser` will be applied at least 3 times, and will
/// be applied up to 5 times if possible. If `parser` fails before parsing 3
/// times (or whatever lower bound applies to `range`, if any), a parsing error
/// is returned from the new parser. Once the upper bound is met (again, if any)
/// parsing automatically ends successfully. `parser` returning a parsing error
/// after meeting the lower bound also ends parsing for the new parser.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of
/// an iterator, [`ManyIter`]. If `collect_fn` returns an [`Ok`] value, the
/// contained value becomes the parsed value of the new parser. If `collect_fn`
/// returns an [`Err`], that gets returned as a parsing error via [`ErrorSeed`].
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// Also note that [`try_many`] is a more generalized version of [`try_many0`],
/// [`try_many1`] and [`try_repeated`]. If `range` is `..`, the returned parser
/// is equivalent to a [`try_many0`] parser. If `range` is `1..`, the returned
/// parser is equivalent to a [`try_many1`] parser. If `range` is `count..=count`,
/// the returned parser is equivalent to a [`try_ repeated`] parser with a size of
/// `count`.
///
/// See also [`Parse::try_many`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_many;
/// # use pars::bytes::{self, PResult};
/// # use pars::ErrorKind;
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     try_many(bytes::u8, 2..=4, |iter| {
///         let sum = iter.map(|byte| byte as u32).sum();
///         // only allow even sums
///         if sum % 2 == 0 {
///             Ok(sum)
///         } else {
///             Err(ErrorKind::InvalidInput)
///         }
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") == Ok(Success(10, b"\x05")));
/// assert!(my_parser.parse(b"\x01\x02\x03") == Ok(Success(6, b"")));
/// assert!(my_parser.parse(b"\x01\x02").is_err());
/// assert!(my_parser.parse(b"\x01").is_err());
/// assert!(my_parser.parse(b"").is_err());
/// ```
#[inline]
pub const fn try_many<P, R, F, O, S, I>(
    parser: P,
    range: R,
    collect_fn: F,
) -> impl Parse<I, Parsed = O, Error = P::Error>
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(ManyIter<'a, P, I>) -> Result<O, S>,
    I: Input,
{
    TryManyParser(parser, range, collect_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct CollectManyParser<P, R, C, I>(P, R, PhantomData<fn() -> (C, I)>)
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    I: Input,
    C: FromIterator<P::Parsed>;

impl<P, R, C, I> Parse<I> for CollectManyParser<P, R, C, I>
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    type Parsed = C;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let max_count = match self.1.end_bound() {
            core::ops::Bound::Included(max_count) => Some(*max_count),
            core::ops::Bound::Excluded(&0) => Some(0),
            core::ops::Bound::Excluded(max_count) => Some(*max_count - 1),
            _ => None,
        };

        let mut count = 0usize;
        let mut err = None;
        let orig_input = input.clone();
        let ret = C::from_iter(ManyIter(
            &self.0, max_count, &mut input, &mut count, &mut err,
        ));
        let _ = ManyIter(&self.0, max_count, &mut input, &mut count, &mut err).count();

        match self.1.start_bound() {
            core::ops::Bound::Included(min_count) if count < *min_count => {
                if let Some(err) = err {
                    Err(Failure(err, orig_input))
                } else {
                    unreachable!()
                }
            }
            core::ops::Bound::Excluded(min_count) if count <= *min_count => {
                if let Some(err) = err {
                    Err(Failure(err, orig_input))
                } else {
                    unreachable!()
                }
            }
            _ => Ok(Success(ret, input)),
        }
    }
}

/// Creates a parser that is repeated a number of times within a range.
///
/// [`collect_many`] produces a parser that will apply `parser` repeatedly. The
/// number of times `parser` will be applied is defined by `range`. For example,
/// if `range` is `3..=5`, `parser` will be applied at least 3 times, and will
/// be applied up to 5 times if possible. If `parser` fails before parsing 3
/// times (or whatever lower bound applies to `range`, if any), a parsing error
/// is returned from the new parser. Once the upper bound is met (again, if any)
/// parsing automatically ends successfully. `parser` returning a parsing error
/// after meeting the lower bound also ends parsing for the new parser.
///
/// The values produced by `parser` are collected by the [`FromIterator`] trait
/// implementation on the parsed type of the parser, which is usually deduced.
///
/// Note that the returned new parser does not allocate unless the
/// [`FromIterator`] implementation allocates.
///
/// Also note that [`collect_many`] is a more generalized version of
/// [`collect_many0`], [`collect_many1`] and [`collect_repeated`]. If `range` is
/// `..`, the returned parser is equivalent to a [`collect_many0`] parser. If
/// `range` is `1..`, the returned parser is equivalent to a [`collect_many1`]
/// parser. If `range` is `count..=count`, the returned parser is equivalent to
/// a [`collect_repeated`] parser with a size of `count`.
///
/// See also [`Parse::collect_many`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_many;
/// # use pars::unicode::PResult;
/// use pars::unicode::{strict::char_with_prop, prop::Alphabetic};
///
/// fn my_parser(input: &str) -> PResult<String, &str> {
///     collect_many(char_with_prop(Alphabetic), 3..=5)
///         .parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello world"), Ok(Success(String::from("hello"), " world")));
/// assert_eq!(my_parser.parse("hey there"), Ok(Success(String::from("hey"), " there")));
/// assert!(my_parser.parse("hi there").is_err());
/// assert_eq!(my_parser.parse("goodbye"), Ok(Success(String::from("goodb"), "ye")));
/// ```
#[inline]
pub const fn collect_many<P, R, C, I>(
    parser: P,
    range: R,
) -> impl Parse<I, Parsed = C, Error = P::Error>
where
    P: Parse<I>,
    R: core::ops::RangeBounds<usize>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    CollectManyParser(parser, range, PhantomData)
}

#[derive(Debug, Clone)]
struct ArrayParser<P, I, const LEN: usize>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I, const LEN: usize> Parse<I> for ArrayParser<P, I, LEN>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = [P::Parsed; LEN];
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        let mut rem = input.clone();
        let mut arr: [core::mem::MaybeUninit<P::Parsed>; LEN] =
            [const { core::mem::MaybeUninit::uninit() }; LEN];
        for idx in 0..LEN {
            match self.0.parse(rem) {
                Ok(Success(val, new_rem)) => {
                    arr[idx].write(val);
                    rem = new_rem;
                }
                Err(Failure(e, _)) => {
                    unsafe {
                        for i in 0..idx {
                            arr[i].assume_init_drop();
                        }
                    }
                    return Err(Failure(e, input));
                }
            }
        }
        Ok(Success(
            unsafe {
                core::ptr::read(core::mem::transmute(
                    &arr as *const [core::mem::MaybeUninit<P::Parsed>; LEN],
                ))
            },
            rem,
        ))
    }
}

/// Creates a parser that is repeated a constant number of times.
///
/// [`array`](array()) produces a parser that applies `parser` `LEN` times and
/// places the parsed results in an array. If `parser` returns a parsing error
/// before parsing `LEN` times, a parsing error is returned from the new parser.
///
/// [`array`](array()) is similar to [`repeated`], except that the number of
/// repetitions is known at compile time and the results are placed in array
/// rather than being processed via an iterator. Most cases where the number of
/// repetitions is known at compile time should prefer to use [`array`](array()),
/// but be aware of the tradeoffs of storing and moving the values on the stack
/// when `LEN` is large.
///
/// See also [`Parse::array`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::array;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<[u8; 4], &[u8]> {
///     array(bytes::u8).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") == Ok(Success([1, 2, 3, 4], b"\x05")));
/// assert!(my_parser.parse(b"\x01\x02\x03").is_err());
/// ```
#[inline]
pub const fn array<P, I, const LEN: usize>(
    parser: P,
) -> impl Parse<I, Parsed = [P::Parsed; LEN], Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    ArrayParser(parser, PhantomData)
}

/// A parser that succeeds on empty input, and fails otherwise.
///
/// [`eof`] only parses successfully when the end of input has been reached.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// fn my_parser(input: &str) -> PResult<(), &str> {
///     verbatim("hello").then(eof).with(|| ()).parse(input)
/// }
///
/// assert!(my_parser.parse("hello").is_ok());
/// assert!(my_parser.parse("hello world").is_err());
/// assert!(my_parser.parse("").is_err());
/// ```
pub fn eof<I: Input, E: Error<I>>(input: I) -> PResult<(), I, E> {
    if let Some(_) = input.clone().next() {
        Err(Failure(E::expected_eof(input.clone()), input))
    } else {
        Ok(Success((), input))
    }
}

#[derive(Debug, Clone)]
struct CompleteParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for CompleteParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        let Success(val, rem) = self.0.parse(input.clone())?;
        if let Some(_) = rem.clone().next() {
            Err(Failure(Error::expected_eof(rem), input))
        } else {
            Ok(Success(val, rem))
        }
    }
}

/// Creates a parser that must consume all input.
///
/// [`complete`] produces a parser that applies `parser` and then checks that the end of
/// input has been reached. If there is still remaining input after `parser` parses
/// successfully, a parsing error is returned via [`Error::expected_eof`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::complete;
/// # use pars::unicode::PResult;
/// use pars::unicode::strict::verbatim;
///
/// fn my_parser(input: &str) -> PResult<(), &str> {
///     complete(verbatim("hello").with(|| ())).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello"), Ok(Success((), "")));
/// assert!(my_parser.parse("hello world").is_err());
/// assert!(my_parser.parse("hi").is_err());
/// ```
#[inline]
pub const fn complete<P, I>(parser: P) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    CompleteParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct SpannedParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for SpannedParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = (P::Parsed, Span<I>);
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        let orig_input = input.clone();
        let Success(ret, rem) = self.0.parse(input)?;
        Ok(Success((ret, Span::new(orig_input, rem.clone())), rem))
    }
}

/// Creates a parser that also returns a span of the input that was parsed.
///
/// [`spanned`] produces a parser that combines the parsed result of `parser`
/// with a span of the input that `parser` parsed in a 2-tuple. This allows
/// a parser to provide information about where in an input stream a parsed
/// value originated from.
///
/// If the parsed value returned by `parser` is not needed, such as a parser
/// that returns the unit type, consider using [`recognize`] instead.
///
/// See also [`Parse::spanned`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::spanned;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<(u32, &[u8]), &[u8]> {
///     spanned(bytes::be::u32)
///         .map(|(val, span)| (val, span.into()))
///         .parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") ==
///     Ok(Success((0x01020304, b"\x01\x02\x03\x04"), b"\x05")));
/// assert!(my_parser.parse(b"").is_err());
/// ```
#[inline]
pub const fn spanned<P, I>(
    parser: P,
) -> impl Parse<I, Parsed = (P::Parsed, Span<I>), Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    SpannedParser(parser, PhantomData)
}

/// Creates a parser that also returns a span of the input that was parsed.
///
/// [`spanned_into`] produces a parser that combines the parsed result of
/// `parser` with a [`Span`] of the input that `parser` parsed converted to
/// `S` via [`Into`] in a 2-tuple. This allows a parser to provide information
/// about where in an input stream a parsed value originated from.
///
/// [`spanned_into`] differs from [`spanned`] in that the produced [`Span`] is
/// converted into another type, `S` by way of [`Into`]. This is a common
/// enough pattern that [`spanned_into`] exists to simplify usage. For example,
/// a `Span<&str>` can be converted to a `&str` that contains just the content
/// of the span.
///
/// If the parsed value returned by `parser` is not needed, such as a parser
/// that returns the unit type, consider using [`recognize`] instead. Note that
/// [`recognize`] doesn't provide a `recognize_into` variant, since the same
/// effect can be accomplished with `recognize(parser).ok_into()` in this case.
///
/// See also [`Parse::spanned_into`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::spanned_into;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<(u32, &[u8]), &[u8]> {
///     spanned_into(bytes::be::u32).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") ==
///     Ok(Success((0x01020304, b"\x01\x02\x03\x04"), b"\x05")));
/// assert!(my_parser.parse(b"").is_err());
/// ```
#[inline]
pub const fn spanned_into<P, S, I>(
    parser: P,
) -> impl Parse<I, Parsed = (P::Parsed, S), Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    Span<I>: Into<S>,
{
    map(spanned(parser), |(res, span)| (res, span.into()))
}

#[derive(Debug, Clone)]
struct RecognizeParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for RecognizeParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = Span<I>;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        let orig_input = input.clone();
        let Success(_, rem) = self.0.parse(input)?;
        Ok(Success(Span::new(orig_input, rem.clone()), rem))
    }
}

#[inline]
pub const fn recognize<P, I>(parser: P) -> impl Parse<I, Parsed = Span<I>, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    RecognizeParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct CondParser<P, I>(P, bool, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for CondParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = Option<P::Parsed>;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        if self.1 {
            Ok(Success(None, input))
        } else {
            self.0.parse(input).map_parsed(Some)
        }
    }
}

#[inline]
pub const fn cond<P, I>(
    parser: P,
    condition: bool,
) -> impl Parse<I, Parsed = Option<P::Parsed>, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    CondParser(parser, condition, PhantomData)
}

#[derive(Debug, Clone)]
struct VerifyParser<P, F, I>(P, F, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input,
    F: Fn(&P::Parsed) -> bool;

impl<P, F, I> Parse<I> for VerifyParser<P, F, I>
where
    P: Parse<I>,
    I: Input,
    F: Fn(&P::Parsed) -> bool,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(val, rem)) if (self.1)(&val) => Ok(Success(val, rem)),
            Ok(_) => Err(Failure(Error::invalid_input(input.clone()), input)),
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn verify<P, F, I>(
    parser: P,
    verify_fn: F,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    F: Fn(&P::Parsed) -> bool,
{
    VerifyParser(parser, verify_fn, PhantomData)
}

#[derive(Debug, Clone)]
struct NotParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for NotParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = ();
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<(), I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(_) => Err(Failure(Error::invalid_input(input.clone()), input)),
            Err(_) => Ok(Success((), input)),
        }
    }
}

#[inline]
pub const fn not<P, I>(parser: P) -> impl Parse<I, Parsed = (), Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    NotParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct OptParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for OptParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = Option<P::Parsed>;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(val, rem)) => Ok(Success(Some(val), rem)),
            Err(Failure(_, rem)) => Ok(Success(None, rem)),
        }
    }
}

#[inline]
pub const fn opt<P, I>(parser: P) -> impl Parse<I, Parsed = Option<P::Parsed>, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    OptParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct PeekParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<P, I> Parse<I> for PeekParser<P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(val, _)) => Ok(Success(val, input)),
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn peek<P, I>(parser: P) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    PeekParser(parser, PhantomData)
}

pub fn remaining<I: Input, E: Error<I>>(mut input: I) -> PResult<I, I, E> {
    let ret = input.clone();
    input.advance_by(usize::MAX);
    Ok(Success(ret, input))
}

pub fn remaining_len<I: Input, E: Error<I>>(input: I) -> PResult<usize, I, E> {
    let len = input.clone().advance_by(usize::MAX);
    Ok(Success(len, input))
}

#[derive(Debug, Clone)]
struct AsRefParser<'a, P, I>(&'a P, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    I: Input;

impl<'a, P, I> Parse<I> for AsRefParser<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        self.0.parse(input)
    }
}

#[inline]
pub const fn as_ref<'a, P, I>(
    parser: &'a P,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error> + 'a
where
    P: Parse<I>,
    I: Input + 'a,
{
    AsRefParser(parser, PhantomData)
}

#[derive(Debug, Clone)]
struct PrefixParser<P, Q, I>(P, Q, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input;

impl<P, Q, I> Parse<I> for PrefixParser<P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = Q::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(_, rem)) => match self.1.parse(rem) {
                Ok(Success(val, rem)) => Ok(Success(val, rem)),
                Err(Failure(e, _)) => Err(Failure(e, input)),
            },
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn prefix<P, Q, I>(
    prefix: P,
    parser: Q,
) -> impl Parse<I, Parsed = Q::Parsed, Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    PrefixParser(prefix, parser, PhantomData)
}

#[derive(Debug, Clone)]
struct SuffixParser<P, Q, I>(P, Q, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input;

impl<P, Q, I> Parse<I> for SuffixParser<P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(val, rem)) => match self.1.parse(rem) {
                Ok(Success(_, rem)) => Ok(Success(val, rem)),
                Err(Failure(e, _)) => Err(Failure(e, input)),
            },
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn suffix<P, Q, I>(
    parser: P,
    suffix: Q,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    SuffixParser(parser, suffix, PhantomData)
}

#[derive(Debug, Clone)]
struct DelimitedParser<P, Q, S, I>(P, Q, S, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: Parse<I, Error = P::Error>,
    I: Input;

impl<P, Q, S, I> Parse<I> for DelimitedParser<P, Q, S, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = Q::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(_, rem)) => match self.1.parse(rem) {
                Ok(Success(val, rem)) => match self.2.parse(rem) {
                    Ok(Success(_, rem)) => Ok(Success(val, rem)),
                    Err(Failure(e, _)) => Err(Failure(e, input)),
                },
                Err(Failure(e, _)) => Err(Failure(e, input)),
            },
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn delimited<P, Q, S, I>(
    prefix: P,
    parser: Q,
    suffix: S,
) -> impl Parse<I, Parsed = Q::Parsed, Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: Parse<I, Error = P::Error>,
    I: Input,
{
    DelimitedParser(prefix, parser, suffix, PhantomData)
}

#[derive(Debug, Clone)]
struct SeparatedParser<P, S, Q, I>(P, S, Q, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    Q: Parse<I, Error = P::Error>,
    I: Input;

impl<P, S, Q, I> Parse<I> for SeparatedParser<P, S, Q, I>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = (P::Parsed, Q::Parsed);
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(first, rem)) => match self.1.parse(rem) {
                Ok(Success(_, rem)) => match self.2.parse(rem) {
                    Ok(Success(second, rem)) => Ok(Success((first, second), rem)),
                    Err(Failure(e, _)) => Err(Failure(e, input)),
                },
                Err(Failure(e, _)) => Err(Failure(e, input)),
            },
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn separated<P, S, Q, I>(
    first: P,
    separator: S,
    second: Q,
) -> impl Parse<I, Parsed = (P::Parsed, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    SeparatedParser(first, separator, second, PhantomData)
}

#[derive(Debug, Clone)]
struct PairParser<P, Q, I>(P, Q, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input;

impl<P, Q, I> Parse<I> for PairParser<P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    type Parsed = (P::Parsed, Q::Parsed);
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(first, rem)) => match self.1.parse(rem) {
                Ok(Success(second, rem)) => Ok(Success((first, second), rem)),
                Err(Failure(e, _)) => Err(Failure(e, input)),
            },
            Err(Failure(e, _)) => Err(Failure(e, input)),
        }
    }
}

#[inline]
pub const fn pair<P, Q, I>(
    first: P,
    second: Q,
) -> impl Parse<I, Parsed = (P::Parsed, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    PairParser(first, second, PhantomData)
}

#[derive(Debug, Clone)]
struct EitherParser<P, Q, I>(P, Q, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    Q: Parse<I, Parsed = P::Parsed, Error = P::Error>,
    I: Input;

impl<P, Q, I> Parse<I> for EitherParser<P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Parsed = P::Parsed, Error = P::Error>,
    I: Input,
{
    type Parsed = P::Parsed;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(val, rem)) => Ok(Success(val, rem)),
            Err(Failure(_, rem)) => match self.1.parse(rem) {
                Ok(Success(val, rem)) => Ok(Success(val, rem)),
                Err(Failure(e, rem)) => Err(Failure(e, rem)),
            },
        }
    }
}

#[inline]
pub const fn either<P, Q, I>(
    first: P,
    second: Q,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Parsed = P::Parsed, Error = P::Error>,
    I: Input,
{
    EitherParser(first, second, PhantomData)
}

struct IntoParser<P, R, E, I>(P, PhantomData<fn() -> (R, E, I)>)
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Into<R>,
    P::Error: Into<E>,
    E: Error<I>;

impl<P, R, E, I> Parse<I> for IntoParser<P, R, E, I>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Into<R>,
    P::Error: Into<E>,
    E: Error<I>,
{
    type Parsed = R;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<R, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input) {
            Ok(Success(val, rem)) => Ok(Success(val.into(), rem)),
            Err(Failure(err, rem)) => Err(Failure(err.into(), rem)),
        }
    }
}

/// Creates a parser whose parsed result or parsing error are converted via [`Into`].
///
/// If `parser` parses successfully, its result value is converted to `R` using the
/// [`Into<R>`] trait. If `parser` fails, the returned parsing error is converted to
/// `E` using the [`Into<E>`] trait.
///
/// See also [`Parse::res_into`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::{PResult, Error};
/// # use pars::basic::res_into;
/// # use pars::bytes;
/// #[derive(Debug, PartialEq)]
/// struct MyError<'a>(&'a [u8]);
///
/// # /*
/// impl<'a> Error<&'a [u8]> for MyError<'a> { ... }
/// impl<'a> From<bytes::Error<&'a [u8]>> for MyError<'a> { ... }
/// # */
/// # impl<'a> Error<&'a [u8]> for MyError<'a> {
/// #     fn need_more_input(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn expected_eof(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn invalid_input(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn position(&self) -> &&'a [u8] { &self.0 }
/// # }
/// # impl<'a> From<bytes::Error<&'a [u8]>> for MyError<'a> {
/// #     fn from(err: bytes::Error<&'a [u8]>) -> Self {
/// #         Self(*err.position())
/// #     }
/// # }
///
/// fn my_parser(input: &[u8]) -> PResult<Vec<u8>, &[u8], MyError<'_>> {
///     res_into(bytes::u8.array::<5>()).parse(input)
/// }
///
/// assert!(my_parser.parse(b"hello world") == Ok(Success(Vec::from(b"hello"), b" world")));
/// assert!(my_parser.parse(b"hi") == Err(Failure(MyError(b""), b"hi")));
/// ```
#[inline]
pub const fn res_into<P, R, E, I>(parser: P) -> impl Parse<I, Parsed = R, Error = E>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Into<R>,
    P::Error: Into<E>,
    E: Error<I>,
{
    IntoParser(parser, PhantomData)
}

/// Creates a parser whose parsed result is converted via [`Into`].
///
/// If `parser` parses successfully, its result value is converted to `R` using the
/// [`Into<R>`] trait.
///
/// See also [`Parse::ok_into`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::ok_into;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<Vec<u8>, &[u8]> {
///     ok_into(bytes::u8.array::<5>()).parse(input)
/// }
///
/// assert!(my_parser.parse(b"hello world") == Ok(Success(Vec::from(b"hello"), b" world")));
/// ```
#[inline]
pub const fn ok_into<P, R, I>(parser: P) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: Into<R>,
{
    IntoParser(parser, PhantomData)
}

/// Creates a parser whose parsing error is converted via [`Into`].
///
/// If `parser` fails to parse, the returned parsing error is converted to
/// `E` using the [`Into<E>`] trait.
///
/// See also [`Parse::err_into`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::{PResult, Error};
/// # use pars::basic::res_into;
/// # use pars::bytes;
/// #[derive(Debug, PartialEq)]
/// struct MyError<'a>(&'a [u8]);
///
/// # /*
/// impl<'a> Error<&'a [u8]> for MyError<'a> { ... }
/// impl<'a> From<bytes::Error<&'a [u8]>> for MyError<'a> { ... }
/// # */
/// # impl<'a> Error<&'a [u8]> for MyError<'a> {
/// #     fn need_more_input(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn expected_eof(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn invalid_input(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn position(&self) -> &&'a [u8] { &self.0 }
/// # }
/// # impl<'a> From<bytes::Error<&'a [u8]>> for MyError<'a> {
/// #     fn from(err: bytes::Error<&'a [u8]>) -> Self {
/// #         Self(*err.position())
/// #     }
/// # }
///
/// fn my_parser(input: &[u8]) -> PResult<u8, &[u8], MyError<'_>> {
///     res_into(bytes::u8).parse(input)
/// }
///
/// assert!(my_parser.parse(b"hello") == Ok(Success(b'h', b"ello")));
/// assert!(my_parser.parse(b"") == Err(Failure(MyError(b""), b"")));
#[inline]
pub const fn err_into<P, E, I>(parser: P) -> impl Parse<I, Parsed = P::Parsed, Error = E>
where
    P: Parse<I>,
    I: Input,
    P::Error: Into<E>,
    E: Error<I>,
{
    IntoParser(parser, PhantomData)
}

struct TryIntoParser<P, R, E, I>(P, PhantomData<fn() -> (R, E, I)>)
where
    P: Parse<I>,
    I: Input,
    P::Parsed: TryInto<R>,
    P::Error: Into<E>,
    E: Error<I>;

impl<P, R, E, I> Parse<I> for TryIntoParser<P, R, E, I>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: TryInto<R>,
    P::Error: Into<E>,
    E: Error<I>,
{
    type Parsed = R;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<R, I, E>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        match self.0.parse(input.clone()) {
            Ok(Success(val, rem)) => match val.try_into() {
                Ok(val) => Ok(Success(val, rem)),
                Err(_) => Err(Failure(E::invalid_input(input.clone()), input)),
            },
            Err(Failure(err, rem)) => Err(Failure(err.into(), rem)),
        }
    }
}

/// Creates a parser whose parsed result is converted via [`TryInto`].
///
/// If `parser` parses successfully, its result value is converted to `R` using the
/// [`TryInto<R>`] trait. If [`TryInto`] fails, a parsing error is returned by
/// calling [`E::invalid_input`](Error::invalid_input). If `parser` returns a parsing
/// error, that error is converted to `E` using the [`Into<E>`] trait.
///
/// Note that the parsing error is not converted using [`TryInto`], but rather the
/// infallible [`Into`] trait. Only the successfully parsed result converts via
/// [`TryInto`].
///
/// See also [`Parse::res_try_into`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::{PResult, Error};
/// # use pars::basic::res_try_into;
/// # use pars::bytes;
/// #[derive(Debug, PartialEq)]
/// struct MyError<'a>(&'a [u8]);
///
/// # /*
/// impl<'a> Error<&'a [u8]> for MyError<'a> { ... }
/// impl<'a> From<bytes::Error<&'a [u8]>> for MyError<'a> { ... }
/// # */
/// # impl<'a> Error<&'a [u8]> for MyError<'a> {
/// #     fn need_more_input(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn expected_eof(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn invalid_input(pos: &'a [u8]) -> Self { Self(pos) }
/// #     fn position(&self) -> &&'a [u8] { &self.0 }
/// # }
/// # impl<'a> From<bytes::Error<&'a [u8]>> for MyError<'a> {
/// #     fn from(err: bytes::Error<&'a [u8]>) -> Self {
/// #         Self(*err.position())
/// #     }
/// # }
///
/// fn my_parser(input: &[u8]) -> PResult<char, &[u8], MyError<'_>> {
///     res_try_into(bytes::be::u32).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x00\x00\x00hello") == Ok(Success('h', b"ello")));
/// assert!(my_parser.parse(b"\xff\xff\xffhello")
///     == Err(Failure(MyError(b"\xff\xff\xffhello"), b"\xff\xff\xffhello")));
/// assert!(my_parser.parse(b"") == Err(Failure(MyError(b""), b"")));
/// ```
#[inline]
pub const fn res_try_into<P, R, E, I>(parser: P) -> impl Parse<I, Parsed = R, Error = E>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: TryInto<R>,
    P::Error: Into<E>,
    E: Error<I>,
{
    TryIntoParser(parser, PhantomData)
}

/// Creates a parser whose parsed result is converted via [`TryInto`].
///
/// If `parser` parses successfully, its result value is converted to `R` using the
/// [`TryInto<R>`] trait. If [`TryInto`] fails, a parsing error is returned by calling
/// [`Error::invalid_input`].
///
/// See also [`Parse::ok_try_into`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::ok_try_into;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<char, &[u8]> {
///     ok_try_into(bytes::be::u32).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x00\x00\x00hello") == Ok(Success('h', b"ello")));
/// assert!(my_parser.parse(b"\xff\xff\xffhello").is_err());
/// ```
#[inline]
pub const fn ok_try_into<P, R, I>(parser: P) -> impl Parse<I, Parsed = R, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
    P::Parsed: TryInto<R>,
{
    TryIntoParser(parser, PhantomData)
}
