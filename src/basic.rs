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

/// Creates a parser that matches a permutation of a sequence of parsers.
///
/// [`permutation`] will accept any number of parsers as arguments. The returned parser
/// will attempt to apply the parsers in an order such that all parsers succeed. When
/// a parser succeeds, its order in the permutation is set, and it will not be applied
/// again. If all remaining parsers fail at any point, the returned parser fails,
/// returning the error of the last failing parser applied.
///
/// The parsed values of the parser arguments are returned in a tuple in the same order
/// as the parsers are provided as arguments, regardless of the permutation order.
///
/// It is important to keep in mind that once a parser succeeds, it will not later be
/// reordered to find a successful permutation. This means that in some cases a valid
/// permutation could be available that will never be attempted and an error is
/// returned.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::permutation;
/// fn my_parser(input: &str) -> PResult<(&str, &str, &str), &str> {
///     permutation!(
///         unicode::strict::verbatim("foo").ok_into(),
///         unicode::strict::verbatim("bar").ok_into(),
///         unicode::strict::verbatim("baz").ok_into(),
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("foobarbazquux"), Ok(Success(("foo", "bar", "baz"), "quux")));
/// assert_eq!(my_parser.parse("foobazbarquux"), Ok(Success(("foo", "bar", "baz"), "quux")));
/// assert_eq!(my_parser.parse("barfoobazquux"), Ok(Success(("foo", "bar", "baz"), "quux")));
/// assert_eq!(my_parser.parse("barbazfooquux"), Ok(Success(("foo", "bar", "baz"), "quux")));
/// assert_eq!(my_parser.parse("bazfoobarquux"), Ok(Success(("foo", "bar", "baz"), "quux")));
/// assert_eq!(my_parser.parse("bazbarfooquux"), Ok(Success(("foo", "bar", "baz"), "quux")));
/// ```
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
/// When using the combinators [`repeated_until`], [`try_repeated_until`], and
/// [`collect_repeated_until`], this iterator type is used as the interface into the
/// repeated applications of the provided parser. The [`Iterator::Item`] is the
/// [`Parse::Parsed`] type of the provided parser.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`RepeatedUntilIter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed. For example,
/// `parser.repeated_until(sentinel, |_| ())`.
///
/// See [`repeated_until`], [`try_repeated_until`], and [`collect_repeated_until`] for
/// examples.
#[derive(Debug)]
pub struct RepeatedUntilIter<'a, P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    parser: &'a P,
    sentinel: &'a Q,
    input: &'a mut I,
    result: &'a mut Option<Result<Q::Parsed, P::Error>>,
}

impl<'a, P, Q, I> Iterator for RepeatedUntilIter<'a, P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        if self.result.is_some() {
            return None;
        }

        match self.sentinel.parse(self.input.clone()) {
            Ok(Success(sent, rem)) => {
                *self.result = Some(Ok(sent));
                *self.input = rem;
                None
            }
            Err(Failure(err, rem)) => match self.parser.parse(rem) {
                Ok(Success(ret, rem)) => {
                    *self.input = rem;
                    Some(ret)
                }
                Err(_) => {
                    *self.result = Some(Err(err));
                    None
                }
            },
        }
    }
}

impl<'a, P, Q, I> core::iter::FusedIterator for RepeatedUntilIter<'a, P, Q, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
{
}

/// Creates a parser that is repeated until a sentinel is parsed.
///
/// [`repeated_until`] produces a parser that will apply `parser` repeatedly until
/// `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it fails,
/// `parser` is applied before trying `sentinel_parser` again. If `sentinel_parser`
/// succeeds, parsing is complete.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of an
/// iterator, [`RepeatedUntilIter`]. The value returned by `collect_fn` and the parsed
/// value from `sentinel_parser` together as a 2-tuple become the parsed result of
/// the overall new parser. If `parser` returns a parsing error at any point, a
/// parsing error is returned from the overall new parser.
///
/// Note that the returned new parser does not allocate. Values produced by
/// the iterator are obtained on demand by applying `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user
/// provided function `collect_fn` allocates to produce its result.
///
/// See also [`Parse::repeated_until`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::repeated_until;
/// # use pars::bytes::{self, PResult};
/// fn c_str_len(input: &[u8]) -> PResult<usize, &[u8]> {
///     repeated_until(bytes::u8, bytes::verbatim(b"\x00"), |iter| iter.count())
///         .map(|(len, _)| len) // we only want the length
///         .parse(input)
/// }
///
/// assert!(c_str_len.parse(b"hello\x00world") == Ok(Success(5, b"world")));
/// assert!(c_str_len.parse(b"\x00") == Ok(Success(0, b"")));
/// assert!(c_str_len.parse(b"hello").is_err());
/// ```
#[inline]
pub const fn repeated_until<P, Q, F, R, I>(
    parser: P,
    sentinel_parser: Q,
    collect_fn: F,
) -> impl Parse<I, Parsed = (R, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    F: for<'a> Fn(RepeatedUntilIter<'a, P, Q, I>) -> R,
    I: Input,
{
    try_repeated_until(
        parser,
        sentinel_parser,
        move |iter| -> Result<R, core::convert::Infallible> { Ok(collect_fn(iter)) },
    )
}

#[derive(Debug, Clone)]
struct TryRepeatedUntilParser<P, Q, F, R, S, I>(P, Q, F, PhantomData<fn() -> (R, S, I)>)
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedUntilIter<'a, P, Q, I>) -> Result<R, S>,
    I: Input;

impl<P, Q, F, R, S, I> Parse<I> for TryRepeatedUntilParser<P, Q, F, R, S, I>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedUntilIter<'a, P, Q, I>) -> Result<R, S>,
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
        let ret = match (self.2)(RepeatedUntilIter {
            parser: &self.0,
            sentinel: &self.1,
            input: &mut input,
            result: &mut sentinel,
        }) {
            Ok(ret) => ret,
            Err(e) => {
                return Err(Failure(e.into_error(orig_input.clone()), orig_input));
            }
        };
        RepeatedUntilIter {
            parser: &self.0,
            sentinel: &self.1,
            input: &mut input,
            result: &mut sentinel,
        }
        .for_each(|_| ());
        match sentinel {
            Some(Ok(sentinel)) => Ok(Success((ret, sentinel), input)),
            Some(Err(err)) => Err(Failure(err, orig_input)),
            None => unreachable!(),
        }
    }
}

/// Creates a parser that is repeated until a sentinel is parsed.
///
/// [`try_repeated_until`] produces a parser that will apply `parser` repeatedly until
/// `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it fails,
/// `parser` is applied before trying `sentinel_parser` again. If `sentinel_parser`
/// succeeds, parsing is complete.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of an
/// iterator, [`RepeatedUntilIter`]. If `collect_fn` returns an [`Ok`] value, that and
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
/// See also [`Parse::try_repeated_until`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::try_repeated_until;
/// # use pars::ErrorKind;
/// # use pars::bytes::{self, PResult};
/// fn c_str_len(input: &[u8]) -> PResult<usize, &[u8]> {
///     try_repeated_until(bytes::u8, bytes::verbatim(b"\x00"), |iter| {
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
pub const fn try_repeated_until<P, Q, F, R, S, I>(
    parser: P,
    sentinel_parser: Q,
    collect_fn: F,
) -> impl Parse<I, Parsed = (R, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedUntilIter<'a, P, Q, I>) -> Result<R, S>,
    I: Input,
{
    TryRepeatedUntilParser(parser, sentinel_parser, collect_fn, PhantomData)
}

/// Creates a parser that is repeated until a sentinel is parsed.
///
/// [`collect_repeated_until`] produces a parser that will apply `parser` repeatedly
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
/// See also [`Parse::collect_repeated_until`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_repeated_until;
/// # use pars::bytes::{self, PResult};
/// fn c_str(input: &[u8]) -> PResult<Vec<u8>, &[u8]> {
///     collect_repeated_until(bytes::u8, bytes::verbatim(b"\x00"))
///         .map(|(s, _)| s)
///         .parse(input)
/// }
///
/// assert!(c_str.parse(b"hello\x00world") == Ok(Success(Vec::from(b"hello"), b"world")));
/// assert!(c_str.parse(b"\x00") == Ok(Success(Vec::new(), b"")));
/// assert!(c_str.parse(b"hello").is_err());
/// ```
#[inline]
pub const fn collect_repeated_until<P, Q, C, I>(
    parser: P,
    sentinel: Q,
) -> impl Parse<I, Parsed = (C, Q::Parsed), Error = P::Error>
where
    P: Parse<I>,
    Q: Parse<I, Error = P::Error>,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    repeated_until(parser, sentinel, |iter| iter.collect())
}

/// An [`Iterator`] over repeated applications of a parser.
///
/// When using the combinators [`repeated`], [`try_repeated`], and [`collect_repeated`],
/// this iterator type is used as the interface into the repeated applications
/// of the provided parser. The [`Iterator::Item`] is the [`Parse::Parsed`]
/// type of the provided parser.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`RepeatedIter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the
/// iterator altogether when the parsed values are not needed. For example,
/// `parser.repeated(3.., |_| ())`.
///
/// See [`repeated`], [`try_repeated`], and [`collect_repeated`] for examples.
#[derive(Debug)]
pub struct RepeatedIter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    parser: &'a P,
    max_count: usize,
    input: &'a mut I,
    count: &'a mut usize,
    error: &'a mut Option<P::Error>,
}

impl<'a, P, I> Iterator for RepeatedIter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        if *self.count >= self.max_count || self.error.is_some() {
            return None;
        }

        match self.parser.parse(self.input.clone()) {
            Ok(Success(ret, rem)) => {
                *self.count += 1;
                *self.input = rem;
                Some(ret)
            }
            Err(Failure(e, _)) => {
                *self.error = Some(e);
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            0,
            if self.max_count == usize::MAX {
                None
            } else {
                Some(self.max_count - *self.count)
            },
        )
    }
}

impl<'a, P, I> core::iter::FusedIterator for RepeatedIter<'a, P, I>
where
    P: Parse<I>,
    I: Input,
{
}

/// Creates a parser that is repeated a number of times within a range.
///
/// [`repeated`] produces a parser that will apply `parser` repeatedly. The number
/// of times `parser` will be applied is defined by `range`. For example, if
/// `range` is `3..=5`, `parser` will be applied at least 3 times, and will be
/// applied up to 5 times if possible. If `parser` fails before parsing 3 times
/// (or whatever lower bound applies to `range`, if any), a parsing error is
/// returned from the new parser. Once the upper bound is met (again, if any)
/// parsing automatically ends successfully. `parser` returning a parsing error
/// after meeting the lower bound also ends parsing for the new parser.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of
/// an iterator, [`RepeatedIter`]. Whever `collect_fn` returns is the parsed value
/// of the new parser.
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
///     repeated(bytes::u8, 2..=4, |iter| {
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
pub const fn repeated<P, R, F, O, I>(
    parser: P,
    range: R,
    collect_fn: F,
) -> impl Parse<I, Parsed = O, Error = P::Error>
where
    P: Parse<I>,
    R: Range,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> O,
    I: Input,
{
    try_repeated(
        parser,
        range,
        move |iter| -> Result<O, core::convert::Infallible> { Ok(collect_fn(iter)) },
    )
}

#[derive(Debug, Clone)]
struct TryRepeatedParser<P, R, F, O, S, I>(P, R, F, PhantomData<fn() -> (O, S, I)>)
where
    P: Parse<I>,
    R: Range,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> Result<O, S>,
    I: Input;

impl<P, R, F, O, S, I> Parse<I> for TryRepeatedParser<P, R, F, O, S, I>
where
    P: Parse<I>,
    R: Range,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> Result<O, S>,
    I: Input,
{
    type Parsed = O;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<O, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let max_count = self.1.maximum();

        let mut count = 0usize;
        let mut err = None;
        let orig_input = input.clone();
        let ret = match (self.2)(RepeatedIter {
            parser: &self.0,
            max_count,
            input: &mut input,
            count: &mut count,
            error: &mut err,
        }) {
            Ok(ret) => ret,
            Err(e) => {
                return Err(Failure(e.into_error(orig_input.clone()), orig_input));
            }
        };
        RepeatedIter {
            parser: &self.0,
            max_count,
            input: &mut input,
            count: &mut count,
            error: &mut err,
        }
        .for_each(|_| ());

        if count < self.1.minimum() {
            let Some(err) = err else {
                unreachable!();
            };
            Err(Failure(err, orig_input))
        } else {
            Ok(Success(ret, input))
        }
    }
}

/// Creates a parser that is repeated a number of times within a range.
///
/// [`try_repeated`] produces a parser that will apply `parser` repeatedly. The
/// number of times `parser` will be applied is defined by `range`. For example,
/// if `range` is `3..=5`, `parser` will be applied at least 3 times, and will
/// be applied up to 5 times if possible. If `parser` fails before parsing 3
/// times (or whatever lower bound applies to `range`, if any), a parsing error
/// is returned from the new parser. Once the upper bound is met (again, if any)
/// parsing automatically ends successfully. `parser` returning a parsing error
/// after meeting the lower bound also ends parsing for the new parser.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of
/// an iterator, [`RepeatedIter`]. If `collect_fn` returns an [`Ok`] value, the
/// contained value becomes the parsed value of the new parser. If `collect_fn`
/// returns an [`Err`], that gets returned as a parsing error via [`ErrorSeed`].
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
/// # use pars::bytes::{self, PResult};
/// # use pars::ErrorKind;
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     try_repeated(bytes::u8, 2..=4, |iter| {
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
pub const fn try_repeated<P, R, F, O, S, I>(
    parser: P,
    range: R,
    collect_fn: F,
) -> impl Parse<I, Parsed = O, Error = P::Error>
where
    P: Parse<I>,
    R: Range,
    S: ErrorSeed<I, P::Error>,
    F: for<'a> Fn(RepeatedIter<'a, P, I>) -> Result<O, S>,
    I: Input,
{
    TryRepeatedParser(parser, range, collect_fn, PhantomData)
}

/// Creates a parser that is repeated a number of times within a range.
///
/// [`collect_repeated`] produces a parser that will apply `parser` repeatedly. The
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
/// See also [`Parse::collect_repeated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_repeated;
/// # use pars::unicode::PResult;
/// use pars::unicode::{strict::char_with_prop, prop::Alphabetic};
///
/// fn my_parser(input: &str) -> PResult<String, &str> {
///     collect_repeated(char_with_prop(Alphabetic), 3..=5)
///         .parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello world"), Ok(Success(String::from("hello"), " world")));
/// assert_eq!(my_parser.parse("hey there"), Ok(Success(String::from("hey"), " there")));
/// assert!(my_parser.parse("hi there").is_err());
/// assert_eq!(my_parser.parse("goodbye"), Ok(Success(String::from("goodb"), "ye")));
/// ```
#[inline]
pub const fn collect_repeated<P, R, C, I>(
    parser: P,
    range: R,
) -> impl Parse<I, Parsed = C, Error = P::Error>
where
    P: Parse<I>,
    R: Range,
    I: Input,
    C: FromIterator<P::Parsed>,
{
    repeated(parser, range, |iter| iter.collect())
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

/// Creates a parser that fails if all input is not consumed.
///
/// [`complete`] produces a parser that applies `parser` and then verifies that
/// all input was consumed. If there is still input remaining, an error is returned
/// via [`Error::expected_eof`].
///
/// See also [`Parse::complete`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::complete;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     complete(bytes::be::u32).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success(0x01020304, &[][..])));
/// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05").is_err());
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

/// Creates a parser that returns a [`Span`] of parsed input in addition to the parsed value.
///
/// [`spanned`] produces a parser that applies `parser`, and on success, it returns the
/// parsed value from `parser` in a tuple with a [`Span`] of the input consumed to produce
/// the parsed value.
///
/// If only the [`Span`] is needed and the parsed value can be discarded, [`recognize`] can
/// also be used instead.
///
/// See also [`Parse::spanned`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::spanned;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<(u32, Span<&[u8]>), &[u8]> {
///     spanned(bytes::be::u32).parse(input)
/// }
///
/// let res = my_parser.parse(b"\x01\x02\x03\x04\x05");
/// assert!(res.is_ok());
/// let Success((value, span), rem) = res.unwrap();
/// let span: &[u8] = span.into();
/// assert_eq!(value, 0x01020304);
/// assert_eq!(span, &[1u8, 2, 3, 4][..]);
/// assert_eq!(rem, &[5u8][..]);
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

/// Creates a parser that returns a [`Span`] of parsed input.
///
/// [`recognize`] produces a parser that applies `parser` and on success, it returns
/// a [`Span`] of the input consumed by `parser`.
///
/// [`recognize`] is similar to [`spanned`], except that the parsed value returned by
/// `parser` is discarded.
///
/// See also [`Parse::recognize`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::recognize;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<Span<&[u8]>, &[u8]> {
///     recognize(bytes::be::u32).parse(input)
/// }
///
/// let res = my_parser.parse(b"\x01\x02\x03\x04\x05");
/// assert!(res.is_ok());
/// let Success(span, rem) = res.unwrap();
/// let span: &[u8] = span.into();
/// assert_eq!(span, b"\x01\x02\x03\x04");
/// assert_eq!(rem, b"\x05");
/// ```
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
            self.0.parse(input).map_parsed(Some)
        } else {
            Ok(Success(None, input))
        }
    }
}

/// Creates a parser that produces a parsed value only if `condition` is `true`.
///
/// [`cond`] produces a parser that applies `parser` only if `condition` is `true`.
/// On success, the parsed value returned by `parser` returned wrapped in [`Some`].
/// If `condition` is `false`, the parser succeeds, but returns [`None`] as the
/// parsed value.
///
/// See also [`Parse::cond`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::cond;
/// # use pars::bytes::{self, PResult};
/// fn my_parser(input: &[u8]) -> PResult<Option<u32>, &[u8]> {
///     bytes::u8.flat_map(|b| {
///         cond(bytes::be::u32, b != 0)
///     }).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x00\x01\x02\x03\x04") == Ok(Success(None, b"\x01\x02\x03\x04")));
/// assert!(my_parser.parse(b"\x01\x01\x02\x03\x04") == Ok(Success(Some(0x01020304), b"")));
/// ```
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

/// Creates a parser that succeeds only if the parsed value passes the given predicate.
///
/// [`verify`] produces a parser that applies `parser`, and on success, passes the parsed
/// value to `verify_fn`. If `verify_fn` returns `true`, the parser returns the parsed value.
/// If `verify_fn` returns `false`, the parser returns an error via [`Error::invalid_input`].
///
/// See also [`Parse::verify`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::verify;
/// fn non_zero(input: &[u8]) -> PResult<u32, &[u8]> {
///     verify(bytes::be::u32, |v| *v != 0).parse(input)
/// }
///
/// assert!(non_zero.parse(b"\x00\x00\x00\x00").is_err());
/// assert!(non_zero.parse(b"\x00\x00\x00\x01") == Ok(Success(1, b"")));
/// ```
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

/// Creates a parser that succeeds only if `parser` fails.
///
/// [`not`] produces a parser that applies `parser`, an on success, it returns an
/// error via [`Error::invalid_input`]. If `parser` fails, the new parser returns
/// a success.
///
/// See also [`Parse::not`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::ascii::{self, PResult};
/// # use pars::basic::not;
/// fn my_parser(input: &str) -> PResult<(), &str> {
///     not(ascii::strict::char_with_prop(ascii::prop::Printable)).parse(input)
/// }
///
/// assert!(my_parser.parse("hello").is_err());
/// assert!(my_parser.parse("\0").is_ok());
/// ```
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

/// Creates a parser that attempts to parse with `parser` if possible.
///
/// [`opt`] produces a parser that applies `parser`, and on success, the new parser
/// returns the parsed value wrapped in [`Some`]. On failure, the new parser still
/// succeeds but returns [`None`] without consuming any input.
///
/// See also [`Parse::opt`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::opt;
/// fn my_parser(input: &[u8]) -> PResult<Option<&[u8]>, &[u8]> {
///     opt(bytes::verbatim("hello").ok_into()).parse(input)
/// }
///
/// assert!(my_parser.parse(b"hello world") == Ok(Success(Some(&b"hello"[..]), b" world")));
/// assert!(my_parser.parse(b"goodbye world") == Ok(Success(None, b"goodbye world")));
/// ```
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

/// Creates a parser that parses without consuming input.
///
/// [`peek`] produces a parser that applies `parser`, and on success, the new parser returns
/// the parsed value returned by `parser` and the entire input that was passed to the parser.
/// On failure, the new parser forwards the error unmodified.
///
/// See also [`Parse::peek`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::peek;
/// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
///     peek(bytes::be::u32).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success(0x01020304, b"\x01\x02\x03\x04")));
/// ```
#[inline]
pub const fn peek<P, I>(parser: P) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error>
where
    P: Parse<I>,
    I: Input,
{
    PeekParser(parser, PhantomData)
}

/// Parser that returns the remaining input.
///
/// [`remaining`] is a parser that always succeeds and consumes all input. The parsed value
/// is the entire input passed to the parser.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::remaining;
/// fn my_parser(input: &[u8]) -> PResult<(u8, &[u8]), &[u8]> {
///     bytes::u8.then(remaining).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success((1u8, &b"\x02\x03\x04"[..]), b"")));
/// assert!(my_parser.parse(b"\x01") == Ok(Success((1, &b""[..]), b"")));
/// ```
pub fn remaining<I: Input, E: Error<I>>(mut input: I) -> PResult<I, I, E> {
    let ret = input.clone();
    input.advance_by(usize::MAX);
    Ok(Success(ret, input))
}

/// Parser that returns the length of the remaining input without consuming input.
///
/// [`remaining_len`] is a parser that always succeeds and does not consume any input. The parsed
/// value is the number of symbols in the input passed to the parser.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::remaining_len;
/// fn my_parser(input: &[u8]) -> PResult<(u8, usize), &[u8]> {
///     bytes::u8.then(remaining_len).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success((1u8, 3), b"\x02\x03\x04")));
/// assert!(my_parser.parse(b"\x01") == Ok(Success((1u8, 0), b"")));
/// ```
pub fn remaining_len<I: Input, E: Error<I>>(input: I) -> PResult<usize, I, E> {
    let len = input.clone().advance_by(usize::MAX);
    Ok(Success(len, input))
}

#[derive(Debug, Clone)]
struct ByRefParser<'a, P, I>(&'a P, PhantomData<fn() -> I>)
where
    P: Parse<I> + ?Sized,
    I: Input;

impl<'a, P, I> Parse<I> for ByRefParser<'a, P, I>
where
    P: Parse<I> + ?Sized,
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

/// Creates a parser out of a reference to another parser.
///
/// [`by_ref`] produces a parser that directly applies `parser`. The produced
/// parser behaves identically to `parser` and internally contains a reference
/// to `parser`.
///
/// [`Parse`] is not automatically implemented for references to types that
/// implement [`Parse`], so [`by_ref`] can by used to convert a reference to
/// a parser into a parser.
///
/// See also [`Parse::by_ref`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::bytes::{self, PResult};
/// # use pars::basic::by_ref;
/// fn my_parser(input: &[u8]) -> PResult<u8, &[u8]> {
///     by_ref(&bytes::u8).parse(input)
/// }
///
/// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success(1u8, b"\x02\x03\x04")));
/// assert!(my_parser.parse(b"").is_err());
/// ```
#[inline]
pub const fn by_ref<'a, P, I>(
    parser: &'a P,
) -> impl Parse<I, Parsed = P::Parsed, Error = P::Error> + 'a
where
    P: Parse<I> + ?Sized,
    I: Input + 'a,
{
    ByRefParser(parser, PhantomData)
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

/// Creates a parser that applies two parsers and discards the first.
///
/// [`prefix`] produces a parser that applies `prefix` and `parser` in
/// sequence. If both succeed, the parsed value returned by `prefix` is
/// discarded and the parsed value returned by `parser` is returned by
/// the new parser. If either parser fails, the corresponding error is
/// returned from the new parser. When `prefix` fails, `parser` is not
/// applied.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::prefix;
/// fn my_parser(input: &str) -> PResult<char, &str> {
///     prefix(
///         unicode::strict::verbatim("hello"),
///         unicode::strict::char,
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("hello world"), Ok(Success(' ', "world")));
/// assert!(my_parser.parse("hello").is_err());
/// assert!(my_parser.parse("goodbye world").is_err());
/// ```
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

/// Creates a parser that applies two parsers and discards the second.
///
/// [`suffix`] produces a parser that applies `parser` and `suffix` in
/// sequence. If both succeed, the parsed value returned by `parser` is
/// returned by the new parser, and the parsed value returned by `suffix`
/// is discarded. If either parser fails, the corresponding error is
/// returned from teh new parser. When `parser` fails, `suffix` is not
/// applied.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::suffix;
/// fn my_parser(input: &str) -> PResult<char, &str> {
///     suffix(
///         unicode::strict::char,
///         unicode::strict::verbatim("foo"),
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("afoobar"), Ok(Success('a', "bar")));
/// assert!(my_parser.parse("foobar").is_err());
/// ```
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

/// Creates a parser that applies three parser and discards the parsed value of the first and last.
///
/// [`delimited`] produces a parser that applies `prefix`, `parser`, and `suffix` in
/// sequence. On success, the parsed value returned by `parser` is returned from the
/// new parser, and the parsed values returned by `prefix` and `suffix` are discarded.
/// If any of the parsers fail, the corresponding error is returned from the new parser
/// and the remaining parsers are not applied.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::delimited;
/// fn my_parser(input: &str) -> PResult<char, &str> {
///     delimited(
///         unicode::strict::verbatim("foo"),
///         unicode::strict::char,
///         unicode::strict::verbatim("bar"),
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("foo bar baz"), Ok(Success(' ', " baz")));
/// assert!(my_parser.parse("foo baz").is_err());
/// assert!(my_parser.parse("baz bar").is_err());
/// ```
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
struct SeparatedPairParser<P, S, Q, I>(P, S, Q, PhantomData<fn() -> I>)
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    Q: Parse<I, Error = P::Error>,
    I: Input;

impl<P, S, Q, I> Parse<I> for SeparatedPairParser<P, S, Q, I>
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

/// Creates a parser that applies three parsers and discards the second.
///
/// [`separated_pair`] produces a parser that applies `first`, `separator`,
/// and `second` in sequence. On Success, the parsed values returned by
/// `first` and `second` are returned by the new parser as a tuple, and
/// the parsed value returned by `separator` is discarded. If any of the
/// parsers fails, the corresponding error is returned by the new parser
/// and any remaining parsers are not applied.
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::separated_pair;
/// fn my_parser(input: &str) -> PResult<(char, char), &str> {
///     separated_pair(
///         unicode::strict::char,
///         unicode::strict::verbatim(","),
///         unicode::strict::char,
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("a,bcd"), Ok(Success(('a', 'b'), "cd")));
/// assert!(my_parser.parse("a,").is_err());
/// assert!(my_parser.parse(",b").is_err());
/// ```
#[inline]
pub const fn separated_pair<P, S, Q, I>(
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
    SeparatedPairParser(first, separator, second, PhantomData)
}

/// Trait representing a minimum and maximum number of repetitions.
///
/// [`Range`] is used by combinators such as [`repeated`] and [`separated`] to
/// specify either or both of the minimum and maximum number of repetitions.
/// [`Range`] is implemented for built-in range values using the `..` and `..=`
/// operators over `usize` values, as well as for plain `usize` values for an
/// exact number of repetitions.
///
/// In parsing, repeating a pattern zero or more times, or one or more times
/// are most common. `..` represents zero or more, and `1..` represents one
/// or more.
///
/// # Example
/// ```
/// # use pars::basic::Range;
/// let range = ..;
/// assert_eq!(range.minimum(), 0);
/// assert_eq!(range.maximum(), usize::MAX);
///
/// let range = ..10;
/// assert_eq!(range.minimum(), 0);
/// assert_eq!(range.maximum(), 9);
///
/// let range = 2..;
/// assert_eq!(range.minimum(), 2);
/// assert_eq!(range.maximum(), usize::MAX);
///
/// let range = 2..10;
/// assert_eq!(range.minimum(), 2);
/// assert_eq!(range.maximum(), 9);
///
/// let range = ..=10;
/// assert_eq!(range.minimum(), 0);
/// assert_eq!(range.maximum(), 10);
///
/// let range = 2..=10;
/// assert_eq!(range.minimum(), 2);
/// assert_eq!(range.maximum(), 10);
///
/// let range = 5;
/// assert_eq!(range.minimum(), 5);
/// assert_eq!(range.maximum(), 5);
/// ```
pub trait Range {
    /// The minimum number of repetitions
    fn minimum(&self) -> usize;

    /// The maximum number of repetitions
    fn maximum(&self) -> usize;
}

impl Range for usize {
    fn minimum(&self) -> usize {
        *self
    }

    fn maximum(&self) -> usize {
        *self
    }
}

impl Range for core::ops::Range<usize> {
    fn minimum(&self) -> usize {
        self.start
    }

    fn maximum(&self) -> usize {
        self.end.saturating_sub(1)
    }
}

impl Range for core::ops::RangeInclusive<usize> {
    fn minimum(&self) -> usize {
        *self.start()
    }

    fn maximum(&self) -> usize {
        *self.end()
    }
}

impl Range for core::ops::RangeFull {
    fn minimum(&self) -> usize {
        0
    }

    fn maximum(&self) -> usize {
        usize::MAX
    }
}

impl Range for core::ops::RangeFrom<usize> {
    fn minimum(&self) -> usize {
        self.start
    }

    fn maximum(&self) -> usize {
        usize::MAX
    }
}

impl Range for core::ops::RangeTo<usize> {
    fn minimum(&self) -> usize {
        0
    }

    fn maximum(&self) -> usize {
        self.end.saturating_sub(1)
    }
}

impl Range for core::ops::RangeToInclusive<usize> {
    fn minimum(&self) -> usize {
        0
    }

    fn maximum(&self) -> usize {
        self.end
    }
}

/// An [`Iterator`] over repeated applications of a parser separated by another parser.
///
/// When using the combinators [`separated`], [`try_separated`], and [`collect_separated`],
/// this iterator type is used as the interface into the repeated applications of the
/// provided parser. The [`Iterator::Item`] is the [`Parse::Parsed`] type of the
/// provided parser. The parsed values of the separator parser is discarded by the iterator.
///
/// Note that consuming the iterator is not required. The combinators that use
/// [`SeparatedIter`] will ensure that the iterator is completely consumed if the
/// user does not iterate to the end. A common pattern is to ignore the iterator
/// altogether when the parsed values are not needed. For example,
/// `parser.separated(3.., separator, |_| ())`.
///
/// See [`separated`], [`try_repeated`], and [`collect_repeated`] for examples.
#[derive(Debug)]
pub struct SeparatedIter<'a, P, S, I>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    I: Input,
{
    parser: &'a P,
    separator: &'a S,
    max_count: usize,
    input: &'a mut I,
    count: &'a mut usize,
    error: &'a mut Option<P::Error>,
}

impl<'a, P, S, I> Iterator for SeparatedIter<'a, P, S, I>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    I: Input,
{
    type Item = P::Parsed;

    fn next(&mut self) -> Option<Self::Item> {
        if *self.count >= self.max_count {
            return None;
        }

        let rem = if *self.count > 0 {
            match self.separator.parse(self.input.clone()) {
                Ok(Success(_, rem)) => rem,
                Err(Failure(e, _)) => {
                    *self.error = Some(e);
                    return None;
                }
            }
        } else {
            self.input.clone()
        };

        match self.parser.parse(rem) {
            Ok(Success(ret, rem)) => {
                *self.count += 1;
                *self.input = rem;
                Some(ret)
            }
            Err(Failure(e, _)) => {
                *self.error = Some(e);
                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            0,
            if self.max_count == usize::MAX {
                None
            } else {
                Some(self.max_count)
            },
        )
    }
}

#[derive(Debug, Clone)]
struct TrySeparatedParser<P, S, R, F, E, O, I>(P, S, R, F, PhantomData<fn() -> (O, I)>)
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    R: Range,
    F: for<'a> Fn(SeparatedIter<'a, P, S, I>) -> Result<O, E>,
    I: Input;

impl<P, S, R, F, E, O, I> Parse<I> for TrySeparatedParser<P, S, R, F, E, O, I>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    R: Range,
    F: for<'a> Fn(SeparatedIter<'a, P, S, I>) -> Result<O, E>,
    E: ErrorSeed<I, P::Error>,
    I: Input,
{
    type Parsed = O;
    type Error = P::Error;

    fn parse<N>(&self, input: N) -> PResult<O, I, Self::Error>
    where
        N: IntoInput<Input = I>,
    {
        let mut input = input.into_input();
        let max_count = self.2.maximum();

        let mut count = 0usize;
        let mut err = None;
        let orig_input = input.clone();
        let res = (self.3)(SeparatedIter {
            parser: &self.0,
            separator: &self.1,
            max_count,
            input: &mut input,
            count: &mut count,
            error: &mut err,
        });
        let ret = match res {
            Ok(ret) => ret,
            Err(err) => return Err(Failure(err.into_error(input), orig_input)),
        };

        SeparatedIter {
            parser: &self.0,
            separator: &self.1,
            max_count,
            input: &mut input,
            count: &mut count,
            error: &mut err,
        }
        .for_each(|_| ());

        if count < self.2.minimum() {
            let Some(err) = err else {
                unreachable!();
            };
            Err(Failure(err, orig_input))
        } else {
            Ok(Success(ret, input))
        }
    }
}

/// Creates a parser that is applied repeatedly while interspersed with a separator.
///
/// [`try_separated`] produces a parser that will apply `parser` and `separator`
/// repeatedly, alternatiging between the two. The parsing pattern starts with
/// `parser` and ends with `parser`, such as `parser separator parser`. This is
/// distinct from `pair(parser, separator).try_repeated(...)` as [`try_separated`]
/// will not parse a trailing separator, and a repeated pair must parse a trailing
/// separator.
///
/// The provided `range` determines the minimum and maximum number of repatitions
/// of `parser`. For example if `range` is `3..=5`, `parser` must be able to parse
/// at least 3 times, and up to 5 times. Similarly, `..` corresponds to 0 or more
/// repetitions, and `1..` corresponds to 1 or more. An exact number of repetitions
/// can be specified with a single integer value such as `3` (but `3..=3` is also
/// valid and equivalent). See [`Range`] for more information on ranges.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of an
/// iterator, [`SeparatedIter`]. `collect_fn` then returns a [`Result`], where the
/// [`Ok`] variant becomes the parsed value of the new parser, and the [`Err`]
/// variant becomes an error returned by the new parser via the [`ErrorSeed`] trait.
///
/// Note that the returned new parser does not allocate. Values produced by the
/// iterator are obtained on demand by applying `separator` and `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user provided
/// `collect_fn` allocates when called.
///
/// See also [`Parse::try_separated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::ErrorKind;
/// # use pars::basic::try_separated;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<Vec<char>, &str> {
///     try_separated(
///         unicode::strict::char,
///         ..,
///         unicode::strict::verbatim(","),
///         |iter| -> Result<Vec<char>, ErrorKind> {
///             let mut out = Vec::new();
///             for ch in iter {
///                 if !ch.is_ascii_alphabetic() {
///                     return Err(ErrorKind::InvalidInput);
///                 }
///                 out.push(ch);
///             }
///             Ok(out)
///         }
///     ).parse(input)
/// }
///
/// assert_eq!(
///     my_parser.parse("a,b,c"),
///     Ok(Success(vec!['a', 'b', 'c'], "")),
/// );
///
/// assert_eq!(
///     my_parser.parse("a,b,c,"),
///     Ok(Success(vec!['a', 'b', 'c'], ",")),
/// );
///
/// assert!(my_parser.parse("a,2,c").is_err());
/// ```
#[inline]
pub const fn try_separated<P, S, R, F, E, O, I>(
    parser: P,
    range: R,
    separator: S,
    collect_fn: F,
) -> impl Parse<I, Parsed = O, Error = P::Error>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    R: Range,
    F: for<'a> Fn(SeparatedIter<'a, P, S, I>) -> Result<O, E>,
    E: ErrorSeed<I, P::Error>,
    I: Input,
{
    TrySeparatedParser(parser, separator, range, collect_fn, PhantomData)
}

/// Creates a parser that is applied repeatedly while interspersed with a separator.
///
/// [`separated`] produces a parser that will apply `parser` and `separator`
/// repeatedly, alternatiging between the two. The parsing pattern starts with
/// `parser` and ends with `parser`, such as `parser separator parser`. This is
/// distinct from `pair(parser, separator).repeated(...)` as [`separated`] will
/// not parse a trailing separator, and a repeated pair must parse a trailing
/// separator.
///
/// The provided `range` determines the minimum and maximum number of repatitions
/// of `parser`. For example if `range` is `3..=5`, `parser` must be able to parse
/// at least 3 times, and up to 5 times. Similarly, `..` corresponds to 0 or more
/// repetitions, and `1..` corresponds to 1 or more. An exact number of repetitions
/// can be specified with a single integer value such as `3` (but `3..=3` is also
/// valid and equivalent). See [`Range`] for more information on ranges.
///
/// The values produced by `parser` are passed to `collect_fn` in the form of an
/// iterator, [`SeparatedIter`]. Whatever `collect_fn` returns is the parsed value
/// of the new parser. The values produced by `separator` are discarded.
///
/// Note that the returned new parser does not allocate. Values produced by the
/// iterator are obtained on demand by applying `separator` and `parser` each time
/// [`Iterator::next`] is called. Allocation will only occur if the user provided
/// `collect_fn` allocates when called.
///
/// See also [`Parse::separated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::separated;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<Vec<char>, &str> {
///     separated(
///         unicode::strict::char,
///         ..,
///         unicode::strict::verbatim(","),
///         |iter| {
///             let mut out = Vec::new();
///             for ch in iter {
///                 out.push(ch);
///             }
///             out
///         }
///     ).parse(input)
/// }
///
/// assert_eq!(
///     my_parser.parse("a,b,c"),
///     Ok(Success(vec!['a', 'b', 'c'], "")),
/// );
///
/// assert_eq!(
///     my_parser.parse("a,b,c,"),
///     Ok(Success(vec!['a', 'b', 'c'], ",")),
/// );
/// ```
#[inline]
pub const fn separated<P, S, R, F, O, I>(
    parser: P,
    range: R,
    separator: S,
    collect_fn: F,
) -> impl Parse<I, Parsed = O, Error = P::Error>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    R: Range,
    F: for<'a> Fn(SeparatedIter<'a, P, S, I>) -> O,
    I: Input,
{
    try_separated(
        parser,
        range,
        separator,
        move |iter| -> Result<O, core::convert::Infallible> { Ok(collect_fn(iter)) },
    )
}

/// Creates a parser that is applied repeatedly while interspersed with a separator.
///
/// [`collect_separated`] produces a parser that will apply `parser` and `separator`
/// repeatedly, alternatiging between the two. The parsing pattern starts with
/// `parser` and ends with `parser`, such as `parser separator parser`. This is
/// distinct from `pair(parser, separator).repeated(...)` as [`collect_separated`]
/// will not parse a trailing separator, and a repeated pair must parse a trailing
/// separator.
///
/// The provided `range` determines the minimum and maximum number of repatitions
/// of `parser`. For example if `range` is `3..=5`, `parser` must be able to parse
/// at least 3 times, and up to 5 times. Similarly, `..` corresponds to 0 or more
/// repetitions, and `1..` corresponds to 1 or more. An exact number of repetitions
/// can be specified with a single integer value such as `3` (but `3..=3` is also
/// valid and equivalent). See [`Range`] for more information on ranges.
///
/// The values produced by `parser` are collected via the [`FromIterator`] trait
/// on the, typically inferred, parsed value type of the new parser. The values
/// produced by `separator` are discarded.
///
/// See also [`Parse::collect_separated`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::basic::collect_separated;
/// # use pars::unicode::{self, PResult};
/// fn my_parser(input: &str) -> PResult<Vec<char>, &str> {
///     // Note that `Vec<char>` is inferred from the return type of `my_parser`
///     collect_separated(
///         unicode::strict::char,
///         ..,
///         unicode::strict::verbatim(","),
///     ).parse(input)
/// }
///
/// assert_eq!(
///     my_parser.parse("a,b,c"),
///     Ok(Success(vec!['a', 'b', 'c'], "")),
/// );
///
/// assert_eq!(
///     my_parser.parse("a,b,c,"),
///     Ok(Success(vec!['a', 'b', 'c'], ",")),
/// );
/// ```
#[inline]
pub const fn collect_separated<P, S, R, C, I>(
    parser: P,
    range: R,
    separator: S,
) -> impl Parse<I, Parsed = C, Error = P::Error>
where
    P: Parse<I>,
    S: Parse<I, Error = P::Error>,
    R: Range,
    C: FromIterator<P::Parsed>,
    I: Input,
{
    separated(parser, range, separator, |iter| iter.collect())
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

/// Creates a parser that applies two parsers in sequence.
///
/// [`pair`] produces a parser that applies `first` and `second` in that
/// order. On success, the new parser returns the parsed values returned
/// by `first` and `second` as a tuple. If either parser fails, the
/// corresponding error is returned from the new parser. When `first`
/// fails, `second` is not applied.
///
/// See also [`Parse::then`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::pair;
/// fn my_parser(input: &str) -> PResult<(char, char), &str> {
///     pair(
///         unicode::strict::char,
///         unicode::strict::char,
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("abc"), Ok(Success(('a', 'b'), "c")));
/// assert!(my_parser.parse("a").is_err());
/// assert!(my_parser.parse("").is_err());
/// ```
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

/// Creates a parser that attempts to parse with each of two parsers.
///
/// [`either`] produces a parser that first attempts to apply `first` and
/// then applies `second` if `first` fails. If `first` succeeds, the
/// parsed value `first` returns is returned by the new parser. If `first`
/// fails and then `second` succeeds, the parsed value returned by `second`
/// is returned by the new parser. If both fail, the error returned by
/// `second` is returned.
///
/// See also [`Parse::or`].
///
/// # Example
/// ```
/// # use pars::prelude::*;
/// # use pars::unicode::{self, PResult};
/// # use pars::basic::either;
/// fn my_parser(input: &str) -> PResult<&str, &str> {
///     either(
///         unicode::strict::verbatim("foo").ok_into(),
///         unicode::strict::verbatim("bar").ok_into(),
///     ).parse(input)
/// }
///
/// assert_eq!(my_parser.parse("foobaz"), Ok(Success("foo", "baz")));
/// assert_eq!(my_parser.parse("barbaz"), Ok(Success("bar", "baz")));
/// assert!(my_parser.parse("baz").is_err());
/// ```
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
/// # use pars::basic::err_into;
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
///     err_into(bytes::u8).parse(input)
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
