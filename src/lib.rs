#![no_std]

//! # Parser-combinator library for Rust.
//! `pars` is a general purpose parser-combinator library, with support for `no_std`.
//! `pars` is heavily inspired by [`nom`](https://crates.io/crates/nom), but `pars`
//! aims to generalize more over different kinds of input and provide more
//! Rust-idiomatic and ergonomic combinators. `pars` also provides direct support for
//! higher level concepts such as Unicode and regular expressions.
//!
//! # Contents
//! * [Example](#example) - Jump directly into an example parser implementation
//! * [Parser Combinators](#parser-combinators) - A brief introduction to
//!   parser-combinators
//! * [Parser Input](#parser-input) - An overview of how parseable input works in
//!   `pars`
//! * [Defining a Parser](#defining-a-parser) - How to write your own parser
//! * [Defining a Combinator](#defining-a-combinator) - How to write your own
//!   combinator
//! * [Parsing Errors](#parsing-errors) - The `pars` error system and how to define
//!   your own error types
//! * [Features](#features) - Available crate features
//!
//! # Example
//! ```
//! use pars::prelude::*;
//! use pars::ErrorKind;
//! use pars::unicode::{
//!     strict::{char as uchar, verbatim},
//!     UnicodeInput as UInput, PResult,
//! };
//!
//! #[derive(Debug, PartialEq)]
//! struct Color {
//!     red: u8,
//!     green: u8,
//!     blue: u8,
//! }
//!
//! fn hex_digit<I: UInput>(input: I) -> PResult<u8, I> {
//!     uchar.try_map(|ch| match ch {
//!         '0'..='9' => Ok((ch as u8) - b'0'),
//!         'a'..='f' => Ok((ch as u8) - b'a' + 10),
//!         'A'..='F' => Ok((ch as u8) - b'A' + 10),
//!         _ => Err(ErrorKind::InvalidInput),
//!     }).parse(input)
//! }
//!
//! fn hex_byte<I: UInput>(input: I) -> PResult<u8, I> {
//!     hex_digit.array().map(|[d0, d1]| (d0 << 4) | d1).parse(input)
//! }
//!
//! fn hex_color<I: UInput>(input: I) -> PResult<Color, I> {
//!     prefix(verbatim("#"), hex_byte.array())
//!         .map(|[r, g, b]| Color {
//!             red: r,
//!             green: g,
//!             blue: b,
//!         })
//!         .parse(input)
//! }
//!
//! fn main() {
//!     assert_eq!(
//!         hex_color.parse("#2F14DF"),
//!         Ok(Success(Color {
//!             red: 0x2f,
//!             green: 0x14,
//!             blue: 0xdf,
//!         }, ""))
//!     );
//! }
//! ```
//!
//! # Parser Combinators
//! Classically, parsers are defined as a grammar that parser generators, such as
//! `lex` and `yacc`, will transpile to an implementation of a state machine. This
//! generally produces the most efficient parsers, to be sure. Some popular parser
//! generators for Rust include [`pest`](https://crates.io/crates/pest),
//! [`LALRPOP`](https://crates.io/crates/lalrpop), and
//! [`peg`](https://crates.io/crates/peg).
//!
//! A parser combinator, on the other hand, is generally a library of parser building
//! blocks for building a recursive descent parser. The trade off here is that we
//! gain the ability to write plain Rust (in the case of `pars`) as well the ability
//! to easily reuse parsers to build more complex parsers, but at the costs associated
//! with recursive descent parsers. The downside of recursive descent parsers is that
//! there is no limit to how far back the parser may need to backtrack in the input
//! stream during parsing, and thus are generally not as efficient as parser produced
//! by parser generators. But note that, for example, most practical compilers are
//! implemented with a recursive descent parser because of their power and
//! flexibility, despite not being the most efficient approach. Also note that in
//! some cases, it is possible define a complex parser without any backtracking with
//! a little extra effort. See the example
//! [`msgpack_alt.rs`](https://github.com/Vociferix/pars/blob/master/examples/msgpack_alt.rs)
//! in the crate repo for an example of a parser with no backtracking.
//!
//! # Parser Input
//! In `pars` a parser is defined as a function that accepts a stream of symbols as a
//! parameter, and returns either a parse success or parse failure. A stream of
//! symbols is generalized by the [`Input`] trait. [`Input`] is very similar to the
//! [`Iterator`] trait in the Rust standard library, but it has some extra
//! properties. [`Input`] must also implement [`Clone`], and it must be possible to
//! test whether two [`Input`] objects are at the same stream position. Note that
//! for good performance, the [`Clone`] implementation should be cheap, but it is
//! not required that it implement [`Copy`].
//!
//! [`Input`] is automatically implemented for slice references, `&[T]` and `&str`.
//! To illustrate the properties of an [`Input`] consider `input: &[u8]`. Advancing
//! the input is equivalent to `input = &input[1..]`. Testing that two inputs are
//! at the same position is just testing that the underlying pointers are equal,
//! `input.as_ptr() == other_input.as_ptr()`. Also, `&[u8]` clearly has a cheap
//! [`Clone`] implementation.
//!
//! See the documentation for [`Input`] for more details.
//!
//! `pars` also provides the [`IntoInput`] trait, which is similarly analogous to
//! the [`IntoIterator`] trait in the Rust standard library. The [`Parse::parse`]
//! function accepts a value implementing [`IntoInput`] instead of [`Input`] for
//! the convience of the caller. For example, [`&Vec<u8>`](alloc::vec::Vec),
//! [`&Box<[u8]>`](alloc::boxed::Box), `&[u8; N]` all implement [`IntoIterator`]
//! and will convert to the input type [`&[u8]`]([u8]).
//!
//! See the documentation for [`IntoInput`] for more details.
//!
//! # Defining a Parser
//! Most user defined parsers should be implemented as a plain function. Types
//! implementing [`Fn(I) -> PResult<T, I, E>`](core::ops::Fn), where `I`
//! implements [`Input`] and `E` implements [`Error<I>`] automatically implement
//! [`Parse<I, Parsed = T, Error = E>`](Parse). Closures can also be used to
//! define a parser inline, but note that occaisionally closures may need some
//! type hinting assistance to compile properly as a parser.
//!
//! ```
//! use pars::{Input, PResult, Success, bytes::Error, Parse};
//!
//! // `my_parser` implements `Parse<I, Parsed = i32, Error = Error<I>>`
//! fn my_parser<I: Input>(input: I) -> PResult<i32, I, Error<I>> {
//!     Success(42, input).into()
//! }
//! ```
//!
//! When needed, [`Parse`] can always be implemented manually.
//!
//! # Defining a Combinator
//! Occaisionly, there is a need to implement a custom combinator for reuse. The
//! simplest way is to define a function returning [`impl Parse`](Parse).
//!
//! ```
//! use pars::{basic::array, Input, Parse};
//!
//! // Creates a parser that applies `parser` twice and
//! // returns the parsed values as an array of length 2.
//! const fn twice<I, P>(parser: P)
//!     -> impl Parse<I, Parsed = [P::Parsed; 2], Error = P::Error>
//! where
//!     I: Input,
//!     P: Parse<I>,
//! {
//!     array(parser)
//! }
//! ```
//!
//! It is usually necessary for the [`impl Parse`](Parse) return to explicitly define
//! the [`Parsed`](Parse::Parsed) and [`Error`](Parse::Error) associated types, in
//! order for type inference to work properly in conjunction with other combinators.
//!
//! # Parsing Errors
//! `pars` does not define a general purpose error for parsing failures. Instead, it
//! provides the [`Error`] trait. Users can define their own parsing error types, and
//! `pars` provides a basic error type for each of the modules
//! [`bytes`](./bytes/struct.Error.html), [`ascii`](./ascii/struct.Error.html), and
//! [`unicode`](./unicode/struct.Error.html).
//!
//! A parsing error, aside from other error information it communicates, contains the
//! input position at which the error occurred. The generic parsers and combinators
//! defined throughout `pars` use the interface described by the [`Error`] trait to
//! instantiate an error as needed, also providing where the error occurred. Note
//! that the input position described by an [`Error`] may be different from the input
//! position described by a [`Failure`] within a [`PResult`]. The [`Failure`] always
//! describes the remaining input that has not been successfully parsed, but the
//! error may have occurred further into the input and caused the parser to
//! backtrack.
//!
//! An important partner to the [`Error`] trait is the [`ErrorSeed`] trait.
//! Essentially, a type implementing [`ErrorSeed`] is a parsing error without the
//! accompanying input position of the error. Such a type can be combined with an
//! input position via the [`ErrorSeed`] trait to create an actual error.
//!
//! Many combinators defined in `pars`, particularly those named `try_*`, require the
//! user to provide a function or closure that returns a [`Result`]. The `Err`
//! variant of that [`Result`] must be convertible to an [`Error`] via [`ErrorSeed`].
//! The reason for this is combinators generally abstract away the input stream,
//! letting the user focus more on how parsers fit together and produce a parsed
//! value. When some intermediate operation is fallible, being able to return an
//! [`ErrorSeed`] simplifies matters by letting the combinator implementation deal
//! with tracking input positions.
//!
//! A typical user defined error will be defined as a pair of types: One implementing
//! [`ErrorSeed`] and another implementing [`Error`].
//!
//! ```
//! # use pars::{Input, ErrorSeed, Error};
//! #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! struct MyErrorKind(&'static str);
//!
//! #[derive(Debug, Clone, PartialEq, Eq, Hash)]
//! struct MyError<I: Input> {
//!     msg: &'static str,
//!     pos: I,
//! }
//!
//! impl<I: Input> ErrorSeed<I, MyError<I>> for MyErrorKind {
//!     fn into_error(self, pos: I) -> MyError<I> {
//!         MyError {
//!             msg: self.0,
//!             pos,
//!         }
//!     }
//! }
//!
//! impl<I: Input> Error<I> for MyError<I> {
//!     fn need_more_input(pos: I) -> Self {
//!         MyErrorKind("need more input").into_error(pos)
//!     }
//!
//!     fn expected_eof(pos: I) -> Self {
//!         MyErrorKind("expected end of input").into_error(pos)
//!     }
//!
//!     fn invalid_input(pos: I) -> Self {
//!         MyErrorKind("invalid input").into_error(pos)
//!     }
//!
//!     fn position(&self) -> &I { &self.pos }
//! }
//! ```
//!
//! For convenience, [`ErrorKind`] is available for use as an [`ErrorSeed`] type that
//! can be converted to any type implementing [`Error`].
//!
//! When combining a user defined error with parsers that use a different error type,
//! such as [`bytes::u8`](./bytes/fn.u8.html), there are a few ways this can be dealt with.
//! The simplest way is to use [`basic::into`] (or [`Parse::parse_into`]).
//!
//! ```
//! # use pars::{bytes, Input, ErrorSeed, Error, Parse, PResult};
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! # struct MyErrorKind(&'static str);
//! #
//! # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
//! # struct MyError<I: Input> {
//! #     msg: &'static str,
//! #     pos: I,
//! # }
//! #
//! # impl<I: Input> ErrorSeed<I, MyError<I>> for MyErrorKind {
//! #     fn into_error(self, pos: I) -> MyError<I> {
//! #         MyError {
//! #             msg: self.0,
//! #             pos,
//! #         }
//! #     }
//! # }
//! #
//! # impl<I: Input> Error<I> for MyError<I> {
//! #     fn need_more_input(pos: I) -> Self {
//! #         MyErrorKind("need more input").into_error(pos)
//! #     }
//! #
//! #     fn expected_eof(pos: I) -> Self {
//! #         MyErrorKind("expected end of input").into_error(pos)
//! #     }
//! #
//! #     fn invalid_input(pos: I) -> Self {
//! #         MyErrorKind("invalid input").into_error(pos)
//! #     }
//! #
//! #     fn position(&self) -> &I { &self.pos }
//! # }
//! // Given `MyError` defined previously.
//! impl<I: Input> From<bytes::Error<I>> for MyError<I> {
//!     fn from(err: bytes::Error<I>) -> Self {
//!         match err.kind() {
//!             bytes::ErrorKind::NeedMoreInput => Self::need_more_input(err.position().clone()),
//!             bytes::ErrorKind::ExpectedEof => Self::expected_eof(err.position().clone()),
//!             _ => Self::invalid_input(err.position().clone()),
//!         }
//!     }
//! }
//!
//! fn my_u8<I: bytes::ByteInput>(input: I) -> PResult<u8, I, MyError<I>> {
//!     // Changes `bytes::u8` to return `MyError` instead of `bytes::Error`
//!     bytes::u8.parse_into().parse(input)
//! }
//! ```
//!
//! When relying on a [`From`] implementation doesn't work, [`basic::map_err`],
//! [`basic::map_res`], and [`basic::map_pres`] are also available to define error
//! conversions separately for each instance.
//!
//! # Features
//! Note that there is no `std` feature, since `pars` never makes use of types that are
//! only available in `std`.
//!
//! * `alloc` - Enable usage of the [`alloc`] crate. This enables [`IntoInput`] impls
//! for types such as [`&Vec<[T]>`](alloc::vec::Vec) and
//! [`&String`](alloc::string::String). Enabled by default.
//! * `bytes` - Enable the [`bytes`](./bytes) module, which provides parsers and utilities
//! for byte streams.
//! * `unicode` - Enable the [`unicode`](./unicode) module, which provides parsers and
//! utilities for UTF-8, UTF-16, and UTF-32 streams.
//! * `ascii` - Enable the [`ascii`](./ascii) module, which provides parsers and utilities
//! for ASCII character streams.

#[cfg(any(doc, feature = "alloc"))]
extern crate alloc;

mod input;
mod span;

pub mod basic;

#[cfg(feature = "ascii")]
pub mod ascii;
#[cfg(feature = "bytes")]
pub mod bytes;
#[cfg(feature = "unicode")]
pub mod unicode;

pub use input::*;
pub use span::*;

extern crate self as pars;

/// The `pars` prelude.
pub mod prelude {
    pub use super::basic::{
        alt, constant, delimited, either, eof, error, pair, permutation, pop, prefix, remaining,
        remaining_len, separated, seq, suffix, take,
    };
    pub use super::{
        Error as _, ErrorSeed as _, Failure, Input, IntoInput, PResultExt, Parse, Span, Success,
    };
}

/// A parsing error.
pub trait Error<I: Input>: Sized {
    /// Creates an error representing the need for more input.
    ///
    /// Generic parsers will call this method to generate an error when parsing failed
    /// due to reaching the end of input.
    fn need_more_input(pos: I) -> Self;

    /// Creates an error representing that the end of input was expected but not reached.
    ///
    /// Generic parsers will call this method to generate an error when parsing failed
    /// because it expected to reach the end of the input, but there was more input
    /// available after parsing was finished.
    fn expected_eof(pos: I) -> Self;

    /// Creates an error representing that the input is unparsable.
    ///
    /// Generic parsers will call this method to generate an error when parsing failed
    /// due to a failed verification of a symbol or parsed value.
    fn invalid_input(pos: I) -> Self;

    /// Gets the input position where the error occured.
    fn position(&self) -> &I;
}

/// A parsing error descriptor that can be used to build a parsing error.
///
/// Most types implementing [`ErrorSeed`] are typically an "error kind" `enum. The most
/// generic [`ErrorSeed`] is [`ErrorKind`]. However, an [`ErrorSeed`] type can be
/// anything as long as it can be combined with some [`Input`] to create an [`Error`].
///
/// An [`ErrorSeed`] is generally used in fallible combinators (i.e. any `basic::try_*`
/// combinator) to represent an error with the input stream abstracted away. For
/// example:
/// ```
/// # use pars::{bytes, Parse, ErrorKind};
/// # fn my_parser(input: &[u8]) -> pars::PResult<u8, &[u8], bytes::Error<&[u8]>> {
/// bytes::u8.try_map(|byte| {
///     if byte < 0x80 {
///         Ok(byte)
///     } else {
///         // `try_map` converts this to a `bytes::Error`
///         Err(ErrorKind::InvalidInput)
///     }
/// })
/// # .parse(input)
/// # }
/// ```
///
/// [`ErrorSeed`] is generic over both the input type and error type, so any
/// [`ErrorSeed`] can convert multiple error types if desired. [`ErrorKind`], for
/// example, can convert to any type implementing [`Error`] for any input type.
pub trait ErrorSeed<I: Input, E: Error<I>> {
    /// Combines this error seed with input to create a parsing error.
    fn into_error(self, pos: I) -> E;
}

/// A type implementing [`ErrorSeed`] for all error and input types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ErrorKind {
    /// Converts to an error using [`Error::need_more_input`].
    NeedMoreInput,
    /// Converts to an error using [`Error::expected_eof`].
    ExpectedEof,
    /// Converts to an error using [`Error::invalid_input`].
    InvalidInput,
}

/// Type returned by a parser when parsing succeeds.
///
/// [`Success`] is returned in the [`Ok`] variant of a [`PResult`] to signal that
/// parsing succeeded. [`Success`] is a named tuple containing the parsed value
/// (see [`Parse::Parsed`]) and the remaining unparsed input.
#[derive(Debug, Clone)]
pub struct Success<T, I>(
    /// The parsed value
    pub T,
    /// The remaining unparsed input
    pub I,
);

/// Type returned by a parser when parsing fails.
///
/// [`Failure`] is returned in the [`Err`] variant of a [`PResult`] to signal that
/// parsing failed. [`Failure`] is a named tuple containing the parsing error
/// (see [`Error`] and [`Parse::Error`]) and the input that failed to parse. The
/// input member should always have the same position as the input that was
/// originally provided to the parser - failure to do so is a bug, but not UB.
#[derive(Debug, Clone)]
pub struct Failure<E, I>(
    /// The parsing error
    pub E,
    /// The input that failed to parse
    pub I,
);

/// The [`Result`] type returned by a parser.
///
/// All parsers return either a [`Success`] when parsing succeeds, or a
/// [`Failure`] when parsing fails. The input type that is returned is the same
/// in either case, and is the same type as was provided to the parser to parse.
///
/// Unlike a typical [`Result`] alias in rust, [`PResult`] has three generic
/// parameters: The parsed value type, the input type, and the error type. Since
/// this differs from the standard convention, the alias has a slightly different
/// name to clearly indicate the break from convention.
pub type PResult<T, I, E> = Result<Success<T, I>, Failure<E, I>>;

/// Trait implemented by all parsers.
///
/// The [`Parse`] trait is where the logic of parsing is implemented. However,
/// most `pars` users will not implement [`Parse`] directly. See the crate level
/// documentation for examples of user defined parsers.
pub trait Parse<I: Input>: Sized {
    /// The value type that is produced by the parser on success.
    type Parsed: Sized;

    /// The error type that is produced by the parser on failure.
    type Error: Error<I>;

    /// Parses the provided input.
    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>;

    #[inline]
    fn map<F, R>(self, map_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        F: Fn(Self::Parsed) -> R,
    {
        basic::map(self, map_fn)
    }

    #[inline]
    fn try_map<F, R, S>(self, map_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        S: ErrorSeed<I, Self::Error>,
        F: Fn(Self::Parsed) -> Result<R, S>,
    {
        basic::try_map(self, map_fn)
    }

    #[inline]
    fn map_err<F, R>(self, map_err_fn: F) -> impl Parse<I, Parsed = Self::Parsed, Error = R>
    where
        F: Fn(Self::Error) -> R,
        R: Error<I>,
    {
        basic::map_err(self, map_err_fn)
    }

    #[inline]
    fn map_res<F, R, E>(self, map_res_fn: F) -> impl Parse<I, Parsed = R, Error = E>
    where
        F: Fn(Result<Self::Parsed, Self::Error>) -> Result<R, E>,
        E: Error<I>,
    {
        basic::map_res(self, map_res_fn)
    }

    #[inline]
    fn map_pres<F, R, E>(self, map_pres_fn: F) -> impl Parse<I, Parsed = R, Error = E>
    where
        F: Fn(PResult<Self::Parsed, I, Self::Error>) -> PResult<R, I, E>,
        E: Error<I>,
    {
        basic::map_pres(self, map_pres_fn)
    }

    #[inline]
    fn parse_into<R, E>(self) -> impl Parse<I, Parsed = R, Error = E>
    where
        R: From<Self::Parsed>,
        E: Error<I> + From<Self::Error>,
    {
        basic::into(self)
    }

    #[inline]
    fn with<F, T>(self, with_fn: F) -> impl Parse<I, Parsed = T, Error = Self::Error>
    where
        F: Fn() -> T,
    {
        basic::with(self, with_fn)
    }

    #[inline]
    fn with_default<T>(self) -> impl Parse<I, Parsed = T, Error = Self::Error>
    where
        T: Default,
    {
        basic::with_default(self)
    }

    #[inline]
    fn with_value<T>(self, value: T) -> impl Parse<I, Parsed = T, Error = Self::Error>
    where
        T: Clone,
    {
        basic::with_value(self, value)
    }

    #[inline]
    fn flat_map<F, P>(self, combinator: F) -> impl Parse<I, Parsed = P::Parsed, Error = Self::Error>
    where
        F: Fn(Self::Parsed) -> P,
        P: Parse<I, Error = Self::Error>,
    {
        basic::flat_map(self, combinator)
    }

    #[inline]
    fn try_flat_map<F, P, S>(
        self,
        combinator: F,
    ) -> impl Parse<I, Parsed = P::Parsed, Error = Self::Error>
    where
        S: ErrorSeed<I, Self::Error>,
        F: Fn(Self::Parsed) -> Result<P, S>,
        P: Parse<I, Error = Self::Error>,
    {
        basic::try_flat_map(self, combinator)
    }

    #[inline]
    fn or_value(
        self,
        value: Self::Parsed,
    ) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self::Parsed: Clone,
    {
        basic::or_value(self, value)
    }

    #[inline]
    fn or_default(self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self::Parsed: Default,
    {
        basic::or_default(self)
    }

    #[inline]
    fn or_else<F>(self, or_else_fn: F) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        F: Fn() -> Self::Parsed,
    {
        basic::or_else(self, or_else_fn)
    }

    #[inline]
    fn many0<F, R>(self, collect_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        F: for<'a> Fn(basic::Many0Iter<'a, Self, I>) -> R,
    {
        basic::many0(self, collect_fn)
    }

    #[inline]
    fn try_many0<F, R, S>(self, collect_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        S: ErrorSeed<I, Self::Error>,
        F: for<'a> Fn(basic::Many0Iter<'a, Self, I>) -> Result<R, S>,
    {
        basic::try_many0(self, collect_fn)
    }

    #[inline]
    fn collect_many0<R>(self) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        R: FromIterator<Self::Parsed>,
    {
        basic::collect_many0(self)
    }

    #[inline]
    fn many1<F, R>(self, collect_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        F: for<'a> Fn(basic::Many1Iter<'a, Self, I>) -> R,
    {
        basic::many1(self, collect_fn)
    }

    #[inline]
    fn try_many1<F, R, S>(self, collect_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        S: ErrorSeed<I, Self::Error>,
        F: for<'a> Fn(basic::Many1Iter<'a, Self, I>) -> Result<R, S>,
    {
        basic::try_many1(self, collect_fn)
    }

    #[inline]
    fn collect_many1<R>(self) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        R: FromIterator<Self::Parsed>,
    {
        basic::collect_many1(self)
    }

    #[inline]
    fn repeated<F, R>(
        self,
        count: usize,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        F: for<'a> Fn(basic::RepeatedIter<'a, Self, I>) -> R,
    {
        basic::repeated(self, count, collect_fn)
    }

    #[inline]
    fn try_repeated<F, R, S>(
        self,
        count: usize,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        S: ErrorSeed<I, Self::Error>,
        F: for<'a> Fn(basic::RepeatedIter<'a, Self, I>) -> Result<R, S>,
    {
        basic::try_repeated(self, count, collect_fn)
    }

    #[inline]
    fn collect_repeated<R>(self, count: usize) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        R: FromIterator<Self::Parsed>,
    {
        basic::collect_repeated(self, count)
    }

    #[inline]
    fn many_until<P, F, R>(
        self,
        sentinel: P,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = (R, P::Parsed), Error = Self::Error>
    where
        P: Parse<I, Error = Self::Error>,
        F: for<'a> Fn(basic::ManyUntilIter<'a, Self, P, I>) -> R,
    {
        basic::many_until(self, sentinel, collect_fn)
    }

    #[inline]
    fn try_many_until<P, F, R, S>(
        self,
        sentinel: P,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = (R, P::Parsed), Error = Self::Error>
    where
        S: ErrorSeed<I, Self::Error>,
        P: Parse<I, Error = Self::Error>,
        F: for<'a> Fn(basic::ManyUntilIter<'a, Self, P, I>) -> Result<R, S>,
    {
        basic::try_many_until(self, sentinel, collect_fn)
    }

    #[inline]
    fn collect_many_until<P, R>(
        self,
        sentinel: P,
    ) -> impl Parse<I, Parsed = (R, P::Parsed), Error = Self::Error>
    where
        P: Parse<I, Error = Self::Error>,
        R: FromIterator<Self::Parsed>,
    {
        basic::collect_many_until(self, sentinel)
    }

    #[inline]
    fn many<N, F, R>(
        self,
        range: N,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        N: core::ops::RangeBounds<usize>,
        F: for<'a> Fn(basic::ManyIter<'a, Self, I>) -> R,
    {
        basic::many(self, range, collect_fn)
    }

    #[inline]
    fn try_many<N, F, R, S>(
        self,
        range: N,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        N: core::ops::RangeBounds<usize>,
        S: ErrorSeed<I, Self::Error>,
        F: for<'a> Fn(basic::ManyIter<'a, Self, I>) -> Result<R, S>,
    {
        basic::try_many(self, range, collect_fn)
    }

    #[inline]
    fn collect_many<N, R>(self, range: N) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        N: core::ops::RangeBounds<usize>,
        R: FromIterator<Self::Parsed>,
    {
        basic::collect_many(self, range)
    }

    #[inline]
    fn array<const LEN: usize>(
        self,
    ) -> impl Parse<I, Parsed = [Self::Parsed; LEN], Error = Self::Error> {
        basic::array(self)
    }

    #[inline]
    fn complete(self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error> {
        basic::complete(self)
    }

    #[inline]
    fn spanned(self) -> impl Parse<I, Parsed = (Self::Parsed, Span<I>), Error = Self::Error> {
        basic::spanned(self)
    }

    #[inline]
    fn recognize(self) -> impl Parse<I, Parsed = Span<I>, Error = Self::Error> {
        basic::recognize(self)
    }

    #[inline]
    fn cond(
        self,
        condition: bool,
    ) -> impl Parse<I, Parsed = Option<Self::Parsed>, Error = Self::Error> {
        basic::cond(self, condition)
    }

    #[inline]
    fn verify<F>(self, verify_fn: F) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        F: Fn(&Self::Parsed) -> bool,
    {
        basic::verify(self, verify_fn)
    }

    #[inline]
    fn not(self) -> impl Parse<I, Parsed = (), Error = Self::Error> {
        basic::not(self)
    }

    #[inline]
    fn opt(self) -> impl Parse<I, Parsed = Option<Self::Parsed>, Error = Self::Error> {
        basic::opt(self)
    }

    #[inline]
    fn peek(self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error> {
        basic::peek(self)
    }

    #[inline]
    fn parse_as_ref<'a>(&'a self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error> + 'a
    where
        I: 'a,
    {
        basic::as_ref(self)
    }

    #[inline]
    fn then<P>(
        self,
        other: P,
    ) -> impl Parse<I, Parsed = (Self::Parsed, P::Parsed), Error = Self::Error>
    where
        P: Parse<I, Error = Self::Error>,
    {
        basic::pair(self, other)
    }

    #[inline]
    fn or<P>(self, other: P) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        P: Parse<I, Parsed = Self::Parsed, Error = Self::Error>,
    {
        basic::either(self, other)
    }
}

mod sealed {
    use super::{Error, Input, PResult};

    pub trait Sealed {}

    impl<T, I: Input, E: Error<I>> Sealed for PResult<T, I, E> {}
}

/// Additional convenience methods for [`PResult`].
pub trait PResultExt: sealed::Sealed {
    type Parsed;
    type Error: Error<Self::Input>;
    type Input: Input;

    fn success(parsed: Self::Parsed, rem: Self::Input) -> Self;

    fn failure(error: Self::Error, rem: Self::Input) -> Self;

    fn remaining(&self) -> &Self::Input;

    fn remaining_mut(&mut self) -> &mut Self::Input;

    fn parsed(&self) -> Option<&Self::Parsed>;

    fn parsed_mut(&mut self) -> Option<&mut Self::Parsed>;

    fn extract(self) -> (Result<Self::Parsed, Self::Error>, Self::Input);

    fn map_parsed<F, R>(self, map_fn: F) -> PResult<R, Self::Input, Self::Error>
    where
        F: FnOnce(Self::Parsed) -> R;
}

impl<T, I: Input, E: Error<I>> PResultExt for PResult<T, I, E> {
    type Parsed = T;
    type Error = E;
    type Input = I;

    fn success(parsed: T, rem: I) -> Self {
        Ok(Success(parsed, rem))
    }

    fn failure(error: E, rem: I) -> Self {
        Err(Failure(error, rem))
    }

    fn remaining(&self) -> &I {
        match self {
            Ok(Success(_, rem)) => rem,
            Err(Failure(_, rem)) => rem,
        }
    }

    fn remaining_mut(&mut self) -> &mut I {
        match self {
            Ok(succ) => &mut succ.1,
            Err(fail) => &mut fail.1,
        }
    }

    fn parsed(&self) -> Option<&Self::Parsed> {
        if let Ok(Success(val, _)) = self {
            Some(val)
        } else {
            None
        }
    }

    fn parsed_mut(&mut self) -> Option<&mut Self::Parsed> {
        if let Ok(succ) = self {
            Some(&mut succ.0)
        } else {
            None
        }
    }

    fn extract(self) -> (Result<T, E>, I) {
        match self {
            Ok(Success(val, rem)) => (Ok(val), rem),
            Err(Failure(err, rem)) => (Err(err), rem),
        }
    }

    fn map_parsed<F, R>(self, map_fn: F) -> PResult<R, I, E>
    where
        F: FnOnce(Self::Parsed) -> R,
    {
        self.map(move |succ| succ.map(map_fn))
    }
}

impl<F, T, I, E> Parse<I> for F
where
    F: Fn(I) -> PResult<T, I, E>,
    I: Input,
    E: Error<I>,
{
    type Parsed = T;
    type Error = E;

    fn parse<N>(&self, input: N) -> PResult<T, I, E>
    where
        N: IntoInput<Input = I>,
    {
        (*self)(input.into_input())
    }
}

impl<T, I: Input> Success<T, I> {
    pub fn map<F, R>(self, map_fn: F) -> Success<R, I>
    where
        F: FnOnce(T) -> R,
    {
        let Success(val, rem) = self;
        Success(map_fn(val), rem)
    }
}

impl<T, I> From<Success<T, I>> for (T, I) {
    fn from(Success(t, i): Success<T, I>) -> (T, I) {
        (t, i)
    }
}

impl<T, I> From<(T, I)> for Success<T, I> {
    fn from((t, i): (T, I)) -> Self {
        Self(t, i)
    }
}

impl<T, U: From<T>, I: Input, E: Error<I>> From<Success<T, I>> for PResult<U, I, E> {
    fn from(Success(val, rem): Success<T, I>) -> Self {
        Ok(Success(U::from(val), rem))
    }
}

impl<T, I> From<Failure<T, I>> for (T, I) {
    fn from(Failure(t, i): Failure<T, I>) -> (T, I) {
        (t, i)
    }
}

impl<T, I> From<(T, I)> for Failure<T, I> {
    fn from((t, i): (T, I)) -> Self {
        Self(t, i)
    }
}

impl<T, I: Input, E: Error<I>, U: Error<I> + From<E>> From<Failure<E, I>> for PResult<T, I, U> {
    fn from(Failure(err, rem): Failure<E, I>) -> Self {
        Err(Failure(U::from(err), rem))
    }
}

impl<I: Input, E: Error<I>> ErrorSeed<I, E> for ErrorKind {
    fn into_error(self, pos: I) -> E {
        match self {
            Self::NeedMoreInput => E::need_more_input(pos),
            Self::ExpectedEof => E::expected_eof(pos),
            Self::InvalidInput => E::invalid_input(pos),
        }
    }
}

impl<LT, LI, RT, RI> PartialEq<Success<RT, RI>> for Success<LT, LI>
where
    LT: PartialEq<RT>,
    LI: PartialEq<RI>,
{
    fn eq(&self, other: &Success<RT, RI>) -> bool {
        PartialEq::eq(&self.0, &other.0) && PartialEq::eq(&self.1, &other.1)
    }
}

impl<T, I> Eq for Success<T, I>
where
    T: Eq,
    I: Eq,
{
}

impl<LE, LI, RE, RI> PartialEq<Failure<RE, RI>> for Failure<LE, LI>
where
    LE: PartialEq<RE>,
    LI: PartialEq<RI>,
{
    fn eq(&self, other: &Failure<RE, RI>) -> bool {
        PartialEq::eq(&self.0, &other.0) && PartialEq::eq(&self.1, &other.1)
    }
}

impl<T, I> Eq for Failure<T, I>
where
    T: Eq,
    I: Eq,
{
}
