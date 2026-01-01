#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]

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
//! Since [`Input`] does not have any constraints on what a "symbol" can be, `pars`
//! can be adapted to consume pretty much any kind of input stream. For example, in
//! some cases it might be desirable to build a lexer (or scanner) to interpret the
//! source input as a stream of tokens, and parse the token stream with `pars`
//! instead of the source input. Sufficiently complex parsers, such as compiler
//! frontends, generally prefer this approach. The lexer just needs to provide an
//! interface with a type that implements [`Input`]. Note that it will usually
//! be necessary for the lexer (or whatever the custom input source is) to be
//! "multi-pass" in order to support parser backtracking.
//!
//! TODO: Include a custom input example.
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
//! The simplest way is to use [`Parse::err_into`].
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
//!     bytes::u8.err_into().parse(input)
//! }
//! ```
//!
//! When relying on a [`From`] implementation doesn't work [`Parse::map_err`] and
//! [`Parse::map_res`] are also available to define error conversions separately for each
//! instance.
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
        remaining_len, separated_pair, seq, suffix, take,
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
/// An [`ErrorSeed`] is generally used in fallible combinators (i.e. any `Parse::try_*`
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
pub trait Parse<I: Input> {
    /// The value type that is produced by the parser on success.
    type Parsed: Sized;

    /// The error type that is produced by the parser on failure.
    type Error: Error<I>;

    /// Parses the provided input.
    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I, Self::Error>
    where
        N: IntoInput<Input = I>;

    /// Creates a parser whose parsed result is transformed.
    ///
    /// The provided function, `map_fn`, is applied to the parsed result of
    /// `self` if it parses successfully. The value returned from `map_fn`
    /// is the parsed result of the new parser.
    ///
    /// If the the mapping operation could fail, use [`Parse::try_map`]
    /// instead.
    ///
    /// See also [`basic::map`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn inv_byte(input: &[u8]) -> PResult<u8, &[u8]> {
    ///     bytes::u8.map(|byte| !byte).parse(input)
    /// }
    ///
    /// assert_eq!(inv_byte.parse(b"\x0f").unwrap().0, 0xf0);
    /// ```
    #[inline]
    fn map<F, R>(self, map_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        F: Fn(Self::Parsed) -> R,
    {
        basic::map(self, map_fn)
    }

    /// Creates a parser whose parsed result is fallibly transformed.
    ///
    /// The provided function, `map_fn`, is applied to the parsed result of
    /// `self` if it parses successfully. `map_fn` is permitted to fail,
    /// which is signaled with an [`Err`] return value. In thise case the
    /// new parser fails, and the contained error is converted to an
    /// [`Error`] via [`ErrorSeed`]. If an [`Ok`] value is returned, the
    /// contained value becomes the parsed result of the new parser.
    ///
    /// If the mapping function cannot fail, use [`Parse::map`] instead.
    ///
    /// See also [`basic::try_map`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// # use pars::ErrorKind;
    /// fn inv_byte(input: &[u8]) -> PResult<u8, &[u8]> {
    ///     bytes::u8.try_map(|byte| {
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
    fn try_map<F, R, S>(self, map_fn: F) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        S: ErrorSeed<I, Self::Error>,
        F: Fn(Self::Parsed) -> Result<R, S>,
    {
        basic::try_map(self, map_fn)
    }

    /// Creates a parser that transforms a parsing error.
    ///
    /// The provided function, `map_err_fn`, is applied the parsing error of
    /// `self` if its parsing fails. The value returned from `map_err_fn`
    /// becomes the parsing error of the new parser. Otherwise, if `self`
    /// succeeds, its parsed result is the parsed result of the new parser.
    ///
    /// This combinator is most useful for converting between error types.
    ///
    /// See also [`basic::map_err`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::{bytes, unicode, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<u8, &[u8], unicode::Error<&[u8]>> {
    ///     bytes::u8.map_err(|err: bytes::Error<&[u8]>| {
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
    fn map_err<F, R>(self, map_err_fn: F) -> impl Parse<I, Parsed = Self::Parsed, Error = R>
    where
        Self: Sized,
        F: Fn(Self::Error) -> R,
        R: Error<I>,
    {
        basic::map_err(self, map_err_fn)
    }

    /// Creates a parser whose result is transformed.
    ///
    /// The provided function, `map_res_fn`, accepts a [`Result`] containing either the
    /// successfully parsed value of `self` or the parsing error returned by `self`.
    /// `map_res_fn` then returns a new [`Result`], which will contain either the new
    /// successful parsed value or a new parsing error.
    ///
    /// Unlike [`Parse::map`] or [`Parse::map_err`], the mapping function may choose to
    /// convert an [`Ok`] into and [`Err`] or an [`Err`] into an [`Ok`].
    ///
    /// See also [`basic::map_res`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult, Error, ErrorKind};
    /// fn my_parser(input: &[u8]) -> PResult<u8, &[u8]> {
    ///     bytes::u8.map_res(|res| match res {
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
    fn map_res<F, R, E>(self, map_res_fn: F) -> impl Parse<I, Parsed = R, Error = E>
    where
        Self: Sized,
        F: Fn(Result<Self::Parsed, Self::Error>) -> Result<R, E>,
        E: Error<I>,
    {
        basic::map_res(self, map_res_fn)
    }

    /// Creates a parser whose parsed result or parsing error are converted via [`Into`].
    ///
    /// If `self` parses successfully, its result value is converted to `R` using the
    /// [`Into<R>`] trait. If `self` fails, the returned parsing error is converted to
    /// `E` using the [`Into<E>`] trait.
    ///
    /// See also [`basic::res_into`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::{PResult, Error};
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
    ///     bytes::u8.array::<5>().res_into().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"hello world") == Ok(Success(Vec::from(b"hello"), b" world")));
    /// assert!(my_parser.parse(b"hi") == Err(Failure(MyError(b""), b"hi")));
    /// ```
    #[inline]
    fn res_into<R, E>(self) -> impl Parse<I, Parsed = R, Error = E>
    where
        Self: Sized,
        Self::Parsed: Into<R>,
        Self::Error: Into<E>,
        E: Error<I>,
    {
        basic::res_into(self)
    }

    /// Creates a parser whose parsed result is converted via [`Into`].
    ///
    /// If `self` parses successfully, its result value is converted to `R` using the
    /// [`Into<R>`] trait.
    ///
    /// See also [`basic::ok_into`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<Vec<u8>, &[u8]> {
    ///     bytes::u8.array::<5>().ok_into().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"hello world") == Ok(Success(Vec::from(b"hello"), b" world")));
    /// ```
    #[inline]
    fn ok_into<R>(self) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        Self::Parsed: Into<R>,
    {
        basic::ok_into(self)
    }

    /// Creates a parser whose parsing error is converted via [`Into`].
    ///
    /// If `slef` fails to parse, the returned parsing error is converted to
    /// `E` using the [`Into<E>`] trait.
    ///
    /// See also [`basic::err_into`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::{PResult, Error};
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
    ///     bytes::u8.err_into().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"hello") == Ok(Success(b'h', b"ello")));
    /// assert!(my_parser.parse(b"") == Err(Failure(MyError(b""), b"")));
    #[inline]
    fn err_into<E>(self) -> impl Parse<I, Parsed = Self::Parsed, Error = E>
    where
        Self: Sized,
        Self::Error: Into<E>,
        E: Error<I>,
    {
        basic::err_into(self)
    }

    /// Creates a parser whose parsed result is converted via [`TryInto`].
    ///
    /// If `self` parses successfully, its result value is converted to `R` using the
    /// [`TryInto<R>`] trait. If [`TryInto`] fails, a parsing error is returned by
    /// calling [`E::invalid_input`](Error::invalid_input). If `self` returns a parsing
    /// error, that error is converted to `E` using the [`Into<E>`] trait.
    ///
    /// Note that the parsing error is not converted using [`TryInto`], but rather the
    /// infallible [`Into`] trait. Only the successfully parsed result converts via
    /// [`TryInto`].
    ///
    /// See also [`basic::res_try_into`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::{PResult, Error};
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
    ///     bytes::be::u32.res_try_into().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x00\x00\x00hello") == Ok(Success('h', b"ello")));
    /// assert!(my_parser.parse(b"\xff\xff\xffhello")
    ///     == Err(Failure(MyError(b"\xff\xff\xffhello"), b"\xff\xff\xffhello")));
    /// assert!(my_parser.parse(b"") == Err(Failure(MyError(b""), b"")));
    /// ```
    #[inline]
    fn res_try_into<R, E>(self) -> impl Parse<I, Parsed = R, Error = E>
    where
        Self: Sized,
        Self::Parsed: core::convert::TryInto<R>,
        Self::Error: Into<E>,
        E: Error<I>,
    {
        basic::res_try_into(self)
    }

    /// Creates a parser whose parsed result is converted via [`TryInto`].
    ///
    /// If `self` parses successfully, its result value is converted to `R` using the
    /// [`TryInto<R>`] trait. If [`TryInto`] fails, a parsing error is returned by calling
    /// [`Error::invalid_input`].
    ///
    /// See also [`basic::ok_try_into`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<char, &[u8]> {
    ///     bytes::be::u32.ok_try_into().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x00\x00\x00hello") == Ok(Success('h', b"ello")));
    /// assert!(my_parser.parse(b"\xff\xff\xffhello").is_err());
    /// ```
    #[inline]
    fn ok_try_into<R>(self) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        Self::Parsed: core::convert::TryInto<R>,
    {
        basic::ok_try_into(self)
    }

    /// Converts a parser to produce a different return value.
    ///
    /// If `self` parses successfully, its returned value is immediately dropped.
    /// `with_fn` is then called to produce the new value. If `self` fails,
    /// `with_fn` is not called.
    ///
    /// See also [`basic::with`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
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
    ///     verbatim("BEGIN").with(|| Token::Begin).parse(input)
    /// }
    ///
    /// fn end(input: &str) -> PResult<Token, &str> {
    ///     verbatim("END").with(|| Token::End).parse(input)
    /// }
    ///
    /// assert_eq!(begin.parse("BEGIN hello"), Ok(Success(Token::Begin, " hello")));
    /// assert_eq!(end.parse("END world"), Ok(Success(Token::End, " world")));
    /// ```
    #[inline]
    fn with<F, T>(self, with_fn: F) -> impl Parse<I, Parsed = T, Error = Self::Error>
    where
        Self: Sized,
        F: Fn() -> T,
    {
        basic::with(self, with_fn)
    }

    /// Converts a parser to produce a different return value, via [`Default`].
    ///
    /// If `self` parses successfully, its returned value is immediately dropped.
    /// The old returned value is replaced with a value of type `T`, produced by
    /// calling [`Default::default()`].
    ///
    /// `parser.with_default()` is equivalent to `parser.with(Default::default)`
    /// (see [`Parse::with`]).
    ///
    /// See also [`Parse::with_default`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::PResult;
    /// use pars::unicode::strict::verbatim;
    ///
    /// #[derive(Debug, PartialEq, Default)]
    /// struct Token;
    ///
    /// fn token(input: &str) -> PResult<Token, &str> {
    ///     verbatim("TOKEN").with_default().parse(input)
    /// }
    ///
    /// assert_eq!(token.parse("TOKEN"), Ok(Success(Token, "")));
    /// ```
    #[inline]
    fn with_default<T>(self) -> impl Parse<I, Parsed = T, Error = Self::Error>
    where
        Self: Sized,
        T: Default,
    {
        basic::with_default(self)
    }

    /// Converts a parser to produce a different return value, via [`Clone`].
    ///
    /// If `self` parses successfully, its returned value is immediately dropped.
    /// `value` is is cloned to replace the returned value.
    ///
    /// See also [`basic::with_value`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::PResult;
    /// use pars::unicode::strict::verbatim;
    ///
    /// #[derive(Debug, PartialEq, Clone)]
    /// struct Token;
    ///
    /// fn token(input: &str) -> PResult<Token, &str> {
    ///     verbatim("TOKEN").with_value(Token).parse(input)
    /// }
    ///
    /// assert_eq!(token.parse("TOKEN"), Ok(Success(Token, "")));
    /// ```
    #[inline]
    fn with_value<T>(self, value: T) -> impl Parse<I, Parsed = T, Error = Self::Error>
    where
        Self: Sized,
        T: Clone,
    {
        basic::with_value(self, value)
    }

    /// Maps the result of a parser onto a combinator to produce a new parser.
    ///
    /// If `self` parses successfully, the result value is passed into
    /// `combinator`. The remaining input after `self` succeeds is then
    /// parsed by the parser returned by `combinator`.
    ///
    /// Generally, this combinator is useful for building a parser that should
    /// parse differently depending on information earlier in the input stream.
    ///
    /// See also [`basic::flat_map`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// // First byte is the length of the string, then that many
    /// // more bytes is the string data.
    /// fn pascal_str(input: &[u8]) -> PResult<&[u8], &[u8]> {
    ///     bytes::u8.ok_into().flat_map(take).ok_into().parse(input)
    /// }
    ///
    /// assert!(pascal_str.parse(b"\x05hello") == Ok(Success(b"hello", b"")));
    /// assert!(pascal_str.parse(b"\x05hi").is_err());
    /// ```
    #[inline]
    fn flat_map<F, P>(self, combinator: F) -> impl Parse<I, Parsed = P::Parsed, Error = Self::Error>
    where
        Self: Sized,
        F: Fn(Self::Parsed) -> P,
        P: Parse<I, Error = Self::Error>,
    {
        basic::flat_map(self, combinator)
    }

    /// Maps the result of a parser onto a combinator to produce a new parser.
    ///
    /// If `self` parses successfully, the result value is passed into
    /// `combinator`. `combinator` then returns a [`Result`] containing either
    /// a new parser or an error implementing [`ErrorSeed`]. If a parser is
    /// returned, the remaining input from `self` is passed to the new
    /// parser. Otherwise, the error is converted to a parsing error and
    /// returned.
    ///
    /// See also [`basic::try_flat_map`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::basic::try_flat_map;
    /// # use pars::bytes::{self, PResult, ErrorKind};
    /// fn my_parser(input: &[u8]) -> PResult<&[u8], &[u8]> {
    ///     bytes::u8.try_flat_map(|value| {
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
    fn try_flat_map<F, P, S>(
        self,
        combinator: F,
    ) -> impl Parse<I, Parsed = P::Parsed, Error = Self::Error>
    where
        Self: Sized,
        S: ErrorSeed<I, Self::Error>,
        F: Fn(Self::Parsed) -> Result<P, S>,
        P: Parse<I, Error = Self::Error>,
    {
        basic::try_flat_map(self, combinator)
    }

    /// Creates a parser that returns a fallback value instead of an error.
    ///
    /// If `self` fails to parse, `value` is cloned and returned as a success
    /// value. The new parser will never return a parsing error.
    ///
    /// See also [`basic::or_value`]
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<char, &str> {
    ///     unicode::strict::char.or_value('\0').parse(input)
    /// }
    ///
    /// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
    /// assert_eq!(my_parser.parse(""), Ok(Success('\0', "")));
    /// ```
    #[inline]
    fn or_value(
        self,
        value: Self::Parsed,
    ) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
        Self::Parsed: Clone,
    {
        basic::or_value(self, value)
    }

    /// Creates a parser that returns a fallback value instead of an error.
    ///
    /// If `self` fails to parse, a default value is returned by calling
    /// [`Default::default`] instead of returning the error. The new parser
    /// will never return a parsing error.
    ///
    /// See also [`basic::or_default`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<char, &str> {
    ///     unicode::strict::char.or_default().parse(input)
    /// }
    ///
    /// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
    /// assert_eq!(my_parser.parse(""), Ok(Success('\0', "")));
    /// ```
    #[inline]
    fn or_default(self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
        Self::Parsed: Default,
    {
        basic::or_default(self)
    }

    /// Creates a parser that returns a fallback value instead of an error.
    ///
    /// If `self` fails to parse, `or_else_fn` is called and its return value
    /// is returned as a success value. The new parser will never return a
    /// parsing error.
    ///
    /// See also [`basic::or_else`]
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<char, &str> {
    ///     unicode::strict::char.or_else(|| '\0').parse(input)
    /// }
    ///
    /// assert_eq!(my_parser.parse("hello"), Ok(Success('h', "ello")));
    /// assert_eq!(my_parser.parse(""), Ok(Success('\0', "")));
    /// ```
    #[inline]
    fn or_else<F>(self, or_else_fn: F) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
        F: Fn() -> Self::Parsed,
    {
        basic::or_else(self, or_else_fn)
    }

    /// Creates a parser that is repeated until a sentinel is parsed.
    ///
    /// [`Parse::repeated_until`] produces a parser that will apply `self` repeatedly
    /// until `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it
    /// fails, `self` is applied before trying `sentinel_parser` again. If
    /// `sentinel_parser` succeeds, parsing is complete.
    ///
    /// The values produced by `self` are passed to `collect_fn` in the form of an
    /// iterator, [`RepeatedUntilIter`](basic::RepeatedUntilIter). The value returned
    /// by `collect_fn` and the parsed value from `sentinel_parser` together as a
    /// 2-tuple become the parsed result of the overall new parser. If `parser`
    /// returns a parsing error at any point, a parsing error is returned from the
    /// overall new parser.
    ///
    /// Note that the returned new parser does not allocate. Values produced by
    /// the iterator are obtained on demand by applying `self` each time
    /// [`Iterator::next`] is called. Allocation will only occur if the user
    /// provided function `collect_fn` allocates to produce its result.
    ///
    /// See also [`basic::repeated_until`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn c_str_len(input: &[u8]) -> PResult<usize, &[u8]> {
    ///     bytes::u8.repeated_until(bytes::verbatim(b"\x00"), |iter| iter.count())
    ///         .map(|(len, _)| len) // we only want the length
    ///         .parse(input)
    /// }
    ///
    /// assert!(c_str_len.parse(b"hello\x00world") == Ok(Success(5, b"world")));
    /// assert!(c_str_len.parse(b"\x00") == Ok(Success(0, b"")));
    /// assert!(c_str_len.parse(b"hello").is_err());
    /// ```
    #[inline]
    fn repeated_until<P, F, R>(
        self,
        sentinel: P,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = (R, P::Parsed), Error = Self::Error>
    where
        Self: Sized,
        P: Parse<I, Error = Self::Error>,
        F: for<'a> Fn(basic::RepeatedUntilIter<'a, Self, P, I>) -> R,
    {
        basic::repeated_until(self, sentinel, collect_fn)
    }

    /// Creates a parser that is repeated until a sentinel is parsed.
    ///
    /// [`Parse::try_repeated_until`] produces a parser that will apply `self` repeatedly
    /// until `sentinel_parser` succeeds. That is, `sentinel_parser` is applied; if it fails,
    /// `self` is applied before trying `sentinel_parser` again. If `sentinel_parser`
    /// succeeds, parsing is complete.
    ///
    /// The values produced by `self` are passed to `collect_fn` in the form of an
    /// iterator, [`RepeatedUntilIter`](basic::RepeatedUntilIter). If `collect_fn` returns
    /// an [`Ok`] value, that and the value from `sentinel_parser` together as a 2-tuple
    /// become the parsed result of the overall new parser. If `collect_fn` returns an
    /// [`Err`], a parsing error is returned. If `self` returns a parsing error at any point,
    /// a parsing error is returned form the overall new parser.
    ///
    /// Note that the returned new parser does not allocate. Values produced by
    /// the iterator are obtained on demand by applying `self` each time
    /// [`Iterator::next`] is called. Allocation will only occur if the user
    /// provided function `collect_fn` allocates to produce its result.
    ///
    /// See also [`basic::try_repeated_until`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::ErrorKind;
    /// # use pars::bytes::{self, PResult};
    /// fn c_str_len(input: &[u8]) -> PResult<usize, &[u8]> {
    ///     bytes::u8.try_repeated_until(bytes::verbatim(b"\x00"), |iter| {
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
    fn try_repeated_until<P, F, R, S>(
        self,
        sentinel: P,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = (R, P::Parsed), Error = Self::Error>
    where
        Self: Sized,
        S: ErrorSeed<I, Self::Error>,
        P: Parse<I, Error = Self::Error>,
        F: for<'a> Fn(basic::RepeatedUntilIter<'a, Self, P, I>) -> Result<R, S>,
    {
        basic::try_repeated_until(self, sentinel, collect_fn)
    }

    /// Creates a parser that is repeated until a sentinel is parsed.
    ///
    /// [`Parse::collect_repeated_until`] produces a parser that will apply `self`
    /// repeatedly until `sentinel_parser` succeeds. That is, `sentinel_parser` is
    /// applied; if it fails, `self` is applied before trying `sentinel_parser` again.
    /// If `sentinel_parser` succeeds, parsing is complete.
    ///
    /// The values produced by `self` are collected using the [`FromIterator`] trait
    /// implementation for the new parser's parsed result type, which is usually
    /// deduced. This value together with the parsed value from `sentinel_parser` as a
    /// 2-tuple become the parsed value for the overall new parser. If `self` returns
    /// a parsing error at any point, a parsing error is returned from the overall new
    /// parser.
    ///
    /// Note that the returned new parser does not allocate unless the
    /// [`FromIterator`] implementation allocates.
    ///
    /// See also [`basic::collect_repeated_until`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn c_str(input: &[u8]) -> PResult<Vec<u8>, &[u8]> {
    ///     bytes::u8.collect_repeated_until(bytes::verbatim(b"\x00"))
    ///         .map(|(s, _)| s)
    ///         .parse(input)
    /// }
    ///
    /// assert!(c_str.parse(b"hello\x00world") == Ok(Success(Vec::from(b"hello"), b"world")));
    /// assert!(c_str.parse(b"\x00") == Ok(Success(Vec::new(), b"")));
    /// assert!(c_str.parse(b"hello").is_err());
    /// ```
    #[inline]
    fn collect_repeated_until<P, R>(
        self,
        sentinel: P,
    ) -> impl Parse<I, Parsed = (R, P::Parsed), Error = Self::Error>
    where
        Self: Sized,
        P: Parse<I, Error = Self::Error>,
        R: FromIterator<Self::Parsed>,
    {
        basic::collect_repeated_until(self, sentinel)
    }

    /// Creates a parser that is repeated a number of times within a range.
    ///
    /// [`Parse::repeated`] produces a parser that will apply `self` repeatedly. The
    /// number of times `self` will be applied is defined by `range`. For example, if
    /// `range` is `3..=5`, `self` will be applied at least 3 times, and will be
    /// applied up to 5 times if possible. If `self` fails before parsing 3 times
    /// (or whatever lower bound applies to `range`, if any), a parsing error is
    /// returned from the new parser. Once the upper bound is met (again, if any)
    /// parsing automatically ends successfully. `self` returning a parsing error
    /// after meeting the lower bound also ends parsing for the new parser.
    ///
    /// The values produced by `self` are passed to `collect_fn` in the form of
    /// an iterator, [`RepeatedIter`](basic::RepeatedIter). Whever `collect_fn`
    /// returns is the parsed value of the new parser.
    ///
    /// Note that the returned new parser does not allocate. Values produced by
    /// the iterator are obtained on demand by applying `self` each time
    /// [`Iterator::next`] is called. Allocation will only occur if the user
    /// provided function `collect_fn` allocates to produce its result.
    ///
    /// See also [`basic::repeated`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
    ///     bytes::u8.repeated(2..=4, |iter| {
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
    fn repeated<N, F, R>(
        self,
        range: N,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        N: basic::Range,
        F: for<'a> Fn(basic::RepeatedIter<'a, Self, I>) -> R,
    {
        basic::repeated(self, range, collect_fn)
    }

    /// Creates a parser that is repeated a number of times within a range.
    ///
    /// [`Parse::try_repeated`] produces a parser that will apply `self` repeatedly.
    /// The number of times `self` will be applied is defined by `range`. For example,
    /// if `range` is `3..=5`, `self` will be applied at least 3 times, and will
    /// be applied up to 5 times if possible. If `self` fails before parsing 3
    /// times (or whatever lower bound applies to `range`, if any), a parsing error
    /// is returned from the new parser. Once the upper bound is met (again, if any)
    /// parsing automatically ends successfully. `self` returning a parsing error
    /// after meeting the lower bound also ends parsing for the new parser.
    ///
    /// The values produced by `self` are passed to `collect_fn` in the form of
    /// an iterator, [`RepeatedIter`](basic::RepeatedIter). If `collect_fn` returns
    /// an [`Ok`] value, the contained value becomes the parsed value of the new
    /// parser. If `collect_fn` returns an [`Err`], that gets returned as a parsing
    /// error via [`ErrorSeed`].
    ///
    /// Note that the returned new parser does not allocate. Values produced by
    /// the iterator are obtained on demand by applying `self` each time
    /// [`Iterator::next`] is called. Allocation will only occur if the user
    /// provided function `collect_fn` allocates to produce its result.
    ///
    /// See also [`basic::try_repeated`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// # use pars::ErrorKind;
    /// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
    ///     bytes::u8.try_repeated(2..=4, |iter| {
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
    fn try_repeated<N, F, R, S>(
        self,
        range: N,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        N: basic::Range,
        S: ErrorSeed<I, Self::Error>,
        F: for<'a> Fn(basic::RepeatedIter<'a, Self, I>) -> Result<R, S>,
    {
        basic::try_repeated(self, range, collect_fn)
    }

    /// Creates a parser that is repeated a number of times within a range.
    ///
    /// [`Parse::collect_repeated`] produces a parser that will apply `self`
    /// repeatedly. The number of times `self` will be applied is defined by `range`.
    /// For example, if `range` is `3..=5`, `self` will be applied at least 3 times,
    /// and will be applied up to 5 times if possible. If `self` fails before parsing
    /// 3 times (or whatever lower bound applies to `range`, if any), a parsing error
    /// is returned from the new parser. Once the upper bound is met (again, if any)
    /// parsing automatically ends successfully. `self` returning a parsing error
    /// after meeting the lower bound also ends parsing for the new parser.
    ///
    /// The values produced by `self` are collected by the [`FromIterator`] trait
    /// implementation on the parsed type of the parser, which is usually deduced.
    ///
    /// Note that the returned new parser does not allocate unless the
    /// [`FromIterator`] implementation allocates.
    ///
    /// See also [`basic::collect_repeated`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::PResult;
    /// use pars::unicode::{strict::char_with_prop, prop::Alphabetic};
    ///
    /// fn my_parser(input: &str) -> PResult<String, &str> {
    ///     char_with_prop(Alphabetic).collect_repeated(3..=5)
    ///         .parse(input)
    /// }
    ///
    /// assert_eq!(my_parser.parse("hello world"), Ok(Success(String::from("hello"), " world")));
    /// assert_eq!(my_parser.parse("hey there"), Ok(Success(String::from("hey"), " there")));
    /// assert!(my_parser.parse("hi there").is_err());
    /// assert_eq!(my_parser.parse("goodbye"), Ok(Success(String::from("goodb"), "ye")));
    /// ```
    #[inline]
    fn collect_repeated<C>(
        self,
        range: impl basic::Range,
    ) -> impl Parse<I, Parsed = C, Error = Self::Error>
    where
        Self: Sized,
        C: FromIterator<Self::Parsed>,
    {
        basic::collect_repeated(self, range)
    }

    /// Creates a parser that is repeated a constant number of times.
    ///
    /// [`Parse::array`] produces a parser that applies `self` `LEN` times and
    /// places the parsed results in an array. If `self` returns a parsing error
    /// before parsing `LEN` times, a parsing error is returned from the new parser.
    ///
    /// [`Parse::array`] is similar to [`Parse::repeated`], except that the number of
    /// repetitions is known at compile time and the results are placed in array
    /// rather than being processed via an iterator. Most cases where the number of
    /// repetitions is known at compile time should prefer to use [`Parse::array`],
    /// but be aware of the tradeoffs of storing and moving the values on the stack
    /// when `LEN` is large.
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<[u8; 4], &[u8]> {
    ///     bytes::u8.array().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") == Ok(Success([1, 2, 3, 4], b"\x05")));
    /// assert!(my_parser.parse(b"\x01\x02\x03").is_err());
    /// ```
    #[inline]
    fn array<const LEN: usize>(
        self,
    ) -> impl Parse<I, Parsed = [Self::Parsed; LEN], Error = Self::Error>
    where
        Self: Sized,
    {
        basic::array(self)
    }

    /// Creates a parser that is applied repeatedly while interspersed with a separator.
    ///
    /// [`Parse::separated`] produces a parser that will apply `self` and `separator`
    /// repeatedly, alternatiging between the two. The parsing pattern starts with
    /// `parser` and ends with `self`, such as `self separator self`. This is
    /// distinct from `parser.then(separator).repeated(...)` as [`Parse::separated`]
    /// will not parse a trailing separator, and a repeated pair must parse a trailing
    /// separator.
    ///
    /// The provided `range` determines the minimum and maximum number of repatitions
    /// of `self`. For example if `range` is `3..=5`, `self` must be able to parse
    /// at least 3 times, and up to 5 times. Similarly, `..` corresponds to 0 or more
    /// repetitions, and `1..` corresponds to 1 or more. An exact number of repetitions
    /// can be specified with a single integer value such as `3` (but `3..=3` is also
    /// valid and equivalent). See [`Range`](basic::Range) for more information on
    /// ranges.
    ///
    /// The values produced by `self` are passed to `collect_fn` in the form of an
    /// iterator, [`SeparatedIter`](basic::SeparatedIter). Whatever `collect_fn`
    /// returns is the parsed value of the new parser. The values produced by
    /// `separator` are discarded.
    ///
    /// Note that the returned new parser does not allocate. Values produced by the
    /// iterator are obtained on demand by applying `separator` and `self` each time
    /// [`Iterator::next`] is called. Allocation will only occur if the user provided
    /// `collect_fn` allocates when called.
    ///
    /// See also [`basic::separated`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<Vec<char>, &str> {
    ///     unicode::strict::char.separated(
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
    fn separated<N, S, F, R>(
        self,
        range: N,
        separator: S,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        N: basic::Range,
        S: Parse<I, Error = Self::Error>,
        F: for<'a> Fn(basic::SeparatedIter<'a, Self, S, I>) -> R,
    {
        basic::separated(self, range, separator, collect_fn)
    }

    /// Creates a parser that is applied repeatedly while interspersed with a separator.
    ///
    /// [`Parse::try_separated`] produces a parser that will apply `self` and
    /// `separator` repeatedly, alternatiging between the two. The parsing pattern
    /// starts with `self` and ends with `self`, such as `self separator self`. This is
    /// distinct from `parser.then(separator).try_repeated(...)` as
    /// [`Parse::try_separated`] will not parse a trailing separator, and a repeated
    /// pair must parse a trailing separator.
    ///
    /// The provided `range` determines the minimum and maximum number of repatitions
    /// of `self`. For example if `range` is `3..=5`, `self` must be able to parse
    /// at least 3 times, and up to 5 times. Similarly, `..` corresponds to 0 or more
    /// repetitions, and `1..` corresponds to 1 or more. An exact number of repetitions
    /// can be specified with a single integer value such as `3` (but `3..=3` is also
    /// valid and equivalent). See [`Range`](basic::Range) for more information on
    /// ranges.
    ///
    /// The values produced by `self` are passed to `collect_fn` in the form of an
    /// iterator, [`SeparatedIter`](basic::SeparatedIter). `collect_fn` then returns a
    /// [`Result`], where the [`Ok`] variant becomes the parsed value of the new parser,
    /// and the [`Err`] variant becomes an error returned by the new parser via the
    /// [`ErrorSeed`] trait.
    ///
    /// Note that the returned new parser does not allocate. Values produced by the
    /// iterator are obtained on demand by applying `separator` and `self` each time
    /// [`Iterator::next`] is called. Allocation will only occur if the user provided
    /// `collect_fn` allocates when called.
    ///
    /// See also [`basic::try_separated`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::ErrorKind;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<Vec<char>, &str> {
    ///     unicode::strict::char.try_separated(
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
    fn try_separated<N, S, F, R, E>(
        self,
        range: N,
        separator: S,
        collect_fn: F,
    ) -> impl Parse<I, Parsed = R, Error = Self::Error>
    where
        Self: Sized,
        N: basic::Range,
        S: Parse<I, Error = Self::Error>,
        F: for<'a> Fn(basic::SeparatedIter<'a, Self, S, I>) -> Result<R, E>,
        E: ErrorSeed<I, Self::Error>,
    {
        basic::try_separated(self, range, separator, collect_fn)
    }

    /// Creates a parser that is applied repeatedly while interspersed with a separator.
    ///
    /// [`Parse::collect_separated`] produces a parser that will apply `self` and
    /// `separator` repeatedly, alternatiging between the two. The parsing pattern
    /// starts with `self` and ends with `self`, such as `self separator self`. This
    /// is distinct from `parser.then(separator).collect_repeated(...)` as
    /// [`Parse::collect_separated`] will not parse a trailing separator, and a repeated
    /// pair must parse a trailing separator.
    ///
    /// The provided `range` determines the minimum and maximum number of repatitions
    /// of `self`. For example if `range` is `3..=5`, `self` must be able to parse
    /// at least 3 times, and up to 5 times. Similarly, `..` corresponds to 0 or more
    /// repetitions, and `1..` corresponds to 1 or more. An exact number of repetitions
    /// can be specified with a single integer value such as `3` (but `3..=3` is also
    /// valid and equivalent). See [`Range`](basic::Range) for more information on
    /// ranges.
    ///
    /// The values produced by `self` are collected via the [`FromIterator`] trait
    /// on the, typically inferred, parsed value type of the new parser. The values
    /// produced by `separator` are discarded.
    ///
    /// See also [`basic::collect_separated`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<Vec<char>, &str> {
    ///     // Note that `Vec<char>` is inferred from the return type of `my_parser`
    ///     unicode::strict::char.collect_separated(
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
    fn collect_separated<C>(
        self,
        range: impl basic::Range,
        separator: impl Parse<I, Error = Self::Error>,
    ) -> impl Parse<I, Parsed = C, Error = Self::Error>
    where
        Self: Sized,
        C: FromIterator<Self::Parsed>,
    {
        basic::collect_separated(self, range, separator)
    }

    /// Creates a parser that fails if all input is not consumed.
    ///
    /// [`Parse::complete`] produces a parser that applies `self` and then verifies that
    /// all input was consumed. If there is still input remaining, an error is returned
    /// via [`Error::expected_eof`].
    ///
    /// See also [`basic::complete`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
    ///     bytes::be::u32.complete().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success(0x01020304, &[][..])));
    /// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05").is_err());
    /// ```
    #[inline]
    fn complete(self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
    {
        basic::complete(self)
    }

    /// Creates a parser that returns a [`Span`] of parsed input in addition to the parsed value.
    ///
    /// [`Parse::spanned`] produces a parser that applies `self`, and on success, it returns the
    /// parsed value from `parser` in a tuple with a [`Span`] of the input consumed to produce
    /// the parsed value.
    ///
    /// If only the [`Span`] is needed and the parsed value can be discarded,
    /// [`Parse::recognize`] can also be used instead.
    ///
    /// See also [`basic::spanned`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<(u32, Span<&[u8]>), &[u8]> {
    ///     bytes::be::u32.spanned().parse(input)
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
    fn spanned(self) -> impl Parse<I, Parsed = (Self::Parsed, Span<I>), Error = Self::Error>
    where
        Self: Sized,
    {
        basic::spanned(self)
    }

    /// Creates a parser that also returns a span of the input that was parsed.
    ///
    /// [`Parse::spanned_into`] produces a parser that combines the parsed result
    /// of `self` with a [`Span`] of the input that `self` parsed converted to
    /// `S` via [`Into`] in a 2-tuple. This allows a parser to provide information
    /// about where in an input stream a parsed value originated from.
    ///
    /// [`Parse::spanned_into`] differs from [`Parse::spanned`] in that the
    /// produced [`Span`] is converted into another type, `S` by way of [`Into`].
    /// This is a common enough pattern that [`Parse::spanned_into`] exists to
    /// simplify usage. For example, a `Span<&str>` can be converted to a `&str`
    /// that contains just the content of the span.
    ///
    /// If the parsed value returned by `self` is not needed, such as a parser
    /// that returns the unit type, consider using [`Parse::recognize`] instead.
    /// Note that [`Parse::recognize`] doesn't provide a `recognize_into` variant,
    /// since the same effect can be accomplished with
    /// `parser.recognize().ok_into()` in this case.
    ///
    /// See also [`basic::spanned_into`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<(u32, &[u8]), &[u8]> {
    ///     bytes::be::u32.spanned_into().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x01\x02\x03\x04\x05") ==
    ///     Ok(Success((0x01020304, b"\x01\x02\x03\x04"), b"\x05")));
    /// assert!(my_parser.parse(b"").is_err());
    /// ```
    #[inline]
    fn spanned_into<S>(self) -> impl Parse<I, Parsed = (Self::Parsed, S), Error = Self::Error>
    where
        Self: Sized,
        Span<I>: Into<S>,
    {
        basic::spanned_into(self)
    }

    /// Creates a parser that returns a [`Span`] of parsed input.
    ///
    /// [`Parse::recognize`] produces a parser that applies `self` and on success, it
    /// returns a [`Span`] of the input consumed by `self`.
    ///
    /// [`Parse::recognize`] is similar to [`Parse::spanned`], except that the parsed
    /// value returned by `self` is discarded.
    ///
    /// See also [`basic::recognize`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<Span<&[u8]>, &[u8]> {
    ///     bytes::be::u32.recognize().parse(input)
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
    fn recognize(self) -> impl Parse<I, Parsed = Span<I>, Error = Self::Error>
    where
        Self: Sized,
    {
        basic::recognize(self)
    }

    /// Creates a parser that produces a parsed value only if `condition` is `true`.
    ///
    /// [`Parse::cond`] produces a parser that applies `self` only if `condition` is
    /// `true`. On success, the parsed value returned by `self` returned wrapped in
    /// [`Some`]. If `condition` is `false`, the parser succeeds, but returns [`None`]
    /// as the parsed value.
    ///
    /// See also [`basic::cond`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<Option<u32>, &[u8]> {
    ///     bytes::u8.flat_map(|b| {
    ///         bytes::be::u32.cond(b != 0)
    ///     }).parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x00\x01\x02\x03\x04") == Ok(Success(None, b"\x01\x02\x03\x04")));
    /// assert!(my_parser.parse(b"\x01\x01\x02\x03\x04") == Ok(Success(Some(0x01020304), b"")));
    /// ```
    #[inline]
    fn cond(
        self,
        condition: bool,
    ) -> impl Parse<I, Parsed = Option<Self::Parsed>, Error = Self::Error>
    where
        Self: Sized,
    {
        basic::cond(self, condition)
    }

    /// Creates a parser that succeeds only if the parsed value passes the given predicate.
    ///
    /// [`Parse::verify`] produces a parser that applies `self`, and on success, passes the parsed
    /// value to `verify_fn`. If `verify_fn` returns `true`, the parser returns the parsed value.
    /// If `verify_fn` returns `false`, the parser returns an error via [`Error::invalid_input`].
    ///
    /// See also [`basic::verify`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn non_zero(input: &[u8]) -> PResult<u32, &[u8]> {
    ///     bytes::be::u32.verify(|v| *v != 0).parse(input)
    /// }
    ///
    /// assert!(non_zero.parse(b"\x00\x00\x00\x00").is_err());
    /// assert!(non_zero.parse(b"\x00\x00\x00\x01") == Ok(Success(1, b"")));
    /// ```
    #[inline]
    fn verify<F>(self, verify_fn: F) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
        F: Fn(&Self::Parsed) -> bool,
    {
        basic::verify(self, verify_fn)
    }

    /// Creates a parser that succeeds only if `self` fails.
    ///
    /// [`Parse::not`] produces a parser that applies `self`, an on success, it returns
    /// an error via [`Error::invalid_input`]. If `self` fails, the new parser returns
    /// a success.
    ///
    /// See also [`basic::not`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::ascii::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<(), &str> {
    ///     ascii::strict::char_with_prop(ascii::prop::Printable).not().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse("hello").is_err());
    /// assert!(my_parser.parse("\0").is_ok());
    /// ```
    #[inline]
    fn not(self) -> impl Parse<I, Parsed = (), Error = Self::Error>
    where
        Self: Sized,
    {
        basic::not(self)
    }

    /// Creates a parser that attempts to parse with `self` if possible.
    ///
    /// [`Parse::opt`] produces a parser that applies `self`, and on success, the new
    /// parser returns the parsed value wrapped in [`Some`]. On failure, the new parser
    /// still succeeds but returns [`None`] without consuming any input.
    ///
    /// See also [`basic::opt`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<Option<&[u8]>, &[u8]> {
    ///     bytes::verbatim("hello").ok_into().opt().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"hello world") == Ok(Success(Some(&b"hello"[..]), b" world")));
    /// assert!(my_parser.parse(b"goodbye world") == Ok(Success(None, b"goodbye world")));
    /// ```
    #[inline]
    fn opt(self) -> impl Parse<I, Parsed = Option<Self::Parsed>, Error = Self::Error>
    where
        Self: Sized,
    {
        basic::opt(self)
    }

    /// Creates a parser that parses without consuming input.
    ///
    /// [`Parse::peek`] produces a parser that applies `self`, and on success, the new parser
    /// returns the parsed value returned by `self` and the entire input that was passed to
    /// the parser. On failure, the new parser forwards the error unmodified.
    ///
    /// See also [`basic::peek`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<u32, &[u8]> {
    ///     bytes::be::u32.peek().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success(0x01020304, b"\x01\x02\x03\x04")));
    /// ```
    #[inline]
    fn peek(self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
    {
        basic::peek(self)
    }

    /// Creates a parser out of a reference to another parser.
    ///
    /// [`Parse::by_ref`] produces a parser that directly applies `self`. The
    /// produced parser behaves identically to `self` and internally contains a
    /// reference to `self`.
    ///
    /// [`Parse`] is not automatically implemented for references to types that
    /// implement [`Parse`], so [`Parse::by_ref`] can by used to convert a
    /// reference to a parser into a parser.
    ///
    /// See also [`basic::by_ref`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::bytes::{self, PResult};
    /// fn my_parser(input: &[u8]) -> PResult<u8, &[u8]> {
    ///     bytes::u8.by_ref().parse(input)
    /// }
    ///
    /// assert!(my_parser.parse(b"\x01\x02\x03\x04") == Ok(Success(1u8, b"\x02\x03\x04")));
    /// assert!(my_parser.parse(b"").is_err());
    /// ```
    #[inline]
    fn by_ref<'a>(&'a self) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error> + 'a
    where
        I: 'a,
    {
        basic::by_ref(self)
    }

    /// Creates a parser that applies two parsers in sequence.
    ///
    /// [`Parse::then`] produces a parser that applies `self` and `other` in that
    /// order. On success, the new parser returns the parsed values returned
    /// by `self` and `other` as a tuple. If either parser fails, the
    /// corresponding error is returned from the new parser. When `self` fails,
    /// `other` is not applied.
    ///
    /// See also [`basic::pair`] and [`basic::seq`].
    ///
    /// # Example
    /// ```
    /// # use pars::prelude::*;
    /// # use pars::unicode::{self, PResult};
    /// fn my_parser(input: &str) -> PResult<(char, char), &str> {
    ///     unicode::strict::char.then(unicode::strict::char)
    ///         .parse(input)
    /// }
    ///
    /// assert_eq!(my_parser.parse("abc"), Ok(Success(('a', 'b'), "c")));
    /// assert!(my_parser.parse("a").is_err());
    /// assert!(my_parser.parse("").is_err());
    /// ```
    #[inline]
    fn then<P>(
        self,
        other: P,
    ) -> impl Parse<I, Parsed = (Self::Parsed, P::Parsed), Error = Self::Error>
    where
        Self: Sized,
        P: Parse<I, Error = Self::Error>,
    {
        basic::pair(self, other)
    }

    /// Creates a parser that attempts to parse with each of two parsers.
    ///
    /// [`Parse::or`] produces a parser that first attempts to apply `self` and
    /// then applies `other` if `self` fails. If `self` succeeds, the
    /// parsed value `self` returns is returned by the new parser. If `self`
    /// fails and then `other` succeeds, the parsed value returned by `other`
    /// is returned by the new parser. If both fail, the error returned by
    /// `other` is returned.
    ///
    /// See also [`basic::either`] and [`basic::alt`].
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
    fn or<P>(self, other: P) -> impl Parse<I, Parsed = Self::Parsed, Error = Self::Error>
    where
        Self: Sized,
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

impl<I: Input, E: Error<I>> ErrorSeed<I, E> for core::convert::Infallible {
    fn into_error(self, pos: I) -> E {
        let _ = pos;
        unreachable!()
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
