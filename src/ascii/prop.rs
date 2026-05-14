//! ASCII character property definitions and combinators.
//!
//! This module provides a set of built-in [`Property`] types for common
//! ASCII character classifications, along with combinator types for composing
//! properties using logical operators.
//!
//! All property types implement [`Not`], [`BitAnd`](core::ops::BitAnd), and
//! [`BitOr`](core::ops::BitOr) via operator overloading, allowing properties to be
//! combined with the `!`, `&`, and `|` operators respectively.
//!
//! # Example
//! ```
//! use pars::ascii::{prop::{Alphabetic, Digit}, strict::char_with_prop};
//! use pars::prelude::*;
//! use pars::ascii::PResult;
//!
//! // Match a letter or digit
//! fn alphanumeric(input: &str) -> PResult<pars::ascii::AsciiChar, &str> {
//!     char_with_prop(Alphabetic | Digit).parse(input)
//! }
//!
//! assert!(alphanumeric.parse("a").is_ok());
//! assert!(alphanumeric.parse("1").is_ok());
//! assert!(alphanumeric.parse("!").is_err());
//! ```

use super::Property;
use ascii::AsciiChar;

/// A property that matches characters NOT matched by the inner property.
///
/// Construct via the `!` operator on any type implementing [`Property`].
///
/// # Example
/// ```
/// use pars::ascii::{prop::{Alphabetic, Not}, strict::char_with_prop};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn non_alpha(input: &str) -> PResult<pars::ascii::AsciiChar, &str> {
///     char_with_prop(!Alphabetic).parse(input)
/// }
///
/// assert!(non_alpha.parse("1").is_ok());
/// assert!(non_alpha.parse("a").is_err());
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Not<P: Property>(P);

impl<P: Property> Property for Not<P> {
    fn contains(self, ch: AsciiChar) -> bool {
        !self.0.contains(ch)
    }
}

impl<P: Property> core::ops::Not for Not<P> {
    type Output = P;

    fn not(self) -> P {
        self.0
    }
}

impl<L: Property, R: Property> core::ops::BitAnd<R> for Not<L> {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<L: Property, R: Property> core::ops::BitOr<R> for Not<L> {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// A property that matches characters matched by both inner properties.
///
/// Construct via the `&` operator on any two types implementing [`Property`].
///
/// # Example
/// ```
/// use pars::ascii::{prop::{Lowercase, HexDigit}, strict::char_with_prop};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn lower_hex(input: &str) -> PResult<pars::ascii::AsciiChar, &str> {
///     char_with_prop(Lowercase & HexDigit).parse(input)
/// }
///
/// assert!(lower_hex.parse("a").is_ok());
/// assert!(lower_hex.parse("A").is_err()); // uppercase
/// assert!(lower_hex.parse("g").is_err()); // not hex
/// ```
#[derive(Debug, Clone, Copy)]
pub struct And<L: Property, R: Property>(L, R);

impl<L: Property, R: Property> Property for And<L, R> {
    fn contains(self, ch: AsciiChar) -> bool {
        self.0.contains(ch) && self.1.contains(ch)
    }
}

impl<L: Property, R: Property> core::ops::Not for And<L, R> {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitAnd<R> for And<LL, LR> {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitOr<R> for And<LL, LR> {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// A property that matches characters matched by either inner property.
///
/// Construct via the `|` operator on any two types implementing [`Property`].
///
/// # Example
/// ```
/// use pars::ascii::{prop::{Digit, Alphabetic}, strict::char_with_prop};
/// use pars::prelude::*;
/// use pars::ascii::PResult;
///
/// fn alpha_or_digit(input: &str) -> PResult<pars::ascii::AsciiChar, &str> {
///     char_with_prop(Alphabetic | Digit).parse(input)
/// }
///
/// assert!(alpha_or_digit.parse("a").is_ok());
/// assert!(alpha_or_digit.parse("9").is_ok());
/// assert!(alpha_or_digit.parse("!").is_err());
/// ```
#[derive(Debug, Clone, Copy)]
pub struct Or<L: Property, R: Property>(L, R);

impl<L: Property, R: Property> Property for Or<L, R> {
    fn contains(self, ch: AsciiChar) -> bool {
        self.0.contains(ch) || self.1.contains(ch)
    }
}

impl<L: Property, R: Property> core::ops::Not for Or<L, R> {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitAnd<R> for Or<LL, LR> {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<LL: Property, LR: Property, R: Property> core::ops::BitOr<R> for Or<LL, LR> {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII alphabetic characters (`A`–`Z`, `a`–`z`).
#[derive(Debug, Clone, Copy)]
pub struct Alphabetic;

impl Property for Alphabetic {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_alphabetic()
    }
}

impl core::ops::Not for Alphabetic {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Alphabetic {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Alphabetic {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII alphanumeric characters (`A`–`Z`, `a`–`z`, `0`–`9`).
#[derive(Debug, Clone, Copy)]
pub struct Alphanumeric;

impl Property for Alphanumeric {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_alphanumeric()
    }
}

impl core::ops::Not for Alphanumeric {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Alphanumeric {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Alphanumeric {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII blank characters (space `' '` and horizontal tab `'\t'`).
#[derive(Debug, Clone, Copy)]
pub struct Blank;

impl Property for Blank {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_blank()
    }
}

impl core::ops::Not for Blank {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Blank {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Blank {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII control characters (code points `0x00`–`0x1F` and `0x7F`).
#[derive(Debug, Clone, Copy)]
pub struct Control;

impl Property for Control {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_control()
    }
}

impl core::ops::Not for Control {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Control {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Control {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII decimal digit characters (`0`–`9`).
#[derive(Debug, Clone, Copy)]
pub struct Digit;

impl Property for Digit {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_digit()
    }
}

impl core::ops::Not for Digit {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Digit {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Digit {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII graphic (visible, non-space) characters (code points `0x21`–`0x7E`).
#[derive(Debug, Clone, Copy)]
pub struct Graphic;

impl Property for Graphic {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_graphic()
    }
}

impl core::ops::Not for Graphic {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Graphic {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Graphic {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII hexadecimal digit characters (`0`–`9`, `a`–`f`, `A`–`F`).
#[derive(Debug, Clone, Copy)]
pub struct HexDigit;

impl Property for HexDigit {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_hexdigit()
    }
}

impl core::ops::Not for HexDigit {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for HexDigit {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for HexDigit {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII lowercase alphabetic characters (`a`–`z`).
#[derive(Debug, Clone, Copy)]
pub struct Lowercase;

impl Property for Lowercase {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_lowercase()
    }
}

impl core::ops::Not for Lowercase {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Lowercase {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Lowercase {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII octal digit characters (`0`–`7`).
#[derive(Debug, Clone, Copy)]
pub struct OctDigit;

impl Property for OctDigit {
    fn contains(self, ch: AsciiChar) -> bool {
        matches!(
            ch,
            AsciiChar::_0
                | AsciiChar::_1
                | AsciiChar::_2
                | AsciiChar::_3
                | AsciiChar::_4
                | AsciiChar::_5
                | AsciiChar::_6
                | AsciiChar::_7
        )
    }
}

impl core::ops::Not for OctDigit {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for OctDigit {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for OctDigit {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII printable characters (graphic characters plus space, code points `0x20`–`0x7E`).
#[derive(Debug, Clone, Copy)]
pub struct Printable;

impl Property for Printable {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_printable()
    }
}

impl core::ops::Not for Printable {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Printable {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Printable {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII punctuation characters (graphic characters excluding alphanumeric ones).
#[derive(Debug, Clone, Copy)]
pub struct Punctuation;

impl Property for Punctuation {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_punctuation()
    }
}

impl core::ops::Not for Punctuation {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Punctuation {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Punctuation {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII uppercase alphabetic characters (`A`–`Z`).
#[derive(Debug, Clone, Copy)]
pub struct Uppercase;

impl Property for Uppercase {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_uppercase()
    }
}

impl core::ops::Not for Uppercase {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Uppercase {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Uppercase {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}

/// Property matching ASCII whitespace characters (space, tab, newline, vertical tab, form feed, carriage return).
#[derive(Debug, Clone, Copy)]
pub struct Whitespace;

impl Property for Whitespace {
    fn contains(self, ch: AsciiChar) -> bool {
        ch.is_ascii_whitespace()
    }
}

impl core::ops::Not for Whitespace {
    type Output = Not<Self>;

    fn not(self) -> Not<Self> {
        Not(self)
    }
}

impl<R: Property> core::ops::BitAnd<R> for Whitespace {
    type Output = And<Self, R>;

    fn bitand(self, rhs: R) -> And<Self, R> {
        And(self, rhs)
    }
}

impl<R: Property> core::ops::BitOr<R> for Whitespace {
    type Output = Or<Self, R>;

    fn bitor(self, rhs: R) -> Or<Self, R> {
        Or(self, rhs)
    }
}
