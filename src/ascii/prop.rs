use super::Property;
use ascii::AsciiChar;

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
