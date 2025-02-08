use crate::{Error as PError, Failure, Input, Success};

pub mod lossy;
pub mod prop;
pub mod strict;

mod loc;

pub use loc::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorKind {
    NeedMoreInput,
    ExpectedEof,
    InvalidInput,
    InvalidUtf8,
    InvalidUtf16,
    InvalidCodePoint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error<I: Input> {
    kind: ErrorKind,
    pos: I,
}

pub type PResult<T, I> = super::PResult<T, I, Error<I>>;

pub trait UnicodeSymbol {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = Self>;

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = Self>;

    fn parse_utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char(input)?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char_lossy(input)?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    fn parse_utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char(input)?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }

    fn parse_utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = Self>,
    {
        let Success(ch, rem) = Self::parse_char_lossy(input)?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }
}

pub trait UnicodeInput: Input {
    fn parse_char(self) -> PResult<core::primitive::char, Self>;

    fn parse_char_lossy(self) -> PResult<core::primitive::char, Self>;

    fn parse_utf8(self, buf: &mut [u8]) -> PResult<&str, Self> {
        let Success(ch, rem) = self.parse_char()?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    fn parse_utf8_lossy(self, buf: &mut [u8]) -> PResult<&str, Self> {
        let Success(ch, rem) = self.parse_char_lossy()?;
        Ok(Success(ch.encode_utf8(buf), rem))
    }

    fn parse_utf16(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        let Success(ch, rem) = self.parse_char()?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }

    fn parse_utf16_lossy(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        let Success(ch, rem) = self.parse_char_lossy()?;
        Ok(Success(ch.encode_utf16(buf), rem))
    }
}

pub trait Property: core::fmt::Debug + Copy {
    fn contains(self, ch: core::primitive::char) -> bool;
}

impl<I> UnicodeInput for I
where
    I: Input,
    I::Symbol: UnicodeSymbol,
{
    fn parse_char(self) -> PResult<core::primitive::char, Self> {
        <I::Symbol as UnicodeSymbol>::parse_char(self)
    }

    fn parse_char_lossy(self) -> PResult<core::primitive::char, Self> {
        <I::Symbol as UnicodeSymbol>::parse_char_lossy(self)
    }

    fn parse_utf8(self, buf: &mut [u8]) -> PResult<&str, Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf8(self, buf)
    }

    fn parse_utf8_lossy(self, buf: &mut [u8]) -> PResult<&str, Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf8_lossy(self, buf)
    }

    fn parse_utf16(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf16(self, buf)
    }

    fn parse_utf16_lossy(self, buf: &mut [u16]) -> PResult<&[u16], Self> {
        <I::Symbol as UnicodeSymbol>::parse_utf16_lossy(self, buf)
    }
}

impl UnicodeSymbol for core::primitive::char {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = core::primitive::char>,
    {
        use crate::basic::pop;
        pop(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = core::primitive::char>,
    {
        use crate::basic::pop;
        pop(input)
    }
}

impl UnicodeSymbol for u32 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u32>,
    {
        utf32_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u32>,
    {
        utf32_char_lossy(input)
    }
}

impl UnicodeSymbol for i32 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i32>,
    {
        utf32_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i32>,
    {
        utf32_char_lossy(input)
    }
}

impl UnicodeSymbol for u16 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u16>,
    {
        utf16_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u16>,
    {
        utf16_char_lossy(input)
    }

    fn parse_utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = u16>,
    {
        utf16(input, buf)
    }

    fn parse_utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = u16>,
    {
        utf16_lossy(input, buf)
    }
}

impl UnicodeSymbol for i16 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i16>,
    {
        utf16_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i16>,
    {
        utf16_char_lossy(input)
    }

    fn parse_utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = i16>,
    {
        utf16(input, buf)
    }

    fn parse_utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
    where
        I: Input<Symbol = i16>,
    {
        utf16_lossy(input, buf)
    }
}

impl UnicodeSymbol for u8 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8_char_lossy(input)
    }

    fn parse_utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8(input, buf)
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = u8>,
    {
        utf8_lossy(input, buf)
    }
}

impl UnicodeSymbol for i8 {
    fn parse_char<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8_char(input)
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8_char_lossy(input)
    }

    fn parse_utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8(input, buf)
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = i8>,
    {
        utf8_lossy(input, buf)
    }
}

#[cfg(feature = "ascii")]
impl UnicodeSymbol for crate::ascii::AsciiChar {
    fn parse_char<I>(mut input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        let ch = input.next();
        match ch {
            Some(ch) => Ok(Success(ch.into(), input)),
            None => Err(Failure(Error::need_more_input(input.clone()), input)),
        }
    }

    fn parse_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        Self::parse_char(input)
    }

    fn parse_utf8<I>(mut input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        let ch = input.next();
        match ch {
            Some(ch) => {
                buf[0] = ch.into();
                Ok(Success(unsafe { core::mem::transmute(&buf[..1]) }, input))
            }
            None => Err(Failure(Error::need_more_input(input.clone()), input)),
        }
    }

    fn parse_utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
    where
        I: Input<Symbol = crate::ascii::AsciiChar>,
    {
        Self::parse_utf8(input, buf)
    }
}

trait AsU8 {
    fn as_u8(self) -> u8;
}

impl AsU8 for u8 {
    fn as_u8(self) -> u8 {
        self
    }
}

impl AsU8 for i8 {
    fn as_u8(self) -> u8 {
        self as u8
    }
}

trait AsU16 {
    fn as_u16(self) -> u16;
}

impl AsU16 for u16 {
    fn as_u16(self) -> u16 {
        self
    }
}

impl AsU16 for i16 {
    fn as_u16(self) -> u16 {
        self as u16
    }
}

trait AsU32 {
    fn as_u32(self) -> u32;
}

impl AsU32 for u32 {
    fn as_u32(self) -> u32 {
        self
    }
}

impl AsU32 for i32 {
    fn as_u32(self) -> u32 {
        self as u32
    }
}

fn utf32_char<I>(mut input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: AsU32,
{
    if let Some(ch) = input.next() {
        if let Some(ch) = core::primitive::char::from_u32(ch.as_u32()) {
            Ok(Success(ch, input))
        } else {
            Err(Failure(Error::invalid_code_point(input.clone()), input))
        }
    } else {
        Err(Failure(Error::need_more_input(input.clone()), input))
    }
}

fn utf32_char_lossy<I>(mut input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: AsU32,
{
    if let Some(ch) = input.next() {
        if let Some(ch) = core::primitive::char::from_u32(ch.as_u32()) {
            Ok(Success(ch, input))
        } else {
            Ok(Success('\u{fffd}', input))
        }
    } else {
        Err(Failure(Error::need_more_input(input.clone()), input))
    }
}

fn utf16<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
where
    I: Input,
    I::Symbol: AsU16,
{
    let mut len = 1usize;
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(AsU16::as_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    buf[0] = c0;
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(AsU16::as_u16) else {
            return Err(Failure(Error::need_more_input(rem), input));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            return Err(Failure(Error::invalid_utf16(tmp), input));
        }
        buf[1] = c1;
        len = 2;
        let c0 = (c0 & 0b0000_0011_1111_1111) as u32;
        let c1 = (c1 & 0b0000_0011_1111_1111) as u32;
        ((c0 << 10) | c1) + 0x10000
    } else {
        c0 as u32
    };
    if let Some(_) = core::primitive::char::from_u32(ch) {
        Ok(Success(&buf[..len], rem))
    } else {
        Err(Failure(Error::invalid_code_point(input.clone()), input))
    }
}

fn utf16_lossy<I>(input: I, buf: &mut [u16]) -> PResult<&[u16], I>
where
    I: Input,
    I::Symbol: AsU16,
{
    let mut len = 1usize;
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(AsU16::as_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    buf[0] = c0;
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(AsU16::as_u16) else {
            buf[0] = 0xfffd;
            return Ok(Success(&buf[..1], rem));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            buf[0] = 0xfffd;
            return Ok(Success(&buf[..1], tmp));
        }
        buf[1] = c1;
        len = 2;
        let c0 = (c0 & 0b0000_0011_1111_1111) as u32;
        let c1 = (c1 & 0b0000_0011_1111_1111) as u32;
        ((c0 << 10) | c1) + 0x10000
    } else {
        c0 as u32
    };
    if let Some(_) = core::primitive::char::from_u32(ch) {
        Ok(Success(&buf[..len], rem))
    } else {
        buf[0] = 0xfffd;
        Ok(Success(&buf[..1], input))
    }
}

fn utf16_char<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: AsU16,
{
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(AsU16::as_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(AsU16::as_u16) else {
            return Err(Failure(Error::need_more_input(rem), input));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            return Err(Failure(Error::invalid_utf16(tmp), input));
        }
        let c0 = (c0 & 0b0000_0011_1111_1111) as u32;
        let c1 = (c1 & 0b0000_0011_1111_1111) as u32;
        ((c0 << 10) | c1) + 0x10000
    } else {
        c0 as u32
    };
    if let Some(ch) = core::primitive::char::from_u32(ch) {
        Ok(Success(ch, rem))
    } else {
        Err(Failure(Error::invalid_code_point(input.clone()), input))
    }
}

fn utf16_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: AsU16,
{
    let mut rem = input.clone();
    let Some(c0) = rem.next().map(AsU16::as_u16) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };
    let ch = if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
        let tmp = rem.clone();
        let Some(c1) = rem.next().map(AsU16::as_u16) else {
            return Ok(Success('\u{fffd}', rem));
        };
        if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let c0 = (c0 & 0b0000_0011_1111_1111) as u32;
        let c1 = (c1 & 0b0000_0011_1111_1111) as u32;
        ((c0 << 10) | c1) + 0x10000
    } else {
        c0 as u32
    };
    if let Some(ch) = core::primitive::char::from_u32(ch) {
        Ok(Success(ch, rem))
    } else {
        Ok(Success('\u{fffd}', input))
    }
}

fn utf8<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
where
    I: Input,
    I::Symbol: AsU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(AsU8::as_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if let Some(_) = char::from_u32(b0 as u32) {
        buf[0] = b0;
        Ok(Success(unsafe { core::mem::transmute(&buf[..1]) }, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        buf[0] = b0;
        buf[1] = b1;
        let b0 = (b0 as u32) & 0b0001_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(_) = char::from_u32(ch) {
            Ok(Success(unsafe { core::mem::transmute(&buf[..2]) }, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        let b0 = (b0 as u32) & 0b0000_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(_) = char::from_u32(ch) {
            Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        buf[3] = b3;
        let b0 = (b0 as u32) & 0b0000_0111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let b3 = (b3 as u32) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(_) = char::from_u32(ch) {
            Ok(Success(unsafe { core::mem::transmute(&buf[..4]) }, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else {
        Err(Failure(Error::invalid_utf8(input.clone()), input))
    }
}

fn utf8_lossy<I>(input: I, buf: &mut [u8]) -> PResult<&str, I>
where
    I: Input,
    I::Symbol: AsU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(AsU8::as_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if let Some(_) = char::from_u32(b0 as u32) {
        buf[0] = b0;
        Ok(Success(unsafe { core::mem::transmute(&buf[..1]) }, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        }
        buf[0] = b0;
        buf[1] = b1;
        let b0 = (b0 as u32) & 0b0001_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(_) = char::from_u32(ch) {
            Ok(Success(unsafe { core::mem::transmute(&buf[..2]) }, rem))
        } else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, rem));
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        let b0 = (b0 as u32) & 0b0000_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(_) = char::from_u32(ch) {
            Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, rem))
        } else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, rem));
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(AsU8::as_u8) else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
        }
        buf[0] = b0;
        buf[1] = b1;
        buf[2] = b2;
        buf[3] = b3;
        let b0 = (b0 as u32) & 0b0000_0111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let b3 = (b3 as u32) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(_) = char::from_u32(ch) {
            Ok(Success(unsafe { core::mem::transmute(&buf[..4]) }, rem))
        } else {
            buf[0] = 0xef;
            buf[1] = 0xbf;
            buf[2] = 0xbd;
            return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, rem));
        }
    } else {
        let mut tmp = rem.clone();
        while rem.next().map(AsU8::as_u8).map(|b| b & 0b1100_0000) == Some(0b1000_0000) {
            tmp = rem.clone();
        }
        buf[0] = 0xef;
        buf[1] = 0xbf;
        buf[2] = 0xbd;
        return Ok(Success(unsafe { core::mem::transmute(&buf[..3]) }, tmp));
    }
}

fn utf8_char<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: AsU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(AsU8::as_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if let Some(ch) = char::from_u32(b0 as u32) {
        Ok(Success(ch, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let b0 = (b0 as u32) & 0b0001_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let b0 = (b0 as u32) & 0b0000_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(AsU8::as_u8) else {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_utf8(tmp), input));
        }
        let b0 = (b0 as u32) & 0b0000_0111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let b3 = (b3 as u32) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_utf8(input.clone()), input))
        }
    } else {
        Err(Failure(Error::invalid_utf8(input.clone()), input))
    }
}

fn utf8_char_lossy<I>(input: I) -> PResult<core::primitive::char, I>
where
    I: Input,
    I::Symbol: AsU8,
{
    let mut rem = input.clone();
    let Some(b0) = rem.next().map(AsU8::as_u8) else {
        return Err(Failure(Error::need_more_input(rem), input));
    };

    if let Some(ch) = char::from_u32(b0 as u32) {
        Ok(Success(ch, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let b0 = (b0 as u32) & 0b0001_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Ok(Success('\u{fffd}', rem))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let b0 = (b0 as u32) & 0b0000_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Ok(Success('\u{fffd}', rem))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let Some(b1) = rem.next().map(AsU8::as_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let tmp = rem.clone();
        let Some(b2) = rem.next().map(AsU8::as_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let tmp = rem.clone();
        let Some(b3) = rem.next().map(AsU8::as_u8) else {
            return Ok(Success('\u{fffd}', tmp));
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Ok(Success('\u{fffd}', tmp));
        }
        let b0 = (b0 as u32) & 0b0000_0111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let b3 = (b3 as u32) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Ok(Success('\u{fffd}', rem))
        }
    } else {
        let mut tmp = rem.clone();
        while rem.next().map(AsU8::as_u8).map(|b| b & 0b1100_0000) == Some(0b1000_0000) {
            tmp = rem.clone();
        }
        Ok(Success('\u{fffd}', tmp))
    }
}

impl<I: Input> Error<I> {
    pub const fn new(kind: ErrorKind, pos: I) -> Self {
        Self { kind, pos }
    }

    pub const fn invalid_utf8(pos: I) -> Self {
        Self::new(ErrorKind::InvalidUtf8, pos)
    }

    pub const fn invalid_utf16(pos: I) -> Self {
        Self::new(ErrorKind::InvalidUtf16, pos)
    }

    pub const fn invalid_code_point(pos: I) -> Self {
        Self::new(ErrorKind::InvalidCodePoint, pos)
    }

    pub const fn kind(&self) -> ErrorKind {
        self.kind
    }
}

impl<I: Input> crate::Error<I> for Error<I> {
    fn need_more_input(pos: I) -> Self {
        Self::new(ErrorKind::NeedMoreInput, pos)
    }

    fn expected_eof(pos: I) -> Self {
        Self::new(ErrorKind::ExpectedEof, pos)
    }

    fn invalid_input(pos: I) -> Self {
        Self::new(ErrorKind::InvalidInput, pos)
    }

    fn position(&self) -> &I {
        &self.pos
    }
}

impl<I: Input> crate::ErrorSeed<I, Error<I>> for ErrorKind {
    fn into_error(self, pos: I) -> Error<I> {
        Error::new(self, pos)
    }
}
