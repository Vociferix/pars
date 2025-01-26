use crate::{basic::pop, Error as PError, Failure, Input, IntoInput, Parse, Success};
use core::marker::PhantomData;

pub use pars_macros::regex_bytes as regex;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error<I: Input> {
    kind: ErrorKind,
    pos: I,
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ErrorKind {
    NeedMoreInput,
    ExpectedEof,
    InvalidInput,
}

pub type PResult<T, I> = super::PResult<T, I, Error<I>>;

pub trait ByteSymbol {
    fn parse_byte<I>(input: I) -> PResult<core::primitive::u8, I>
    where
        I: Input<Symbol = Self>;
}

pub trait ByteInput: Input {
    fn parse_byte(self) -> PResult<core::primitive::u8, Self>;
}

impl<I: Input> Error<I> {
    pub const fn new(kind: ErrorKind, pos: I) -> Self {
        Self { kind, pos }
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

impl<I> ByteInput for I
where
    I: Input,
    I::Symbol: ByteSymbol,
{
    fn parse_byte(self) -> PResult<core::primitive::u8, Self> {
        <I::Symbol as ByteSymbol>::parse_byte(self)
    }
}

impl ByteSymbol for core::primitive::u8 {
    fn parse_byte<I>(input: I) -> PResult<core::primitive::u8, I>
    where
        I: Input<Symbol = Self>,
    {
        pop(input)
    }
}

impl ByteSymbol for core::primitive::i8 {
    fn parse_byte<I>(input: I) -> PResult<core::primitive::u8, I>
    where
        I: Input<Symbol = Self>,
    {
        pop.map(|b| b as core::primitive::u8).parse(input)
    }
}

impl ByteSymbol for crate::ascii::AsciiChar {
    fn parse_byte<I>(input: I) -> PResult<core::primitive::u8, I>
    where
        I: Input<Symbol = Self>,
    {
        pop.map(|ch: Self| ch.as_byte()).parse(input)
    }
}

#[derive(Debug, Clone)]
struct VerbatimParser<P, I>(P, PhantomData<fn() -> I>)
where
    P: AsRef<[core::primitive::u8]>,
    I: ByteInput;

impl<P, I> Parse<I> for VerbatimParser<P, I>
where
    P: AsRef<[core::primitive::u8]>,
    I: ByteInput,
{
    type Parsed = super::Span<I>;
    type Error = Error<I>;

    fn parse<N>(&self, input: N) -> PResult<Self::Parsed, I>
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        let mut expected = self.0.as_ref();
        let mut rem = input.clone();

        while let Some(ex) = expected.next() {
            let tmp = rem.clone();
            match rem.parse_byte() {
                Ok(Success(b, new_rem)) => {
                    if b != ex {
                        return Err(Failure(PError::invalid_input(tmp), input));
                    }
                    rem = new_rem;
                }
                Err(Failure(e, _)) => {
                    return Err(Failure(e, input));
                }
            }
        }

        Ok(Success(super::Span::new(input, rem.clone()), rem))
    }
}

#[inline]
pub const fn verbatim<P, I>(pattern: P) -> impl Parse<I, Parsed = super::Span<I>, Error = Error<I>>
where
    P: AsRef<[core::primitive::u8]>,
    I: ByteInput,
{
    VerbatimParser(pattern, PhantomData)
}

pub fn ascii_char<I: ByteInput>(input: I) -> PResult<crate::ascii::AsciiChar, I> {
    u8.try_map(|b| crate::ascii::AsciiChar::from_ascii(b).map_err(|_| ErrorKind::InvalidInput))
        .parse(input)
}

pub fn utf8_char<I: ByteInput>(input: I) -> PResult<char, I> {
    let Success(b0, rem) = input.clone().parse_byte()?;

    if let Some(ch) = char::from_u32(b0 as u32) {
        Ok(Success(ch, rem))
    } else if (b0 & 0b1110_0000) == 0b1100_0000 {
        let tmp = rem.clone();
        let (b1, rem) = match rem.parse_byte() {
            Ok(Success(b1, rem)) => (b1, rem),
            Err(Failure(e, _)) => {
                return Err(Failure(e, input.clone()));
            }
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_input(tmp), input));
        }
        let b0 = (b0 as u32) & 0b0001_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let ch = (b0 << 6) | b1;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_input(input.clone()), input))
        }
    } else if (b0 & 0b1111_0000) == 0b1110_0000 {
        let tmp = rem.clone();
        let (b1, rem) = match rem.parse_byte() {
            Ok(Success(b1, rem)) => (b1, rem),
            Err(Failure(e, _)) => {
                return Err(Failure(e, input.clone()));
            }
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_input(tmp), input));
        }
        let tmp = rem.clone();
        let (b2, rem) = match rem.parse_byte() {
            Ok(Success(b2, rem)) => (b2, rem),
            Err(Failure(e, _)) => {
                return Err(Failure(e, input.clone()));
            }
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_input(tmp), input));
        }
        let b0 = (b0 as u32) & 0b0000_1111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let ch = (b0 << 12) | (b1 << 6) | b2;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_input(input.clone()), input))
        }
    } else if (b0 & 0b1111_1000) == 0b1111_0000 {
        let tmp = rem.clone();
        let (b1, rem) = match rem.parse_byte() {
            Ok(Success(b1, rem)) => (b1, rem),
            Err(Failure(e, _)) => {
                return Err(Failure(e, input.clone()));
            }
        };
        if (b1 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_input(tmp), input));
        }
        let tmp = rem.clone();
        let (b2, rem) = match rem.parse_byte() {
            Ok(Success(b2, rem)) => (b2, rem),
            Err(Failure(e, _)) => {
                return Err(Failure(e, input.clone()));
            }
        };
        if (b2 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_input(tmp), input));
        }
        let tmp = rem.clone();
        let (b3, rem) = match rem.parse_byte() {
            Ok(Success(b3, rem)) => (b3, rem),
            Err(Failure(e, _)) => {
                return Err(Failure(e, input.clone()));
            }
        };
        if (b3 & 0b1100_0000) != 0b1000_0000 {
            return Err(Failure(Error::invalid_input(tmp), input));
        }
        let b0 = (b0 as u32) & 0b0000_0111;
        let b1 = (b1 as u32) & 0b0011_1111;
        let b2 = (b2 as u32) & 0b0011_1111;
        let b3 = (b3 as u32) & 0b0011_1111;
        let ch = (b0 << 18) | (b1 << 12) | (b2 << 6) | b3;
        if let Some(ch) = char::from_u32(ch) {
            Ok(Success(ch, rem))
        } else {
            Err(Failure(Error::invalid_input(input.clone()), input))
        }
    } else {
        Err(Failure(Error::invalid_input(input.clone()), input))
    }
}

pub fn u8<I: ByteInput>(input: I) -> PResult<core::primitive::u8, I> {
    I::parse_byte(input)
}

pub fn i8<I: ByteInput>(input: I) -> PResult<core::primitive::i8, I> {
    u8.map(|b| b as core::primitive::i8).parse(input)
}

pub mod be {
    use super::{u8, ByteInput, Error, ErrorKind, PResult};
    use crate::{Error as PError, Failure, Parse, Success};

    pub fn utf16_char<I: ByteInput>(input: I) -> PResult<char, I> {
        let Success(c0, rem) = u16.parse(input.clone())?;
        if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
            let tmp = rem.clone();
            let (c1, rem) = match u16.parse(input.clone()) {
                Ok(Success(c1, rem)) => (c1, rem),
                Err(Failure(e, _)) => {
                    return Err(Failure(e, input.clone()));
                }
            };
            if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
                return Err(Failure(Error::invalid_input(tmp), input.clone()));
            }
            let c0 = (c0 & 0b0000_0011_1111_1111) as core::primitive::u32;
            let c1 = (c1 & 0b0000_0011_1111_1111) as core::primitive::u32;
            if let Some(ch) = char::from_u32(((c0 << 10) | c1) + 0x10000) {
                Ok(Success(ch, rem))
            } else {
                Err(Failure(Error::invalid_input(input.clone()), input))
            }
        } else {
            if let Some(ch) = char::from_u32(c0 as core::primitive::u32) {
                Ok(Success(ch, rem))
            } else {
                Err(Failure(Error::invalid_input(input.clone()), input))
            }
        }
    }

    pub fn utf32_char<I: ByteInput>(input: I) -> PResult<char, I> {
        u32.try_map(|ch| char::from_u32(ch).ok_or(ErrorKind::InvalidInput))
            .parse(input)
    }

    pub fn u16<I: ByteInput>(input: I) -> PResult<core::primitive::u16, I> {
        u8.array()
            .map(core::primitive::u16::from_be_bytes)
            .parse(input)
    }

    pub fn u24<I: ByteInput>(input: I) -> PResult<core::primitive::u32, I> {
        u8.array()
            .map(|[b0, b1, b2]| core::primitive::u32::from_be_bytes([0, b0, b1, b2]))
            .parse(input)
    }

    pub fn u32<I: ByteInput>(input: I) -> PResult<core::primitive::u32, I> {
        u8.array()
            .map(core::primitive::u32::from_be_bytes)
            .parse(input)
    }

    pub fn u40<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4]| {
                core::primitive::u64::from_be_bytes([0, 0, 0, b0, b1, b2, b3, b4])
            })
            .parse(input)
    }

    pub fn u48<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5]| {
                core::primitive::u64::from_be_bytes([0, 0, b0, b1, b2, b3, b4, b5])
            })
            .parse(input)
    }

    pub fn u56<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6]| {
                core::primitive::u64::from_be_bytes([0, b0, b1, b2, b3, b4, b5, b6])
            })
            .parse(input)
    }

    pub fn u64<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(core::primitive::u64::from_be_bytes)
            .parse(input)
    }

    pub fn u72<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8]| {
                core::primitive::u128::from_be_bytes([
                    0, 0, 0, 0, 0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7, b8,
                ])
            })
            .parse(input)
    }

    pub fn u80<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]| {
                core::primitive::u128::from_be_bytes([
                    0, 0, 0, 0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
                ])
            })
            .parse(input)
    }

    pub fn u88<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]| {
                core::primitive::u128::from_be_bytes([
                    0, 0, 0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
                ])
            })
            .parse(input)
    }

    pub fn u96<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]| {
                core::primitive::u128::from_be_bytes([
                    0, 0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
                ])
            })
            .parse(input)
    }

    pub fn u104<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]| {
                core::primitive::u128::from_be_bytes([
                    0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
                ])
            })
            .parse(input)
    }

    pub fn u112<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]| {
                    core::primitive::u128::from_be_bytes([
                        0, 0, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
                    ])
                },
            )
            .parse(input)
    }

    pub fn u120<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]| {
                    core::primitive::u128::from_be_bytes([
                        0, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
                    ])
                },
            )
            .parse(input)
    }

    pub fn u128<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(core::primitive::u128::from_be_bytes)
            .parse(input)
    }

    pub fn i16<I: ByteInput>(input: I) -> PResult<core::primitive::i16, I> {
        u8.array()
            .map(core::primitive::i16::from_be_bytes)
            .parse(input)
    }

    pub fn i24<I: ByteInput>(input: I) -> PResult<core::primitive::i32, I> {
        u8.array()
            .map(|[b0, b1, b2]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i32::from_be_bytes([s, b0, b1, b2])
            })
            .parse(input)
    }

    pub fn i32<I: ByteInput>(input: I) -> PResult<core::primitive::i32, I> {
        u8.array()
            .map(core::primitive::i32::from_be_bytes)
            .parse(input)
    }

    pub fn i40<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i64::from_be_bytes([s, s, s, b0, b1, b2, b3, b4])
            })
            .parse(input)
    }

    pub fn i48<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i64::from_be_bytes([s, s, b0, b1, b2, b3, b4, b5])
            })
            .parse(input)
    }

    pub fn i56<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i64::from_be_bytes([s, b0, b1, b2, b3, b4, b5, b6])
            })
            .parse(input)
    }

    pub fn i64<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(core::primitive::i64::from_be_bytes)
            .parse(input)
    }

    pub fn i72<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_be_bytes([
                    s, s, s, s, s, s, s, b0, b1, b2, b3, b4, b5, b6, b7, b8,
                ])
            })
            .parse(input)
    }

    pub fn i80<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_be_bytes([
                    s, s, s, s, s, s, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
                ])
            })
            .parse(input)
    }

    pub fn i88<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_be_bytes([
                    s, s, s, s, s, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
                ])
            })
            .parse(input)
    }

    pub fn i96<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_be_bytes([
                    s, s, s, s, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
                ])
            })
            .parse(input)
    }

    pub fn i104<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]| {
                let s = if b0 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_be_bytes([
                    s, s, s, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
                ])
            })
            .parse(input)
    }

    pub fn i112<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]| {
                    let s = if b0 < 0x80 { 0 } else { 0xff };
                    core::primitive::i128::from_be_bytes([
                        s, s, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
                    ])
                },
            )
            .parse(input)
    }

    pub fn i120<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]| {
                    let s = if b0 < 0x80 { 0 } else { 0xff };
                    core::primitive::i128::from_be_bytes([
                        s, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
                    ])
                },
            )
            .parse(input)
    }

    pub fn i128<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(core::primitive::i128::from_be_bytes)
            .parse(input)
    }

    pub fn f32<I: ByteInput>(input: I) -> PResult<core::primitive::f32, I> {
        u8.array()
            .map(core::primitive::f32::from_be_bytes)
            .parse(input)
    }

    pub fn f64<I: ByteInput>(input: I) -> PResult<core::primitive::f64, I> {
        u8.array()
            .map(core::primitive::f64::from_be_bytes)
            .parse(input)
    }
}

pub mod le {
    use super::{u8, ByteInput, Error, ErrorKind, PResult};
    use crate::{Error as PError, Failure, Parse, Success};

    pub fn utf16_char<I: ByteInput>(input: I) -> PResult<char, I> {
        let Success(c0, rem) = u16.parse(input.clone())?;
        if (c0 & 0b1111_1100_0000_0000) == 0b1101_1000_0000_0000 {
            let tmp = rem.clone();
            let (c1, rem) = match u16.parse(input.clone()) {
                Ok(Success(c1, rem)) => (c1, rem),
                Err(Failure(e, _)) => {
                    return Err(Failure(e, input.clone()));
                }
            };
            if (c1 & 0b1111_1100_0000_0000) != 0b1101_1100_0000_0000 {
                return Err(Failure(Error::invalid_input(tmp), input.clone()));
            }
            let c0 = (c0 & 0b0000_0011_1111_1111) as core::primitive::u32;
            let c1 = (c1 & 0b0000_0011_1111_1111) as core::primitive::u32;
            if let Some(ch) = char::from_u32(((c0 << 10) | c1) + 0x10000) {
                Ok(Success(ch, rem))
            } else {
                Err(Failure(Error::invalid_input(input.clone()), input))
            }
        } else {
            if let Some(ch) = char::from_u32(c0 as core::primitive::u32) {
                Ok(Success(ch, rem))
            } else {
                Err(Failure(Error::invalid_input(input.clone()), input))
            }
        }
    }

    pub fn utf32_char<I: ByteInput>(input: I) -> PResult<char, I> {
        u32.try_map(|ch| char::from_u32(ch).ok_or(ErrorKind::InvalidInput))
            .parse(input)
    }

    pub fn u16<I: ByteInput>(input: I) -> PResult<core::primitive::u16, I> {
        u8.array()
            .map(core::primitive::u16::from_le_bytes)
            .parse(input)
    }

    pub fn u24<I: ByteInput>(input: I) -> PResult<core::primitive::u32, I> {
        u8.array()
            .map(|[b0, b1, b2]| core::primitive::u32::from_le_bytes([b0, b1, b2, 0]))
            .parse(input)
    }

    pub fn u32<I: ByteInput>(input: I) -> PResult<core::primitive::u32, I> {
        u8.array()
            .map(core::primitive::u32::from_le_bytes)
            .parse(input)
    }

    pub fn u40<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4]| {
                core::primitive::u64::from_le_bytes([b0, b1, b2, b3, b4, 0, 0, 0])
            })
            .parse(input)
    }

    pub fn u48<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5]| {
                core::primitive::u64::from_le_bytes([b0, b1, b2, b3, b4, b5, 0, 0])
            })
            .parse(input)
    }

    pub fn u56<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6]| {
                core::primitive::u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, 0])
            })
            .parse(input)
    }

    pub fn u64<I: ByteInput>(input: I) -> PResult<core::primitive::u64, I> {
        u8.array()
            .map(core::primitive::u64::from_le_bytes)
            .parse(input)
    }

    pub fn u72<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8]| {
                core::primitive::u128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, 0, 0, 0, 0, 0, 0, 0,
                ])
            })
            .parse(input)
    }

    pub fn u80<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]| {
                core::primitive::u128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, 0, 0, 0, 0, 0, 0,
                ])
            })
            .parse(input)
    }

    pub fn u88<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]| {
                core::primitive::u128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, 0, 0, 0, 0, 0,
                ])
            })
            .parse(input)
    }

    pub fn u96<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]| {
                core::primitive::u128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, 0, 0, 0, 0,
                ])
            })
            .parse(input)
    }

    pub fn u104<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]| {
                core::primitive::u128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, 0, 0, 0,
                ])
            })
            .parse(input)
    }

    pub fn u112<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]| {
                    core::primitive::u128::from_le_bytes([
                        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, 0, 0,
                    ])
                },
            )
            .parse(input)
    }

    pub fn u120<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]| {
                    core::primitive::u128::from_le_bytes([
                        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, 0,
                    ])
                },
            )
            .parse(input)
    }

    pub fn u128<I: ByteInput>(input: I) -> PResult<core::primitive::u128, I> {
        u8.array()
            .map(core::primitive::u128::from_le_bytes)
            .parse(input)
    }

    pub fn i16<I: ByteInput>(input: I) -> PResult<core::primitive::i16, I> {
        u8.array()
            .map(core::primitive::i16::from_le_bytes)
            .parse(input)
    }

    pub fn i24<I: ByteInput>(input: I) -> PResult<core::primitive::i32, I> {
        u8.array()
            .map(|[b0, b1, b2]| {
                let s = if b2 < 0x80 { 0 } else { 0xff };
                core::primitive::i32::from_le_bytes([b0, b1, b2, s])
            })
            .parse(input)
    }

    pub fn i32<I: ByteInput>(input: I) -> PResult<core::primitive::i32, I> {
        u8.array()
            .map(core::primitive::i32::from_le_bytes)
            .parse(input)
    }

    pub fn i40<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4]| {
                let s = if b4 < 0x80 { 0 } else { 0xff };
                core::primitive::i64::from_le_bytes([b0, b1, b2, b3, b4, s, s, s])
            })
            .parse(input)
    }

    pub fn i48<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5]| {
                let s = if b5 < 0x80 { 0 } else { 0xff };
                core::primitive::i64::from_le_bytes([b0, b1, b2, b3, b4, b5, s, s])
            })
            .parse(input)
    }

    pub fn i56<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6]| {
                let s = if b6 < 0x80 { 0 } else { 0xff };
                core::primitive::i64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, s])
            })
            .parse(input)
    }

    pub fn i64<I: ByteInput>(input: I) -> PResult<core::primitive::i64, I> {
        u8.array()
            .map(core::primitive::i64::from_le_bytes)
            .parse(input)
    }

    pub fn i72<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8]| {
                let s = if b8 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, s, s, s, s, s, s, s,
                ])
            })
            .parse(input)
    }

    pub fn i80<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]| {
                let s = if b9 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, s, s, s, s, s, s,
                ])
            })
            .parse(input)
    }

    pub fn i88<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]| {
                let s = if b10 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, s, s, s, s, s,
                ])
            })
            .parse(input)
    }

    pub fn i96<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]| {
                let s = if b11 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, s, s, s, s,
                ])
            })
            .parse(input)
    }

    pub fn i104<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(|[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]| {
                let s = if b12 < 0x80 { 0 } else { 0xff };
                core::primitive::i128::from_le_bytes([
                    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, s, s, s,
                ])
            })
            .parse(input)
    }

    pub fn i112<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]| {
                    let s = if b13 < 0x80 { 0 } else { 0xff };
                    core::primitive::i128::from_le_bytes([
                        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, s, s,
                    ])
                },
            )
            .parse(input)
    }

    pub fn i120<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(
                |[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]| {
                    let s = if b14 < 0x80 { 0 } else { 0xff };
                    core::primitive::i128::from_le_bytes([
                        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, s,
                    ])
                },
            )
            .parse(input)
    }

    pub fn i128<I: ByteInput>(input: I) -> PResult<core::primitive::i128, I> {
        u8.array()
            .map(core::primitive::i128::from_le_bytes)
            .parse(input)
    }

    pub fn f32<I: ByteInput>(input: I) -> PResult<core::primitive::f32, I> {
        u8.array()
            .map(core::primitive::f32::from_le_bytes)
            .parse(input)
    }

    pub fn f64<I: ByteInput>(input: I) -> PResult<core::primitive::f64, I> {
        u8.array()
            .map(core::primitive::f64::from_le_bytes)
            .parse(input)
    }
}

#[cfg(test)]
mod test {
    use super::ByteInput as Input;
    use super::*;
    use crate::{Parse, Success};

    fn ident<I: Input>(input: I) -> PResult<(), I> {
        regex!(r#"\p{XID_Start}\p{XID_Continue}*"#).parse(input)
    }

    #[test]
    fn regex() {
        assert!(ident.parse(b"hello world") == Ok(Success((), b" world")));
        assert!(ident.parse(b"hello_world") == Ok(Success((), b"")));
    }
}
