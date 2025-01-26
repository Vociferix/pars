//! This example takes a MessagePack byte stream from stdin,
//! parses it, and prints the parsed value as JSON.
//!
//! The difference between the `msgpack` example and this
//! one (`msgpack_alt`) is that this one is guaranteed to
//! never backtrack at the cost of a slightly more complex
//! implementation. Benchmarks will usually show that
//! `msgpack_alt` is marginally faster in release mode.
//!
//! Compare with hyperfine:
//! ```sh
//! $ cargo build --release --example msgpack
//! $ cargo build --release --example msgpack_alt
//! $ hyperfine -N --input <msgpack-file> --warmup 1000 \
//!       ./target/release/examples/msgpack             \
//!       ./target/release/examples/msgpack_alt
//! ```

use pars::bytes::{self, ByteInput as BInput, Error, ErrorKind, PResult};
use pars::prelude::*;
use std::cmp::Ordering;
use std::collections::BTreeMap;

// NOTE: Extension types not supported
#[derive(Debug, Clone, PartialEq, PartialOrd)]
enum Object {
    Nil,
    Bool(bool),
    Int(i64),
    UInt(u64),
    Float(f64),
    String(String),
    Bytes(Vec<u8>),
    Array(Vec<Object>),
    Map(BTreeMap<Object, Object>),
}

impl Eq for Object {}

impl Ord for Object {
    fn cmp(&self, other: &Self) -> Ordering {
        match PartialOrd::partial_cmp(self, other) {
            Some(ord) => ord,
            None => Ordering::Equal,
        }
    }
}

impl std::fmt::Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Nil => f.write_str("null"),
            Self::Bool(val) => f.write_str(if *val { "true" } else { "false" }),
            Self::Int(val) => write!(f, "{val}"),
            Self::UInt(val) => write!(f, "{val}"),
            Self::Float(val) => write!(f, "{val}"),
            Self::String(val) => write!(f, "{:?}", &val[..]),
            Self::Bytes(val) => {
                f.write_str("[")?;
                let mut first = true;
                for elem in val.iter() {
                    if first {
                        first = false;
                    } else {
                        f.write_str(",")?;
                    }
                    write!(f, "{elem}")?;
                }
                f.write_str("]")
            }
            Self::Array(val) => {
                f.write_str("[")?;
                let mut first = true;
                for elem in val.iter() {
                    if first {
                        first = false;
                    } else {
                        f.write_str(",")?;
                    }
                    write!(f, "{elem}")?;
                }
                f.write_str("]")
            }
            Self::Map(val) => {
                f.write_str("{")?;
                let mut first = true;
                for (k, v) in val.iter() {
                    if first {
                        first = false;
                    } else {
                        f.write_str(",")?;
                    }
                    write!(f, "{k}:{v}")?;
                }
                f.write_str("}")
            }
        }
    }
}

fn nil<I: BInput>(input: I) -> PResult<Object, I> {
    constant(|| Object::Nil).parse(input)
}

fn bool_false<I: BInput>(input: I) -> PResult<Object, I> {
    constant(|| Object::Bool(false)).parse(input)
}

fn bool_true<I: BInput>(input: I) -> PResult<Object, I> {
    constant(|| Object::Bool(true)).parse(input)
}

fn pos_fix_int<I: BInput>(value: u8) -> impl Parse<I, Parsed = Object, Error = Error<I>> {
    constant(move || Object::UInt(value as u64))
}

fn neg_fix_int<I: BInput>(value: i8) -> impl Parse<I, Parsed = Object, Error = Error<I>> {
    constant(move || Object::Int(value as i64))
}

fn uint8<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8.map(|val| Object::UInt(val as u64)).parse(input)
}

fn uint16<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u16
        .map(|val| Object::UInt(val as u64))
        .parse(input)
}

fn uint32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u32
        .map(|val| Object::UInt(val as u64))
        .parse(input)
}

fn uint64<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u64.map(Object::UInt).parse(input)
}

fn int8<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::i8.map(|val| Object::Int(val as i64)).parse(input)
}

fn int16<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::i16
        .map(|val| Object::Int(val as i64))
        .parse(input)
}

fn int32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::i32
        .map(|val| Object::Int(val as i64))
        .parse(input)
}

fn int64<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::i64.map(Object::Int).parse(input)
}

fn float32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::f32
        .map(|val| Object::Float(val as f64))
        .parse(input)
}

fn float64<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::f64.map(Object::Float).parse(input)
}

fn fix_str<I: BInput>(len: usize) -> impl Parse<I, Parsed = Object, Error = Error<I>> {
    bytes::u8
        .collect_repeated(len)
        .try_map(|s: Vec<u8>| match String::from_utf8(s) {
            Ok(s) => Ok(Object::String(s)),
            Err(_) => Err(ErrorKind::InvalidInput),
        })
}

fn str8<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .map(|b| b as usize)
        .flat_map(|len| {
            bytes::u8
                .collect_repeated(len)
                .try_map(|s: Vec<u8>| match String::from_utf8(s) {
                    Ok(s) => Ok(Object::String(s)),
                    Err(_) => Err(ErrorKind::InvalidInput),
                })
        })
        .parse(input)
}

fn str16<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u16
        .map(|b| b as usize)
        .flat_map(|len| {
            bytes::u8
                .collect_repeated(len)
                .try_map(|s: Vec<u8>| match String::from_utf8(s) {
                    Ok(s) => Ok(Object::String(s)),
                    Err(_) => Err(ErrorKind::InvalidInput),
                })
        })
        .parse(input)
}

fn str32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u32
        .map(|b| b as usize)
        .flat_map(|len| {
            bytes::u8
                .collect_repeated(len)
                .try_map(|s: Vec<u8>| match String::from_utf8(s) {
                    Ok(s) => Ok(Object::String(s)),
                    Err(_) => Err(ErrorKind::InvalidInput),
                })
        })
        .parse(input)
}

fn bin8<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .map(|b| b as usize)
        .flat_map(|len| bytes::u8.collect_repeated(len).map(Object::Bytes))
        .parse(input)
}

fn bin16<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u16
        .map(|b| b as usize)
        .flat_map(|len| bytes::u8.collect_repeated(len).map(Object::Bytes))
        .parse(input)
}

fn bin32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u32
        .map(|b| b as usize)
        .flat_map(|len| bytes::u8.collect_repeated(len).map(Object::Bytes))
        .parse(input)
}

fn fix_array<I: BInput>(len: usize) -> impl Parse<I, Parsed = Object, Error = Error<I>> {
    msgpack.collect_repeated(len).map(Object::Array)
}

fn array16<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u16
        .map(|b| b as usize)
        .flat_map(|len| msgpack.collect_repeated(len).map(Object::Array))
        .parse(input)
}

fn array32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u32
        .map(|b| b as usize)
        .flat_map(|len| msgpack.collect_repeated(len).map(Object::Array))
        .parse(input)
}

fn fix_map<I: BInput>(len: usize) -> impl Parse<I, Parsed = Object, Error = Error<I>> {
    msgpack.then(msgpack).collect_repeated(len).map(Object::Map)
}

fn map16<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u16
        .map(|b| b as usize)
        .flat_map(|len| msgpack.then(msgpack).collect_repeated(len).map(Object::Map))
        .parse(input)
}

fn map32<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::be::u32
        .map(|b| b as usize)
        .flat_map(|len| msgpack.then(msgpack).collect_repeated(len).map(Object::Map))
        .parse(input)
}

#[derive(Debug, Clone, Copy)]
enum Prefix {
    Nil,
    BoolFalse,
    BoolTrue,
    PosFixInt(u8),
    NegFixInt(i8),
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Int8,
    Int16,
    Int32,
    Int64,
    Float32,
    Float64,
    FixStr(usize),
    Str8,
    Str16,
    Str32,
    Bin8,
    Bin16,
    Bin32,
    FixArray(usize),
    Array16,
    Array32,
    FixMap(usize),
    Map16,
    Map32,
}

impl<I: BInput> Parse<I> for Prefix {
    type Parsed = Object;
    type Error = Error<I>;

    fn parse<N>(&self, input: N) -> PResult<Object, I>
    where
        N: IntoInput<Input = I>,
    {
        match self {
            Self::Nil => nil.parse(input),
            Self::BoolFalse => bool_false.parse(input),
            Self::BoolTrue => bool_true.parse(input),
            Self::PosFixInt(val) => pos_fix_int(*val).parse(input),
            Self::NegFixInt(val) => neg_fix_int(*val).parse(input),
            Self::UInt8 => uint8.parse(input),
            Self::UInt16 => uint16.parse(input),
            Self::UInt32 => uint32.parse(input),
            Self::UInt64 => uint64.parse(input),
            Self::Int8 => int8.parse(input),
            Self::Int16 => int16.parse(input),
            Self::Int32 => int32.parse(input),
            Self::Int64 => int64.parse(input),
            Self::Float32 => float32.parse(input),
            Self::Float64 => float64.parse(input),
            Self::FixStr(len) => fix_str(*len).parse(input),
            Self::Str8 => str8.parse(input),
            Self::Str16 => str16.parse(input),
            Self::Str32 => str32.parse(input),
            Self::Bin8 => bin8.parse(input),
            Self::Bin16 => bin16.parse(input),
            Self::Bin32 => bin32.parse(input),
            Self::FixArray(len) => fix_array(*len).parse(input),
            Self::Array16 => array16.parse(input),
            Self::Array32 => array32.parse(input),
            Self::FixMap(len) => fix_map(*len).parse(input),
            Self::Map16 => map16.parse(input),
            Self::Map32 => map32.parse(input),
        }
    }
}

fn prefix<I: BInput>(input: I) -> PResult<Prefix, I> {
    bytes::u8
        .try_map(|b| match b {
            0x00..0x80 => Ok(Prefix::PosFixInt(b)),
            0xe0..=0xff => Ok(Prefix::NegFixInt(b as i8)),
            0xc0 => Ok(Prefix::Nil),
            0xc2 => Ok(Prefix::BoolFalse),
            0xc3 => Ok(Prefix::BoolTrue),
            0xcc => Ok(Prefix::UInt8),
            0xcd => Ok(Prefix::UInt16),
            0xce => Ok(Prefix::UInt32),
            0xcf => Ok(Prefix::UInt64),
            0xd0 => Ok(Prefix::Int8),
            0xd1 => Ok(Prefix::Int16),
            0xd2 => Ok(Prefix::Int32),
            0xd3 => Ok(Prefix::Int64),
            0xca => Ok(Prefix::Float32),
            0xcb => Ok(Prefix::Float64),
            0xa0..0xc0 => Ok(Prefix::FixStr((b & 0x1f) as usize)),
            0xd9 => Ok(Prefix::Str8),
            0xda => Ok(Prefix::Str16),
            0xdb => Ok(Prefix::Str32),
            0xc4 => Ok(Prefix::Bin8),
            0xc5 => Ok(Prefix::Bin16),
            0xc6 => Ok(Prefix::Bin32),
            0x90..0xa0 => Ok(Prefix::FixArray((b & 0xf) as usize)),
            0xdc => Ok(Prefix::Array16),
            0xdd => Ok(Prefix::Array32),
            0x80..0x90 => Ok(Prefix::FixMap((b & 0xf) as usize)),
            0xde => Ok(Prefix::Map16),
            0xdf => Ok(Prefix::Map32),
            _ => Err(ErrorKind::InvalidInput),
        })
        .parse(input)
}

fn msgpack<I: BInput>(input: I) -> PResult<Object, I> {
    prefix.flat_map(|p| p).parse(input)
}

fn main() -> std::io::Result<()> {
    use std::io::Read;
    let mut input = Vec::new();
    std::io::stdin().lock().read_to_end(&mut input)?;
    let Ok(pars::Success(obj, _)) = msgpack.parse(&input) else {
        return Err(std::io::ErrorKind::InvalidData.into());
    };
    println!("{obj}");
    Ok(())
}
