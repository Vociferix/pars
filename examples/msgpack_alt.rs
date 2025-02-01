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

fn msgpack<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .verify(|prefix| !matches!(*prefix, 0xc1 | 0xc7..0xca | 0xd4..0xd9))
        .flat_map(|prefix| {
            move |input: I| -> PResult<Object, I> {
                match prefix {
                    0x00..0x80 => pos_fix_int(prefix).parse(input),
                    0xe0..=0xff => neg_fix_int(prefix as i8).parse(input),
                    0xc0 => nil.parse(input),
                    0xc2 => bool_false.parse(input),
                    0xc3 => bool_true.parse(input),
                    0xcc => uint8.parse(input),
                    0xcd => uint16.parse(input),
                    0xce => uint32.parse(input),
                    0xcf => uint64.parse(input),
                    0xd0 => int8.parse(input),
                    0xd1 => int16.parse(input),
                    0xd2 => int32.parse(input),
                    0xd3 => int64.parse(input),
                    0xca => float32.parse(input),
                    0xcb => float64.parse(input),
                    0xa0..0xc0 => fix_str((prefix & 0x1f) as usize).parse(input),
                    0xd9 => str8.parse(input),
                    0xda => str16.parse(input),
                    0xdb => str32.parse(input),
                    0xc4 => bin8.parse(input),
                    0xc5 => bin16.parse(input),
                    0xc6 => bin32.parse(input),
                    0x90..0xa0 => fix_array((prefix & 0x0f) as usize).parse(input),
                    0xdc => array16.parse(input),
                    0xdd => array32.parse(input),
                    0x80..0x90 => fix_map((prefix & 0x0f) as usize).parse(input),
                    0xde => map16.parse(input),
                    0xdf => map32.parse(input),
                    _ => unreachable!(),
                }
            }
        })
        .parse(input)
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
