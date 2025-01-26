//! This example takes a MessagePack byte stream from stdin,
//! parses it, and prints the parsed value as JSON.

use pars::bytes::{self, ByteInput as BInput, ErrorKind, PResult};
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
    bytes::verbatim(b"\xc0").with(|| Object::Nil).parse(input)
}

fn bool_false<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::verbatim(b"\xc2")
        .with(|| Object::Bool(false))
        .parse(input)
}

fn bool_true<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::verbatim(b"\xc3")
        .with(|| Object::Bool(true))
        .parse(input)
}

fn pos_fixint<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .try_map(|b| {
            if (b & 0x80) == 0 {
                Ok(Object::UInt(b as u64))
            } else {
                Err(ErrorKind::InvalidInput)
            }
        })
        .parse(input)
}

fn neg_fixint<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .try_map(|b| {
            if (b & 0xe0) == 0xe0 {
                Ok(Object::Int((b as i8) as i64))
            } else {
                Err(ErrorKind::InvalidInput)
            }
        })
        .parse(input)
}

fn uint8<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xcc"),
        bytes::u8.map(|val| Object::UInt(val as u64)),
    )
    .parse(input)
}

fn uint16<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xcd"),
        bytes::be::u16.map(|val| Object::UInt(val as u64)),
    )
    .parse(input)
}

fn uint32<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xce"),
        bytes::be::u32.map(|val| Object::UInt(val as u64)),
    )
    .parse(input)
}

fn uint64<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xcf"), bytes::be::u64.map(Object::UInt)).parse(input)
}

fn int8<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xd0"),
        bytes::i8.map(|val| Object::Int(val as i64)),
    )
    .parse(input)
}

fn int16<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xd1"),
        bytes::be::i16.map(|val| Object::Int(val as i64)),
    )
    .parse(input)
}

fn int32<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xd2"),
        bytes::be::i32.map(|val| Object::Int(val as i64)),
    )
    .parse(input)
}

fn int64<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xd3"), bytes::be::i64.map(Object::Int)).parse(input)
}

fn float32<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(
        bytes::verbatim(b"\xca"),
        bytes::be::f32.map(|val| Object::Float(val as f64)),
    )
    .parse(input)
}

fn float64<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xcb"), bytes::be::f64.map(Object::Float)).parse(input)
}

fn fixstr<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .try_map(|b| {
            if (b & 0b1110_0000) == 0b1010_0000 {
                Ok((b & 0b0001_1111) as usize)
            } else {
                Err(ErrorKind::InvalidInput)
            }
        })
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

fn str8<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xd9"), bytes::u8.map(|b| b as usize))
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
    prefix(bytes::verbatim(b"\xda"), bytes::be::u16.map(|b| b as usize))
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
    prefix(bytes::verbatim(b"\xdb"), bytes::be::u32.map(|b| b as usize))
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
    prefix(bytes::verbatim(b"\xc4"), bytes::u8.map(|b| b as usize))
        .flat_map(|len| bytes::u8.collect_repeated(len).map(Object::Bytes))
        .parse(input)
}

fn bin16<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xc5"), bytes::be::u16.map(|b| b as usize))
        .flat_map(|len| bytes::u8.collect_repeated(len).map(Object::Bytes))
        .parse(input)
}

fn bin32<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xc6"), bytes::be::u32.map(|b| b as usize))
        .flat_map(|len| bytes::u8.collect_repeated(len).map(Object::Bytes))
        .parse(input)
}

fn fixarray<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .try_map(|b| {
            if (b & 0b1111_0000) == 0b1001_0000 {
                Ok((b & 0b0000_1111) as usize)
            } else {
                Err(ErrorKind::InvalidInput)
            }
        })
        .flat_map(|len| msgpack.collect_repeated(len).map(Object::Array))
        .parse(input)
}

fn array16<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xdc"), bytes::be::u16.map(|b| b as usize))
        .flat_map(|len| msgpack.collect_repeated(len).map(Object::Array))
        .parse(input)
}

fn array32<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xdd"), bytes::be::u32.map(|b| b as usize))
        .flat_map(|len| msgpack.collect_repeated(len).map(Object::Array))
        .parse(input)
}

fn fixmap<I: BInput>(input: I) -> PResult<Object, I> {
    bytes::u8
        .try_map(|b| {
            if (b & 0b1111_0000) == 0b1000_0000 {
                Ok((b & 0b0000_1111) as usize)
            } else {
                Err(ErrorKind::InvalidInput)
            }
        })
        .flat_map(|len| msgpack.then(msgpack).collect_repeated(len).map(Object::Map))
        .parse(input)
}

fn map16<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xde"), bytes::be::u16.map(|b| b as usize))
        .flat_map(|len| msgpack.then(msgpack).collect_repeated(len).map(Object::Map))
        .parse(input)
}

fn map32<I: BInput>(input: I) -> PResult<Object, I> {
    prefix(bytes::verbatim(b"\xdf"), bytes::be::u32.map(|b| b as usize))
        .flat_map(|len| msgpack.then(msgpack).collect_repeated(len).map(Object::Map))
        .parse(input)
}

fn msgpack<I: BInput>(input: I) -> PResult<Object, I> {
    alt!(
        nil, bool_false, bool_true, pos_fixint, neg_fixint, uint8, uint16, uint32, uint64, int8,
        int16, int32, int64, float32, float64, fixstr, str8, str16, str32, bin8, bin16, bin32,
        fixarray, array16, array32, fixmap, map16, map32,
    )
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
