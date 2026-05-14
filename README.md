# pars

[![CI](https://github.com/Vociferix/pars/actions/workflows/ci.yml/badge.svg)](https://github.com/Vociferix/pars/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/pars.svg)](https://crates.io/crates/pars)
[![docs.rs](https://img.shields.io/docsrs/pars)](https://docs.rs/pars)
[![codecov](https://codecov.io/gh/Vociferix/pars/graph/badge.svg)](https://codecov.io/gh/Vociferix/pars)

`pars` is a parser-combinator library for Rust with first-class Unicode and
regex support, designed to be ergonomic, flexible, and `no_std`-compatible.

## Why pars?

Parser-combinator crates in the Rust ecosystem — notably
[`nom`](https://crates.io/crates/nom) and
[`winnow`](https://crates.io/crates/winnow) — are excellent choices for many
parsing tasks. `pars` takes a different approach in a few key areas:

- **Generalized input** — Parsers are generic over any type implementing the
  `Input` trait, not just bytes or strings. The same combinators work whether
  you are parsing raw bytes, Unicode text, or a custom token stream from a
  lexer.

- **Unicode out of the box** — The `unicode` module includes extended grapheme
  cluster segmentation per [UAX #29](https://www.unicode.org/reports/tr29/),
  Unicode-aware line breaking, and character property matching backed by ICU
  data tables. Unicode is not an afterthought layered on top of byte parsers.

- **Compile-time regex** — The `regex!` macro compiles a regular expression
  into a finite state machine at compile time. The resulting parser is
  zero-cost at runtime and composes naturally with other combinators via
  `.recognize()`, `.map()`, and friends.

- **Ergonomic combinator API** — Method chaining on the `ParseExt` trait
  (`.map()`, `.recognize()`, `.opt()`, `.repeated(..)`, `.verify()`, etc.)
  produces readable, composable parsers without macro-heavy syntax.

- **`no_std` support** — The entire library works without the standard
  library. Heap allocation is gated behind the optional `alloc` feature.

## Quick Example

```rust
use pars::prelude::*;
use pars::ErrorKind;
use pars::basic::prefix;
use pars::unicode::{
    strict::{char, verbatim},
    UnicodeInput, PResult,
};

#[derive(Debug, PartialEq)]
struct Color { red: u8, green: u8, blue: u8 }

fn hex_digit<I: UnicodeInput>(input: I) -> PResult<u8, I> {
    char.try_map(|ch| match ch {
        '0'..='9' => Ok((ch as u8) - b'0'),
        'a'..='f' => Ok((ch as u8) - b'a' + 10),
        'A'..='F' => Ok((ch as u8) - b'A' + 10),
        _ => Err(ErrorKind::InvalidInput),
    }).parse(input)
}

fn hex_byte<I: UnicodeInput>(input: I) -> PResult<u8, I> {
    hex_digit.array().map(|[d0, d1]| (d0 << 4) | d1).parse(input)
}

fn hex_color<I: UnicodeInput>(input: I) -> PResult<Color, I> {
    prefix(verbatim("#"), hex_byte.array())
        .map(|[r, g, b]| Color { red: r, green: g, blue: b })
        .parse(input)
}

assert_eq!(
    hex_color.parse("#2F14DF"),
    Ok(Success(Color { red: 0x2f, green: 0x14, blue: 0xdf }, ""))
);
```

## Modules

| Module | Description |
|---|---|
| `basic` | Core combinators: `alt!`, `seq!`, `map`, `opt`, `repeated`, `recognize`, and more |
| `bytes` | Byte stream parsers: big- and little-endian integers, UTF-8/16/32 characters, and regex |
| `ascii` | ASCII parsers, available in `strict` (error on non-ASCII) and `lossy` (substitute) variants |
| `unicode` | Unicode parsers with grapheme cluster segmentation, line breaking, character properties, and regex |

## Crate Features

| Feature | Default | Description |
|---|---|---|
| `alloc` | ✓ | Enable heap-allocated types |
| `ascii` | ✓ | Enable the `ascii` module |
| `bytes` | ✓ | Enable the `bytes` module |
| `unicode` | ✓ | Enable the `unicode` module |
| `nightly` | | Enable nightly-only optimizations |

## Examples

Complete example programs are available in the [`examples/`](examples/) directory:

- [`arithmetic.rs`](examples/arithmetic.rs) — A recursive-descent arithmetic expression parser and interpreter
- [`msgpack.rs`](examples/msgpack.rs) — A [MessagePack](https://msgpack.org) binary format reader with zero backtracking

## License

Licensed under either of [Apache License 2.0](LICENSE-APACHE) or [MIT License](LICENSE-MIT) at your option.
