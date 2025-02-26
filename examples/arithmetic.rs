//! This example implements an arithmetic expression parser.
//!
//! When the program is run, there will be a prompt. Enter any
//! basic arithmetic expression, and the result will be printed.
//!
//! Operators:
//! In the following, `n` and `m` are placeholders for numbers.
//! * `+n`    - Identity
//! * `-n`    - Negation
//! * `n + m` - Addition
//! * `n - m` - Subtraction
//! * `n * m` - Multiplication
//! * `n / m` - Division (integer)
//! * `n % m` - Remainder
//!
//! Operators follow standard precedence rules. Parentheses may
//! also be used to explicity specify precedence.
//!
//! Numbers are signed 64-bit integers. As this is just an
//! example, there are no overflow checks. An expression or
//! literal that overflows a 64-bit integer will crash the
//! program.

use pars::prelude::*;
use pars::unicode::{
    strict::{char as uchar, regex},
    Error, PResult, UnicodeInput as UInput,
};

fn ws<I: UInput>(input: I) -> PResult<(), I> {
    /*
    // Alternative without using `regex!`
    uchar
        .verify(|ch: &char| ch.is_whitespace())
        .many0(|_| ())
    */
    regex!(r"\s*").parse(input)
}

const fn ws_delim<P, I>(parser: P) -> impl Parse<I, Parsed = P::Parsed, Error = Error<I>>
where
    P: Parse<I, Error = Error<I>>,
    I: UInput,
{
    prefix(ws, parser)
}

fn digit<I: UInput>(input: I) -> PResult<i64, I> {
    uchar
        .verify(|ch: &char| *ch >= '0' && *ch <= '9')
        .map(|ch| ((ch as u32 as u8) - b'0') as i64)
        .parse(input)
}

fn number<I: UInput>(input: I) -> PResult<i64, I> {
    ws_delim(digit.many1(|iter| -> i64 {
        let mut ret = 0i64;
        for d in iter {
            ret = (ret * 10) + d;
        }
        ret
    }))
    .parse(input)
}

#[derive(Debug, Clone, Copy)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl Op {
    fn calc(self, lhs: i64, rhs: i64) -> i64 {
        match self {
            Op::Add => lhs + rhs,
            Op::Sub => lhs - rhs,
            Op::Mul => lhs * rhs,
            Op::Div => lhs / rhs,
            Op::Mod => lhs % rhs,
        }
    }
}

fn plus<I: UInput>(input: I) -> PResult<Op, I> {
    ws_delim(uchar.verify(|ch| *ch == '+').with_value(Op::Add)).parse(input)
}

fn minus<I: UInput>(input: I) -> PResult<Op, I> {
    ws_delim(uchar.verify(|ch| *ch == '-').with_value(Op::Sub)).parse(input)
}

fn mult<I: UInput>(input: I) -> PResult<Op, I> {
    ws_delim(uchar.verify(|ch| *ch == '*').with_value(Op::Mul)).parse(input)
}

fn div<I: UInput>(input: I) -> PResult<Op, I> {
    ws_delim(uchar.verify(|ch| *ch == '/').with_value(Op::Div)).parse(input)
}

fn modulus<I: UInput>(input: I) -> PResult<Op, I> {
    ws_delim(uchar.verify(|ch| *ch == '%').with_value(Op::Mod)).parse(input)
}

fn lparen<I: UInput>(input: I) -> PResult<(), I> {
    ws_delim(uchar.verify(|ch| *ch == '(').with_value(())).parse(input)
}

fn rparen<I: UInput>(input: I) -> PResult<(), I> {
    ws_delim(uchar.verify(|ch| *ch == ')').with_value(())).parse(input)
}

fn primary_expr<I: UInput>(input: I) -> PResult<i64, I> {
    alt!(number, delimited(lparen, expr, rparen)).parse(input)
}

fn unary_expr<I: UInput>(input: I) -> PResult<i64, I> {
    alt!(
        prefix(plus, unary_expr),
        prefix(minus, unary_expr).map(|val| -val),
        primary_expr,
    )
    .parse(input)
}

fn term_expr<I: UInput>(input: I) -> PResult<i64, I> {
    unary_expr
        .flat_map(|init: i64| {
            seq!(alt!(mult, div, modulus), unary_expr).many0(move |iter| {
                let mut ret = init;
                for (op, val) in iter {
                    ret = op.calc(ret, val);
                }
                ret
            })
        })
        .parse(input)
}

fn expr<I: UInput>(input: I) -> PResult<i64, I> {
    term_expr
        .flat_map(|init: i64| {
            seq!(alt!(plus, minus), term_expr).many0(move |iter| {
                let mut ret = init;
                for (op, val) in iter {
                    ret = op.calc(ret, val);
                }
                ret
            })
        })
        .parse(input)
}

fn eval<I>(input: I) -> Result<i64, Error<I::Input>>
where
    I: IntoInput,
    I::Input: UInput,
{
    suffix(expr, ws).complete().parse(input).extract().0
}

fn main() -> std::io::Result<()> {
    use std::io::BufRead;
    use std::io::Write;

    let mut out = std::io::stdout();
    write!(out, "Enter 'q', 'quit', or 'exit' to exit.\n")?;
    write!(out, "> ")?;
    out.flush()?;

    for input in std::io::stdin().lock().lines() {
        let input = input?;

        if input == "q" || input == "quit" || input == "exit" {
            break;
        }

        if input.trim().is_empty() {
            write!(out, "> ")?;
            out.flush()?;
            continue;
        }

        if let Ok(value) = eval(&input) {
            write!(out, "{value}\n")?;
        } else {
            write!(out, "invalid expression\n")?;
        }

        write!(out, "> ")?;
        out.flush()?;
    }

    Ok(())
}
