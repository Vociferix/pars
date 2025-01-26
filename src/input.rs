use crate::{Parse, Success};

/// A parsable symbol stream.
///
/// [`Input`] is very similar to [`Iterator`]. The key difference is that a type
/// implementing [`Input`] must support multiple and partial passes in any
/// combination. `pars` implements recursive descent parsing, which means that
/// there is no limit to the number of symbols the parser may consume before
/// determining that it needs to backtrack (although individual parsers may have
/// a finite bound).
///
/// As such, [`Input`] is essentially an [`Iterator`] that can be cloned and can
/// be compared with clones for positional equality.
pub trait Input: Clone {
    /// The symbol type this input provides a stream of.
    type Symbol;

    /// Gets the next symbol in the stream.
    ///
    /// [`None`] indicates that the end of the input has been reached.
    fn next(&mut self) -> Option<Self::Symbol>;

    /// Compares the position of two inputs for positional equality.
    ///
    /// If both inputs are at the same position of the stream, `true` is
    /// returned, `false` otherwise.
    fn pos_eq(&self, other: &Self) -> bool;

    /// Advances the stream by a given number of symbols.
    ///
    /// The number of skipped symbols is returned, which should always be equal
    /// to `count`, unless the remaining input was less than `count` symbols.
    /// If the returned value is not equal to `count`, the input must now be
    /// at the end of input.
    ///
    /// Implementors may wish to customize this method to provide a more
    /// performant implementation than calling [`next`](Input::next) `count`
    /// times.
    fn advance_by(&mut self, count: usize) -> usize {
        for idx in 0..count {
            let Some(_) = self.next() else {
                return idx;
            };
        }
        count
    }

    /// Returns the remaining number of symbols, if known.
    ///
    /// Not all input streams can easily know how many symbols they contain,
    /// but when it is known, some parsers can use that information for
    /// optimization.
    ///
    /// It is recommended that implementors customize this method if the
    /// remaining size of the stream can be computed in constant time.
    fn size_hint(&self) -> Option<usize> {
        None
    }

    /// Returns `true` if the stream is at the end of input.
    ///
    /// Implementors may wish to customize this method to provide a more
    /// performant implementation. The default implementation clones the
    /// input and checks if calling [`next`](Input::next) yeilds a value.
    fn is_empty(&self) -> bool {
        self.clone().next().is_none()
    }

    /// Creates a new input stream with mapped values.
    ///
    /// The provided function or closure will be used by the returned
    /// stream to transform symbols of the original stream.
    fn map<F, O>(self, map_fn: F) -> impl Input<Symbol = O>
    where
        F: Clone + Fn(Self::Symbol) -> O,
    {
        struct Map<I, F, O>(I, F, core::marker::PhantomData<O>);

        impl<I: Clone, F: Clone, O> Clone for Map<I, F, O> {
            fn clone(&self) -> Self {
                Self(self.0.clone(), self.1.clone(), core::marker::PhantomData)
            }
        }

        impl<I, F, O> Input for Map<I, F, O>
        where
            I: Input,
            F: Clone + Fn(I::Symbol) -> O,
        {
            type Symbol = O;

            fn next(&mut self) -> Option<Self::Symbol> {
                self.0.next().map(&self.1)
            }

            fn pos_eq(&self, other: &Self) -> bool {
                self.0.pos_eq(&other.0)
            }

            fn advance_by(&mut self, count: usize) -> usize {
                self.0.advance_by(count)
            }

            fn size_hint(&self) -> Option<usize> {
                self.0.size_hint()
            }
        }

        Map(self, map_fn, core::marker::PhantomData)
    }
}

/// Trait for types that can be directly converted into an [`Input`] type.
///
/// [`IntoInput`] is analogous to [`IntoIterator`]. For example, `&[u8]`
/// implements [`Input`], but [`Vec<u8>`](alloc::vec::Vec) does not. However,
/// [`&Vec<u8>`](alloc::vec::Vec) implements [`IntoInput`] and will convert
/// to [`&[u8]`].
///
/// The [`Parse::parse`] function accepts a type implementing [`IntoInput`]
/// for convenience. So given `let my_input: Vec<u8>;`,
/// `my_parser.parse(&my_input)` works without needing to explicitly
/// convert the [`Vec`](alloc::vec::Vec) into a slice.
pub trait IntoInput {
    /// The symbol type of the [`Input`] this type will convert to.
    type Symbol;

    /// The [`Input`] this type will convert to.
    type Input: Input<Symbol = Self::Symbol>;

    /// Convert to an [`Input`] type.
    fn into_input(self) -> Self::Input;
}

/// Input derived from other input by repeatedly applying a parser.
///
/// [`ParsedInput`] consists of an underlying input and a parser.
/// Each symbol produced by a [`ParsedInput`] is produced by applying
/// the parser to the inner input. After parsing a symbol, the inner
/// input becomes the remaining unparsed inner input. The [`ParsedInput`]
/// ends when parsing a symbol fails.
#[derive(Debug, Clone)]
pub struct ParsedInput<P, I>
where
    P: Parse<I> + Clone,
    I: Input,
{
    parser: P,
    input: Option<I>,
}

impl<T: Copy> Input for &[T] {
    type Symbol = T;

    fn next(&mut self) -> Option<Self::Symbol> {
        if let Some((head, tail)) = self.split_at_checked(1) {
            *self = tail;
            head.first().copied()
        } else {
            None
        }
    }

    fn pos_eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }

    fn advance_by(&mut self, count: usize) -> usize {
        let count = core::cmp::min(self.len(), count);
        *self = &self[count..];
        count
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.len())
    }

    fn is_empty(&self) -> bool {
        <[T]>::is_empty(*self)
    }
}

impl Input for &str {
    type Symbol = char;

    fn next(&mut self) -> Option<Self::Symbol> {
        let mut chars = self.chars();
        let ret = chars.next();
        *self = chars.as_str();
        ret
    }

    fn pos_eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }

    fn is_empty(&self) -> bool {
        str::is_empty(*self)
    }
}

#[cfg(feature = "ascii")]
impl Input for &crate::ascii::AsciiStr {
    type Symbol = crate::ascii::AsciiChar;

    fn next(&mut self) -> Option<Self::Symbol> {
        let mut chars = self.chars();
        let ret = chars.next();
        *self = chars.as_str();
        ret
    }

    fn pos_eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }

    fn is_empty(&self) -> bool {
        ascii::AsciiStr::is_empty(*self)
    }
}

impl<I: Input> IntoInput for I {
    type Symbol = <I as Input>::Symbol;
    type Input = I;

    fn into_input(self) -> Self::Input {
        self
    }
}

impl<'a, T: Copy, const LEN: usize> IntoInput for &'a [T; LEN] {
    type Symbol = T;
    type Input = &'a [T];

    fn into_input(self) -> Self::Input {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: Copy> IntoInput for &'a alloc::vec::Vec<T> {
    type Symbol = T;
    type Input = &'a [T];

    fn into_input(self) -> &'a [T] {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: Copy> IntoInput for &'a alloc::boxed::Box<[T]> {
    type Symbol = T;
    type Input = &'a [T];

    fn into_input(self) -> &'a [T] {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> IntoInput for &'a alloc::boxed::Box<str> {
    type Symbol = char;
    type Input = &'a str;

    fn into_input(self) -> &'a str {
        self
    }
}

#[cfg(all(feature = "alloc", feature = "ascii"))]
impl<'a> IntoInput for &'a alloc::boxed::Box<crate::ascii::AsciiStr> {
    type Symbol = crate::ascii::AsciiChar;
    type Input = &'a crate::ascii::AsciiStr;

    fn into_input(self) -> Self::Input {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: Copy> IntoInput for &'a alloc::rc::Rc<[T]> {
    type Symbol = T;
    type Input = &'a [T];

    fn into_input(self) -> &'a [T] {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> IntoInput for &'a alloc::rc::Rc<str> {
    type Symbol = char;
    type Input = &'a str;

    fn into_input(self) -> &'a str {
        self
    }
}

#[cfg(all(feature = "alloc", feature = "ascii"))]
impl<'a> IntoInput for &'a alloc::rc::Rc<crate::ascii::AsciiStr> {
    type Symbol = crate::ascii::AsciiChar;
    type Input = &'a crate::ascii::AsciiStr;

    fn into_input(self) -> Self::Input {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> IntoInput for &'a alloc::string::String {
    type Symbol = char;
    type Input = &'a str;

    fn into_input(self) -> &'a str {
        self
    }
}

#[cfg(all(feature = "alloc", feature = "ascii"))]
impl<'a> IntoInput for &'a crate::ascii::AsciiString {
    type Symbol = crate::ascii::AsciiChar;
    type Input = &'a crate::ascii::AsciiStr;

    fn into_input(self) -> Self::Input {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: Copy> IntoInput for &'a alloc::sync::Arc<[T]> {
    type Symbol = T;
    type Input = &'a [T];

    fn into_input(self) -> &'a [T] {
        self
    }
}

#[cfg(feature = "alloc")]
impl<'a> IntoInput for &'a alloc::sync::Arc<str> {
    type Symbol = char;
    type Input = &'a str;

    fn into_input(self) -> &'a str {
        self
    }
}

#[cfg(all(feature = "alloc", feature = "ascii"))]
impl<'a> IntoInput for &'a alloc::sync::Arc<crate::ascii::AsciiStr> {
    type Symbol = crate::ascii::AsciiChar;
    type Input = &'a crate::ascii::AsciiStr;

    fn into_input(self) -> Self::Input {
        self
    }
}

impl<P, I> ParsedInput<P, I>
where
    P: Parse<I> + Clone,
    I: Input,
{
    /// Creates a new [`ParsedInput`].
    ///
    /// The returned [`ParsedInput`] will produce symbols by repeated
    /// applying the provided parser over the provided input.
    pub const fn new(parser: P, input: I) -> Self {
        Self {
            parser,
            input: Some(input),
        }
    }
}

impl<P, I> Input for ParsedInput<P, I>
where
    P: Parse<I> + Clone,
    I: Input,
{
    type Symbol = P::Parsed;

    fn next(&mut self) -> Option<Self::Symbol> {
        let Some(input) = self.input.take() else {
            return None;
        };
        match self.parser.parse(input) {
            Ok(Success(symb, rem)) => {
                self.input = Some(rem);
                Some(symb)
            }
            _ => None,
        }
    }

    fn pos_eq(&self, other: &Self) -> bool {
        if let Some(input) = self.input.as_ref() {
            if let Some(other) = other.input.as_ref() {
                input.pos_eq(other)
            } else {
                false
            }
        } else {
            other.input.is_none()
        }
    }

    fn is_empty(&self) -> bool {
        self.input.as_ref().map(I::is_empty).unwrap_or(true)
    }
}
