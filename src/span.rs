use crate::Input;

/// A slice of parser input.
///
/// A [`Span`] represents a subset of input. Internally, a [`Span`]
/// consists of two [`Input`] objects: one representing the start
/// of the [`Span`] and the other other representing the end.
#[derive(Debug, Clone)]
pub struct Span<I: Input> {
    begin: I,
    end: I,
}

impl<I: Input + Copy> Copy for Span<I> {}

impl<I: Input> Span<I> {
    /// Creates a new [`Span`] over the input between `begin` and `end`.
    pub fn new(start: I, end: I) -> Self {
        Self { begin: start, end }
    }

    /// Gets the start position of the [`Span`].
    pub fn start(&self) -> &I {
        &self.begin
    }

    /// Gets the end position of the [`Span`].
    pub fn end(&self) -> &I {
        &self.end
    }

    /// Checks if the [`Span`] is empty.
    ///
    /// A [`Span`] is empty if the start and end are at the same position.
    pub fn is_empty(&self) -> bool {
        self.begin.pos_eq(&self.end)
    }
}

impl<I: Input> Input for Span<I> {
    type Symbol = I::Symbol;

    fn next(&mut self) -> Option<Self::Symbol> {
        if self.begin.pos_eq(&self.end) {
            None
        } else {
            self.begin.next()
        }
    }

    fn pos_eq(&self, other: &Self) -> bool {
        self.begin.pos_eq(&other.begin)
    }
}

impl<I: Input> Iterator for Span<I> {
    type Item = I::Symbol;

    fn next(&mut self) -> Option<Self::Item> {
        Input::next(self)
    }
}

impl<'a> From<Span<&'a str>> for &'a str {
    fn from(span: Span<&'a str>) -> &'a str {
        &span.start()[..(span.start().len() - span.end().len())]
    }
}

impl<'a, T: Copy> From<Span<&'a [T]>> for &'a [T] {
    fn from(span: Span<&'a [T]>) -> &'a [T] {
        &span.start()[..(span.start().len() - span.end().len())]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn str_span() {
        let input = "hello world";
        let start = &input[3..];
        let end = &input[9..];

        let mut span = Span::new(start, end);

        assert_eq!(*span.start(), "lo world");
        assert_eq!(*span.end(), "ld");
        assert!(!span.is_empty());

        let spanned: &str = span.into();
        assert_eq!(spanned, "lo wor");

        assert_eq!(Input::next(&mut span), Some('l'));
        assert_eq!(Input::next(&mut span), Some('o'));
        assert_eq!(Input::next(&mut span), Some(' '));
        assert_eq!(Input::next(&mut span), Some('w'));
        assert_eq!(Input::next(&mut span), Some('o'));
        assert_eq!(Input::next(&mut span), Some('r'));
        assert_eq!(Input::next(&mut span), None);

        assert!(Span::new(start, start).is_empty());
    }
}
