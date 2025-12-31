use super::{AsciiInput, lossy::char as char_lossy, lossy::line as line_lossy};
use crate::{Input, IntoInput, Parse, Span, Success};

/// ASCII input that tracks location information.
///
/// Lines are separated by CR, LF, or CRLF. In the case where the
/// input would be invalid ASCII, the ASCII control character SUB
/// (`0x1A`) is used as a replacement character when calculating
/// line breaks.
///
/// The line and column numbers start at 1.
///
/// [`LocInput`] is useful for providing diagnostics to the user that
/// contain the human readable location of errors and parsed entities
/// in the source input.
#[derive(Debug, Clone)]
pub struct LocInput<I: AsciiInput> {
    input: I,
    line_start: I,
    line_curr: I,
    lineno: u64,
    ch_start: I,
    ch_curr: I,
    colno: u64,
}

impl<I: AsciiInput> LocInput<I> {
    /// Creates a new [`LocInput`] from some source input.
    ///
    /// The new [`LocInput`] always starts at line 1, column 1.
    /// If some source input had previously been consumed, the [`LocInput`]
    /// is not aware of it. Thus, it perceives the provided input as being
    /// the very beginning of the source input.
    pub fn new<N>(input: N) -> Self
    where
        N: IntoInput<Input = I>,
    {
        let input = input.into_input();
        if let Ok(Success(l, rem)) = line_lossy(input.clone()) {
            if let Ok(Success(ch, lrem)) = char_lossy.recognize().parse(l.start().clone()) {
                Self {
                    input: rem,
                    line_start: l.start().clone(),
                    line_curr: lrem,
                    lineno: 1,
                    ch_start: ch.start().clone(),
                    ch_curr: ch.start().clone(),
                    colno: 1,
                }
            } else {
                Self {
                    input: rem,
                    line_start: l.start().clone(),
                    line_curr: l.start().clone(),
                    lineno: 1,
                    ch_start: l.start().clone(),
                    ch_curr: l.start().clone(),
                    colno: 1,
                }
            }
        } else {
            Self {
                input: input.clone(),
                line_start: input.clone(),
                line_curr: input.clone(),
                lineno: 1,
                ch_start: input.clone(),
                ch_curr: input,
                colno: 1,
            }
        }
    }

    /// Gets the current position of the source input.
    pub fn position(&self) -> &I {
        &self.ch_curr
    }

    /// Gets a [`Span`] containing the current line in the source input.
    pub fn line(&self) -> Span<I> {
        Span::new(self.line_start.clone(), self.input.clone())
    }

    /// Gets the current line number in the source input.
    pub fn line_num(&self) -> u64 {
        self.lineno
    }

    /// Gets the current column number in the source input.
    pub fn column_num(&self) -> u64 {
        self.colno
    }
}

impl<I: AsciiInput> Input for LocInput<I> {
    type Symbol = I::Symbol;

    fn next(&mut self) -> Option<Self::Symbol> {
        if self.ch_curr.pos_eq(&self.line_curr) {
            if self.line_curr.pos_eq(&self.input) {
                if let Ok(Success(l, rem)) = line_lossy(self.input.clone()) {
                    self.input = rem;
                    self.line_start = l.start().clone();
                    self.line_curr = l.start().clone();
                    self.lineno += 1;
                    self.colno = 1;
                } else {
                    return None;
                }
            }
            if let Ok(Success(ch, rem)) = char_lossy.recognize().parse(self.line_curr.clone()) {
                self.line_curr = rem;
                self.ch_start = ch.start().clone();
                self.ch_curr = ch.start().clone();
                self.colno += 1;
            } else {
                return None;
            }
        }
        self.ch_curr.next()
    }

    fn pos_eq(&self, other: &Self) -> bool {
        self.ch_curr.pos_eq(&other.ch_curr)
    }

    fn size_hint(&self) -> Option<usize> {
        self.ch_curr.size_hint()
    }

    fn is_empty(&self) -> bool {
        self.ch_curr.is_empty()
    }
}
