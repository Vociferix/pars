use super::{
    UnicodeInput, lossy::grapheme_cluster as grapheme_cluster_lossy, lossy::line as line_lossy,
};
use crate::{Input, IntoInput, Span, Success};

/// Unicode input that tracks location information.
///
/// Lines are tracked by the Unicode mandatory line break rules, and
/// columns are tracked by counting grapheme clusters according to the
/// Unicode segmentation rules. In the case where the input would be
/// invalid Unicode, the Unicode Replacement Character (U+FFFD) is
/// used to replace the invalid input when calculating line breaks and
/// grapheme clusters.
///
/// The line and column numbers start at 1.
///
/// [`LocInput`] is useful for providing diagnostics to the user that
/// contain the human readable location of errors and parsed entities
/// in the source input.
#[derive(Debug, Clone)]
pub struct LocInput<I: UnicodeInput> {
    input: I,
    line_start: I,
    line_curr: I,
    lineno: u64,
    grapheme_start: I,
    grapheme_curr: I,
    colno: u64,
}

impl<I: UnicodeInput> LocInput<I> {
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
            if let Ok(Success(g, lrem)) = grapheme_cluster_lossy(l.start().clone()) {
                Self {
                    input: rem,
                    line_start: l.start().clone(),
                    line_curr: lrem,
                    lineno: 1,
                    grapheme_start: g.start().clone(),
                    grapheme_curr: g.start().clone(),
                    colno: 1,
                }
            } else {
                Self {
                    input: rem,
                    line_start: l.start().clone(),
                    line_curr: l.start().clone(),
                    lineno: 1,
                    grapheme_start: l.start().clone(),
                    grapheme_curr: l.start().clone(),
                    colno: 1,
                }
            }
        } else {
            Self {
                input: input.clone(),
                line_start: input.clone(),
                line_curr: input.clone(),
                lineno: 1,
                grapheme_start: input.clone(),
                grapheme_curr: input,
                colno: 1,
            }
        }
    }

    /// Gets the current position of the source input.
    pub fn position(&self) -> &I {
        &self.grapheme_curr
    }

    /// Gets a [`Span`] containing the current line in the source input.
    pub fn line(&self) -> Span<I> {
        Span::new(self.line_start.clone(), self.input.clone())
    }

    /// Gets a [`Span`] containing the current grapheme cluster in the souce input.
    pub fn grapheme_cluster(&self) -> Span<I> {
        Span::new(self.grapheme_start.clone(), self.line_curr.clone())
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

impl<I: UnicodeInput> Input for LocInput<I> {
    type Symbol = I::Symbol;

    fn next(&mut self) -> Option<Self::Symbol> {
        if self.grapheme_curr.pos_eq(&self.line_curr) {
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
            if let Ok(Success(g, rem)) = grapheme_cluster_lossy(self.line_curr.clone()) {
                self.line_curr = rem;
                self.grapheme_start = g.start().clone();
                self.grapheme_curr = g.start().clone();
                self.colno += 1;
            } else {
                return None;
            }
        }
        self.grapheme_curr.next()
    }

    fn pos_eq(&self, other: &Self) -> bool {
        self.grapheme_curr.pos_eq(&other.grapheme_curr)
    }

    fn size_hint(&self) -> Option<usize> {
        self.grapheme_curr.size_hint()
    }

    fn is_empty(&self) -> bool {
        self.grapheme_curr.is_empty()
    }
}
