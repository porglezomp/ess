//! A `Span` represents a location in source file.
//!
//! Spans are useful for reporting error messages. They're used during parsing
//! and are carried around in the `Sexp` type so that errors can be reported at
//! a higher level than the s-expressions, for example reporting semantic errors
//! in a Lisp implementation.

/// Represents a way of talking about a region in the source.
///
/// All spans begin at a point in the source and contain some (possibly empty)
/// amount of text.
pub trait Span {
    /// The `Begin` type represents the beginning point of a span.
    type Begin;

    /// Moves a `Span` forward by `begin`.
    ///
    /// useful for moving a relatively positioned span to start at a specific
    /// absolute position.
    fn offset(&self, begin: Self::Begin) -> Self;
    /// Returns the point where a span begins.
    fn begin(&self) -> Self::Begin;
    /// Combines two spans into a single span that contains both of their
    /// contents.
    fn union(&self, other: &Self) -> Self;
}

/// `ByteSpan` is a very simple span, and the default for all of the parsers in
/// Ess.
///
/// It represents a half-open range of bytes, the first element is the first
/// byte in the span and the second element is the first by after the span. This
/// means that `&text[span.0..span.1]` works exactly as we would expect it to.
pub type ByteSpan = (usize, usize);

impl Span for ByteSpan {
    type Begin = usize;

    fn offset(&self, begin: Self::Begin) -> Self {
        (self.0 + begin, self.1 + begin)
    }

    fn begin(&self) -> Self::Begin {
        self.0
    }

    fn union(&self, other: &Self) -> Self {
        use std::cmp::{max, min};
        (min(self.0, other.0), max(self.1, other.1))
    }
}
