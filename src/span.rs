//! A `Span` represents a location in source file.

pub trait Span {
    type Begin;

    fn offset(&self, begin: Self::Begin) -> Self;
    fn begin(&self) -> Self::Begin;
    fn union(&self, other: &Self) -> Self;
}

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
        use std::cmp::{min, max};
        (min(self.0, other.0), max(self.1, other.1))
    }
}

