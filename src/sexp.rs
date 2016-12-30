//! The `Sexp` type, the representation of s-expressions.

use std::borrow::Cow;

use span::{Span, ByteSpan};

/// A type representing arbitrary s-expressions.
///
/// `Sexp` carries the source code location it came from along with it for later
/// diagnostic purposes.
#[derive(Debug, PartialEq, Clone, PartialOrd)]
pub enum Sexp<'a, Loc=ByteSpan> where Loc: Span {
    /// A value representing a symbol.
    Sym(Cow<'a, str>, Loc),
    /// A value representing a string literal.
    Str(Cow<'a, str>, Loc),
    /// A value representing a single character.
    Char(char, Loc),
    /// A value representing an integer. Any number containing no decimal point
    /// will be parsed as an `Int`.
    Int(i64, Loc),
    /// A value representing a floating point number. Any number containing a
    /// decimal point will be parsed as a `Float`.
    Float(f64, Loc),
    /// A list of subexpressions.
    List(Vec<Sexp<'a, Loc>>, Loc),
}

impl<'a, Loc> Sexp<'a, Loc> where Loc: Span {
    /// Gives a reference to the source location contained in the `Sexp`.
    pub fn get_loc(&self) -> &Loc {
        match *self {
            Sexp::Sym(.., ref l) | Sexp::Str(.., ref l) |
            Sexp::Char(.., ref l) | Sexp::Int(.., ref l) |
            Sexp::Float(.., ref l) | Sexp::List(.., ref l) => l,
        }
    }

    /// Gives a mutable reference to the `Sexp`'s source location.
    pub fn get_loc_mut(&mut self) -> &mut Loc {
        match *self {
            Sexp::Sym(.., ref mut l) | Sexp::Str(.., ref mut l) |
            Sexp::Char(.., ref mut l) | Sexp::Int(.., ref mut l) |
            Sexp::Float(.., ref mut l) | Sexp::List(.., ref mut l) => l,
        }
    }
}

fn extend_cow<'a, T: ?Sized>(cow: &Cow<'a, T>) -> Cow<'static, T>
    where T: ToOwned
{
    Cow::Owned(cow.clone().into_owned())
}

impl<'a, Loc> Sexp<'a, Loc> where Loc: Span + Clone {
    /// Take ownership of an s-expression's contents.
    pub fn to_owned(&self) -> Sexp<'static, Loc> {
        match *self {
            Sexp::Sym(ref s, ref l) => Sexp::Sym(extend_cow(s), l.clone()),
            Sexp::Str(ref s, ref l) => Sexp::Str(extend_cow(s), l.clone()),
            Sexp::Char(c, ref l) => Sexp::Char(c, l.clone()),
            Sexp::Int(i, ref l) => Sexp::Int(i, l.clone()),
            Sexp::Float(f, ref l) => Sexp::Float(f, l.clone()),
            Sexp::List(ref xs, ref l) =>
                Sexp::List(xs.iter().map(Sexp::to_owned).collect(),
                           l.clone()),
        }
    }
}
