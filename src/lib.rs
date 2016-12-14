//! A lightweight S-expression parser intended for language implementation.

#![warn(missing_docs)]
#![deny(unsafe_code)]

#[macro_use]
extern crate nom;

use nom::{digit, multispace, IResult};

#[derive(Debug, PartialEq, Clone, PartialOrd)]
pub enum Atom {
    /// A value representing a symbol. A symbol is an atomic unit
    Sym(String),
    /// A value representing a string literal.
    Str(String),
    /// A value representing an integer. Any number containing no decimal point
    /// will be parsed as an `Int`.
    Int(i64),
    /// A value representing a float. Any number containing a decimal point will
    /// be parsed as a `Float`.
    Float(f64),
}

#[derive(Debug, PartialEq, Clone, PartialOrd)]
pub enum Sexp {
    /// A wrapper around the atom type
    Atom {
        atom: Atom,
    },
    /// A list of subexpressions
    List {
        list: Vec<Sexp>,
    }
}

pub fn parse(input: &str) -> Result<Sexp, ()> {
    match sexp(input) {
        IResult::Done(_, res) => Ok(res),
        _ => Err(()),
    }
}

named!(sexp<&str, Sexp>,
  alt!(
      list => { |list| Sexp::List { list: list } }
    | atom => { |atom| Sexp::Atom { atom: atom } }
  )
);

named!(list<&str, Vec<Sexp> >,
  do_parse!(
    opt!(multispace) >>
    tag_s!("(") >>
    entries: many0!(sexp) >>
    opt!(multispace) >>
    tag_s!(")") >>
    (entries)
  )
);

named!(atom<&str, Atom>, alt!(string | symbol | number));

named!(string<&str, Atom>,
  do_parse!(
    opt!(multispace) >>
    tag_s!("\"") >>
    contents: take_until_s!("\"") >>
    tag_s!("\"") >>
    opt!(multispace) >>
    (Atom::Str(contents.into()))
  )
);

named!(symbol<&str, Atom>,
  do_parse!(
    peek!(not!(digit)) >>
    name: take_while1_s!(valid_ident_char) >>
    (Atom::Sym(name.into()))
  )
);

fn valid_ident_char(c: char) -> bool {
    !c.is_whitespace() && c != '"' && c != '(' && c != ')'
}

named!(number<&str, Atom>,
  do_parse!(
    opt!(multispace) >>
    integral: digit >>
    (Atom::Int(integral.chars().fold(0, |i, c| i * 10 + c as i64 - '0' as i64)))
  )
);

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
