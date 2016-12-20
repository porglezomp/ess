//! A lightweight S-expression parser intended for language implementation.

// #![warn(missing_docs)]
#![deny(unsafe_code)]

#[macro_use]
extern crate nom;

use nom::{digit, multispace, IResult};

/// Indicates how parsing failed.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ParseError {
    /// We can't explain how the parsing failed.
    Unspecified,
}

#[derive(Debug, PartialEq, Clone, PartialOrd)]
/// An `Atom` is the representation of a non-composite object
pub enum Atom {
    /// A value representing a symbol. A symbol is an atomic unit
    Sym(String),
    /// A value representing a string literal.
    Str(String),
    /// A value representing a single character.
    Char(char),
    /// A value representing an integer. Any number containing no decimal point
    /// will be parsed as an `Int`.
    Int(i64),
    /// A value representing a float. Any number containing a decimal point will
    /// be parsed as a `Float`.
    Float(f64),
}

#[derive(Debug, PartialEq, Clone, PartialOrd)]
/// A `Sexp` represents either an `Atom` or a `List`. It encompasses all
/// possible lisp expressions.
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

pub fn parse(input: &str) -> Result<Sexp, ParseError> {
    match do_parse!(input, exp: sexp >> opt!(multispace) >> eof!() >> (exp)) {
        IResult::Done(_, res) => Ok(res),
        _ => Err(ParseError::Unspecified),
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

named!(atom<&str, Atom>, alt!(string | symbol | number | character));

named!(string<&str, Atom>,
  do_parse!(
    opt!(multispace) >>
    tag_s!("\"") >>
    contents: take_until_s!("\"") >>
    tag_s!("\"") >>
    (Atom::Str(contents.into()))
  )
);

named!(symbol<&str, Atom>,
  do_parse!(
    opt!(multispace) >>
    peek!(valid_ident_prefix) >>
    name: take_while1_s!(valid_ident_char) >>
    (Atom::Sym(name.into()))
  )
);

fn valid_ident_prefix(ident: &str) -> IResult<&str, ()>  {
    match ident.chars().next() {
        Some(c) if c != '#' && !c.is_digit(10) && valid_ident_char(c) =>
            IResult::Done(&ident[1..], ()),
        None => IResult::Incomplete(nom::Needed::Unknown),
        _ => IResult::Error(nom::ErrorKind::Custom(0)),
    }
}

fn valid_ident_char(c: char) -> bool {
    !c.is_whitespace() && c != '"' && c != '(' && c != ')'
}

named!(number<&str, Atom>,
  do_parse!(
    opt!(multispace) >>
    integral: digit >>
    peek!(not!(valid_ident_prefix)) >>
    (Atom::Int(integral.chars().fold(0, |i, c| i * 10 + c as i64 - '0' as i64)))
  )
);

named!(character<&str, Atom>,
  do_parse!(
    opt!(multispace) >>
    tag_s!("#\\") >>
    character: take_s!(1) >>
    (Atom::Char(character.chars().next().unwrap()))
  )
);

#[cfg(test)]
#[test]
fn test_parse_number() {
    assert_eq!(number("0"), IResult::Done("", Atom::Int(0)));
    assert_eq!(number("123"), IResult::Done("", Atom::Int(123)));
    assert_eq!(number("0123456789"), IResult::Done("", Atom::Int(123456789)));
    assert_eq!(number("    42"), IResult::Done("", Atom::Int(42)));

    assert!(number(" 42a").is_err());
    assert_eq!(number("13()"), IResult::Done("()", Atom::Int(13)));

    assert!(number("abc").is_err());
    assert!(number("()").is_err());
    assert!(number("").is_incomplete());
}

#[cfg(test)]
#[test]
fn test_parse_ident() {
    assert_eq!(symbol("+"), IResult::Done("", Atom::Sym("+".into())));
    assert_eq!(symbol(" nil?"), IResult::Done("", Atom::Sym("nil?".into())));
    assert_eq!(symbol(" ->socket"), IResult::Done("", Atom::Sym("->socket".into())));
    assert_eq!(symbol("fib("), IResult::Done("(", Atom::Sym("fib".into())));

    // We reserve #foo for the implementation to do as it wishes
    assert!(symbol("#hi").is_err());

    assert!(symbol("0").is_err());
    assert!(symbol("()").is_err());
    assert!(symbol("").is_incomplete());
}

#[cfg(test)]
#[test]
fn test_parse_string() {
    assert_eq!(string(r#""hello""#), IResult::Done("", Atom::Str("hello".into())));
    assert_eq!(string(r#"  "this is a nice string
with 0123 things in it""#),
               IResult::Done("", Atom::Str("this is a nice string\nwith 0123 things in it".into())));

    assert!(string(r#""hi"#).is_err());
}

#[cfg(test)]
#[test]
fn test_parse_char() {
    assert_eq!(character("#\\\""), IResult::Done("", Atom::Char('"')));
    assert_eq!(character("#\\ "), IResult::Done("", Atom::Char(' ')));
    assert_eq!(character("  #\\\\"), IResult::Done("", Atom::Char('\\')));

    assert!(character("#").is_incomplete());
    assert!(character("a").is_err());
}

#[cfg(test)]
#[test]
fn test_parse_list() {
    assert_eq!(list("()"), IResult::Done("", vec![]));
    assert_eq!(list("(1)"), IResult::Done("", vec![Sexp::Atom { atom: Atom::Int(1) }]));
    assert_eq!(list("  ( 1    2  3 a )"), IResult::Done("", vec![
        Sexp::Atom { atom: Atom::Int(1) },
        Sexp::Atom { atom: Atom::Int(2) },
        Sexp::Atom { atom: Atom::Int(3) },
        Sexp::Atom { atom: Atom::Sym("a".into()) },
    ]));
}

#[cfg(test)]
#[test]
fn test_cant_parse() {
    assert!(parse("1 2").is_err());
}

#[cfg(test)]
#[test]
fn test_parse_expression() {
    assert_eq!(parse(r#"
(def (main)
  (print (str "say " #\" "Hello, World" #\" " today!")))
"#),
               Ok(Sexp::List {
                   list: vec![
                       Sexp::Atom { atom: Atom::Sym("def".into()) },
                       Sexp::List {
                           list: vec![
                               Sexp::Atom { atom: Atom::Sym("main".into()) }
                           ]
                       },
                       Sexp::List {
                           list: vec![
                               Sexp::Atom { atom: Atom::Sym("print".into()) },
                               Sexp::List {
                                   list: vec![
                                       Sexp::Atom {
                                           atom: Atom::Sym("str".into())
                                       },
                                       Sexp::Atom {
                                           atom: Atom::Str("say ".into())
                                       },
                                       Sexp::Atom { atom: Atom::Char('"') },
                                       Sexp::Atom {
                                           atom: Atom::Str("Hello, World".into())
                                       },
                                       Sexp::Atom { atom: Atom::Char('"') },
                                       Sexp::Atom {
                                           atom: Atom::Str(" today!".into())
                                       }
                                   ]
                               }
                           ]
                       }
                   ]
               }));
}
