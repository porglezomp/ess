//! A lightweight S-expression parser intended for language implementation.

// #![warn(missing_docs)]
#![deny(unsafe_code)]

#[macro_use]
extern crate nom;

use nom::{digit, multispace, IResult};
use std::str::FromStr;

/// Indicates how parsing failed.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ParseError {
    /// We can't explain how the parsing failed.
    Unspecified,
}

#[derive(Debug, PartialEq, Clone, PartialOrd)]
pub enum Sexp {
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
    /// A list of subexpressions
    List(Vec<Sexp>),
}

pub fn parse_one(input: &str) -> Result<Sexp, ParseError> {
    match do_parse!(input,
                    exp: sexp >>
                    opt!(complete!(multispace)) >>
                    eof!() >>
                    (exp)) {
        IResult::Done(_, res) => Ok(res),
        _ => Err(ParseError::Unspecified),
    }
}

pub fn parse(input: &str) -> Result<Vec<Sexp>, ParseError> {
    let parse_res: IResult<&str, Vec<Sexp>> =
        do_parse!(input,
                  exps: many1!(complete!(sexp)) >>
                  opt!(complete!(multispace)) >>
                  eof!() >>
                  (exps));
    match parse_res {
        IResult::Done(_, res) => Ok(res),
        e => {
            println!("{:#?}", e);
            Err(ParseError::Unspecified)
        }
    }
}

named!(sexp<&str, Sexp>,
  alt_complete!(
      list => { |list| Sexp::List(list) }
    | atom
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

named!(atom<&str, Sexp>, alt_complete!(string | symbol | number | character));

named!(string<&str, Sexp>,
  do_parse!(
    opt!(multispace) >>
    tag_s!(r#"""#) >>
    contents: take_until_s!(r#"""#) >>
    tag_s!(r#"""#) >>
    (Sexp::Str(contents.into()))
  )
);

named!(symbol<&str, Sexp>,
  do_parse!(
    opt!(multispace) >>
    peek!(valid_ident_prefix) >>
    name: take_while1_s!(valid_ident_char) >>
    (Sexp::Sym(name.into()))
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

named!(number<&str, Sexp>,
  preceded!(opt!(multispace),
    map_res!(
      recognize!(do_parse!(
        digit >>
        is_float: opt!(complete!(tag_s!("."))) >>
        opt!(complete!(digit)) >>
        peek!(not!(valid_ident_prefix)) >>
        ()
      )),
      |text: &str| {
          if text.contains(".") {
              f64::from_str(text).map(Sexp::Float).or(Err(()))
          } else {
              i64::from_str(text).map(Sexp::Int).or(Err(()))
          }
      }
    )
  )
);

named!(character<&str, Sexp>,
  do_parse!(
    opt!(multispace) >>
    tag_s!(r#"#\"#) >>
    character: take_s!(1) >>
    (Sexp::Char(character.chars().next().unwrap()))
  )
);

#[cfg(test)]
#[test]
fn test_parse_number() {
    assert_eq!(number("0"), IResult::Done("", Sexp::Int(0)));
    assert_eq!(number("123"), IResult::Done("", Sexp::Int(123)));
    assert_eq!(number("0123456789"), IResult::Done("", Sexp::Int(123456789)));
    assert_eq!(number("    42"), IResult::Done("", Sexp::Int(42)));

    assert_eq!(number("4."), IResult::Done("", Sexp::Float(4.)));
    assert_eq!(number("4.2"), IResult::Done("", Sexp::Float(4.2)));
    assert_eq!(number("1.00000000001"),
               IResult::Done("", Sexp::Float(1.00000000001)));

    assert!(number(" 42a").is_err());
    assert_eq!(number("13()"), IResult::Done("()", Sexp::Int(13)));

    assert!(number("abc").is_err());
    assert!(number("()").is_err());
    assert!(number("").is_incomplete());
}

#[cfg(test)]
#[test]
fn test_parse_ident() {
    assert_eq!(symbol("+"), IResult::Done("", Sexp::Sym("+".into())));
    assert_eq!(symbol(" nil?"), IResult::Done("", Sexp::Sym("nil?".into())));
    assert_eq!(symbol(" ->socket"), IResult::Done("", Sexp::Sym("->socket".into())));
    assert_eq!(symbol("fib("), IResult::Done("(", Sexp::Sym("fib".into())));

    // We reserve #foo for the implementation to do as it wishes
    assert!(symbol("#hi").is_err());

    assert!(symbol("0").is_err());
    assert!(symbol("()").is_err());
    assert!(symbol("").is_incomplete());
}

#[cfg(test)]
#[test]
fn test_parse_string() {
    assert_eq!(string(r#""hello""#), IResult::Done("", Sexp::Str("hello".into())));
    assert_eq!(string(r#"  "this is a nice string
with 0123 things in it""#),
               IResult::Done("", Sexp::Str("this is a nice string\nwith 0123 things in it".into())));

    assert!(string(r#""hi"#).is_err());
}

#[cfg(test)]
#[test]
fn test_parse_char() {
    assert_eq!(character(r#"#\""#), IResult::Done("", Sexp::Char('"')));
    assert_eq!(character(r#"#\ "#), IResult::Done("", Sexp::Char(' ')));
    assert_eq!(character(r#"  #\\"#), IResult::Done("", Sexp::Char('\\')));

    assert!(character("#").is_incomplete());
    assert!(character("a").is_err());
}

#[cfg(test)]
#[test]
fn test_parse_list() {
    assert_eq!(list("()"), IResult::Done("", vec![]));
    assert_eq!(list("(1)"), IResult::Done("", vec![Sexp::Int(1)]));
    assert_eq!(list("  ( 1    2  3 a )"), IResult::Done("", vec![
        Sexp::Int(1),
        Sexp::Int(2),
        Sexp::Int(3),
        Sexp::Sym("a".into()),
    ]));
}

#[cfg(test)]
#[test]
fn test_parse_only_one() {
    assert!(parse_one("1 2").is_err());
}

#[cfg(test)]
#[test]
fn test_parse_expression() {
    assert_eq!(parse_one(r#"
(def (main)
  (print (str "say " #\" "Hello, World" #\" " today!")))
"#),
               Ok(Sexp::List(vec![
                   Sexp::Sym("def".into()),
                   Sexp::List(
                       vec![Sexp::Sym("main".into())]
                   ),
                   Sexp::List(vec![
                       Sexp::Sym("print".into()),
                       Sexp::List(vec![
                           Sexp::Sym("str".into()),
                           Sexp::Str("say ".into()),
                           Sexp::Char('"'),
                           Sexp::Str("Hello, World".into()),
                           Sexp::Char('"'),
                           Sexp::Str(" today!".into()),
                       ])
                   ])
               ])));
}

#[cfg(test)]
#[test]
fn test_parse_multi() {
    assert_eq!(parse(" 1 2 3 "),
               Ok(vec![Sexp::Int(1), Sexp::Int(2), Sexp::Int(3)]));
}
