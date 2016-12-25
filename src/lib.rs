//! A lightweight S-expression parser intended for language implementation.

// #![warn(missing_docs)]
#![deny(unsafe_code)]

use std::borrow::Cow;

/// A type representing arbitrary symbolic expressions. `Sexp` carries the
/// source code location it came from along with it for later diagnostic
/// purposes.
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
    pub fn get_loc(&self) -> &Loc {
        match *self {
            Sexp::Sym(.., ref l) => l,
            Sexp::Str(.., ref l) => l,
            Sexp::Char(.., ref l) => l,
            Sexp::Int(.., ref l) => l,
            Sexp::Float(.., ref l) => l,
            Sexp::List(.., ref l) => l,
        }
    }

    pub fn get_loc_mut(&mut self) -> &mut Loc {
        match *self {
            Sexp::Sym(.., ref mut l) => l,
            Sexp::Str(.., ref mut l) => l,
            Sexp::Char(.., ref mut l) => l,
            Sexp::Int(.., ref mut l) => l,
            Sexp::Float(.., ref mut l) => l,
            Sexp::List(.., ref mut l) => l,
        }
    }
}


// General Parsing Types ///////////////////////////////////////////////////////

pub trait Span {
    type Begin;

    fn offset(&self, begin: Self::Begin) -> Self;
    fn begin(&self) -> Self::Begin;
    fn union(&self, other: &Self) -> Self;
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseResult<'a, T, E> {
    Done(&'a str, T),
    Error(E),
}

use ParseResult::*;


// Specific Parsing Types (ParseError, ByteSpan) ///////////////////////////////

/// Indicates how parsing failed.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseError<Loc=ByteSpan> where Loc: Span {
    /// We can't explain how the parsing failed.
    UnexpectedEof,
    Char(Box<ParseError>, Loc),
    String(Box<ParseError>, Loc),
    Symbol(Box<ParseError>, Loc),
    Number(Box<ParseError>, Loc),
    Unexpected(char, Loc::Begin),
    Unimplemented,
}

type ByteSpan = (usize, usize);

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



// Parsing Utilities ///////////////////////////////////////////////////////////

trait IsDelimeter {
    fn is_delimiter(&self) -> bool;
}

impl IsDelimeter for char {
    fn is_delimiter(&self) -> bool {
        self.is_whitespace() || *self == ';'
            || *self == '(' || *self == ')'
            || *self == '[' || *self == ']'
            || *self == '{' || *self == '}'
            || *self == '"' || *self == '\''
            || *self == '`' || *self == ','
    }
}


// Parsers /////////////////////////////////////////////////////////////////////

// pub fn parse_one(input: &str) -> Result<Sexp, ParseError>;

// pub fn parse(input: &str) -> Result<Vec<Sexp>, ParseError>;

pub fn parse_number(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    // Consume all the whitespace at the beginning of the string
    let end_of_white = if let Some(pos) = input.find(|c: char| !c.is_whitespace()) {
        pos
    } else {
        return Error(ParseError::Number(
            Box::new(ParseError::UnexpectedEof),
            (input.len(), input.len()).offset(start_loc)));
    };

    let input = &input[end_of_white..];
    let start_loc = start_loc + end_of_white;

    match input.chars().next() {
        Some(c) if !c.is_digit(10) => {
            return Error(ParseError::Number(
                Box::new(ParseError::Unexpected(c, start_loc)),
                (0, c.len_utf8()).offset(start_loc)));
        }
        None => return Error(ParseError::Number(
            Box::new(ParseError::UnexpectedEof),
            (0, 0).offset(start_loc))),
        _ => (),
    }

    let base = 10;

    let mut end = 0;
    // Before the decimal point
    for (i, c) in input.char_indices() {
        if c == '.' {
            end = i + 1;
            break;
        }

        if c.is_delimiter() {
            return Done(&input[i..],
                        Sexp::Int(input[..i].parse().expect("Already matched digits"),
                                  (0, i).offset(start_loc)));
        }

        if !c.is_digit(base) {
            return Error(ParseError::Number(
                Box::new(ParseError::Unexpected(c, start_loc + i)),
                (i, i).offset(start_loc)));
        }

        end = i + c.len_utf8();
    }

    if input[end..].is_empty() {
        return Done(&input[end..],
                    Sexp::Int(input.parse().expect("Already matched digits"),
                              (0, end).offset(start_loc)));
    }

    // After the decimal point
    for (i, c) in input[end..].char_indices() {
        if c.is_delimiter() {
            return Done(&input[i+end..],
                        Sexp::Float(input[..end+i].parse().expect("Already matched digits.digits"),
                                    (0, end+i).offset(start_loc)));
        }

        if !c.is_digit(base) {
            return Error(ParseError::Number(
                Box::new(ParseError::Unexpected(c, start_loc + i + end)),
                (i+end, i+end).offset(start_loc)));
        }
    }

    Done(&input[input.len()..],
         Sexp::Float(input.parse().expect("Already matched digits.digits"),
                     (0, input.len()).offset(start_loc)))
}

pub fn parse_symbol(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let end_of_white = if let Some(pos) = input.find(|c: char| !c.is_whitespace()) {
        pos
    } else {
        return Error(ParseError::Symbol(
            Box::new(ParseError::UnexpectedEof),
            (input.len(), input.len()).offset(start_loc)));
    };

    let input = &input[end_of_white..];
    let start_loc = start_loc + end_of_white;

    match input.chars().next() {
        Some(c@'#') | Some(c@':') | Some(c@'0'...'9') =>
            return Error(ParseError::Symbol(
                Box::new(ParseError::Unexpected(c, start_loc)),
                (0, 0).offset(start_loc))),
        Some(c) if c.is_delimiter() =>
            return Error(ParseError::Symbol(
                Box::new(ParseError::Unexpected(c, start_loc)),
                (0, 0).offset(start_loc))),
        Some(_) => (),
        None => unreachable!(),
    }

    for (i, c) in input.char_indices() {
        if c.is_delimiter() {
            return Done(&input[i..],
                        Sexp::Sym(input[..i].into(), (0, i).offset(start_loc)));
        }
    }

    Done(&input[input.len()..],
         Sexp::Sym(input.into(), (0, input.len()).offset(start_loc)))
}

pub fn parse_string(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let end_of_white = if let Some(pos) = input.find(|c: char| !c.is_whitespace()) {
        pos
    } else {
        return Error(ParseError::String(
            Box::new(ParseError::UnexpectedEof),
            (input.len(), input.len()).offset(start_loc)));
    };

    let input = &input[end_of_white..];
    let start_loc = start_loc + end_of_white;

    match input.chars().next() {
        Some('"') => (),
        Some(c) =>
            return Error(ParseError::String(
                Box::new(ParseError::Unexpected(c, start_loc)),
            (0, 0).offset(start_loc))),
        None => unreachable!(),
    }

    for (i, c) in input[1..].char_indices() {
        if c == '"' {
            return Done(&input[2+i..],
            Sexp::Str(input[1..i+1].into(), (0, i+2).offset(start_loc)));
        }
    }

    Error(ParseError::String(
        Box::new(ParseError::UnexpectedEof),
        (0, input.len()).offset(start_loc)))
}

pub fn parse_character(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let end_of_white = if let Some(pos) = input.find(|c: char| !c.is_whitespace()) {
        pos
    } else {
        return Error(ParseError::String(
            Box::new(ParseError::UnexpectedEof),
            (input.len(), input.len()).offset(start_loc)));
    };

    let input = &input[end_of_white..];
    let start_loc = start_loc + end_of_white;

    match input.chars().nth(0) {
        Some('#') => (),
        Some(c) =>
            return Error(ParseError::Char(
                Box::new(ParseError::Unexpected(c, start_loc)),
                (0, 0).offset(start_loc))),
        None =>
            return Error(ParseError::Char(
                Box::new(ParseError::UnexpectedEof),
                (0, 0).offset(start_loc))),
    }

    match input.chars().nth(1) {
        Some('\\') => (),
        Some(c) =>
            return Error(ParseError::Char(
                Box::new(ParseError::Unexpected(c, start_loc + 1)),
                (1, 1).offset(start_loc))),
        None =>
            return Error(ParseError::Char(
                Box::new(ParseError::UnexpectedEof),
                (1, 1).offset(start_loc)))
    }

    match input.chars().nth(2) {
        Some(c) =>
            Done(&input[3..], Sexp::Char(c, (0, 3).offset(start_loc))),
        None =>
            Error(ParseError::Char(
                Box::new(ParseError::UnexpectedEof),
                (2, 2).offset(start_loc)))
    }
}


// Tests ///////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod test {
    use super::*;
    use super::ParseResult::*;

    #[test]
    fn test_parse_number() {
        assert_eq!(parse_number("1", 0), Done("", Sexp::Int(1, (0, 1))));
        assert_eq!(parse_number(" 13", 0), Done("", Sexp::Int(13, (1, 3))));
        assert_eq!(parse_number("1.2", 0), Done("", Sexp::Float(1.2, (0, 3))));
        assert_eq!(parse_number("\u{3000}4.2", 0), Done("", Sexp::Float(4.2, (0, 3).offset('\u{3000}'.len_utf8()))));
        assert_eq!(parse_number(" 	42 ", 0), Done(" ", Sexp::Int(42, (2, 4))));
        assert_eq!(parse_number(" 4.2  ", 0), Done("  ", Sexp::Float(4.2, (1, 4))));
        assert_eq!(parse_number("1()", 0), Done("()", Sexp::Int(1, (0, 1))));
        assert_eq!(parse_number("3.6()", 0), Done("()", Sexp::Float(3.6, (0, 3))));

        assert_eq!(parse_number("", 0), Error(ParseError::Number(Box::new(ParseError::UnexpectedEof), (0, 0))));
        assert_eq!(parse_number("123a", 0), Error(ParseError::Number(Box::new(ParseError::Unexpected('a', 3)), (3, 3))));
        assert_eq!(parse_number("66.6+", 0), Error(ParseError::Number(Box::new(ParseError::Unexpected('+', 4)), (4, 4))));
    }

    #[test]
    fn test_parse_ident() {
        assert_eq!(parse_symbol("+", 0), Done("", Sexp::Sym("+".into(), (0, 1))));
        assert_eq!(parse_symbol(" nil?", 0), Done("", Sexp::Sym("nil?".into(), (1, 5))));
        assert_eq!(parse_symbol(" ->socket", 0), Done("", Sexp::Sym("->socket".into(), (1, 9))));
        assert_eq!(parse_symbol("fib(", 0), Done("(", Sexp::Sym("fib".into(), (0, 3))));
        assert_eq!(parse_symbol("foo2", 0), Done("", Sexp::Sym("foo2".into(), (0, 4))));

        // We reserve #foo for the implementation to do as it wishes
        assert_eq!(parse_symbol("#hi", 0), Error(ParseError::Symbol(Box::new(ParseError::Unexpected('#', 0)), (0, 0))));
        // We reserve :foo for keywords
        assert_eq!(parse_symbol(":hi", 0), Error(ParseError::Symbol(Box::new(ParseError::Unexpected(':', 0)), (0, 0))));

        assert_eq!(parse_symbol("", 0), Error(ParseError::Symbol(Box::new(ParseError::UnexpectedEof), (0, 0))));
        assert_eq!(parse_symbol("0", 0), Error(ParseError::Symbol(Box::new(ParseError::Unexpected('0', 0)), (0, 0))));
        assert_eq!(parse_symbol("()", 0), Error(ParseError::Symbol(Box::new(ParseError::Unexpected('(', 0)), (0, 0))));
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(parse_string(r#""""#, 0), Done("", Sexp::Str("".into(), (0, 2))));
        assert_eq!(parse_string(r#""hello""#, 0), Done("", Sexp::Str("hello".into(), (0, 7))));
        assert_eq!(parse_string(r#"  "this is a nice string
with 0123 things in it""#, 0),
                   Done("", Sexp::Str("this is a nice string\nwith 0123 things in it".into(), (2, 48))));
        assert_eq!(parse_string(r#""hi"#, 0), Error(ParseError::String(Box::new(ParseError::UnexpectedEof), (0, 3))));
    }

    #[test]
    fn test_parse_char() {
        assert_eq!(parse_character(r#"#\""#, 0), Done("", Sexp::Char('"', (0, 3))));
        assert_eq!(parse_character(r#"#\ "#, 0), Done("", Sexp::Char(' ', (0, 3))));
        assert_eq!(parse_character(r#"  #\\"#, 0), Done("", Sexp::Char('\\', (2, 5))));

        assert_eq!(parse_character("#", 0), Error(ParseError::Char(Box::new(ParseError::UnexpectedEof), (1, 1))));
        assert_eq!(parse_character("a", 0), Error(ParseError::Char(Box::new(ParseError::Unexpected('a', 0)), (0, 0))));
    }
}


// #[cfg(test)]
// #[test]
// fn test_parse_list() {
//     assert_eq!(list("()"), IResult::Done("", vec![]));
//     assert_eq!(list("(1)"), IResult::Done("", vec![Sexp::Int(1)]));
//     assert_eq!(list("  ( 1    2  3 a )"), IResult::Done("", vec![
//         Sexp::Int(1),
//         Sexp::Int(2),
//         Sexp::Int(3),
//         Sexp::Sym("a".into()),
//     ]));
// }

// #[cfg(test)]
// #[test]
// fn test_parse_only_one() {
//     assert!(parse_one("1 2").is_err());
// }

// #[cfg(test)]
// #[test]
// fn test_parse_expression() {
//     assert_eq!(parse_one(r#"
// (def (main)
//   (print (str "say " #\" "Hello, World" #\" " today!")))
// "#),
//                Ok(Sexp::List(vec![
//                    Sexp::Sym("def".into()),
//                    Sexp::List(
//                        vec![Sexp::Sym("main".into())]
//                    ),
//                    Sexp::List(vec![
//                        Sexp::Sym("print".into()),
//                        Sexp::List(vec![
//                            Sexp::Sym("str".into()),
//                            Sexp::Str("say ".into()),
//                            Sexp::Char('"'),
//                            Sexp::Str("Hello, World".into()),
//                            Sexp::Char('"'),
//                            Sexp::Str(" today!".into()),
//                        ])
//                    ])
//                ])));
// }

// #[cfg(test)]
// #[test]
// fn test_parse_multi() {
//     assert_eq!(parse(" 1 2 3 "),
//                Ok(vec![Sexp::Int(1), Sexp::Int(2), Sexp::Int(3)]));
// }
