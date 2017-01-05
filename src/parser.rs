//! Functions to parse s-expressions and expression atoms.
//!
//! This module contains the core parsing machinery.
//!
//! * If you're interested in getting a parsed s-expression that you can use,
//!   then looking at [`parse`] and [`parse_one`] are your best bet.
//! * If you want to write your own parsers that contain s-expressions,
//!   [`ParseResult`] and [`parse_expression`] will be the most useful to you.
//!
//! [`parse`]: fn.parse.html
//! [`parse_one`]: fn.parse_one.html
//! [`ParseResult`]: enum.ParseResult.html
//! [`parse_expression`]: fn.parse_expression.html

use sexp::Sexp;
use span::{Span, ByteSpan};


// Parsing Types ///////////////////////////////////////////////////////////////

/// Represents what to do next in partially completed parsing.
///
/// `ParseResult` is returned from all intermediate parsers. If you just want to
/// get back parsed s-expressions, you won't need to worry about this type since
/// the top level parsers just return a `Result`.
///
/// If the parser failed to produce a result, it will return `Error`, and if it
/// succeeded we'll get the `Done` variant containing the value produced and the
/// rest of the text to work on.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseResult<'a, T, E> {
    /// The parser succeeded, this contains first the un-consumed portion of the
    /// input then the result produced by parsing.
    Done(&'a str, T),
    /// The parser failed, the `E` represents the reason for the failure.
    Error(E),
}

/// Indicates how parsing failed.
///
/// Most `ParseError` variants contain a `Box<ParseError>` that represents the
/// cause of that error. Using this, `ParseError` variants can be chained to
/// produce a more complete picture of what exactly went wrong during parsing.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ParseError<Loc=ByteSpan> where Loc: Span {
    /// Parsing reached the end of input where not expecting to, usually this
    /// will be contained inside another `ParseError` like `String(box
    /// UnexpectedEof, ...)` which indicates that the closing quote was never
    /// found.
    UnexpectedEof,
    /// Some problem occurred while parsing a list, along with the cause of that
    /// error.
    List(Box<ParseError>, Loc),
    /// Some problem occurred while parsing an s-expression. This will only be
    /// generated if EOF is reached unexpectedly at the beginning of
    /// `parse_expression`, so it should probably be removed.
    Sexp(Box<ParseError>, Loc),
    /// Some problem occurred while parsing a character literal, along with the
    /// cause of the error.
    Char(Box<ParseError>, Loc),
    /// Some problem occurred while parsing a string literal, along with the
    /// cause of the error.
    String(Box<ParseError>, Loc),
    /// Some problem occurred while parsing a symbol, along with the cause of
    /// the error.
    Symbol(Box<ParseError>, Loc),
    /// Some problem occurred while parsing a number literal, along with the
    /// cause of the error.
    Number(Box<ParseError>, Loc),
    /// An unexpected character was found. This will usually be the root cause
    /// in some chain of `ParseError`s.
    Unexpected(char, Loc::Begin),
}
use self::ParseResult::*;


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

macro_rules! consume_whitespace {
    ($input:expr, $start_loc:expr, $ErrorFn:expr) => {
        if let Some(pos) = $input.find(|c: char| !c.is_whitespace()) {
            (&$input[pos..], $start_loc + pos)
        } else {
            return Error($ErrorFn(
                Box::new(ParseError::UnexpectedEof),
                ($input.len(), $input.len()).offset($start_loc)));
        }
    }
}


// Top Level Parsers ///////////////////////////////////////////////////////////

/// Parse a sequence of s-expressions.
///
/// This function returns `(Vec<Sexp>, Option<ParseError>)` so that it can
/// return partial results, for when some component parses successfully and a
/// later part fails.
///
/// # Errors
///
/// If the text contains an invalid s-expression (imbalanced parenthesis,
/// quotes, invalid numbers like 123q, etc.) then the parser will stop and
/// return an error. Every s-expression before that point that successfully
/// parsed will still be returned.
///
/// # Examples
///
/// We can get useful partial results
///
/// ```rust
/// # use ess::parser::parse;
/// let (exprs, err) = parse("1 2 3 ( 4");
/// assert_eq!(exprs.len(), 3);
/// assert!(err.is_some());
/// ```
pub fn parse(mut input: &str) -> (Vec<Sexp>, Option<ParseError>) {
    let mut start_loc = 0;
    let mut results = Vec::new();
    loop {
        match parse_expression(input, start_loc) {
            Done(rest, result) => {
                input = rest;
                start_loc = result.get_loc().1;
                results.push(result);
                if rest.trim() == "" {
                    return (results, None);
                }
            }
            Error(err) => {
                return (results, Some(err));
            }
        }
    }
}

/// Parses a single s-expression, ignoring any trailing text.
///
/// This function returns a pair of the parsed s-expression and the tail of the text.
///
/// # Errors
///
/// If the text begins with an invalid s-expression (imbalanced parenthesis,
/// quotes, invalid numbers like 123q, etc.) then the parser will return an
/// error. Any text after the first s-expression doesn't affect the parsing.
///
/// # Examples
///
/// ```rust
/// # use ess::parser::parse_one;
/// let (expr, rest) = parse_one("1 (").unwrap();
/// assert_eq!(rest, " (");
/// ```
pub fn parse_one(input: &str) -> Result<(Sexp, &str), ParseError> {
    match parse_expression(input, 0) {
        Done(rest, result) => Ok((result, rest)),
        Error(err) => Err(err),
    }
}


// Core Parsers ////////////////////////////////////////////////////////////////

// TODO: All of these parsers deserve docs, but since they're somewhat internal
// parsers, it's less critical than the rest of the API.

#[allow(missing_docs)]
pub fn parse_expression(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let (input, start_loc) = consume_whitespace!(input, start_loc, ParseError::Sexp);

    match input.chars().next() {
        Some('0'...'9') => parse_number(input, start_loc),
        Some('(') => parse_list(input, start_loc),
        Some('#') => parse_character(input, start_loc),
        Some('"') => parse_string(input, start_loc),
        Some('\'') => {
            match parse_expression(&input[1..], start_loc + 1) {
                Done(rest, result) => {
                    let span = *result.get_loc();
                    let quote_span = (0, 1).offset(start_loc);
                    Done(rest,
                         Sexp::List(vec![Sexp::Sym("quote".into(), quote_span), result],
                                    quote_span.union(&span)))
                }
                err => err,
            }
        }
        Some('`') => {
            match parse_expression(&input[1..], start_loc + 1) {
                Done(rest, result) => {
                    let span = *result.get_loc();
                    let quote_span = (0, 1).offset(start_loc);
                    Done(rest,
                         Sexp::List(vec![Sexp::Sym("quasiquote".into(), quote_span),
                                         result],
                                    quote_span.union(&span)))
                }
                err => err,
            }
        }
        Some(_) => parse_symbol(input, start_loc),
        None => unreachable!(),
    }
}

#[allow(missing_docs)]
pub fn parse_list(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let (input, start_loc) = consume_whitespace!(input, start_loc, ParseError::List);

    match input.chars().nth(0) {
        Some('(') => (),
        Some(c) =>
            return Error(ParseError::List(
                Box::new(ParseError::Unexpected(c, 0)),
                (0, 0).offset(start_loc))),
        None => unreachable!(),
    }

    let mut input = &input[1..];
    let mut loc = start_loc + 1;
    let mut members = Vec::new();
    loop {
        {
            let (new_input, new_loc) = consume_whitespace!(input, loc, ParseError::List);
            input = new_input;
            loc = new_loc;
        }

        match input.chars().nth(0) {
            Some(')') =>
                return Done(&input[1..],
                            Sexp::List(members, (start_loc, loc+1))),
            Some(_) => (),
            None => unreachable!(),
        }

        match parse_expression(input, loc) {
            Done(new_input, member) => {
                loc = member.get_loc().1;
                members.push(member);
                input = new_input;
            }
            Error(err) =>
                return Error(ParseError::List(
                    Box::new(err),
                    (0, 0).offset(loc)))
        }
    }
}

#[allow(missing_docs)]
pub fn parse_number(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let (input, start_loc) = consume_whitespace!(input, start_loc, ParseError::Number);

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

#[allow(missing_docs)]
pub fn parse_symbol(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let (input, start_loc) = consume_whitespace!(input, start_loc, ParseError::Symbol);

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

#[allow(missing_docs)]
pub fn parse_string(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let (input, start_loc) = consume_whitespace!(input, start_loc, ParseError::String);

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

#[allow(missing_docs)]
pub fn parse_character(input: &str, start_loc: usize) -> ParseResult<Sexp, ParseError> {
    let (input, start_loc) = consume_whitespace!(input, start_loc, ParseError::Char);

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
    use sexp::Sexp;
    use span::Span;
    use parser::*;
    use parser::ParseResult::*;

    #[test]
    fn test_parse() {
        assert_eq!(parse("1 2 3"), (vec![
            Sexp::Int(1, (0, 1)), Sexp::Int(2, (2, 3)), Sexp::Int(3, (4, 5))
        ], None));
        assert_eq!(parse("1 2 )"), (vec![
            Sexp::Int(1, (0, 1)), Sexp::Int(2, (2, 3))
        ], Some(ParseError::Symbol(Box::new(ParseError::Unexpected(')', 4)), (4, 4)))));
    }

    #[test]
    fn test_parse_one() {
        assert_eq!(parse_one("1 2"),
                   Ok((Sexp::Int(1, (0, 1)), " 2")));
    }

    #[test]
    fn test_parse_expression() {
        assert_eq!(parse_expression("	1", 0),
                   Done("", Sexp::Int(1, (1, 2))));
        assert_eq!(parse_expression("2.2", 0),
                   Done("", Sexp::Float(2.2, (0, 3))));
        assert_eq!(parse_expression(" a", 0),
                   Done("", Sexp::Sym("a".into(), (1, 2))));
        assert_eq!(parse_expression("#\\c", 0),
                   Done("", Sexp::Char('c', (0, 3))));
        assert_eq!(parse_expression(r#""hi""#, 0),
                   Done("", Sexp::Str("hi".into(), (0, 4))));
        assert_eq!(parse_expression("()", 0),
                   Done("", Sexp::List(vec![], (0, 2))));
        assert_eq!(parse_expression("( 1 2 3 )", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Int(1, (2, 3)),
                       Sexp::Int(2, (4, 5)),
                       Sexp::Int(3, (6, 7)),
                   ], (0, 9))));

        assert_eq!(parse_expression("", 0),
                   Error(ParseError::Sexp(Box::new(ParseError::UnexpectedEof), (0, 0))));
    }

    #[test]
    fn test_parse_expr_quote() {
        assert_eq!(parse_expression("'a", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quote".into(), (0, 1)),
                       Sexp::Sym("a".into(), (1, 2)),
                   ], (0, 2))));
        assert_eq!(parse_expression("'1", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quote".into(), (0, 1)),
                       Sexp::Int(1, (1, 2)),
                   ], (0, 2))));
        assert_eq!(parse_expression("' (1 2 3)", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quote".into(), (0, 1)),
                       Sexp::List(vec![
                           Sexp::Int(1, (3, 4)),
                           Sexp::Int(2, (5, 6)),
                           Sexp::Int(3, (7, 8)),
                       ], (2, 9)),
                   ], (0, 9))));

        assert_eq!(parse_expression("'", 0),
                   Error(ParseError::Sexp(Box::new(ParseError::UnexpectedEof), (1, 1))));
        assert_eq!(parse_expression("`'", 0),
                   Error(ParseError::Sexp(Box::new(ParseError::UnexpectedEof), (2, 2))));
    }

    #[test]
    fn test_parse_expr_quasiquote() {
        assert_eq!(parse_expression("`a", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quasiquote".into(), (0, 1)),
                       Sexp::Sym("a".into(), (1, 2)),
                   ], (0, 2))));
        assert_eq!(parse_expression("`1", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quasiquote".into(), (0, 1)),
                       Sexp::Int(1, (1, 2)),
                   ], (0, 2))));
        assert_eq!(parse_expression("` (1 2 3)", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quasiquote".into(), (0, 1)),
                       Sexp::List(vec![
                           Sexp::Int(1, (3, 4)),
                           Sexp::Int(2, (5, 6)),
                           Sexp::Int(3, (7, 8)),
                       ], (2, 9)),
                   ], (0, 9))));
        assert_eq!(parse_expression("`'a", 0),
                   Done("", Sexp::List(vec![
                       Sexp::Sym("quasiquote".into(), (0, 1)),
                       Sexp::List(vec![
                           Sexp::Sym("quote".into(), (1, 2)),
                           Sexp::Sym("a".into(), (2, 3)),
                       ], (1, 3)),
                   ], (0, 3))));

        assert_eq!(parse_expression("`", 0),
                   Error(ParseError::Sexp(Box::new(ParseError::UnexpectedEof), (1, 1))));
    }

    #[test]
    fn test_parse_list() {
        assert_eq!(parse_list("()", 0),
                   Done("", Sexp::List(vec![], (0, 2))));
        assert_eq!(parse_list("(1)", 0),
                   Done("", Sexp::List(vec![Sexp::Int(1, (1, 2))], (0, 3))));
        assert_eq!(parse_list("  ( 1    2  3 a )", 0), Done("", Sexp::List(vec![
            Sexp::Int(1, (4, 5)),
            Sexp::Int(2, (9, 10)),
            Sexp::Int(3, (12, 13)),
            Sexp::Sym("a".into(), (14, 15)),
        ], (2, 17))));
    }

    #[test]
    fn test_parse_number() {
        assert_eq!(parse_number("1", 0),
                   Done("", Sexp::Int(1, (0, 1))));
        assert_eq!(parse_number(" 13", 0),
                   Done("", Sexp::Int(13, (1, 3))));
        assert_eq!(parse_number("1.2", 0),
                   Done("", Sexp::Float(1.2, (0, 3))));
        assert_eq!(parse_number("\u{3000}4.2", 0),
                   Done("", Sexp::Float(4.2, (0, 3).offset('\u{3000}'.len_utf8()))));
        assert_eq!(parse_number(" 	42 ", 0),
                   Done(" ", Sexp::Int(42, (2, 4))));
        assert_eq!(parse_number(" 4.2  ", 0),
                   Done("  ", Sexp::Float(4.2, (1, 4))));
        assert_eq!(parse_number("1()", 0),
                   Done("()", Sexp::Int(1, (0, 1))));
        assert_eq!(parse_number("3.6()", 0),
                   Done("()", Sexp::Float(3.6, (0, 3))));

        assert_eq!(parse_number("", 0),
                   Error(ParseError::Number(Box::new(ParseError::UnexpectedEof), (0, 0))));
        assert_eq!(parse_number("123a", 0),
                   Error(ParseError::Number(Box::new(ParseError::Unexpected('a', 3)), (3, 3))));
        assert_eq!(parse_number("66.6+", 0),
                   Error(ParseError::Number(Box::new(ParseError::Unexpected('+', 4)), (4, 4))));
    }

    #[test]
    fn test_parse_ident() {
        assert_eq!(parse_symbol("+", 0),
                   Done("", Sexp::Sym("+".into(), (0, 1))));
        assert_eq!(parse_symbol(" nil?", 0),
                   Done("", Sexp::Sym("nil?".into(), (1, 5))));
        assert_eq!(parse_symbol(" ->socket", 0),
                   Done("", Sexp::Sym("->socket".into(), (1, 9))));
        assert_eq!(parse_symbol("fib(", 0),
                   Done("(", Sexp::Sym("fib".into(), (0, 3))));
        assert_eq!(parse_symbol("foo2", 0),
                   Done("", Sexp::Sym("foo2".into(), (0, 4))));

        // We reserve #foo for the implementation to do as it wishes
        assert_eq!(parse_symbol("#hi", 0),
                   Error(ParseError::Symbol(Box::new(ParseError::Unexpected('#', 0)), (0, 0))));
        // We reserve :foo for keywords
        assert_eq!(parse_symbol(":hi", 0),
                   Error(ParseError::Symbol(Box::new(ParseError::Unexpected(':', 0)), (0, 0))));

        assert_eq!(parse_symbol("", 0),
                   Error(ParseError::Symbol(Box::new(ParseError::UnexpectedEof), (0, 0))));
        assert_eq!(parse_symbol("0", 0),
                   Error(ParseError::Symbol(Box::new(ParseError::Unexpected('0', 0)), (0, 0))));
        assert_eq!(parse_symbol("()", 0),
                   Error(ParseError::Symbol(Box::new(ParseError::Unexpected('(', 0)), (0, 0))));
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(parse_string(r#""""#, 0),
                   Done("", Sexp::Str("".into(), (0, 2))));
        assert_eq!(parse_string(r#""hello""#, 0),
                   Done("", Sexp::Str("hello".into(), (0, 7))));
        assert_eq!(parse_string(r#"  "this is a nice string
with 0123 things in it""#, 0),
                   Done("", Sexp::Str("this is a nice string\nwith 0123 things in it".into(), (2, 48))));

        assert_eq!(parse_string("", 0),
                   Error(ParseError::String(Box::new(ParseError::UnexpectedEof), (0, 0))));
        assert_eq!(parse_string(r#""hi"#, 0),
                   Error(ParseError::String(Box::new(ParseError::UnexpectedEof), (0, 3))));
    }

    #[test]
    fn test_parse_char() {
        assert_eq!(parse_character(r#"#\""#, 0), Done("", Sexp::Char('"', (0, 3))));
        assert_eq!(parse_character(r#"#\ "#, 0), Done("", Sexp::Char(' ', (0, 3))));
        assert_eq!(parse_character(r#"  #\\"#, 0), Done("", Sexp::Char('\\', (2, 5))));

        assert_eq!(parse_character("", 0),
                   Error(ParseError::Char(Box::new(ParseError::UnexpectedEof), (0, 0))));
        assert_eq!(parse_character("#", 0),
                   Error(ParseError::Char(Box::new(ParseError::UnexpectedEof), (1, 1))));
        assert_eq!(parse_character("#\\", 0),
                   Error(ParseError::Char(Box::new(ParseError::UnexpectedEof), (2, 2))));
        assert_eq!(parse_character("a", 0),
                   Error(ParseError::Char(Box::new(ParseError::Unexpected('a', 0)), (0, 0))));
    }
}
