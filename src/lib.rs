//! A lightweight S-expression parser intended for language implementation.

#![warn(missing_docs)]
#![deny(unsafe_code)]

pub mod parser;
pub mod sexp;
pub mod span;

pub use parser::{parse, parse_one};
pub use sexp::Sexp;
