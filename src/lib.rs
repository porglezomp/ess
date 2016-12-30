//! A lightweight S-expression parser intended for language implementation.

// #![warn(missing_docs)]
#![deny(unsafe_code)]

pub mod sexp;
pub mod span;
pub mod parser;

pub use sexp::Sexp;
pub use parser::{parse, parse_one};
