//! This module contains the SaslError enum which is used throughout the compiler for returning informative
//! errors to the user in order to simplify debugging of the source code.

use std::{error::Error, fmt, fmt::Display};

use crate::frontend::position::Position;

/// A `SaslError` distinguishes between different stages of the compiler so that
/// different instance of `SaslError` is used in regard to the occurence of the error.
/// This helps narrowing down potential bugs in the compiler.
#[derive(Debug, PartialEq)]
pub enum SaslError {
    /// An error occuring while tokenizing.
    SyntaxError { pos: Position, msg: String },
    /// An error occuring while parsing the tokens.
    ParseError { pos: Position, msg: String },
    /// An error occuring while evaluating, reducing or abstracting the AST.
    CompilerError { msg: String },
}

impl Display for SaslError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SaslError::SyntaxError { pos, msg } => write!(f, "Syntax error at {}: {}", pos, msg),
            SaslError::ParseError { pos, msg } => write!(f, "Parse error at {}: {}", pos, msg),
            SaslError::CompilerError { msg } => write!(f, "Compilation error: {}", msg),
        }
    }
}

impl Error for SaslError {
    fn description(&self) -> &str {
        match self {
            SaslError::SyntaxError { pos: _, msg } => msg,
            SaslError::ParseError { pos: _, msg } => msg,
            SaslError::CompilerError { msg } => msg,
        }
    }
}
