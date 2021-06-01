use std::{error::Error, fmt, fmt::Display};

use crate::frontend::utils::Position;

#[derive(Debug)]
pub enum SaslError {
    SyntaxError { pos: Position, msg: String },
    ParseError { pos: Position, msg: String },
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
