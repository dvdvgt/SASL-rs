use std::{error::Error, fmt::Display, fmt};

use crate::frontend::utils::Position;

#[derive(Debug)]
pub struct SyntaxError {
    pos: Position,
    details: String
}

impl SyntaxError {
    pub fn new(pos: Position, details: String) -> Self {
        Self { pos, details }
    }
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Syntax error at {}: {}", self.pos, self.details)
    }
}

impl Error for SyntaxError {
    fn description(&self) -> &str {
        &self.details
    }
}
