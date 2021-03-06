//! Various different utility structs and function used throughout the project.

use std::fmt::{Display, Formatter, Result};

/// Position of a `Token` in the source file/source code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Position {
    pub line: u32,
    pub start_column: u32,
    pub end_column: u32,
}

impl Display for Position {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "({:?}, {:?}-{:?})",
            self.line, self.start_column, self.end_column
        )
    }
}

impl Position {
    pub fn new(line: u32, start_column: u32, end_column: u32) -> Self {
        Self {
            line,
            start_column,
            end_column,
        }
    }

    /// Increment the column counter by 1
    pub fn next_column(&mut self) {
        self.end_column += 1;
    }

    /// Increment the line counter by 1 and reset the column count
    pub fn next_line(&mut self) {
        self.line += 1;
        self.end_column = 1;
    }
}
