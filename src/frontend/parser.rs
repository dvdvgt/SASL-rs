//! Recursive descent parser implementation

use std::collections::VecDeque;
use std::error::Error;

use super::ast::{Expr, Op};
use super::token::{Token, Type};
use crate::error::SaslError::ParseError;

pub struct Parser<'a> {
    tokens: &'a mut VecDeque<Token<'a>>,
}

type ParserResult<'a> = Result<Expr<'a>, Box<dyn Error>>;

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a mut VecDeque<Token<'a>>) -> Self {
        Self { tokens }
    }

    //-------
    // HELPER
    //-------

    fn match_next_token(&mut self, expected_types: &[Type]) -> Option<Token<'a>> {
        for t in expected_types {
            match self.peek() {
                Some(tok) if tok.typ == *t => {
                    return self.advance();
                }
                _ => (),
            }
        }
        None
    }

    fn advance(&mut self) -> Option<Token<'a>> {
        self.tokens.pop_back()
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.back()
    }
}
