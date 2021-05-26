//! The lexer struct is responsible for tokenizing the source code so that it can be used by the parser to create the AST.

use std::{collections::VecDeque, error::Error, iter::Peekable, str::Chars};

use super::{
    token::{Token, Type},
    utils::Position,
};
use crate::error::SaslError::SyntaxError;
use crate::T;

/// The lexer struct is responsible for the tokeniziation of the source code.
pub struct Lexer<'a> {
    /// Contains the source code. Used for 'cutting' out lexemes for the tokens.
    source: &'a str,
    /// Peekable iterator over all characters of the source string.
    chars: Peekable<Chars<'a>>,
    /// Vector where all the tokens are saved.
    tokens: VecDeque<Token<'a>>,
    /// The current relative position in the source code in repespect to the
    /// current line i.e. that the column is reset once a line break occurs.
    token_pos: Position,
    /// The current absolute starting position of a token.
    start_idx: usize,
    /// The current absolute position in the source code. 
    current_idx: usize,
}

type LexerResult<'a> = Result<Token<'a>, Box<dyn Error>>;

impl<'a> Lexer<'a> {
    /// Create a new instance of `Lexer`
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.chars().peekable(),
            tokens: VecDeque::new(),
            token_pos: Position::new(1, 1, 0),
            start_idx: 0,
            current_idx: 0,
        }
    }

    /// Tokenize source string.
    pub fn tokenize(&mut self) -> Result<VecDeque<Token<'a>>, Box<dyn Error>> {
        while !self.is_at_end() {
            self.start_idx = self.current_idx;
            let token = self.next_token()?;
            if token.typ != Type::Whitespace {
                self.tokens.push_back(token);
            }
            self.token_pos.start_column = self.token_pos.end_column + 1;
        }
        // Add end of file token at the end.
        self.start_idx = self.current_idx;
        self.tokens.push_back(
            Token::new(
                T![eof],
                Position::new(self.token_pos.line, self.start_idx as u32, self.current_idx as u32),
            "EOF"
            )
        );
        Ok(self.tokens.clone())
    }

    /// Return the next token.
    fn next_token(&mut self) -> LexerResult<'a> {
        match self.advance() {
            Some('(') => self.new_token(Type::LeftParenthese),
            Some(')') => self.new_token(Type::RightParenthese),
            Some('[') => self.new_token(Type::LeftBrackets),
            Some(']') => self.new_token(Type::RightBrackets),
            Some('.') => self.new_token(Type::Dot),
            Some(',') => self.new_token(Type::Comma),
            Some(':') => self.new_token(Type::Colon),
            Some(';') => self.new_token(Type::Semicolon),
            Some('=') => self.new_token(Type::Equal),
            Some('~') if self.chars.peek() == Some(&'=') => {
                self.advance();
                self.new_token(Type::NotEqual)
            }
            Some('<') => match self.advance_if(&|x| x == &'=') {
                Some(_) => self.new_token(Type::Leq),
                _ => self.new_token(Type::Less),
            },
            Some('>') => match self.advance_if(&|x| x == &'=') {
                Some(_) => self.new_token(Type::Geq),
                _ => self.new_token(Type::Greater),
            },
            Some('+') => self.new_token(Type::Plus),
            Some('-') => self.new_token(Type::Minus),
            Some('*') => self.new_token(Type::Mult),
            Some('/') => match self.advance_if(&|x| x == &'/') {
                Some(_) => {
                    self.advance_while(&|x| x != &'\n');
                    self.new_token(Type::Whitespace)
                }
                _ => self.new_token(Type::Div),
            },

            Some(' ') | Some('\t') | Some('\r') => self.new_token(Type::Whitespace), // Whitespaces will be discarded
            Some('\n') => {
                self.token_pos.next_line();
                self.new_token(Type::Whitespace)
            }
            Some('\"') => self.string(),
            // Literals, keywords
            Some(c) => {
                if c.is_digit(10) {
                    self.number()
                } else if c.is_alphabetic() {
                    self.keyword()
                } else {
                    Err(Box::new(SyntaxError {
                        pos: self.token_pos,
                        msg: "Invalid keyword/identifier.".to_string(),
                    }))
                }
            }
            _ => Err(Box::new(SyntaxError {
                pos: self.token_pos,
                msg: "Invalid input.".to_string(),
            })),
        }
    }

    //-------
    // HELPER
    //-------

    /// Extracts a substring from the source string starting at `start_index` and ending at `current_index`.
    fn get_substr_from_current_range(&self) -> &'a str {
        &self.source[self.start_idx..self.current_idx]
    }

    /// Convenience function for creating new `Token`s easily.
    fn new_token(&self, typ: Type) -> LexerResult<'a> {
        Ok(Token::new_non_literal(
            typ,
            self.token_pos,
            self.source,
            self.start_idx..self.current_idx,
        ))
    }

    /// Consume the current iterator and return the char it pointed at.
    /// If the iterator reached the `None` will be returned.
    fn advance(&mut self) -> Option<char> {
        self.token_pos.next_column();
        self.current_idx += 1;
        self.chars.next()
    }

    /// Only advance the iterator if the next character is the expected one.
    fn advance_if(&mut self, predicate: &dyn Fn(&char) -> bool) -> Option<char> {
        match self.chars.peek() {
            Some(c) if predicate(c) => self.advance(),
            _ => None,
        }
    }

    /// Consumes all iterators while a given predicate is fullfilled.
    ///
    /// ## Example
    /// advance_while(&mut self, &|c| c.is_alphabetic());
    fn advance_while(&mut self, predicate: &dyn Fn(&char) -> bool) {
        loop {
            match self.chars.peek() {
                Some(c) if !predicate(c) => break,
                Some(c) => {
                    if c == &'\n' {
                        self.token_pos.next_line();
                    }
                    self.advance();
                }
                None => break,
            }
        }
    }

    /// Check if the char iterator has reached the end.
    fn is_at_end(&mut self) -> bool {
        self.chars.peek() == None
    }

    //---------
    // Literals
    //---------

    /// Tokenize a number literal.
    fn number(&mut self) -> LexerResult<'a> {
        self.advance_while(&|c| c.is_digit(10));
        if self.chars.peek() == Some(&'.') {
            self.advance();
            if let Some(num) = self.chars.peek() {
                if !num.is_digit(10) {
                    return Err(Box::new(SyntaxError {
                        pos: self.token_pos,
                        msg: "Expected floating point number.".to_string(),
                    }));
                }
            } else {
                return Err(Box::new(SyntaxError {
                    pos: self.token_pos,
                    msg: "Expected floating point number.".to_string(),
                }));
            }
            self.advance_while(&|c| c.is_digit(10))
        }
        let val: f64 = self.source[self.start_idx..self.current_idx]
            .parse()
            .unwrap();
        Ok(Token::new(
            Type::Number(val),
            self.token_pos,
            &self.get_substr_from_current_range(),
        ))
    }

    /// Tokenize a string literal
    fn string(&mut self) -> LexerResult<'a> {
        // Advance until closing `"` is found or the iterator reaches the end in which case an
        // error is returned.
        while !self.is_at_end() && self.chars.peek() != Some(&'\"') {
            // Don't known whether multi-line strings should be implemented. Might complicate things quite a bit.
            //if self.chars.peek() == Some(&'\n') {
            //    self.token_pos.next_line();
            //}
            self.advance();
        }
        if self.is_at_end() {
            return Err(Box::new(SyntaxError {
                pos: self.token_pos,
                msg: "missing clossing \".".to_string(),
            }));
        }
        // Advance over "
        self.advance();

        let val = self.source[self.start_idx + 1..self.current_idx - 1].to_string();
        Ok(Token::new(
            Type::String(val),
            self.token_pos,
            &self.get_substr_from_current_range(),
        ))
    }

    //----------------------
    // Identifier & keywords
    //----------------------

    /// Checks whether the following character stream is a known keyword. If not it has to be an identifier.
    fn keyword(&mut self) -> LexerResult<'a> {
        self.advance_while(&|x| x.is_alphanumeric());
        let substr = self.get_substr_from_current_range();
        // If it's not a known keyword it has to be an identifier
        let typ = Token::get_keyword(substr).unwrap_or(Type::Identifier);
        self.new_token(typ)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_advance() {
        let mut lx = Lexer::new("1.23");
        assert_eq!(lx.advance(), Some('1'));
        assert_eq!(lx.token_pos.line, 1);
        assert_eq!(lx.token_pos.start_column, 1);
        assert_eq!(lx.token_pos.end_column, 1);
        assert_eq!(lx.advance(), Some('.'));
    }

    #[test]
    fn test_advance_if() {
        let mut lx = Lexer::new("1 + 2 * 5");
        assert_eq!(lx.advance_if(&|x| x.is_digit(10)), Some('1'));
        lx.advance();
        assert_eq!(lx.advance_if(&|x| x.is_alphanumeric()), None);
    }

    #[test]
    fn test_advance_while() {
        let mut lx = Lexer::new("ej0d2e9j0ej");
        lx.advance_while(&|x| x.is_alphanumeric());
        assert_eq!(lx.is_at_end(), true);
        let mut lx2 = Lexer::new("123.45678");
        lx2.advance_while(&|x| x.is_digit(10));
        assert_eq!(lx2.advance(), Some('.'));
    }
}
