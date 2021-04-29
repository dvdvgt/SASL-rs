//! Token

use std::{collections::VecDeque, error::Error, iter::Peekable, str::Chars};

use super::{token::{Token, Type}, utils::Position};
use crate::error::SyntaxError;

pub struct Lexer<'a> {
    source: &'a str,
    chars: Peekable<Chars<'a>>,
    tokens: VecDeque<Token<'a>>,
    token_pos: Position,
    start_idx: usize,
    current_idx: usize
}

type LexerResult<'a> = Result<Token<'a>, Box<Error>>;

impl<'a> Lexer<'a> {
    // Create a new instance of `Lexer`
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.chars().peekable(),
            tokens: VecDeque::new(),
            token_pos: Position::new(1, 1, 0),
            start_idx: 0,
            current_idx: 0
        }
    }

    /// Tokenize source string.
    pub fn tokenize(&mut self) -> Result<&VecDeque<Token<'a>>, Box<Error>> {
        while !self.is_at_end() {
            self.start_idx = self.current_idx;
            let token = self.next_token()?;
            if token.typ != Type::Whitespace {
                self.tokens.push_back(token);
            }
            self.token_pos.start_column = self.token_pos.end_column + 1;
        }
        Ok(&self.tokens)
    }

    /// Return the next token.
    fn next_token(&mut self) -> LexerResult<'a> {
        match self.advance() {
        Some('(') => self.new_token(Type::LeftParenthese),
        Some(')') => self.new_token(Type::RightParenthese),
        Some('[') => self.new_token(Type::LeftBrackets),
        Some(']') => self.new_token(Type::RightBrackets),
        Some('.') => self.new_token(Type::Dot),

        Some('=') => self.new_token(Type::Equal),
        Some('~') if self.chars.peek() == Some(&'=') => {
            self.advance();
            self.new_token(Type::NotEqual)
        },
        Some('<') => match self.advance_if(&'=') {
            Some(_) => self.new_token(Type::Leq),
            _ => self.new_token(Type::Less)
        },
        Some('>') => match self.advance_if(&'=') {
            Some(_) => self.new_token(Type::Geq),
            _ => self.new_token(Type::Greater)
        }
        Some('+') => self.new_token(Type::Plus),
        Some('-') => self.new_token(Type::Minus),
        Some('*') => self.new_token(Type::Mult),
        Some('/') => match self.advance_if(&'/') {
            Some(_) => {
                self.advance_while(&|x| x != &'\n');
                self.new_token(Type::Whitespace)
            }
            _ => self.new_token(Type::Div)
        }

        Some(' ') | Some('\t') => self.new_token(Type::Whitespace),
        // Literals
        Some(c) => self.number(),
        _ => todo!()
        }
    }

    //-------
    // HELPER
    //-------

    fn new_token(&self, typ: Type) -> LexerResult<'a> {
        Ok(Token::new_non_literal(typ, self.token_pos, self.source, self.start_idx..self.current_idx))
    }
    
    /// Consume the current iterator and return the char it pointed at.
    /// If the iterator reached the `None` will be returned.
    fn advance(&mut self) -> Option<char> {
        self.token_pos.next_column();
        self.current_idx += 1;
        self.chars.next()
    }

    fn advance_if(&mut self, expected: &char) -> Option<char> {
        match self.chars.peek() {
            Some(c) if c == expected => self.advance(),
            _ => None
        }
    }

    /// Consumes all iterators while a given predicate is fullfilled.
    /// 
    /// ## Example
    /// advance_while(&mut self, &|c| c.is_alphabetic());
    fn advance_while(&mut self, predicate: &Fn(&char) -> bool) {
        loop {
            match self.chars.peek() {
                Some(c) if !predicate(c) => break,
                Some(c) => {
                    if c == &'\n' {
                        self.token_pos.next_line();
                    }
                    self.advance();
                }
                None => break
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

    fn number(&mut self) -> LexerResult<'a> {
        self.advance_while(&|c| c.is_digit(10));
        if self.chars.peek() == Some(&'.') {
            self.advance();
            if !self.chars.peek().unwrap().is_digit(10) {
                return Err(Box::new(SyntaxError::new(self.token_pos, "expected floating point number.".to_string())));
            }
            self.advance_while(&|c| c.is_digit(10))
        }
        let val: f64 = self.source[self.start_idx..self.current_idx].parse().unwrap();
        Ok(Token::new(Type::Number(val), self.token_pos, &self.source[self.start_idx..self.current_idx]))     
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
    fn test_advance_while() {
        let mut lx = Lexer::new("ej0d2e9j0ej");
        lx.advance_while(&|x| x.is_alphanumeric());
        assert_eq!(lx.is_at_end(), true);
        let mut lx2 = Lexer::new("123.45678");
        lx2.advance_while(&|x| x.is_digit(10));
        assert_eq!(lx2.advance(), Some('.'));
    }

    #[test]
    fn test_tokenize() {
        let mut lx = Lexer::new("(123.34 = 12) // A comment that will be ignored");
        println!("{:?}", lx.tokenize().unwrap());
    }
}
