use std::collections::HashMap;
use phf::{phf_map};

use super::utils::Position;

#[derive(Debug)]
pub struct Token<'a> {
    pub typ: Type,
    pos: Position,
    lexeme: &'a str
}

impl<'a> Token<'a> {
    pub fn new_non_literal(typ: Type, pos: Position, src: &'a str, range: std::ops::Range<usize>) -> Self {
        Self {
            typ, pos,
            lexeme: &src[range]
        }
    }
    pub fn new(typ: Type, pos: Position, lexeme: &'a str) -> Self {
        Self {
            typ, pos, lexeme
        }
    }

}

#[derive(Debug, PartialEq)]
pub enum Type {
    // Literals
    Number(f64),
    String(String),
    Boolean(bool),
    Nil,
    // keywords
    Def, Where, If, Then, Else,
    // Boolean operators
    And, Or, Not,
    // Builtin
    Head, Tail,
    // Unary/Binary operators
    Plus, Minus, Mult, Div,

    Equal, NotEqual, Less, Greater, Leq, Geq,

    Identifier,

    Dot, LeftParenthese, RightParenthese, LeftBrackets, RightBrackets,

    Whitespace
}

static KEYWORDS: phf::Map<&'static str, Type> = phf_map! {
    "hd" => Type::Head
    // ...
};