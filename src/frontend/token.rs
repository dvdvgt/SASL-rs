use phf::phf_map;
use std::fmt;

use super::utils::Position;

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    pub typ: Type,
    pub pos: Position,
    lexeme: &'a str,
}

impl<'a> Token<'a> {
    pub fn new_non_literal(
        typ: Type,
        pos: Position,
        src: &'a str,
        range: std::ops::Range<usize>,
    ) -> Self {
        Self {
            typ,
            pos,
            lexeme: &src[range],
        }
    }
    pub fn new(typ: Type, pos: Position, lexeme: &'a str) -> Self {
        Self { typ, pos, lexeme }
    }

    pub fn get_keyword(key: &str) -> Option<Type> {
        match KEYWORDS.get(key) {
            Some(tok) => Some(tok.clone()),
            _ => None,
        }
    }
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{:?}: {} @ {}>", self.typ, self.lexeme, self.pos)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    // Literals
    Number(f64),
    String(String),
    Boolean(bool),
    Nil,
    // keywords
    Def,
    Where,
    If,
    Then,
    Else,
    // Boolean operators
    And,
    Or,
    Not,
    // Builtin
    Head,
    Tail,
    // Unary/Binary operators
    Plus,
    Minus,
    Mult,
    Div,

    Equal,
    NotEqual,
    Less,
    Greater,
    Leq,
    Geq,

    Identifier,

    Dot,
    LeftParenthese,
    RightParenthese,
    LeftBrackets,
    RightBrackets,
    Comma,
    Colon,
    Semicolon,

    Whitespace,
}

static KEYWORDS: phf::Map<&'static str, Type> = phf_map! {
    "hd" => Type::Head,
    "tl" => Type::Tail,
    "nil" => Type::Nil,
    "def" => Type::Def,
    "where" => Type::Where,
    "if" => Type::If,
    "then" => Type::Then,
    "else" => Type::Else,
    "or" => Type::Or,
    "and" => Type::And,
    "not" => Type::Not,
    "true" => Type::Boolean(true),
    "false" => Type::Boolean(false)
};
