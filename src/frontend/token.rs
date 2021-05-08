use phf::phf_map;
use std::fmt;

use super::utils::Position;
use crate::T;

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    pub typ: Type,
    pub pos: Position,
    pub lexeme: &'a str,
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
    Eof
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f, "{}",
            match self {
                Type::String(x) => format!("String:{}", x),
                Type::Number(x) => format!("Number:{}", x),
                Type::Boolean(x) => format!("Boolean:{}", x),
                T![nil] => "nil".to_string(),
                T![def] => "Def".to_string(),
                T![where] => "where".to_string(),
                T![if] => "if".to_string(),
                T![then] => "then".to_string(),
                T![else] => "else".to_string(),
                T![and] => "and".to_string(),
                T![or] => "or".to_string(),
                T![not] => "not".to_string(),
                T![head] => "hd".to_string(),
                T![tail] => "tl".to_string(),
                T![+] => "+".to_string(),
                T![-] => "-".to_string(),
                T![*] => "*".to_string(),
                T![/] => "/".to_string(),
                T![=] => "=".to_string(),
                T![~=] => "~=".to_string(),
                T![<] => "<".to_string(),
                T![>] => ">".to_string(),
                T![<=] => "<=".to_string(),
                T![>=] => ">=".to_string(),
                T![ident] => "Identifier".to_string(),
                T![.] => ".".to_string(),
                T![,] => ",".to_string(),
                T![:] => ":".to_string(),
                T![;] => ";".to_string(),
                T!['('] => "(".to_string(),
                T![')'] => ")".to_string(),
                T!['['] => "[".to_string(),
                T![']'] => "]".to_string(),
                Type::Whitespace => " ".to_string(),
                T![eof] => "<EOF>".to_string()
            }
        )
    }
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

#[macro_export]
macro_rules! T {
    [+] => {
        $crate::frontend::token::Type::Plus
    };
    [-] => {
        $crate::frontend::token::Type::Minus
    };
    [*] => {
        $crate::frontend::token::Type::Mult
    };
    [/] => {
        $crate::frontend::token::Type::Div
    };
    [=] => {
        $crate::frontend::token::Type::Equal
    };
    [~=] => {
        $crate::frontend::token::Type::NotEqual
    };
    [<] => {
        $crate::frontend::token::Type::Less
    };
    [>] => {
        $crate::frontend::token::Type::Greater
    };
    [<=] => {
        $crate::frontend::token::Type::Leq
    };
    [>=] => {
        $crate::frontend::token::Type::Geq
    };
    [nil] => {
        $crate::frontend::token::Type::Nil
    };
    [and] => {
        $crate::frontend::token::Type::And
    };
    [or] => {
        $crate::frontend::token::Type::Or
    };
    [not] => {
        $crate::frontend::token::Type::Not
    };
    [head] => {
        $crate::frontend::token::Type::Head
    };
    [tail] => {
        $crate::frontend::token::Type::Tail
    };
    [ident] => {
        $crate::frontend::token::Type::Identifier
    };
    [def] => {
        $crate::frontend::token::Type::Def
    };
    [where] => {
        $crate::frontend::token::Type::Where
    };
    [if] => {
        $crate::frontend::token::Type::If
    };
    [then] => {
        $crate::frontend::token::Type::Then
    };
    [else] => {
        $crate::frontend::token::Type::Else
    };
    [.] => {
        $crate::frontend::token::Type::Dot
    };
    ['['] => {
        $crate::frontend::token::Type::LeftBrackets
    };
    [']'] => {
        $crate::frontend::token::Type::RightBrackets
    };
    ['('] => {
        $crate::frontend::token::Type::LeftParenthese
    };
    [')'] => {
        $crate::frontend::token::Type::RightParenthese
    };
    [,] => {
        $crate::frontend::token::Type::Comma
    };
    [;] => {
        $crate::frontend::token::Type::Semicolon
    };
    [:] => {
        $crate::frontend::token::Type::Colon
    };
    [eof] => {
        $crate::frontend::token::Type::Eof
    };
}