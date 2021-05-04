//! Abstract syntax tree implementation.

use super::token::Token;

pub enum Op {
    // Basic arithmetic operations
    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    // Logic operations
    And,
    Or,
    Not,
    // Comparators
    Equal,
    NotEqual,
    Less,
    Greater,
    Leq,
    Geq,
    // Lists
    Cons,
    Head,
    Tail,
    // Conditional Expression
    Cond,
}

#[derive(Debug, PartialEq)]
/// Everything is an expression in SASL.
pub enum Expr<'a> {
    /// Function application used for currying functions.
    App(Box<Expr<'a>>, Box<Expr<'a>>),
    // Variables and function definitions
    Var(&'a str),
    FunctionDef(&'a str, Vec<&'a str>),
    // Atomics
    String(&'a str),
    Number(f64),
    Boolean(bool),
    Nil,
    /// A list contains a abritary number of elements of abritary types.
    List(Vec<Expr<'a>>),
    // Predefinied functions
    Builtin(Token<'a>),
    Empty,
}
