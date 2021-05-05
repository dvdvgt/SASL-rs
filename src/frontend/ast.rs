//! Abstract syntax tree implementation.

use std::collections::HashMap;

use super::{token::Token, utils::Position};

/// Represents a variable/function identifier.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Ident<'a> {
    name: &'a str,
    pos: Position
}

impl<'a> Ident<'a> {
    pub fn token_to_ident(t: Token<'a>) -> Self {
        Self {
            pos: t.pos, name: t.lexeme
        }
    }
}

/// Type alias for parameter vectors.
type Params<'a> = Vec<Ident<'a>>;

/// Represents a variable/function definition.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Def<'a> {
    pub name: Ident<'a>,
    pub params: Option<Params<'a>>
}

impl<'a> Def<'a> {
    /// True if the definition has parameters i.e. is a function.
    pub fn is_func(&self) -> bool {
        match self.params {
            Some(_) => true,
            _ => false
        }
    }

    /// True if the definition does not have parameters i.e. is a constant.
    pub fn is_const(&self) -> bool {
        !self.is_func()
    }
}

/// Represents either a local or global environment
/// with defintions of variables or functions.
#[derive(Debug)]
pub struct Env<'a> {
    defs: HashMap<Def<'a>, Expr<'a>>
}

impl<'a> Env<'a> {
    pub fn new() -> Self {
        Self { defs: HashMap::new() }
    }

    /// Insertion a new definition into the environment.
    pub fn add_def(&mut self, def: Def<'a>, expr: Expr<'a>) {
        self.defs.insert(def, expr);
    }

    /// looks up the corresponding AST/expression to a definition.
    pub fn lookup_def(&self, def: &Def<'a>) -> Option<&Expr<'a>> {
        self.defs.get(def)
    }
}

#[derive(Debug)]
/// Everything is an expression in SASL.
pub enum Expr<'a> {
    // Local and global environments
    Program(Env<'a>, Box<Expr<'a>>),
    Where(Env<'a>, Box<Expr<'a>>),
    /// Function application used for currying functions
    App(Box<Expr<'a>>, Box<Expr<'a>>),
    // Variable/function identifier
    Ident(Ident<'a>),
    // Atomics
    Constant(Token<'a>),
    // Predefinied functions
    Builtin(Token<'a>),
    // Conditional expression / teneray operator
    Cond,
    // Empty expression
    Empty,
}
