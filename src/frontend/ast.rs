//! Abstract syntax tree implementation.

use std::{collections::HashMap, fmt};

use super::{token::Type, utils::Position};

#[derive(Debug, Hash, Clone, PartialEq)]
pub struct Def {
    name: String,
    params: Option<Vec<String>>
}

pub struct Ast {
    global_defs: HashMap<Def, AstNode>,
    //root: AstNode,
    body: AstNode,
}

#[derive(Debug, Clone)]
/// Everything is an expression in SASL.
pub enum AstNode {
    Where(Box<AstNode>, HashMap<Def, AstNode>),
    /// Function application used for currying functions
    App(Box<AstNode>, Box<AstNode>),
    // Variable/function identifier
    Ident(String),
    // Atomics
    Constant(Type),
    // Predefinied functions
    Builtin(Op),
    // Empty expression
    Empty,
}

impl fmt::Display for AstNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{}",
            match self {
                AstNode::Where(ast, defs) => format!("{} where", ast),
                AstNode::App(ast1, ast2) => format!("({} @ {})", ast1, ast2),
                AstNode::Ident(s) => format!("var:{}", s),
                AstNode::Constant(t) => t.to_string(),
                AstNode::Builtin(op) => format!("{}", op),
                AstNode::Empty => "empty".to_string()
            }
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Op {
    PrefixOp(Type),
    InfixOp(Type),
    //PostfixOp(Type),
    Cond
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{}", 
            match self {
                Op::PrefixOp(t) | Op::InfixOp(t) => t.to_string(),
                Op::Cond => "cond".to_string()
            }
        )
    }
}
