//! Abstract syntax tree implementation.

use std::{collections::HashMap, fmt};

use super::{token::Type};

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Def {
    pub name: String,
    pub params: Option<Vec<String>>
}

impl Def {
    pub fn new(name: String, params: Option<Vec<String>>) -> Self {
        Self {
            name,
            params
        }
    }

    pub fn add_new_parameter(&mut self, param_name: &str) {
        match self.params {
            Some(ref mut vec) => vec.push(param_name.to_string()),
            None => {
                let vec = vec![param_name.to_string()];
                self.params = Some(vec)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Ast {
    pub global_defs: HashMap<Def, AstNode>,
    //root: AstNode,
    pub body: AstNode,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            global_defs: HashMap::new(),
            body: AstNode::Empty
        }
    }
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{} . {}",
            "defs", self.body
        )
    }
}

#[derive(Debug, Clone)]
/// Everything is an expression in SASL.
pub enum AstNode {
    Where(Option<Box<AstNode>>, HashMap<Def, AstNode>, Option<Box<AstNode>>),
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
                AstNode::Where(Some(expr), _, Some(nested_where)) => format!("{} where {}", expr, nested_where),
                AstNode::Where(Some(expr), _, None) => format!("{} where", expr),
                AstNode::Where(None, _, None) => format!("where"),
                AstNode::App(ast1, ast2) => format!("({} @ {})", ast1, ast2),
                AstNode::Ident(s) => format!("var:{}", s),
                AstNode::Constant(t) => t.to_string(),
                AstNode::Builtin(op) => format!("{}", op),
                AstNode::Empty => "empty".to_string(),
                _ => "unkown".to_string()
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
