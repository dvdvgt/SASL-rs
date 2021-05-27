//! Abstract syntax tree datastructures.
//! In here are all datastructures needed for creating the AST in the parser.

use std::{collections::HashMap, fmt};

use super::token::Type;

/// Represents a definition in SASL consisting of a name and
/// a (optional) number of parameters.
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

/// Represents the whole abstract syntax tree which consists of
///     - Global definitions stored in a hash map. Each global definition is a
///     direct child of the root node.
///     - The body which consists of a single expression which is seperated from
///     the global definitions by a dot ('.').
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

impl Default for Ast {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
/// Basic nodes of which the AST consists.
///     - Identifiers, constants and builtins are always leave nodes
///     - App is short for function application and is used for currying functions
///     - Where is how local definition are defined in SASL
///     - Empty represents an empty expression which is used throughout the parser
///     implementation but never actually stored in the AST.
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
                AstNode::Where(None, _, None) => "where".to_string(),
                AstNode::App(ast1, ast2) => format!("({} @ {})", ast1, ast2),
                AstNode::Ident(s) => format!("Id:{}", s),
                AstNode::Constant(t) => t.to_string(),
                AstNode::Builtin(op) => op.to_string(),
                AstNode::Empty => "empty".to_string(),
                _ => "unkown".to_string()
            }
        )
    }
}

/// Different types of operations. In SASL there are three types:
///     - Prefix operations like -, not
///     - Infox operations like all arthimetic operations
///     - The ternary operator: if a then b else c
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
