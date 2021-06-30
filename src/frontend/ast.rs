//! Abstract syntax tree datastructures.
//! In here are all datastructures needed for creating the AST in the parser.

use std::{cell::RefCell, collections::HashMap, fmt, ops::Deref, rc::Rc};

use super::token::Type;
use crate::ptr;

/// Represents a definition in SASL consisting of a name and
/// a (optional) number of parameters.
#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Def {
    pub name: Identifier,
    pub params: Params,
}

impl Def {
    pub fn new(name: String, params: Option<Vec<String>>) -> Self {
        Self { name, params }
    }

    /// Add a new parameter name to the definition.
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

pub type AstNodePtr = Rc<RefCell<AstNode>>;

/// A vector of identifiers (strings) which may or may not exist depending on the
/// type of definition. A constant definition does not have any parameters whereas
/// a function definition has at least one parameter.
/// # Example
/// `def f x y` has the `Params` `Some(vec!["x".to_string(), "y".to_string()])`
pub type Params = Option<Vec<Identifier>>;

/// An identifier is a string representing the name of either constant or function
/// name.
pub type Identifier = String;

/// Represents the whole abstract syntax tree which consists of
///     - Global definitions stored in a hash map. Each global definition is a
///     direct child of the root node.
///     - The body which consists of a single expression which is seperated from
///     the global definitions by a dot ('.') in the source code.
#[derive(Debug, Clone)]
pub struct Ast {
    pub global_defs: HashMap<Identifier, (Params, AstNodePtr)>,
    //root: AstNode,
    pub body: AstNodePtr,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            global_defs: HashMap::new(),
            body: ptr!(AstNode::Empty),
        }
    }

    pub fn lookup(&self, def: &str) -> Option<&(Params, AstNodePtr)> {
        self.global_defs.get(def)
    }
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} . {}", "defs", self.body.deref().borrow())
    }
}

impl Default for Ast {
    fn default() -> Self {
        Self::new()
    }
}

/// Basic nodes of which the AST consists.
///     - Identifiers, constants and builtins are always leave nodes
///     - App is short for function application and is used for currying functions
///     - Where is how local definition are defined in SASL
///     - Empty represents an empty expression which is used throughout the parser
///     implementation but never actually stored in the AST.
#[derive(Debug, Clone)]
pub enum AstNode {
    Where(
        AstNodePtr,
        HashMap<Identifier, (Params, AstNodePtr)>,
    ),
    /// Function application used for currying functions
    App(AstNodePtr, AstNodePtr),
    // Variable/function identifier
    Ident(String),
    // Atomics
    Constant(Type),
    // Predefinied functions
    Builtin(Op),
    // Empty expression
    Empty,
    Pair(AstNodePtr ,AstNodePtr),
    // Combinators
    S,
    K,
    I,
    Y,
    U,
}

impl fmt::Display for AstNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                //AstNode::Where(Some(expr), _, Some(nested_where)) =>
                    //format!("{} where {}", expr, nested_where),
                AstNode::Where(expr, _) => format!("{} where", expr.deref().borrow()),
                //AstNode::Where(None, _, None) => "where".to_string(),
                AstNode::App(ast1, ast2) => format!("({} @ {})", ast1.deref().borrow(), ast2.deref().borrow()),
                AstNode::Ident(s) => format!("Id:{}", s),
                AstNode::Constant(t) => t.to_string(),
	        AstNode::Pair(a,b) => format!("({} @ {})", a.deref().borrow(), b.deref().borrow()),
                AstNode::Builtin(op) => op.to_string(),
                AstNode::Empty => "empty".to_string(),
                AstNode::S => "S".to_string(),
                AstNode::K => "K".to_string(),
                AstNode::I => "I".to_string(),
                AstNode::Y => "Y".to_string(),
                AstNode::U => "U".to_string(),
            }
        )
    }
}

pub(crate) fn apply2(astnode1: AstNodePtr, astnode2: AstNodePtr) -> AstNodePtr {
    ptr!(AstNode::App(astnode1, astnode2))
}

pub(crate) fn apply3(astnode1: AstNodePtr, astnode2: AstNodePtr, astnode3: AstNodePtr) -> AstNodePtr {
    ptr!(AstNode::App(apply2(astnode1, astnode2), astnode3))
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
    Cond,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::PrefixOp(t) | Op::InfixOp(t) => t.to_string(),
                Op::Cond => "cond".to_string(),
            }
        )
    }
}
