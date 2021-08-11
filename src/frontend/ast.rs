//! This module contains all datastructures needed for creating and modifying the AST in the parser, compiler and virtual machine.

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

/// A convenience type alias for saving some screen estate and typing.
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
    /// Contains all global definitions which are accessible by
    /// the name (identifier) of the definition.
    pub global_defs: HashMap<Identifier, (Params, AstNodePtr)>,
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

    pub fn insert_defs(&mut self, defs: &HashMap<Identifier, (Params, AstNodePtr)>) {
        for (key, value) in defs {
            if !self.global_defs.contains_key(key) {
                self.global_defs.insert(key.clone(), value.clone());
            }
        }
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
///     - A pair which represents the headd and the tail of list.
///     - A bunch of combinators which are used in the reduction machine for evaluating
///     the final AST.
#[derive(Debug, Clone)]
pub enum AstNode {
    /// A local where definition containing the expression body which it belongs to
    /// and all the local definitions.
    /// ```text
    ///     Where
    ///    /     \
    ///  Body   Definitions
    /// ```
    Where(AstNodePtr, Vec<(Identifier, (Params, AstNodePtr))>),
    /// Function application used for currying functions
    App(AstNodePtr, AstNodePtr),
    /// Variable/function identifier
    Ident(String),
    /// Atomics
    Constant(Type),
    /// Predefinied functions
    Builtin(Op),
    /// Empty expression
    Empty,
    /// A pair represents the head and tail of a list
    Pair(AstNodePtr, AstNodePtr),
    // Combinators
    /// S-Combinator rule: `S @ f @ g @ x ~> f @ x @ (g @ x)`
    S,
    /// K-Combinator rule: `K @ x @ y = x`
    K,
    /// I-Combinator rule: `I @ x ~> x`
    I,
    /// Y-Combinator rule: `Y @ f ~> f @ (Y @ f)`
    Y,
    /// U-Combinator rule: `U @ f @ z ~> f @ (hd @ z) @ (tl @ z)`
    U,
    /// B-Combinator rule: `B @ f @ g @ x ~> f @ (g @ x)`
    B,
    /// B*-Combinator rule: `B* @ c @ f @ g @ x ~> c @ (f @ (g @ x))`
    B_,
    /// C-Combinator rule: `C @ f @ g @ x ~> f @ x @ g`
    C,
    /// C'-Combinator rule: `C' @ c @ f @ g @ x ~> c @ (f @ x) @ g`
    C_,
    /// S'-Combinator rule: `S' @ c @ f @ g @ x ~> c @ (f @ x) @ (g @ x)
    S_,
}

impl fmt::Display for AstNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                //AstNode::Where(Some(expr), _, Some(nested_where)) =>
                //format!("{} where {}", expr, nested_where),
                AstNode::Where(expr, defs) => format!("{} where {:?}", expr.borrow(), defs),
                //AstNode::Where(None, _, None) => "where".to_string(),
                AstNode::App(ast1, ast2) => format!("({} @ {})", ast1.borrow(), ast2.borrow()),
                AstNode::Ident(s) => format!("Id:{}", s),
                AstNode::Constant(t) => t.to_string(),
                AstNode::Pair(a, b) => format!("({} @_pair {})", a.borrow(), b.borrow()),
                AstNode::Builtin(op) => op.to_string(),
                AstNode::Empty => "".to_string(),
                AstNode::S => "S".to_string(),
                AstNode::K => "K".to_string(),
                AstNode::I => "I".to_string(),
                AstNode::Y => "Y".to_string(),
                AstNode::U => "U".to_string(),
                AstNode::B => "B".to_string(),
                AstNode::C => "C".to_string(),
                AstNode::S_ => "S_".to_string(),
                AstNode::B_ => "B_".to_string(),
                AstNode::C_ => "C_".to_string(),
            }
        )
    }
}

/// A convenience function for easily applying one node to the other. \
/// `astnode1, astnode2 ~> astnode1 @ astnode2`
pub(crate) fn apply2(astnode1: AstNodePtr, astnode2: AstNodePtr) -> AstNodePtr {
    ptr!(AstNode::App(astnode1, astnode2))
}

/// A convenience function for easily applying applying three nodes to each other. \
/// `astnode1, astnode2, astnode3 ~> (astnode1 @ astnode2) @ astnode3`
pub(crate) fn apply3(
    astnode1: AstNodePtr,
    astnode2: AstNodePtr,
    astnode3: AstNodePtr,
) -> AstNodePtr {
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
