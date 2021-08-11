//! This module contains some useful macros for manipulating and accessing values with 
//! Rc<RefCell<AstNode>> which usually requires quite a lot of verbose, boilerplate code
//! which can be avoided with these convenience macros.

/// Clone the reference of either the left or right child of an App node.
/// 
/// If the node is not an App node the macro panics.
#[macro_export]
macro_rules! get_app_child {
    (rhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::App(_, rhs) => Rc::clone(rhs),
            _ => panic!("get_app_child: Expected App node."),
        }
    };
    (lhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::App(lhs, _) => Rc::clone(lhs),
            _ => panic!("get_app_child: Expected App node."),
        }
    };
}

/// Clone either the left or right reference of a Pair node.
/// 
/// If the node is not a Pair node the macro panics.
#[macro_export]
macro_rules! get_pair_child {
    (rhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::Pair(_, rhs) => Rc::clone(rhs),
            _ => panic!("get_pair_child: Expected Pair node."),
        }
    };
    (lhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::Pair(lhs, _) => Rc::clone(lhs),
            _ => panic!("get_pair_child: Expected Pair node."),
        }
    };
}

/// Set the left or right child of an App node. 
/// 
/// Be wary and make sure the borrowing rules are upheld during runtime otherwise the 
/// program panics.
#[macro_export]
macro_rules! set_app_child_value {
    ( rhs($app_node:expr) = $node:expr ) => {
        if let AstNode::App(_, rhs) = &*$app_node.borrow() {
            *rhs.borrow_mut() = $node;
        };
    };
    ( lhs($app_node:expr) = $node:expr ) => {
        if let AstNode::App(lhs, _) = &*$app_node.borrow() {
            *lhs.borrow_mut() = $node;
        };
    };
}

/// Check the type of a given AstNode and return true upon match.
#[macro_export]
macro_rules! check_type {
    ($nodeptr:expr; number) => {
        if let AstNode::Constant(Type::Number(_)) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
    ($nodeptr:expr; boolean) => {
        if let AstNode::Constant(Type::Boolean(_)) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
    ($nodeptr:expr; nil) => {
        if let AstNode::Constant(Type::Nil) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
}

/// Clone the value encapsulated within a `Rc<RefCell<AstNode>>`.
#[macro_export]
macro_rules! get_const_val {
    ($node:expr; number) => {
        if let AstNode::Constant(Type::Number(x)) = &*$node.borrow() {
            x.clone()
        } else {
            panic!("Expected number.")
        }
    };
    ($node:expr; boolean) => {
        if let AstNode::Constant(Type::Boolean(x)) = &*$node.borrow() {
            x.clone()
        } else {
            panic!("Expected boolean.")
        }
    };
}

/// Matching AstNodes encapsulated within `Rc<RefCell<AstNode>>` is a bit verbose
/// so this macro saves some boilerplate code.
#[macro_export]
macro_rules! match_astnode {
    ($node:expr; app) => {
        if let AstNode::App(_, _) = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; S) => {
        if let AstNode::S = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; K) => {
        if let AstNode::K = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; I) => {
        if let AstNode::I = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; Y) => {
        if let AstNode::Y = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; U) => {
        if let AstNode::U = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; B) => {
        if let AstNode::B = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; C) => {
        if let AstNode::C = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; B_) => {
        if let AstNode::B_ = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; C_) => {
        if let AstNode::I = &*$node.borrow() {
            true
        } else {
            false
        }
    };
    ($node:expr; S_) => {
        if let AstNode::S_ = &*$node.borrow() {
            true
        } else {
            false
        }
    };
}