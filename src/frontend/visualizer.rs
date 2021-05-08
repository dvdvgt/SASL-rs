//! Functionality concerned with visualizing an AST as tree with the help of Graphviz and the DOT DSL.

use super::ast::AstNode;

pub struct Visualizer<'a> {
    ast: &'a AstNode,
    
}