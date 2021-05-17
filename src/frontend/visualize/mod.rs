use super::visualize::graph::{Graph, Edge, Node};
use super::ast::{AstNode, Op};
use crate::frontend::token::Type;

use std::{process::{Command, Stdio}};
use std::{io::Write};

pub mod graph;

pub struct Visualizer {
    /// Counter used for giving each node a unique name.
    node_counter: u32,
    /// Graph that will be filled.
    pub graph: Graph
}


impl Visualizer {
    const NODE_NAME_PREFIX: &'static str = "node";

    pub fn new(graph_name: &str, is_directed: bool) -> Self {
        Self {
            node_counter: 1,
            graph: Graph::new(graph_name, is_directed)
        }
    }

    pub fn visualize_ast(&mut self, ast: &AstNode) {
        match ast {
            AstNode::Empty => (),
            AstNode::Ident(x) => self.add_node(format!("Id:{}", x)),
            AstNode::Where(Some(lhs_expr), _, _) => {
                let where_name = format!("{}{}", Visualizer::NODE_NAME_PREFIX, self.node_counter);
                self.add_node("where".to_string());

                let lhs_name = format!("{}{}", Visualizer::NODE_NAME_PREFIX, self.node_counter);
                self.add_edge(&where_name, &lhs_name);
                self.visualize_ast(lhs_expr);
            }
            // Constants
            AstNode::Constant(Type::String(x)) => self.add_node(format!("String:{}", x)),
            AstNode::Constant(Type::Number(x)) => self.add_node(format!("Num:{}", x)),
            AstNode::Constant(Type::Boolean(x)) => self.add_node(format!("Bool:{}", x)),
            AstNode::Constant(Type::Nil) => self.add_node(format!("nil")),
            // Operator
            AstNode::Builtin(Op::InfixOp(op)) | AstNode::Builtin(Op::PrefixOp(op)) => {
                self.add_node(format!("{}", op))
            }
            AstNode::Builtin(Op::Cond) => self.add_node(format!("cond")),
            // Application
            AstNode::App(lhs, rhs) => {
                let node_name = format!("{}{}", Visualizer::NODE_NAME_PREFIX, self.node_counter);
                self.add_node("@".to_string());

                let lhs_name = format!("{}{}", Visualizer::NODE_NAME_PREFIX, self.node_counter);
                self.add_edge(&node_name, &lhs_name);
                self.visualize_ast(lhs);

                let rhs_name = format!("{}{}", Visualizer::NODE_NAME_PREFIX, self.node_counter);
                self.add_edge(&node_name, &rhs_name);
                self.visualize_ast(rhs);
            }
            _ => ()
        };
    }

    fn add_node(&mut self, label: String) {
        let mut name = String::new();
        name.push_str(Visualizer::NODE_NAME_PREFIX);
        name.push_str(self.node_counter.to_string().as_str());
        self.node_counter += 1;
        self.graph.add_node(Node::new(&name, Some(&label)));
    }

    fn add_edge(&mut self, id1: &str, id2: &str) {
        self.graph.add_edge(
            Edge::new(
                id1,
                id2,
                self.graph.is_directed
            )
        )
    }

    pub fn write_to_pdf(&self, outfile: &str) {
        // Get graph represented in graphviz DOT language
        let mut buf = String::new();
        self.graph.as_dot(&mut buf).unwrap();

        let mut dot = Command::new("dot")
            .stdin(Stdio::piped())
            .arg("-Tpdf")
            .arg(format!("-o {}", outfile))
            .spawn().expect("Unable to create AST visualization. Graphviz is probably not installed");

        let mut stdin = dot.stdin.take().expect("Failed to write to stdin");
        stdin.write(buf.as_bytes()).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::frontend::lexer::Lexer;
    use crate::frontend::parser::Parser;

    fn parse(input: &str) -> AstNode {
        let mut lx = Lexer::new(input);
        let tokens = lx.tokenize().unwrap().clone();
        let mut parser = Parser::new(tokens);
        parser.parse_expr().unwrap()
    }

    #[test]
    fn test_visualizer() {
        let ast = parse("1 + 2 where a = 1; b = 2; c d e = d + e");
        let mut vis = Visualizer::new("g", false);
        vis.visualize_ast(&ast);
        vis.write_to_pdf("graph.pdf");
    }
}