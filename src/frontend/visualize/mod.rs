use super::visualize::graph::{Graph, Edge, Node};
use super::ast::{AstNode, Op, Ast, Def};
use crate::frontend::token::Type;

use std::{process::{Command, Stdio}, io::Write, fs::File};
use std::collections::hash_map;

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

    /// Return the node id which will be given to the next node.
    fn get_next_id(&self) -> String {
        format!("{}{}", Visualizer::NODE_NAME_PREFIX, self.node_counter)
    }

    /// Add definitions to the graph with a given definition root and a hash map iterator
    /// with all definitions.
    fn add_definition(&mut self, def_root_id: String, defs: hash_map::Iter<'_, Def, AstNode>) {
        for (def, ast_node) in defs {
            let mut def_name = def.name.clone();
            // Add param names to definition node name.
            match def.params {
                Some(ref params) => {
                    for param_name in params {
                        def_name += " ";
                        def_name += param_name;
                    }
                }
                None => ()
            }
            // Add node for definition and edge from definition to the
            // corresponding AST.
            let def_id = self.get_next_id();
            self.add_node(def_name);
            let ast_id = self.get_next_id();
            self.add_edge(&def_id, &ast_id);
            // Add Edge from root to each definition
            self.add_edge(&def_root_id, &def_id);
            // Visualize the expression body of the definition
            self.visualize_ast_nodes(ast_node);            
        }
    }

    /// Create a graph from a given AST.
    pub fn visualize_ast(&mut self, ast: &Ast) {
        // Create root node
        let system_id = self.get_next_id();
        self.add_node("Prog".to_string());
        self.add_definition(system_id.clone(), ast.global_defs.iter());
        // Visualize program body expression and add edge to the root.
        self.add_edge(&system_id, &self.get_next_id());
        self.visualize_ast_nodes(&ast.body);
    }

    /// Create a graph from ast_nodes.
    pub fn visualize_ast_nodes(&mut self, nodes: &AstNode) {
        match nodes {
            AstNode::Empty => (),
            AstNode::Ident(x) => self.add_node(format!("Id:{}", x)),
            AstNode::Where(Some(lhs_expr), defs, _) => {
                let where_id = self.get_next_id();
                self.add_node("where".to_string());

                let lhs_id = self.get_next_id();
                self.add_edge(&where_id, &lhs_id);
                self.visualize_ast_nodes(lhs_expr);

                self.add_definition(where_id.clone(), defs.iter());

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
                let node_name = self.get_next_id();
                self.add_node("@".to_string());

                let lhs_name = self.get_next_id();
                self.add_edge(&node_name, &lhs_name);
                self.visualize_ast_nodes(lhs);

                let rhs_name = self.get_next_id();
                self.add_edge(&node_name, &rhs_name);
                self.visualize_ast_nodes(rhs);
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

    /// Outputs the created graph to a pdf at a given path.
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

    pub fn write_to_dot(&self, outfile: &str) {
        let mut file = File::create(outfile).expect("Could not create .dot file.");
        let mut buf = String::new();
        self.graph.as_dot(&mut buf).unwrap();
        file.write_all(buf.as_bytes()).expect("Error writing to .dot file.");
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
        vis.visualize_ast_nodes(&ast);
        vis.write_to_pdf("graph.pdf");
    }
}